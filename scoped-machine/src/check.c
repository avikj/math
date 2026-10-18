#include "check.h"
#include "reuse.h"
#include "fine.h"
#include "lib.h"
#include "compiler.h"
#include <sys/mman.h>

/* The checker's judgments are frame families (kframe.h): every judgment form
 * (inference, checking, type and term conversion, neutral spines, context,
 * map, origin, symbol and template-boundary validation) and the claim
 * protocol (acquisition with its waits, stepped resolution, release) is a
 * resumable frame; the public functions are their synchronous drivers. A
 * frame that owns a claim or a root entry releases it when it is dropped. */

/* a call of another unit's family (a resume point), and a plain call (a
 * bounded procedure, or one whose whole body runs under its own lock) */
#define KX(fn, dest, ...) KF_CALL(fn, dest, __VA_ARGS__)
#define KXV(fn, ...) KF_CALL(fn, NULL, __VA_ARGS__)
#define KP(fn, dest, ...) (*(dest) = fn(__VA_ARGS__))

/* ------------------------------------------------------------------ */
/* state: request claims, memo, budget                                  */

/* Every memoized checking request (context validity, typed map, origin
 * validation, symbol validation, clause conversion) is a *claim*: one
 * producer computes it, every other client waits for that producer's
 * outcome, and the outcome is published once. A request already running on
 * the same computation, or on one that is (transitively) waiting for this
 * one, is a genuine cycle in the demand graph: for conversion, origins,
 * contexts and maps it yields no verdict (UNRESOLVED); for a symbol it means
 * the recursive occurrence is typed by the declaration (§34).
 *
 * Verdicts obtained while some symbol's body validation is still running are
 * *provisional* on those symbols: the claim records them, and it is committed
 * only when every such symbol validates; if one is rejected (or reaches no
 * verdict), the provisional claims are withdrawn and recomputed on demand.
 * This is the admission transaction of §34 (Q2 of the review): declared
 * signatures are assumptions while a body is checked, and no success that
 * rests on them escapes before the bodies they belong to are accepted. */
typedef struct {
    int state;              /* 0 absent, 1 running, 2 done */
    uint64_t owner;         /* producing computation while running */
    uint64_t result;        /* verdict code when done: 1 valid/equal, 2 invalid/unequal, 3 unresolved (this attempt only) */
    uint64_t attempt;       /* admission attempt that produced an unresolved outcome */
    const char *reason;
    uint64_t aux[3];        /* origin: context, required face, type */
    Words deps;             /* symbol claims this verdict is provisional on */
    Words gdeps;            /* §79: (symbol, revision) pairs the verdict read; reusable only while they are current */
    bool is_symbol;
} Claim;

typedef struct { size_t claim; Words deps; Words gdeps; } Frame;

static struct {
    WordMap idx;            /* (kind, words...) → claim index + 1 */
    Chunked recs; size_t nrecs;   /* V21 R4: claim records at stable addresses in an extensible table (full-width directory, no fixed capacity) */
    pthread_mutex_t mu; pthread_cond_t cv;
    VEC(uint64_t) wait_on;  /* per computation id: claim index + 1 it is blocked on (0 = none) */
    VEC(void *) kstack;     /* per computation id: the engine stack running it (a waiter on an engine stack suspends with that dependency) */
    VEC(uint8_t) assume;    /* per computation id: released from a wait on a symbol with "typed by the declaration" */
    VEC(uint64_t) free_ids; /* identities of completed engine computations, reused */
    uint64_t ntids;
    size_t budget;
    uint64_t attempt;       /* §59.4: a changed budget or a retry begins a new attempt */
    size_t clients;         /* top-level requests in progress (atomic): the session boundary requires zero */
    uint64_t crev;          /* bumped (under mu) when a published verdict is withdrawn or a premise discharged: a stepped resolution revalidates against it */
    int live;
} K;
#define CLAIM(i) ((Claim *)chunked_get(&K.recs, (i)))

/* §59.4: computation identities are session-qualified; the generation
 * allocator survives check_free so a reused client re-registers in a new
 * session. A plain thread is one computation; an engine stack is another
 * (its identity travels with it as computation-local state) */
static uint64_t session_gen;
typedef struct { uint64_t tid, gen; } CkId;
static __thread CkId tl_id;

/* §57 R1 / §59.4: the whole-environment admission transaction. One attempt
 * per environment version runs at a time; concurrent public clients wait for
 * its result; a changed environment begins a new attempt. */
static struct { bool running, have; uint64_t version, attempt; CheckStatus status; const char *reason; } ADM;
/* diagnostics built at runtime are immutable strings owned by the checker
 * session (a published claim keeps a pointer to its text) */
static struct { VEC(char *) items; pthread_mutex_t mu; } DIAG;
static const char *diag_intern(const char *text) {
    char *copy = strdup(text); require(copy, "out of memory");
    pthread_mutex_lock(&DIAG.mu); vec_push(&DIAG.items, copy); pthread_mutex_unlock(&DIAG.mu);
    return copy;
}
typedef VEC(Frame) FrameVec;
static __thread FrameVec tl_frames;
static __thread Words tl_pending;        /* symbols a finished top-level verdict still rests on */
static __thread size_t tl_steps, tl_depth, tl_budget;   /* the budget is fixed for a top-level request when it enters */
static const char *R_BUDGET = "budget exhausted";

enum { CL_CTX = 1, CL_MAP, CL_ORIGIN, CL_SYMBOL, CL_CONV, CL_TVIEW, CL_TBOUND };
typedef enum { ACQ_OWNER, ACQ_DONE, ACQ_CYCLE } Acq;

/* the checker's computation-local state (kframe.h) */
static void *a_id(void) { return &tl_id; }
static void *a_frames(void) { return &tl_frames; }
static void *a_pending(void) { return &tl_pending; }
static void *a_steps(void) { return &tl_steps; }
static void *a_depth(void) { return &tl_depth; }
static void *a_budget(void) { return &tl_budget; }
/* a completed or discarded engine computation returns its identity (its claims were released or abandoned by then) */
static void release_id(void *p) {
    CkId id = *(CkId *)p;
    if (!id.tid || !__atomic_load_n(&K.live, __ATOMIC_ACQUIRE)) return;
    pthread_mutex_lock(&K.mu);
    if (K.live && id.gen == session_gen && id.tid < K.wait_on.len) {
        K.wait_on.data[id.tid] = 0; K.assume.data[id.tid] = 0; K.kstack.data[id.tid] = NULL;
        vec_push(&K.free_ids, id.tid);
    }
    pthread_mutex_unlock(&K.mu);
}
static void release_frames(void *p) {
    FrameVec *v = p;
    for (size_t k = 0; k < v->len; k++) { words_free(&v->data[k].deps); words_free(&v->data[k].gdeps); }
    vec_free(v);
}
static void release_pending(void *p) { words_free((Words *)p); }
__attribute__((constructor)) static void check_ctx_register(void) {
    kf_ctx_register(a_id, sizeof tl_id, NULL, release_id);
    kf_ctx_register(a_frames, sizeof tl_frames, NULL, release_frames);
    kf_ctx_register(a_pending, sizeof tl_pending, NULL, release_pending);
    kf_ctx_register(a_steps, sizeof tl_steps, NULL, NULL);
    kf_ctx_register(a_depth, sizeof tl_depth, NULL, NULL);
    kf_ctx_register(a_budget, sizeof tl_budget, NULL, NULL);
}

void check_init(void) {
    memset(&K, 0, sizeof K);
    memset(&ADM, 0, sizeof ADM);
    memset(&DIAG, 0, sizeof DIAG); pthread_mutex_init(&DIAG.mu, NULL);
    session_gen++;
    K.attempt = 1;
    wordmap_init(&K.idx);
    /* V21 R4: the claim records live in an extensible chunked table (stable
     * addresses, full-width directory): a claim is created under K.mu
     * without growing or copying an array; the chunk it needs is created
     * before K.mu is taken (claim_index) */
    chunked_init(&K.recs, sizeof(Claim)); K.nrecs = 0;
    pthread_mutex_init(&K.mu, NULL); pthread_cond_init(&K.cv, NULL);
    vec_push(&K.wait_on, 0); vec_push(&K.assume, 0); vec_push(&K.kstack, NULL);
    __atomic_store_n(&K.live, 1, __ATOMIC_RELEASE);
}
void check_free(void) {
    pthread_mutex_lock(&K.mu); __atomic_store_n(&K.live, 0, __ATOMIC_RELEASE); pthread_mutex_unlock(&K.mu);
    for (size_t k = 0; k < K.nrecs; k++) { words_free(&CLAIM(k)->deps); words_free(&CLAIM(k)->gdeps); }
    chunked_free(&K.recs); K.nrecs = 0;
    vec_free(&K.wait_on); vec_free(&K.assume); vec_free(&K.kstack); vec_free(&K.free_ids);
    wordmap_free(&K.idx);
    pthread_mutex_destroy(&K.mu); pthread_cond_destroy(&K.cv);
    memset(&K, 0, sizeof K);
    for (size_t k = 0; k < DIAG.items.len; k++) free(DIAG.items.data[k]);
    vec_free(&DIAG.items); pthread_mutex_destroy(&DIAG.mu); memset(&DIAG, 0, sizeof DIAG);
}
uint64_t check_session_id(void) { return session_gen; }
void check_set_budget(size_t steps) {
    pthread_mutex_lock(&K.mu);
    if (K.budget != steps) { K.budget = steps; K.attempt++; }   /* a changed budget is a new attempt */
    pthread_mutex_unlock(&K.mu);
}
void check_new_attempt(void) { pthread_mutex_lock(&K.mu); K.attempt++; pthread_mutex_unlock(&K.mu); }
uint64_t check_attempt(void) { pthread_mutex_lock(&K.mu); uint64_t a = K.attempt; pthread_mutex_unlock(&K.mu); return a; }
const char *check_status_name(CheckStatus s) { return s == CK_VALID ? "VALID" : s == CK_INVALID ? "INVALID" : "UNRESOLVED"; }
const char *conv_status_name(ConvStatus s) { return s == CV_EQUAL ? "EQUAL" : s == CV_UNEQUAL ? "UNEQUAL" : "UNRESOLVED"; }

static bool budget_ok(void) { tl_steps++; fine_bump(FC_CHECK_FRAMES); size_t b = tl_depth ? tl_budget : K.budget; return b == 0 || tl_steps <= b; }

/* computation identity, assigned on first use (under K.mu) */
static uint64_t tid_locked(void) {
    if (!tl_id.tid || tl_id.gen != session_gen) {
        if (kf_tl && K.free_ids.len) tl_id.tid = K.free_ids.data[--K.free_ids.len];
        else { tl_id.tid = ++K.ntids; vec_push(&K.wait_on, 0); vec_push(&K.assume, 0); vec_push(&K.kstack, NULL); }
        tl_id.gen = session_gen;
    }
    K.kstack.data[tl_id.tid] = kf_tl;   /* the engine stack this computation runs on (NULL: a plain thread) */
    return tl_id.tid;
}
/* §94: a wait on a claim another computation owns — an engine stack
 * suspends with that dependency (one transition), a plain thread waits */
#define CLAIM_WAIT(owner) do { \
        KStack *on_ = (owner) < K.kstack.len ? (KStack *)K.kstack.data[(owner)] : NULL; \
        KF_WAIT(&K.cv, &K.mu, on_, on_ ? on_->job : 0); } while (0)

/* every claim belongs to one definition environment (§57 R1 / §59.4): the
 * key carries the environment version, so a successful candidate mutation
 * makes every earlier environment-dependent verdict unreachable */
static void claim_key(uint64_t kind, const uint64_t *w, size_t n, uint64_t key[10]) {
    /* §79.2: the whole-signature admission (CL_SYMBOL) stays keyed by the
     * environment version; every other judgment is keyed by its semantic
     * request and validated by the symbol revisions it actually read */
    key[0] = kind; key[1] = kind == CL_SYMBOL ? global_env_version() : 0; memcpy(key + 2, w, n * sizeof(uint64_t));
}
/* the claim of an interned key: created under K.mu (one constant step) when
 * the key's value is still unpublished */
static size_t claim_of_slot_locked(uint64_t *slot, uint64_t kind) {
    uint64_t v = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
    if (v) return (size_t)v - 1;
    Claim c; memset(&c, 0, sizeof c); words_init(&c.deps); words_init(&c.gdeps); c.is_symbol = kind == CL_SYMBOL;
    *(Claim *)chunked_at(&K.recs, K.nrecs) = c; __atomic_store_n(&K.nrecs, K.nrecs + 1, __ATOMIC_RELEASE);   /* a stable slot; a new chunk is a zero block (no copy, no clearing under K.mu) */
    __atomic_store_n(slot, K.nrecs, __ATOMIC_RELEASE);
    return K.nrecs - 1;
}
__attribute__((unused)) static size_t claim_index_locked(uint64_t kind, const uint64_t *w, size_t n) {   /* the white-box probes call it under K.mu */
    uint64_t key[10]; claim_key(kind, w, n, key);
    uint64_t id = interner_intern(&K.idx.keys, key, n + 2, NULL);
    return claim_of_slot_locked((uint64_t *)chunked_at(&K.idx.vals, id - 1), kind);
}
/* §94: the key is interned outside K.mu (the interner's cursor sections);
 * K.mu is held only to create the claim of a new key */
#define claim_index_PARAMS(X) X(uint64_t, kind) X(const uint64_t *, w) X(size_t, n)
KF_DECL(claim_index, size_t, claim_index_PARAMS, uint64_t key[10]; uint64_t id; size_t at;)
KF_STEP(claim_index) {
    KF_BEGIN(claim_index);
    claim_key(F->kind, F->w, F->n, F->key);
    KF_CALL(interner_intern, &F->id, &K.idx.keys, F->key, F->n + 2, NULL);
    KF_CALL(chunked_prepare, NULL, &K.idx.vals, F->id - 1);
    {
        uint64_t *slot = (uint64_t *)chunked_at(&K.idx.vals, F->id - 1);
        uint64_t v = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
        if (v) KF_RET((size_t)v - 1);
    }
    F->at = __atomic_load_n(&K.nrecs, __ATOMIC_ACQUIRE); KF_CALL(chunked_prepare, NULL, &K.recs, F->at); KF_CALL(chunked_prepare, NULL, &K.recs, F->at + 1);   /* the next chunk, published outside K.mu (a racing candidate is retired) */
    {
        uint64_t *slot = (uint64_t *)chunked_at(&K.idx.vals, F->id - 1);
        pthread_mutex_lock(&K.mu); size_t c = claim_of_slot_locked(slot, F->kind); pthread_mutex_unlock(&K.mu);
        KF_RET(c);
    }
    KF_END;
}

/* §79: a frame's premises (claim indices) and read dependencies ((symbol, revision) pairs) are
 * collected append-only — one push per recorded premise, growth a child frame — and made sets
 * once, when the frame's verdict is published (sorted and deduplicated, one transition per step) */
#define deps_push_PARAMS(X) X(Words *, w) X(uint64_t, x)
KF_DECL(deps_push, void, deps_push_PARAMS,)
KF_STEP(deps_push) { KF_BEGIN(deps_push); KF_WORDS_PUSH(F->w, F->x); KF_RETV(); KF_END; }
#define gdeps_push_PARAMS(X) X(Words *, g) X(uint64_t, sym) X(uint64_t, rev)
KF_DECL(gdeps_push, void, gdeps_push_PARAMS,)
KF_STEP(gdeps_push) { KF_BEGIN(gdeps_push); KF_WORDS_PUSH(F->g, F->sym); KF_WORDS_PUSH(F->g, F->rev); KF_RETV(); KF_END; }
/* premises as a set; `drop` (a symbol's own claim, closed by its verdict) removed */
#define deps_canon_PARAMS(X) X(Words *, w) X(uint64_t, drop) X(bool, has_drop)
KF_DECL(deps_canon, void, deps_canon_PARAMS, size_t j, k;)
KF_STEP(deps_canon) {
    KF_BEGIN(deps_canon);
    KF_CALL(sort_unique_u64, &F->w->n, F->w->w, F->w->n);
    if (F->has_drop) {
        for (F->j = F->k = 0; F->k < F->w->n; F->k++) { if (F->w->w[F->k] != F->drop) F->w->w[F->j++] = F->w->w[F->k]; fine_bump(FC_CLAIM_STEPS); KF_SAFE(); }
        F->w->n = F->j;
    }
    KF_RETV();
    KF_END;
}
/* read dependencies as a set of pairs */
#define gdeps_canon_PARAMS(X) X(Words *, g)
KF_DECL(gdeps_canon, void, gdeps_canon_PARAMS, size_t j, k;)
KF_STEP(gdeps_canon) {
    KF_BEGIN(gdeps_canon);
    if (F->g->n < 4) KF_RETV();
    KF_CALL(pair_sort, NULL, F->g->w, F->g->n / 2);
    for (F->j = 2, F->k = 2; F->k + 1 < F->g->n; F->k += 2) {
        if (F->g->w[F->k] != F->g->w[F->j - 2] || F->g->w[F->k + 1] != F->g->w[F->j - 1]) { F->g->w[F->j] = F->g->w[F->k]; F->g->w[F->j + 1] = F->g->w[F->k + 1]; F->j += 2; }
        fine_bump(FC_CLAIM_STEPS); KF_SAFE();
    }
    F->g->n = F->j;
    KF_RETV();
    KF_END;
}

/* Would blocking on a claim owned by `owner` close a wait cycle back to this
 * computation? When it would, and some computation on the cycle is blocked on
 * a *symbol* claim, that wait is the one to yield: the symbol's declaration
 * becomes that computation's assumption (exactly what a single computation
 * does when it meets its own running symbol), and the caller may block. Only
 * a cycle with no symbol on it is a genuine cyclic request. */
static bool wait_cycle_locked(uint64_t owner, uint64_t me, uint64_t *symbol_waiter) {
    uint64_t cur = owner;
    *symbol_waiter = 0;
    for (uint64_t steps = 0; steps <= K.ntids; steps++) {
        if (cur == me) return true;
        uint64_t w = K.wait_on.data[cur];
        if (!w) return false;
        Claim *c = CLAIM(w - 1);
        if (c->is_symbol && c->state == 1 && !*symbol_waiter) *symbol_waiter = cur;
        if (c->state != 1) return false;
        cur = c->owner;
    }
    return true;
}
/* decide how to treat a claim owned by another computation: true = block on
 * it, false = it is a genuine cycle */
static bool may_block_locked(uint64_t owner, uint64_t me) {
    uint64_t sw;
    if (!wait_cycle_locked(owner, me, &sw)) return true;
    if (!sw) return false;
    K.assume.data[sw] = 1;
    pthread_cond_broadcast(&K.cv);
    return true;
}

static Frame *top_frame(void) { return tl_frames.len ? &tl_frames.data[tl_frames.len - 1] : NULL; }
static void frame_push(size_t claim) { Frame f; f.claim = claim; words_init(&f.deps); words_init(&f.gdeps); vec_push(&tl_frames, f); }
/* room for one more checker frame, made before a claim can be owned (the growth is a child frame; the push itself is then one step) */
KF_DECL(frames_reserve, void, KF_NOPARAMS, size_t cap; void *p;)
KF_STEP(frames_reserve) {
    KF_BEGIN(frames_reserve);
    if (tl_frames.len < tl_frames.cap) KF_RETV();
    F->cap = tl_frames.cap ? tl_frames.cap * 2 : 8;
    KF_CALL(k_regrow, &F->p, tl_frames.data, F->cap * sizeof(Frame));   /* into the frame: a thread-local's address does not survive a suspension */
    tl_frames.data = F->p; tl_frames.cap = F->cap;
    KF_RETV();
    KF_END;
}
/* §79.1: dependency-recording reads, appended to the enclosing frame */
#define NOTE_SYMBOL(s) do { if (top_frame()) KF_CALL(gdeps_push, NULL, &top_frame()->gdeps, (s), global_revision(s)); } while (0)
#define note_entry_PARAMS(X) X(EntryId, e)
KF_DECL(note_entry, void, note_entry_PARAMS, const PVec *p; size_t n, k;)
KF_STEP(note_entry) {   /* a ready entry's read dependencies (immutable once it is ready), one pair per transition */
    KF_BEGIN(note_entry);
    if (!top_frame() || !F->e) KF_RETV();
    F->n = 2 * eval_entry_gdeps(F->e, &F->p);
    KF_CALL(words_reserve, NULL, &top_frame()->gdeps, F->n);
    for (F->k = 0; F->k < F->n; F->k++) { Frame *f = top_frame(); f->gdeps.w[f->gdeps.n++] = pv_get(F->p, F->k); fine_bump(FC_DEP_PAIRS); KF_SAFE(); }
    KF_RETV();
    KF_END;
}

/* §94: K.mu is held for one claim or one premise at a time and released
 * between steps (one fine transition, FC_CLAIM_STEPS, a suspension point) */
#define RESOLVE_PAUSE() do { pthread_mutex_unlock(&K.mu); fine_bump(FC_CLAIM_STEPS); KF_SAFE(); pthread_mutex_lock(&K.mu); } while (0)

/* Resolve provisional verdicts against the symbols they rest on:
 *   - a premise rejected or unresolved withdraws the dependent verdict, which
 *     is recomputed on demand;
 *   - a committed premise is discharged;
 *   - a set of accepted symbol verdicts resting only on each other (mutual
 *     recursion validated from both ends) is committed together: it is the
 *     greatest set of accepted symbols closed under their premises.
 * Runs under K.mu after a symbol verdict is published; the caller holds K.mu
 * on entry and on return. A withdrawal or discharge is decided on the state
 * seen under the lock at that step. The greatest committed set is computed
 * against a snapshot of `crev`: a withdrawal or discharge by any computation
 * meanwhile restarts the resolution; each commit (clearing a member's
 * premises) is made under the lock only while `crev` is unchanged since the
 * set was computed — a commit made before a later change is the commit the
 * atomic resolution would have made at that point. */
KF_DECL_DROP(resolve_locked, void, KF_NOPARAMS, resolve_drop, bool changed, restart, committed, shrink, ok; size_t c, k, n0, nin; uint64_t rev0; bool *in;)
static void resolve_drop(resolve_locked_F *F) { free(F->in); F->in = NULL; }
KF_STEP(resolve_locked) {
    KF_BEGIN(resolve_locked);
    for (;;) {
        F->changed = true;
        while (F->changed) {
            F->changed = false;
            for (F->c = 0; F->c < K.nrecs; F->c++) {
                for (F->k = 0;;) {
                    Claim *r = CLAIM(F->c);
                    if (r->state != 2 || F->k >= r->deps.n) break;
                    Claim *d = CLAIM(r->deps.w[F->k]);
                    if (d->state == 2 && d->result != 1) { r->state = 0; r->deps.n = 0; K.crev++; F->changed = true; break; }
                    if (d->state == 2 && d->result == 1 && d->deps.n == 0) { r->deps.w[F->k] = r->deps.w[--r->deps.n]; K.crev++; F->changed = true; }   /* discharged (the premises are a set) */
                    else F->k++;
                    RESOLVE_PAUSE();
                }
                RESOLVE_PAUSE();
            }
        }
        F->rev0 = K.crev; F->n0 = K.nrecs;
        pthread_mutex_unlock(&K.mu);
        F->in = calloc(F->n0 ? F->n0 : 1, sizeof(bool));
        pthread_mutex_lock(&K.mu);
        F->restart = K.crev != F->rev0; F->committed = false;
        F->nin = 0;
        for (F->c = 0; F->c < F->n0 && !F->restart; F->c++) {
            Claim *r = CLAIM(F->c);
            if (r->is_symbol && r->state == 2 && r->result == 1 && r->deps.n) { F->in[F->c] = true; F->nin++; }
            RESOLVE_PAUSE(); F->restart = K.crev != F->rev0;
        }
        F->shrink = true;
        while (F->shrink && F->nin && !F->restart) {
            F->shrink = false;
            for (F->c = 0; F->c < F->n0 && !F->restart; F->c++) {
                if (!F->in[F->c]) continue;
                for (F->k = 0;; F->k++) {
                    Claim *r = CLAIM(F->c);
                    if (F->k >= r->deps.n) break;
                    size_t dd = r->deps.w[F->k]; Claim *d = CLAIM(dd);
                    F->ok = (dd < F->n0 && F->in[dd]) || (d->state == 2 && d->result == 1 && d->deps.n == 0);
                    if (!F->ok) { F->in[F->c] = false; F->nin--; F->shrink = true; }
                    RESOLVE_PAUSE(); F->restart = K.crev != F->rev0;
                    if (!F->ok || F->restart) break;
                }
            }
        }
        for (F->c = 0; F->c < F->n0 && F->nin && !F->restart; F->c++) {
            if (!F->in[F->c]) continue;
            if (K.crev != F->rev0) { F->restart = true; break; }
            (*CLAIM(F->c)).deps.n = 0; F->committed = true;
            RESOLVE_PAUSE();
        }
        free(F->in); F->in = NULL;
        if (!F->restart && !F->committed) KF_RETV();
    }
    KF_END;
}

/* acquire claim `c`: ACQ_OWNER (this computation computes it, a frame is
 * pushed), ACQ_DONE (verdict copied out, provisional premises inherited), or
 * ACQ_CYCLE (the request is on this computation's own demand path). */
#define claim_acquire_PARAMS(X) X(size_t, c) X(uint64_t *, result) X(const char **, reason) X(uint64_t *, aux)
KF_DECL_DROP(claim_acquire, Acq, claim_acquire_PARAMS, claim_acquire_drop, uint64_t me; size_t assumed, k, d; uint64_t rev0; bool stale, moved, waited; uint64_t sym, rev;)
static void claim_acquire_drop(claim_acquire_F *F) {   /* dropped inside a wait: this computation no longer waits */
    if (!F->me || !__atomic_load_n(&K.live, __ATOMIC_ACQUIRE)) return;
    pthread_mutex_lock(&K.mu); if (F->me < K.wait_on.len) { K.wait_on.data[F->me] = 0; K.assume.data[F->me] = 0; } pthread_mutex_unlock(&K.mu);
}
KF_STEP(claim_acquire) {
    KF_BEGIN(claim_acquire);
    KF_CALL0(frames_reserve, NULL);
    pthread_mutex_lock(&K.mu);
    F->me = tid_locked();
    F->assumed = SIZE_MAX;       /* a premise taken as a declaration assumption after a cycle */
    for (;;) {
        /* records are reacquired by index after every wait (§59.4) */
        { Claim *r = CLAIM(F->c); if (r->state == 2 && r->result == 3 && r->attempt != K.attempt) { r->state = 0; K.crev++; } }   /* an old attempt's unresolved outcome */
        /* §94: the verdict's lists are examined one entry per K.mu section
         * (one fine transition between sections). Any withdrawal or
         * discharge meanwhile (crev) restarts the examination; entries
         * already inherited into this computation's frame are extra premises
         * / read dependencies — conservative, and deduplicated on the next
         * pass. */
        F->rev0 = K.crev;
        if (CLAIM(F->c)->state == 2 && !CLAIM(F->c)->is_symbol) {   /* §79.2: a read dependency changed */
            F->stale = false; F->moved = false;
            reuse_bump(REUSE_DEPENDENCY_CHECK);
            for (F->k = 0;; F->k += 2) {
                Claim *r = CLAIM(F->c);
                if (r->state != 2 || K.crev != F->rev0) { F->moved = true; break; }
                if (F->k + 1 >= r->gdeps.n) break;
                if (global_revision(r->gdeps.w[F->k]) != r->gdeps.w[F->k + 1]) { F->stale = true; break; }
                RESOLVE_PAUSE();
            }
            if (F->moved) continue;
            if (F->stale) { Claim *r = CLAIM(F->c); r->state = 0; r->deps.n = 0; r->gdeps.n = 0; K.crev++; }
        }
        if (CLAIM(F->c)->state == 2) {
            /* a verdict provisional on symbols: a rejected premise withdraws
             * it (recomputed now, by us); a premise another computation is
             * still validating is waited for unless waiting would close a
             * cycle (then the declaration is our assumption too) */
            F->waited = false;
            for (F->k = 0; !F->waited; F->k++) {
                Claim *r = CLAIM(F->c);
                if (r->state != 2 || K.crev != F->rev0) { F->waited = true; break; }
                if (F->k >= r->deps.n) break;
                F->d = r->deps.w[F->k];
                Claim *dc = CLAIM(F->d);
                if (dc->state == 2 && dc->result != 1) { KF_CALL0(resolve_locked, NULL); F->waited = true; break; }
                if (dc->state == 1 && dc->owner != F->me && F->d != F->assumed && may_block_locked(dc->owner, F->me)) {
                    K.wait_on.data[F->me] = F->d + 1;
                    CLAIM_WAIT(CLAIM(F->d)->owner);
                    K.wait_on.data[F->me] = 0;
                    if (K.assume.data[F->me]) { K.assume.data[F->me] = 0; F->assumed = F->d; }   /* told to assume: inherit on the next pass */
                    F->waited = true;
                    break;
                }
                RESOLVE_PAUSE();
            }
            if (F->waited) continue;
            { Claim *r = CLAIM(F->c); *F->result = r->result; if (F->reason) *F->reason = r->reason; if (F->aux) memcpy(F->aux, r->aux, sizeof r->aux); }
            F->moved = false;
            for (F->k = 0;; F->k++) {   /* premises, one per section, into this computation's frame */
                Claim *r = CLAIM(F->c);
                if (r->state != 2 || K.crev != F->rev0) { F->moved = true; break; }
                if (F->k >= r->deps.n) break;
                F->d = r->deps.w[F->k];
                pthread_mutex_unlock(&K.mu);
                if (top_frame()) KF_CALL(deps_push, NULL, &top_frame()->deps, F->d);
                fine_bump(FC_CLAIM_STEPS);
                KF_SAFE();
                pthread_mutex_lock(&K.mu);
            }
            for (F->k = 0; !F->moved; F->k += 2) {   /* read dependencies, one pair per section */
                Claim *r = CLAIM(F->c);
                if (r->state != 2 || K.crev != F->rev0) { F->moved = true; break; }
                if (F->k + 1 >= r->gdeps.n) break;
                F->sym = r->gdeps.w[F->k]; F->rev = r->gdeps.w[F->k + 1];
                pthread_mutex_unlock(&K.mu);
                if (top_frame()) KF_CALL(gdeps_push, NULL, &top_frame()->gdeps, F->sym, F->rev);
                fine_bump(FC_CLAIM_STEPS);
                KF_SAFE();
                pthread_mutex_lock(&K.mu);
            }
            if (F->moved) continue;
            pthread_mutex_unlock(&K.mu);
            KF_RET(ACQ_DONE);
        }
        if (CLAIM(F->c)->state == 0) {
            Claim *r = CLAIM(F->c);
            r->state = 1; r->owner = F->me;
            pthread_mutex_unlock(&K.mu);
            frame_push(F->c);   /* this computation's frame stack: room was made before K.mu (frames_reserve) */
            KF_RET(ACQ_OWNER);
        }
        if (CLAIM(F->c)->owner == F->me || !may_block_locked(CLAIM(F->c)->owner, F->me)) { pthread_mutex_unlock(&K.mu); KF_RET(ACQ_CYCLE); }
        K.wait_on.data[F->me] = F->c + 1;
        CLAIM_WAIT(CLAIM(F->c)->owner);
        K.wait_on.data[F->me] = 0;
        if (K.assume.data[F->me]) { K.assume.data[F->me] = 0; pthread_mutex_unlock(&K.mu); KF_RET(ACQ_CYCLE); }
    }
    KF_END;
}

/* release the claim this computation owns at the top of its frame stack.
 * result 0 = no verdict (the attempt's waiters receive the unresolved
 * outcome); otherwise the verdict is published, provisional on the running
 * symbols the computation relied on. The published lists are prepared
 * outside K.mu and swapped in under it (one constant step). */
#define claim_release_PARAMS(X) X(size_t, c) X(uint64_t, result) X(const char *, reason) X(const uint64_t *, aux)
KF_DECL_DROP(claim_release, void, claim_release_PARAMS, claim_release_drop, Words deps, gdeps, gnew, dnew; Claim *r;)
static void claim_release_drop(claim_release_F *F) { words_free(&F->deps); words_free(&F->gdeps); words_free(&F->gnew); words_free(&F->dnew); }
KF_STEP(claim_release) {
    KF_BEGIN(claim_release);
    {
        Frame *f = top_frame();
        require(f && f->claim == F->c, "claim release out of order");
        F->deps = f->deps; F->gdeps = f->gdeps; tl_frames.len--;
    }
    F->r = CLAIM(F->c);                     /* a stable address */
    KF_CALL(deps_canon, NULL, &F->deps, F->c, F->r->is_symbol);   /* a set; self-recursion is closed by this verdict */
    KF_CALL(gdeps_canon, NULL, &F->gdeps);
    words_init(&F->gnew); words_init(&F->dnew);
    KF_CALL(words_append, NULL, &F->gnew, F->gdeps.w, F->gdeps.n);
    if (F->result != 0) KF_CALL(words_append, NULL, &F->dnew, F->deps.w, F->deps.n);
    pthread_mutex_lock(&K.mu);
    { Words t = F->r->gdeps; F->r->gdeps = F->gnew; F->gnew = t; }
    if (F->result == 0) {
        /* no verdict in this attempt: the attempt's waiters receive the
         * unresolved outcome (one producer per attempt, §59.4); a new attempt
         * recomputes */
        F->r->state = 2; F->r->result = 3; F->r->reason = F->reason ? F->reason : "unresolved: no verdict in this attempt"; F->r->attempt = K.attempt;
        F->r->deps.n = 0;
    } else {
        F->r->state = 2; F->r->result = F->result; F->r->reason = F->reason;
        if (F->aux) memcpy(F->r->aux, F->aux, sizeof F->r->aux); else memset(F->r->aux, 0, sizeof F->r->aux);
        { Words t = F->r->deps; F->r->deps = F->dnew; F->dnew = t; }
    }
    pthread_cond_broadcast(&K.cv);                  /* the verdict is published before the stepped resolution releases K.mu */
    if (F->r->is_symbol) { KF_CALL0(resolve_locked, NULL); pthread_cond_broadcast(&K.cv); }
    pthread_mutex_unlock(&K.mu);
    if (top_frame()) { KF_CALL(words_append, NULL, &top_frame()->deps, F->deps.w, F->deps.n); KF_CALL(words_append, NULL, &top_frame()->gdeps, F->gdeps.w, F->gdeps.n); }   /* into this computation's enclosing frame */
    words_free(&F->deps); words_free(&F->gdeps); words_free(&F->gnew); words_free(&F->dnew);
    KF_RETV();
    KF_END;
}
/* DROP of a frame that owns claim `c`: the computation ends with no verdict
 * (closed-session destruction; runs outside any step on the dropping thread,
 * with the computation's state current) */
static void claim_abandon(size_t c) {
    if (!__atomic_load_n(&K.live, __ATOMIC_ACQUIRE)) return;
    Frame *f = top_frame();
    if (!f || f->claim != c) return;
    KStack *s = kf_sync_begin(); claim_release_push(s, NULL, c, 0, "unresolved: the computation was discarded", NULL); kf_sync_run(s); kf_sync_end(s);
}

/* Top-level requests run in a root frame. A root frame may end with
 * provisional premises only when a symbol validated by another computation
 * was taken as an assumption to break a wait cycle; the verdict is then not
 * final: top_settled waits for those validations and asks the caller to
 * recompute (the recomputation finds committed or withdrawn claims). */
static void top_enter(void) { if (tl_depth++ == 0) { __atomic_add_fetch(&K.clients, 1, __ATOMIC_ACQ_REL); tl_steps = 0; tl_budget = __atomic_load_n(&K.budget, __ATOMIC_ACQUIRE); frame_push(0); } }
KF_DECL_DROP(top_leave, void, KF_NOPARAMS, top_leave_drop, Words pend;)
static void top_leave_drop(top_leave_F *F) { words_free(&F->pend); }
KF_STEP(top_leave) {
    KF_BEGIN(top_leave);
    if (--tl_depth == 0) {
        { Frame *f = top_frame(); require(f && f->claim == 0, "root frame mismatch"); }
        words_free(&tl_pending); words_init(&F->pend);
        KF_CALL(words_append, NULL, &F->pend, top_frame()->deps.w, top_frame()->deps.n);   /* built in the frame (a thread-local's address does not survive a suspension) */
        KF_CALL(deps_canon, NULL, &F->pend, 0, false);
        tl_pending = F->pend; words_init(&F->pend);
        { Frame *f = top_frame(); words_free(&f->deps); words_free(&f->gdeps); tl_frames.len--; }
        if (tl_frames.len == 0) vec_free(&tl_frames);   /* computation-local storage is released at the outermost exit */
        __atomic_sub_fetch(&K.clients, 1, __ATOMIC_ACQ_REL);
    }
    KF_RETV();
    KF_END;
}
/* DROP of a frame inside an entered root: the root is left without a verdict */
static void top_abandon(void) {
    KStack *s = kf_sync_begin(); top_leave_push(s, NULL); kf_sync_run(s); kf_sync_end(s);
    words_free(&tl_pending);
}
KF_DECL(top_settled, bool, KF_NOPARAMS, uint64_t me; size_t k, d;)
KF_STEP(top_settled) {
    KF_BEGIN(top_settled);
    if (tl_depth > 0) KF_RET(true);
    if (tl_pending.n == 0) { words_free(&tl_pending); KF_RET(true); }
    pthread_mutex_lock(&K.mu);
    F->me = tid_locked();
    for (F->k = 0; F->k < tl_pending.n; F->k++) {
        F->d = tl_pending.w[F->k];
        while ((*CLAIM(F->d)).state == 1 && (*CLAIM(F->d)).owner != F->me) {
            K.wait_on.data[F->me] = F->d + 1;
            CLAIM_WAIT((*CLAIM(F->d)).owner);
            K.wait_on.data[F->me] = 0;
            K.assume.data[F->me] = 0;
        }
    }
    KF_CALL0(resolve_locked, NULL);
    pthread_mutex_unlock(&K.mu);
    words_free(&tl_pending);
    KF_RET(false);
    KF_END;
}

static uint64_t ck_code(CheckStatus s) { return s == CK_VALID ? 1 : s == CK_INVALID ? 2 : 0; }
static CheckStatus ck_of(uint64_t v) { return v == 1 ? CK_VALID : v == 2 ? CK_INVALID : CK_UNRESOLVED; }
static uint64_t cv_code(ConvStatus s) { return s == CV_EQUAL ? 1 : s == CV_UNEQUAL ? 2 : 0; }
static ConvStatus cv_of(uint64_t v) { return v == 1 ? CV_EQUAL : v == 2 ? CV_UNEQUAL : CV_UNRESOLVED; }

/* ------------------------------------------------------------------ */
/* faces: clauses and clause substitution                               */

/* the clauses of a face, each as a face; *out is owned by the caller */
#define clauses_of_PARAMS(X) X(FaceId, chi) X(FaceId **, out)
KF_DECL_DROP(clauses_of, size_t, clauses_of_PARAMS, clauses_of_drop, Dnf d, one; FaceId *cs; size_t i, n;)
static void clauses_of_drop(clauses_of_F *F) { dnf_free(&F->d); dnf_free(&F->one); free(F->cs); F->cs = NULL; }
KF_STEP(clauses_of) {
    KF_BEGIN(clauses_of);
    KF_CALL(fc_to_dnf, NULL, F->chi, &F->d);
    F->cs = malloc((F->d.n ? F->d.n : 1) * sizeof(FaceId));
    for (F->i = 0; F->i < F->d.n; F->i++) {
        dnf_init(&F->one);
        KF_CALL(dnf_add_clause, NULL, &F->one, F->d.c[F->i].a, F->d.c[F->i].n);
        KF_CALL(fc_from_dnf, &F->cs[F->i], &F->one);
    }
    F->n = F->d.n;
    dnf_free(&F->d);
    *F->out = F->cs; F->cs = NULL;
    KF_RET(F->n);
    KF_END;
}

/* the endpoints fixed by a single clause, as a dimension map */
#define clause_map_PARAMS(X) X(FaceId, C)
KF_DECL_DROP(clause_map, MapId, clause_map_PARAMS, clause_map_drop, Dnf d; MapBuilder b; size_t k; IntervalId e; MapId m;)
static void clause_map_drop(clause_map_F *F) { dnf_free(&F->d); words_free(&F->b.t); words_free(&F->b.d); }
KF_STEP(clause_map) {
    KF_BEGIN(clause_map);
    KF_CALL(fc_to_dnf, NULL, F->C, &F->d);
    mapb_init(&F->b);
    if (F->d.n == 1) KF_MAPB_RESERVE(&F->b, 0, F->d.c[0].n);
    if (F->d.n == 1) for (F->k = 0; F->k < F->d.c[0].n; F->k++) {
        if (FC_LIT_EPS(F->d.c[0].a[F->k])) KF_CALL0(iv_one, &F->e); else KF_CALL0(iv_zero, &F->e);
        mapb_dim(&F->b, FC_LIT_DIM(F->d.c[0].a[F->k]), F->e);
    }
    dnf_free(&F->d);
    KX(mapb_finish, &F->m, &F->b);
    KF_RET(F->m);
    KF_END;
}
#define iv_equal_under_PARAMS(X) X(FaceId, C) X(IntervalId, r) X(IntervalId, s)
KF_DECL(iv_equal_under, bool, iv_equal_under_PARAMS, MapId m; IntervalId a, b;)
KF_STEP(iv_equal_under) {
    KF_BEGIN(iv_equal_under);
    KF_CALL(clause_map, &F->m, F->C);
    KX(iv_reindex, &F->a, F->r, F->m); KX(iv_reindex, &F->b, F->s, F->m);
    KF_RET(F->a == F->b);
    KF_END;
}
#define fc_equal_under_PARAMS(X) X(FaceId, C) X(FaceId, a) X(FaceId, b)
KF_DECL(fc_equal_under, bool, fc_equal_under_PARAMS, FaceId x, y;)
KF_STEP(fc_equal_under) {
    KF_BEGIN(fc_equal_under);
    KF_CALL(fc_meet, &F->x, F->C, F->a); KF_CALL(fc_meet, &F->y, F->C, F->b);
    KF_RET(F->x == F->y);
    KF_END;
}

static bool dims_declared(ContextId G, DimSetId S) {
    size_t n; const uint64_t *ds = dimset_get(S, &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_dim(G, ds[k])) return false;
    return true;
}
#define face_dims_PARAMS(X) X(FaceId, f)
KF_DECL_DROP(face_dims, DimSetId, face_dims_PARAMS, face_dims_drop, Words w; DimSetId s;)
static void face_dims_drop(face_dims_F *F) { words_free(&F->w); }
KF_STEP(face_dims) {
    KF_BEGIN(face_dims);
    words_init(&F->w); fc_dims(F->f, &F->w);
    KF_CALL(dimset_make, &F->s, F->w.w, F->w.n);
    words_free(&F->w);
    KF_RET(F->s);
    KF_END;
}
#define iv_dimset_PARAMS(X) X(IntervalId, r)
KF_DECL_DROP(iv_dimset, DimSetId, iv_dimset_PARAMS, iv_dimset_drop, Words w; DimSetId s;)
static void iv_dimset_drop(iv_dimset_F *F) { words_free(&F->w); }
KF_STEP(iv_dimset) {
    KF_BEGIN(iv_dimset);
    words_init(&F->w); iv_dims(F->r, &F->w);
    KF_CALL(dimset_make, &F->s, F->w.w, F->w.n);
    words_free(&F->w);
    KF_RET(F->s);
    KF_END;
}

/* ------------------------------------------------------------------ */
/* fresh comparison identities (distinct owner namespace)               */

/* keyed by the comparison request (both sides and the expected type head) */
#define conv_var_PARAMS(X) X(RefId, l) X(RefId, r) X(RefId, head) X(uint64_t, slot) X(RefId, type)
KF_DECL(conv_var, TermVarId, conv_var_PARAMS, KeyWord kw[5]; TermVarId x;)
KF_STEP(conv_var) {
    KF_BEGIN(conv_var);
    F->kw[0] = (KeyWord){ KW_CONST, 5000 }; F->kw[1] = (KeyWord){ KW_REF, F->l }; F->kw[2] = (KeyWord){ KW_REF, F->r }; F->kw[3] = (KeyWord){ KW_REF, F->head }; F->kw[4] = (KeyWord){ KW_CONST, F->slot };
    KX(fresh_term_keyed, &F->x, F->kw, 5, F->type);
    KF_RET(F->x);
    KF_END;
}
#define conv_dim_PARAMS(X) X(RefId, l) X(RefId, r) X(uint64_t, slot)
KF_DECL(conv_dim, DimVarId, conv_dim_PARAMS, KeyWord kw[4]; DimVarId j;)
KF_STEP(conv_dim) {
    KF_BEGIN(conv_dim);
    F->kw[0] = (KeyWord){ KW_CONST, 5001 }; F->kw[1] = (KeyWord){ KW_REF, F->l }; F->kw[2] = (KeyWord){ KW_REF, F->r }; F->kw[3] = (KeyWord){ KW_CONST, F->slot };
    KF_CALL(nominal_var, &F->j, F->kw, 4, 3, S_DIM, 0, 0, false);
    KF_RET(F->j);
    KF_END;
}

/* ------------------------------------------------------------------ */
/* observation helpers                                                  */

#define observe_PARAMS(X) X(FaceId, C) X(RefId, t) X(EvalResult **, out) X(const char **, reason)
KF_DECL(observe, CheckStatus, observe_PARAMS, WhnfStatus st; EvalResult *r; EntryId e;)
KF_STEP(observe) {
    KF_BEGIN(observe);
    KX(whnf, &F->r, F->t, F->C, &F->st);
    if (F->st == W_OK) { KX(eval_entry_lookup, &F->e, F->t, F->C); KF_CALL(note_entry, NULL, F->e); *F->out = F->r; KF_RET(CK_VALID); }
    *F->out = NULL;
    if (F->st == W_STUCK) { *F->reason = "unresolved: weak-head observation did not complete (cyclic or suspended demand)"; KF_RET(CK_UNRESOLVED); }
    *F->reason = F->r && F->r->message ? F->r->message : "invalid observation";
    KF_RET(CK_INVALID);
    KF_END;
}

/* weak-head observe a type and require a given introduction tag */
#define observe_head_PARAMS(X) X(FaceId, C) X(RefId, T) X(Tag, want) X(RefId *, head) X(const char **, reason)
KF_DECL_DROP(observe_head, CheckStatus, observe_head_PARAMS, observe_head_drop, EvalResult *r; CheckStatus s; Head h;)
static void observe_head_drop(observe_head_F *F) { head_free(&F->h); }
KF_STEP(observe_head) {
    KF_BEGIN(observe_head);
    KF_CALL(observe, &F->s, F->C, F->T, &F->r, F->reason);
    if (F->s != CK_VALID) KF_RET(F->s);
    if (F->r->cls != R_INTRODUCTION) { *F->reason = "expected a type former, found a neutral or system"; KF_RET(CK_INVALID); }
    KXV(open_ref, F->r->ref, &F->h);
    { Tag tag = F->h.tag; head_free(&F->h);
      if (tag != F->want) { *F->reason = "type former mismatch"; KF_RET(CK_INVALID); } }
    *F->head = F->r->ref;
    KF_RET(CK_VALID);
    KF_END;
}

static void infer_clause_push(KStack *ks, CheckStatus *ret, ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static void check_clause_push(KStack *ks, CheckStatus *ret, ContextId G, FaceId C, RefId t, RefId A, const char **reason);
static void conv_type_clause_push(KStack *ks, ConvStatus *ret, ContextId G, FaceId C, RefId A, RefId B);
static void conv_term_clause_push(KStack *ks, ConvStatus *ret, ContextId G, FaceId C, RefId t, RefId u, RefId A);
static void spine_push(KStack *ks, ConvStatus *ret, ContextId G, FaceId C, RefId n1, RefId n2);
static void infer_head_push(KStack *ks, CheckStatus *ret, ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static void validate_symbol_push(KStack *ks, CheckStatus *ret, SymbolId s, const char **reason);

/* the universe level of a type under a clause */
#define level_of_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, A) X(uint64_t *, lvl) X(const char **, reason)
KF_DECL_DROP(level_of, CheckStatus, level_of_PARAMS, level_of_drop, RefId T, U; CheckStatus s; Head h;)
static void level_of_drop(level_of_F *F) { head_free(&F->h); }
KF_STEP(level_of) {
    KF_BEGIN(level_of);
    KF_CALL(infer_clause, &F->s, F->G, F->C, F->A, &F->T, F->reason);
    if (F->s != CK_VALID) KF_RET(F->s);
    KF_CALL(observe_head, &F->s, F->C, F->T, T_UNIVERSE, &F->U, F->reason);
    if (F->s != CK_VALID) { if (F->s == CK_INVALID) *F->reason = "not a type: its type is not a universe"; KF_RET(F->s); }
    KXV(open_ref, F->U, &F->h); *F->lvl = F->h.payload; head_free(&F->h);
    KF_RET(CK_VALID);
    KF_END;
}

/* ------------------------------------------------------------------ */
/* contexts                                                             */

KF_DECL_EXT_DROP(origin_context, ContextId, origin_context_PARAMS, origin_context_drop, CtxDecl *decls; bool *placed; ContextId ctx;)
static void origin_context_drop(origin_context_F *F) { free(F->decls); F->decls = NULL; free(F->placed); F->placed = NULL; }
KF_STEP(origin_context) {
    KF_BEGIN(origin_context);
    {
        size_t nd, nt;
        const uint64_t *ds = dimset_get(origin_fd(F->C), &nd);
        const uint64_t *xs = varset_get(origin_ft(F->C), &nt);
        F->decls = malloc((nd + nt + 1) * sizeof(CtxDecl));
        size_t n = 0;
        for (size_t k = 0; k < nd; k++) { F->decls[n].sort = S_DIM; F->decls[n].id = ds[k]; F->decls[n].type = 0; n++; }
        /* term variables in dependency order: a variable follows the free
         * variables of its declared type */
        F->placed = calloc(nt ? nt : 1, sizeof(bool));
        size_t done = 0;
        while (done < nt) {
            bool progress = false;
            for (size_t k = 0; k < nt; k++) {
                if (F->placed[k]) continue;
                size_t m; const uint64_t *fv = varset_get(ref_freevars(term_var_type(xs[k])), &m);
                bool ready = true;
                for (size_t q = 0; q < m && ready; q++) { bool found = false; for (size_t j = 0; j < nt; j++) if (xs[j] == fv[q] && F->placed[j]) found = true; if (!found) ready = false; }
                if (!ready) continue;
                F->decls[n].sort = S_TERM; F->decls[n].id = xs[k]; F->decls[n].type = term_var_type(xs[k]); n++;
                F->placed[k] = true; done++; progress = true;
            }
            require(progress, "cyclic declaration dependency in origin boundary");
        }
        free(F->placed); F->placed = NULL;
        KX(context_make, &F->ctx, n, F->decls, origin_required(F->C));
    }
    free(F->decls); F->decls = NULL;
    KF_RET(F->ctx);
    KF_END;
}
KF_SYNC_DEF(origin_context, ContextId, origin_context_PARAMS, origin_context(OriginId C))

/* the claim-owning judgment frames share one protocol: a root entry (ENTER),
 * a claim acquisition, the body, the release, the root exit (LEAVE) and the
 * settlement retry. `owns` and `entered` record what a drop must release. */
#define OWNED_FIELDS size_t cl; uint64_t v; const char *why; Acq a; bool owns, entered, settled;
#define OWNED_DROP(F) do { if ((F)->owns) { claim_abandon((F)->cl); (F)->owns = false; } if ((F)->entered) { top_abandon(); (F)->entered = false; } } while (0)
#define ENTER_F() do { top_enter(); F->entered = true; } while (0)
#define LEAVE_F() do { KF_CALL0(top_leave, NULL); F->entered = false; } while (0)
#define SETTLED_F() KF_CALL0(top_settled, &F->settled)
#define RELEASE_F(code, why, aux) do { F->owns = false; KF_CALL(claim_release, NULL, F->cl, (code), (why), (aux)); } while (0)

KF_DECL_EXT_DROP(check_context, CheckStatus, check_context_PARAMS, check_context_drop, OWNED_FIELDS uint64_t key[1]; CheckStatus st; size_t n, k, j, nd, npd, nc, c; FaceId assumption, proj, req2; uint64_t *dims, *pd; CtxDecl *prefix; DimSetId all, fds, pds, sup; ContextId P; RefId decl; RefId both[2]; int w; FaceId *cs; uint64_t l; ConvStatus cv; CtxDecl d;)
static void check_context_drop(check_context_F *F) { free(F->dims); F->dims = NULL; free(F->pd); F->pd = NULL; free(F->prefix); F->prefix = NULL; free(F->cs); F->cs = NULL; OWNED_DROP(F); }
KF_STEP(check_context) {
    KF_BEGIN(check_context);
  for (;;) {
    F->key[0] = F->G; F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_CTX, F->key, 1);
    ENTER_F();
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, NULL);
    if (F->a == ACQ_DONE) { LEAVE_F(); if (F->v != 1) *F->reason = F->why; SETTLED_F(); if (F->settled) KF_RET(ck_of(F->v)); continue; }
    if (F->a == ACQ_CYCLE) { LEAVE_F(); SETTLED_F(); *F->reason = "unresolved: context validation depends on itself"; KF_RET(CK_UNRESOLVED); }
    F->owns = true;
    F->st = CK_VALID;
    F->n = context_size(F->G);
    F->assumption = context_assumption(F->G);
    /* 1. unique identities; the assumption uses declared dimensions */
    F->dims = malloc((F->n ? F->n : 1) * sizeof(uint64_t)); F->nd = 0;
    for (F->k = 0; F->k < F->n && F->st == CK_VALID; F->k++) {
        CtxDecl d = context_decl(F->G, F->k);
        for (size_t j = 0; j < F->k; j++) { CtxDecl e = context_decl(F->G, j); if (e.sort == d.sort && e.id == d.id) { *F->reason = "duplicate declaration"; F->st = CK_INVALID; } }
        if (d.sort == S_DIM) F->dims[F->nd++] = d.id;
    }
    if (F->st == CK_VALID) {
        KF_CALL(dimset_make, &F->all, F->dims, F->nd);
        KF_CALL(face_dims, &F->fds, F->assumption);
        { size_t m; const uint64_t *fd = dimset_get(F->fds, &m);
          for (size_t q = 0; q < m; q++) if (!dimset_contains(F->all, fd[q])) { *F->reason = "assumption mentions an undeclared dimension"; F->st = CK_INVALID; } }
    }
    /* 2. each term declaration's type and required face use only the prefix;
     * the type is a type under the assumption projected to the prefix dims,
     * and it is compatible (convertible under each clause) with the
     * variable's recorded declaration (§2, §33 item 3) */
    for (F->k = 0; F->k < F->n && F->st == CK_VALID; F->k++) {
        F->d = context_decl(F->G, F->k);
        if (F->d.sort != S_TERM) continue;
        F->prefix = malloc((F->k ? F->k : 1) * sizeof(CtxDecl));
        F->pd = malloc((F->k ? F->k : 1) * sizeof(uint64_t)); F->npd = 0;
        for (size_t j = 0; j < F->k; j++) { F->prefix[j] = context_decl(F->G, j); if (F->prefix[j].sort == S_DIM) F->pd[F->npd++] = F->prefix[j].id; }
        KF_CALL(dimset_make, &F->pds, F->pd, F->npd);
        { size_t m; const uint64_t *S = dimset_get(F->pds, &m); KF_CALL(fc_project, &F->proj, F->assumption, S, m); }
        KX(context_make, &F->P, F->k, F->prefix, F->proj);
        free(F->prefix); F->prefix = NULL; free(F->pd); F->pd = NULL;
        F->decl = term_var_type(F->d.id);
        F->both[0] = F->d.type; F->both[1] = F->decl;
        for (F->w = 0; F->w < 2 && F->st == CK_VALID; F->w++) {
            size_t m; const uint64_t *fv = varset_get(ref_freevars(F->both[F->w]), &m);
            for (size_t q = 0; q < m && F->st == CK_VALID; q++) if (!context_declares_term(F->P, fv[q], NULL)) { *F->reason = "declaration type mentions a variable not declared earlier"; F->st = CK_INVALID; }
            if (F->st == CK_VALID && !dims_declared(F->P, ref_support(F->both[F->w]))) { *F->reason = "declaration type mentions a dimension not declared earlier"; F->st = CK_INVALID; }
        }
        if (F->st == CK_VALID) { KF_CALL(face_dims, &F->sup, term_var_required(F->d.id)); if (!dims_declared(F->P, F->sup)) { *F->reason = "declaration's required face mentions a dimension not declared earlier"; F->st = CK_INVALID; } }
        if (F->st == CK_VALID) {
            /* §59.2: a declaration partial on φ_x forms under the projected
             * prefix assumption conjoined with φ_x (its type may use earlier
             * declarations available only there); scope was checked above */
            KF_CALL(fc_meet, &F->req2, F->proj, term_var_required(F->d.id));
            KF_CALL(clauses_of, &F->nc, F->req2, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(level_of, &F->st, F->P, F->cs[F->c], F->d.type, &F->l, F->reason);
                if (F->st == CK_VALID && F->decl != F->d.type) {
                    KF_CALL(level_of, &F->st, F->P, F->cs[F->c], F->decl, &F->l, F->reason);
                    if (F->st != CK_VALID) break;
                    KF_CALL(conv_type_clause, &F->cv, F->P, F->cs[F->c], F->d.type, F->decl);
                    if (F->cv == CV_UNEQUAL) { *F->reason = "declared type is not convertible to the variable's declaration"; F->st = CK_INVALID; }
                    else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: declaration type compatibility"; F->st = CK_UNRESOLVED; }
                }
            }
            free(F->cs); F->cs = NULL;
        }
    }
    free(F->dims); F->dims = NULL;
    RELEASE_F(ck_code(F->st), *F->reason, NULL);
    LEAVE_F();
    SETTLED_F();
    if (F->settled) KF_RET(F->st);
  }
    KF_END;
}
KF_SYNC_DEF(check_context, CheckStatus, check_context_PARAMS, check_context(ContextId G, const char **reason))

/* the judgment Γ;χ: the context carries χ as its assumption, so that
 * declaration types are validated under the same face they are used under */
#define under_PARAMS(X) X(ContextId, G) X(FaceId, C)
KF_DECL_DROP(under, ContextId, under_PARAMS, under_drop, CtxDecl *ds; ContextId out;)
static void under_drop(under_F *F) { free(F->ds); F->ds = NULL; }
KF_STEP(under) {
    KF_BEGIN(under);
    if (context_assumption(F->G) == F->C) KF_RET(F->G);
    { size_t n = context_size(F->G);
      F->ds = malloc((n ? n : 1) * sizeof(CtxDecl));
      for (size_t k = 0; k < n; k++) F->ds[k] = context_decl(F->G, k);
      KX(context_make, &F->out, n, F->ds, F->C); }
    free(F->ds); F->ds = NULL;
    KF_RET(F->out);
    KF_END;
}

/* ------------------------------------------------------------------ */
/* typed maps and origins (substitution lemma)                          */

KF_DECL_EXT_DROP(check_map, CheckStatus, check_map_PARAMS, check_map_drop, OWNED_FIELDS uint64_t key[5]; CheckStatus st; size_t n, k, nc, c; CtxDecl d; RefId image, Asub; FaceId where, tr, chis; DimSetId ds; IntervalId im; FaceId *cs; bool ok, ent;)
static void check_map_drop(check_map_F *F) { free(F->cs); F->cs = NULL; OWNED_DROP(F); }
KF_STEP(check_map) {
    KF_BEGIN(check_map);
  KF_CALL(under, &F->Delta, F->Delta, F->psi); KF_CALL(under, &F->Gamma, F->Gamma, F->chi);
  for (;;) {
    F->key[0] = F->Delta; F->key[1] = F->psi; F->key[2] = F->sigma; F->key[3] = F->Gamma; F->key[4] = F->chi; F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_MAP, F->key, 5);
    ENTER_F();
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, NULL);
    if (F->a == ACQ_DONE) { LEAVE_F(); if (F->v != 1) *F->reason = F->why; SETTLED_F(); if (F->settled) KF_RET(ck_of(F->v)); continue; }
    if (F->a == ACQ_CYCLE) { LEAVE_F(); SETTLED_F(); *F->reason = "unresolved: map validation depends on itself"; KF_RET(CK_UNRESOLVED); }
    F->owns = true;
    KF_CALL(check_context, &F->st, F->Gamma, F->reason);
    if (F->st == CK_VALID) KF_CALL(check_context, &F->st, F->Delta, F->reason);
    F->n = context_size(F->Gamma);
    for (F->k = 0; F->k < F->n && F->st == CK_VALID; F->k++) {
        F->d = context_decl(F->Gamma, F->k);
        if (F->d.sort == S_DIM) {
            /* the dimension image is an interval over the source dimensions */
            KX(map_dim_image, &F->im, F->sigma, F->d.id);
            KF_CALL(iv_dimset, &F->ds, F->im);
            if (!dims_declared(F->Delta, F->ds)) { *F->reason = "dimension image mentions an undeclared source dimension"; F->st = CK_INVALID; }
            continue;
        }
        /* the term image (the identity image when the entry is absent) is in
         * the source scope whatever the source face: only the typing
         * obligations below are vacuous on false (§33) */
        KX(map_term_image, &F->image, F->sigma, F->d.id);
        KX(ref_validate, &F->ok, F->image, F->reason);
        if (!F->ok) { F->st = CK_INVALID; break; }
        { size_t m; const uint64_t *fv = varset_get(ref_freevars(F->image), &m);
          for (size_t q = 0; q < m && F->st == CK_VALID; q++) if (!context_declares_term(F->Delta, fv[q], NULL)) { *F->reason = "term image mentions a variable not declared in the source context"; F->st = CK_INVALID; }
          if (F->st == CK_VALID && !dims_declared(F->Delta, ref_support(F->image))) { *F->reason = "term image mentions a dimension not declared in the source context"; F->st = CK_INVALID; } }
        if (F->st != CK_VALID) break;
        /* the target declaration's required-face obligation: a declaration
         * partial on phi_x is only used under phi_x in the target, so its
         * image is checked against A[sigma] under psi ∧ phi_x[sigma] */
        KX(reindex, &F->Asub, F->d.type, F->sigma);
        KX(fc_reindex, &F->tr, term_var_required(F->d.id), F->sigma);
        KF_CALL(fc_meet, &F->where, F->psi, F->tr);
        KF_CALL(clauses_of, &F->nc, F->where, &F->cs);
        for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) KF_CALL(check_clause, &F->st, F->Delta, F->cs[F->c], F->image, F->Asub, F->reason);
        free(F->cs); F->cs = NULL;
    }
    if (F->st == CK_VALID) {
        KX(fc_reindex, &F->chis, F->chi, F->sigma);
        KF_CALL(fc_entails, &F->ent, F->psi, F->chis);
        if (!F->ent) { *F->reason = "source face does not entail the substituted target assumption"; F->st = CK_INVALID; }
    }
    RELEASE_F(ck_code(F->st), *F->reason, NULL);
    LEAVE_F();
    SETTLED_F();
    if (F->settled) KF_RET(F->st);
  }
    KF_END;
}
KF_SYNC_DEF(check_map, CheckStatus, check_map_PARAMS, check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason))

KF_DECL_EXT_DROP(check_origin, CheckStatus, check_origin_PARAMS, check_origin_drop, OWNED_FIELDS uint64_t key[1]; uint64_t aux[3]; ContextId ctx; FaceId req; RefId type, t; CheckStatus st; FaceId *cs; size_t nc, c; RefId *types; MapId id; bool same;)
static void check_origin_drop(check_origin_F *F) { free(F->cs); F->cs = NULL; free(F->types); F->types = NULL; OWNED_DROP(F); }
KF_STEP(check_origin) {
    KF_BEGIN(check_origin);
  for (;;) {
    F->key[0] = F->C; F->aux[0] = F->aux[1] = F->aux[2] = 0; F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_ORIGIN, F->key, 1);
    ENTER_F();
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, F->aux);
    if (F->a == ACQ_DONE) {
        LEAVE_F();
        SETTLED_F();
        if (!F->settled) continue;
        if (F->v == 1) { if (F->ctx_out) *F->ctx_out = F->aux[0]; if (F->required_out) *F->required_out = F->aux[1]; if (F->type_out) *F->type_out = F->aux[2]; KF_RET(CK_VALID); }
        *F->reason = F->why; KF_RET(ck_of(F->v));
    }
    if (F->a == ACQ_CYCLE) { LEAVE_F(); SETTLED_F(); *F->reason = "unresolved: origin validation depends on itself (cyclic dependency)"; KF_RET(CK_UNRESOLVED); }
    F->owns = true;
    KF_CALL(origin_context, &F->ctx, F->C);
    F->req = origin_required(F->C);
    F->type = 0;
    KF_CALL(check_context, &F->st, F->ctx, F->reason);
    if (F->st == CK_VALID) {
        KF_CALL0(map_identity, &F->id);
        KX(make_view, &F->t, F->C, F->id);
        /* a system's own required face is its coverage; the body is checked under it */
        KF_CALL(clauses_of, &F->nc, F->req, &F->cs);
        F->types = malloc((F->nc ? F->nc : 1) * sizeof(RefId));
        for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) KF_CALL(infer_head, &F->st, F->ctx, F->cs[F->c], F->t, &F->types[F->c], F->reason);
        if (F->st == CK_VALID) {
            F->same = true;
            for (size_t c = 1; c < F->nc; c++) if (F->types[c] != F->types[0]) F->same = false;
            if (F->nc == 0) KX(mk_system, &F->type, 0, NULL, NULL);            /* required face false: vacuous */
            else if (F->same) F->type = F->types[0];
            else KX(mk_system, &F->type, F->nc, F->cs, F->types);
        }
        free(F->types); F->types = NULL; free(F->cs); F->cs = NULL;
    }
    F->aux[0] = F->ctx; F->aux[1] = F->req; F->aux[2] = F->type;
    RELEASE_F(ck_code(F->st), *F->reason, F->aux);
    LEAVE_F();
    SETTLED_F();
    if (!F->settled) continue;
    if (F->st == CK_VALID) { if (F->ctx_out) *F->ctx_out = F->ctx; if (F->required_out) *F->required_out = F->req; if (F->type_out) *F->type_out = F->type; }
    KF_RET(F->st);
  }
    KF_END;
}
KF_SYNC_DEF(check_origin, CheckStatus, check_origin_PARAMS, check_origin(OriginId C, ContextId *ctx_out, FaceId *required_out, RefId *type_out, const char **reason))

/* ------------------------------------------------------------------ */
/* inference                                                            */

#define glue_data_ok_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e) X(uint64_t *, lvl) X(const char **, reason)
KF_DECL_DROP(glue_data_ok, CheckStatus, glue_data_ok_PARAMS, glue_data_ok_drop, CheckStatus st; DimSetId fd; FaceId Ca; FaceId *cs; size_t nc, c; uint64_t lT; RefId eq;)
static void glue_data_ok_drop(glue_data_ok_F *F) { free(F->cs); F->cs = NULL; }
KF_STEP(glue_data_ok) {
    KF_BEGIN(glue_data_ok);
    KF_CALL(level_of, &F->st, F->G, F->C, F->A, F->lvl, F->reason);
    if (F->st != CK_VALID) KF_RET(F->st);
    KF_CALL(face_dims, &F->fd, F->alpha);
    if (!dims_declared(F->G, F->fd)) { *F->reason = "Glue face mentions an undeclared dimension"; KF_RET(CK_INVALID); }
    KF_CALL(fc_meet, &F->Ca, F->C, F->alpha);
    if (fc_is_false(F->Ca)) KF_RET(CK_VALID);              /* vacuous */
    KF_CALL(clauses_of, &F->nc, F->Ca, &F->cs);
    for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
        KF_CALL(level_of, &F->st, F->G, F->cs[F->c], F->T, &F->lT, F->reason);
        if (F->st == CK_VALID && F->lT != *F->lvl) { *F->reason = "Glue fibre type is not in the base's universe"; F->st = CK_INVALID; }
        if (F->st == CK_VALID) { KX(mk_equiv, &F->eq, F->lT, *F->lvl, F->T, F->A); KF_CALL(check_clause, &F->st, F->G, F->cs[F->c], F->e, F->eq, F->reason); }
    }
    free(F->cs); F->cs = NULL;
    KF_RET(F->st);
    KF_END;
}

/* §59.1: every required type position carries its level; a missing or
 * differing annotation is INVALID */
static bool level_ok1(uint64_t levels, uint64_t inferred) { return levels_first(levels) == inferred; }
static bool level_ok2(uint64_t levels, uint64_t i, uint64_t j) { return levels_first(levels) == i && levels_second(levels) == j; }
static const char *level_why(uint64_t levels, const char *differs) { return levels == LEVELS_NONE || levels_first(levels) == LEVEL_NONE ? "missing universe annotation at a required type position (§59.1)" : differs; }

#define infer_head_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, t) X(RefId *, type) X(const char **, reason)
KF_DECL_DROP(infer_head, CheckStatus, infer_head_PARAMS, infer_head_drop,
    CheckStatus st, ls; Head h, hp; uint64_t i, j, l, la, lb, lT, ld, lc, lv; TermOpen o; DimOpen dop, fam, tube;
    RefId B, Tf, P, dom, cod, A, Bt, T, e, tt, a, v, a0, A0, Ar, x0, x1, eqt, Asub, gt, fstx, appx, tmp; TermVarId x; FaceId alpha, phi, Ca, Cp, uni, Ck, Ckl, mkl;
    ContextId Gx, Gj, Gs; FaceId *cs; size_t nc, c, nb, sel, k, kk, np; RefId *types; ConvStatus cv, c1, c2; IntervalId z, one;
    DimSetId fd; bool ok, ent; SymbolId s; uint64_t id; int dir; MapId sigma; const CompiledTransform *tr; TermVarId ty; FaceId ftrue;)
static void infer_head_drop(infer_head_F *F) { head_free(&F->h); head_free(&F->hp); free(F->cs); F->cs = NULL; free(F->types); F->types = NULL; }
KF_STEP(infer_head) {
    KF_BEGIN(infer_head);
    if (!budget_ok()) { *F->reason = R_BUDGET; KF_RET(CK_UNRESOLVED); }
    KF_CALL(under, &F->G, F->G, F->C);
    if (ref_is_var(F->t)) {
        TermVarId x = ref_var_id(F->t);
        RefId ty;
        if (!context_declares_term(F->G, x, &ty)) { *F->reason = "unbound variable"; KF_RET(CK_INVALID); }
        F->ty = ty; F->x = x;
        KF_CALL(fc_entails, &F->ent, F->C, term_var_required(F->x));
        if (!F->ent) { *F->reason = "variable used outside its required face"; KF_RET(CK_INVALID); }
        *F->type = F->ty;
        KF_RET(CK_VALID);
    }
    KXV(open_ref, F->t, &F->h);
    F->st = CK_VALID;
    switch (F->h.tag) {
    case T_UNIVERSE: KX(level_succ, &F->lv, F->h.payload); KX(mk_universe, F->type, F->lv); break;   /* checked successor: overflow is a host failure (§59.1) */
    case T_PI: case T_SIGMA: {
        KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[0].id, &F->i, F->reason);
        if (F->st != CK_VALID) break;
        KX(resolve_term_binder, &F->o, F->t, 0, 1);
        KX(context_extend_term, &F->Gx, F->G, F->o.x, F->o.type);
        KF_CALL(level_of, &F->st, F->Gx, F->C, F->o.body, &F->j, F->reason);
        if (F->st == CK_VALID && !level_ok2(F->h.levels, F->i, F->j)) { *F->reason = level_why(F->h.levels, "universe annotation differs from the formation levels"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) KX(mk_universe, F->type, F->i > F->j ? F->i : F->j);
        break;
    }
    case T_LAM: {
        KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[0].id, &F->i, F->reason);
        if (F->st != CK_VALID) break;
        if (!level_ok1(F->h.levels, F->i)) { *F->reason = level_why(F->h.levels, "lambda domain level annotation differs"); F->st = CK_INVALID; break; }
        KX(resolve_term_binder, &F->o, F->t, 0, 1);
        KX(context_extend_term, &F->Gx, F->G, F->o.x, F->o.type);
        KF_CALL(infer_clause, &F->st, F->Gx, F->C, F->o.body, &F->B, F->reason);
        if (F->st == CK_VALID) KF_CALL(level_of, &F->st, F->Gx, F->C, F->B, &F->j, F->reason);
        if (F->st == CK_VALID) KX(mk_pi_lv, F->type, F->i, F->j, F->o.x, F->o.type, F->B);
        break;
    }
    case T_APP: {
        KF_CALL(infer_clause, &F->st, F->G, F->C, F->h.f[0].id, &F->Tf, F->reason);
        if (F->st != CK_VALID) break;
        KF_CALL(observe_head, &F->st, F->C, F->Tf, T_PI, &F->P, F->reason);
        if (F->st != CK_VALID) { if (F->st == CK_INVALID) *F->reason = "application of a non-function"; break; }
        KXV(open_ref, F->P, &F->hp); F->dom = F->hp.f[0].id; head_free(&F->hp);
        KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[1].id, F->dom, F->reason);
        if (F->st == CK_VALID) KX(apply_term_binder, F->type, F->P, 0, 1, F->h.f[1].id);
        break;
    }
    case T_PAIR: {
        if (F->h.n == 3) {
            /* annotated: the stored Σ type is the expected type; validate the
             * annotation as a type and the form against it (§33) */
            KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[2].id, &F->l, F->reason);
            if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "pair annotation level differs"); F->st = CK_INVALID; }
            if (F->st == CK_VALID) KF_CALL(check_clause, &F->st, F->G, F->C, F->t, F->h.f[2].id, F->reason);
            if (F->st == CK_VALID) *F->type = F->h.f[2].id;
            break;
        }
        KF_CALL(infer_clause, &F->st, F->G, F->C, F->h.f[0].id, &F->A, F->reason);
        if (F->st == CK_VALID) KF_CALL(infer_clause, &F->st, F->G, F->C, F->h.f[1].id, &F->Bt, F->reason);
        if (F->st == CK_VALID) KF_CALL(level_of, &F->st, F->G, F->C, F->A, &F->la, F->reason);
        if (F->st == CK_VALID) KF_CALL(level_of, &F->st, F->G, F->C, F->Bt, &F->lb, F->reason);
        if (F->st == CK_VALID) { KF_CALL(conv_var, &F->x, F->t, F->t, F->A, 0, F->A); KX(mk_sigma_lv, F->type, F->la, F->lb, F->x, F->A, F->Bt); }
        break;
    }
    case T_FST: case T_SND: {
        KF_CALL(infer_clause, &F->st, F->G, F->C, F->h.f[0].id, &F->Tf, F->reason);
        if (F->st != CK_VALID) break;
        KF_CALL(observe_head, &F->st, F->C, F->Tf, T_SIGMA, &F->P, F->reason);
        if (F->st != CK_VALID) { if (F->st == CK_INVALID) *F->reason = "projection of a non-pair"; break; }
        KXV(open_ref, F->P, &F->hp); F->dom = F->hp.f[0].id; head_free(&F->hp);
        if (F->h.tag == T_FST) *F->type = F->dom;
        else { KX(mk_fst, &F->fstx, F->h.f[0].id); KX(apply_term_binder, F->type, F->P, 0, 1, F->fstx); }
        break;
    }
    case T_PATH: {
        KX(resolve_dim_binder, &F->dop, F->t, 0, 0);
        KX(context_extend_dim, &F->Gx, F->G, F->dop.j);
        KF_CALL(level_of, &F->st, F->Gx, F->C, F->dop.body, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "path family level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) { KF_CALL0(iv_zero, &F->z); KX(reindex_dim, &F->x0, F->dop.body, F->dop.j, F->z); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[1].id, F->x0, F->reason); }
        if (F->st == CK_VALID) { KF_CALL0(iv_one, &F->one); KX(reindex_dim, &F->x1, F->dop.body, F->dop.j, F->one); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[2].id, F->x1, F->reason); }
        if (F->st == CK_VALID) KX(mk_universe, F->type, F->l);
        break;
    }
    case T_PLAM: {
        KX(resolve_dim_binder, &F->dop, F->t, 0, 0);
        KX(context_extend_dim, &F->Gx, F->G, F->dop.j);
        KF_CALL(infer_clause, &F->st, F->Gx, F->C, F->dop.body, &F->B, F->reason);
        if (F->st == CK_VALID) {
            KF_CALL(level_of, &F->ls, F->Gx, F->C, F->B, &F->lb, F->reason);
            if (F->ls != CK_VALID) { F->st = F->ls; break; }
            KF_CALL0(iv_zero, &F->z); KX(reindex_dim, &F->x0, F->dop.body, F->dop.j, F->z);
            KF_CALL0(iv_one, &F->one); KX(reindex_dim, &F->x1, F->dop.body, F->dop.j, F->one);
            KX(mk_path_lv, F->type, F->lb, F->dop.j, F->B, F->x0, F->x1);
        }
        break;
    }
    case T_PAPP: {
        KX(resolve_dim_binder, &F->dop, F->t, 0, 0);
        KX(context_extend_dim, &F->Gx, F->G, F->dop.j);
        KF_CALL(level_of, &F->st, F->Gx, F->C, F->dop.body, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "path application family level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) { KF_CALL0(iv_zero, &F->z); KX(reindex_dim, &F->x0, F->dop.body, F->dop.j, F->z); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[1].id, F->x0, F->reason); }
        if (F->st == CK_VALID) { KF_CALL0(iv_one, &F->one); KX(reindex_dim, &F->x1, F->dop.body, F->dop.j, F->one); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[2].id, F->x1, F->reason); }
        if (F->st == CK_VALID) { KF_CALL(iv_dimset, &F->fd, F->h.f[4].id); if (!dims_declared(F->G, F->fd)) { *F->reason = "path applied to an out-of-scope interval"; F->st = CK_INVALID; } }
        if (F->st == CK_VALID) { KX(mk_path_lv, &F->tmp, F->l, F->dop.j, F->dop.body, F->h.f[1].id, F->h.f[2].id); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[3].id, F->tmp, F->reason); }
        if (F->st == CK_VALID) KX(reindex_dim, F->type, F->dop.body, F->dop.j, F->h.f[4].id);
        break;
    }
    case T_GLUE_TYPE: {
        KF_CALL(glue_data_ok, &F->st, F->G, F->C, F->h.f[0].id, F->h.f[1].id, F->h.f[2].id, F->h.f[3].id, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "Glue level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) KX(mk_universe, F->type, F->l);
        break;
    }
    case T_GLUE_INTRO: {
        F->A = F->h.f[0].id; F->T = F->h.f[2].id; F->e = F->h.f[3].id; F->tt = F->h.f[4].id; F->a = F->h.f[5].id; F->alpha = F->h.f[1].id;
        KF_CALL(glue_data_ok, &F->st, F->G, F->C, F->A, F->alpha, F->T, F->e, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "glue level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) KF_CALL(check_clause, &F->st, F->G, F->C, F->a, F->A, F->reason);
        KF_CALL(fc_meet, &F->Ca, F->C, F->alpha);
        if (F->st == CK_VALID && !fc_is_false(F->Ca)) {
            KF_CALL(clauses_of, &F->nc, F->Ca, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(check_clause, &F->st, F->G, F->cs[F->c], F->tt, F->T, F->reason);
                if (F->st != CK_VALID) break;
                KX(mk_fst, &F->fstx, F->e); KX(mk_app, &F->appx, F->fstx, F->tt);
                KF_CALL(conv_term_clause, &F->cv, F->G, F->cs[F->c], F->appx, F->a, F->A);
                if (F->cv == CV_UNEQUAL) { *F->reason = "glue: e.map(t) is not the base term on the Glue face"; F->st = CK_INVALID; }
                else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: glue map agreement"; F->st = CK_UNRESOLVED; }
            }
            free(F->cs); F->cs = NULL;
        }
        if (F->st == CK_VALID) KX(mk_glue_type_lv, F->type, F->l, F->A, F->alpha, F->T, F->e);
        break;
    }
    case T_UNGLUE: {
        F->A = F->h.f[0].id; F->T = F->h.f[2].id; F->e = F->h.f[3].id; F->v = F->h.f[4].id; F->alpha = F->h.f[1].id;
        KF_CALL(glue_data_ok, &F->st, F->G, F->C, F->A, F->alpha, F->T, F->e, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "unglue level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) { KX(mk_glue_type_lv, &F->tmp, F->l, F->A, F->alpha, F->T, F->e); KF_CALL(check_clause, &F->st, F->G, F->C, F->v, F->tmp, F->reason); }
        if (F->st == CK_VALID) *F->type = F->A;
        break;
    }
    case T_COMP: {
        KX(resolve_dim_binder, &F->fam, F->t, 0, 0); KX(resolve_dim_binder, &F->tube, F->t, 0, 2);
        F->phi = F->h.f[1].id; F->a0 = F->h.f[3].id;
        KX(context_extend_dim, &F->Gj, F->G, F->fam.j);
        KF_CALL(level_of, &F->st, F->Gj, F->C, F->fam.body, &F->l, F->reason);
        if (F->st == CK_VALID && !level_ok1(F->h.levels, F->l)) { *F->reason = level_why(F->h.levels, "composition family level annotation differs"); F->st = CK_INVALID; }
        if (F->st == CK_VALID) { KF_CALL(face_dims, &F->fd, F->phi); if (!dims_declared(F->G, F->fd) || dimset_contains(F->fd, F->fam.j)) { *F->reason = "composition face must be in scope and independent of the bound dimension"; F->st = CK_INVALID; } }
        KF_CALL0(iv_zero, &F->z);
        KX(reindex_dim, &F->A0, F->fam.body, F->fam.j, F->z);
        if (F->st == CK_VALID) KF_CALL(check_clause, &F->st, F->G, F->C, F->a0, F->A0, F->reason);
        KF_CALL(fc_meet, &F->Cp, F->C, F->phi);
        if (F->st == CK_VALID && !fc_is_false(F->Cp)) {
            KF_CALL(clauses_of, &F->nc, F->Cp, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(check_clause, &F->st, F->Gj, F->cs[F->c], F->tube.body, F->fam.body, F->reason);
                if (F->st != CK_VALID) break;
                KX(reindex_dim, &F->x0, F->tube.body, F->tube.j, F->z);
                KF_CALL(conv_term_clause, &F->cv, F->G, F->cs[F->c], F->x0, F->a0, F->A0);
                if (F->cv == CV_UNEQUAL) { *F->reason = "composition: tube at 0 disagrees with the cap"; F->st = CK_INVALID; }
                else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: cap/tube agreement"; F->st = CK_UNRESOLVED; }
            }
            free(F->cs); F->cs = NULL;
        }
        if (F->st == CK_VALID) { KF_CALL0(iv_one, &F->one); KX(reindex_dim, F->type, F->fam.body, F->fam.j, F->one); }
        break;
    }
    case T_SYSTEM: {
        F->nb = F->h.n / 2;
        KF_CALL0(fc_false, &F->uni);
        for (F->k = 0; F->k < F->nb; F->k++) KF_CALL(fc_join, &F->uni, F->uni, F->h.f[2 * F->k].id);
        KF_CALL(fc_entails, &F->ent, F->C, F->uni);
        if (!F->ent) { *F->reason = "system does not cover the face"; F->st = CK_INVALID; break; }
        F->types = calloc(F->nb ? F->nb : 1, sizeof(RefId));
        F->sel = F->nb;
        for (F->k = 0; F->k < F->nb && F->st == CK_VALID; F->k++) {
            KF_CALL(fc_meet, &F->Ck, F->C, F->h.f[2 * F->k].id);
            KF_CALL(face_dims, &F->fd, F->h.f[2 * F->k].id);
            if (!dims_declared(F->G, F->fd)) { *F->reason = "system guard mentions an undeclared dimension"; F->st = CK_INVALID; break; }
            if (fc_is_false(F->Ck)) continue;
            KF_CALL(infer_clause, &F->st, F->G, F->Ck, F->h.f[2 * F->k + 1].id, &F->types[F->k], F->reason);
            if (F->st == CK_VALID && F->sel == F->nb) { KF_CALL(fc_entails, &F->ent, F->C, F->h.f[2 * F->k].id); if (F->ent) F->sel = F->k; }
        }
        /* overlaps: branches agree in their (convertible) types */
        for (F->k = 0; F->k < F->nb && F->st == CK_VALID; F->k++)
            for (F->kk = F->k + 1; F->kk < F->nb && F->st == CK_VALID; F->kk++) {
                KF_CALL(fc_meet, &F->mkl, F->h.f[2 * F->k].id, F->h.f[2 * F->kk].id);
                KF_CALL(fc_meet, &F->Ckl, F->C, F->mkl);
                if (fc_is_false(F->Ckl)) continue;
                KF_CALL(clauses_of, &F->nc, F->Ckl, &F->cs);
                for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                    KF_CALL(conv_type_clause, &F->cv, F->G, F->cs[F->c], F->types[F->k], F->types[F->kk]);
                    if (F->cv == CV_EQUAL) KF_CALL(conv_term_clause, &F->cv, F->G, F->cs[F->c], F->h.f[2 * F->k + 1].id, F->h.f[2 * F->kk + 1].id, F->types[F->k]);
                    if (F->cv == CV_UNEQUAL) { *F->reason = "system branches disagree on an overlap"; F->st = CK_INVALID; }
                    else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: system overlap"; F->st = CK_UNRESOLVED; }
                }
                free(F->cs); F->cs = NULL;
            }
        if (F->st == CK_VALID) { require(F->sel < F->nb, "a covered system has an entailed branch under a single clause"); *F->type = F->types[F->sel]; }
        free(F->types); F->types = NULL;
        break;
    }
    case T_GLOBAL: {
        F->s = (SymbolId)F->h.payload;
        KF_CALL(validate_symbol, &F->st, F->s, F->reason);
        if (F->st != CK_VALID) break;
        KF_CALL(origin_context, &F->Gs, F->h.origin);
        KF_CALL0(fc_true, &F->ftrue);
        KF_CALL(check_map, &F->st, F->G, F->C, F->h.map, F->Gs, F->ftrue, F->reason);
        NOTE_SYMBOL(F->s);
        if (F->st == CK_VALID) KX(reindex, F->type, global_type(F->s), F->h.map);
        break;
    }
    case T_TCALL: {
        /* §43: a validated compiled record, a typed parameter map whose
         * source face entails required_face[σ], the argument at the
         * instantiated domain; the annotations must be the instantiated
         * domain and codomain; the result type is the output annotation */
        KX(compiler_decode_call, &F->ok, &F->h, &F->id, &F->dir, &F->sigma, &F->a);
        if (!F->ok) { *F->reason = "malformed TRANSFORM_CALL or unknown transform"; F->st = CK_INVALID; break; }
        F->tr = transform_get(F->id);
        KF_CALL(check_map, &F->st, F->G, F->C, F->sigma, F->tr->parameters, F->tr->required_face, F->reason);
        if (F->st != CK_VALID) break;
        KX(reindex, &F->dom, F->dir ? F->tr->codomain : F->tr->domain, F->sigma); KX(reindex, &F->cod, F->dir ? F->tr->domain : F->tr->codomain, F->sigma);
        F->np = context_size(F->tr->parameters);
        KF_CALL(conv_type_clause, &F->c1, F->G, F->C, F->h.f[F->np + 1].id, F->dom);
        F->c2 = F->c1;
        if (F->c1 == CV_EQUAL) KF_CALL(conv_type_clause, &F->c2, F->G, F->C, F->h.f[F->np + 2].id, F->cod);
        if (F->c2 == CV_UNEQUAL) { *F->reason = "TRANSFORM_CALL annotations differ from the instantiated domain/codomain"; F->st = CK_INVALID; break; }
        if (F->c2 == CV_UNRESOLVED) { *F->reason = "unresolved: TRANSFORM_CALL annotation conversion"; F->st = CK_UNRESOLVED; break; }
        /* §59.1: the record's stored TypeAt levels are the formation levels of the annotations */
        KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[F->np + 1].id, &F->ld, F->reason); if (F->st != CK_VALID) break;
        KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[F->np + 2].id, &F->lc, F->reason); if (F->st != CK_VALID) break;
        { uint64_t ed = F->dir ? F->tr->codomain_level : F->tr->domain_level, ec = F->dir ? F->tr->domain_level : F->tr->codomain_level;
          if (F->ld != ed || F->lc != ec) { *F->reason = "TRANSFORM_CALL annotation levels differ from the record's stored levels"; F->st = CK_INVALID; break; } }
        KF_CALL(check_clause, &F->st, F->G, F->C, F->a, F->dom, F->reason);
        if (F->st == CK_VALID) *F->type = F->h.f[F->np + 2].id;
        break;
    }
    }
    head_free(&F->h);
    KF_RET(F->st);
    KF_END;
}

/* inference of an arbitrary reference under a clause: variables directly,
 * views through the substitution lemma */
static void infer_tview_push(KStack *ks, CheckStatus *ret, ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
#define infer_clause_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, t) X(RefId *, type) X(const char **, reason)
KF_DECL(infer_clause, CheckStatus, infer_clause_PARAMS, bool ent; OriginId O; ContextId Gc; FaceId req; RefId Ac; CheckStatus st;)
KF_STEP(infer_clause) {
    KF_BEGIN(infer_clause);
    if (!budget_ok()) { *F->reason = R_BUDGET; KF_RET(CK_UNRESOLVED); }
    KF_CALL(under, &F->G, F->G, F->C);
    if (ref_is_var(F->t)) { KF_CALL(infer_head, &F->st, F->G, F->C, F->t, F->type, F->reason); KF_RET(F->st); }
    KF_CALL(fc_entails, &F->ent, F->C, ref_required(F->t));
    if (!F->ent) { *F->reason = "occurrence outside its required face"; KF_RET(CK_INVALID); }
    if (ref_is_tview(F->t)) { KF_CALL(infer_tview, &F->st, F->G, F->C, F->t, F->type, F->reason); KF_RET(F->st); }
    if (origin_tag(ref_origin(F->t)) == T_GLOBAL) { KF_CALL(infer_head, &F->st, F->G, F->C, F->t, F->type, F->reason); KF_RET(F->st); }
    F->O = ref_origin(F->t);
    KF_CALL(check_origin, &F->st, F->O, &F->Gc, &F->req, &F->Ac, F->reason);
    if (F->st != CK_VALID) KF_RET(F->st);
    KF_CALL(check_map, &F->st, F->G, F->C, ref_map(F->t), F->Gc, F->req, F->reason);
    if (F->st != CK_VALID) KF_RET(F->st);
    KX(reindex, F->type, F->Ac, ref_map(F->t));
    KF_RET(CK_VALID);
    KF_END;
}

/* §50.1–4: the supplied scope's own validity, in its own ambient-plus-local
 * context under its own guards: every term local's declaration forms (in the
 * supplied prefix, under the projected clause conjoined with that local's
 * required face) at its required stated level; under C ∧ supplied guard the
 * result type forms at its stated level and the body has that type. The
 * metadata requirements hold whatever the guards; the typing judgments are
 * vacuous where the guards are false. */
#define check_scope_own_PARAMS(X) X(ContextId, G) X(FaceId, C) X(ScopeId, S) X(const char **, reason)
KF_DECL_DROP(check_scope_own, CheckStatus, check_scope_own_PARAMS, check_scope_own_drop, bool ok; uint64_t *ids; Val *args; size_t n, k, nc, c; ContextId Gx; CheckStatus st; LocalDecl d; RefId sty; FaceId sreq, m; uint64_t slv, l; FaceId *cs; TypedPartial sup; TypedPartial tp;)
static void check_scope_own_drop(check_scope_own_F *F) { free(F->ids); F->ids = NULL; free(F->args); F->args = NULL; free(F->cs); F->cs = NULL; }
KF_STEP(check_scope_own) {
    KF_BEGIN(check_scope_own);
    /* finite structure first, independent of any face: bound occurrences
     * name existing telescopes/slots of the right sort, declarations use
     * their prefix, metadata is present; and the scope's free identities
     * are declared in the occurrence context */
    KX(scope_validate, &F->ok, F->S, F->reason);
    if (!F->ok) KF_RET(CK_INVALID);
    { size_t m; const uint64_t *fv = varset_get(scope_freevars(F->S), &m);
      for (size_t q = 0; q < m; q++) if (!context_declares_term(F->G, fv[q], NULL)) { *F->reason = "scope mentions a variable not declared in the occurrence context"; KF_RET(CK_INVALID); }
      if (!dims_declared(F->G, scope_support(F->S))) { *F->reason = "scope mentions a dimension not declared in the occurrence context"; KF_RET(CK_INVALID); } }
    F->n = scope_arity(F->S);
    F->ids = malloc((F->n ? F->n : 1) * sizeof(uint64_t)); F->args = malloc((F->n ? F->n : 1) * sizeof(Val));
    require(F->ids && F->args, "out of memory");
    KX(open_scope_fresh, &F->tp, F->S, 0x52, F->ids);
    F->Gx = F->G;
    F->st = CK_VALID;
    for (F->k = 0; F->k < F->n && F->st == CK_VALID; F->k++) {
        F->d = scope_local(F->S, F->k);
        if (F->d.sort == S_DIM) { F->args[F->k].sort = VS_INTERVAL; KF_CALL(iv_var, &F->args[F->k].id, (DimVarId)F->ids[F->k]); KX(context_extend_dim, &F->Gx, F->Gx, (DimVarId)F->ids[F->k]); continue; }
        F->args[F->k].sort = VS_REF; KX(ref_var, &F->args[F->k].id, (TermVarId)F->ids[F->k]);
        KXV(scope_local_at, F->S, F->k, F->args, &F->sty, &F->sreq, &F->slv);
        if (!F->sty) { *F->reason = "scope local has no declared type"; F->st = CK_INVALID; break; }
        if (F->slv == LEVEL_NONE) { *F->reason = "missing universe annotation on a scope local (§59.1)"; F->st = CK_INVALID; break; }
        KF_CALL(fc_meet, &F->m, F->C, F->sreq);
        KF_CALL(clauses_of, &F->nc, F->m, &F->cs);
        for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
            KF_CALL(check_is_type, &F->st, F->Gx, F->cs[F->c], F->sty, &F->l, F->reason);
            if (F->st == CK_INVALID) { *F->reason = "scope local type is not a type"; break; }
            if (F->st == CK_VALID && F->l != F->slv) { *F->reason = "scope local level annotation differs from its formation level"; F->st = CK_INVALID; }
        }
        free(F->cs); F->cs = NULL;
        KX(context_extend_term, &F->Gx, F->Gx, (TermVarId)F->ids[F->k], F->sty);
    }
    if (F->st == CK_VALID) {
        KX(apply_scope, &F->sup, F->S, F->n, F->args);
        if (F->sup.body.sort == VS_REF) {
            if (!F->sup.type) { *F->reason = "scope has no declared result type"; F->st = CK_INVALID; }
            else if (F->sup.level == LEVEL_NONE) { *F->reason = "missing universe annotation on a scope result (§59.1)"; F->st = CK_INVALID; }
            F->nc = 0;
            if (F->st == CK_VALID) { KF_CALL(fc_meet, &F->m, F->C, F->sup.guard); KF_CALL(clauses_of, &F->nc, F->m, &F->cs); }
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(check_is_type, &F->st, F->Gx, F->cs[F->c], F->sup.type, &F->l, F->reason);
                if (F->st == CK_INVALID) { *F->reason = "scope result type is not a type"; break; }
                if (F->st != CK_VALID) break;
                if (F->sup.level != F->l) { *F->reason = "scope result level annotation differs from its formation level"; F->st = CK_INVALID; break; }
                KF_CALL(check_clause, &F->st, F->Gx, F->cs[F->c], F->sup.body.id, F->sup.type, F->reason);
            }
            free(F->cs); F->cs = NULL;
        }
    }
    free(F->ids); F->ids = NULL; free(F->args); F->args = NULL;
    KF_RET(F->st);
    KF_END;
}

/* §51.4: a (valid) scope argument S supplied at the expected contextual
 * signature Sig (locals = expected telescope, body = expected result type,
 * level, guard). Both are opened at one common fresh telescope (the
 * signature's); the supplied local declarations must convert to the expected
 * ones, the expected guard must entail the supplied one under the source
 * clause, and the result types must convert under the expected guard. A
 * face / interval scope is total syntax: arity, sorts and guard only. */
#define check_scope_arg_PARAMS(X) X(ContextId, G) X(FaceId, C) X(ScopeId, S) X(ScopeId, Sig) X(const char **, reason)
KF_DECL_DROP(check_scope_arg, CheckStatus, check_scope_arg_PARAMS, check_scope_arg_drop, size_t n, k, nc, c; Val sb, gb; CheckStatus st; uint64_t *ids; Val *args; TypedPartial sig, sup; ContextId Gx; LocalDecl d; RefId sty, ety; FaceId sreq, m; uint64_t slv; ConvStatus cv; bool ent; FaceId *cs;)
static void check_scope_arg_drop(check_scope_arg_F *F) { free(F->ids); F->ids = NULL; free(F->args); F->args = NULL; free(F->cs); F->cs = NULL; }
KF_STEP(check_scope_arg) {
    KF_BEGIN(check_scope_arg);
    F->n = scope_arity(F->S);
    if (F->n != scope_arity(F->Sig)) { *F->reason = "scope argument telescope length differs from the signature"; KF_RET(CK_INVALID); }
    for (size_t k = 0; k < F->n; k++) if (scope_local(F->S, k).sort != scope_local(F->Sig, k).sort) { *F->reason = "scope argument telescope sorts differ from the signature"; KF_RET(CK_INVALID); }
    F->sb = scope_body(F->S); F->gb = scope_body(F->Sig);
    if (F->sb.sort != F->gb.sort) { *F->reason = "scope argument body sort differs from the signature"; KF_RET(CK_INVALID); }
    KF_CALL(check_scope_own, &F->st, F->G, F->C, F->S, F->reason);
    if (F->st != CK_VALID) KF_RET(F->st);
    F->ids = malloc((F->n ? F->n : 1) * sizeof(uint64_t)); F->args = malloc((F->n ? F->n : 1) * sizeof(Val));
    require(F->ids && F->args, "out of memory");
    KX(open_scope_fresh, &F->sig, F->Sig, 0x51, F->ids);
    F->Gx = F->G;
    for (F->k = 0; F->k < F->n && F->st == CK_VALID; F->k++) {
        F->d = scope_local(F->Sig, F->k);
        if (F->d.sort == S_DIM) { F->args[F->k].sort = VS_INTERVAL; KF_CALL(iv_var, &F->args[F->k].id, (DimVarId)F->ids[F->k]); KX(context_extend_dim, &F->Gx, F->Gx, (DimVarId)F->ids[F->k]); continue; }
        F->args[F->k].sort = VS_REF; KX(ref_var, &F->args[F->k].id, (TermVarId)F->ids[F->k]);
        F->ety = term_var_type((TermVarId)F->ids[F->k]);
        KXV(scope_local_at, F->S, F->k, F->args, &F->sty, &F->sreq, &F->slv);
        KF_CALL(conv_type_clause, &F->cv, F->Gx, F->C, F->sty, F->ety);
        if (F->cv == CV_UNEQUAL) { *F->reason = "scope argument local type differs from the signature"; F->st = CK_INVALID; break; }
        if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: scope argument local type conversion"; F->st = CK_UNRESOLVED; break; }
        KX(context_extend_term, &F->Gx, F->Gx, (TermVarId)F->ids[F->k], F->ety);
    }
    if (F->st == CK_VALID) {
        KX(apply_scope, &F->sup, F->S, F->n, F->args);
        /* availability: expected guard ⊢ supplied guard under the source clause */
        KF_CALL(fc_meet, &F->m, F->C, F->sig.guard);
        KF_CALL(fc_entails, &F->ent, F->m, F->sup.guard);
        if (!F->ent) { *F->reason = "scope argument is not available where the signature requires it"; F->st = CK_INVALID; }
        else if (F->sb.sort == VS_REF) {
            KF_CALL(clauses_of, &F->nc, F->m, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(conv_type_clause, &F->cv, F->Gx, F->cs[F->c], F->sup.type, F->sig.body.id);
                if (F->cv == CV_UNEQUAL) { *F->reason = "scope argument result type differs from the signature"; F->st = CK_INVALID; break; }
                if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: scope argument result type conversion"; F->st = CK_UNRESOLVED; break; }
            }
            free(F->cs); F->cs = NULL;
        }
    }
    free(F->ids); F->ids = NULL; free(F->args); F->args = NULL;
    KF_RET(F->st);
    KF_END;
}

/* the template boundary of an instance (§51.4, §59.1): its declared required
 * face must be entailed; every retained reference parameter image is checked
 * against the signature's instantiated declared type and every retained scope
 * against its contextual signature. Memoized per (view, declarations,
 * projected clause). */
#define tview_boundary_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, t) X(const char **, reason)
KF_DECL_DROP(tview_boundary, CheckStatus, tview_boundary_PARAMS, tview_boundary_drop, OWNED_FIELDS bool ent, ok; uint64_t key[3]; FaceId ftrue, m; CheckStatus st; TEnvId E; size_t q, ne, ns, k, nc, c; ParamSig *sig; uint64_t image; FaceId *cs;)
static void tview_boundary_drop(tview_boundary_F *F) { free(F->sig); F->sig = NULL; free(F->cs); F->cs = NULL; OWNED_DROP(F); }
KF_STEP(tview_boundary) {
    KF_BEGIN(tview_boundary);
    KF_CALL(fc_entails, &F->ent, F->C, ref_required(F->t));
    if (!F->ent) { *F->reason = "template instance used outside its declared required face"; KF_RET(CK_INVALID); }
    F->key[0] = F->t;
    KF_CALL0(fc_true, &F->ftrue);
    KF_CALL(under, &F->key[1], F->G, F->ftrue);
    { size_t n; const uint64_t *ds = dimset_get(ref_support(F->t), &n); KF_CALL(fc_project, &F->key[2], F->C, ds, n); }
    F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_TBOUND, F->key, 3);
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, NULL);
    if (F->a == ACQ_DONE) { if (F->v == 1) KF_RET(CK_VALID); *F->reason = F->why; KF_RET(ck_of(F->v)); }
    if (F->a == ACQ_CYCLE) { *F->reason = "unresolved: template boundary validation depends on itself"; KF_RET(CK_UNRESOLVED); }
    F->owns = true;
    F->st = CK_VALID;
    KP(tenv_of, &F->E, F->t);
    /* finite structure of every retained image before any signature recipe
     * can apply a supplied scope (§50.1–2, review R3) */
    for (F->q = 0, F->ne = tenv_size(F->E); F->q < F->ne && F->st == CK_VALID; F->q++) {
        uint64_t slot; TVal val; tenv_entry(F->E, F->q, &slot, &val);
        if (val.sort == PS_SCOPE) { KX(scope_validate, &F->ok, (ScopeId)val.id, F->reason); if (!F->ok) F->st = CK_INVALID; }
        else if (val.sort == PS_REF) { KX(ref_validate, &F->ok, val.id, F->reason); if (!F->ok) F->st = CK_INVALID; }
    }
    if (F->st != CK_VALID) { RELEASE_F(ck_code(F->st), *F->reason, NULL); KF_RET(F->st); }
    KX(tnode_signature, &F->ns, F->t, NULL, 0);
    require(F->ns <= SIZE_MAX / sizeof(ParamSig), "template signature allocation overflow");
    F->sig = F->ns ? malloc(F->ns * sizeof *F->sig) : NULL;
    KXV(tnode_signature, F->t, F->sig, F->ns);
    for (F->k = 0; F->k < F->ns && F->st == CK_VALID; F->k++) {
        { size_t ne = tenv_size(F->E); bool have = false; F->image = 0;
          for (size_t q = 0; q < ne; q++) { uint64_t slot; TVal val; tenv_entry(F->E, q, &slot, &val); if (slot == F->sig[F->k].slot) { F->image = val.id; have = true; } }
          require(have, "template boundary: a retained slot has no image"); }
        if (F->sig[F->k].sort == PS_REF) {
            if (!F->sig[F->k].type) continue;                     /* an undeclared parameter (none in the library) */
            /* a partial parameter or local is checked on its declared guarded use */
            KF_CALL(fc_meet, &F->m, F->C, F->sig[F->k].guard);
            KF_CALL(clauses_of, &F->nc, F->m, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) KF_CALL(check_clause, &F->st, F->G, F->cs[F->c], F->image, F->sig[F->k].type, F->reason);
            free(F->cs); F->cs = NULL;
            if (F->st == CK_INVALID) { char buf[256]; snprintf(buf, sizeof buf, "template parameter image is not of its declared type (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(F->t))), F->sig[F->k].slot, *F->reason); *F->reason = diag_intern(buf); }
        } else if (F->sig[F->k].sort == PS_SCOPE) {
            if (!F->sig[F->k].sig) continue;
            KF_CALL(check_scope_arg, &F->st, F->G, F->C, (ScopeId)F->image, F->sig[F->k].sig, F->reason);
            if (F->st == CK_INVALID) { char buf[256]; snprintf(buf, sizeof buf, "template scope argument does not meet its signature (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(F->t))), F->sig[F->k].slot, *F->reason); *F->reason = diag_intern(buf); }
        }
    }
    free(F->sig); F->sig = NULL;
    RELEASE_F(ck_code(F->st), *F->reason, NULL);
    KF_RET(F->st);
    KF_END;
}

/* A template instance: boundary, then the opened head by the existing
 * constructor rules; when the instance is a program's root its inferred type
 * must convert to the declared result type instantiated by the environment. */
KF_DECL_DROP(infer_tview, CheckStatus, infer_clause_PARAMS, infer_tview_drop, OWNED_FIELDS uint64_t key[3]; uint64_t aux[3]; FaceId ftrue; CheckStatus st; RefId ty, declared; uint64_t dl; bool have; ConvStatus cv;)
static void infer_tview_drop(infer_tview_F *F) { OWNED_DROP(F); }
KF_STEP(infer_tview) {
    KF_BEGIN(infer_tview);
    F->key[0] = F->t;
    KF_CALL0(fc_true, &F->ftrue);
    KF_CALL(under, &F->key[1], F->G, F->ftrue);
    { size_t n; const uint64_t *ds = dimset_get(ref_support(F->t), &n); KF_CALL(fc_project, &F->key[2], F->C, ds, n); }
    F->aux[0] = F->aux[1] = F->aux[2] = 0; F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_TVIEW, F->key, 3);
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, F->aux);
    if (F->a == ACQ_DONE) { if (F->v == 1) { *F->type = F->aux[0]; KF_RET(CK_VALID); } *F->reason = F->why; KF_RET(ck_of(F->v)); }
    if (F->a == ACQ_CYCLE) { *F->reason = "unresolved: template instance validation depends on itself"; KF_RET(CK_UNRESOLVED); }
    F->owns = true;
    KF_CALL(tview_boundary, &F->st, F->G, F->C, F->t, F->reason);
    F->ty = 0;
    if (F->st == CK_VALID) KF_CALL(infer_head, &F->st, F->G, F->C, F->t, &F->ty, F->reason);
    if (F->st == CK_VALID) {
        KX(tnode_result, &F->have, F->t, &F->declared, &F->dl);
        if (F->have) {
            KF_CALL(conv_type_clause, &F->cv, F->G, F->C, F->ty, F->declared);
            if (F->cv == CV_UNEQUAL) { char buf[256]; snprintf(buf, sizeof buf, "library instance type differs from its declared result type (%s)", tdef_name(tnode_def(ref_tnode(F->t)))); *F->reason = diag_intern(buf); F->st = CK_INVALID; }
            else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: declared result type conversion"; F->st = CK_UNRESOLVED; }
        }
    }
    F->aux[0] = F->ty;
    RELEASE_F(ck_code(F->st), *F->reason, F->aux);
    if (F->st == CK_VALID) *F->type = F->ty;
    KF_RET(F->st);
    KF_END;
}

#define scope_ok_PARAMS(X) X(ContextId, G) X(FaceId, chi) X(RefId, t) X(const char **, reason)
KF_DECL(scope_ok, CheckStatus, scope_ok_PARAMS, DimSetId fd; bool ok;)
KF_STEP(scope_ok) {
    KF_BEGIN(scope_ok);
    KF_CALL(face_dims, &F->fd, F->chi);
    if (!dims_declared(F->G, F->fd)) { *F->reason = "face mentions an undeclared dimension"; KF_RET(CK_INVALID); }
    KX(ref_validate, &F->ok, F->t, F->reason);
    if (!F->ok) KF_RET(CK_INVALID);      /* finite structure, independent of the face (§50.1–2) */
    { size_t n; const uint64_t *xs = varset_get(ref_freevars(F->t), &n);
      for (size_t k = 0; k < n; k++) if (!context_declares_term(F->G, xs[k], NULL)) { *F->reason = "unbound variable"; KF_RET(CK_INVALID); } }
    if (!dims_declared(F->G, ref_support(F->t))) { *F->reason = "unbound dimension"; KF_RET(CK_INVALID); }
    KF_RET(CK_VALID);
    KF_END;
}

KF_DECL_EXT_DROP(infer, Inference, infer_PARAMS, infer_drop, Inference out; FaceId *cs; size_t nc, c; RefId *types; bool entered, settled, same;)
static void infer_drop(infer_F *F) { free(F->cs); F->cs = NULL; free(F->types); F->types = NULL; if (F->entered) { top_abandon(); F->entered = false; } }
KF_STEP(infer) {
    KF_BEGIN(infer);
  for (;;) {
    F->out.st = CK_VALID; F->out.type = 0; F->out.reason = NULL;
    ENTER_F();
    KF_CALL(scope_ok, &F->out.st, F->G, F->chi, F->t, &F->out.reason);
    if (F->out.st != CK_VALID) { LEAVE_F(); SETTLED_F(); KF_RET(F->out); }
    KF_CALL(clauses_of, &F->nc, F->chi, &F->cs);
    F->types = malloc((F->nc ? F->nc : 1) * sizeof(RefId));
    for (F->c = 0; F->c < F->nc && F->out.st == CK_VALID; F->c++) KF_CALL(infer_clause, &F->out.st, F->G, F->cs[F->c], F->t, &F->types[F->c], &F->out.reason);
    if (F->out.st == CK_VALID) {
        if (F->nc == 0) KX(mk_system, &F->out.type, 0, NULL, NULL);
        else { F->same = true; for (size_t c = 1; c < F->nc; c++) if (F->types[c] != F->types[0]) F->same = false; if (F->same) F->out.type = F->types[0]; else KX(mk_system, &F->out.type, F->nc, F->cs, F->types); }
    }
    free(F->types); F->types = NULL; free(F->cs); F->cs = NULL;
    LEAVE_F();
    SETTLED_F();
    if (F->settled) KF_RET(F->out);
  }
    KF_END;
}
KF_SYNC_DEF(infer, Inference, infer_PARAMS, infer(ContextId G, FaceId chi, RefId t))

/* ------------------------------------------------------------------ */
/* checking against an expected type                                    */

#define check_clause_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, t) X(RefId, A) X(const char **, reason)
KF_DECL_DROP(check_clause, CheckStatus, check_clause_PARAMS, check_clause_drop, bool ent; Tag tag; CheckStatus st, bs; Head h, hp; RefId P, D, l, r, T, body, Bj, bx, px, vx, t0, p0, t1, p1, tmp; ConvStatus cv, c0, c1; uint64_t lv; TermVarId x; DimVarId j; IntervalId vj, z, one; ContextId Gx; size_t nb, k, kk, nc, c; FaceId uni, Ck, Ckl, mkl; DimSetId fd; FaceId *cs;)
static void check_clause_drop(check_clause_F *F) { head_free(&F->h); head_free(&F->hp); free(F->cs); F->cs = NULL; }
KF_STEP(check_clause) {
    KF_BEGIN(check_clause);
    if (!budget_ok()) { *F->reason = R_BUDGET; KF_RET(CK_UNRESOLVED); }
    KF_CALL(under, &F->G, F->G, F->C);
    F->tag = 0;
    /* §2/§33: an occurrence is used only under a clause entailing its
     * required face — on every path, the checking forms included */
    if (!ref_is_var(F->t)) { KF_CALL(fc_entails, &F->ent, F->C, ref_required(F->t)); if (!F->ent) { *F->reason = "occurrence outside its required face"; KF_RET(CK_INVALID); } }
    if (!ref_is_var(F->t)) F->tag = ref_tag(F->t);
    if (F->tag == T_LAM || F->tag == T_PAIR || F->tag == T_PLAM || F->tag == T_SYSTEM) {
        if (ref_is_tview(F->t)) { KF_CALL(tview_boundary, &F->bs, F->G, F->C, F->t, F->reason); if (F->bs != CK_VALID) KF_RET(F->bs); }   /* the checking form does not bypass the template boundary */
        KXV(open_ref, F->t, &F->h);
        F->st = CK_VALID;
        switch (F->tag) {
        case T_LAM: {
            KF_CALL(observe_head, &F->st, F->C, F->A, T_PI, &F->P, F->reason);
            if (F->st != CK_VALID) { if (F->st == CK_INVALID) *F->reason = "lambda checked against a non-product type"; break; }
            KXV(open_ref, F->P, &F->hp); F->D = F->hp.f[0].id; head_free(&F->hp);
            KF_CALL(conv_type_clause, &F->cv, F->G, F->C, F->h.f[0].id, F->D);
            if (F->cv == CV_UNEQUAL) { *F->reason = "lambda domain differs from the expected domain"; F->st = CK_INVALID; break; }
            if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: lambda domain conversion"; F->st = CK_UNRESOLVED; break; }
            KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[0].id, &F->lv, F->reason); if (F->st != CK_VALID) break;   /* the annotation is a type at its stored level */
            if (!level_ok1(F->h.levels, F->lv)) { *F->reason = level_why(F->h.levels, "lambda domain level annotation differs"); F->st = CK_INVALID; break; }
            KF_CALL(conv_var, &F->x, F->t, F->P, F->P, 0, F->D);
            KX(context_extend_term, &F->Gx, F->G, F->x, F->D);
            KX(ref_var, &F->vx, F->x);
            KX(apply_term_binder, &F->bx, F->t, 0, 1, F->vx); KX(apply_term_binder, &F->px, F->P, 0, 1, F->vx);
            KF_CALL(check_clause, &F->st, F->Gx, F->C, F->bx, F->px, F->reason);
            break;
        }
        case T_PAIR: {
            if (F->h.n == 3) {
                /* annotated pair (§59.2): the stored Σ forms at its stored
                 * level, is convertible with the expected type, and governs
                 * the component checks */
                KF_CALL(level_of, &F->st, F->G, F->C, F->h.f[2].id, &F->lv, F->reason); if (F->st != CK_VALID) break;
                if (!level_ok1(F->h.levels, F->lv)) { *F->reason = level_why(F->h.levels, "pair annotation level differs"); F->st = CK_INVALID; break; }
                KF_CALL(conv_type_clause, &F->cv, F->G, F->C, F->h.f[2].id, F->A);
                if (F->cv == CV_UNEQUAL) { *F->reason = "pair annotation differs from the expected type"; F->st = CK_INVALID; break; }
                if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: pair annotation conversion"; F->st = CK_UNRESOLVED; break; }
                F->A = F->h.f[2].id;
            }
            KF_CALL(observe_head, &F->st, F->C, F->A, T_SIGMA, &F->P, F->reason);
            if (F->st != CK_VALID) { if (F->st == CK_INVALID) *F->reason = "pair checked against a non-sum type"; break; }
            KXV(open_ref, F->P, &F->hp); F->D = F->hp.f[0].id; head_free(&F->hp);
            KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[0].id, F->D, F->reason);
            if (F->st == CK_VALID) { KX(apply_term_binder, &F->tmp, F->P, 0, 1, F->h.f[0].id); KF_CALL(check_clause, &F->st, F->G, F->C, F->h.f[1].id, F->tmp, F->reason); }
            break;
        }
        case T_PLAM: {
            KF_CALL(observe_head, &F->st, F->C, F->A, T_PATH, &F->P, F->reason);
            if (F->st != CK_VALID) { if (F->st == CK_INVALID) *F->reason = "path lambda checked against a non-path type"; break; }
            KXV(open_ref, F->P, &F->hp); F->l = F->hp.f[1].id; F->r = F->hp.f[2].id; head_free(&F->hp);
            KF_CALL(conv_dim, &F->j, F->t, F->P, 0);
            KF_CALL(iv_var, &F->vj, F->j);
            KX(apply_dim_binder, &F->body, F->t, 0, 0, F->vj); KX(apply_dim_binder, &F->Bj, F->P, 0, 0, F->vj);
            KX(context_extend_dim, &F->Gx, F->G, F->j);
            KF_CALL(check_clause, &F->st, F->Gx, F->C, F->body, F->Bj, F->reason);
            if (F->st != CK_VALID) break;
            KF_CALL0(iv_zero, &F->z); KX(apply_dim_binder, &F->t0, F->t, 0, 0, F->z); KX(apply_dim_binder, &F->p0, F->P, 0, 0, F->z);
            KF_CALL(conv_term_clause, &F->c0, F->G, F->C, F->t0, F->l, F->p0);
            F->c1 = F->c0;
            if (F->c0 == CV_EQUAL) { KF_CALL0(iv_one, &F->one); KX(apply_dim_binder, &F->t1, F->t, 0, 0, F->one); KX(apply_dim_binder, &F->p1, F->P, 0, 0, F->one); KF_CALL(conv_term_clause, &F->c1, F->G, F->C, F->t1, F->r, F->p1); }
            if (F->c1 == CV_UNEQUAL) { *F->reason = "path lambda endpoints differ from the path type's endpoints"; F->st = CK_INVALID; }
            else if (F->c1 == CV_UNRESOLVED) { *F->reason = "unresolved: path endpoint conversion"; F->st = CK_UNRESOLVED; }
            break;
        }
        case T_SYSTEM: {
            F->nb = F->h.n / 2;
            KF_CALL0(fc_false, &F->uni);
            for (F->k = 0; F->k < F->nb; F->k++) KF_CALL(fc_join, &F->uni, F->uni, F->h.f[2 * F->k].id);
            KF_CALL(fc_entails, &F->ent, F->C, F->uni);
            if (!F->ent) { *F->reason = "system does not cover the face"; F->st = CK_INVALID; break; }
            for (F->k = 0; F->k < F->nb && F->st == CK_VALID; F->k++) {
                KF_CALL(fc_meet, &F->Ck, F->C, F->h.f[2 * F->k].id);
                KF_CALL(face_dims, &F->fd, F->h.f[2 * F->k].id);
                if (!dims_declared(F->G, F->fd)) { *F->reason = "system guard mentions an undeclared dimension"; F->st = CK_INVALID; break; }
                if (fc_is_false(F->Ck)) continue;
                KF_CALL(clauses_of, &F->nc, F->Ck, &F->cs);
                for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) KF_CALL(check_clause, &F->st, F->G, F->cs[F->c], F->h.f[2 * F->k + 1].id, F->A, F->reason);
                free(F->cs); F->cs = NULL;
            }
            for (F->k = 0; F->k < F->nb && F->st == CK_VALID; F->k++)
                for (F->kk = F->k + 1; F->kk < F->nb && F->st == CK_VALID; F->kk++) {
                    KF_CALL(fc_meet, &F->mkl, F->h.f[2 * F->k].id, F->h.f[2 * F->kk].id);
                    KF_CALL(fc_meet, &F->Ckl, F->C, F->mkl);
                    if (fc_is_false(F->Ckl)) continue;
                    KF_CALL(clauses_of, &F->nc, F->Ckl, &F->cs);
                    for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                        KF_CALL(conv_term_clause, &F->cv, F->G, F->cs[F->c], F->h.f[2 * F->k + 1].id, F->h.f[2 * F->kk + 1].id, F->A);
                        if (F->cv == CV_UNEQUAL) { *F->reason = "system branches disagree on an overlap"; F->st = CK_INVALID; }
                        else if (F->cv == CV_UNRESOLVED) { *F->reason = "unresolved: system overlap"; F->st = CK_UNRESOLVED; }
                    }
                    free(F->cs); F->cs = NULL;
                }
            break;
        }
        default: break;
        }
        head_free(&F->h);
        KF_RET(F->st);
    }
    KF_CALL(infer_clause, &F->st, F->G, F->C, F->t, &F->T, F->reason);
    if (F->st != CK_VALID) KF_RET(F->st);
    KF_CALL(conv_type_clause, &F->cv, F->G, F->C, F->T, F->A);
    if (F->cv == CV_EQUAL) KF_RET(CK_VALID);
    if (F->cv == CV_UNEQUAL) {
        if (getenv("CK_DEBUG")) { fprintf(stderr, "UNEQUAL under "); fc_print(F->C, stderr); fprintf(stderr, "\n  term: "); print_ref_depth(F->t, stderr, 2); fprintf(stderr, "\n  inferred: "); print_ref_depth(F->T, stderr, 3); fprintf(stderr, "\n  expected: "); print_ref_depth(F->A, stderr, 3); fprintf(stderr, "\n"); }
        *F->reason = "inferred type is not convertible to the expected type"; KF_RET(CK_INVALID);
    }
    *F->reason = "unresolved: type conversion";
    KF_RET(CK_UNRESOLVED);
    KF_END;
}

KF_DECL_EXT_DROP(check, CheckStatus, check_PARAMS, check_drop, CheckStatus st; FaceId *cs; size_t nc, c; bool entered, settled;)
static void check_drop(check_F *F) { free(F->cs); F->cs = NULL; if (F->entered) { top_abandon(); F->entered = false; } }
KF_STEP(check) {
    KF_BEGIN(check);
  *F->reason = "";   /* a VALID verdict leaves a defined (empty) diagnostic: callers print it */
  for (;;) {
    ENTER_F();
    KF_CALL(scope_ok, &F->st, F->G, F->chi, F->t, F->reason);
    if (F->st == CK_VALID) KF_CALL(scope_ok, &F->st, F->G, F->chi, F->A, F->reason);
    if (F->st != CK_VALID) { LEAVE_F(); SETTLED_F(); KF_RET(F->st); }
    KF_CALL(clauses_of, &F->nc, F->chi, &F->cs);
    for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) KF_CALL(check_clause, &F->st, F->G, F->cs[F->c], F->t, F->A, F->reason);
    free(F->cs); F->cs = NULL;
    LEAVE_F();
    SETTLED_F();
    if (F->settled) KF_RET(F->st);
  }
    KF_END;
}
KF_SYNC_DEF(check, CheckStatus, check_PARAMS, check(ContextId G, FaceId chi, RefId t, RefId A, const char **reason))

/* ------------------------------------------------------------------ */
/* conversion                                                           */

/* conversion requests are claims keyed by (mode, context without assumption,
 * face projected to the support of the request, a, b, T) */
/* §77.2: the judgment's context projected to the dependency-closed free
 * declarations of its operands (free variables are already closed through
 * declaration types and required faces), in the original telescope order */
#define project_context_PARAMS(X) X(ContextId, G) X(VarSetId, vs) X(DimSetId, ds)
KF_DECL_DROP(project_context, ContextId, project_context_PARAMS, project_context_drop, CtxDecl *kept; size_t m; FaceId ftrue; ContextId out;)
static void project_context_drop(project_context_F *F) { free(F->kept); F->kept = NULL; }
KF_STEP(project_context) {
    KF_BEGIN(project_context);
    { size_t n = context_size(F->G); F->kept = malloc((n ? n : 1) * sizeof(CtxDecl)); require(F->kept, "out of memory"); F->m = 0;
      for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(F->G, k); if (d.sort == S_TERM ? varset_contains(F->vs, d.id) : dimset_contains(F->ds, d.id)) F->kept[F->m++] = d; } }
    KF_CALL0(fc_true, &F->ftrue);
    KX(context_make, &F->out, F->m, F->kept, F->ftrue);
    free(F->kept); F->kept = NULL;
    KF_RET(F->out);
    KF_END;
}
#define conv_claim_PARAMS(X) X(uint64_t, mode) X(ContextId, G) X(FaceId, C) X(RefId, a) X(RefId, b) X(RefId, T)
KF_DECL_DROP(conv_claim, size_t, conv_claim_PARAMS, conv_claim_drop, DimSetId S, S2; VarSetId V; FaceId Cp; Words dd; uint64_t key[6]; size_t cl;)
static void conv_claim_drop(conv_claim_F *F) { words_free(&F->dd); }
KF_STEP(conv_claim) {
    KF_BEGIN(conv_claim);
    KF_CALL(dimset_union, &F->S, ref_support(F->a), ref_support(F->b));
    KF_CALL(varset_union, &F->V, ref_freevars(F->a), ref_freevars(F->b));
    if (F->T) { KF_CALL(dimset_union, &F->S, F->S, ref_support(F->T)); KF_CALL(varset_union, &F->V, F->V, ref_freevars(F->T)); }
    { size_t n; const uint64_t *ds = dimset_get(F->S, &n); KF_CALL(fc_project, &F->Cp, F->C, ds, n); }
    words_init(&F->dd); fc_dims(F->Cp, &F->dd);
    KF_CALL(dimset_make, &F->S2, F->dd.w, F->dd.n);
    words_free(&F->dd);
    KF_CALL(dimset_union, &F->S, F->S, F->S2);
    F->key[0] = F->mode;
    KF_CALL(project_context, &F->key[1], F->G, F->V, F->S);
    F->key[2] = F->Cp; F->key[3] = F->a; F->key[4] = F->b; F->key[5] = F->T;
    KF_CALL(claim_index, &F->cl, CL_CONV, F->key, 6);
    KF_RET(F->cl);
    KF_END;
}

/* the common level of a Glue's base and fibre: the annotation, else inferred */
#define glue_level_PARAMS(X) X(ContextId, G) X(FaceId, C) X(uint64_t, levels) X(RefId, A)
KF_DECL(glue_level, uint64_t, glue_level_PARAMS, uint64_t l; const char *why; CheckStatus st;)
KF_STEP(glue_level) {
    KF_BEGIN(glue_level);
    F->l = levels_first(F->levels);
    if (F->l != LEVEL_NONE) KF_RET(F->l);
    KF_CALL(level_of, &F->st, F->G, F->C, F->A, &F->l, &F->why);
    if (F->st != CK_VALID) KF_RET(LEVEL_NONE);
    KF_RET(F->l);
    KF_END;
}

static ConvStatus and3(ConvStatus a, ConvStatus b) {
    if (a == CV_UNEQUAL || b == CV_UNEQUAL) return CV_UNEQUAL;
    if (a == CV_UNRESOLVED || b == CV_UNRESOLVED) return CV_UNRESOLVED;
    return CV_EQUAL;
}

#define observe_both_PARAMS(X) X(FaceId, C) X(RefId, a) X(RefId, b) X(EvalResult **, ra) X(EvalResult **, rb)
KF_DECL(observe_both, ConvStatus, observe_both_PARAMS, const char *reason; CheckStatus st;)
KF_STEP(observe_both) {
    KF_BEGIN(observe_both);
    KF_CALL(observe, &F->st, F->C, F->a, F->ra, &F->reason);
    if (F->st != CK_VALID) KF_RET(CV_UNRESOLVED);
    KF_CALL(observe, &F->st, F->C, F->b, F->rb, &F->reason);
    if (F->st != CK_VALID) KF_RET(CV_UNRESOLVED);
    KF_RET(CV_EQUAL);
    KF_END;
}

#define conv_type_clause_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, A) X(RefId, B)
KF_DECL_DROP(conv_type_clause, ConvStatus, conv_type_clause_PARAMS, conv_type_clause_drop, size_t cl; uint64_t v; Acq acq; bool owns; ConvStatus out; EvalResult *ra, *rb; Head ha, hb; TermVarId x; DimVarId j; IntervalId vj, z, one; RefId vx, Ba, Bb, ea, eb, eq; ContextId Gx; bool eu; FaceId Ca; FaceId *cs; size_t nc, c; uint64_t gl;)
static void conv_type_clause_drop(conv_type_clause_F *F) { head_free(&F->ha); head_free(&F->hb); free(F->cs); F->cs = NULL; if (F->owns) { claim_abandon(F->cl); F->owns = false; } }
KF_STEP(conv_type_clause) {
    KF_BEGIN(conv_type_clause);
    if (F->A == F->B) KF_RET(CV_EQUAL);
    if (!budget_ok()) KF_RET(CV_UNRESOLVED);
    KF_CALL(under, &F->G, F->G, F->C);
    KF_CALL(conv_claim, &F->cl, 1, F->G, F->C, F->A, F->B, 0);
    KF_CALL(claim_acquire, &F->acq, F->cl, &F->v, NULL, NULL);
    if (F->acq == ACQ_DONE) KF_RET(cv_of(F->v));
    if (F->acq == ACQ_CYCLE) KF_RET(CV_UNRESOLVED);  /* the comparison depends on itself: no coinductive assumption */
    F->owns = true;
    reuse_bump(REUSE_CONVERSION_BODY);
    F->out = CV_UNRESOLVED;
    { ConvStatus ob; KF_CALL(observe_both, &F->out, F->C, F->A, F->B, &F->ra, &F->rb); ob = F->out; F->out = CV_UNRESOLVED; if (ob != CV_EQUAL) goto done; }
    if (F->ra->ref == F->rb->ref) { F->out = CV_EQUAL; goto done; }
    if (F->ra->cls == R_SYSTEM || F->rb->cls == R_SYSTEM) { F->out = CV_UNRESOLVED; goto done; }
    if (F->ra->cls != F->rb->cls) { F->out = CV_UNEQUAL; goto done; }
    if (F->ra->cls == R_NEUTRAL) { KF_CALL(spine, &F->out, F->G, F->C, F->ra->ref, F->rb->ref); goto done; }
    KXV(open_ref, F->ra->ref, &F->ha); KXV(open_ref, F->rb->ref, &F->hb);
    if (F->ha.tag != F->hb.tag) F->out = CV_UNEQUAL;
    else switch (F->ha.tag) {
    case T_UNIVERSE: F->out = F->ha.payload == F->hb.payload ? CV_EQUAL : CV_UNEQUAL; break;
    case T_PI: case T_SIGMA: {
        KF_CALL(conv_type_clause, &F->out, F->G, F->C, F->ha.f[0].id, F->hb.f[0].id);
        if (F->out != CV_EQUAL) break;
        KF_CALL(conv_var, &F->x, F->ra->ref, F->rb->ref, F->ra->ref, 0, F->ha.f[0].id);
        KX(context_extend_term, &F->Gx, F->G, F->x, F->ha.f[0].id);
        KX(ref_var, &F->vx, F->x);
        KX(apply_term_binder, &F->Ba, F->ra->ref, 0, 1, F->vx); KX(apply_term_binder, &F->Bb, F->rb->ref, 0, 1, F->vx);
        KF_CALL(conv_type_clause, &F->out, F->Gx, F->C, F->Ba, F->Bb);
        break;
    }
    case T_PATH: {
        KF_CALL(conv_dim, &F->j, F->ra->ref, F->rb->ref, 0);
        KF_CALL(iv_var, &F->vj, F->j);
        KX(apply_dim_binder, &F->Ba, F->ra->ref, 0, 0, F->vj); KX(apply_dim_binder, &F->Bb, F->rb->ref, 0, 0, F->vj);
        KX(context_extend_dim, &F->Gx, F->G, F->j);
        KF_CALL(conv_type_clause, &F->out, F->Gx, F->C, F->Ba, F->Bb);
        if (F->out == CV_EQUAL) { KF_CALL0(iv_zero, &F->z); KX(reindex_dim, &F->ea, F->Ba, F->j, F->z); KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->ha.f[1].id, F->hb.f[1].id, F->ea); }
        if (F->out == CV_EQUAL) { KF_CALL0(iv_one, &F->one); KX(reindex_dim, &F->eb, F->Ba, F->j, F->one); KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->ha.f[2].id, F->hb.f[2].id, F->eb); }
        break;
    }
    case T_GLUE_TYPE: {
        KF_CALL(fc_equal_under, &F->eu, F->C, F->ha.f[1].id, F->hb.f[1].id);
        if (!F->eu) { F->out = CV_UNEQUAL; break; }
        KF_CALL(conv_type_clause, &F->out, F->G, F->C, F->ha.f[0].id, F->hb.f[0].id);
        KF_CALL(fc_meet, &F->Ca, F->C, F->ha.f[1].id);
        if (F->out == CV_EQUAL && !fc_is_false(F->Ca)) {
            KF_CALL(clauses_of, &F->nc, F->Ca, &F->cs);
            for (F->c = 0; F->c < F->nc && F->out == CV_EQUAL; F->c++) {
                KF_CALL(conv_type_clause, &F->out, F->G, F->cs[F->c], F->ha.f[2].id, F->hb.f[2].id);
                if (F->out == CV_EQUAL) {
                    KF_CALL(glue_level, &F->gl, F->G, F->cs[F->c], F->ha.levels, F->ha.f[0].id);
                    if (F->gl == LEVEL_NONE) { F->out = CV_UNRESOLVED; break; }
                    KX(mk_equiv, &F->eq, F->gl, F->gl, F->ha.f[2].id, F->ha.f[0].id);
                    KF_CALL(conv_term_clause, &F->out, F->G, F->cs[F->c], F->ha.f[3].id, F->hb.f[3].id, F->eq);
                }
            }
            free(F->cs); F->cs = NULL;
        }
        break;
    }
    default: F->out = CV_UNEQUAL; break;       /* an introduction that is not a type former */
    }
    head_free(&F->ha); head_free(&F->hb);
done:
    F->owns = false;
    KF_CALL(claim_release, NULL, F->cl, cv_code(F->out), NULL, NULL);
    KF_RET(F->out);
    KF_END;
}

#define conv_term_clause_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, t) X(RefId, u) X(RefId, A)
KF_DECL_DROP(conv_term_clause, ConvStatus, conv_term_clause_PARAMS, conv_term_clause_drop, size_t cl; uint64_t v; Acq acq; bool owns; ConvStatus out, ob; EvalResult *rA, *rt, *ru; const char *reason; CheckStatus st; Head h; TermVarId x; DimVarId j; DimOpen o; RefId vx, Bx, ta, ua, ft, fu, st2, su, Bj, pt, pu, Ab, T, e; IntervalId vj; ContextId Gx; FaceId alpha, Ca; FaceId *cs; size_t nc, c; uint64_t n;)
static void conv_term_clause_drop(conv_term_clause_F *F) { head_free(&F->h); free(F->cs); F->cs = NULL; if (F->owns) { claim_abandon(F->cl); F->owns = false; } }
KF_STEP(conv_term_clause) {
    KF_BEGIN(conv_term_clause);
    if (F->t == F->u) KF_RET(CV_EQUAL);
    if (!budget_ok()) KF_RET(CV_UNRESOLVED);
    KF_CALL(under, &F->G, F->G, F->C);
    KF_CALL(conv_claim, &F->cl, 2, F->G, F->C, F->t, F->u, F->A);
    KF_CALL(claim_acquire, &F->acq, F->cl, &F->v, NULL, NULL);
    if (F->acq == ACQ_DONE) KF_RET(cv_of(F->v));
    if (F->acq == ACQ_CYCLE) KF_RET(CV_UNRESOLVED);
    F->owns = true;
    reuse_bump(REUSE_CONVERSION_BODY);
    F->out = CV_UNRESOLVED;
    KF_CALL(observe, &F->st, F->C, F->A, &F->rA, &F->reason);
    if (F->st != CK_VALID) goto done;
    if (F->rA->cls == R_INTRODUCTION) {
        KXV(open_ref, F->rA->ref, &F->h);
        switch (F->h.tag) {
        case T_PI: {
            KF_CALL(conv_var, &F->x, F->t, F->u, F->rA->ref, 0, F->h.f[0].id);
            KX(ref_var, &F->vx, F->x);
            KX(apply_term_binder, &F->Bx, F->rA->ref, 0, 1, F->vx);
            KX(context_extend_term, &F->Gx, F->G, F->x, F->h.f[0].id);
            KX(mk_app, &F->ta, F->t, F->vx); KX(mk_app, &F->ua, F->u, F->vx);
            KF_CALL(conv_term_clause, &F->out, F->Gx, F->C, F->ta, F->ua, F->Bx);
            break;
        }
        case T_SIGMA: {
            KX(mk_fst, &F->ft, F->t); KX(mk_fst, &F->fu, F->u);
            KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->ft, F->fu, F->h.f[0].id);
            if (F->out == CV_EQUAL) {
                KX(mk_snd, &F->st2, F->t); KX(mk_snd, &F->su, F->u);
                KX(apply_term_binder, &F->Bx, F->rA->ref, 0, 1, F->ft);
                KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->st2, F->su, F->Bx);
            }
            break;
        }
        case T_PATH: {
            KF_CALL(conv_dim, &F->j, F->t, F->u, 0);
            KX(resolve_dim_binder, &F->o, F->rA->ref, 0, 0);
            KF_CALL(iv_var, &F->vj, F->j);
            KX(reindex_dim, &F->Bj, F->o.body, F->o.j, F->vj);
            F->n = levels_first(F->h.levels);
            KX(mk_papp_lv, &F->pt, F->n, F->o.j, F->o.body, F->h.f[1].id, F->h.f[2].id, F->t, F->vj);
            KX(mk_papp_lv, &F->pu, F->n, F->o.j, F->o.body, F->h.f[1].id, F->h.f[2].id, F->u, F->vj);
            KX(context_extend_dim, &F->Gx, F->G, F->j);
            KF_CALL(conv_term_clause, &F->out, F->Gx, F->C, F->pt, F->pu, F->Bj);
            break;
        }
        case T_GLUE_TYPE: {
            /* non-collapsed Glue (C does not entail alpha): Glue eta */
            F->Ab = F->h.f[0].id; F->T = F->h.f[2].id; F->e = F->h.f[3].id; F->alpha = F->h.f[1].id;
            F->n = levels_first(F->h.levels);
            KX(mk_unglue_lv, &F->pt, F->n, F->Ab, F->alpha, F->T, F->e, F->t); KX(mk_unglue_lv, &F->pu, F->n, F->Ab, F->alpha, F->T, F->e, F->u);
            KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->pt, F->pu, F->Ab);
            KF_CALL(fc_meet, &F->Ca, F->C, F->alpha);
            if (F->out == CV_EQUAL && !fc_is_false(F->Ca)) {
                KF_CALL(clauses_of, &F->nc, F->Ca, &F->cs);
                for (F->c = 0; F->c < F->nc && F->out == CV_EQUAL; F->c++) KF_CALL(conv_term_clause, &F->out, F->G, F->cs[F->c], F->t, F->u, F->T);
                free(F->cs); F->cs = NULL;
            }
            break;
        }
        case T_UNIVERSE: KF_CALL(conv_type_clause, &F->out, F->G, F->C, F->t, F->u); break;
        default: F->out = CV_UNEQUAL; break;
        }
        head_free(&F->h);
    } else if (F->rA->cls == R_NEUTRAL) {
        /* neutral expected type: observe the terms and compare their neutral structures */
        KF_CALL(observe_both, &F->ob, F->C, F->t, F->u, &F->rt, &F->ru);
        if (F->ob != CV_EQUAL) goto done;
        if (F->rt->ref == F->ru->ref) F->out = CV_EQUAL;
        else if (F->rt->cls == R_NEUTRAL && F->ru->cls == R_NEUTRAL) KF_CALL(spine, &F->out, F->G, F->C, F->rt->ref, F->ru->ref);
        else if (F->rt->cls == R_SYSTEM || F->ru->cls == R_SYSTEM) F->out = CV_UNRESOLVED;
        else F->out = CV_UNEQUAL;
    } else F->out = CV_UNRESOLVED;                 /* a system type under a single clause is not a covered type */
done:
    F->owns = false;
    KF_CALL(claim_release, NULL, F->cl, cv_code(F->out), NULL, NULL);
    KF_RET(F->out);
    KF_END;
}

/* structural comparison of neutral spines; n1, n2 are neutral result references */
#define spine_PARAMS(X) X(ContextId, G) X(FaceId, C) X(RefId, n1) X(RefId, n2)
KF_DECL_DROP(spine, ConvStatus, spine_PARAMS, spine_drop, Head a, b, hp; ConvStatus out, ob; EvalResult *fa, *fb; RefId Tf, P, dom, A1, A2, u1, u2, ea, ma, mb, eq; const char *reason; CheckStatus st; bool eu; DimVarId j; IntervalId vj, z, ia, ib; ContextId Gj, Gs; FaceId Ca, Cp; FaceId *cs; size_t nc, c, n, k; uint64_t gl; CtxDecl d;)
static void spine_drop(spine_F *F) { head_free(&F->a); head_free(&F->b); head_free(&F->hp); free(F->cs); F->cs = NULL; }
KF_STEP(spine) {
    KF_BEGIN(spine);
    if (F->n1 == F->n2) KF_RET(CV_EQUAL);
    if (!budget_ok()) KF_RET(CV_UNRESOLVED);
    KF_CALL(under, &F->G, F->G, F->C);
    if (ref_is_var(F->n1) || ref_is_var(F->n2)) KF_RET((ref_is_var(F->n1) && ref_is_var(F->n2) && ref_var_id(F->n1) == ref_var_id(F->n2)) ? CV_EQUAL : CV_UNEQUAL);
    KXV(open_ref, F->n1, &F->a); KXV(open_ref, F->n2, &F->b);
    F->out = CV_UNEQUAL;
    if (F->a.tag != F->b.tag) goto done;
    switch (F->a.tag) {
    case T_APP: {
        KF_CALL(observe_both, &F->ob, F->C, F->a.f[0].id, F->b.f[0].id, &F->fa, &F->fb);
        if (F->ob != CV_EQUAL) { F->out = CV_UNRESOLVED; break; }
        if (F->fa->cls != R_NEUTRAL || F->fb->cls != R_NEUTRAL) { F->out = CV_UNRESOLVED; break; }
        KF_CALL(spine, &F->out, F->G, F->C, F->fa->ref, F->fb->ref);
        if (F->out != CV_EQUAL) break;
        KF_CALL(infer_clause, &F->st, F->G, F->C, F->a.f[0].id, &F->Tf, &F->reason);
        if (F->st != CK_VALID) { F->out = CV_UNRESOLVED; break; }
        KF_CALL(observe_head, &F->st, F->C, F->Tf, T_PI, &F->P, &F->reason);
        if (F->st != CK_VALID) { F->out = CV_UNRESOLVED; break; }
        KXV(open_ref, F->P, &F->hp); F->dom = F->hp.f[0].id; head_free(&F->hp);
        KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->a.f[1].id, F->b.f[1].id, F->dom);
        break;
    }
    case T_FST: case T_SND: {
        KF_CALL(observe_both, &F->ob, F->C, F->a.f[0].id, F->b.f[0].id, &F->fa, &F->fb);
        if (F->ob != CV_EQUAL || F->fa->cls != R_NEUTRAL || F->fb->cls != R_NEUTRAL) { F->out = CV_UNRESOLVED; break; }
        KF_CALL(spine, &F->out, F->G, F->C, F->fa->ref, F->fb->ref);
        break;
    }
    case T_PAPP: {
        KF_CALL(iv_equal_under, &F->eu, F->C, F->a.f[4].id, F->b.f[4].id);
        if (!F->eu) { F->out = CV_UNEQUAL; break; }
        KF_CALL(observe_both, &F->ob, F->C, F->a.f[3].id, F->b.f[3].id, &F->fa, &F->fb);
        if (F->ob != CV_EQUAL || F->fa->cls != R_NEUTRAL || F->fb->cls != R_NEUTRAL) { F->out = CV_UNRESOLVED; break; }
        KF_CALL(spine, &F->out, F->G, F->C, F->fa->ref, F->fb->ref);
        break;
    }
    case T_UNGLUE: {
        KF_CALL(fc_equal_under, &F->eu, F->C, F->a.f[1].id, F->b.f[1].id);
        if (!F->eu) { F->out = CV_UNEQUAL; break; }
        KF_CALL(conv_type_clause, &F->out, F->G, F->C, F->a.f[0].id, F->b.f[0].id);
        KF_CALL(fc_meet, &F->Ca, F->C, F->a.f[1].id);
        if (F->out == CV_EQUAL && !fc_is_false(F->Ca)) {
            KF_CALL(clauses_of, &F->nc, F->Ca, &F->cs);
            for (F->c = 0; F->c < F->nc && F->out == CV_EQUAL; F->c++) {
                KF_CALL(conv_type_clause, &F->out, F->G, F->cs[F->c], F->a.f[2].id, F->b.f[2].id);
                if (F->out == CV_EQUAL) {
                    KF_CALL(glue_level, &F->gl, F->G, F->cs[F->c], F->a.levels, F->a.f[0].id);
                    if (F->gl == LEVEL_NONE) { F->out = CV_UNRESOLVED; break; }
                    KX(mk_equiv, &F->eq, F->gl, F->gl, F->a.f[2].id, F->a.f[0].id);
                    KF_CALL(conv_term_clause, &F->out, F->G, F->cs[F->c], F->a.f[3].id, F->b.f[3].id, F->eq);
                }
            }
            free(F->cs); F->cs = NULL;
        }
        if (F->out != CV_EQUAL) break;
        KF_CALL(observe_both, &F->ob, F->C, F->a.f[4].id, F->b.f[4].id, &F->fa, &F->fb);
        if (F->ob != CV_EQUAL || F->fa->cls != R_NEUTRAL || F->fb->cls != R_NEUTRAL) { F->out = CV_UNRESOLVED; break; }
        KF_CALL(spine, &F->out, F->G, F->C, F->fa->ref, F->fb->ref);
        break;
    }
    case T_COMP: {
        KF_CALL(fc_equal_under, &F->eu, F->C, F->a.f[1].id, F->b.f[1].id);
        if (!F->eu) { F->out = CV_UNEQUAL; break; }
        KF_CALL(conv_dim, &F->j, F->n1, F->n2, 0);
        KF_CALL(iv_var, &F->vj, F->j);
        KX(apply_dim_binder, &F->A1, F->n1, 0, 0, F->vj); KX(apply_dim_binder, &F->A2, F->n2, 0, 0, F->vj);
        KX(context_extend_dim, &F->Gj, F->G, F->j);
        KF_CALL(conv_type_clause, &F->out, F->Gj, F->C, F->A1, F->A2);
        if (F->out == CV_EQUAL) { KF_CALL0(iv_zero, &F->z); KX(reindex_dim, &F->ea, F->A1, F->j, F->z); KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->a.f[3].id, F->b.f[3].id, F->ea); }
        KF_CALL(fc_meet, &F->Cp, F->C, F->a.f[1].id);
        if (F->out == CV_EQUAL && !fc_is_false(F->Cp)) {
            KX(apply_dim_binder, &F->u1, F->n1, 0, 2, F->vj); KX(apply_dim_binder, &F->u2, F->n2, 0, 2, F->vj);
            KF_CALL(clauses_of, &F->nc, F->Cp, &F->cs);
            for (F->c = 0; F->c < F->nc && F->out == CV_EQUAL; F->c++) KF_CALL(conv_term_clause, &F->out, F->Gj, F->cs[F->c], F->u1, F->u2, F->A1);
            free(F->cs); F->cs = NULL;
        }
        break;
    }
    case T_GLOBAL: {
        if (F->a.payload != F->b.payload) { F->out = CV_UNEQUAL; break; }
        KF_CALL(origin_context, &F->Gs, F->a.origin);
        F->out = CV_EQUAL;
        F->n = context_size(F->Gs);
        for (F->k = 0; F->k < F->n && F->out == CV_EQUAL; F->k++) {
            F->d = context_decl(F->Gs, F->k);
            if (F->d.sort == S_DIM) {
                KX(map_dim_image, &F->ia, F->a.map, F->d.id); KX(map_dim_image, &F->ib, F->b.map, F->d.id);
                KF_CALL(iv_equal_under, &F->eu, F->C, F->ia, F->ib);
                if (!F->eu) F->out = CV_UNEQUAL;
            } else {
                KX(map_term_image, &F->ma, F->a.map, F->d.id); KX(map_term_image, &F->mb, F->b.map, F->d.id);
                KX(reindex, &F->eq, F->d.type, F->a.map);
                KF_CALL(conv_term_clause, &F->out, F->G, F->C, F->ma, F->mb, F->eq);
            }
        }
        break;
    }
    default: F->out = CV_UNEQUAL; break;
    }
done:
    head_free(&F->a); head_free(&F->b);
    KF_RET(F->out);
    KF_END;
}

KF_DECL_EXT_DROP(convert_type, ConvStatus, convert_type_PARAMS, convert_type_drop, const char *why; CheckStatus s1, s2; FaceId *cs; size_t nc, c; ConvStatus out, r; bool entered, settled;)
static void convert_type_drop(convert_type_F *F) { free(F->cs); F->cs = NULL; if (F->entered) { top_abandon(); F->entered = false; } }
KF_STEP(convert_type) {
    KF_BEGIN(convert_type);
    KF_CALL(scope_ok, &F->s1, F->G, F->chi, F->A, &F->why);
    if (F->s1 != CK_VALID) KF_RET(CV_UNRESOLVED);
    KF_CALL(scope_ok, &F->s2, F->G, F->chi, F->B, &F->why);
    if (F->s2 != CK_VALID) KF_RET(CV_UNRESOLVED);
    for (;;) {
        ENTER_F();
        KF_CALL(clauses_of, &F->nc, F->chi, &F->cs);
        F->out = CV_EQUAL;
        for (F->c = 0; F->c < F->nc; F->c++) { KF_CALL(conv_type_clause, &F->r, F->G, F->cs[F->c], F->A, F->B); F->out = and3(F->out, F->r); if (F->out == CV_UNEQUAL) break; }
        free(F->cs); F->cs = NULL;
        LEAVE_F();
        SETTLED_F();
        if (F->settled) KF_RET(F->out);
    }
    KF_END;
}
KF_SYNC_DEF(convert_type, ConvStatus, convert_type_PARAMS, convert_type(ContextId G, FaceId chi, RefId A, RefId B))
KF_DECL_EXT_DROP(convert_term, ConvStatus, convert_term_PARAMS, convert_term_drop, const char *why; CheckStatus s; FaceId *cs; size_t nc, c; ConvStatus out, r; bool entered, settled;)
static void convert_term_drop(convert_term_F *F) { free(F->cs); F->cs = NULL; if (F->entered) { top_abandon(); F->entered = false; } }
KF_STEP(convert_term) {
    KF_BEGIN(convert_term);
    KF_CALL(scope_ok, &F->s, F->G, F->chi, F->t, &F->why); if (F->s != CK_VALID) KF_RET(CV_UNRESOLVED);
    KF_CALL(scope_ok, &F->s, F->G, F->chi, F->u, &F->why); if (F->s != CK_VALID) KF_RET(CV_UNRESOLVED);
    KF_CALL(scope_ok, &F->s, F->G, F->chi, F->A, &F->why); if (F->s != CK_VALID) KF_RET(CV_UNRESOLVED);
    for (;;) {
        ENTER_F();
        KF_CALL(clauses_of, &F->nc, F->chi, &F->cs);
        F->out = CV_EQUAL;
        for (F->c = 0; F->c < F->nc; F->c++) { KF_CALL(conv_term_clause, &F->r, F->G, F->cs[F->c], F->t, F->u, F->A); F->out = and3(F->out, F->r); if (F->out == CV_UNEQUAL) break; }
        free(F->cs); F->cs = NULL;
        LEAVE_F();
        SETTLED_F();
        if (F->settled) KF_RET(F->out);
    }
    KF_END;
}
KF_SYNC_DEF(convert_term, ConvStatus, convert_term_PARAMS, convert_term(ContextId G, FaceId chi, RefId t, RefId u, RefId A))

/* A declared symbol is validated once: its declared type is a type over its
 * parameters, and its registered body (if any) checks against that type.
 * While a symbol's own body is being validated, its recursive occurrences
 * use the declared type: the signature's declaration is the assumption the
 * body is checked under (this does not prove termination). Every verdict
 * reached under that assumption is provisional on the symbol and is
 * committed by claim_release only when the body is accepted. */
#define validate_symbol_PARAMS(X) X(SymbolId, s) X(const char **, reason)
KF_DECL_DROP(validate_symbol, CheckStatus, validate_symbol_PARAMS, validate_symbol_drop, OWNED_FIELDS uint64_t key[1]; RefId type, body, gref; CheckStatus st; OriginId o; ContextId Gs; FaceId ftrue; uint64_t l;)
static void validate_symbol_drop(validate_symbol_F *F) { OWNED_DROP(F); }
KF_STEP(validate_symbol) {
    KF_BEGIN(validate_symbol);
  for (;;) {
    F->key[0] = F->s; F->why = NULL;
    KF_CALL(claim_index, &F->cl, CL_SYMBOL, F->key, 1);
    ENTER_F();
    KF_CALL(claim_acquire, &F->a, F->cl, &F->v, &F->why, NULL);
    if (F->a == ACQ_DONE) { LEAVE_F(); if (F->v != 1) *F->reason = F->why; SETTLED_F(); if (F->settled) KF_RET(ck_of(F->v)); continue; }
    if (F->a == ACQ_CYCLE) { if (top_frame()) KF_CALL(deps_push, NULL, &top_frame()->deps, F->cl); LEAVE_F(); require(tl_depth > 0 || tl_pending.n == 0, "declaration assumed at the top level"); KF_RET(CK_VALID); }   /* recursive occurrence: typed by the declaration */
    F->owns = true;
    F->type = global_type(F->s); NOTE_SYMBOL(F->s);
    F->st = CK_VALID;
    if (!F->type) { *F->reason = "symbol without a declared type"; F->st = CK_INVALID; }
    KX(global_ref, &F->gref, F->s);
    F->o = ref_origin(F->gref);
    KF_CALL(origin_context, &F->Gs, F->o);
    if (F->st == CK_VALID) KF_CALL(check_context, &F->st, F->Gs, F->reason);
    KF_CALL0(fc_true, &F->ftrue);
    if (F->st == CK_VALID) KF_CALL(level_of, &F->st, F->Gs, F->ftrue, F->type, &F->l, F->reason);
    F->body = global_body(F->s);
    if (F->st == CK_VALID && F->body) KF_CALL(check, &F->st, F->Gs, F->ftrue, F->body, F->type, F->reason);
    RELEASE_F(ck_code(F->st), *F->reason, NULL);
    LEAVE_F();
    SETTLED_F();
    if (F->settled) KF_RET(F->st);
  }
    KF_END;
}

KF_DECL_EXT(check_admission, CheckStatus, check_admission_PARAMS, const char *why; CheckStatus st; uint64_t v;)
KF_STEP(check_admission) {
    KF_BEGIN(check_admission);
    env_freeze();                        /* the freeze boundary precedes candidate admission */
    pthread_mutex_lock(&K.mu);
    for (;;) {
        F->v = global_env_version();
        /* a settled verdict for this environment is reused; an UNRESOLVED
         * verdict only within the attempt that produced it */
        if (!ADM.running && ADM.have && ADM.version == F->v && (ADM.status != CK_UNRESOLVED || ADM.attempt == K.attempt)) {
            F->st = ADM.status; *F->reason = ADM.reason; pthread_mutex_unlock(&K.mu); KF_RET(F->st);
        }
        if (!ADM.running) { ADM.running = true; ADM.version = F->v; ADM.attempt = K.attempt; pthread_mutex_unlock(&K.mu); break; }
        KF_WAIT(&K.cv, &K.mu, NULL, 0);
    }
    F->why = "";
    KF_CALL(check_signature, &F->st, &F->why);
    pthread_mutex_lock(&K.mu);
    ADM.running = false; ADM.have = true; ADM.status = F->st; ADM.reason = F->why;
    pthread_cond_broadcast(&K.cv);
    pthread_mutex_unlock(&K.mu);
    *F->reason = F->why;
    KF_RET(F->st);
    KF_END;
}
KF_SYNC_DEF(check_admission, CheckStatus, check_admission_PARAMS, check_admission(const char **reason))

/* §57 R1 / §59.4: a new candidate environment. The previous environment's
 * verdicts, claims, diagnostics and observations are retired (a fresh checker
 * session and a reset evaluator); registration is open again until the next
 * admission. This is a closed session boundary: every checker, compiler and
 * observation client must have returned and evaluator work must have
 * drained; the caller stops admitting new clients while crossing it. The
 * precondition is enforced here (no top-level request in progress, no
 * admission attempt running) and in eval_reset (no outstanding work). */
void check_open_environment(void) {
    pthread_mutex_lock(&K.mu);
    require(!ADM.running, "check_open_environment during a running admission attempt");
    require(__atomic_load_n(&K.clients, __ATOMIC_ACQUIRE) == 0, "check_open_environment while a checker client is in progress");
    size_t budget = K.budget;
    pthread_mutex_unlock(&K.mu);
    check_free(); check_init();
    pthread_mutex_lock(&K.mu); K.budget = budget; pthread_mutex_unlock(&K.mu);
    /* §79.3: a new admission session; persistent mathematical answers of the
     * evaluator survive and are filtered by their recorded dependencies */
    env_unfreeze();
}

KF_DECL_EXT(observe_checked, EvalResult *, observe_checked_PARAMS, CheckStatus st; Inference I; EvalResult *r;)
KF_STEP(observe_checked) {
    KF_BEGIN(observe_checked);
    /* public checked execution enters the admission gate first */
    KF_CALL(check_admission, &F->st, F->reason);
    if (F->st == CK_INVALID) { if (F->status) *F->status = W_INVALID; KF_RET(NULL); }
    if (F->st == CK_UNRESOLVED) { if (F->status) *F->status = W_STUCK; KF_RET(NULL); }
    KF_CALL(check_context, &F->st, F->G, F->reason);
    if (F->st == CK_VALID) { KF_CALL(infer, &F->I, F->G, context_assumption(F->G), F->t); F->st = F->I.st; if (F->st != CK_VALID) *F->reason = F->I.reason; }
    if (F->st == CK_INVALID) { if (F->status) *F->status = W_INVALID; KF_RET(NULL); }
    if (F->st == CK_UNRESOLVED) { if (F->status) *F->status = W_STUCK; KF_RET(NULL); }
    KX(whnf, &F->r, F->t, context_assumption(F->G), F->status);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(observe_checked, EvalResult *, observe_checked_PARAMS, observe_checked(ContextId G, RefId t, WhnfStatus *status, const char **reason))

/* formation: A is a type under chi; its universe level (equal under every
 * clause) is returned. Successful inference of some type for A is not enough
 * (§59.5): the inferred type is observed and must be a universe. */
KF_DECL_EXT_DROP(check_is_type, CheckStatus, check_is_type_PARAMS, check_is_type_drop, CheckStatus st; uint64_t lvl, l; bool have, entered, settled; FaceId *cs; size_t nc, c;)
static void check_is_type_drop(check_is_type_F *F) { free(F->cs); F->cs = NULL; if (F->entered) { top_abandon(); F->entered = false; } }
KF_STEP(check_is_type) {
    KF_BEGIN(check_is_type);
    for (;;) {
        ENTER_F();
        KF_CALL(scope_ok, &F->st, F->G, F->chi, F->A, F->reason);
        F->lvl = 0; F->have = false;
        if (F->st == CK_VALID) {
            KF_CALL(clauses_of, &F->nc, F->chi, &F->cs);
            for (F->c = 0; F->c < F->nc && F->st == CK_VALID; F->c++) {
                KF_CALL(level_of, &F->st, F->G, F->cs[F->c], F->A, &F->l, F->reason);
                if (F->st == CK_VALID) { if (F->have && F->l != F->lvl) { *F->reason = "type lives in different universes under different clauses"; F->st = CK_INVALID; } F->lvl = F->l; F->have = true; }
            }
            free(F->cs); F->cs = NULL;
        }
        LEAVE_F();
        SETTLED_F();
        if (F->settled) { if (F->st == CK_VALID && F->level) *F->level = F->lvl; KF_RET(F->st); }
    }
    KF_END;
}
KF_SYNC_DEF(check_is_type, CheckStatus, check_is_type_PARAMS, check_is_type(ContextId G, FaceId chi, RefId A, uint64_t *level, const char **reason))

KF_DECL_EXT(check_signature, CheckStatus, check_signature_PARAMS, size_t n; SymbolId s; CheckStatus st;)
KF_STEP(check_signature) {
    KF_BEGIN(check_signature);
    F->n = global_count();
    for (F->s = 1; F->s <= F->n; F->s++) { KF_CALL(validate_symbol, &F->st, F->s, F->reason); if (F->st != CK_VALID) KF_RET(F->st); }
    KF_RET(CK_VALID);
    KF_END;
}
KF_SYNC_DEF(check_signature, CheckStatus, check_signature_PARAMS, check_signature(const char **reason))

#include "check.h"
#include "lib.h"
#include "compiler.h"

/* ------------------------------------------------------------------ */
/* state: request claims, memo, budget                                  */

/* Every memoized checking request (context validity, typed map, origin
 * validation, symbol validation, clause conversion) is a *claim*: one
 * producer computes it, every other client waits for that producer's
 * outcome, and the outcome is published once. A request already running on
 * the same thread, or on a thread that is (transitively) waiting for this
 * thread, is a genuine cycle in the demand graph: for conversion, origins,
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
    uint64_t owner;         /* producing thread while running */
    uint64_t result;        /* verdict code when done: 1 valid/equal, 2 invalid/unequal, 3 unresolved (this attempt only) */
    uint64_t attempt;       /* admission attempt that produced an unresolved outcome */
    const char *reason;
    uint64_t aux[3];        /* origin: context, required face, type */
    Words deps;             /* symbol claims this verdict is provisional on */
    bool is_symbol;
} Claim;

typedef struct { size_t claim; Words deps; } Frame;

static struct {
    WordMap idx;            /* (kind, words...) → claim index + 1 */
    VEC(Claim) recs;
    pthread_mutex_t mu; pthread_cond_t cv;
    VEC(uint64_t) wait_on;  /* per thread id: claim index + 1 the thread is blocked on (0 = none) */
    VEC(uint8_t) assume;    /* per thread id: released from a wait on a symbol with "typed by the declaration" */
    uint64_t ntids;
    size_t budget;
    uint64_t attempt;       /* §59.4: a changed budget or a retry begins a new attempt */
    size_t clients;         /* top-level requests in progress (atomic): the session boundary requires zero */
} K;

/* §59.4: thread identities are session-qualified; the generation allocator
 * survives check_free so a reused client thread re-registers in a new session */
static uint64_t session_gen;
static __thread uint64_t tl_tid, tl_gen;

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
static __thread VEC(Frame) tl_frames;
static __thread Words tl_pending;        /* symbols a finished top-level verdict still rests on */
static __thread size_t tl_steps, tl_depth, tl_budget;   /* the budget is fixed for a top-level request when it enters */
static const char *R_BUDGET = "budget exhausted";

enum { CL_CTX = 1, CL_MAP, CL_ORIGIN, CL_SYMBOL, CL_CONV, CL_TVIEW, CL_TBOUND };
typedef enum { ACQ_OWNER, ACQ_DONE, ACQ_CYCLE } Acq;

void check_init(void) {
    memset(&K, 0, sizeof K);
    memset(&ADM, 0, sizeof ADM);
    memset(&DIAG, 0, sizeof DIAG); pthread_mutex_init(&DIAG.mu, NULL);
    session_gen++;
    K.attempt = 1;
    wordmap_init(&K.idx);
    pthread_mutex_init(&K.mu, NULL); pthread_cond_init(&K.cv, NULL);
    vec_push(&K.wait_on, 0); vec_push(&K.assume, 0);
}
void check_free(void) {
    for (size_t k = 0; k < K.recs.len; k++) words_free(&K.recs.data[k].deps);
    vec_free(&K.recs); vec_free(&K.wait_on); vec_free(&K.assume);
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
const char *check_status_name(CheckStatus s) { return s == CK_VALID ? "VALID" : s == CK_INVALID ? "INVALID" : "UNRESOLVED"; }
const char *conv_status_name(ConvStatus s) { return s == CV_EQUAL ? "EQUAL" : s == CV_UNEQUAL ? "UNEQUAL" : "UNRESOLVED"; }

static bool budget_ok(void) { tl_steps++; size_t b = tl_depth ? tl_budget : K.budget; return b == 0 || tl_steps <= b; }

/* thread identity, assigned on first use (under K.mu) */
static uint64_t tid_locked(void) {
    if (!tl_tid || tl_gen != session_gen) { tl_tid = ++K.ntids; tl_gen = session_gen; vec_push(&K.wait_on, 0); vec_push(&K.assume, 0); }
    return tl_tid;
}

/* every claim belongs to one definition environment (§57 R1 / §59.4): the
 * key carries the environment version, so a successful candidate mutation
 * makes every earlier environment-dependent verdict unreachable */
static size_t claim_index_locked(uint64_t kind, const uint64_t *w, size_t n) {
    uint64_t key[10] = { kind, global_env_version() }; memcpy(key + 2, w, n * sizeof(uint64_t));
    uint64_t v;
    if (wordmap_get(&K.idx, key, n + 2, &v)) return (size_t)v - 1;
    Claim c; memset(&c, 0, sizeof c); words_init(&c.deps); c.is_symbol = kind == CL_SYMBOL;
    vec_push(&K.recs, c);
    wordmap_put(&K.idx, key, n + 2, K.recs.len);
    return K.recs.len - 1;
}

static bool words_contains(const Words *w, uint64_t x) { for (size_t k = 0; k < w->n; k++) if (w->w[k] == x) return true; return false; }
static void words_add(Words *w, uint64_t x) { if (!words_contains(w, x)) words_push(w, x); }
static void words_remove(Words *w, uint64_t x) { size_t j = 0; for (size_t k = 0; k < w->n; k++) if (w->w[k] != x) w->w[j++] = w->w[k]; w->n = j; }

/* Would blocking on a claim owned by `owner` close a wait cycle back to this
 * thread? When it would, and some thread on the cycle is blocked on a
 * *symbol* claim, that wait is the one to yield: the symbol's declaration
 * becomes that thread's assumption (exactly what a single thread does when
 * it meets its own running symbol), and the caller may block. Only a cycle
 * with no symbol on it is a genuine cyclic request. */
static bool wait_cycle_locked(uint64_t owner, uint64_t me, uint64_t *symbol_waiter) {
    uint64_t cur = owner;
    *symbol_waiter = 0;
    for (uint64_t steps = 0; steps <= K.ntids; steps++) {
        if (cur == me) return true;
        uint64_t w = K.wait_on.data[cur];
        if (!w) return false;
        Claim *c = &K.recs.data[w - 1];
        if (c->is_symbol && c->state == 1 && !*symbol_waiter) *symbol_waiter = cur;
        if (c->state != 1) return false;
        cur = c->owner;
    }
    return true;
}
/* decide how to treat a claim owned by another thread: true = block on it,
 * false = it is a genuine cycle */
static bool may_block_locked(uint64_t owner, uint64_t me) {
    uint64_t sw;
    if (!wait_cycle_locked(owner, me, &sw)) return true;
    if (!sw) return false;
    K.assume.data[sw] = 1;
    pthread_cond_broadcast(&K.cv);
    return true;
}

static void resolve_locked(void);
static Frame *top_frame(void) { return tl_frames.len ? &tl_frames.data[tl_frames.len - 1] : NULL; }
static void frame_push(size_t claim) { Frame f; f.claim = claim; words_init(&f.deps); vec_push(&tl_frames, f); }
static void inherit_locked(const Words *deps) { Frame *f = top_frame(); if (f) for (size_t k = 0; k < deps->n; k++) words_add(&f->deps, deps->w[k]); }

/* acquire claim `c`: ACQ_OWNER (this thread computes it, a frame is pushed),
 * ACQ_DONE (verdict copied out, provisional premises inherited), or
 * ACQ_CYCLE (the request is on this thread's own demand path). */
static Acq claim_acquire(size_t c, uint64_t *result, const char **reason, uint64_t aux[3]) {
    pthread_mutex_lock(&K.mu);
    uint64_t me = tid_locked();
    size_t assumed = SIZE_MAX;       /* a premise taken as a declaration assumption after a cycle */
    for (;;) {
        /* K.recs may have been reallocated during any wait: records are
         * reacquired by index at the top of every iteration (§59.4) */
        Claim *r = &K.recs.data[c];
        if (r->state == 2 && r->result == 3 && r->attempt != K.attempt) r->state = 0;   /* an old attempt's unresolved outcome */
        if (r->state == 2) {
            /* a verdict provisional on symbols: a rejected premise withdraws
             * it (recomputed now, by us); a premise another thread is still
             * validating is waited for unless waiting would close a cycle
             * (then the declaration is our assumption too) */
            bool waited = false;
            for (size_t k = 0; k < r->deps.n && !waited; k++) {
                size_t d = r->deps.w[k];
                Claim *dc = &K.recs.data[d];
                if (dc->state == 2 && dc->result != 1) { resolve_locked(); waited = true; break; }
                if (dc->state == 1 && dc->owner != me && d != assumed && may_block_locked(dc->owner, me)) {
                    K.wait_on.data[me] = d + 1;
                    pthread_cond_wait(&K.cv, &K.mu);
                    K.wait_on.data[me] = 0;
                    if (K.assume.data[me]) { K.assume.data[me] = 0; assumed = d; }   /* told to assume: inherit on the next pass */
                    waited = true;
                }
            }
            if (waited) continue;
            *result = r->result; if (reason) *reason = r->reason; if (aux) memcpy(aux, r->aux, sizeof r->aux);
            inherit_locked(&r->deps);
            pthread_mutex_unlock(&K.mu);
            return ACQ_DONE;
        }
        if (r->state == 0) {
            r->state = 1; r->owner = me;
            frame_push(c);
            pthread_mutex_unlock(&K.mu);
            return ACQ_OWNER;
        }
        if (r->owner == me || !may_block_locked(r->owner, me)) { pthread_mutex_unlock(&K.mu); return ACQ_CYCLE; }
        K.wait_on.data[me] = c + 1;
        pthread_cond_wait(&K.cv, &K.mu);
        K.wait_on.data[me] = 0;
        if (K.assume.data[me]) { K.assume.data[me] = 0; pthread_mutex_unlock(&K.mu); return ACQ_CYCLE; }
    }
}

/* Resolve provisional verdicts against the symbols they rest on:
 *   - a premise rejected or unresolved withdraws the dependent verdict, which
 *     is recomputed on demand;
 *   - a committed premise is discharged;
 *   - a set of accepted symbol verdicts resting only on each other (mutual
 *     recursion validated from both ends) is committed together: it is the
 *     greatest set of accepted symbols closed under their premises.
 * Runs under K.mu after a symbol verdict is published. */
static void resolve_locked(void) {
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t c = 0; c < K.recs.len; c++) {
            Claim *r = &K.recs.data[c];
            if (r->state != 2 || r->deps.n == 0) continue;
            for (size_t k = 0; k < r->deps.n; ) {
                Claim *d = &K.recs.data[r->deps.w[k]];
                if (d->state == 2 && d->result != 1) { r->state = 0; r->deps.n = 0; changed = true; break; }
                if (d->state == 2 && d->result == 1 && d->deps.n == 0) { words_remove(&r->deps, r->deps.w[k]); changed = true; continue; }
                k++;
            }
        }
        bool *in = calloc(K.recs.len ? K.recs.len : 1, sizeof(bool));
        size_t nin = 0;
        for (size_t c = 0; c < K.recs.len; c++) { Claim *r = &K.recs.data[c]; if (r->is_symbol && r->state == 2 && r->result == 1 && r->deps.n) { in[c] = true; nin++; } }
        bool shrink = true;
        while (shrink && nin) {
            shrink = false;
            for (size_t c = 0; c < K.recs.len; c++) {
                if (!in[c]) continue;
                Claim *r = &K.recs.data[c];
                for (size_t k = 0; k < r->deps.n; k++) {
                    Claim *d = &K.recs.data[r->deps.w[k]];
                    bool ok = in[r->deps.w[k]] || (d->state == 2 && d->result == 1 && d->deps.n == 0);
                    if (!ok) { in[c] = false; nin--; shrink = true; break; }
                }
            }
        }
        for (size_t c = 0; c < K.recs.len; c++) if (in[c]) { K.recs.data[c].deps.n = 0; changed = true; }
        free(in);
    }
}

/* release the claim this thread owns at the top of its stack. result 0 = no
 * verdict (the claim returns to absent); otherwise the verdict is published,
 * provisional on the running symbols the computation relied on. */
static void claim_release(size_t c, uint64_t result, const char *reason, const uint64_t aux[3]) {
    pthread_mutex_lock(&K.mu);
    Frame *f = top_frame();
    require(f && f->claim == c, "claim release out of order");
    Words deps = f->deps; tl_frames.len--;
    Claim *r = &K.recs.data[c];
    if (r->is_symbol) words_remove(&deps, c);        /* self-recursion is closed by this verdict */
    if (result == 0) {
        /* no verdict in this attempt: the attempt's waiters receive the
         * unresolved outcome (one producer per attempt, §59.4); a new attempt
         * recomputes */
        r->state = 2; r->result = 3; r->reason = reason ? reason : "unresolved: no verdict in this attempt"; r->attempt = K.attempt;
        r->deps.n = 0;
    } else {
        r->state = 2; r->result = result; r->reason = reason;
        if (aux) memcpy(r->aux, aux, sizeof r->aux); else memset(r->aux, 0, sizeof r->aux);
        r->deps.n = 0; words_append(&r->deps, deps.w, deps.n);
    }
    if (r->is_symbol) resolve_locked();
    inherit_locked(&deps);
    words_free(&deps);
    pthread_cond_broadcast(&K.cv);
    pthread_mutex_unlock(&K.mu);
}

/* a recursive occurrence of a running symbol: typed by its declaration,
 * provisionally on that symbol's validation */
static void assume_symbol(size_t c) {
    pthread_mutex_lock(&K.mu);
    Frame *f = top_frame();
    if (f) words_add(&f->deps, c);
    pthread_mutex_unlock(&K.mu);
}

/* Top-level requests run in a root frame. A root frame may end with
 * provisional premises only when a symbol validated on another thread was
 * taken as an assumption to break a wait cycle; the verdict is then not
 * final: top_settled waits for those validations and asks the caller to
 * recompute (the recomputation finds committed or withdrawn claims). */
static void top_enter(void) { if (tl_depth++ == 0) { __atomic_add_fetch(&K.clients, 1, __ATOMIC_ACQ_REL); tl_steps = 0; tl_budget = __atomic_load_n(&K.budget, __ATOMIC_ACQUIRE); frame_push(0); } }
static void top_leave(void) {
    if (--tl_depth == 0) {
        Frame *f = top_frame(); require(f && f->claim == 0, "root frame mismatch");
        tl_pending.n = 0; words_append(&tl_pending, f->deps.w, f->deps.n);
        words_free(&f->deps); tl_frames.len--;
        if (tl_frames.len == 0) vec_free(&tl_frames);   /* thread-local storage is released at the outermost exit */
        __atomic_sub_fetch(&K.clients, 1, __ATOMIC_ACQ_REL);
    }
}
static bool top_settled(void) {
    if (tl_depth > 0) return true;
    if (tl_pending.n == 0) { words_free(&tl_pending); return true; }
    pthread_mutex_lock(&K.mu);
    uint64_t me = tid_locked();
    for (size_t k = 0; k < tl_pending.n; k++) {
        size_t d = tl_pending.w[k];
        while (K.recs.data[d].state == 1 && K.recs.data[d].owner != me) {
            K.wait_on.data[me] = d + 1;
            pthread_cond_wait(&K.cv, &K.mu);
            K.wait_on.data[me] = 0;
            K.assume.data[me] = 0;
        }
    }
    resolve_locked();
    pthread_mutex_unlock(&K.mu);
    words_free(&tl_pending);
    return false;
}
#define ENTER() top_enter()
#define LEAVE() top_leave()

static uint64_t ck_code(CheckStatus s) { return s == CK_VALID ? 1 : s == CK_INVALID ? 2 : 0; }
static CheckStatus ck_of(uint64_t v) { return v == 1 ? CK_VALID : v == 2 ? CK_INVALID : CK_UNRESOLVED; }
static uint64_t cv_code(ConvStatus s) { return s == CV_EQUAL ? 1 : s == CV_UNEQUAL ? 2 : 0; }
static ConvStatus cv_of(uint64_t v) { return v == 1 ? CV_EQUAL : v == 2 ? CV_UNEQUAL : CV_UNRESOLVED; }

/* ------------------------------------------------------------------ */
/* faces: clauses and clause substitution                               */

static size_t clauses_of(FaceId chi, FaceId **out) {
    Dnf d; fc_to_dnf(chi, &d);
    FaceId *cs = malloc((d.n ? d.n : 1) * sizeof(FaceId));
    for (size_t i = 0; i < d.n; i++) { Dnf one; dnf_init(&one); dnf_add_clause(&one, d.c[i].a, d.c[i].n); cs[i] = fc_from_dnf(&one); }
    size_t n = d.n;
    dnf_free(&d);
    *out = cs;
    return n;
}

/* the endpoints fixed by a single clause, as a dimension map */
static MapId clause_map(FaceId C) {
    Dnf d; fc_to_dnf(C, &d);
    MapBuilder b; mapb_init(&b);
    if (d.n == 1) for (size_t k = 0; k < d.c[0].n; k++) mapb_dim(&b, FC_LIT_DIM(d.c[0].a[k]), FC_LIT_EPS(d.c[0].a[k]) ? iv_one() : iv_zero());
    dnf_free(&d);
    return mapb_finish(&b);
}
static bool iv_equal_under(FaceId C, IntervalId r, IntervalId s) { MapId m = clause_map(C); return iv_reindex(r, m) == iv_reindex(s, m); }
static bool fc_equal_under(FaceId C, FaceId a, FaceId b) { return fc_meet(C, a) == fc_meet(C, b); }

static bool dims_declared(ContextId G, DimSetId S) {
    size_t n; const uint64_t *ds = dimset_get(S, &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_dim(G, ds[k])) return false;
    return true;
}
static DimSetId face_dims(FaceId f) { Words w; words_init(&w); fc_dims(f, &w); DimSetId s = dimset_make(w.w, w.n); words_free(&w); return s; }
static DimSetId iv_dimset(IntervalId r) { Words w; words_init(&w); iv_dims(r, &w); DimSetId s = dimset_make(w.w, w.n); words_free(&w); return s; }

/* ------------------------------------------------------------------ */
/* fresh comparison identities (distinct owner namespace)               */

/* keyed by the comparison request (both sides and the expected type head) */
static TermVarId conv_var(RefId l, RefId r, RefId head, uint64_t slot, RefId type) {
    KeyWord kw[5] = { { KW_CONST, 5000 }, { KW_REF, l }, { KW_REF, r }, { KW_REF, head }, { KW_CONST, slot } };
    return fresh_term_keyed(kw, 5, type);
}
static DimVarId conv_dim(RefId l, RefId r, uint64_t slot) {
    KeyWord kw[4] = { { KW_CONST, 5001 }, { KW_REF, l }, { KW_REF, r }, { KW_CONST, slot } };
    return fresh_dim_keyed(kw, 4);
}

/* ------------------------------------------------------------------ */
/* observation helpers                                                  */

static CheckStatus observe(FaceId C, RefId t, EvalResult **out, const char **reason) {
    WhnfStatus st;
    EvalResult *r = whnf(t, C, &st);
    if (st == W_OK) { *out = r; return CK_VALID; }
    *out = NULL;
    if (st == W_STUCK) { *reason = "unresolved: weak-head observation did not complete (cyclic or suspended demand)"; return CK_UNRESOLVED; }
    *reason = r && r->message ? r->message : "invalid observation";
    return CK_INVALID;
}

/* weak-head observe a type and require a given introduction tag */
static CheckStatus observe_head(FaceId C, RefId T, Tag want, RefId *head, const char **reason) {
    EvalResult *r;
    CheckStatus s = observe(C, T, &r, reason);
    if (s != CK_VALID) return s;
    if (r->cls != R_INTRODUCTION) { *reason = "expected a type former, found a neutral or system"; return CK_INVALID; }
    Head h; open_ref(r->ref, &h); Tag tag = h.tag; head_free(&h);
    if (tag != want) { *reason = "type former mismatch"; return CK_INVALID; }
    *head = r->ref;
    return CK_VALID;
}

static CheckStatus infer_clause(ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static CheckStatus check_clause(ContextId G, FaceId C, RefId t, RefId A, const char **reason);
static ConvStatus conv_type_clause(ContextId G, FaceId C, RefId A, RefId B);
static ConvStatus conv_term_clause(ContextId G, FaceId C, RefId t, RefId u, RefId A);

/* the universe level of a type under a clause */
static CheckStatus level_of(ContextId G, FaceId C, RefId A, uint64_t *lvl, const char **reason) {
    RefId T; CheckStatus s = infer_clause(G, C, A, &T, reason);
    if (s != CK_VALID) return s;
    RefId U;
    s = observe_head(C, T, T_UNIVERSE, &U, reason);
    if (s != CK_VALID) { if (s == CK_INVALID) *reason = "not a type: its type is not a universe"; return s; }
    Head h; open_ref(U, &h); *lvl = h.payload; head_free(&h);
    return CK_VALID;
}

/* ------------------------------------------------------------------ */
/* contexts                                                             */

ContextId origin_context(OriginId C) {
    size_t nd, nt;
    const uint64_t *ds = dimset_get(origin_fd(C), &nd);
    const uint64_t *xs = varset_get(origin_ft(C), &nt);
    CtxDecl *decls = malloc((nd + nt + 1) * sizeof(CtxDecl));
    size_t n = 0;
    for (size_t k = 0; k < nd; k++) { decls[n].sort = S_DIM; decls[n].id = ds[k]; decls[n].type = 0; n++; }
    /* term variables in dependency order: a variable follows the free
     * variables of its declared type */
    bool *placed = calloc(nt ? nt : 1, sizeof(bool));
    size_t done = 0;
    while (done < nt) {
        bool progress = false;
        for (size_t k = 0; k < nt; k++) {
            if (placed[k]) continue;
            size_t m; const uint64_t *fv = varset_get(ref_freevars(term_var_type(xs[k])), &m);
            bool ready = true;
            for (size_t q = 0; q < m && ready; q++) { bool found = false; for (size_t j = 0; j < nt; j++) if (xs[j] == fv[q] && placed[j]) found = true; if (!found) ready = false; }
            if (!ready) continue;
            decls[n].sort = S_TERM; decls[n].id = xs[k]; decls[n].type = term_var_type(xs[k]); n++;
            placed[k] = true; done++; progress = true;
        }
        require(progress, "cyclic declaration dependency in origin boundary");
    }
    free(placed);
    ContextId ctx = context_make(n, decls, origin_required(C));
    free(decls);
    return ctx;
}

CheckStatus check_context(ContextId G, const char **reason) {
  for (;;) {
    uint64_t key[1] = { G }, v; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_CTX, key, 1); pthread_mutex_unlock(&K.mu);
    ENTER();
    Acq a = claim_acquire(cl, &v, &why, NULL);
    if (a == ACQ_DONE) { LEAVE(); if (v != 1) *reason = why; if (top_settled()) return ck_of(v); continue; }
    if (a == ACQ_CYCLE) { LEAVE(); (void)top_settled(); *reason = "unresolved: context validation depends on itself"; return CK_UNRESOLVED; }
    CheckStatus st = CK_VALID;
    size_t n = context_size(G);
    FaceId assumption = context_assumption(G);
    /* 1. unique identities; the assumption uses declared dimensions */
    uint64_t *dims = malloc((n ? n : 1) * sizeof(uint64_t)); size_t nd = 0;
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(G, k);
        for (size_t j = 0; j < k; j++) { CtxDecl e = context_decl(G, j); if (e.sort == d.sort && e.id == d.id) { *reason = "duplicate declaration"; st = CK_INVALID; } }
        if (d.sort == S_DIM) dims[nd++] = d.id;
    }
    if (st == CK_VALID) {
        DimSetId all = dimset_make(dims, nd);
        size_t m; const uint64_t *fd = dimset_get(face_dims(assumption), &m);
        for (size_t q = 0; q < m; q++) if (!dimset_contains(all, fd[q])) { *reason = "assumption mentions an undeclared dimension"; st = CK_INVALID; }
    }
    /* 2. each term declaration's type and required face use only the prefix;
     * the type is a type under the assumption projected to the prefix dims,
     * and it is compatible (convertible under each clause) with the
     * variable's recorded declaration (§2, §33 item 3) */
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(G, k);
        if (d.sort != S_TERM) continue;
        CtxDecl *prefix = malloc((k ? k : 1) * sizeof(CtxDecl));
        uint64_t *pd = malloc((k ? k : 1) * sizeof(uint64_t)); size_t npd = 0;
        for (size_t j = 0; j < k; j++) { prefix[j] = context_decl(G, j); if (prefix[j].sort == S_DIM) pd[npd++] = prefix[j].id; }
        DimSetId pds = dimset_make(pd, npd);
        FaceId proj = fc_project(assumption, dimset_get(pds, &npd), npd);
        ContextId P = context_make(k, prefix, proj);
        free(prefix); free(pd);
        RefId decl = term_var_type(d.id);
        RefId both[2] = { d.type, decl };
        for (int w = 0; w < 2 && st == CK_VALID; w++) {
            size_t m; const uint64_t *fv = varset_get(ref_freevars(both[w]), &m);
            for (size_t q = 0; q < m && st == CK_VALID; q++) if (!context_declares_term(P, fv[q], NULL)) { *reason = "declaration type mentions a variable not declared earlier"; st = CK_INVALID; }
            if (st == CK_VALID && !dims_declared(P, ref_support(both[w]))) { *reason = "declaration type mentions a dimension not declared earlier"; st = CK_INVALID; }
        }
        if (st == CK_VALID && !dims_declared(P, face_dims(term_var_required(d.id)))) { *reason = "declaration's required face mentions a dimension not declared earlier"; st = CK_INVALID; }
        if (st == CK_VALID) {
            /* §59.2: a declaration partial on φ_x forms under the projected
             * prefix assumption conjoined with φ_x (its type may use earlier
             * declarations available only there); scope was checked above */
            FaceId *cs; size_t nc = clauses_of(fc_meet(proj, term_var_required(d.id)), &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                uint64_t l; st = level_of(P, cs[c], d.type, &l, reason);
                if (st == CK_VALID && decl != d.type) {
                    st = level_of(P, cs[c], decl, &l, reason);
                    if (st != CK_VALID) break;
                    ConvStatus cv = conv_type_clause(P, cs[c], d.type, decl);
                    if (cv == CV_UNEQUAL) { *reason = "declared type is not convertible to the variable's declaration"; st = CK_INVALID; }
                    else if (cv == CV_UNRESOLVED) { *reason = "unresolved: declaration type compatibility"; st = CK_UNRESOLVED; }
                }
            }
            free(cs);
        }
    }
    free(dims);
    claim_release(cl, ck_code(st), *reason, NULL);
    LEAVE();
    if (top_settled()) return st;
  }
}

/* the judgment Γ;χ: the context carries χ as its assumption, so that
 * declaration types are validated under the same face they are used under */
static ContextId under(ContextId G, FaceId C) {
    if (context_assumption(G) == C) return G;
    size_t n = context_size(G);
    CtxDecl *ds = malloc((n ? n : 1) * sizeof(CtxDecl));
    for (size_t k = 0; k < n; k++) ds[k] = context_decl(G, k);
    ContextId out = context_make(n, ds, C);
    free(ds);
    return out;
}
static ContextId extend_term(ContextId G, TermVarId x, RefId type) { return context_extend_term(G, x, type); }
static ContextId extend_dim(ContextId G, DimVarId j) { return context_extend_dim(G, j); }

/* ------------------------------------------------------------------ */
/* typed maps and origins (substitution lemma)                          */

CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason) {
  Delta = under(Delta, psi); Gamma = under(Gamma, chi);
  for (;;) {
    uint64_t key[5] = { Delta, psi, sigma, Gamma, chi }, v; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_MAP, key, 5); pthread_mutex_unlock(&K.mu);
    ENTER();
    Acq a = claim_acquire(cl, &v, &why, NULL);
    if (a == ACQ_DONE) { LEAVE(); if (v != 1) *reason = why; if (top_settled()) return ck_of(v); continue; }
    if (a == ACQ_CYCLE) { LEAVE(); (void)top_settled(); *reason = "unresolved: map validation depends on itself"; return CK_UNRESOLVED; }
    CheckStatus st = check_context(Gamma, reason);
    if (st == CK_VALID) st = check_context(Delta, reason);
    size_t n = context_size(Gamma);
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(Gamma, k);
        if (d.sort == S_DIM) {
            /* the dimension image is an interval over the source dimensions */
            if (!dims_declared(Delta, iv_dimset(map_dim_image(sigma, d.id)))) { *reason = "dimension image mentions an undeclared source dimension"; st = CK_INVALID; }
            continue;
        }
        /* the term image (the identity image when the entry is absent) is in
         * the source scope whatever the source face: only the typing
         * obligations below are vacuous on false (§33) */
        RefId image = map_term_image(sigma, d.id);
        { size_t m; const uint64_t *fv = varset_get(ref_freevars(image), &m);
          if (!ref_validate(image, reason)) { st = CK_INVALID; break; }
          for (size_t q = 0; q < m && st == CK_VALID; q++) if (!context_declares_term(Delta, fv[q], NULL)) { *reason = "term image mentions a variable not declared in the source context"; st = CK_INVALID; }
          if (st == CK_VALID && !dims_declared(Delta, ref_support(image))) { *reason = "term image mentions a dimension not declared in the source context"; st = CK_INVALID; } }
        if (st != CK_VALID) break;
        /* the target declaration's required-face obligation: a declaration
         * partial on phi_x is only used under phi_x in the target, so its
         * image is checked against A[sigma] under psi ∧ phi_x[sigma] */
        RefId Asub = reindex(d.type, sigma);
        FaceId where = fc_meet(psi, fc_reindex(term_var_required(d.id), sigma));
        FaceId *cs; size_t nc = clauses_of(where, &cs);
        for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(Delta, cs[c], image, Asub, reason);
        free(cs);
    }
    if (st == CK_VALID && !fc_entails(psi, fc_reindex(chi, sigma))) { *reason = "source face does not entail the substituted target assumption"; st = CK_INVALID; }
    claim_release(cl, ck_code(st), *reason, NULL);
    LEAVE();
    if (top_settled()) return st;
  }
}

static CheckStatus infer_head(ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static CheckStatus validate_symbol(SymbolId s, const char **reason);

CheckStatus check_origin(OriginId C, ContextId *ctx_out, FaceId *req_out, RefId *type_out, const char **reason) {
  for (;;) {
    uint64_t key[1] = { C }, v, aux[3] = { 0, 0, 0 }; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_ORIGIN, key, 1); pthread_mutex_unlock(&K.mu);
    ENTER();
    Acq a = claim_acquire(cl, &v, &why, aux);
    if (a == ACQ_DONE) {
        LEAVE();
        if (!top_settled()) continue;
        if (v == 1) { if (ctx_out) *ctx_out = aux[0]; if (req_out) *req_out = aux[1]; if (type_out) *type_out = aux[2]; return CK_VALID; }
        *reason = why; return ck_of(v);
    }
    if (a == ACQ_CYCLE) { LEAVE(); (void)top_settled(); *reason = "unresolved: origin validation depends on itself (cyclic dependency)"; return CK_UNRESOLVED; }
    ContextId ctx = origin_context(C);
    FaceId req = origin_required(C);
    RefId type = 0;
    CheckStatus st = check_context(ctx, reason);
    if (st == CK_VALID) {
        RefId t = make_view(C, map_identity());
        /* a system's own required face is its coverage; the body is checked under it */
        FaceId *cs; size_t nc = clauses_of(req, &cs);
        RefId *types = malloc((nc ? nc : 1) * sizeof(RefId));
        for (size_t c = 0; c < nc && st == CK_VALID; c++) st = infer_head(ctx, cs[c], t, &types[c], reason);
        if (st == CK_VALID) {
            bool same = true;
            for (size_t c = 1; c < nc; c++) if (types[c] != types[0]) same = false;
            if (nc == 0) type = mk_system(0, NULL, NULL);            /* required face false: vacuous */
            else if (same) type = types[0];
            else type = mk_system(nc, cs, types);
        }
        free(types); free(cs);
    }
    aux[0] = ctx; aux[1] = req; aux[2] = type;
    claim_release(cl, ck_code(st), *reason, aux);
    LEAVE();
    if (!top_settled()) continue;
    if (st == CK_VALID) { if (ctx_out) *ctx_out = ctx; if (req_out) *req_out = req; if (type_out) *type_out = type; }
    return st;
  }
}

/* ------------------------------------------------------------------ */
/* inference                                                            */

static CheckStatus glue_data_ok(ContextId G, FaceId C, RefId A, FaceId alpha, RefId T, RefId e, uint64_t *lvl, const char **reason) {
    CheckStatus st = level_of(G, C, A, lvl, reason);
    if (st != CK_VALID) return st;
    if (!dims_declared(G, face_dims(alpha))) { *reason = "Glue face mentions an undeclared dimension"; return CK_INVALID; }
    FaceId Ca = fc_meet(C, alpha);
    if (fc_is_false(Ca)) return CK_VALID;              /* vacuous */
    FaceId *cs; size_t nc = clauses_of(Ca, &cs);
    for (size_t c = 0; c < nc && st == CK_VALID; c++) {
        uint64_t lT;
        st = level_of(G, cs[c], T, &lT, reason);
        if (st == CK_VALID && lT != *lvl) { *reason = "Glue fibre type is not in the base's universe"; st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, cs[c], e, mk_equiv(lT, *lvl, T, A), reason);
    }
    free(cs);
    return st;
}

/* §59.1: every required type position carries its level; a missing or
 * differing annotation is INVALID */
static bool level_ok1(uint64_t levels, uint64_t inferred) { return levels_first(levels) == inferred; }
static bool level_ok2(uint64_t levels, uint64_t i, uint64_t j) { return levels_first(levels) == i && levels_second(levels) == j; }
static const char *level_why(uint64_t levels, const char *differs) { return levels == LEVELS_NONE || levels_first(levels) == LEVEL_NONE ? "missing universe annotation at a required type position (§59.1)" : differs; }

static CheckStatus infer_head(ContextId G, FaceId C, RefId t, RefId *type, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    if (ref_is_var(t)) {
        TermVarId x = ref_var_id(t);
        RefId ty;
        if (!context_declares_term(G, x, &ty)) { *reason = "unbound variable"; return CK_INVALID; }
        if (!fc_entails(C, term_var_required(x))) { *reason = "variable used outside its required face"; return CK_INVALID; }
        *type = ty;
        return CK_VALID;
    }
    Head h; open_ref(t, &h);
    CheckStatus st = CK_VALID;
    switch (h.tag) {
    case T_UNIVERSE: *type = mk_universe(level_succ(h.payload)); break;   /* checked successor: overflow is a host failure (§59.1) */
    case T_PI: case T_SIGMA: {
        uint64_t i, j;
        st = level_of(G, C, HF(&h, 0).id, &i, reason);
        if (st != CK_VALID) break;
        TermOpen o = resolve_term_binder(t, 0, 1);
        st = level_of(extend_term(G, o.x, o.type), C, o.body, &j, reason);
        if (st == CK_VALID && !level_ok2(h.levels, i, j)) { *reason = level_why(h.levels, "universe annotation differs from the formation levels"); st = CK_INVALID; }
        if (st == CK_VALID) *type = mk_universe(i > j ? i : j);
        break;
    }
    case T_LAM: {
        uint64_t i;
        st = level_of(G, C, HF(&h, 0).id, &i, reason);
        if (st != CK_VALID) break;
        if (!level_ok1(h.levels, i)) { *reason = level_why(h.levels, "lambda domain level annotation differs"); st = CK_INVALID; break; }
        TermOpen o = resolve_term_binder(t, 0, 1);
        RefId B; uint64_t j;
        st = infer_clause(extend_term(G, o.x, o.type), C, o.body, &B, reason);
        if (st == CK_VALID) st = level_of(extend_term(G, o.x, o.type), C, B, &j, reason);
        if (st == CK_VALID) *type = mk_pi_lv(i, j, o.x, o.type, B);
        break;
    }
    case T_APP: {
        RefId Tf, P;
        st = infer_clause(G, C, HF(&h, 0).id, &Tf, reason);
        if (st != CK_VALID) break;
        st = observe_head(C, Tf, T_PI, &P, reason);
        if (st != CK_VALID) { if (st == CK_INVALID) *reason = "application of a non-function"; break; }
        Head hp; open_ref(P, &hp); RefId dom = HF(&hp, 0).id; head_free(&hp);
        st = check_clause(G, C, HF(&h, 1).id, dom, reason);
        if (st == CK_VALID) *type = apply_term_binder(P, 0, 1, HF(&h, 1).id);
        break;
    }
    case T_PAIR: {
        if (h.n == 3) {
            /* annotated: the stored Σ type is the expected type; validate the
             * annotation as a type and the form against it (§33) */
            uint64_t l;
            st = level_of(G, C, HF(&h, 2).id, &l, reason);
            if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "pair annotation level differs"); st = CK_INVALID; }
            if (st == CK_VALID) st = check_clause(G, C, t, HF(&h, 2).id, reason);
            if (st == CK_VALID) *type = HF(&h, 2).id;
            break;
        }
        RefId A, B; uint64_t la, lb;
        st = infer_clause(G, C, HF(&h, 0).id, &A, reason);
        if (st == CK_VALID) st = infer_clause(G, C, HF(&h, 1).id, &B, reason);
        if (st == CK_VALID) st = level_of(G, C, A, &la, reason);
        if (st == CK_VALID) st = level_of(G, C, B, &lb, reason);
        if (st == CK_VALID) { TermVarId x = conv_var(t, t, A, 0, A); *type = mk_sigma_lv(la, lb, x, A, B); }
        break;
    }
    case T_FST: case T_SND: {
        RefId Tp, P;
        st = infer_clause(G, C, HF(&h, 0).id, &Tp, reason);
        if (st != CK_VALID) break;
        st = observe_head(C, Tp, T_SIGMA, &P, reason);
        if (st != CK_VALID) { if (st == CK_INVALID) *reason = "projection of a non-pair"; break; }
        Head hp; open_ref(P, &hp); RefId dom = HF(&hp, 0).id; head_free(&hp);
        *type = h.tag == T_FST ? dom : apply_term_binder(P, 0, 1, mk_fst(HF(&h, 0).id));
        break;
    }
    case T_PATH: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        uint64_t l;
        st = level_of(extend_dim(G, o.j), C, o.body, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "path family level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, HF(&h, 1).id, reindex_dim(o.body, o.j, iv_zero()), reason);
        if (st == CK_VALID) st = check_clause(G, C, HF(&h, 2).id, reindex_dim(o.body, o.j, iv_one()), reason);
        if (st == CK_VALID) *type = mk_universe(l);
        break;
    }
    case T_PLAM: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        RefId Bj;
        st = infer_clause(extend_dim(G, o.j), C, o.body, &Bj, reason);
        if (st == CK_VALID) { uint64_t lb; CheckStatus ls = level_of(extend_dim(G, o.j), C, Bj, &lb, reason); if (ls != CK_VALID) { st = ls; break; } *type = mk_path_lv(lb, o.j, Bj, reindex_dim(o.body, o.j, iv_zero()), reindex_dim(o.body, o.j, iv_one())); }
        break;
    }
    case T_PAPP: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        uint64_t l;
        st = level_of(extend_dim(G, o.j), C, o.body, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "path application family level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, HF(&h, 1).id, reindex_dim(o.body, o.j, iv_zero()), reason);
        if (st == CK_VALID) st = check_clause(G, C, HF(&h, 2).id, reindex_dim(o.body, o.j, iv_one()), reason);
        if (st == CK_VALID && !dims_declared(G, iv_dimset(HF(&h, 4).id))) { *reason = "path applied to an out-of-scope interval"; st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, HF(&h, 3).id, mk_path_lv(l, o.j, o.body, HF(&h, 1).id, HF(&h, 2).id), reason);
        if (st == CK_VALID) *type = reindex_dim(o.body, o.j, HF(&h, 4).id);
        break;
    }
    case T_GLUE_TYPE: {
        uint64_t l;
        st = glue_data_ok(G, C, HF(&h, 0).id, HF(&h, 1).id, HF(&h, 2).id, HF(&h, 3).id, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "Glue level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID) *type = mk_universe(l);
        break;
    }
    case T_GLUE_INTRO: {
        uint64_t l;
        RefId A = HF(&h, 0).id, T = HF(&h, 2).id, e = HF(&h, 3).id, tt = HF(&h, 4).id, a = HF(&h, 5).id; FaceId alpha = HF(&h, 1).id;
        st = glue_data_ok(G, C, A, alpha, T, e, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "glue level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, a, A, reason);
        FaceId Ca = fc_meet(C, alpha);
        if (st == CK_VALID && !fc_is_false(Ca)) {
            FaceId *cs; size_t nc = clauses_of(Ca, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                st = check_clause(G, cs[c], tt, T, reason);
                if (st != CK_VALID) break;
                ConvStatus cv = conv_term_clause(G, cs[c], mk_app(mk_fst(e), tt), a, A);
                if (cv == CV_UNEQUAL) { *reason = "glue: e.map(t) is not the base term on the Glue face"; st = CK_INVALID; }
                else if (cv == CV_UNRESOLVED) { *reason = "unresolved: glue map agreement"; st = CK_UNRESOLVED; }
            }
            free(cs);
        }
        if (st == CK_VALID) *type = mk_glue_type_lv(l, A, alpha, T, e);
        break;
    }
    case T_UNGLUE: {
        uint64_t l;
        RefId A = HF(&h, 0).id, T = HF(&h, 2).id, e = HF(&h, 3).id, v = HF(&h, 4).id; FaceId alpha = HF(&h, 1).id;
        st = glue_data_ok(G, C, A, alpha, T, e, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "unglue level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, v, mk_glue_type_lv(l, A, alpha, T, e), reason);
        if (st == CK_VALID) *type = A;
        break;
    }
    case T_COMP: {
        DimOpen fam = resolve_dim_binder(t, 0, 0), tube = resolve_dim_binder(t, 0, 2);
        FaceId phi = HF(&h, 1).id; RefId a0 = HF(&h, 3).id;
        ContextId Gj = extend_dim(G, fam.j);
        uint64_t l;
        st = level_of(Gj, C, fam.body, &l, reason);
        if (st == CK_VALID && !level_ok1(h.levels, l)) { *reason = level_why(h.levels, "composition family level annotation differs"); st = CK_INVALID; }
        if (st == CK_VALID && (!dims_declared(G, face_dims(phi)) || dimset_contains(face_dims(phi), fam.j))) { *reason = "composition face must be in scope and independent of the bound dimension"; st = CK_INVALID; }
        RefId A0 = reindex_dim(fam.body, fam.j, iv_zero());
        if (st == CK_VALID) st = check_clause(G, C, a0, A0, reason);
        FaceId Cp = fc_meet(C, phi);
        if (st == CK_VALID && !fc_is_false(Cp)) {
            FaceId *cs; size_t nc = clauses_of(Cp, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                st = check_clause(Gj, cs[c], tube.body, fam.body, reason);
                if (st != CK_VALID) break;
                ConvStatus cv = conv_term_clause(G, cs[c], reindex_dim(tube.body, tube.j, iv_zero()), a0, A0);
                if (cv == CV_UNEQUAL) { *reason = "composition: tube at 0 disagrees with the cap"; st = CK_INVALID; }
                else if (cv == CV_UNRESOLVED) { *reason = "unresolved: cap/tube agreement"; st = CK_UNRESOLVED; }
            }
            free(cs);
        }
        if (st == CK_VALID) *type = reindex_dim(fam.body, fam.j, iv_one());
        break;
    }
    case T_SYSTEM: {
        size_t nb = h.n / 2;
        FaceId uni = fc_false();
        for (size_t k = 0; k < nb; k++) uni = fc_join(uni, HF(&h, 2 * k).id);
        if (!fc_entails(C, uni)) { *reason = "system does not cover the face"; st = CK_INVALID; break; }
        RefId *types = calloc(nb ? nb : 1, sizeof(RefId));
        size_t sel = nb;
        for (size_t k = 0; k < nb && st == CK_VALID; k++) {
            FaceId Ck = fc_meet(C, HF(&h, 2 * k).id);
            if (!dims_declared(G, face_dims(HF(&h, 2 * k).id))) { *reason = "system guard mentions an undeclared dimension"; st = CK_INVALID; break; }
            if (fc_is_false(Ck)) continue;
            st = infer_clause(G, Ck, HF(&h, 2 * k + 1).id, &types[k], reason);
            if (st == CK_VALID && sel == nb && fc_entails(C, HF(&h, 2 * k).id)) sel = k;
        }
        /* overlaps: branches agree in their (convertible) types */
        for (size_t k = 0; k < nb && st == CK_VALID; k++)
            for (size_t l = k + 1; l < nb && st == CK_VALID; l++) {
                FaceId Ckl = fc_meet(C, fc_meet(HF(&h, 2 * k).id, HF(&h, 2 * l).id));
                if (fc_is_false(Ckl)) continue;
                FaceId *cs; size_t nc = clauses_of(Ckl, &cs);
                for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                    ConvStatus cv = conv_type_clause(G, cs[c], types[k], types[l]);
                    if (cv == CV_EQUAL) cv = conv_term_clause(G, cs[c], HF(&h, 2 * k + 1).id, HF(&h, 2 * l + 1).id, types[k]);
                    if (cv == CV_UNEQUAL) { *reason = "system branches disagree on an overlap"; st = CK_INVALID; }
                    else if (cv == CV_UNRESOLVED) { *reason = "unresolved: system overlap"; st = CK_UNRESOLVED; }
                }
                free(cs);
            }
        if (st == CK_VALID) { require(sel < nb, "a covered system has an entailed branch under a single clause"); *type = types[sel]; }
        free(types);
        break;
    }
    case T_GLOBAL: {
        SymbolId s = (SymbolId)h.payload;
        st = validate_symbol(s, reason);
        if (st != CK_VALID) break;
        ContextId Gs = origin_context(h.origin);
        st = check_map(G, C, h.map, Gs, fc_true(), reason);
        if (st == CK_VALID) *type = reindex(global_type(s), h.map);
        break;
    }
    case T_TCALL: {
        /* §43: a validated compiled record, a typed parameter map whose
         * source face entails required_face[σ], the argument at the
         * instantiated domain; the annotations must be the instantiated
         * domain and codomain; the result type is the output annotation */
        uint64_t id; int dir; MapId sigma; RefId a;
        if (!compiler_decode_call(&h, &id, &dir, &sigma, &a)) { *reason = "malformed TRANSFORM_CALL or unknown transform"; st = CK_INVALID; break; }
        const CompiledTransform *tr = transform_get(id);
        st = check_map(G, C, sigma, tr->parameters, tr->required_face, reason);
        if (st != CK_VALID) break;
        RefId dom = reindex(dir ? tr->codomain : tr->domain, sigma), cod = reindex(dir ? tr->domain : tr->codomain, sigma);
        size_t np = context_size(tr->parameters);
        ConvStatus c1 = conv_type_clause(G, C, HF(&h, np + 1).id, dom);
        ConvStatus c2 = c1 == CV_EQUAL ? conv_type_clause(G, C, HF(&h, np + 2).id, cod) : c1;
        if (c2 == CV_UNEQUAL) { *reason = "TRANSFORM_CALL annotations differ from the instantiated domain/codomain"; st = CK_INVALID; break; }
        if (c2 == CV_UNRESOLVED) { *reason = "unresolved: TRANSFORM_CALL annotation conversion"; st = CK_UNRESOLVED; break; }
        /* §59.1: the record's stored TypeAt levels are the formation levels of the annotations */
        { uint64_t ld, lc;
          st = level_of(G, C, HF(&h, np + 1).id, &ld, reason); if (st != CK_VALID) break;
          st = level_of(G, C, HF(&h, np + 2).id, &lc, reason); if (st != CK_VALID) break;
          uint64_t ed = dir ? tr->codomain_level : tr->domain_level, ec = dir ? tr->domain_level : tr->codomain_level;
          if (ld != ed || lc != ec) { *reason = "TRANSFORM_CALL annotation levels differ from the record's stored levels"; st = CK_INVALID; break; } }
        st = check_clause(G, C, a, dom, reason);
        if (st == CK_VALID) *type = HF(&h, np + 2).id;
        break;
    }
    }
    head_free(&h);
    return st;
}

/* inference of an arbitrary reference under a clause: variables directly,
 * views through the substitution lemma */
static CheckStatus infer_tview(ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static CheckStatus infer_clause(ContextId G, FaceId C, RefId t, RefId *type, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    if (ref_is_var(t)) return infer_head(G, C, t, type, reason);
    if (!fc_entails(C, ref_required(t))) { *reason = "occurrence outside its required face"; return CK_INVALID; }
    if (ref_is_tview(t)) return infer_tview(G, C, t, type, reason);
    if (origin_tag(ref_origin(t)) == T_GLOBAL) return infer_head(G, C, t, type, reason);
    OriginId O = ref_origin(t);
    ContextId Gc; FaceId req; RefId Ac;
    CheckStatus st = check_origin(O, &Gc, &req, &Ac, reason);
    if (st != CK_VALID) return st;
    st = check_map(G, C, ref_map(t), Gc, req, reason);
    if (st != CK_VALID) return st;
    *type = reindex(Ac, ref_map(t));
    return CK_VALID;
}

/* §50.1–4: the supplied scope's own validity, in its own ambient-plus-local
 * context under its own guards: every term local's declaration forms (in the
 * supplied prefix, under the projected clause conjoined with that local's
 * required face) at its required stated level; under C ∧ supplied guard the
 * result type forms at its stated level and the body has that type. The
 * metadata requirements hold whatever the guards; the typing judgments are
 * vacuous where the guards are false. */
static CheckStatus check_scope_own(ContextId G, FaceId C, ScopeId S, const char **reason) {
    /* finite structure first, independent of any face: bound occurrences
     * name existing telescopes/slots of the right sort, declarations use
     * their prefix, metadata is present; and the scope's free identities
     * are declared in the occurrence context */
    if (!scope_validate(S, reason)) return CK_INVALID;
    { size_t m; const uint64_t *fv = varset_get(scope_freevars(S), &m);
      for (size_t q = 0; q < m; q++) if (!context_declares_term(G, fv[q], NULL)) { *reason = "scope mentions a variable not declared in the occurrence context"; return CK_INVALID; }
      if (!dims_declared(G, scope_support(S))) { *reason = "scope mentions a dimension not declared in the occurrence context"; return CK_INVALID; } }
    size_t n = scope_arity(S);
    uint64_t *ids = malloc((n ? n : 1) * sizeof(uint64_t)); Val *args = malloc((n ? n : 1) * sizeof(Val));
    require(ids && args, "out of memory");
    (void)open_scope_fresh(S, 0x52, ids);
    ContextId Gx = G;
    CheckStatus st = CK_VALID;
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        LocalDecl d = scope_local(S, k);
        if (d.sort == S_DIM) { args[k].sort = VS_INTERVAL; args[k].id = iv_var((DimVarId)ids[k]); Gx = extend_dim(Gx, (DimVarId)ids[k]); continue; }
        args[k].sort = VS_REF; args[k].id = ref_var((TermVarId)ids[k]);
        RefId sty; FaceId sreq; uint64_t slv;
        scope_local_at(S, k, args, &sty, &sreq, &slv);
        if (!sty) { *reason = "scope local has no declared type"; st = CK_INVALID; break; }
        if (slv == LEVEL_NONE) { *reason = "missing universe annotation on a scope local (§59.1)"; st = CK_INVALID; break; }
        FaceId *cs = NULL; size_t nc = clauses_of(fc_meet(C, sreq), &cs);
        for (size_t c = 0; c < nc && st == CK_VALID; c++) {
            uint64_t l; st = check_is_type(Gx, cs[c], sty, &l, reason);
            if (st == CK_INVALID) { *reason = "scope local type is not a type"; break; }
            if (st == CK_VALID && l != slv) { *reason = "scope local level annotation differs from its formation level"; st = CK_INVALID; }
        }
        free(cs);
        Gx = extend_term(Gx, (TermVarId)ids[k], sty);
    }
    if (st == CK_VALID) {
        TypedPartial sup = apply_scope(S, n, args);
        if (sup.body.sort == VS_REF) {
            if (!sup.type) { *reason = "scope has no declared result type"; st = CK_INVALID; }
            else if (sup.level == LEVEL_NONE) { *reason = "missing universe annotation on a scope result (§59.1)"; st = CK_INVALID; }
            FaceId *cs = NULL; size_t nc = st == CK_VALID ? clauses_of(fc_meet(C, sup.guard), &cs) : 0;
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                uint64_t l; st = check_is_type(Gx, cs[c], sup.type, &l, reason);
                if (st == CK_INVALID) { *reason = "scope result type is not a type"; break; }
                if (st != CK_VALID) break;
                if (sup.level != l) { *reason = "scope result level annotation differs from its formation level"; st = CK_INVALID; break; }
                st = check_clause(Gx, cs[c], sup.body.id, sup.type, reason);
            }
            free(cs);
        }
    }
    free(ids); free(args);
    return st;
}

/* §51.4: a (valid) scope argument S supplied at the expected contextual
 * signature Sig (locals = expected telescope, body = expected result type,
 * level, guard). Both are opened at one common fresh telescope (the
 * signature's); the supplied local declarations must convert to the expected
 * ones, the expected guard must entail the supplied one under the source
 * clause, and the result types must convert under the expected guard. A
 * face / interval scope is total syntax: arity, sorts and guard only. */
static CheckStatus check_scope_arg(ContextId G, FaceId C, ScopeId S, ScopeId Sig, const char **reason) {
    size_t n = scope_arity(S);
    if (n != scope_arity(Sig)) { *reason = "scope argument telescope length differs from the signature"; return CK_INVALID; }
    for (size_t k = 0; k < n; k++) if (scope_local(S, k).sort != scope_local(Sig, k).sort) { *reason = "scope argument telescope sorts differ from the signature"; return CK_INVALID; }
    Val sb = scope_body(S), gb = scope_body(Sig);
    if (sb.sort != gb.sort) { *reason = "scope argument body sort differs from the signature"; return CK_INVALID; }
    CheckStatus st = check_scope_own(G, C, S, reason);
    if (st != CK_VALID) return st;
    uint64_t *ids = malloc((n ? n : 1) * sizeof(uint64_t)); Val *args = malloc((n ? n : 1) * sizeof(Val));
    require(ids && args, "out of memory");
    TypedPartial sig = open_scope_fresh(Sig, 0x51, ids);
    ContextId Gx = G;
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        LocalDecl d = scope_local(Sig, k);
        if (d.sort == S_DIM) { args[k].sort = VS_INTERVAL; args[k].id = iv_var((DimVarId)ids[k]); Gx = extend_dim(Gx, (DimVarId)ids[k]); continue; }
        args[k].sort = VS_REF; args[k].id = ref_var((TermVarId)ids[k]);
        RefId sty, ety = term_var_type((TermVarId)ids[k]); FaceId sreq; uint64_t slv;
        scope_local_at(S, k, args, &sty, &sreq, &slv);
        ConvStatus cv = conv_type_clause(Gx, C, sty, ety);
        if (cv == CV_UNEQUAL) { *reason = "scope argument local type differs from the signature"; st = CK_INVALID; break; }
        if (cv == CV_UNRESOLVED) { *reason = "unresolved: scope argument local type conversion"; st = CK_UNRESOLVED; break; }
        Gx = extend_term(Gx, (TermVarId)ids[k], ety);
    }
    if (st == CK_VALID) {
        TypedPartial sup = apply_scope(S, n, args);
        /* availability: expected guard ⊢ supplied guard under the source clause */
        if (!fc_entails(fc_meet(C, sig.guard), sup.guard)) { *reason = "scope argument is not available where the signature requires it"; st = CK_INVALID; }
        else if (sb.sort == VS_REF) {
            FaceId *cs = NULL; size_t nc = clauses_of(fc_meet(C, sig.guard), &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                ConvStatus cv = conv_type_clause(Gx, cs[c], sup.type, sig.body.id);
                if (cv == CV_UNEQUAL) { *reason = "scope argument result type differs from the signature"; st = CK_INVALID; break; }
                if (cv == CV_UNRESOLVED) { *reason = "unresolved: scope argument result type conversion"; st = CK_UNRESOLVED; break; }
            }
            free(cs);
        }
    }
    free(ids); free(args);
    return st;
}

/* the template boundary of an instance (§51.4, §59.1): its declared required
 * face must be entailed; every retained reference parameter image is checked
 * against the signature's instantiated declared type and every retained scope
 * against its contextual signature. Memoized per (view, declarations,
 * projected clause). */
static CheckStatus tview_boundary(ContextId G, FaceId C, RefId t, const char **reason) {
    if (!fc_entails(C, ref_required(t))) { *reason = "template instance used outside its declared required face"; return CK_INVALID; }
    size_t n; const uint64_t *ds = dimset_get(ref_support(t), &n);
    uint64_t key[3] = { t, under(G, fc_true()), fc_project(C, ds, n) }, v; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_TBOUND, key, 3); pthread_mutex_unlock(&K.mu);
    Acq a = claim_acquire(cl, &v, &why, NULL);
    if (a == ACQ_DONE) { if (v == 1) return CK_VALID; *reason = why; return ck_of(v); }
    if (a == ACQ_CYCLE) { *reason = "unresolved: template boundary validation depends on itself"; return CK_UNRESOLVED; }
    CheckStatus st = CK_VALID;
    TEnvId E = tenv_of(t);
    /* finite structure of every retained image before any signature recipe
     * can apply a supplied scope (§50.1–2, review R3) */
    for (size_t q = 0, ne = tenv_size(E); q < ne && st == CK_VALID; q++) {
        uint64_t slot; TVal val; tenv_entry(E, q, &slot, &val);
        if (val.sort == PS_SCOPE && !scope_validate((ScopeId)val.id, reason)) st = CK_INVALID;
        else if (val.sort == PS_REF && !ref_validate(val.id, reason)) st = CK_INVALID;
    }
    if (st != CK_VALID) { claim_release(cl, ck_code(st), *reason, NULL); return st; }
    ParamSig sig[16]; size_t ns = tnode_signature(t, sig, 16);
    for (size_t k = 0; k < ns && st == CK_VALID; k++) {
        size_t ne = tenv_size(E); uint64_t image = 0; bool have = false;
        for (size_t q = 0; q < ne; q++) { uint64_t slot; TVal val; tenv_entry(E, q, &slot, &val); if (slot == sig[k].slot) { image = val.id; have = true; } }
        require(have, "template boundary: a retained slot has no image");
        if (sig[k].sort == PS_REF) {
            if (!sig[k].type) continue;                     /* an undeclared parameter (none in the library) */
            /* a partial parameter or local is checked on its declared guarded use */
            FaceId *cs = NULL; size_t nc = clauses_of(fc_meet(C, sig[k].guard), &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(G, cs[c], image, sig[k].type, reason);
            free(cs);
            if (st == CK_INVALID) { char buf[256]; snprintf(buf, sizeof buf, "template parameter image is not of its declared type (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(t))), sig[k].slot, *reason); *reason = diag_intern(buf); }
        } else if (sig[k].sort == PS_SCOPE) {
            if (!sig[k].sig) continue;
            st = check_scope_arg(G, C, (ScopeId)image, sig[k].sig, reason);
            if (st == CK_INVALID) { char buf[256]; snprintf(buf, sizeof buf, "template scope argument does not meet its signature (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(t))), sig[k].slot, *reason); *reason = diag_intern(buf); }
        }
    }
    claim_release(cl, ck_code(st), *reason, NULL);
    return st;
}

/* A template instance: boundary, then the opened head by the existing
 * constructor rules; when the instance is a program's root its inferred type
 * must convert to the declared result type instantiated by the environment. */
static CheckStatus infer_tview(ContextId G, FaceId C, RefId t, RefId *type, const char **reason) {
    size_t n; const uint64_t *ds = dimset_get(ref_support(t), &n);
    uint64_t key[3] = { t, under(G, fc_true()), fc_project(C, ds, n) }, v, aux[3] = { 0, 0, 0 }; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_TVIEW, key, 3); pthread_mutex_unlock(&K.mu);
    Acq a = claim_acquire(cl, &v, &why, aux);
    if (a == ACQ_DONE) { if (v == 1) { *type = aux[0]; return CK_VALID; } *reason = why; return ck_of(v); }
    if (a == ACQ_CYCLE) { *reason = "unresolved: template instance validation depends on itself"; return CK_UNRESOLVED; }
    CheckStatus st = tview_boundary(G, C, t, reason);
    RefId ty = 0;
    if (st == CK_VALID) st = infer_head(G, C, t, &ty, reason);
    if (st == CK_VALID) {
        RefId declared; uint64_t dl;
        if (tnode_result(t, &declared, &dl)) {
            ConvStatus cv = conv_type_clause(G, C, ty, declared);
            if (cv == CV_UNEQUAL) { char buf[256]; snprintf(buf, sizeof buf, "library instance type differs from its declared result type (%s)", tdef_name(tnode_def(ref_tnode(t)))); *reason = diag_intern(buf); st = CK_INVALID; }
            else if (cv == CV_UNRESOLVED) { *reason = "unresolved: declared result type conversion"; st = CK_UNRESOLVED; }
        }
    }
    aux[0] = ty;
    claim_release(cl, ck_code(st), *reason, aux);
    if (st == CK_VALID) *type = ty;
    return st;
}

static CheckStatus scope_ok(ContextId G, FaceId chi, RefId t, const char **reason) {
    if (!dims_declared(G, face_dims(chi))) { *reason = "face mentions an undeclared dimension"; return CK_INVALID; }
    if (!ref_validate(t, reason)) return CK_INVALID;      /* finite structure, independent of the face (§50.1–2) */
    size_t n; const uint64_t *xs = varset_get(ref_freevars(t), &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_term(G, xs[k], NULL)) { *reason = "unbound variable"; return CK_INVALID; }
    if (!dims_declared(G, ref_support(t))) { *reason = "unbound dimension"; return CK_INVALID; }
    return CK_VALID;
}

Inference infer(ContextId G, FaceId chi, RefId t) {
  for (;;) {
    Inference out = { CK_VALID, 0, NULL };
    ENTER();
    out.st = scope_ok(G, chi, t, &out.reason);
    if (out.st != CK_VALID) { LEAVE(); (void)top_settled(); return out; }
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    RefId *types = malloc((nc ? nc : 1) * sizeof(RefId));
    for (size_t c = 0; c < nc && out.st == CK_VALID; c++) out.st = infer_clause(G, cs[c], t, &types[c], &out.reason);
    if (out.st == CK_VALID) {
        if (nc == 0) out.type = mk_system(0, NULL, NULL);
        else { bool same = true; for (size_t c = 1; c < nc; c++) if (types[c] != types[0]) same = false; out.type = same ? types[0] : mk_system(nc, cs, types); }
    }
    free(types); free(cs);
    LEAVE();
    if (top_settled()) return out;
  }
}


/* ------------------------------------------------------------------ */
/* checking against an expected type                                    */

static CheckStatus check_clause(ContextId G, FaceId C, RefId t, RefId A, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    Tag tag = 0;
    /* §2/§33: an occurrence is used only under a clause entailing its
     * required face — on every path, the checking forms included */
    if (!ref_is_var(t) && !fc_entails(C, ref_required(t))) { *reason = "occurrence outside its required face"; return CK_INVALID; }
    if (!ref_is_var(t)) tag = ref_tag(t);
    if (tag == T_LAM || tag == T_PAIR || tag == T_PLAM || tag == T_SYSTEM) {
        if (ref_is_tview(t)) { CheckStatus bs = tview_boundary(G, C, t, reason); if (bs != CK_VALID) return bs; }   /* the checking form does not bypass the template boundary */
        Head h; open_ref(t, &h);
        CheckStatus st = CK_VALID;
        RefId P;
        switch (tag) {
        case T_LAM: {
            st = observe_head(C, A, T_PI, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "lambda checked against a non-product type"; break; }
            Head hp; open_ref(P, &hp); RefId D = HF(&hp, 0).id; head_free(&hp);
            ConvStatus cv = conv_type_clause(G, C, HF(&h, 0).id, D);
            if (cv == CV_UNEQUAL) { *reason = "lambda domain differs from the expected domain"; st = CK_INVALID; break; }
            if (cv == CV_UNRESOLVED) { *reason = "unresolved: lambda domain conversion"; st = CK_UNRESOLVED; break; }
            { uint64_t l; st = level_of(G, C, HF(&h, 0).id, &l, reason); if (st != CK_VALID) break;   /* the annotation is a type at its stored level */
              if (!level_ok1(h.levels, l)) { *reason = level_why(h.levels, "lambda domain level annotation differs"); st = CK_INVALID; break; } }
            TermVarId x = conv_var(t, P, P, 0, D);
            st = check_clause(extend_term(G, x, D), C, apply_term_binder(t, 0, 1, ref_var(x)), apply_term_binder(P, 0, 1, ref_var(x)), reason);
            break;
        }
        case T_PAIR: {
            if (h.n == 3) {
                /* annotated pair (§59.2): the stored Σ forms at its stored
                 * level, is convertible with the expected type, and governs
                 * the component checks */
                uint64_t l; st = level_of(G, C, HF(&h, 2).id, &l, reason); if (st != CK_VALID) break;
                if (!level_ok1(h.levels, l)) { *reason = level_why(h.levels, "pair annotation level differs"); st = CK_INVALID; break; }
                ConvStatus cv = conv_type_clause(G, C, HF(&h, 2).id, A);
                if (cv == CV_UNEQUAL) { *reason = "pair annotation differs from the expected type"; st = CK_INVALID; break; }
                if (cv == CV_UNRESOLVED) { *reason = "unresolved: pair annotation conversion"; st = CK_UNRESOLVED; break; }
                A = HF(&h, 2).id;
            }
            st = observe_head(C, A, T_SIGMA, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "pair checked against a non-sum type"; break; }
            Head hp; open_ref(P, &hp); RefId D = HF(&hp, 0).id; head_free(&hp);
            st = check_clause(G, C, HF(&h, 0).id, D, reason);
            if (st == CK_VALID) st = check_clause(G, C, HF(&h, 1).id, apply_term_binder(P, 0, 1, HF(&h, 0).id), reason);
            break;
        }
        case T_PLAM: {
            st = observe_head(C, A, T_PATH, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "path lambda checked against a non-path type"; break; }
            Head hp; open_ref(P, &hp); RefId l = HF(&hp, 1).id, r = HF(&hp, 2).id; head_free(&hp);
            DimVarId j = conv_dim(t, P, 0);
            RefId body = apply_dim_binder(t, 0, 0, iv_var(j)), Bj = apply_dim_binder(P, 0, 0, iv_var(j));
            st = check_clause(extend_dim(G, j), C, body, Bj, reason);
            if (st != CK_VALID) break;
            ConvStatus c0 = conv_term_clause(G, C, apply_dim_binder(t, 0, 0, iv_zero()), l, apply_dim_binder(P, 0, 0, iv_zero()));
            ConvStatus c1 = c0 == CV_EQUAL ? conv_term_clause(G, C, apply_dim_binder(t, 0, 0, iv_one()), r, apply_dim_binder(P, 0, 0, iv_one())) : c0;
            if (c1 == CV_UNEQUAL) { *reason = "path lambda endpoints differ from the path type's endpoints"; st = CK_INVALID; }
            else if (c1 == CV_UNRESOLVED) { *reason = "unresolved: path endpoint conversion"; st = CK_UNRESOLVED; }
            break;
        }
        case T_SYSTEM: {
            size_t nb = h.n / 2;
            FaceId uni = fc_false();
            for (size_t k = 0; k < nb; k++) uni = fc_join(uni, HF(&h, 2 * k).id);
            if (!fc_entails(C, uni)) { *reason = "system does not cover the face"; st = CK_INVALID; break; }
            for (size_t k = 0; k < nb && st == CK_VALID; k++) {
                FaceId Ck = fc_meet(C, HF(&h, 2 * k).id);
                if (!dims_declared(G, face_dims(HF(&h, 2 * k).id))) { *reason = "system guard mentions an undeclared dimension"; st = CK_INVALID; break; }
                if (fc_is_false(Ck)) continue;
                FaceId *cs; size_t nc = clauses_of(Ck, &cs);
                for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(G, cs[c], HF(&h, 2 * k + 1).id, A, reason);
                free(cs);
            }
            for (size_t k = 0; k < nb && st == CK_VALID; k++)
                for (size_t l = k + 1; l < nb && st == CK_VALID; l++) {
                    FaceId Ckl = fc_meet(C, fc_meet(HF(&h, 2 * k).id, HF(&h, 2 * l).id));
                    if (fc_is_false(Ckl)) continue;
                    FaceId *cs; size_t nc = clauses_of(Ckl, &cs);
                    for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                        ConvStatus cv = conv_term_clause(G, cs[c], HF(&h, 2 * k + 1).id, HF(&h, 2 * l + 1).id, A);
                        if (cv == CV_UNEQUAL) { *reason = "system branches disagree on an overlap"; st = CK_INVALID; }
                        else if (cv == CV_UNRESOLVED) { *reason = "unresolved: system overlap"; st = CK_UNRESOLVED; }
                    }
                    free(cs);
                }
            break;
        }
        default: break;
        }
        head_free(&h);
        return st;
    }
    RefId T;
    CheckStatus st = infer_clause(G, C, t, &T, reason);
    if (st != CK_VALID) return st;
    ConvStatus cv = conv_type_clause(G, C, T, A);
    if (cv == CV_EQUAL) return CK_VALID;
    if (cv == CV_UNEQUAL) {
        if (getenv("CK_DEBUG")) { fprintf(stderr, "UNEQUAL under "); fc_print(C, stderr); fprintf(stderr, "\n  term: "); print_ref_depth(t, stderr, 2); fprintf(stderr, "\n  inferred: "); print_ref_depth(T, stderr, 3); fprintf(stderr, "\n  expected: "); print_ref_depth(A, stderr, 3); fprintf(stderr, "\n"); }
        *reason = "inferred type is not convertible to the expected type"; return CK_INVALID;
    }
    *reason = "unresolved: type conversion";
    return CK_UNRESOLVED;
}

CheckStatus check(ContextId G, FaceId chi, RefId t, RefId A, const char **reason) {
  for (;;) {
    ENTER();
    CheckStatus st = scope_ok(G, chi, t, reason);
    if (st == CK_VALID) st = scope_ok(G, chi, A, reason);
    if (st != CK_VALID) { LEAVE(); (void)top_settled(); return st; }
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(G, cs[c], t, A, reason);
    free(cs);
    LEAVE();
    if (top_settled()) return st;
  }
}

/* ------------------------------------------------------------------ */
/* conversion                                                           */

/* conversion requests are claims keyed by (mode, context without assumption,
 * face projected to the support of the request, a, b, T) */
static size_t conv_claim(uint64_t mode, ContextId G, FaceId C, RefId a, RefId b, RefId T) {
    DimSetId S = dimset_union(ref_support(a), ref_support(b));
    if (T) S = dimset_union(S, ref_support(T));
    size_t n; const uint64_t *ds = dimset_get(S, &n);
    uint64_t key[6] = { mode, under(G, fc_true()), fc_project(C, ds, n), a, b, T };
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_CONV, key, 6); pthread_mutex_unlock(&K.mu);
    return cl;
}

/* the common level of a Glue's base and fibre: the annotation, else inferred */
static uint64_t glue_level(ContextId G, FaceId C, uint64_t levels, RefId A) {
    uint64_t l = levels_first(levels);
    if (l != LEVEL_NONE) return l;
    const char *why; if (level_of(G, C, A, &l, &why) != CK_VALID) return LEVEL_NONE;
    return l;
}

static ConvStatus and3(ConvStatus a, ConvStatus b) {
    if (a == CV_UNEQUAL || b == CV_UNEQUAL) return CV_UNEQUAL;
    if (a == CV_UNRESOLVED || b == CV_UNRESOLVED) return CV_UNRESOLVED;
    return CV_EQUAL;
}

static ConvStatus spine(ContextId G, FaceId C, RefId n1, RefId n2);

static ConvStatus observe_both(FaceId C, RefId a, RefId b, EvalResult **ra, EvalResult **rb) {
    const char *reason;
    if (observe(C, a, ra, &reason) != CK_VALID) return CV_UNRESOLVED;
    if (observe(C, b, rb, &reason) != CK_VALID) return CV_UNRESOLVED;
    return CV_EQUAL;
}

static ConvStatus conv_type_clause(ContextId G, FaceId C, RefId A, RefId B) {
    if (A == B) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    size_t cl = conv_claim(1, G, C, A, B, 0); uint64_t v;
    Acq acq = claim_acquire(cl, &v, NULL, NULL);
    if (acq == ACQ_DONE) return cv_of(v);
    if (acq == ACQ_CYCLE) return CV_UNRESOLVED;  /* the comparison depends on itself: no coinductive assumption */
    ConvStatus out = CV_UNRESOLVED;
    EvalResult *ra, *rb;
    if (observe_both(C, A, B, &ra, &rb) != CV_EQUAL) goto done;
    if (ra->ref == rb->ref) { out = CV_EQUAL; goto done; }
    if (ra->cls == R_SYSTEM || rb->cls == R_SYSTEM) { out = CV_UNRESOLVED; goto done; }
    if (ra->cls != rb->cls) { out = CV_UNEQUAL; goto done; }
    if (ra->cls == R_NEUTRAL) { out = spine(G, C, ra->ref, rb->ref); goto done; }
    {
        Head ha, hb; open_ref(ra->ref, &ha); open_ref(rb->ref, &hb);
        if (ha.tag != hb.tag) out = CV_UNEQUAL;
        else switch (ha.tag) {
        case T_UNIVERSE: out = ha.payload == hb.payload ? CV_EQUAL : CV_UNEQUAL; break;
        case T_PI: case T_SIGMA: {
            out = conv_type_clause(G, C, HF(&ha, 0).id, HF(&hb, 0).id);
            if (out != CV_EQUAL) break;
            TermVarId x = conv_var(ra->ref, rb->ref, ra->ref, 0, HF(&ha, 0).id);
            out = conv_type_clause(extend_term(G, x, HF(&ha, 0).id), C, apply_term_binder(ra->ref, 0, 1, ref_var(x)), apply_term_binder(rb->ref, 0, 1, ref_var(x)));
            break;
        }
        case T_PATH: {
            DimVarId j = conv_dim(ra->ref, rb->ref, 0);
            RefId Ba = apply_dim_binder(ra->ref, 0, 0, iv_var(j)), Bb = apply_dim_binder(rb->ref, 0, 0, iv_var(j));
            out = conv_type_clause(extend_dim(G, j), C, Ba, Bb);
            if (out == CV_EQUAL) out = conv_term_clause(G, C, HF(&ha, 1).id, HF(&hb, 1).id, reindex_dim(Ba, j, iv_zero()));
            if (out == CV_EQUAL) out = conv_term_clause(G, C, HF(&ha, 2).id, HF(&hb, 2).id, reindex_dim(Ba, j, iv_one()));
            break;
        }
        case T_GLUE_TYPE: {
            if (!fc_equal_under(C, HF(&ha, 1).id, HF(&hb, 1).id)) { out = CV_UNEQUAL; break; }
            out = conv_type_clause(G, C, HF(&ha, 0).id, HF(&hb, 0).id);
            FaceId Ca = fc_meet(C, HF(&ha, 1).id);
            if (out == CV_EQUAL && !fc_is_false(Ca)) {
                FaceId *cs; size_t nc = clauses_of(Ca, &cs);
                for (size_t c = 0; c < nc && out == CV_EQUAL; c++) {
                    out = conv_type_clause(G, cs[c], HF(&ha, 2).id, HF(&hb, 2).id);
                    if (out == CV_EQUAL) { uint64_t gl = glue_level(G, cs[c], ha.levels, HF(&ha, 0).id); if (gl == LEVEL_NONE) { out = CV_UNRESOLVED; break; } out = conv_term_clause(G, cs[c], HF(&ha, 3).id, HF(&hb, 3).id, mk_equiv(gl, gl, HF(&ha, 2).id, HF(&ha, 0).id)); }
                }
                free(cs);
            }
            break;
        }
        default: out = CV_UNEQUAL; break;       /* an introduction that is not a type former */
        }
        head_free(&ha); head_free(&hb);
    }
done:
    claim_release(cl, cv_code(out), NULL, NULL);
    return out;
}

static ConvStatus conv_term_clause(ContextId G, FaceId C, RefId t, RefId u, RefId A) {
    if (t == u) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    size_t cl = conv_claim(2, G, C, t, u, A); uint64_t v;
    Acq acq = claim_acquire(cl, &v, NULL, NULL);
    if (acq == ACQ_DONE) return cv_of(v);
    if (acq == ACQ_CYCLE) return CV_UNRESOLVED;
    ConvStatus out = CV_UNRESOLVED;
    EvalResult *rA; const char *reason;
    if (observe(C, A, &rA, &reason) != CK_VALID) goto done;
    if (rA->cls == R_INTRODUCTION) {
        Head h; open_ref(rA->ref, &h);
        switch (h.tag) {
        case T_PI: {
            TermVarId x = conv_var(t, u, rA->ref, 0, HF(&h, 0).id);
            RefId Bx = apply_term_binder(rA->ref, 0, 1, ref_var(x));
            out = conv_term_clause(extend_term(G, x, HF(&h, 0).id), C, mk_app(t, ref_var(x)), mk_app(u, ref_var(x)), Bx);
            break;
        }
        case T_SIGMA: {
            out = conv_term_clause(G, C, mk_fst(t), mk_fst(u), HF(&h, 0).id);
            if (out == CV_EQUAL) out = conv_term_clause(G, C, mk_snd(t), mk_snd(u), apply_term_binder(rA->ref, 0, 1, mk_fst(t)));
            break;
        }
        case T_PATH: {
            DimVarId j = conv_dim(t, u, 0);
            DimOpen o = resolve_dim_binder(rA->ref, 0, 0);
            RefId Bj = reindex_dim(o.body, o.j, iv_var(j));
            { uint64_t n = levels_first(h.levels);
              out = conv_term_clause(extend_dim(G, j), C, mk_papp_lv(n, o.j, o.body, HF(&h, 1).id, HF(&h, 2).id, t, iv_var(j)), mk_papp_lv(n, o.j, o.body, HF(&h, 1).id, HF(&h, 2).id, u, iv_var(j)), Bj); }
            break;
        }
        case T_GLUE_TYPE: {
            /* non-collapsed Glue (C does not entail alpha): Glue eta */
            RefId Ab = HF(&h, 0).id, T = HF(&h, 2).id, e = HF(&h, 3).id; FaceId alpha = HF(&h, 1).id;
            { uint64_t n = levels_first(h.levels);
              out = conv_term_clause(G, C, mk_unglue_lv(n, Ab, alpha, T, e, t), mk_unglue_lv(n, Ab, alpha, T, e, u), Ab); }
            FaceId Ca = fc_meet(C, alpha);
            if (out == CV_EQUAL && !fc_is_false(Ca)) {
                FaceId *cs; size_t nc = clauses_of(Ca, &cs);
                for (size_t c = 0; c < nc && out == CV_EQUAL; c++) out = conv_term_clause(G, cs[c], t, u, T);
                free(cs);
            }
            break;
        }
        case T_UNIVERSE: out = conv_type_clause(G, C, t, u); break;
        default: out = CV_UNEQUAL; break;
        }
        head_free(&h);
    } else if (rA->cls == R_NEUTRAL) {
        /* neutral expected type: observe the terms and compare their neutral structures */
        EvalResult *rt, *ru;
        if (observe_both(C, t, u, &rt, &ru) != CV_EQUAL) goto done;
        if (rt->ref == ru->ref) out = CV_EQUAL;
        else if (rt->cls == R_NEUTRAL && ru->cls == R_NEUTRAL) out = spine(G, C, rt->ref, ru->ref);
        else if (rt->cls == R_SYSTEM || ru->cls == R_SYSTEM) out = CV_UNRESOLVED;
        else out = CV_UNEQUAL;
    } else out = CV_UNRESOLVED;                 /* a system type under a single clause is not a covered type */
done:
    claim_release(cl, cv_code(out), NULL, NULL);
    return out;
}

/* structural comparison of neutral spines; n1, n2 are neutral result references */
static ConvStatus spine(ContextId G, FaceId C, RefId n1, RefId n2) {
    if (n1 == n2) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    if (ref_is_var(n1) || ref_is_var(n2)) return (ref_is_var(n1) && ref_is_var(n2) && ref_var_id(n1) == ref_var_id(n2)) ? CV_EQUAL : CV_UNEQUAL;
    Head a, b; open_ref(n1, &a); open_ref(n2, &b);
    ConvStatus out = CV_UNEQUAL;
    if (a.tag != b.tag) goto done;
    switch (a.tag) {
    case T_APP: {
        EvalResult *fa, *fb;
        if (observe_both(C, HF(&a, 0).id, HF(&b, 0).id, &fa, &fb) != CV_EQUAL) { out = CV_UNRESOLVED; break; }
        if (fa->cls != R_NEUTRAL || fb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, fa->ref, fb->ref);
        if (out != CV_EQUAL) break;
        RefId Tf, P; const char *reason;
        if (infer_clause(G, C, HF(&a, 0).id, &Tf, &reason) != CK_VALID || observe_head(C, Tf, T_PI, &P, &reason) != CK_VALID) { out = CV_UNRESOLVED; break; }
        Head hp; open_ref(P, &hp); RefId dom = HF(&hp, 0).id; head_free(&hp);
        out = conv_term_clause(G, C, HF(&a, 1).id, HF(&b, 1).id, dom);
        break;
    }
    case T_FST: case T_SND: {
        EvalResult *pa, *pb;
        if (observe_both(C, HF(&a, 0).id, HF(&b, 0).id, &pa, &pb) != CV_EQUAL || pa->cls != R_NEUTRAL || pb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, pa->ref, pb->ref);
        break;
    }
    case T_PAPP: {
        if (!iv_equal_under(C, HF(&a, 4).id, HF(&b, 4).id)) { out = CV_UNEQUAL; break; }
        EvalResult *pa, *pb;
        if (observe_both(C, HF(&a, 3).id, HF(&b, 3).id, &pa, &pb) != CV_EQUAL || pa->cls != R_NEUTRAL || pb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, pa->ref, pb->ref);
        break;
    }
    case T_UNGLUE: {
        if (!fc_equal_under(C, HF(&a, 1).id, HF(&b, 1).id)) { out = CV_UNEQUAL; break; }
        out = conv_type_clause(G, C, HF(&a, 0).id, HF(&b, 0).id);
        FaceId Ca = fc_meet(C, HF(&a, 1).id);
        if (out == CV_EQUAL && !fc_is_false(Ca)) {
            FaceId *cs; size_t nc = clauses_of(Ca, &cs);
            for (size_t c = 0; c < nc && out == CV_EQUAL; c++) {
                out = conv_type_clause(G, cs[c], HF(&a, 2).id, HF(&b, 2).id);
                if (out == CV_EQUAL) { uint64_t gl = glue_level(G, cs[c], a.levels, HF(&a, 0).id); if (gl == LEVEL_NONE) { out = CV_UNRESOLVED; break; } out = conv_term_clause(G, cs[c], HF(&a, 3).id, HF(&b, 3).id, mk_equiv(gl, gl, HF(&a, 2).id, HF(&a, 0).id)); }
            }
            free(cs);
        }
        if (out != CV_EQUAL) break;
        EvalResult *va, *vb;
        if (observe_both(C, HF(&a, 4).id, HF(&b, 4).id, &va, &vb) != CV_EQUAL || va->cls != R_NEUTRAL || vb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, va->ref, vb->ref);
        break;
    }
    case T_COMP: {
        if (!fc_equal_under(C, HF(&a, 1).id, HF(&b, 1).id)) { out = CV_UNEQUAL; break; }
        DimVarId j = conv_dim(n1, n2, 0);
        RefId A1 = apply_dim_binder(n1, 0, 0, iv_var(j)), A2 = apply_dim_binder(n2, 0, 0, iv_var(j));
        ContextId Gj = extend_dim(G, j);
        out = conv_type_clause(Gj, C, A1, A2);
        if (out == CV_EQUAL) out = conv_term_clause(G, C, HF(&a, 3).id, HF(&b, 3).id, reindex_dim(A1, j, iv_zero()));
        FaceId Cp = fc_meet(C, HF(&a, 1).id);
        if (out == CV_EQUAL && !fc_is_false(Cp)) {
            RefId u1 = apply_dim_binder(n1, 0, 2, iv_var(j)), u2 = apply_dim_binder(n2, 0, 2, iv_var(j));
            FaceId *cs; size_t nc = clauses_of(Cp, &cs);
            for (size_t c = 0; c < nc && out == CV_EQUAL; c++) out = conv_term_clause(Gj, cs[c], u1, u2, A1);
            free(cs);
        }
        break;
    }
    case T_GLOBAL: {
        if (a.payload != b.payload) { out = CV_UNEQUAL; break; }
        ContextId Gs = origin_context(a.origin);
        out = CV_EQUAL;
        size_t n = context_size(Gs);
        for (size_t k = 0; k < n && out == CV_EQUAL; k++) {
            CtxDecl d = context_decl(Gs, k);
            if (d.sort == S_DIM) { if (!iv_equal_under(C, map_dim_image(a.map, d.id), map_dim_image(b.map, d.id))) out = CV_UNEQUAL; }
            else out = conv_term_clause(G, C, map_term_image(a.map, d.id), map_term_image(b.map, d.id), reindex(d.type, a.map));
        }
        break;
    }
    default: out = CV_UNEQUAL; break;
    }
done:
    head_free(&a); head_free(&b);
    return out;
}

ConvStatus convert_type(ContextId G, FaceId chi, RefId A, RefId B) {
    const char *why;
    if (scope_ok(G, chi, A, &why) != CK_VALID || scope_ok(G, chi, B, &why) != CK_VALID) return CV_UNRESOLVED;
    for (;;) {
        ENTER();
        FaceId *cs; size_t nc = clauses_of(chi, &cs);
        ConvStatus out = CV_EQUAL;
        for (size_t c = 0; c < nc; c++) { ConvStatus r = conv_type_clause(G, cs[c], A, B); out = and3(out, r); if (out == CV_UNEQUAL) break; }
        free(cs);
        LEAVE();
        if (top_settled()) return out;
    }
}
ConvStatus convert_term(ContextId G, FaceId chi, RefId t, RefId u, RefId A) {
    const char *why;
    if (scope_ok(G, chi, t, &why) != CK_VALID || scope_ok(G, chi, u, &why) != CK_VALID || scope_ok(G, chi, A, &why) != CK_VALID) return CV_UNRESOLVED;
    for (;;) {
        ENTER();
        FaceId *cs; size_t nc = clauses_of(chi, &cs);
        ConvStatus out = CV_EQUAL;
        for (size_t c = 0; c < nc; c++) { ConvStatus r = conv_term_clause(G, cs[c], t, u, A); out = and3(out, r); if (out == CV_UNEQUAL) break; }
        free(cs);
        LEAVE();
        if (top_settled()) return out;
    }
}

/* A declared symbol is validated once: its declared type is a type over its
 * parameters, and its registered body (if any) checks against that type.
 * While a symbol's own body is being validated, its recursive occurrences
 * use the declared type: the signature's declaration is the assumption the
 * body is checked under (this does not prove termination). Every verdict
 * reached under that assumption is provisional on the symbol and is
 * committed by claim_release only when the body is accepted. */
static CheckStatus validate_symbol(SymbolId s, const char **reason) {
  for (;;) {
    uint64_t key[1] = { s }, v; const char *why = NULL;
    pthread_mutex_lock(&K.mu); size_t cl = claim_index_locked(CL_SYMBOL, key, 1); pthread_mutex_unlock(&K.mu);
    ENTER();
    Acq a = claim_acquire(cl, &v, &why, NULL);
    if (a == ACQ_DONE) { LEAVE(); if (v != 1) *reason = why; if (top_settled()) return ck_of(v); continue; }
    if (a == ACQ_CYCLE) { assume_symbol(cl); LEAVE(); require(tl_depth > 0 || tl_pending.n == 0, "declaration assumed at the top level"); return CK_VALID; }   /* recursive occurrence: typed by the declaration */
    RefId type = global_type(s);
    CheckStatus st = CK_VALID;
    if (!type) { *reason = "symbol without a declared type"; st = CK_INVALID; }
    OriginId o = ref_origin(global_ref(s));
    ContextId Gs = origin_context(o);
    if (st == CK_VALID) st = check_context(Gs, reason);
    if (st == CK_VALID) { uint64_t l; st = level_of(Gs, fc_true(), type, &l, reason); }
    RefId body = global_body(s);
    if (st == CK_VALID && body) st = check(Gs, fc_true(), body, type, reason);
    claim_release(cl, ck_code(st), *reason, NULL);
    LEAVE();
    if (top_settled()) return st;
  }
}

CheckStatus check_admission(const char **reason) {
    env_freeze();                        /* the freeze boundary precedes candidate admission */
    pthread_mutex_lock(&K.mu);
    for (;;) {
        uint64_t v = global_env_version();
        /* a settled verdict for this environment is reused; an UNRESOLVED
         * verdict only within the attempt that produced it */
        if (!ADM.running && ADM.have && ADM.version == v && (ADM.status != CK_UNRESOLVED || ADM.attempt == K.attempt)) {
            CheckStatus st = ADM.status; *reason = ADM.reason; pthread_mutex_unlock(&K.mu); return st;
        }
        if (!ADM.running) { ADM.running = true; ADM.version = v; ADM.attempt = K.attempt; pthread_mutex_unlock(&K.mu); break; }
        pthread_cond_wait(&K.cv, &K.mu);
    }
    const char *why = "";
    CheckStatus st = check_signature(&why);
    pthread_mutex_lock(&K.mu);
    ADM.running = false; ADM.have = true; ADM.status = st; ADM.reason = why;
    pthread_cond_broadcast(&K.cv);
    pthread_mutex_unlock(&K.mu);
    *reason = why;
    return st;
}

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
    eval_reset();
    env_unfreeze();
}

EvalResult *observe_checked(ContextId G, RefId t, WhnfStatus *status, const char **reason) {
    /* public checked execution enters the admission gate first */
    CheckStatus st = check_admission(reason);
    if (st == CK_INVALID) { if (status) *status = W_INVALID; return NULL; }
    if (st == CK_UNRESOLVED) { if (status) *status = W_STUCK; return NULL; }
    st = check_context(G, reason);
    if (st == CK_VALID) { Inference I = infer(G, context_assumption(G), t); st = I.st; if (st != CK_VALID) *reason = I.reason; }
    if (st == CK_INVALID) { if (status) *status = W_INVALID; return NULL; }
    if (st == CK_UNRESOLVED) { if (status) *status = W_STUCK; return NULL; }
    return whnf(t, context_assumption(G), status);
}

/* formation: A is a type under chi; its universe level (equal under every
 * clause) is returned. Successful inference of some type for A is not enough
 * (§59.5): the inferred type is observed and must be a universe. */
CheckStatus check_is_type(ContextId G, FaceId chi, RefId A, uint64_t *level, const char **reason) {
    for (;;) {
        ENTER();
        CheckStatus st = scope_ok(G, chi, A, reason);
        uint64_t lvl = 0; bool have = false;
        if (st == CK_VALID) {
            FaceId *cs; size_t nc = clauses_of(chi, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                uint64_t l;
                st = level_of(G, cs[c], A, &l, reason);
                if (st == CK_VALID) { if (have && l != lvl) { *reason = "type lives in different universes under different clauses"; st = CK_INVALID; } lvl = l; have = true; }
            }
            free(cs);
        }
        LEAVE();
        if (top_settled()) { if (st == CK_VALID && level) *level = lvl; return st; }
    }
}

CheckStatus check_signature(const char **reason) {
    size_t n = global_count();
    for (SymbolId s = 1; s <= n; s++) { CheckStatus st = validate_symbol(s, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}

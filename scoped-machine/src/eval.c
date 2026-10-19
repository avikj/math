#include "eval.h"
#include "lib.h"
#include "pool.h"
#include "pins.h"
#include "judge.h"
#include "chain.h"
#include "effect.h"
#include "proof.h"
#include <sched.h>

/* ---------------- continuations, joins, results ----------------
 *
 * Ownership (§19–§20): a continuation is single-consumer and is released when
 * it has been resumed (a frame that set `keep` is reused for its next child);
 * a join box is freed when it publishes; a published result is owned by the
 * machine's result list for the life of the machine. Nothing is reclaimed
 * while a live root, entry, descriptor or continuation can still reach it. */

/* a join: a frame awaiting n independent demands; each box receives one
 * value, and the last arrival (or the frame, if every box filled while it was
 * still issuing) resumes the frame */
/* a heap resource owned by the frame whose step created it: freed by its
 * family code, or with the frame when the frame is released, or at teardown
 * when the frame is a stuck waiter */
typedef struct Owned { struct Owned *next, *prev; Cont *owner; int is_join; } Owned;
struct Join {
    Owned own;                /* first: a Join is its ownership record */
    Cont *frame;
    size_t n, pending;        /* boxes outstanding, plus one until the frame has issued them all */
    uint64_t *vals;
    pthread_mutex_t mu;
    size_t slot;              /* index in the live-join registry */
};

struct RootBox {
    pthread_mutex_t mu; pthread_cond_t cv;
    bool done; uint64_t result;
    int refs;                 /* client + root continuation; the last one frees */
};

static void rootbox_release(RootBox *b) {
    pthread_mutex_lock(&b->mu);
    int left = --b->refs;
    pthread_mutex_unlock(&b->mu);
    if (left == 0) { pthread_mutex_destroy(&b->mu); pthread_cond_destroy(&b->cv); free(b); }
}

#define ENTRY_READY ((Cont *)(uintptr_t)1)

/* a job: EVALUATE(entry); RESUME(k, v) — whose k may head a delivery chain of
 * published entry, of which each job delivers exactly one */
typedef enum { TK_EVAL = 0, TK_RESUME } TaskKind;
typedef struct { TaskKind kind; EntryId entry; Cont *k; uint64_t v; } Task;

/* the ready-job multiset: a linked list of fixed-size chunks; push, pop at
 * either end and a policy-chosen pop are each O(1) */
#define QCHUNK 254
typedef struct QChunk { struct QChunk *prev, *next; uint32_t lo, hi; Task t[QCHUNK]; } QChunk;
typedef struct { pthread_mutex_t mu; QChunk *front, *back; size_t len; } Queue;

typedef struct { const char *name; FamStart start; FamResume resume; size_t loc_size; bool pure; } FamilyDef;
static FamilyDef FAM[F_MAX];
static size_t n_fam = F_WHNF + 1;  /* F_WHNF is built in; registered families follow */
static Family F_INTERN;
static void intern_families_init(void);
static uint64_t obs_key(FaceId eta, PinSet P) { uint64_t w[2] = { eta, P }; return interner_intern(&M.keys, w, 2, NULL); }
static FaceId key_face(uint64_t b) { size_t n; return interner_get(&M.keys, b, &n)[0]; }
static PinSet key_pins(uint64_t b) { size_t n; return interner_get(&M.keys, b, &n)[1]; }

static struct {
    /* cache */
    Interner keys;                 /* (family, a, b, env version) → EntryId */
    Chunked entries;               /* Entry per EntryId-1, non-moving, zero = U */
    /* ready jobs */
    Queue shared;                  /* jobs pushed by threads outside the pool */
    Queue *wq;                     /* one per worker: its own pushes, taken back first */
    size_t outstanding;            /* §35: queued + executing jobs (+ reserved launches); atomic */
    pthread_mutex_t idle_mu; pthread_cond_t work_cv, idle_cv;
    size_t idle; bool stop;        /* parked workers; pool shutdown (under idle_mu) */
    pthread_t *workers; size_t nworkers;
    Pool cont_pool, chunk_pool;
    Pool loc_pool[F_MAX];             /* frame locals records, per family (made when the families are defined) */
    /* rooted results (immutable payloads), an intrusive list */
    EvalResult *results;
    /* live joins: a join that never fills (stuck children) is dismantled at teardown */
    VEC(Cont *) stuck;                /* teardown: frames reached as stuck waiters or queued jobs */
    /* readings: one shard per thread that has executed protocol events */
    struct Shard *shards;             /* pushed by CAS, one per thread */
    uint64_t epoch;
} E;

/* A shard is written by its one thread only: the protocol events and the
 * steps per family that thread executed (exact counts). A reading sums the
 * shards' snapshots; no counter is shared between writers. */
typedef struct Shard { struct Shard *next; Count ev[RD_STEPS]; Count steps[F_MAX]; } Shard;
static uint64_t eval_epochs;                               /* one per evaluator lifetime, never reused */
static __thread Shard *tl_shard; static __thread uint64_t tl_epoch;
static Shard *shard(void) {
    if (tl_epoch != E.epoch) {
        Shard *s = calloc(1, sizeof *s); require(s, "out of memory: a reading shard");
        s->next = __atomic_load_n(&E.shards, __ATOMIC_RELAXED);
        while (!__atomic_compare_exchange_n(&E.shards, &s->next, s, true, __ATOMIC_RELEASE, __ATOMIC_RELAXED)) ;
        tl_shard = s; tl_epoch = E.epoch;
    }
    return tl_shard;
}
static void event(Reading r) { count_bump(&shard()->ev[r]); }
/* the steps executed so far, as a word for a caller's budget (saturating) */
static uint64_t steps_now(void) {
    Exact x = { 0, NULL }; uint64_t v;
    Shard *s = __atomic_load_n(&E.shards, __ATOMIC_ACQUIRE);
    for (; s; s = s->next) exact_add_count(&x, &s->ev[RD_STEP]);
    if (!exact_to_u64(&x, &v)) v = UINT64_MAX;
    exact_free(&x); return v;
}
static Entry *ENT(EntryId e);
EntryId eval_entry_find(Family f, uint64_t a, uint64_t b) { uint64_t w[3] = { f, a, b }; return interner_find(&E.keys, w, 3); }
void eval_work(size_t n, const EntryId *roots, Exact *out, size_t *support) {
    size_t ne = interner_count(&E.keys), cnt = 0;
    bool *seen = calloc(ne + 1, sizeof *seen);
    EntryId *stk = malloc((ne + 1) * sizeof *stk); size_t sp = 0;
    require(seen && stk, "out of memory: a work reading");
    for (size_t q = 0; q < n; q++) if (roots[q] && !seen[roots[q]]) { seen[roots[q]] = true; stk[sp++] = roots[q]; }
    while (sp) {
        Entry *e = ENT(stk[--sp]); cnt++;
        exact_add_count(out, &e->work);
        for (size_t d = 0; d < e->ndeps; d++) if (!seen[e->deps[d]]) { seen[e->deps[d]] = true; stk[sp++] = e->deps[d]; }
    }
    free(seen); free(stk);
    if (support) *support = cnt;
}
void eval_reading(Reading r, Family f, Exact *out) {
    require(r <= RD_STEPS && (r != RD_STEPS || (f >= 1 && f < F_MAX)), "bad reading");
    Shard *s = __atomic_load_n(&E.shards, __ATOMIC_ACQUIRE);
    for (; s; s = s->next) exact_add_count(out, r == RD_STEPS ? &s->steps[f] : &s->ev[r]);
}

Family family_register(const char *name, FamStart start, FamResume resume) {
    /* idempotent per name: machines are re-initialized many times in one process */
    for (size_t f = F_WHNF + 1; f < n_fam; f++) if (FAM[f].name == name || strcmp(FAM[f].name, name) == 0) { FAM[f].start = start; FAM[f].resume = resume; return (Family)f; }
    require(n_fam < F_MAX, "too many operation families");
    FAM[n_fam].name = name; FAM[n_fam].start = start; FAM[n_fam].resume = resume;
    FAM[n_fam].loc_size = 0; FAM[n_fam].pure = false;
    return (Family)n_fam++;
}
Family family_lookup(const char *name) {
    for (size_t f = F_WHNF + 1; f < n_fam; f++) if (strcmp(FAM[f].name, name) == 0) return (Family)f;
    return 0;
}
Family family_define(const char *name, FamResume step, size_t loc_size, bool pure) {
    Family f = family_register(name, NULL, step);
    FAM[f].loc_size = loc_size; FAM[f].pure = pure;
    if (E.epoch && loc_size && !E.loc_pool[f].size) pool_init(&E.loc_pool[f], loc_size);   /* defined while an evaluator is live */
    return f;
}

static void *worker_main(void *arg);
static void q_init(Queue *q); static size_t q_push(Queue *q, Task t); static bool q_take(Queue *q, bool back, Task *out); static void q_free(Queue *q);
static size_t outstanding(void);
static void evaluator_init(void);
static void evaluator_bind(void);

void eval_init(void) {
    memset(&E, 0, sizeof E);
    interner_init(&E.keys);
    chunked_init(&E.entries, sizeof(Entry));
    q_init(&E.shared);
    pthread_mutex_init(&E.idle_mu, NULL);
    pthread_cond_init(&E.work_cv, NULL);
    pthread_cond_init(&E.idle_cv, NULL);
    pool_init(&E.cont_pool, sizeof(Cont));
    pool_init(&E.chunk_pool, sizeof(QChunk));
    E.epoch = __atomic_add_fetch(&eval_epochs, 1, __ATOMIC_RELAXED);
    intern_families_init();
    dnf_families_init();
    subst_families_init();
    construct_families_init();
    scope_families_init();
    template_families_init();
    evaluator_init();
    templates_init();                  /* the library programs, registered once per machine */
    lib_families_init();
    pins_families_init();
    judge_families_init();
    proof_families_init();
    chain_families_init();
    effect_families_init();
    for (size_t f = 1; f < n_fam; f++) if (FAM[f].loc_size && !E.loc_pool[f].size) pool_init(&E.loc_pool[f], FAM[f].loc_size);   /* families defined in an earlier lifetime */
    evaluator_bind();
}

/* a new definition environment retires every observation: the memo, the
 * results and the pending pairs; the scheduler configuration survives */
void eval_reset(void) {
    size_t pending = outstanding();
    require(pending == 0, "eval_reset with outstanding evaluator work (the session boundary requires quiescence)");
    size_t w = E.nworkers;
    eval_free(); eval_init();
    if (w) eval_set_workers(w);
}
static void owned_link(Cont *owner, Owned *o, int is_join) {
    require(owner && owner->kind == K_FRAME, "a frame-owned resource is created by a frame's step");
    o->owner = owner; o->is_join = is_join; o->prev = NULL; o->next = owner->owned;
    if (owner->owned) owner->owned->prev = o;
    owner->owned = o;
}
static void owned_unlink(Owned *o) {
    if (o->prev) o->prev->next = o->next; else o->owner->owned = o->next;
    if (o->next) o->next->prev = o->prev;
}
static void join_release(Join *j) { pthread_mutex_destroy(&j->mu); free(j->vals); free(j); }
static void owned_free_all(Cont *k) {
    for (Owned *o = k->owned, *n; o; o = n) { n = o->next; if (o->is_join) join_release((Join *)o); else free(o); }
    k->owned = NULL;
}
void join_free(Join *j) {
    owned_unlink(&j->own);
    join_release(j);
}

static void stop_workers(void) {
    if (!E.nworkers) return;
    pthread_mutex_lock(&E.idle_mu);
    E.stop = true;
    pthread_cond_broadcast(&E.work_cv);
    pthread_mutex_unlock(&E.idle_mu);
    for (size_t i = 0; i < E.nworkers; i++) pthread_join(E.workers[i], NULL);
    /* jobs still queued at a worker move to the shared queue */
    for (size_t i = 0; i < E.nworkers; i++) { Task t; while (q_take(&E.wq[i], false, &t)) q_push(&E.shared, t); q_free(&E.wq[i]); }
    free(E.wq); E.wq = NULL;
    free(E.workers); E.workers = NULL; E.nworkers = 0; E.stop = false;
}

void eval_set_workers(size_t n) {
    stop_workers();
    if (!n) return;
    E.workers = calloc(n, sizeof(pthread_t)); E.wq = calloc(n, sizeof(Queue));
    require(E.workers && E.wq, "out of memory");
    for (size_t i = 0; i < n; i++) q_init(&E.wq[i]);
    E.nworkers = n;
    for (size_t i = 0; i < n; i++) require(pthread_create(&E.workers[i], NULL, worker_main, (void *)(uintptr_t)(i + 1)) == 0, "cannot start worker");
}
size_t eval_workers(void) { return E.nworkers; }

static Entry *ENT(EntryId e) { return (Entry *)chunked_at(&E.entries, e - 1); }
static const uint64_t *entry_key(EntryId e) { size_t n; return interner_get(&E.keys, e, &n); }
Family eval_entry_family(EntryId e) { return (Family)entry_key(e)[0]; }
uint64_t eval_entry_a(EntryId e) { return entry_key(e)[1]; }
uint64_t eval_entry_b(EntryId e) { return entry_key(e)[2]; }

static void cont_dispose(Cont *k) {
    /* a waiter that will never be resumed: release what it owns, and what the
     * continuations it would have resumed own — up its chain of unkeyed frames
     * (subroutines, launched frames) and from a join box to its frame, ending
     * at a root, an external receiver, or a keyed frame (whose own entry's
     * waiters are disposed with that entry) */
    while (k && !k->disposed) {
        k->disposed = true;
        if (k->kind == K_FRAME) vec_push(&E.stuck, k);
        if (k->kind == K_EXTERNAL) { if (k->ext_free) k->ext_free(k->ext_ctx); return; }
        if (k->kind == K_ROOT) { rootbox_release(k->root); return; }
        if (k->kind == K_JOIN) { k = k->join->frame; continue; }
        if (k->dest) return;
        k = k->parent;
    }
}

void eval_free(void) {
    stop_workers();
    effect_free();
    for (Shard *s = E.shards, *n; s; s = n) {
        n = s->next;
        for (size_t r = 0; r < RD_STEPS; r++) count_free(&s->ev[r]);
        for (size_t f = 0; f < F_MAX; f++) count_free(&s->steps[f]);
        free(s);
    }
    E.shards = NULL;
    interner_set_flatten_hook(NULL);
    size_t ne = interner_count(&E.keys);
    for (size_t i = 0; i < ne; i++) {
        Entry *e = chunked_peek(&E.entries, i);
        if (!e) continue;
        count_free(&e->work); free(e->deps);
        Cont *h = e->head;
        if (h == ENTRY_READY) continue;
        for (Cont *k = h; k; k = k->next) cont_dispose(k);     /* suspended forever: stuck demands */
    }
    {   Task t; while (q_take(&E.shared, false, &t)) if (t.kind == TK_RESUME) cont_dispose(t.k); }   /* jobs never run */
    interner_free(&E.keys);
    chunked_free(&E.entries);
    for (EvalResult *r = E.results; r; ) { EvalResult *nx = r->next_alloc; free(r->faces); free(r->terms); free(r); r = nx; }
    /* the stuck frames reached above own their remaining blocks and joins */
    for (size_t i = 0; i < E.stuck.len; i++) owned_free_all(E.stuck.data[i]);
    vec_free(&E.stuck);
    pool_destroy(&E.cont_pool);
    pool_destroy(&E.chunk_pool);
    for (size_t f = 0; f < F_MAX; f++) if (E.loc_pool[f].size) pool_destroy(&E.loc_pool[f]);
    q_free(&E.shared);
    pthread_mutex_destroy(&E.idle_mu);
    pthread_cond_destroy(&E.work_cv); pthread_cond_destroy(&E.idle_cv);
    memset(&E, 0, sizeof E);
}

static Cont *cont_new(ContKind kind, EntryId dest, FaceId chi) {
    Cont *k = pool_alloc(&E.cont_pool);
    k->kind = kind; k->dest = dest; k->chi = chi; k->disposed = false; k->owner = 0; k->owned = NULL;
    return k;
}
static Pool *loc_pool(Family f) { return &E.loc_pool[f]; }
static void cont_release(Cont *k) {
    if (k->kind == K_FRAME && k->owned) owned_free_all(k);
    if (k->kind == K_FRAME && k->loc) pool_free(loc_pool(k->fam), k->loc);
    pool_free(&E.cont_pool, k);
}
Cont *frame_new(Family f, EntryId dest) {
    Cont *k = cont_new(K_FRAME, dest, 0); k->fam = f; k->owner = dest;
    if (FAM[f].loc_size) k->loc = pool_alloc(loc_pool(f));
    return k;
}
Cont *frame_new(Family f, EntryId dest);
static EntryId cont_owner(const Cont *k) {
    if (!k) return 0;
    if (k->kind == K_FRAME) return k->owner;
    if (k->kind == K_JOIN) return k->join->frame ? k->join->frame->owner : 0;
    return 0;
}
Cont *frame_sub(Family f, const Cont *caller) {
    require(f > F_WHNF && f < n_fam && FAM[f].start == NULL, "a subroutine is a frame family");
    Cont *k = frame_new(f, 0); k->owner = cont_owner(caller);
    return k;
}

Cont *cont_external(ExternalDeliver fn, void *ctx, void (*free_ctx)(void *)) {
    Cont *k = cont_new(K_EXTERNAL, 0, 0);
    k->ext_fn = fn; k->ext_ctx = ctx; k->ext_free = free_ctx;
    return k;
}

static EvalResult *result_new(ResultClass cls, RefId ref) {
    EvalResult *r = calloc(1, sizeof *r);
    require(r, "out of memory");
    r->cls = cls; r->ref = ref;
    EvalResult *h = __atomic_load_n(&E.results, __ATOMIC_RELAXED);
    do r->next_alloc = h; while (!__atomic_compare_exchange_n(&E.results, &h, r, false, __ATOMIC_RELEASE, __ATOMIC_RELAXED));
    return r;
}

static EvalResult *result_invalid(const char *msg) {
    EvalResult *r = result_new(R_INVALID, 0);
    r->message = msg;
    return r;
}

static EvalResult *result_system(RefId owner, size_t n, const FaceId *faces, const RefId *terms) {
    EvalResult *r = result_new(R_SYSTEM, owner);
    r->nbr = n;
    r->faces = malloc((n ? n : 1) * sizeof(FaceId));
    r->terms = malloc((n ? n : 1) * sizeof(RefId));
    require(r->faces && r->terms, "out of memory");
    if (n && faces) { memcpy(r->faces, faces, n * sizeof(FaceId)); memcpy(r->terms, terms, n * sizeof(RefId)); }   /* NULL: filled by the caller, one entry per step */
    return r;
}

/* ---------------- job queues ----------------
 * A worker pushes to its own queue and takes from its back, so a chain of
 * steps continues on the thread that holds its frame; an idle worker takes
 * from the front of the shared queue, then of another worker's queue. A
 * worker wakes a parked one only when its queue holds surplus work; a push
 * from outside the pool always offers its job to a parked worker. */
static __thread size_t tl_worker;              /* 0 outside the pool; worker i is i + 1 */
static void q_init(Queue *q) { pthread_mutex_init(&q->mu, NULL); q->front = q->back = NULL; q->len = 0; }
static void q_unlink_if_empty(Queue *q, QChunk *c) {
    if (c->lo < c->hi) return;
    if (c->prev) c->prev->next = c->next; else q->front = c->next;
    if (c->next) c->next->prev = c->prev; else q->back = c->prev;
    pool_free(&E.chunk_pool, c);
}
static size_t q_push(Queue *q, Task t) {
    pthread_mutex_lock(&q->mu);
    if (!q->back || q->back->hi == QCHUNK) {
        QChunk *c = pool_alloc(&E.chunk_pool);
        c->lo = c->hi = 0; c->next = NULL; c->prev = q->back;
        if (q->back) q->back->next = c; else q->front = c;
        q->back = c;
    }
    q->back->t[q->back->hi++] = t;
    size_t n = ++q->len;
    pthread_mutex_unlock(&q->mu);
    return n;
}
static bool q_take(Queue *q, bool back, Task *out) {
    pthread_mutex_lock(&q->mu);
    bool got = q->len > 0;
    if (got) {
        QChunk *c = back ? q->back : q->front;
        *out = back ? c->t[--c->hi] : c->t[c->lo++];
        q->len--; q_unlink_if_empty(q, c);
    }
    pthread_mutex_unlock(&q->mu);
    return got;
}
static void q_free(Queue *q) { pthread_mutex_destroy(&q->mu); }
/* the next job for this thread: its own queue's back, then the shared
 * queue, then another worker's queue */
static bool take_job(Task *out) {
    size_t w = tl_worker;
    if (w && q_take(&E.wq[w - 1], true, out)) return true;
    if (q_take(&E.shared, false, out)) return true;
    for (size_t i = 0; w && i < E.nworkers; i++) if (i != w - 1 && q_take(&E.wq[i], false, out)) return true;
    return false;
}
static void wake_one(void) {
    if (!__atomic_load_n(&E.idle, __ATOMIC_SEQ_CST)) return;
    pthread_mutex_lock(&E.idle_mu); pthread_cond_signal(&E.work_cv); pthread_mutex_unlock(&E.idle_mu);
}
static void push_job(Task t) {
    size_t w = tl_worker;
    size_t n = q_push(w ? &E.wq[w - 1] : &E.shared, t);
    if (!w || n > 1) wake_one();
}

/* §35 quiescence protocol: outstanding = queued + executing. A launch
 * reserves its job (outstanding += 1) before the key can be observed
 * RUNNING, so no observer can see a running key with outstanding == 0. */
static void reserve_job(void) { __atomic_add_fetch(&E.outstanding, 1, __ATOMIC_SEQ_CST); }
static size_t outstanding(void) { return __atomic_load_n(&E.outstanding, __ATOMIC_SEQ_CST); }
static void finish_job(void) {
    size_t was = __atomic_fetch_sub(&E.outstanding, 1, __ATOMIC_SEQ_CST);
    require(was > 0, "finish without outstanding job");
    if (was == 1) { pthread_mutex_lock(&E.idle_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.idle_mu); }
}
static void enqueue_reserved(Task t) { push_job(t); }
static void enqueue(Task t) { reserve_job(); push_job(t); }

/* one delivery: the RESUME job of k. DELIVER is counted here, for ready hits
 * and for publication alike; the resumed frame step is counted when the
 * RESUME job executes. Delivery never happens inside an entry transition. */
static void deliver(Cont *k, uint64_t v) {
    /* k heads a delivery chain only when it comes from a published waiter
     * stack; every other caller passes a continuation whose link is clear */
    event(RD_DELIVER);
    Task t; memset(&t, 0, sizeof t); t.kind = TK_RESUME; t.k = k; t.v = v;
    enqueue(t);
}



/* ---------------- entries ---------------- */

static EntryId entry_intern(Family f, uint64_t a, uint64_t b) {
    /* every key names its dependencies in its operands (an observation its
     * pin set, an unfolding its body revision): no environment version. The
     * entry's operands are read from its key record, so a zero entry is a
     * complete U state the moment its key is discoverable. */
    uint64_t w[3] = { f, a, b };
    EntryId id = interner_intern(&E.keys, w, 3, NULL);
    chunked_at(&E.entries, id - 1);
    return id;
}

EntryState eval_entry_state(EntryId e) {
    Cont *h = __atomic_load_n(&ENT(e)->head, __ATOMIC_ACQUIRE);
    return h == NULL ? E_UNEVALUATED : h == ENTRY_READY ? E_READY : E_RUNNING;
}
size_t eval_entry_count(void) { return interner_count(&E.keys); }
bool eval_entry_live(EntryId e) { return interner_live(&E.keys, e); }
size_t eval_entry_runs(EntryId e) { return __atomic_load_n(&ENT(e)->runs, __ATOMIC_ACQUIRE); }

/* PUB(K,v) + R(W) → D(v) + {DELIVER(c,v) : c ∈ W}: the value is stored, the
 * waiter stack is exchanged for READY in one atomic step, and the stack is
 * handed to one delivery job; each delivery job delivers one waiter and
 * hands the rest on (§26, bounded per step). */
void family_publish(EntryId eid, uint64_t v) {
    Entry *e = ENT(eid);
    __atomic_store_n(&e->value, v, __ATOMIC_RELEASE);
    Cont *w = __atomic_exchange_n(&e->head, ENTRY_READY, __ATOMIC_ACQ_REL);
    require(w != NULL && w != ENTRY_READY, "publish into an entry that is not running");
    event(RD_PUBLISH);
    deliver(w, v);
}


/* REQ(K,c): U → R({c}) + EVAL(K), R(W) → R(W ⊎ {c}), D(v) → D(v) + DELIVER(c,v) */
/* A failed CAS here means another request launched, pushed onto or published
 * this entry in between: each failure is charged to that success (at most
 * one per concurrent worker per success), so the retries of all requests are
 * within a constant factor of their number. Strong CAS only: a spurious
 * failure would be charged to nothing. */
static void ledger_lock(Entry *o) { while (__atomic_exchange_n(&o->ledger_lk, 1, __ATOMIC_ACQUIRE)) sched_yield(); }
static void ledger_unlock(Entry *o) { __atomic_store_n(&o->ledger_lk, 0, __ATOMIC_RELEASE); }
static void record_dep(EntryId owner, EntryId eid) {
    Entry *o = ENT(owner);
    ledger_lock(o);
    if (o->ndeps == o->capdeps) {
        size_t c = o->capdeps ? 2 * o->capdeps : 4;
        EntryId *d = realloc(o->deps, c * sizeof *d); require(d, "out of memory: a dependency record");
        o->deps = d; o->capdeps = c;
    }
    o->deps[o->ndeps++] = eid;
    ledger_unlock(o);
}
static void record_work(EntryId owner) { Entry *o = ENT(owner); ledger_lock(o); count_bump(&o->work); ledger_unlock(o); }
static void request_entry(EntryId eid, Cont *k) {
    Entry *e = ENT(eid);
    event(RD_REQUEST);
    {   EntryId o = cont_owner(k); if (o) record_dep(o, eid); }
    for (;;) {
        Cont *h = __atomic_load_n(&e->head, __ATOMIC_ACQUIRE);
        if (h == ENTRY_READY) {
            uint64_t v = __atomic_load_n(&e->value, __ATOMIC_ACQUIRE);
            k->next = NULL;             /* a failed push left a stale link: k is delivered alone */
            deliver(k, v);
            return;
        }
        if (h == NULL) {
            /* the launch is reserved before RUNNING can be observed */
            reserve_job();
            k->next = NULL;
            if (__atomic_compare_exchange_n(&e->head, &h, k, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                event(RD_LAUNCH);
                Task job; memset(&job, 0, sizeof job); job.kind = TK_EVAL; job.entry = eid;
                enqueue_reserved(job);
                return;
            }
            finish_job();               /* not the launcher: give the reservation back */
            continue;
        }
        k->next = h;
        if (__atomic_compare_exchange_n(&e->head, &h, k, false, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE)) {
            return;
        }
    }
}

void family_request(Family f, uint64_t a, uint64_t b, Cont *k) {
    require(f >= F_WHNF && f < n_fam && FAM[f].resume, "unregistered family");
    request_entry(entry_intern(f, a, b), k);
}

/* ---------------- frame programs ----------------
 * A step schedules its continuation: a request (U: install the one
 * producer; R: attach to it; D: delivery), the subroutine's first step, its
 * own next step, a publication or the parent's resumption.
 * A scheduled step that reschedules its own frame records that here, before
 * the frame can be resumed elsewhere; the executing job reads only this
 * thread-local flag after the step (never the frame, which may already be
 * running on another worker). */
static __thread Cont *tl_step_frame; static __thread bool tl_kept;
static __thread int tl_in_job;          /* inside a counted step: synchronous requests are refused */
static void keep_frame(Cont *k) { if (k == tl_step_frame) tl_kept = true; }

static void enqueue_resume(Cont *k, uint64_t v) {
    Task t; memset(&t, 0, sizeof t); t.kind = TK_RESUME; t.k = k; t.v = v;
    enqueue(t);
}
void frame_request(Cont *k, Family f, uint64_t a, uint64_t b) {
    keep_frame(k);
    family_request(f, a, b, k);
}
void frame_call(Cont *k, Cont *child) {
    require(child->kind == K_FRAME && child->dest == 0, "a subroutine frame of this caller");
    child->parent = k; keep_frame(k);
    enqueue_resume(child, 0);
}
void frame_yield(Cont *k) {
    keep_frame(k);
    enqueue_resume(k, 0);
}
void frame_finish(Cont *k, uint64_t v) {
    if (k->parent) { Cont *p = k->parent; k->parent = NULL; enqueue_resume(p, v); return; }
    family_publish(k->dest, v);
}

/* the interning subroutine: a bounded advance of the insertion per step */
#define INTERN_BUDGET 8
/* the stepped construction of a record: at most INTERN_BUDGET units per
 * step; a large record then requests its flat record (INTERNING.md) */
static Family F_FLATTEN;
static void intern_step(Cont *k, uint64_t v) {
    InternState *s = k->loc;
    uint64_t r = 0; int st;
    FR_BEGIN(k);
    while ((st = intern_advance(s, INTERN_BUDGET)) == INTERN_RUNNING) FR_YIELD(k);
    if (st == INTERN_FLATTEN) { FR_AWAIT(k, r, F_FLATTEN, s->t->index, s->root); s->result = r; }
    {   bool *created = (bool *)(uintptr_t)k->w[0];
        if (created) *created = s->created; }
    FR_FINISH(k, s->result);
    FR_END(k);
}
Cont *intern_sub(const Cont *caller, Interner *t, WordBuf *buf, bool *created) {
    Cont *k = frame_sub(F_INTERN, caller);
    intern_begin(k->loc, t, NULL, buf, buf->n);
    k->w[0] = (uint64_t)(uintptr_t)created;
    return k;
}
/* the one owner of a large record's flat record, keyed by (table, tree
 * root): one leaf (≤ TREE_FAN words) copied per step, then the record
 * published; every other requester is delivered its id */
typedef struct { Interner *t; uint64_t root, *dst; size_t n, at; uint64_t stk[TREE_LEVELS]; uint8_t pos[TREE_LEVELS]; int sp; } FlatLoc;
static void flatten_step(Cont *k, uint64_t v) {
    FlatLoc *L = FR_LOC(k, FlatLoc);
    FR_BEGIN(k);
    L->t = interner_by_index(k->w[0]); L->root = k->w[1];
    require(L->t, "intern.flatten of a freed table");
    { uint64_t id = interner_flat_of(L->t, L->root); if (id) FR_FINISH(k, id); }   /* published in an earlier generation */
    {   size_t m; const uint64_t *rw = interner_tree_get(L->t, L->root, &m);
        require(m == 3 && rw[0] == TREE_ROOT, "intern.flatten of a non-root");
        L->n = rw[1]; L->stk[0] = rw[2]; L->pos[0] = 0; L->sp = 1; }
    L->dst = interner_flat_reserve(L->t, L->n); L->at = 0;
    while (L->sp > 0) {
        /* to the next leaf (≤ 2·TREE_LEVELS moves), copy it */
        for (;;) {
            size_t m; const uint64_t *w = interner_tree_get(L->t, L->stk[L->sp - 1], &m);
            if (w[0] == TREE_LEAF) { memcpy(L->dst + L->at, w + 1, (m - 1) * sizeof(uint64_t)); L->at += m - 1; L->sp--; break; }
            if ((size_t)L->pos[L->sp - 1] + 1 < m) { uint64_t c = w[1 + L->pos[L->sp - 1]++]; L->stk[L->sp] = c; L->pos[L->sp] = 0; L->sp++; }
            else { L->sp--; if (!L->sp) break; }
        }
        FR_YIELD(k);
    }
    require(L->at == L->n, "tree length");
    FR_FINISH(k, interner_flat_publish(L->t, L->root, L->dst, L->n));
    FR_END(k);
}
static uint64_t flatten_root(Interner *t, uint64_t root) { return family_call(F_FLATTEN, t->index, root); }
static void intern_families_init(void) {
    F_INTERN = family_define("intern", intern_step, sizeof(InternState), false);
    F_FLATTEN = family_define("intern.flatten", flatten_step, sizeof(FlatLoc), true);
    interner_set_flatten_hook(flatten_root);
}

/* the synchronous embedding: an external caller submits a root and drives the
 * ordinary scheduler until it is delivered. Inside a counted step a request
 * suspends the frame instead; it is never drained by a host call. */
uint64_t family_call(Family f, uint64_t a, uint64_t b) {
    require(!tl_in_job, "synchronous request of %s inside a counted step: the frame must await it", f < n_fam ? FAM[f].name : "?");
    WhnfStatus st;
    uint64_t v = family_run(f, a, b, &st);
    require(st == W_OK, "synchronous request of %s did not complete (an unresolved dependency)", FAM[f].name);
    return v;
}

/* An observation request: the observation frame validates the occurrence
 * (the ambient face must entail the reference's required face, which already
 * folds in its free variables'), projects χ to the support and awaits
 * WHNF(t, η) — every operand awaited, never computed synchronously, so the
 * request is the same inside a counted step and from a root. */
static Family F_OBS_;
/* An observation is bound to a pin set P (pins.h): the revisions of the
 * symbols it may unfold. The key of WHNF(t, η) under P is (t, [η, P]).
 * P = 0 asks for the closure of t's symbols at their current revisions,
 * read once at the start of the request. */
void eval_request_pinned(RefId t, FaceId chi, PinSet P, Cont *k) {
    k->next = NULL;
    if (fc_is_false(chi)) { deliver(k, (uint64_t)(uintptr_t)result_new(R_NO_OBSERVATION, t)); return; }
    Cont *f = frame_new(F_OBS_, 0);
    f->w[0] = t; f->w[1] = chi; f->w[2] = 0; f->w[3] = P;
    frame_launch(f, k);
}
void eval_request(RefId t, FaceId chi, Cont *k) { eval_request_pinned(t, chi, 0, k); }


/* ---------------- the evaluator: a frame program ----------------
 * WHNF(t, χ) (χ projected to t's support) is a frame family like every
 * other: each step does a constant amount of work and awaits its operands
 * from their families (fields, binder application, face tests, projections,
 * constructions) and its sub-observations through the observation
 * subroutine. A branchwise result is a join: the frame issues one branch per
 * step and is resumed by the last arrival (§12, §26). */
static Family F_UNFOLDF, F_COMPCLAUSEF, F_CBRANCH;
static Family F_OBS, F_FIELDF, F_BINDERF, F_CONSTRUCTF, F_HEADF, F_FCENTF, F_FCPROJF, F_FCMEETF, F_FCJOINF, F_FCFORALLF, F_FCENDF;
#define RES(x) ((EvalResult *)(uintptr_t)(x))
#define RV(r) ((uint64_t)(uintptr_t)(r))
static uint64_t binder_rec(Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) { uint64_t e[4] = { sort, slot, field, image }; return interner_intern(&M.keys, e, 4, NULL); }
/* a construction request (construct.c) made by the evaluator: no declared
 * face. The request record is built into a word buffer (a bounded number of
 * words for the fixed shapes, one branch per step for a system) and interned
 * by the stepped subroutine; the subroutine then awaits the construction. */
static Family F_CREQ;
typedef struct { WordBuf w; uint64_t id; bool created; } CrLoc;
static void creq_head(WordBuf *w, Tag tag, uint64_t payload, uint64_t levels, size_t nf) {
    wordbuf_init(w);
    wordbuf_push(w, tag); wordbuf_push(w, payload); wordbuf_push(w, levels); wordbuf_push(w, 0); wordbuf_push(w, 0); wordbuf_push(w, 0); wordbuf_push(w, nf);
}
static void creq_field(WordBuf *w, Field f) { wordbuf_push(w, f.kind); wordbuf_push(w, f.slot); wordbuf_push(w, f.id); }
static void creq_step(Cont *k, uint64_t v) {
    CrLoc *L = FR_LOC(k, CrLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_CALL(k, L->id, intern_sub(k, &M.keys, &L->w, &L->created));
    FR_AWAIT(k, r, F_CONSTRUCTF, L->id, 0);
    FR_FINISH(k, r);
    FR_END(k);
}
/* the request record already in a buffer (moved into the subroutine) */
static Cont *creq_buf(const Cont *k, WordBuf *w) { Cont *c = frame_sub(F_CREQ, k); FR_LOC(c, CrLoc)->w = *w; wordbuf_init(w); return c; }
Cont *construct_buf_sub(const Cont *caller, WordBuf *w) { return creq_buf(caller, w); }
static Cont *creq(const Cont *k, Tag tag, uint64_t payload, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b) {
    require(nf <= 6 && nb <= 1, "a fixed-shape construction request");
    WordBuf w; creq_head(&w, tag, payload, levels, nf);
    for (size_t q = 0; q < nf; q++) creq_field(&w, f[q]);
    wordbuf_push(&w, nb);
    for (size_t q = 0; q < nb; q++) { wordbuf_push(&w, b[q].sort); wordbuf_push(&w, b[q].formal); wordbuf_push(&w, b[q].domain_field); }
    return creq_buf(k, &w);
}
/* a sub-observation of an evaluation frame (whnf or forward: w[1] is its key's [η, P]) under the same pins */
static Cont *obs_sub(const Cont *k, RefId x, FaceId chi) { Cont *c = frame_sub(F_OBS, k); c->w[0] = x; c->w[1] = chi; c->w[2] = 0; c->w[3] = key_pins(k->w[1]); return c; }
/* an observation subroutine for any frame: x under χ and pins P */
Cont *observe_sub(const Cont *caller, RefId x, FaceId chi, uint64_t P) { Cont *c = frame_sub(F_OBS, caller); c->w[0] = x; c->w[1] = chi; c->w[2] = 0; c->w[3] = P; return c; }
Cont *construct_sub(const Cont *caller, Tag tag, uint64_t payload, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b) { return creq(caller, tag, payload, levels, nf, f, nb, b); }
/* the observation of x under χ ∧ φ (a branch) */
static Cont *obs_under(const Cont *k, RefId x, FaceId chi, FaceId phi) { Cont *c = obs_sub(k, x, chi); c->w[2] = phi; return c; }

/* observe x under χ: no observation on the false face; an invalid occurrence
 * outside x's required face; otherwise the producer (x, π_S(x) χ) */
static void obs_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    RefId x = k->w[0];
    FR_BEGIN(k);
    if (!k->w[3]) {
        /* the premises: the closure of x's symbols at the revisions read now */
        { WordBuf roots; wordbuf_init(&roots); wordbuf_push(&roots, 0); wordbuf_push(&roots, x); k->w[4] = (uint64_t)(uintptr_t)pins_closure_sub(k, &roots); }
        FR_CALL(k, k->w[3], (Cont *)(uintptr_t)k->w[4]);
    }
    if (k->w[2]) { FR_AWAIT(k, r, F_FCMEETF, k->w[1], k->w[2]); k->w[1] = r; k->w[2] = 0; }
    if (fc_is_false(k->w[1])) FR_FINISH(k, RV(result_new(R_NO_OBSERVATION, x)));
    FR_AWAIT(k, r, F_FCENTF, k->w[1], ref_required(x));
    if (r != 2) FR_FINISH(k, RV(result_invalid("occurrence outside its required face")));
    FR_AWAIT(k, r, F_FCPROJF, k->w[1], ref_support(x));
    FR_AWAIT(k, r, F_WHNF, x, obs_key(r, k->w[3]));
    FR_FINISH(k, r);
    FR_END(k);
}

/* frame-owned memory: a block a frame's locals point to, owned by that
 * frame (a frame suspended forever does not leak it) */
typedef struct { Owned own; uint64_t pad; } MemHdr;
void *frame_mem(size_t bytes) {
    MemHdr *h = malloc(sizeof(MemHdr) + (bytes ? bytes : 1)); require(h, "out of memory");
    owned_link(tl_step_frame, &h->own, 0);
    return h + 1;
}
void frame_mem_free(void *p) {
    if (!p) return;
    MemHdr *h = (MemHdr *)p - 1;
    owned_unlink(&h->own);
    free(h);
}

Join *join_new(Cont *frame, size_t n) {
    Join *j = calloc(1, sizeof *j);
    require(j, "out of memory");
    j->frame = frame; j->n = n; j->pending = n + 1;
    j->vals = calloc(n ? n : 1, sizeof(uint64_t));
    require(j->vals, "out of memory");
    pthread_mutex_init(&j->mu, NULL);
    owned_link(frame, &j->own, 1);
    return j;
}
static bool join_arrive(Join *j) {
    pthread_mutex_lock(&j->mu);
    bool last = --j->pending == 0;
    pthread_mutex_unlock(&j->mu);
    return last;
}
static Cont *join_box(Join *j, size_t i) { require(i < j->n, "join box out of range"); Cont *bk = cont_new(K_JOIN, 0, 0); bk->join = j; bk->box = i; return bk; }
void join_request(Join *j, size_t i, Family f, uint64_t a, uint64_t b) { family_request(f, a, b, join_box(j, i)); }
void join_call(Join *j, size_t i, Cont *child) {
    require(child->kind == K_FRAME && child->dest == 0, "a subroutine frame");
    child->parent = join_box(j, i);
    enqueue_resume(child, 0);
}
uint64_t join_value(const Join *j, size_t i) { return j->vals[i]; }
/* a frame started for a continuation that is not a frame (an external owner) */
void frame_launch(Cont *f, Cont *parent) {
    require(f->kind == K_FRAME && f->dest == 0, "a detached frame");
    f->parent = parent;
    enqueue_resume(f, 0);
}
void join_fill(Join *j, size_t i, uint64_t v) {
    require(i < j->n, "join box out of range");
    pthread_mutex_lock(&j->mu); j->vals[i] = v; pthread_mutex_unlock(&j->mu);
    if (join_arrive(j)) enqueue_resume(j->frame, 0);
}
static void resume_join(Cont *k, uint64_t v) {
    Join *j = k->join;
    pthread_mutex_lock(&j->mu); j->vals[k->box] = v; pthread_mutex_unlock(&j->mu);
    if (join_arrive(j)) enqueue_resume(j->frame, 0);
}
void frame_await_join(Cont *k, Join *j) {
    keep_frame(k);
    if (join_arrive(j)) enqueue_resume(k, 0);
}

typedef struct {
    Tag tag; uint64_t levels, payload, a1, a3, a4, x;
    EvalResult *res;
    size_t n, q, kept, m; FaceId uni, g; FaceId *faces; RefId *terms;
    DimVarId j; RefId fam, tube, cap; FaceId phi;
    Join *gath, *flat; size_t nfs; EvalResult *res2; WordBuf wb;
} WhLoc;
static void wh_free(WhLoc *L) { frame_mem_free(L->faces); frame_mem_free(L->terms); L->faces = NULL; L->terms = NULL; }
static void wh_alloc(WhLoc *L, size_t n) {
    L->faces = frame_mem((n ? n : 1) * sizeof(FaceId)); L->terms = frame_mem((n ? n : 1) * sizeof(RefId));
}
static bool intro_tag(Tag t) { return t == T_UNIVERSE || t == T_PI || t == T_SIGMA || t == T_LAM || t == T_PAIR || t == T_PATH || t == T_PLAM; }
static bool elim_tag(Tag t) { return t == T_APP || t == T_FST || t == T_SND || t == T_PAPP || t == T_UNGLUE; }

static void whnf_step(Cont *k, uint64_t v) {
    WhLoc *L = FR_LOC(k, WhLoc);
    RefId t = k->w[0]; FaceId chi = key_face(k->w[1]); PinSet P = key_pins(k->w[1]);
    uint64_t r = 0;
    FR_BEGIN(k);
    if (ref_is_var(t)) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
    L->tag = ref_tag(t);
    if (intro_tag(L->tag)) FR_FINISH(k, RV(result_new(R_INTRODUCTION, t)));

    if (L->tag == T_GLOBAL) {
        /* a declared symbol without a body is an opaque constant: neutral */
        /* the revision this observation is bound to */
        FR_AWAIT(k, L->payload, F_HEADF, t, 0);
        {   RefId b = 0;
            if (!pins_lookup(P, (SymbolId)L->payload, &b)) FR_FINISH(k, RV(result_invalid("a symbol outside the observation's premises")));
            if (!b) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
            L->a1 = b; }
        FR_AWAIT(k, L->x, F_UNFOLDF, t, L->a1);
        FR_CALL(k, r, obs_sub(k, L->x, chi));
        FR_FINISH(k, r);
    }

    if (L->tag == T_GLUE_TYPE || L->tag == T_GLUE_INTRO) {
        FR_AWAIT(k, L->a1, F_FIELDF, t, 1);
        FR_AWAIT(k, r, F_FCENTF, chi, L->a1);
        if (r != 2) FR_FINISH(k, RV(result_new(R_INTRODUCTION, t)));
        FR_AWAIT(k, L->x, F_FIELDF, t, L->tag == T_GLUE_TYPE ? 2 : 4);
        FR_CALL(k, r, obs_sub(k, L->x, chi));
        FR_FINISH(k, r);
    }

    if (elim_tag(L->tag)) {
        if (L->tag == T_PAPP) {
            FR_AWAIT(k, L->a4, F_FIELDF, t, 4);
            FR_AWAIT(k, r, F_FCENDF, L->a4, 0);
            FR_AWAIT(k, r, F_FCENTF, chi, r);
            if (r == 2) { FR_AWAIT(k, L->x, F_FIELDF, t, 1); goto forward_x; }
            FR_AWAIT(k, r, F_FCENDF, L->a4, 1);
            FR_AWAIT(k, r, F_FCENTF, chi, r);
            if (r == 2) { FR_AWAIT(k, L->x, F_FIELDF, t, 2); goto forward_x; }
            FR_AWAIT(k, L->x, F_FIELDF, t, 3);
        } else if (L->tag == T_UNGLUE) {
            FR_AWAIT(k, L->a1, F_FIELDF, t, 1);
            FR_AWAIT(k, r, F_FCENTF, chi, L->a1);
            if (r == 2) {
                /* on the Glue face: (fst e) v */
                FR_AWAIT(k, L->a3, F_FIELDF, t, 3);
                FR_AWAIT(k, L->a4, F_FIELDF, t, 4);
                { Field f[1] = { { F_REF, NO_SLOT, L->a3 } }; FR_CALL(k, L->x, creq(k, T_FST, 0, LEVELS_NONE, 1, f, 0, NULL)); }
                { Field f[2] = { { F_REF, NO_SLOT, L->x }, { F_REF, NO_SLOT, L->a4 } }; FR_CALL(k, L->x, creq(k, T_APP, 0, LEVELS_NONE, 2, f, 0, NULL)); }
                goto forward_x;
            }
            FR_AWAIT(k, L->x, F_FIELDF, t, 4);
        } else {
            if (L->tag == T_APP) FR_AWAIT(k, L->a1, F_FIELDF, t, 1);
            FR_AWAIT(k, L->x, F_FIELDF, t, 0);
        }
        /* the scrutinee */
        FR_CALL(k, r, obs_sub(k, L->x, chi));
        L->res = RES(r);
        if (L->res->cls == R_NO_OBSERVATION || L->res->cls == R_INVALID) FR_FINISH(k, r);
        if (L->res->cls == R_NEUTRAL) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
        if (L->res->cls == R_SYSTEM) {
            /* distribute: the eliminator rebuilt around each branch — the
             * shared operands once, then the branch constructions as one join */
            L->n = L->res->nbr; wh_alloc(L, L->n);
            FR_AWAIT(k, L->levels, F_HEADF, t, 1);
            if (L->tag == T_PAPP) {
                L->j = binder_dim_var(t, 0);
                FR_AWAIT(k, L->fam, F_BINDERF, t, binder_rec(S_DIM, 0, 0, iv_var(L->j)));
                FR_AWAIT(k, L->a1, F_FIELDF, t, 1);
                FR_AWAIT(k, L->a3, F_FIELDF, t, 2);
            } else if (L->tag == T_UNGLUE) {
                FR_AWAIT(k, L->fam, F_FIELDF, t, 0);
                FR_AWAIT(k, L->a3, F_FIELDF, t, 2);
                FR_AWAIT(k, L->tube, F_FIELDF, t, 3);
            }
            L->flat = join_new(k, L->n);
            for (L->q = 0; L->q < L->n; L->q++) {
                L->faces[L->q] = L->res->faces[L->q];
                {   RefId bt = L->res->terms[L->q]; Cont *c;
                    if (L->tag == T_APP) { Field f[2] = { { F_REF, NO_SLOT, bt }, { F_REF, NO_SLOT, L->a1 } }; c = creq(k, T_APP, 0, LEVELS_NONE, 2, f, 0, NULL); }
                    else if (L->tag == T_FST || L->tag == T_SND) { Field f[1] = { { F_REF, NO_SLOT, bt } }; c = creq(k, L->tag, 0, LEVELS_NONE, 1, f, 0, NULL); }
                    else if (L->tag == T_PAPP) {
                        Field f[5] = { { F_REF, 0, L->fam }, { F_REF, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, bt }, { F_INTERVAL, NO_SLOT, L->a4 } };
                        Binder b[1] = { { S_DIM, L->j, NO_FIELD } };
                        c = creq(k, T_PAPP, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 1, b);
                    } else {
                        Field f[5] = { { F_REF, NO_SLOT, L->fam }, { F_FACE, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, L->tube }, { F_REF, NO_SLOT, bt } };
                        c = creq(k, T_UNGLUE, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 0, NULL);
                    }
                    join_call(L->flat, L->q, c); }
                if (L->q + 1 < L->n) FR_YIELD(k);
            }
            FR_JOIN(k, L->flat);
            for (L->q = 0; L->q < L->n; L->q++) { L->terms[L->q] = join_value(L->flat, L->q); FR_YIELD(k); }
            join_free(L->flat); L->flat = NULL;
            L->kept = L->n;
            goto branchwise;
        }
        /* an introduction under the eliminator */
        {   Tag ht = ref_tag(L->res->ref);
            if (L->tag == T_APP && ht != T_LAM) FR_FINISH(k, RV(result_invalid("application of a non-function introduction")));
            if ((L->tag == T_FST || L->tag == T_SND) && ht != T_PAIR) FR_FINISH(k, RV(result_invalid("projection of a non-pair introduction")));
            if (L->tag == T_PAPP && ht != T_PLAM) FR_FINISH(k, RV(result_invalid("path application of a non-path introduction")));
            if (L->tag == T_UNGLUE && ht != T_GLUE_INTRO) FR_FINISH(k, RV(result_invalid("unglue of a non-glue introduction"))); }
        if (L->tag == T_APP) FR_AWAIT(k, L->x, F_BINDERF, L->res->ref, binder_rec(S_TERM, 0, 1, L->a1));
        else if (L->tag == T_PAPP) FR_AWAIT(k, L->x, F_BINDERF, L->res->ref, binder_rec(S_DIM, 0, 0, L->a4));
        else FR_AWAIT(k, L->x, F_FIELDF, L->res->ref, L->tag == T_FST ? 0 : L->tag == T_SND ? 1 : 5);
        goto forward_x;
    }

    if (L->tag == T_SYSTEM) {
        /* the covered, consistent branches; a branch entailed by χ is the value */
        L->n = tnode_nfields(ref_tnode(t)) / 2;
        L->res = result_system(t, L->n, NULL, NULL);            /* filled one kept branch per step */
        L->kept = 0; L->uni = fc_false();
        for (L->q = 0; L->q < L->n; L->q++) {
            FR_AWAIT(k, L->phi, F_FIELDF, t, 2 * L->q);
            FR_AWAIT(k, r, F_FCMEETF, chi, L->phi);
            if (fc_is_false(r)) continue;                       /* inconsistent branch dropped */
            FR_AWAIT(k, L->x, F_FIELDF, t, 2 * L->q + 1);
            FR_AWAIT(k, r, F_FCENTF, chi, L->phi);
            if (r == 2) goto forward_x;
            L->res->faces[L->kept] = L->phi; L->res->terms[L->kept] = L->x; L->kept++;
            FR_AWAIT(k, L->uni, F_FCJOINF, L->uni, L->phi);
        }
        FR_AWAIT(k, r, F_FCENTF, chi, L->uni);
        if (r != 2) FR_FINISH(k, RV(result_invalid("system does not cover the ambient face")));
        L->res->nbr = L->kept;
        FR_FINISH(k, RV(L->res));
    }

    if (L->tag == T_COMP) {
        FR_AWAIT(k, L->phi, F_FIELDF, t, 1);
        FR_AWAIT(k, r, F_FCENTF, chi, L->phi);
        if (r == 2) { FR_AWAIT(k, L->x, F_BINDERF, t, binder_rec(S_DIM, 0, 2, iv_one())); goto forward_x; }   /* tube coverage first */
        L->j = binder_dim_var(t, 0);
        FR_AWAIT(k, L->fam, F_BINDERF, t, binder_rec(S_DIM, 0, 0, iv_var(L->j)));
        FR_AWAIT(k, L->tube, F_BINDERF, t, binder_rec(S_DIM, 0, 2, iv_var(L->j)));
        FR_AWAIT(k, L->cap, F_FIELDF, t, 3);
        FR_AWAIT(k, L->levels, F_HEADF, t, 1);
        FR_CALL(k, r, obs_sub(k, L->fam, chi));
        L->res = RES(r);
        if (L->res->cls == R_NO_OBSERVATION || L->res->cls == R_INVALID) FR_FINISH(k, r);
        if (L->res->cls == R_NEUTRAL) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
        if (L->res->cls == R_SYSTEM) {
            /* a branch available along the whole j line: outer guard ∀j.φ_k;
             * the branches are independent: one join of comp.branch */
            L->n = L->res->nbr; wh_alloc(L, L->n);
            L->kept = 0; L->uni = fc_false();
            L->flat = join_new(k, L->n);
            for (L->q = 0; L->q < L->n; L->q++) {
                {   Cont *c = frame_sub(F_CBRANCH, k);
                    c->w[0] = L->res->faces[L->q]; c->w[1] = L->res->terms[L->q]; c->w[2] = L->j; c->w[3] = chi;
                    c->w[4] = L->phi; c->w[5] = L->tube; c->w[6] = L->cap; c->w[7] = L->levels;
                    join_call(L->flat, L->q, c); }
                if (L->q + 1 < L->n) FR_YIELD(k);
            }
            FR_JOIN(k, L->flat);
            for (L->q = 0; L->q < L->n; L->q++) {
                if (!join_value(L->flat, L->q)) { FR_YIELD(k); continue; }          /* inconsistent along the line: dropped */
                {   size_t m; const uint64_t *gw = interner_get(&M.keys, join_value(L->flat, L->q), &m);
                    L->faces[L->kept] = gw[0]; L->terms[L->kept] = gw[1]; L->g = gw[0]; L->kept++; }
                FR_AWAIT(k, L->uni, F_FCJOINF, L->uni, L->g);
            }
            join_free(L->flat); L->flat = NULL;
            FR_AWAIT(k, r, F_FCENTF, chi, L->uni);
            if (r != 2) { wh_free(L); FR_FINISH(k, RV(result_invalid("type-family system has no branch along the whole composition line"))); }
            for (L->q = 0; L->q < L->kept; L->q++) {
                FR_AWAIT(k, r, F_FCENTF, chi, L->faces[L->q]);
                if (r == 2) { L->x = L->terms[L->q]; wh_free(L); goto forward_x; }
            }
            goto branchwise;
        }
        /* an introduction: the one fixed clause (§53–§54) */
        { uint64_t w[5] = { L->j, L->res->ref, L->phi, L->tube, L->cap }; FR_AWAIT(k, L->x, F_COMPCLAUSEF, interner_intern(&M.keys, w, 5, NULL), 0); }
        if (!L->x) FR_FINISH(k, RV(result_invalid("composition in a family whose head is not a type former or lacks its universe annotation")));
        goto forward_x;
    }
    die("whnf: unhandled head tag %d", (int)L->tag);

forward_x:
    FR_CALL(k, r, obs_sub(k, L->x, chi));
    FR_FINISH(k, r);

branchwise:
    /* demand each guarded term under χ ∧ φ_k; the join is enabled when every
     * box is full; the result is reconstructed in the original branch order */
    if (L->kept == 0) {
        wh_free(L);
        FR_CALL(k, r, creq(k, T_SYSTEM, 0, LEVELS_NONE, 0, NULL, 0, NULL));
        FR_FINISH(k, RV(result_system(r, 0, NULL, NULL)));
    }
    L->gath = join_new(k, L->kept);
    for (L->q = 0; L->q < L->kept; L->q++) {
        join_call(L->gath, L->q, obs_under(k, L->terms[L->q], chi, L->faces[L->q]));
        if (L->q + 1 < L->kept) FR_YIELD(k);
    }
    FR_JOIN(k, L->gath);
    /* a failure is selected by original branch order, independent of arrival order */
    for (L->q = 0; L->q < L->kept; L->q++) {
        L->res = RES(join_value(L->gath, L->q));
        if (L->res->cls == R_INVALID) { join_free(L->gath); wh_free(L); FR_FINISH(k, RV(L->res)); }
        if (L->res->cls == R_NO_OBSERVATION) { join_free(L->gath); wh_free(L); FR_FINISH(k, RV(result_invalid("branch under an inconsistent guard"))); }
        FR_YIELD(k);
    }
    /* nested system results are flattened under conjoined guards */
    /* flattening: the branch faces meet the inner faces — independent
     * demands, one join (counted first, one branch per step) */
    L->nfs = 0;
    for (L->q = 0; L->q < L->kept; L->q++) { L->res = RES(join_value(L->gath, L->q)); L->nfs += L->res->cls == R_SYSTEM ? L->res->nbr : 1; FR_YIELD(k); }
    L->res2 = result_system(0, L->nfs, NULL, NULL);           /* registered with the results: no leak if stuck */
    L->flat = join_new(k, L->nfs);
    L->m = 0;
    for (L->q = 0; L->q < L->kept; L->q++) {
        L->res = RES(join_value(L->gath, L->q));
        if (L->res->cls == R_SYSTEM) {
            for (L->a3 = 0; L->a3 < L->res->nbr; L->a3++) {
                join_request(L->flat, L->m, F_FCMEETF, L->faces[L->q], L->res->faces[L->a3]);
                L->res2->terms[L->m++] = L->res->terms[L->a3];
                FR_YIELD(k);
            }
        } else { join_fill(L->flat, L->m, L->faces[L->q]); L->res2->terms[L->m++] = L->res->ref; FR_YIELD(k); }
    }
    FR_JOIN(k, L->flat);
    /* the faces from the join and the system request, one branch per step */
    creq_head(&L->wb, T_SYSTEM, L->nfs, LEVELS_NONE, 2 * L->nfs);
    for (L->m = 0; L->m < L->nfs; L->m++) {
        L->res2->faces[L->m] = join_value(L->flat, L->m);
        creq_field(&L->wb, (Field){ F_FACE, NO_SLOT, L->res2->faces[L->m] }); creq_field(&L->wb, (Field){ F_REF, NO_SLOT, L->res2->terms[L->m] });
        FR_YIELD(k);
    }
    wordbuf_push(&L->wb, 0);
    join_free(L->flat); L->flat = NULL;
    join_free(L->gath); L->gath = NULL; wh_free(L);
    FR_CALL(k, r, creq_buf(k, &L->wb));
    L->res = L->res2; L->res->ref = r;
    FR_FINISH(k, RV(L->res));
    FR_END(k);
}

/* comp.branch: one branch of a type-family system under a composition —
 * its guard along the whole line ∀j.φ_k, dropped (0) when inconsistent with
 * χ, otherwise [∀j.φ_k, comp^j over the branch] */
static void cbranch_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_AWAIT(k, k->w[0], F_FCFORALLF, k->w[0], k->w[2]);
    FR_AWAIT(k, r, F_FCMEETF, k->w[3], k->w[0]);
    if (fc_is_false(r)) FR_FINISH(k, 0);
    {   uint64_t lv = k->w[7] == LEVELS_NONE ? LEVEL_NONE : levels_first(k->w[7]);
        Field f[4] = { { F_REF, 0, k->w[1] }, { F_FACE, NO_SLOT, k->w[4] }, { F_REF, 0, k->w[5] }, { F_REF, NO_SLOT, k->w[6] } };
        Binder b[1] = { { S_DIM, (DimVarId)k->w[2], NO_FIELD } };
        k->w[1] = (uint64_t)(uintptr_t)creq(k, T_COMP, 0, levels_pack(lv, LEVEL_NONE), 4, f, 1, b); }
    FR_CALL(k, r, (Cont *)(uintptr_t)k->w[1]);
    { uint64_t w[2] = { k->w[0], r }; FR_FINISH(k, interner_intern(&M.keys, w, 2, NULL)); }
    FR_END(k);
}

/* the evaluator family and its operand families (registered by eval_init) */
static void evaluator_init(void) {
    FAM[F_WHNF].name = "whnf"; FAM[F_WHNF].start = NULL; FAM[F_WHNF].resume = whnf_step;
    FAM[F_WHNF].loc_size = sizeof(WhLoc); FAM[F_WHNF].pure = false;
    F_OBS = family_define("whnf.observe", obs_step, 0, false); F_OBS_ = F_OBS;
    F_CREQ = family_define("construct.request", creq_step, sizeof(CrLoc), false);
    F_CBRANCH = family_define("whnf.comp_branch", cbranch_step, 0, false);
    F_FIELDF = family_lookup("field"); F_BINDERF = family_lookup("binder"); F_CONSTRUCTF = family_lookup("construct"); F_HEADF = family_lookup("head.annotation");
    F_FCENTF = family_lookup("fc.entails"); F_FCPROJF = family_lookup("fc.project"); F_FCMEETF = family_lookup("fc.meet");
    F_FCJOINF = family_lookup("fc.join"); F_FCFORALLF = family_lookup("fc.forall"); F_FCENDF = family_lookup("fc.endpoint");
    require(F_FIELDF && F_HEADF && F_FCENDF, "the evaluator's operand families are registered first");
}

static void evaluator_bind(void) {
    F_UNFOLDF = family_lookup("global.unfold"); F_COMPCLAUSEF = family_lookup("comp.clause");
    require(F_UNFOLDF && F_COMPCLAUSEF, "the evaluator's clause families are registered");
}

static void evaluate(EntryId eid) {
    Entry *e = ENT(eid);
    require(__atomic_fetch_add(&e->runs, 1, __ATOMIC_ACQ_REL) == 0, "a key is evaluated by exactly one task");
    Family f = eval_entry_family(eid);
    count_bump(&shard()->steps[f]);
    record_work(eid);
    if (FAM[f].start) FAM[f].start(eid, eval_entry_a(eid), eval_entry_b(eid));
    else {
        /* a frame family: its first step */
        Cont *k = frame_new(f, eid); k->w[0] = eval_entry_a(eid); k->w[1] = eval_entry_b(eid);
        Cont *sf = tl_step_frame; bool sk = tl_kept;
        tl_step_frame = k; tl_kept = false;
        FAM[f].resume(k, 0);
        bool kept = tl_kept;
        tl_step_frame = sf; tl_kept = sk;
        if (!kept) cont_release(k);
    }
}


static void resume(Cont *k, uint64_t v) {
    EvalResult *r = (EvalResult *)(uintptr_t)v;
    if (k->kind == K_FRAME) { FAM[k->fam].resume(k, v); return; }
    if (k->kind == K_ROOT) {
        RootBox *b = k->root;
        pthread_mutex_lock(&b->mu); b->result = v; b->done = true; pthread_cond_broadcast(&b->cv); pthread_mutex_unlock(&b->mu);
        /* wake clients waiting for either their root or quiescence */
        pthread_mutex_lock(&E.idle_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.idle_mu);
        rootbox_release(b);
        return;
    }
    if (k->kind == K_EXTERNAL) { k->ext_fn(k->ext_ctx, r); return; }
    if (k->kind == K_JOIN) { resume_join(k, v); return; }
    die("unreachable continuation kind");
}

/* one elementary frame step */
static void execute_job(Task t) {
    event(RD_STEP);
    if (t.kind == TK_EVAL) { evaluate(t.entry); return; }
    Cont *k = t.k;
    if (k->next) { Cont *rest = k->next; k->next = NULL; deliver(rest, t.v); }   /* hand the chain on: one delivery per job */
    if (k->kind == K_FRAME) { count_bump(&shard()->steps[k->fam]); if (k->owner) record_work(k->owner); }   /* a delivery to a root, join or external continuation belongs to no family (it is still a step of W) */
    Cont *sf = tl_step_frame; bool sk = tl_kept;
    tl_step_frame = k; tl_kept = false;
    resume(k, t.v);
    bool kept = tl_kept;
    tl_step_frame = sf; tl_kept = sk;
    if (!kept) cont_release(k);                    /* single consumer: released once resumed */
}
static void execute(Task t) {
    tl_in_job++; intern_in_step++;
    execute_job(t);
    tl_in_job--; intern_in_step--;
}


static void *worker_main(void *arg) {
    tl_worker = (size_t)(uintptr_t)arg;
    for (;;) {
        Task t;
        if (take_job(&t)) { execute(t); finish_job(); continue; }   /* all child jobs are enqueued before the job finishes */
        /* park: counted idle, every queue rechecked under idle_mu, so a push
         * that saw no idle worker is seen here */
        pthread_mutex_lock(&E.idle_mu);
        __atomic_add_fetch(&E.idle, 1, __ATOMIC_SEQ_CST);
        bool got = false;
        while (!E.stop && !(got = take_job(&t))) pthread_cond_wait(&E.work_cv, &E.idle_mu);
        __atomic_sub_fetch(&E.idle, 1, __ATOMIC_SEQ_CST);
        bool stop = E.stop && !got;
        pthread_mutex_unlock(&E.idle_mu);
        if (stop) break;
        execute(t); finish_job();
    }
    return NULL;
}

void eval_run(void) {
    if (E.nworkers) {
        /* wait until outstanding == 0 (no queued, reserved or executing job) */
        pthread_mutex_lock(&E.idle_mu);
        while (outstanding() > 0) pthread_cond_wait(&E.idle_cv, &E.idle_mu);
        pthread_mutex_unlock(&E.idle_mu);
        return;
    }
    for (;;) {
        Task t;
        if (!take_job(&t)) break;
        execute(t);
        finish_job();
    }
}

/* drive the queue until the root continuation of `box` is resumed, or the
 * machine is quiescent (a stuck demand); returns whether it was resumed */
static bool drive_root(RootBox *box, uint64_t *out) {
    if (E.nworkers) {
        /* wait for this root, or for quiescence of the whole machine (stuck) */
        pthread_mutex_lock(&E.idle_mu);
        for (;;) {
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            if (d || outstanding() == 0) break;
            pthread_cond_wait(&E.idle_cv, &E.idle_mu);
        }
        pthread_mutex_unlock(&E.idle_mu);
    } else {
        /* no pool: this client runs the queue; while another client thread
         * is still executing a job (its publication may resume this root, or
         * enqueue more work), wait for the root or for quiescence rather
         * than reporting a stuck demand */
        for (;;) {
            eval_run();
            pthread_mutex_lock(&E.idle_mu);
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            pthread_mutex_lock(&E.shared.mu); bool queued = E.shared.len > 0; pthread_mutex_unlock(&E.shared.mu);
            if (d || outstanding() == 0) { pthread_mutex_unlock(&E.idle_mu); break; }
            if (!queued) pthread_cond_wait(&E.idle_cv, &E.idle_mu);
            pthread_mutex_unlock(&E.idle_mu);
        }
    }
    pthread_mutex_lock(&box->mu);
    bool done = box->done; *out = box->result;
    pthread_mutex_unlock(&box->mu);
    /* a stuck root keeps its continuation as a waiter; the box survives
     * until that continuation is resumed or the machine is freed */
    rootbox_release(box);
    return done;
}

static RootBox *root_new(Cont **k, FaceId chi) {
    RootBox *box = calloc(1, sizeof *box); require(box, "out of memory");
    pthread_mutex_init(&box->mu, NULL); pthread_cond_init(&box->cv, NULL); box->refs = 2;
    *k = cont_new(K_ROOT, 0, chi);
    (*k)->root = box;
    return box;
}

/* outside jobs: run a detached frame (frame_new(f, 0)) to its value */
uint64_t frame_run(Cont *f, WhnfStatus *status) {
    require(!tl_in_job, "frame_run inside a counted step: the frame must be called");
    Cont *root; RootBox *box = root_new(&root, 0);
    frame_launch(f, root);
    uint64_t v = 0;
    bool done = drive_root(box, &v);
    if (status) *status = done ? W_OK : W_STUCK;
    return done ? v : 0;
}

/* a root driven for at most `budget` jobs (0: unlimited): an unfinished root
 * is reported stuck; its work stays queued (or running) and completes when a
 * later root drives the machine — nothing executed is discarded */
uint64_t family_run_budget(Family f, uint64_t a, uint64_t b, size_t budget, WhnfStatus *status) {
    if (!budget) return family_run(f, a, b, status);
    Cont *root; RootBox *box = root_new(&root, 0);
    family_request(f, a, b, root);
    uint64_t start = steps_now();
    if (E.nworkers) {
        for (;;) {
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            size_t out = outstanding();
            if (d || out == 0 || steps_now() - start >= budget) break;
            sched_yield();
        }
    } else {
        for (;;) {
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            if (d || steps_now() - start >= budget) break;
            Task t;
            bool got = take_job(&t);
            if (!got) break;
            execute(t); finish_job();
        }
    }
    pthread_mutex_lock(&box->mu); bool done = box->done; uint64_t v = box->result; pthread_mutex_unlock(&box->mu);
    rootbox_release(box);
    if (status) *status = done ? W_OK : W_STUCK;
    return done ? v : 0;
}

uint64_t family_run(Family f, uint64_t a, uint64_t b, WhnfStatus *status) {
    Cont *root; RootBox *box = root_new(&root, 0);
    family_request(f, a, b, root);
    uint64_t v = 0;
    bool done = drive_root(box, &v);
    if (status) *status = done ? W_OK : W_STUCK;
    return done ? v : 0;
}

EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status) { return whnf_pinned(t, chi, 0, status); }
EvalResult *whnf_pinned(RefId t, FaceId chi, PinSet P, WhnfStatus *status) {
    Cont *root; RootBox *box = root_new(&root, chi);
    eval_request_pinned(t, chi, P, root);
    uint64_t v = 0;
    bool done = drive_root(box, &v);
    EvalResult *out = (EvalResult *)(uintptr_t)v;
    if (!done) { if (status) *status = W_STUCK; return NULL; }
    if (status) {
        if (out->cls == R_NO_OBSERVATION) *status = W_NO_OBSERVATION;
        else if (out->cls == R_INVALID) *status = W_INVALID;
        else *status = W_OK;
    }
    return out;
}


void print_result(const EvalResult *r, FILE *f) {
    if (!r) { fprintf(f, "<pending>"); return; }
    switch (r->cls) {
    case R_INTRODUCTION: fprintf(f, "INTRO "); print_ref(r->ref, f); break;
    case R_NEUTRAL: fprintf(f, "NEUTRAL "); print_ref(r->ref, f); break;
    case R_SYSTEM:
        fprintf(f, "SYSTEM [");
        for (size_t i = 0; i < r->nbr; i++) { if (i) fprintf(f, ", "); fc_print(r->faces[i], f); fprintf(f, " ↦ "); print_ref(r->terms[i], f); }
        fprintf(f, "]");
        break;
    case R_NO_OBSERVATION: fprintf(f, "NO_OBSERVATION"); break;
    case R_INVALID: fprintf(f, "INVALID(%s)", r->message ? r->message : ""); break;
    }
}

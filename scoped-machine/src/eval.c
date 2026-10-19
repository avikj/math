#include "eval.h"
#include "lib.h"
#include "pool.h"
#include "pins.h"
#include "judge.h"
#include "chain.h"
#include "effect.h"
#include "proof.h"
#include <sched.h>

/* ---------------- jobs, families, the evaluator state ---------------- */

#define ENTRY_READY ((Cont *)(uintptr_t)1)
#define ENTRY_LAUNCHED ((Cont *)(uintptr_t)2)    /* R(∅): the producer runs, nobody waits yet */

/* a job: EVALUATE(entry); RESUME(k, v) — whose k may head a delivery chain of
 * a published entry, of which each job delivers exactly one */
typedef enum { TK_EVAL = 0, TK_RESUME } TaskKind;
typedef struct { TaskKind kind; EntryId entry; Cont *k; uint64_t v; } Task;

/* the ready-job multiset: a linked list of fixed-size chunks; push, pop at
 * either end are each O(1) */
#define QCHUNK 254
typedef struct QChunk { struct QChunk *prev, *next; uint32_t lo, hi; Task t[QCHUNK]; } QChunk;
typedef struct { pthread_mutex_t mu; QChunk *front, *back; size_t len; } Queue;

typedef struct { const char *name; FamResume resume; size_t loc_size; } FamilyDef;
static FamilyDef FAM[F_MAX];
static size_t n_fam = F_FIXED;     /* families defined at run time (tests) follow the fixed ids */
static uint64_t obs_key(FaceId eta, PinSet P) { uint64_t w[2] = { eta, P }; return interner_intern(&M.keys, w, 2, NULL); }
static FaceId key_face(uint64_t b) { size_t n; return interner_get(&M.keys, b, &n)[0]; }
static PinSet key_pins(uint64_t b) { size_t n; return interner_get(&M.keys, b, &n)[1]; }

typedef struct Shard Shard;
static struct {
    Interner keys;                 /* (family, a, b) → EntryId */
    Chunked entries;               /* Entry per EntryId-1, non-moving, zero = U */
    Queue shared;                  /* jobs pushed by threads outside the pool */
    Queue *wq;                     /* one per worker: its own pushes, taken back first */
    size_t outstanding;            /* §35: queued + executing jobs (+ reserved launches); atomic */
    pthread_mutex_t idle_mu; pthread_cond_t work_cv, idle_cv;
    size_t idle; bool stop;        /* parked workers; pool shutdown (under idle_mu) */
    size_t hosts_waiting;          /* root drivers asleep on idle_cv (no pool: a push must wake them) */
    pthread_t *workers; size_t nworkers;
    Pool cont_pool, chunk_pool, dep_pool;
    Pool loc_pool[F_MAX];          /* frame locals records, per family */
    Shard *shards;                 /* readings: pushed by CAS, one per thread */
    uint64_t epoch;                /* this lifetime (0: no evaluator) */
} E;

/* ---------------- readings ----------------
 * A shard is written by its one thread only: the protocol events and the
 * steps per family that thread executed (exact counts). A reading sums the
 * shards' snapshots; no counter is shared between writers. */
struct Shard { Shard *next; Count ev[RD_STEPS]; Count steps[F_MAX]; };
static uint64_t eval_epochs;
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
static Entry *ENT(EntryId e) { return (Entry *)chunked_at(&E.entries, e - 1); }
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
        for (DepNode *d = __atomic_load_n(&e->deps, __ATOMIC_ACQUIRE); d; d = d->next)
            if (d->e <= ne && !seen[d->e]) { seen[d->e] = true; stk[sp++] = d->e; }
    }
    free(seen); free(stk);
    if (support) *support = cnt;
}
void eval_reading(Reading r, Family f, Exact *out) {
    require(r <= RD_STEPS && (r != RD_STEPS || (f >= 1 && f < F_MAX)), "bad reading");
    for (Shard *s = __atomic_load_n(&E.shards, __ATOMIC_ACQUIRE); s; s = s->next) exact_add_count(out, r == RD_STEPS ? &s->steps[f] : &s->ev[r]);
}

/* ---------------- families ----------------
 * Defined once per process at their ids (families.h): their code is static;
 * the evaluator of each machine makes their locals pools. */
static void family_set(Family f, const char *name, FamResume step, size_t loc_size) {
    require(f >= 1 && f < F_MAX && !FAM[f].resume, "family %s defined twice or out of range", name);
    FAM[f].name = name; FAM[f].resume = step; FAM[f].loc_size = loc_size;
    if (E.epoch && loc_size) pool_init(&E.loc_pool[f], loc_size);       /* defined while an evaluator lives */
}
void family_define(Family f, const char *name, FamResume step, size_t loc_size) {
    require(f < F_FIXED, "a fixed family id");
    family_set(f, name, step, loc_size);
}
Family family_new(const char *name, FamResume step, size_t loc_size) {
    Family f = (Family)__atomic_fetch_add(&n_fam, 1, __ATOMIC_RELAXED);
    family_set(f, name, step, loc_size);
    return f;
}

static void *worker_main(void *arg);
static void q_init(Queue *q); static size_t q_push(Queue *q, Task t); static bool q_take(Queue *q, bool back, Task *out); static void q_free(Queue *q);
static size_t outstanding(void);
static void evaluator_init(void);
static void intern_families_init(void);

static pthread_once_t families_once = PTHREAD_ONCE_INIT;
static void families_define(void) {
    intern_families_init();
    dnf_families_init();
    subst_families_init();
    construct_families_init();
    scope_families_init();
    template_families_init();
    evaluator_init();
    lib_families_init();
    pins_families_init();
    judge_families_init();
    proof_families_init();
    chain_families_init();
    effect_families_init();
}

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
    pool_init(&E.dep_pool, sizeof(DepNode));
    pthread_once(&families_once, families_define);
    for (size_t f = 1; f < F_MAX; f++) if (FAM[f].loc_size) pool_init(&E.loc_pool[f], FAM[f].loc_size);
    E.epoch = __atomic_add_fetch(&eval_epochs, 1, __ATOMIC_RELAXED);
    effect_state_init();
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

static const uint64_t *entry_key(EntryId e) { size_t n; return interner_get(&E.keys, e, &n); }
Family eval_entry_family(EntryId e) { return (Family)entry_key(e)[0]; }
uint64_t eval_entry_a(EntryId e) { return entry_key(e)[1]; }
uint64_t eval_entry_b(EntryId e) { return entry_key(e)[2]; }

/* Teardown: every frame, waiter, dependency node and queued job lives in a
 * pool of this lifetime and every value in the machine's tables, so the
 * pools are destroyed whole; a suspended frame owns nothing else (its word
 * buffers' pages belong to the process page pool). */
void eval_free(void) {
    stop_workers();
    effect_state_free();
    for (Shard *s = E.shards, *n; s; s = n) {
        n = s->next;
        for (size_t r = 0; r < RD_STEPS; r++) count_free(&s->ev[r]);
        for (size_t f = 0; f < F_MAX; f++) count_free(&s->steps[f]);
        free(s);
    }
    size_t ne = interner_count(&E.keys);
    for (size_t i = 0; i < ne; i++) { Entry *e = chunked_peek(&E.entries, i); if (e) count_free(&e->work); }
    interner_free(&E.keys);
    chunked_free(&E.entries);
    { Task t; while (q_take(&E.shared, false, &t)) {} }
    pool_destroy(&E.cont_pool); pool_destroy(&E.chunk_pool); pool_destroy(&E.dep_pool);
    for (size_t f = 0; f < F_MAX; f++) if (E.loc_pool[f].size) pool_destroy(&E.loc_pool[f]);
    q_free(&E.shared);
    pthread_mutex_destroy(&E.idle_mu);
    pthread_cond_destroy(&E.work_cv); pthread_cond_destroy(&E.idle_cv);
    memset(&E, 0, sizeof E);
}

Cont *frame_new(Family f, EntryId dest);
Cont *frame_new(Family f, EntryId dest) {
    Cont *k = pool_alloc(&E.cont_pool);
    k->fam = f; k->dest = dest; k->owner = dest;
    if (FAM[f].loc_size) k->loc = pool_alloc(&E.loc_pool[f]);
    return k;
}
static void cont_release(Cont *k) {
    if (k->loc) pool_free(&E.loc_pool[k->fam], k->loc);
    pool_free(&E.cont_pool, k);
}
Cont *frame_sub(Family f, const Cont *caller) {
    require(f > F_WHNF && f < F_MAX && FAM[f].resume, "a subroutine is a frame family");
    Cont *k = frame_new(f, 0); k->owner = caller ? caller->owner : 0;
    return k;
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
static void notify_hosts(void);
static void push_job(Task t) {
    size_t w = tl_worker;
    size_t n = q_push(w ? &E.wq[w - 1] : &E.shared, t);
    if (!w || n > 1) wake_one();
    if (!E.nworkers && __atomic_load_n(&E.hosts_waiting, __ATOMIC_SEQ_CST)) notify_hosts();   /* without a pool the root drivers run the jobs */
}

/* §35 quiescence protocol: outstanding = queued + executing. A launch
 * reserves its job (outstanding += 1) before the key can be observed
 * RUNNING, so no observer can see a running key with outstanding == 0. */
static void reserve_job(void) { __atomic_add_fetch(&E.outstanding, 1, __ATOMIC_SEQ_CST); }
static size_t outstanding(void) { return __atomic_load_n(&E.outstanding, __ATOMIC_SEQ_CST); }
static void notify_hosts(void) { pthread_mutex_lock(&E.idle_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.idle_mu); }
static void finish_job(void) {
    size_t was = __atomic_fetch_sub(&E.outstanding, 1, __ATOMIC_SEQ_CST);
    require(was > 0, "finish without outstanding job");
    if (was == 1) notify_hosts();
}
static void enqueue(Task t) { reserve_job(); push_job(t); }

/* one delivery: the RESUME job of k (DELIVER is counted here; the resumed
 * step is counted when the RESUME job executes) */
static void deliver(Cont *k, uint64_t v) {
    event(RD_DELIVER);
    Task t; memset(&t, 0, sizeof t); t.kind = TK_RESUME; t.k = k; t.v = v;
    enqueue(t);
}

/* ---------------- entries ---------------- */

static EntryId entry_intern(Family f, uint64_t a, uint64_t b) {
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
static void publish(EntryId eid, uint64_t v) {
    Entry *e = ENT(eid);
    __atomic_store_n(&e->value, v, __ATOMIC_RELEASE);
    Cont *w = __atomic_exchange_n(&e->head, ENTRY_READY, __ATOMIC_ACQ_REL);
    require(w != NULL && w != ENTRY_READY, "publish into an entry that is not running");
    event(RD_PUBLISH);
    if (w != ENTRY_LAUNCHED) deliver(w, v);
}

/* the producer's ledger: its requests and its steps, written by its one
 * running frame (frames of one producer never run concurrently) */
static void record_dep(EntryId owner, EntryId eid) {
    Entry *o = ENT(owner);
    DepNode *d = pool_alloc(&E.dep_pool);
    d->e = eid; d->next = o->deps;
    __atomic_store_n(&o->deps, d, __ATOMIC_RELEASE);
}
static void record_work(EntryId owner) { count_bump(&ENT(owner)->work); }

/* REQ(K,c): U → R({c}) + EVAL(K), R(W) → R(W ⊎ {c}), D(v) → D(v) + DELIVER(c,v);
 * c = NULL is a launch: U → R(∅) + EVAL(K), otherwise nothing. A failed CAS
 * means another request launched, pushed onto or published this entry in
 * between: each failure is charged to that success. Strong CAS only. */
static void request_entry(EntryId eid, Cont *k, EntryId owner) {
    Entry *e = ENT(eid);
    event(RD_REQUEST);
    if (owner) record_dep(owner, eid);
    for (;;) {
        Cont *h = __atomic_load_n(&e->head, __ATOMIC_ACQUIRE);
        if (h == ENTRY_READY) {
            if (!k) return;
            k->next = NULL;
            deliver(k, __atomic_load_n(&e->value, __ATOMIC_ACQUIRE));
            return;
        }
        if (h == NULL) {
            reserve_job();                  /* the launch is reserved before RUNNING can be observed */
            Cont *mine = k ? k : ENTRY_LAUNCHED;
            if (k) k->next = NULL;
            if (__atomic_compare_exchange_n(&e->head, &h, mine, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                event(RD_LAUNCH);
                Task job; memset(&job, 0, sizeof job); job.kind = TK_EVAL; job.entry = eid;
                push_job(job);
                return;
            }
            finish_job();                   /* not the launcher: give the reservation back */
            continue;
        }
        if (!k) return;                     /* running: a launch has nothing to add */
        k->next = h == ENTRY_LAUNCHED ? NULL : h;
        if (__atomic_compare_exchange_n(&e->head, &h, k, false, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE)) return;
    }
}

/* ---------------- frame programs ----------------
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
    require(f >= F_WHNF && f < F_MAX && FAM[f].resume, "unregistered family");
    keep_frame(k);
    request_entry(entry_intern(f, a, b), k, k->owner);
}
void family_launch(Family f, uint64_t a, uint64_t b) {
    require(tl_step_frame, "a launch is made by a frame's step");
    require(f >= F_WHNF && f < F_MAX && FAM[f].resume, "unregistered family");
    request_entry(entry_intern(f, a, b), NULL, tl_step_frame->owner);
}
void frame_call(Cont *k, Cont *child) {
    require(child->dest == 0, "a subroutine frame of this caller");
    child->parent = k; keep_frame(k);
    enqueue_resume(child, 0);
}
void frame_yield(Cont *k) {
    keep_frame(k);
    enqueue_resume(k, 0);
}
void frame_finish(Cont *k, uint64_t v) {
    if (k->parent) { Cont *p = k->parent; k->parent = NULL; enqueue_resume(p, v); return; }
    if (k->dest) publish(k->dest, v);
}

/* the host frame: the waiter by which a root's publication reaches the
 * outside caller (its one step wakes the hosts waiting for their roots) */
static void host_step(Cont *k, uint64_t v) { (void)k; (void)v; notify_hosts(); }

/* the interning subroutine: a bounded advance of the insertion per step */
#define INTERN_BUDGET 8
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
    { uint64_t id = interner_flat_of(L->t, L->root); if (id) FR_FINISH(k, id); }
    {   size_t m; const uint64_t *rw = interner_tree_get(L->t, L->root, &m);
        require(m == 3 && rw[0] == TREE_ROOT, "intern.flatten of a non-root");
        L->n = rw[1]; L->stk[0] = rw[2]; L->pos[0] = 0; L->sp = 1; }
    L->dst = interner_flat_reserve(L->t, L->n); L->at = 0;
    while (L->sp > 0) {
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
    family_define(F_INTERN, "intern", intern_step, sizeof(InternState));
    family_define(F_FLATTEN, "intern.flatten", flatten_step, sizeof(FlatLoc));
    family_define(F_HOST, "host", host_step, 0);
    interner_set_flatten_hook(flatten_root);
}

/* ---------------- execution ---------------- */
static void step_frame(Cont *k, uint64_t v) {
    Cont *sf = tl_step_frame; bool sk = tl_kept;
    tl_step_frame = k; tl_kept = false;
    FAM[k->fam].resume(k, v);
    bool kept = tl_kept;
    tl_step_frame = sf; tl_kept = sk;
    if (!kept) cont_release(k);                    /* single consumer: released once resumed */
}
static void evaluate(EntryId eid) {
    Entry *e = ENT(eid);
    require(__atomic_fetch_add(&e->runs, 1, __ATOMIC_ACQ_REL) == 0, "a key is evaluated by exactly one task");
    Family f = eval_entry_family(eid);
    count_bump(&shard()->steps[f]);
    record_work(eid);
    Cont *k = frame_new(f, eid); k->w[0] = eval_entry_a(eid); k->w[1] = eval_entry_b(eid);
    step_frame(k, 0);
}
static void execute_job(Task t) {
    event(RD_STEP);
    if (t.kind == TK_EVAL) { evaluate(t.entry); return; }
    Cont *k = t.k;
    if (k->next) { Cont *rest = k->next; k->next = NULL; deliver(rest, t.v); }   /* hand the chain on: one delivery per job */
    count_bump(&shard()->steps[k->fam]);
    if (k->owner) record_work(k->owner);
    step_frame(k, t.v);
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
        if (take_job(&t)) { execute(t); finish_job(); continue; }
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
        pthread_mutex_lock(&E.idle_mu);
        while (outstanding() > 0) pthread_cond_wait(&E.idle_cv, &E.idle_mu);
        pthread_mutex_unlock(&E.idle_mu);
        return;
    }
    for (;;) { Task t; if (!take_job(&t)) break; execute(t); finish_job(); }
}

/* ---------------- roots ----------------
 * A root is requested with a host frame as its waiter; the caller drives
 * (or, with a pool, waits) until the entry is READY or the machine is
 * quiescent (a stuck demand). With W > 0 the wait also ends when the work
 * of the root's dependency support exceeds the budget. */
static uint64_t support_work(EntryId e) {
    Exact x = { 0, NULL }; uint64_t w;
    eval_work(1, &e, &x, NULL);
    if (!exact_to_u64(&x, &w)) w = UINT64_MAX;
    exact_free(&x);
    return w;
}
static bool ready(EntryId e) { return eval_entry_state(e) == E_READY; }
static uint64_t drive(EntryId e, size_t budget, WhnfStatus *status) {
    require(!tl_in_job, "root driving inside a counted step: the frame must await it");
    request_entry(e, frame_new(F_HOST, 0), 0);
    size_t next_check = budget;                    /* W grows by at most one per executed job */
    for (;;) {
        if (ready(e)) break;
        if (budget && next_check == 0) {
            uint64_t w = support_work(e);
            if (w > budget) break;
            next_check = budget - (size_t)w + 1;
        }
        if (!E.nworkers) {
            Task t;
            if (take_job(&t)) { execute(t); finish_job(); if (next_check) next_check--; continue; }
        }
        /* nothing to run here: wait for a host notification (a root's
         * publication, or quiescence); with a budget, wake periodically */
        pthread_mutex_lock(&E.idle_mu);
        __atomic_add_fetch(&E.hosts_waiting, 1, __ATOMIC_SEQ_CST);
        bool queued = false;
        if (!E.nworkers) { pthread_mutex_lock(&E.shared.mu); queued = E.shared.len > 0; pthread_mutex_unlock(&E.shared.mu); }
        if (ready(e) || outstanding() == 0) { __atomic_sub_fetch(&E.hosts_waiting, 1, __ATOMIC_SEQ_CST); pthread_mutex_unlock(&E.idle_mu); break; }
        if (!queued) {
            if (budget) {
                struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts);
                ts.tv_nsec += 1000000; if (ts.tv_nsec >= 1000000000) { ts.tv_sec++; ts.tv_nsec -= 1000000000; }
                pthread_cond_timedwait(&E.idle_cv, &E.idle_mu, &ts);
                next_check = 0;
            } else pthread_cond_wait(&E.idle_cv, &E.idle_mu);
        }
        __atomic_sub_fetch(&E.hosts_waiting, 1, __ATOMIC_SEQ_CST);
        pthread_mutex_unlock(&E.idle_mu);
    }
    bool done = ready(e) && (!budget || support_work(e) <= budget);
    if (status) *status = done ? W_OK : W_STUCK;
    return done ? __atomic_load_n(&ENT(e)->value, __ATOMIC_ACQUIRE) : 0;
}
uint64_t family_run(Family f, uint64_t a, uint64_t b, WhnfStatus *status) {
    require(f >= F_WHNF && f < F_MAX && FAM[f].resume, "unregistered family");
    return drive(entry_intern(f, a, b), 0, status);
}
uint64_t family_run_budget(Family f, uint64_t a, uint64_t b, size_t budget, WhnfStatus *status) {
    require(f >= F_WHNF && f < F_MAX && FAM[f].resume, "unregistered family");
    return drive(entry_intern(f, a, b), budget, status);
}
uint64_t family_call(Family f, uint64_t a, uint64_t b) {
    require(!tl_in_job, "synchronous request of %s inside a counted step: the frame must await it", f < F_MAX ? FAM[f].name : "?");
    WhnfStatus st;
    uint64_t v = family_run(f, a, b, &st);
    require(st == W_OK, "synchronous request of %s did not complete (an unresolved dependency)", FAM[f].name);
    return v;
}

/* ---------------- results ---------------- */
static uint64_t res_rec(ResultClass c, RefId ref, const char *msg) { uint64_t w[3] = { c, ref, (uint64_t)(uintptr_t)msg }; return interner_intern(&M.keys, w, 3, NULL); }
EvalResult res_get(uint64_t v) {
    size_t n; const uint64_t *w = interner_get(&M.keys, v, &n);
    require(n >= 3 && (n - 3) % 2 == 0 && w[0] >= R_INTRODUCTION && w[0] <= R_INVALID, "not a result record");
    EvalResult r = { (ResultClass)w[0], w[n - 2], (n - 3) / 2, w + 1, (const char *)(uintptr_t)w[n - 1] };
    return r;
}

/* ---------------- the evaluator ----------------
 * WHNF(t, [χ, P]) (χ projected to t's support) is a frame family like every
 * other: each step does a constant amount of work and awaits its operands
 * from their families (fields, binder application, face tests, projections,
 * constructions) and its sub-observations from the observation family. A
 * branchwise result launches its independent children (one per step) and
 * then awaits each in branch order (§12, §26). */
static uint64_t binder_rec(Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) { uint64_t e[4] = { sort, slot, field, image }; return interner_intern(&M.keys, e, 4, NULL); }
static uint64_t rq3(uint64_t a, uint64_t b, uint64_t c) { uint64_t w[3] = { a, b, c }; return interner_intern(&M.keys, w, 3, NULL); }
uint64_t observe_key(FaceId chi, FaceId phi, uint64_t pins) { require(pins, "an observation is bound to a pin set"); return rq3(chi, phi, pins); }

/* a construction request (construct.c) made by the evaluator: no declared
 * face. The request record is built into a word buffer and interned by the
 * stepped subroutine; the subroutine then awaits the construction. */
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
    FR_AWAIT(k, r, F_CONSTRUCT, L->id, 0);
    FR_FINISH(k, r);
    FR_END(k);
}
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
Cont *construct_sub(const Cont *caller, Tag tag, uint64_t payload, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b) { return creq(caller, tag, payload, levels, nf, f, nb, b); }

/* observe(x, [χ, φ, P]): no observation on the false face; an invalid
 * occurrence outside x's required face; otherwise WHNF(x, [π_S(x) χ, P]) */
static void obs_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    RefId x = k->w[0];
    FR_BEGIN(k);
    {   size_t n; const uint64_t *q = interner_get(&M.keys, k->w[1], &n); k->w[2] = q[0]; k->w[3] = q[1]; k->w[4] = q[2]; }
    if (k->w[3]) { FR_AWAIT(k, r, F_FCMEET, k->w[2], k->w[3]); k->w[2] = r; }
    if (fc_is_false(k->w[2])) FR_FINISH(k, res_rec(R_NO_OBSERVATION, x, NULL));
    FR_AWAIT(k, r, F_FCENT, k->w[2], ref_required(x));
    if (r != 2) FR_FINISH(k, res_rec(R_INVALID, 0, "occurrence outside its required face"));
    FR_AWAIT(k, r, F_FCPROJ, k->w[2], ref_support(x));
    FR_AWAIT(k, r, F_WHNF, x, obs_key(r, k->w[4]));
    FR_FINISH(k, r);
    FR_END(k);
}

static bool intro_tag(Tag t) { return t == T_UNIVERSE || t == T_PI || t == T_SIGMA || t == T_LAM || t == T_PAIR || t == T_PATH || t == T_PLAM; }
static bool elim_tag(Tag t) { return t == T_APP || t == T_FST || t == T_SND || t == T_PAPP || t == T_UNGLUE; }

/* whnf.distribute(t, b): the eliminator t rebuilt around b, a branch of its
 * scrutinee's system (its shared operands are t's fields, awaited from their
 * keyed families) */
typedef struct { uint64_t levels, j, fam, a1, a3, a4, tube; } DiLoc;
static void dist_step(Cont *k, uint64_t v) {
    DiLoc *L = FR_LOC(k, DiLoc);
    RefId t = k->w[0], bt = k->w[1];
    Tag tag = ref_tag(t);
    uint64_t r = 0;
    FR_BEGIN(k);
    if (tag == T_APP) {
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        { Field f[2] = { { F_REF, NO_SLOT, bt }, { F_REF, NO_SLOT, L->a1 } }; FR_CALL(k, r, creq(k, T_APP, 0, LEVELS_NONE, 2, f, 0, NULL)); }
        FR_FINISH(k, r);
    }
    if (tag == T_FST || tag == T_SND) {
        { Field f[1] = { { F_REF, NO_SLOT, bt } }; FR_CALL(k, r, creq(k, tag, 0, LEVELS_NONE, 1, f, 0, NULL)); }
        FR_FINISH(k, r);
    }
    FR_AWAIT(k, L->levels, F_HEAD, t, 1);
    if (tag == T_PAPP) {
        L->j = binder_dim_var(t, 0);
        FR_AWAIT(k, L->fam, F_BINDER, t, binder_rec(S_DIM, 0, 0, iv_var(L->j)));
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, L->a3, F_FIELD, t, 2);
        FR_AWAIT(k, L->a4, F_FIELD, t, 4);
        {   Field f[5] = { { F_REF, 0, L->fam }, { F_REF, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, bt }, { F_INTERVAL, NO_SLOT, L->a4 } };
            Binder b[1] = { { S_DIM, L->j, NO_FIELD } };
            FR_CALL(k, r, creq(k, T_PAPP, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 1, b)); }
        FR_FINISH(k, r);
    }
    require(tag == T_UNGLUE, "whnf.distribute of a non-eliminator");
    FR_AWAIT(k, L->fam, F_FIELD, t, 0);
    FR_AWAIT(k, L->a1, F_FIELD, t, 1);
    FR_AWAIT(k, L->a3, F_FIELD, t, 2);
    FR_AWAIT(k, L->tube, F_FIELD, t, 3);
    {   Field f[5] = { { F_REF, NO_SLOT, L->fam }, { F_FACE, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, L->tube }, { F_REF, NO_SLOT, bt } };
        FR_CALL(k, r, creq(k, T_UNGLUE, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 0, NULL)); }
    FR_FINISH(k, r);
    FR_END(k);
}

/* whnf.comp_branch(t, [g, b, χ]): one branch g ↦ b of the type-family system
 * of the composition t — its guard along the whole line ∀j.g, dropped (0)
 * when inconsistent with χ, otherwise [∀j.g, comp^j over the branch] */
typedef struct { uint64_t j, g, phi, tube, cap, levels; } CbLoc;
static void cbranch_step(Cont *k, uint64_t v) {
    CbLoc *L = FR_LOC(k, CbLoc);
    RefId t = k->w[0];
    uint64_t r = 0;
    FR_BEGIN(k);
    {   size_t n; const uint64_t *q = interner_get(&M.keys, k->w[1], &n); k->w[2] = q[0]; k->w[3] = q[1]; k->w[4] = q[2]; }
    L->j = binder_dim_var(t, 0);
    FR_AWAIT(k, L->g, F_FCFORALL, k->w[2], L->j);
    FR_AWAIT(k, r, F_FCMEET, k->w[4], L->g);
    if (fc_is_false(r)) FR_FINISH(k, 0);
    FR_AWAIT(k, L->phi, F_FIELD, t, 1);
    FR_AWAIT(k, L->tube, F_BINDER, t, binder_rec(S_DIM, 0, 2, iv_var(L->j)));
    FR_AWAIT(k, L->cap, F_FIELD, t, 3);
    FR_AWAIT(k, L->levels, F_HEAD, t, 1);
    {   uint64_t lv = L->levels == LEVELS_NONE ? LEVEL_NONE : levels_first(L->levels);
        Field f[4] = { { F_REF, 0, k->w[3] }, { F_FACE, NO_SLOT, L->phi }, { F_REF, 0, L->tube }, { F_REF, NO_SLOT, L->cap } };
        Binder b[1] = { { S_DIM, (DimVarId)L->j, NO_FIELD } };
        FR_CALL(k, r, creq(k, T_COMP, 0, levels_pack(lv, LEVEL_NONE), 4, f, 1, b)); }
    {   uint64_t w[2] = { L->g, r }; FR_FINISH(k, interner_intern(&M.keys, w, 2, NULL)); }
    FR_END(k);
}

typedef struct {
    Tag tag; uint64_t levels, payload, a1, a4, x, res, sys, uni, g, j, fam, tube, cap, phi, fail, mf;
    size_t n, q, a, kept, nfs; WordBuf wb, wc; bool created;
} WhLoc;
#define RES(id) res_get(id)
static uint64_t sys_face(uint64_t sys, size_t q) { size_t n; return interner_get(&M.keys, sys, &n)[2 * q]; }
static uint64_t sys_term(uint64_t sys, size_t q) { size_t n; return interner_get(&M.keys, sys, &n)[2 * q + 1]; }

static void whnf_step(Cont *k, uint64_t v) {
    WhLoc *L = FR_LOC(k, WhLoc);
    RefId t = k->w[0]; FaceId chi = key_face(k->w[1]); PinSet P = key_pins(k->w[1]);
    uint64_t r = 0;
    FR_BEGIN(k);
    if (ref_is_var(t)) FR_FINISH(k, res_rec(R_NEUTRAL, t, NULL));
    L->tag = ref_tag(t);
    if (intro_tag(L->tag)) FR_FINISH(k, res_rec(R_INTRODUCTION, t, NULL));

    if (L->tag == T_GLOBAL) {
        /* a declared symbol without a body is an opaque constant: neutral;
         * the revision this observation is bound to */
        FR_AWAIT(k, L->payload, F_HEAD, t, 0);
        FR_AWAIT(k, r, F_LOOKUP, P, L->payload);
        if (!r) FR_FINISH(k, res_rec(R_INVALID, 0, "a symbol outside the observation's premises"));
        L->a1 = subst_value(P, r - 1);
        if (!L->a1) FR_FINISH(k, res_rec(R_NEUTRAL, t, NULL));
        FR_AWAIT(k, L->x, F_UNFOLD, t, L->a1);
        goto forward_x;
    }

    if (L->tag == T_GLUE_TYPE || L->tag == T_GLUE_INTRO) {
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, r, F_FCENT, chi, L->a1);
        if (r != 2) FR_FINISH(k, res_rec(R_INTRODUCTION, t, NULL));
        FR_AWAIT(k, L->x, F_FIELD, t, L->tag == T_GLUE_TYPE ? 2 : 4);
        goto forward_x;
    }

    if (elim_tag(L->tag)) {
        if (L->tag == T_PAPP) {
            FR_AWAIT(k, L->a4, F_FIELD, t, 4);
            FR_AWAIT(k, r, F_FCEND, L->a4, 0);
            FR_AWAIT(k, r, F_FCENT, chi, r);
            if (r == 2) { FR_AWAIT(k, L->x, F_FIELD, t, 1); goto forward_x; }
            FR_AWAIT(k, r, F_FCEND, L->a4, 1);
            FR_AWAIT(k, r, F_FCENT, chi, r);
            if (r == 2) { FR_AWAIT(k, L->x, F_FIELD, t, 2); goto forward_x; }
            FR_AWAIT(k, L->x, F_FIELD, t, 3);
        } else if (L->tag == T_UNGLUE) {
            FR_AWAIT(k, L->a1, F_FIELD, t, 1);
            FR_AWAIT(k, r, F_FCENT, chi, L->a1);
            if (r == 2) {
                /* on the Glue face: (fst e) v */
                FR_AWAIT(k, L->x, F_FIELD, t, 3);
                FR_AWAIT(k, L->a4, F_FIELD, t, 4);
                { Field f[1] = { { F_REF, NO_SLOT, L->x } }; FR_CALL(k, L->x, creq(k, T_FST, 0, LEVELS_NONE, 1, f, 0, NULL)); }
                { Field f[2] = { { F_REF, NO_SLOT, L->x }, { F_REF, NO_SLOT, L->a4 } }; FR_CALL(k, L->x, creq(k, T_APP, 0, LEVELS_NONE, 2, f, 0, NULL)); }
                goto forward_x;
            }
            FR_AWAIT(k, L->x, F_FIELD, t, 4);
        } else FR_AWAIT(k, L->x, F_FIELD, t, 0);
        /* the scrutinee */
        FR_AWAIT(k, L->res, F_OBS, L->x, observe_key(chi, 0, P));
        if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, L->res);
        if (RES(L->res).cls == R_NEUTRAL) FR_FINISH(k, res_rec(R_NEUTRAL, t, NULL));
        if (RES(L->res).cls == R_SYSTEM) {
            /* distribute: the eliminator rebuilt around each branch, launched
             * one per step, then awaited in branch order */
            L->n = RES(L->res).nbr;
            for (L->q = 0; L->q < L->n; L->q++) { family_launch(F_DIST, t, RES(L->res).br[2 * L->q + 1]); FR_YIELD(k); }
            wordbuf_init(&L->wb);
            for (L->q = 0; L->q < L->n; L->q++) {
                wordbuf_push(&L->wb, RES(L->res).br[2 * L->q]);
                FR_AWAIT(k, r, F_DIST, t, RES(L->res).br[2 * L->q + 1]);
                wordbuf_push(&L->wb, r);
            }
            FR_CALL(k, L->sys, intern_sub(k, &M.keys, &L->wb, &L->created));
            L->kept = L->n;
            goto branchwise;
        }
        /* an introduction under the eliminator */
        {   Tag ht = ref_tag(RES(L->res).ref);
            if (L->tag == T_APP && ht != T_LAM) FR_FINISH(k, res_rec(R_INVALID, 0, "application of a non-function introduction"));
            if ((L->tag == T_FST || L->tag == T_SND) && ht != T_PAIR) FR_FINISH(k, res_rec(R_INVALID, 0, "projection of a non-pair introduction"));
            if (L->tag == T_PAPP && ht != T_PLAM) FR_FINISH(k, res_rec(R_INVALID, 0, "path application of a non-path introduction"));
            if (L->tag == T_UNGLUE && ht != T_GLUE_INTRO) FR_FINISH(k, res_rec(R_INVALID, 0, "unglue of a non-glue introduction")); }
        if (L->tag == T_APP) {
            FR_AWAIT(k, L->a1, F_FIELD, t, 1);
            FR_AWAIT(k, L->x, F_BINDER, RES(L->res).ref, binder_rec(S_TERM, 0, 1, L->a1));
        } else if (L->tag == T_PAPP) FR_AWAIT(k, L->x, F_BINDER, RES(L->res).ref, binder_rec(S_DIM, 0, 0, L->a4));
        else FR_AWAIT(k, L->x, F_FIELD, RES(L->res).ref, L->tag == T_FST ? 0 : L->tag == T_SND ? 1 : 5);
        goto forward_x;
    }

    if (L->tag == T_SYSTEM) {
        /* the covered, consistent branches; a branch entailed by χ is the value */
        L->n = tnode_nfields(ref_tnode(t)) / 2;
        wordbuf_init(&L->wb); wordbuf_push(&L->wb, R_SYSTEM);
        L->uni = fc_false();
        for (L->q = 0; L->q < L->n; L->q++) {
            FR_AWAIT(k, L->phi, F_FIELD, t, 2 * L->q);
            FR_AWAIT(k, r, F_FCMEET, chi, L->phi);
            if (fc_is_false(r)) continue;                       /* inconsistent branch dropped */
            FR_AWAIT(k, L->x, F_FIELD, t, 2 * L->q + 1);
            FR_AWAIT(k, r, F_FCENT, chi, L->phi);
            if (r == 2) { wordbuf_clear(&L->wb); goto forward_x; }
            wordbuf_push(&L->wb, L->phi); wordbuf_push(&L->wb, L->x);
            FR_AWAIT(k, L->uni, F_FCJOIN, L->uni, L->phi);
        }
        FR_AWAIT(k, r, F_FCENT, chi, L->uni);
        if (r != 2) { wordbuf_clear(&L->wb); FR_FINISH(k, res_rec(R_INVALID, 0, "system does not cover the ambient face")); }
        wordbuf_push(&L->wb, t); wordbuf_push(&L->wb, 0);
        FR_CALL(k, r, intern_sub(k, &M.keys, &L->wb, &L->created));
        FR_FINISH(k, r);
    }

    if (L->tag == T_COMP) {
        FR_AWAIT(k, L->phi, F_FIELD, t, 1);
        FR_AWAIT(k, r, F_FCENT, chi, L->phi);
        if (r == 2) { FR_AWAIT(k, L->x, F_BINDER, t, binder_rec(S_DIM, 0, 2, iv_one())); goto forward_x; }   /* tube coverage first */
        L->j = binder_dim_var(t, 0);
        FR_AWAIT(k, L->fam, F_BINDER, t, binder_rec(S_DIM, 0, 0, iv_var(L->j)));
        FR_AWAIT(k, L->res, F_OBS, L->fam, observe_key(chi, 0, P));
        if (RES(L->res).cls == R_NO_OBSERVATION || RES(L->res).cls == R_INVALID) FR_FINISH(k, L->res);
        if (RES(L->res).cls == R_NEUTRAL) FR_FINISH(k, res_rec(R_NEUTRAL, t, NULL));
        if (RES(L->res).cls == R_SYSTEM) {
            /* a branch available along the whole j line: outer guard ∀j.g;
             * the branches are independent: launched, then awaited in order */
            L->n = RES(L->res).nbr;
            for (L->q = 0; L->q < L->n; L->q++) { family_launch(F_CBRANCH, t, rq3(RES(L->res).br[2 * L->q], RES(L->res).br[2 * L->q + 1], chi)); FR_YIELD(k); }
            wordbuf_init(&L->wb); L->kept = 0; L->uni = fc_false();
            for (L->q = 0; L->q < L->n; L->q++) {
                FR_AWAIT(k, r, F_CBRANCH, t, rq3(RES(L->res).br[2 * L->q], RES(L->res).br[2 * L->q + 1], chi));
                if (!r) continue;                                   /* inconsistent along the line: dropped */
                {   size_t m; const uint64_t *gw = interner_get(&M.keys, r, &m);
                    wordbuf_push(&L->wb, gw[0]); wordbuf_push(&L->wb, gw[1]); L->g = gw[0]; L->kept++; }
                FR_AWAIT(k, L->uni, F_FCJOIN, L->uni, L->g);
            }
            FR_CALL(k, L->sys, intern_sub(k, &M.keys, &L->wb, &L->created));
            FR_AWAIT(k, r, F_FCENT, chi, L->uni);
            if (r != 2) FR_FINISH(k, res_rec(R_INVALID, 0, "type-family system has no branch along the whole composition line"));
            for (L->q = 0; L->q < L->kept; L->q++) {
                FR_AWAIT(k, r, F_FCENT, chi, sys_face(L->sys, L->q));
                if (r == 2) { L->x = sys_term(L->sys, L->q); goto forward_x; }
            }
            goto branchwise;
        }
        /* an introduction: the one fixed clause (§53–§54) */
        FR_AWAIT(k, L->tube, F_BINDER, t, binder_rec(S_DIM, 0, 2, iv_var(L->j)));
        FR_AWAIT(k, L->cap, F_FIELD, t, 3);
        { uint64_t w[5] = { L->j, RES(L->res).ref, L->phi, L->tube, L->cap }; FR_AWAIT(k, L->x, F_COMPCLAUSE, interner_intern(&M.keys, w, 5, NULL), 0); }
        if (!L->x) FR_FINISH(k, res_rec(R_INVALID, 0, "composition in a family whose head is not a type former or lacks its universe annotation"));
        goto forward_x;
    }
    die("whnf: unhandled head tag %d", (int)L->tag);

forward_x:
    FR_AWAIT(k, r, F_OBS, L->x, observe_key(chi, 0, P));
    FR_FINISH(k, r);

branchwise:
    /* the guarded terms of L->sys under χ ∧ φ_k: launched one per step, then
     * awaited in branch order (a failure is the first in branch order); the
     * result is reconstructed in the original branch order, nested systems
     * flattened under conjoined guards */
    if (L->kept == 0) {
        FR_CALL(k, r, creq(k, T_SYSTEM, 0, LEVELS_NONE, 0, NULL, 0, NULL));
        FR_FINISH(k, res_rec(R_SYSTEM, r, NULL));
    }
    for (L->q = 0; L->q < L->kept; L->q++) { family_launch(F_OBS, sys_term(L->sys, L->q), observe_key(chi, sys_face(L->sys, L->q), P)); FR_YIELD(k); }
    L->nfs = 0; L->fail = 0;
    for (L->q = 0; L->q < L->kept; L->q++) {
        FR_AWAIT(k, L->res, F_OBS, sys_term(L->sys, L->q), observe_key(chi, sys_face(L->sys, L->q), P));
        if (!L->fail && RES(L->res).cls == R_INVALID) L->fail = L->res;
        if (!L->fail && RES(L->res).cls == R_NO_OBSERVATION) L->fail = res_rec(R_INVALID, 0, "branch under an inconsistent guard");
        L->nfs += RES(L->res).cls == R_SYSTEM ? RES(L->res).nbr : 1;
    }
    if (L->fail) FR_FINISH(k, L->fail);
    /* the conjoined guards of nested branches: launched, then awaited */
    for (L->q = 0; L->q < L->kept; L->q++) {
        FR_AWAIT(k, L->res, F_OBS, sys_term(L->sys, L->q), observe_key(chi, sys_face(L->sys, L->q), P));
        if (RES(L->res).cls != R_SYSTEM) continue;
        for (L->a = 0; L->a < RES(L->res).nbr; L->a++) { family_launch(F_FCMEET, sys_face(L->sys, L->q), RES(L->res).br[2 * L->a]); FR_YIELD(k); }
    }
    creq_head(&L->wb, T_SYSTEM, L->nfs, LEVELS_NONE, 2 * L->nfs);
    wordbuf_init(&L->wc); wordbuf_push(&L->wc, R_SYSTEM);
    for (L->q = 0; L->q < L->kept; L->q++) {
        FR_AWAIT(k, L->res, F_OBS, sys_term(L->sys, L->q), observe_key(chi, sys_face(L->sys, L->q), P));
        if (RES(L->res).cls != R_SYSTEM) {
            creq_field(&L->wb, (Field){ F_FACE, NO_SLOT, sys_face(L->sys, L->q) }); creq_field(&L->wb, (Field){ F_REF, NO_SLOT, RES(L->res).ref });
            wordbuf_push(&L->wc, sys_face(L->sys, L->q)); wordbuf_push(&L->wc, RES(L->res).ref);
            continue;
        }
        for (L->a = 0; L->a < RES(L->res).nbr; L->a++) {
            FR_AWAIT(k, L->mf, F_FCMEET, sys_face(L->sys, L->q), RES(L->res).br[2 * L->a]);
            creq_field(&L->wb, (Field){ F_FACE, NO_SLOT, L->mf }); creq_field(&L->wb, (Field){ F_REF, NO_SLOT, RES(L->res).br[2 * L->a + 1] });
            wordbuf_push(&L->wc, L->mf); wordbuf_push(&L->wc, RES(L->res).br[2 * L->a + 1]);
        }
    }
    wordbuf_push(&L->wb, 0);
    FR_CALL(k, r, creq_buf(k, &L->wb));
    wordbuf_push(&L->wc, r); wordbuf_push(&L->wc, 0);
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->wc, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}

/* the evaluator family and its operand families */
static void evaluator_init(void) {
    FAM[F_WHNF].name = "whnf"; FAM[F_WHNF].resume = whnf_step; FAM[F_WHNF].loc_size = sizeof(WhLoc);
    family_define(F_OBS, "whnf.observe", obs_step, 0);
    family_define(F_CREQ, "construct.request", creq_step, sizeof(CrLoc));
    family_define(F_CBRANCH, "whnf.comp_branch", cbranch_step, sizeof(CbLoc));
    family_define(F_DIST, "whnf.distribute", dist_step, sizeof(DiLoc));
    
    
    
    
}
/* comp.clause is defined by the library after the evaluator */

EvalResult whnf(RefId t, FaceId chi, WhnfStatus *status) { return whnf_pinned(t, chi, 0, status); }
EvalResult whnf_pinned(RefId t, FaceId chi, PinSet P, WhnfStatus *status) {
    if (!P) P = pins_current(1, &t);
    WhnfStatus st; uint64_t v = family_run(F_OBS, t, observe_key(chi, 0, P), &st);
    EvalResult out; memset(&out, 0, sizeof out);
    if (st != W_OK) { if (status) *status = W_STUCK; return out; }
    out = res_get(v);
    if (status) *status = out.cls == R_NO_OBSERVATION ? W_NO_OBSERVATION : out.cls == R_INVALID ? W_INVALID : W_OK;
    return out;
}

void print_result(EvalResult r, FILE *f) {
    switch (r.cls) {
    case R_INTRODUCTION: fprintf(f, "INTRO "); print_ref(r.ref, f); break;
    case R_NEUTRAL: fprintf(f, "NEUTRAL "); print_ref(r.ref, f); break;
    case R_SYSTEM:
        fprintf(f, "SYSTEM [");
        for (size_t i = 0; i < r.nbr; i++) { if (i) fprintf(f, ", "); fc_print(r.br[2 * i], f); fprintf(f, " ↦ "); print_ref(r.br[2 * i + 1], f); }
        fprintf(f, "]");
        break;
    case R_NO_OBSERVATION: fprintf(f, "NO_OBSERVATION"); break;
    case R_INVALID: fprintf(f, "INVALID(%s)", r.message ? r.message : ""); break;
    default: fprintf(f, "<pending>"); break;
    }
}

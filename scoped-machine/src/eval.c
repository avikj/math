#include "eval.h"
#include "lib.h"
#include "net.h"
#include "compiler.h"
#include "pool.h"

/* ---------------- continuations, joins, results ----------------
 *
 * Ownership (§19–§20): a continuation is single-consumer and is released when
 * it has been resumed (a frame that set `keep` is reused for its next child);
 * a join box is freed when it publishes; a published result is owned by the
 * machine's result list for the life of the machine. Nothing is reclaimed
 * while a live root, entry, descriptor or continuation can still reach it. */

struct Gather {
    EntryId dest;
    size_t n, arrived;
    FaceId *faces;
    EvalResult **results;
    bool failed;
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
/* the bottom of the waiter stack of a key claimed by the inline driver: the
 * key is running on the claiming thread, which publishes it */
#define INLINE_CLAIM ((Cont *)(uintptr_t)2)

/* a job: EVALUATE(entry); RESUME(k, v) — whose k may head a delivery chain of
 * entry `src`, of which each job delivers exactly one; or a NET_PAIR (§43) */
typedef enum { TK_EVAL = 0, TK_RESUME, TK_PAIR } TaskKind;
typedef struct { TaskKind kind; EntryId entry; Cont *k; uint64_t v; EntryId src; Active pair; } Task;

/* the ready-job multiset: a linked list of fixed-size chunks; push, pop at
 * either end and a policy-chosen pop are each O(1) */
#define QCHUNK 254
typedef struct QChunk { struct QChunk *prev, *next; uint32_t lo, hi; Task t[QCHUNK]; } QChunk;

typedef struct { const char *name; FamStart start; FamResume resume; size_t steps; size_t loc_size; bool pure; } FamilyDef;
static FamilyDef FAM[F_MAX];
static size_t n_fam = F_WHNF + 1;  /* F_WHNF is built in; registered families follow */

static struct {
    /* cache */
    Interner keys;                 /* (family, a, b, env version) → EntryId */
    Chunked entries;               /* Entry per EntryId-1, non-moving, zero = U */
    /* ready jobs */
    QChunk *qfront, *qback; size_t qlen;
    pthread_mutex_t q_mu; pthread_cond_t q_cv, idle_cv;
    size_t outstanding;            /* §35: queued jobs + executing jobs (+ reserved launches) */
    bool stop;
    pthread_t *workers; size_t nworkers;
    Pool cont_pool, chunk_pool;
    Pool loc_pool[F_MAX]; bool loc_ready[F_MAX]; pthread_mutex_t loc_mu;   /* frame locals records, per family */
    /* rooted results (immutable payloads), an intrusive list */
    EvalResult *results;
    /* live joins: a join that never fills (stuck children) is dismantled at teardown */
    VEC(Gather *) joins; pthread_mutex_t join_mu;
    /* the evaluator's net (§43): APPLY_TRANSFORM / CONTINUE_REFERENCE pairs
     * are jobs of this scheduler (one outstanding count) */
    Net net; SchedPolicy pair_policy;
    /* counters */
    size_t tasks_created;
    EvalEvents ev;
    SchedPolicy policy; uint64_t rng;
} E;

static size_t add_count(size_t *p) { return __atomic_add_fetch(p, 1, __ATOMIC_RELAXED); }
EvalEvents eval_events(void) {
    EvalEvents v;
    v.request = __atomic_load_n(&E.ev.request, __ATOMIC_SEQ_CST);
    v.eval_step = __atomic_load_n(&E.ev.eval_step, __ATOMIC_SEQ_CST);
    v.publish = __atomic_load_n(&E.ev.publish, __ATOMIC_SEQ_CST);
    v.deliver = __atomic_load_n(&E.ev.deliver, __ATOMIC_SEQ_CST);
    v.ready_hit = __atomic_load_n(&E.ev.ready_hit, __ATOMIC_SEQ_CST);
    v.running_hit = __atomic_load_n(&E.ev.running_hit, __ATOMIC_SEQ_CST);
    v.launch = __atomic_load_n(&E.ev.launch, __ATOMIC_SEQ_CST);
    return v;
}
size_t family_steps(Family f) { require(f >= 1 && f < F_MAX, "bad family"); return __atomic_load_n(&FAM[f].steps, __ATOMIC_SEQ_CST); }
void eval_set_policy(SchedPolicy p, uint64_t seed) { E.policy = p; E.rng = seed ? seed : 0x9E3779B97F4A7C15ULL; }
void eval_set_pair_policy(SchedPolicy p, uint64_t seed) {
    E.pair_policy = p;
    E.net.policy = p == POL_LIFO ? 0 : p == POL_FIFO ? 1 : 2;
    E.net.rng = seed ? seed : 0x9E3779B97F4A7C15ULL;
}
Net *eval_net(void) { return &E.net; }
EvalNetEvents eval_net_events(void) {
    EvalNetEvents v;
    v.apply = __atomic_load_n(&E.net.n_apply, __ATOMIC_SEQ_CST);
    v.continue_ref = __atomic_load_n(&E.net.n_continue, __ATOMIC_SEQ_CST);
    v.op = __atomic_load_n(&E.net.n_op, __ATOMIC_SEQ_CST);
    v.eval_deliver = __atomic_load_n(&E.net.n_eval_deliver, __ATOMIC_SEQ_CST);
    v.retries = __atomic_load_n(&E.net.retries, __ATOMIC_SEQ_CST);
    return v;
}
static uint64_t rng_next(void) { E.rng ^= E.rng << 13; E.rng ^= E.rng >> 7; E.rng ^= E.rng << 17; return E.rng; }

Family family_register(const char *name, FamStart start, FamResume resume) {
    /* idempotent per name: machines are re-initialized many times in one process */
    for (size_t f = F_WHNF + 1; f < n_fam; f++) if (FAM[f].name == name || strcmp(FAM[f].name, name) == 0) { FAM[f].start = start; FAM[f].resume = resume; return (Family)f; }
    require(n_fam < F_MAX, "too many operation families");
    FAM[n_fam].name = name; FAM[n_fam].start = start; FAM[n_fam].resume = resume;
    FAM[n_fam].loc_size = 0; FAM[n_fam].pure = false;
    return (Family)n_fam++;
}
Family family_define(const char *name, FamResume step, size_t loc_size, bool pure) {
    Family f = family_register(name, NULL, step);
    FAM[f].loc_size = loc_size; FAM[f].pure = pure;
    return f;
}

static void *worker_main(void *arg);

void eval_init(void) {
    memset(&E, 0, sizeof E);
    interner_init(&E.keys);
    chunked_init(&E.entries, sizeof(Entry));
    pthread_mutex_init(&E.q_mu, NULL);
    pthread_cond_init(&E.q_cv, NULL);
    pthread_cond_init(&E.idle_cv, NULL);
    pthread_mutex_init(&E.join_mu, NULL);
    pool_init(&E.cont_pool, sizeof(Cont));
    pool_init(&E.chunk_pool, sizeof(QChunk));
    pthread_mutex_init(&E.loc_mu, NULL);
    for (size_t f = 0; f < F_MAX; f++) FAM[f].steps = 0;
    net_init(&E.net);
    net_share_scheduler(&E.net, &E.q_mu, &E.q_cv, &E.outstanding);
    E.net.policy = 1;   /* pairs FIFO by default */
}

/* a new definition environment retires every observation: the memo, the
 * results and the pending pairs; the scheduler configuration survives */
void eval_reset(void) {
    pthread_mutex_lock(&E.q_mu); size_t pending = E.outstanding; pthread_mutex_unlock(&E.q_mu);
    require(pending == 0, "eval_reset with outstanding evaluator work (the session boundary requires quiescence)");
    size_t w = E.nworkers; SchedPolicy p = E.policy, pp = E.pair_policy; uint64_t rng = E.rng; int np = E.net.policy; uint64_t nrng = E.net.rng;
    eval_free(); eval_init();
    E.policy = p; E.pair_policy = pp; E.rng = rng; E.net.policy = np; E.net.rng = nrng;
    if (w) eval_set_workers(w);
}
static void gather_free(Gather *g) {
    pthread_mutex_lock(&E.join_mu);
    E.joins.data[g->slot] = NULL;
    pthread_mutex_unlock(&E.join_mu);
    pthread_mutex_destroy(&g->mu); free(g->faces); free(g->results); free(g);
}

static void stop_workers(void) {
    if (!E.nworkers) return;
    pthread_mutex_lock(&E.q_mu);
    E.stop = true;
    pthread_cond_broadcast(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
    for (size_t i = 0; i < E.nworkers; i++) pthread_join(E.workers[i], NULL);
    free(E.workers); E.workers = NULL; E.nworkers = 0; E.stop = false;
}

void eval_set_workers(size_t n) {
    stop_workers();
    if (!n) return;
    E.workers = calloc(n, sizeof(pthread_t));
    require(E.workers, "out of memory");
    E.nworkers = n;
    for (size_t i = 0; i < n; i++) require(pthread_create(&E.workers[i], NULL, worker_main, NULL) == 0, "cannot start worker");
}
size_t eval_workers(void) { return E.nworkers; }

static Entry *ENT(EntryId e) { return (Entry *)chunked_get(&E.entries, e - 1); }
static const uint64_t *entry_key(EntryId e) { size_t n; return interner_get(&E.keys, e, &n); }
Family eval_entry_family(EntryId e) { return (Family)entry_key(e)[0]; }
uint64_t eval_entry_a(EntryId e) { return entry_key(e)[1]; }
uint64_t eval_entry_b(EntryId e) { return entry_key(e)[2]; }

static void cont_dispose(Cont *k) {
    /* a waiter that will never be resumed: release what it owns */
    if (k->kind == K_EXTERNAL && k->ext_free) k->ext_free(k->ext_ctx);
    if (k->kind == K_ROOT) rootbox_release(k->root);
}

void eval_free(void) {
    stop_workers();
    net_free(&E.net);           /* after the workers: a pending pair is a job */
    size_t ne = interner_count(&E.keys);
    for (size_t i = 0; i < ne; i++) {
        Entry *e = chunked_peek(&E.entries, i);
        if (!e) continue;
        Cont *h = e->head;
        if (h == ENTRY_READY) continue;
        for (Cont *k = h; k && k != INLINE_CLAIM; k = k->next) cont_dispose(k);     /* suspended forever: stuck demands */
    }
    interner_free(&E.keys);
    chunked_free(&E.entries);
    for (EvalResult *r = E.results; r; ) { EvalResult *nx = r->next_alloc; free(r->faces); free(r->terms); free(r); r = nx; }
    /* dismantle suspended joins (their branch continuations were waiters of stuck entries) */
    for (size_t i = 0; i < E.joins.len; i++) if (E.joins.data[i]) { Gather *g = E.joins.data[i]; pthread_mutex_destroy(&g->mu); free(g->faces); free(g->results); free(g); }
    vec_free(&E.joins);
    pthread_mutex_destroy(&E.join_mu);
    pool_destroy(&E.cont_pool);
    pool_destroy(&E.chunk_pool);
    for (size_t f = 0; f < F_MAX; f++) if (E.loc_ready[f]) pool_destroy(&E.loc_pool[f]);
    pthread_mutex_destroy(&E.loc_mu);
    pthread_mutex_destroy(&E.q_mu);
    pthread_cond_destroy(&E.q_cv); pthread_cond_destroy(&E.idle_cv);
    memset(&E, 0, sizeof E);
}

static Cont *cont_new(ContKind kind, EntryId dest, FaceId chi) {
    Cont *k = pool_alloc(&E.cont_pool);
    k->kind = kind; k->dest = dest; k->chi = chi;
    return k;
}
static Pool *loc_pool(Family f) {
    if (!__atomic_load_n(&E.loc_ready[f], __ATOMIC_ACQUIRE)) {
        pthread_mutex_lock(&E.loc_mu);
        if (!E.loc_ready[f]) { pool_init(&E.loc_pool[f], FAM[f].loc_size); __atomic_store_n(&E.loc_ready[f], true, __ATOMIC_RELEASE); }
        pthread_mutex_unlock(&E.loc_mu);
    }
    return &E.loc_pool[f];
}
static void cont_release(Cont *k) {
    if (k->kind == K_FRAME && k->loc) pool_free(loc_pool(k->fam), k->loc);
    pool_free(&E.cont_pool, k);
}
Cont *frame_new(Family f, EntryId dest) {
    Cont *k = cont_new(K_FRAME, dest, 0); k->fam = f;
    if (FAM[f].loc_size) k->loc = pool_alloc(loc_pool(f));
    return k;
}
Cont *frame_sub(Family f, const Cont *caller) {
    require(f > F_WHNF && f < n_fam && FAM[f].start == NULL, "a subroutine is a frame family");
    Cont *k = frame_new(f, 0); k->inl = caller->inl;
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
    do r->next_alloc = h; while (!__atomic_compare_exchange_n(&E.results, &h, r, true, __ATOMIC_RELEASE, __ATOMIC_RELAXED));
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
    if (n) { memcpy(r->faces, faces, n * sizeof(FaceId)); memcpy(r->terms, terms, n * sizeof(RefId)); }
    return r;
}

/* ---------------- job queue ---------------- */

static void q_push_locked(Task t) {
    if (!E.qback || E.qback->hi == QCHUNK) {
        QChunk *c = pool_alloc(&E.chunk_pool);
        c->prev = E.qback;
        if (E.qback) E.qback->next = c; else E.qfront = c;
        E.qback = c;
    }
    E.qback->t[E.qback->hi++] = t;
    E.qlen++;
}
static void q_unlink_if_empty(QChunk *c) {
    if (c->lo < c->hi) return;
    if (c->prev) c->prev->next = c->next; else E.qfront = c->next;
    if (c->next) c->next->prev = c->prev; else E.qback = c->prev;
    pool_free(&E.chunk_pool, c);
}
static Task q_pop_front_locked(void) { QChunk *c = E.qfront; Task t = c->t[c->lo++]; E.qlen--; q_unlink_if_empty(c); return t; }
static Task q_pop_back_locked(void) { QChunk *c = E.qback; Task t = c->t[--c->hi]; E.qlen--; q_unlink_if_empty(c); return t; }
static Task q_pop_random_locked(void) {
    /* a uniformly chosen job of the front or the back chunk */
    QChunk *c = (rng_next() & 1) ? E.qfront : E.qback;
    uint32_t i = c->lo + (uint32_t)(rng_next() % (c->hi - c->lo));
    if (c == E.qback) { Task x = c->t[i]; c->t[i] = c->t[c->hi - 1]; c->t[c->hi - 1] = x; return q_pop_back_locked(); }
    Task x = c->t[i]; c->t[i] = c->t[c->lo]; c->t[c->lo] = x; return q_pop_front_locked();
}

/* §35 quiescence protocol: outstanding = queued + executing. A launch
 * reserves its job (outstanding += 1) before the key can be observed
 * RUNNING, so no observer can see a running key with outstanding == 0. */
static void reserve_job(void) { pthread_mutex_lock(&E.q_mu); E.outstanding++; pthread_mutex_unlock(&E.q_mu); }
static void finish_job(void) {
    pthread_mutex_lock(&E.q_mu);
    require(E.outstanding > 0, "finish without outstanding job");
    if (--E.outstanding == 0) pthread_cond_broadcast(&E.idle_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void enqueue_reserved(Task t) {
    pthread_mutex_lock(&E.q_mu);
    q_push_locked(t);
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void enqueue(Task t) {
    pthread_mutex_lock(&E.q_mu);
    E.outstanding++;
    q_push_locked(t);
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}

/* one delivery: the RESUME job of k. DELIVER is counted here, for ready hits
 * and for publication alike; the resumed frame step is counted when the
 * RESUME job executes. Delivery never happens inside an entry transition. */
static void deliver(Cont *k, uint64_t v, EntryId src) {
    /* k heads a delivery chain only when it comes from a published waiter
     * stack; every other caller passes a continuation whose link is clear */
    add_count(&E.ev.deliver);
    if (src) __atomic_add_fetch(&ENT(src)->n_deliver, 1, __ATOMIC_RELAXED);
    Task t; memset(&t, 0, sizeof t); t.kind = TK_RESUME; t.k = k; t.v = v; t.src = src;
    enqueue(t);
}

/* pick the next job under q_mu according to the policy */
static bool pop_locked(Task *out) {
    size_t npairs = net_pending_pairs_locked(&E.net);
    bool have_jobs = E.qlen > 0;
    if (npairs) {
        /* two queues, each with its own policy; which queue goes first is
         * itself a policy choice (FIFO: jobs first, LIFO: pairs first,
         * RANDOM: a coin) */
        bool pairs_first = !have_jobs || E.policy == POL_LIFO || (E.policy == POL_RANDOM && (rng_next() & 1));
        if (pairs_first) { memset(out, 0, sizeof *out); out->kind = TK_PAIR; require(net_pop_pair_locked(&E.net, &out->pair), "pair queue"); return true; }
    }
    if (!have_jobs) return false;
    *out = E.policy == POL_LIFO ? q_pop_back_locked() : E.policy == POL_RANDOM ? q_pop_random_locked() : q_pop_front_locked();
    return true;
}

/* ---------------- entries ---------------- */

static EntryId entry_intern(Family f, uint64_t a, uint64_t b) {
    /* an observation belongs to one definition environment: a candidate
     * mutation makes earlier observations unreachable (§57 R1). The entry's
     * operands are read from its key record, so a zero entry is a complete U
     * state the moment its key is discoverable. */
    uint64_t w[4] = { f, a, b, FAM[f].pure ? 0 : global_env_version() };
    EntryId id = interner_intern(&E.keys, w, 4, NULL);
    chunked_at(&E.entries, id - 1);
    return id;
}

EntryId eval_entry_lookup(RefId t, FaceId chi) {
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    uint64_t w[4] = { F_WHNF, t, fc_project(chi, S, n), global_env_version() };
    return interner_find(&E.keys, w, 4);
}
EntryState eval_entry_state(EntryId e) {
    Cont *h = __atomic_load_n(&ENT(e)->head, __ATOMIC_ACQUIRE);
    return h == NULL ? E_UNEVALUATED : h == ENTRY_READY ? E_READY : E_RUNNING;
}
FaceId eval_entry_face(EntryId e) { return eval_entry_b(e); }
size_t eval_entry_count(void) { return interner_count(&E.keys); }
size_t eval_entry_runs(EntryId e) { return __atomic_load_n(&ENT(e)->runs, __ATOMIC_ACQUIRE); }
RefId eval_entry_ref(EntryId e) { return eval_entry_a(e); }
void eval_entry_events(EntryId e, size_t *req, size_t *dl, size_t *pub) {
    Entry *x = ENT(e);
    *req = __atomic_load_n(&x->n_req, __ATOMIC_ACQUIRE); *dl = __atomic_load_n(&x->n_deliver, __ATOMIC_ACQUIRE); *pub = __atomic_load_n(&x->n_pub, __ATOMIC_ACQUIRE);
}
size_t eval_running_count(void) { size_t c = 0, n = eval_entry_count(); for (size_t i = 1; i <= n; i++) if (eval_entry_state(i) == E_RUNNING) c++; return c; }
size_t eval_task_count(void) { return __atomic_load_n(&E.tasks_created, __ATOMIC_SEQ_CST); }

/* PUB(K,v) + R(W) → D(v) + {DELIVER(c,v) : c ∈ W}: the value is stored, the
 * waiter stack is exchanged for READY in one atomic step, and the stack is
 * handed to one delivery job; each delivery job delivers one waiter and
 * hands the rest on (§26, bounded per step). */
void family_publish(EntryId eid, uint64_t v) {
    Entry *e = ENT(eid);
    __atomic_store_n(&e->value, v, __ATOMIC_RELEASE);
    __atomic_add_fetch(&e->n_pub, 1, __ATOMIC_RELAXED);
    Cont *w = __atomic_exchange_n(&e->head, ENTRY_READY, __ATOMIC_ACQ_REL);
    require(w != NULL && w != ENTRY_READY, "publish into an entry that is not running");
    __atomic_store_n(&e->state, E_READY, __ATOMIC_RELEASE);
    add_count(&E.ev.publish);
    if (w != INLINE_CLAIM) deliver(w, v, eid);
}

static void publish(EntryId eid, EvalResult *r) {
    require(r->cls != R_NO_OBSERVATION, "no observation is never a published value");
    family_publish(eid, (uint64_t)(uintptr_t)r);
}

/* REQ(K,c): U → R({c}) + EVAL(K), R(W) → R(W ⊎ {c}), D(v) → D(v) + DELIVER(c,v) */
static void request_entry(EntryId eid, Cont *k) {
    Entry *e = ENT(eid);
    add_count(&E.ev.request);
    __atomic_add_fetch(&e->n_req, 1, __ATOMIC_RELAXED);
    for (;;) {
        Cont *h = __atomic_load_n(&e->head, __ATOMIC_ACQUIRE);
        if (h == ENTRY_READY) {
            uint64_t v = __atomic_load_n(&e->value, __ATOMIC_ACQUIRE);
            add_count(&E.ev.ready_hit);
            k->next = NULL;             /* a failed push left a stale link: k is delivered alone */
            deliver(k, v, eid);
            return;
        }
        if (h == NULL) {
            /* the launch is reserved before RUNNING can be observed */
            reserve_job();
            k->next = NULL;
            if (__atomic_compare_exchange_n(&e->head, &h, k, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                __atomic_store_n(&e->state, E_RUNNING, __ATOMIC_RELEASE);
                add_count(&E.ev.launch);
                add_count(&E.tasks_created);
                Task job; memset(&job, 0, sizeof job); job.kind = TK_EVAL; job.entry = eid;
                enqueue_reserved(job);
                return;
            }
            finish_job();               /* not the launcher: give the reservation back */
            continue;
        }
        k->next = h;
        if (__atomic_compare_exchange_n(&e->head, &h, k, true, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE)) {
            add_count(&E.ev.running_hit);
            return;
        }
    }
}

void family_request(Family f, uint64_t a, uint64_t b, Cont *k) {
    require(f > F_WHNF && f < n_fam, "unregistered family");
    request_entry(entry_intern(f, a, b), k);
}

/* ---------------- frame programs ----------------
 * A scheduled frame's step schedules its continuation (a request, the
 * subroutine's first step, its own next step, a publication or the parent's
 * resumption). An inline frame's step records its outcome for the inline
 * driver, which runs the same step functions on the calling thread. */
typedef enum { IN_NONE = 0, IN_REQUEST, IN_CALL, IN_YIELD, IN_FINISH } InKind;
typedef struct { InKind kind; Family f; uint64_t a, b, v; Cont *child; } InOut;
static __thread InOut tl_out;
static __thread unsigned tl_inline_depth;

static void enqueue_resume(Cont *k, uint64_t v) {
    Task t; memset(&t, 0, sizeof t); t.kind = TK_RESUME; t.k = k; t.v = v;
    enqueue(t);
}
static void inline_out(InKind kind, Family f, uint64_t a, uint64_t b, uint64_t v, Cont *child) {
    require(tl_out.kind == IN_NONE, "an inline frame step ended in two outcomes");
    tl_out.kind = kind; tl_out.f = f; tl_out.a = a; tl_out.b = b; tl_out.v = v; tl_out.child = child;
}
void frame_request(Cont *k, Family f, uint64_t a, uint64_t b) {
    if (k->inl) { inline_out(IN_REQUEST, f, a, b, 0, NULL); return; }
    k->keep = true;
    family_request(f, a, b, k);
}
void frame_call(Cont *k, Cont *child) {
    require(child->kind == K_FRAME && child->dest == 0 && child->inl == k->inl, "a subroutine frame of this caller");
    if (k->inl) { inline_out(IN_CALL, 0, 0, 0, 0, child); return; }
    child->parent = k; k->keep = true;
    enqueue_resume(child, 0);
}
void frame_yield(Cont *k) {
    if (k->inl) { inline_out(IN_YIELD, 0, 0, 0, 0, NULL); return; }
    k->keep = true;
    enqueue_resume(k, 0);
}
void frame_finish(Cont *k, uint64_t v) {
    if (k->inl) { inline_out(IN_FINISH, 0, 0, 0, v, NULL); return; }
    if (k->parent) { Cont *p = k->parent; k->parent = NULL; enqueue_resume(p, v); return; }
    family_publish(k->dest, v);
}

/* drive one inline frame (and the subroutines it calls) to its value */
static uint64_t inline_drive(Cont *k) {
    InOut saved = tl_out;
    VEC(Cont *) callers = { 0 };
    uint64_t v = 0, result = 0;
    for (;;) {
        tl_out.kind = IN_NONE;
        __atomic_add_fetch(&FAM[k->fam].steps, 1, __ATOMIC_RELAXED);
        FAM[k->fam].resume(k, v);
        InOut o = tl_out;
        switch (o.kind) {
        case IN_REQUEST: v = family_call(o.f, o.a, o.b); break;
        case IN_YIELD: v = 0; break;
        case IN_CALL: vec_push(&callers, k); k = o.child; v = 0; break;
        case IN_FINISH:
            cont_release(k);
            if (!callers.len) { result = o.v; goto done; }
            k = callers.data[--callers.len]; v = o.v;
            break;
        default: die("an inline frame step ended without an outcome (family %s, pc %u)", FAM[k->fam].name, (unsigned)k->pc);
        }
    }
done:
    vec_free(&callers);
    tl_out = saved;
    return result;
}

uint64_t family_call(Family f, uint64_t a, uint64_t b) {
    require(f > F_WHNF && f < n_fam && FAM[f].start == NULL, "family_call needs a frame family");
    require(++tl_inline_depth < (1u << 20), "inline call depth");
    EntryId eid = entry_intern(f, a, b);
    Entry *e = ENT(eid);
    uint64_t out;
    Cont *h = __atomic_load_n(&e->head, __ATOMIC_ACQUIRE);
    if (h == ENTRY_READY) out = __atomic_load_n(&e->value, __ATOMIC_ACQUIRE);
    else {
        bool claimed = false;
        if (h == NULL) {
            claimed = __atomic_compare_exchange_n(&e->head, &h, INLINE_CLAIM, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
            if (!claimed && h == ENTRY_READY) { out = __atomic_load_n(&e->value, __ATOMIC_ACQUIRE); goto done; }
        }
        if (claimed) {
            require(__atomic_fetch_add(&e->runs, 1, __ATOMIC_ACQ_REL) == 0, "a key is evaluated by exactly one task");
            __atomic_store_n(&e->state, E_RUNNING, __ATOMIC_RELEASE);
        }
        Cont *k = frame_new(f, claimed ? eid : 0); k->inl = true; k->w[0] = a; k->w[1] = b;
        out = inline_drive(k);
        if (claimed) family_publish(eid, out);
    }
done:
    tl_inline_depth--;
    return out;
}

static bool validate_occurrence(RefId t, FaceId chi) {
    /* the ambient face must entail the reference's required face (which
     * already folds in the required faces of its free variables) */
    return fc_entails(chi, ref_required(t));
}

void eval_request(RefId t, FaceId chi, Cont *k) {
    k->next = NULL;
    if (fc_is_false(chi)) { deliver(k, (uint64_t)(uintptr_t)result_new(R_NO_OBSERVATION, t), 0); return; }
    if (!validate_occurrence(t, chi)) { deliver(k, (uint64_t)(uintptr_t)result_invalid("occurrence outside its required face"), 0); return; }
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    FaceId eta = fc_project(chi, S, n);
    request_entry(entry_intern(F_WHNF, t, eta), k);
}

static void forward(RefId t, FaceId chi, EntryId dest) { eval_request(t, chi, cont_new(K_FORWARD, dest, chi)); }

/* ---------------- dispatch ---------------- */

static void eval_system_head(RefId t, const Head *h, FaceId chi, EntryId dest) {
    size_t nb = h->n / 2;
    FaceId *faces = malloc((nb ? nb : 1) * sizeof(FaceId));
    RefId *terms = malloc((nb ? nb : 1) * sizeof(RefId));
    require(faces && terms, "out of memory");
    size_t kept = 0;
    FaceId uni = fc_false();
    for (size_t k = 0; k < nb; k++) {
        FaceId phi = HF(h, 2 * k).id;
        RefId tk = HF(h, 2 * k + 1).id;
        if (fc_is_false(fc_meet(chi, phi))) continue;           /* inconsistent branch dropped */
        if (fc_entails(chi, phi)) { free(faces); free(terms); forward(tk, chi, dest); return; }
        faces[kept] = phi; terms[kept] = tk; kept++;
        uni = fc_join(uni, phi);
    }
    if (!fc_entails(chi, uni)) { free(faces); free(terms); publish(dest, result_invalid("system does not cover the ambient face")); return; }
    publish(dest, result_system(t, kept, faces, terms));
    free(faces); free(terms);
}

static void evaluate_whnf(EntryId eid);
static void evaluate(EntryId eid) {
    Entry *e = ENT(eid);
    require(__atomic_fetch_add(&e->runs, 1, __ATOMIC_ACQ_REL) == 0, "a key is evaluated by exactly one task");
    Family f = eval_entry_family(eid);
    __atomic_add_fetch(&FAM[f].steps, 1, __ATOMIC_RELAXED);
    if (f == F_WHNF) evaluate_whnf(eid);
    else if (FAM[f].start) FAM[f].start(eid, eval_entry_a(eid), eval_entry_b(eid));
    else {
        /* a frame family: its first step */
        Cont *k = frame_new(f, eid); k->w[0] = eval_entry_a(eid); k->w[1] = eval_entry_b(eid);
        FAM[f].resume(k, 0);
        if (!k->keep) cont_release(k);
    }
}

static void evaluate_whnf(EntryId eid) {
    RefId t = eval_entry_a(eid);
    FaceId chi = eval_entry_b(eid);   /* evaluate under the key's face, not a requester's */
    if (ref_is_var(t)) { publish(eid, result_new(R_NEUTRAL, t)); return; }
    Head h; open_ref(t, &h);
    switch (h.tag) {
    case T_UNIVERSE: case T_PI: case T_SIGMA: case T_LAM: case T_PAIR: case T_PATH: case T_PLAM:
        publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLOBAL:
        /* a declared symbol without a body is an opaque constant: neutral */
        if (!global_body((SymbolId)h.payload)) publish(eid, result_new(R_NEUTRAL, t));
        else forward(unfold_global(t), chi, eid);
        break;
    case T_APP: {
        Cont *k = cont_new(K_APP, eid, chi); k->orig = t; k->a = HF(&h, 1).id;
        eval_request(HF(&h, 0).id, chi, k);
        break;
    }
    case T_FST: case T_SND: {
        Cont *k = cont_new(h.tag == T_FST ? K_FST : K_SND, eid, chi); k->orig = t;
        eval_request(HF(&h, 0).id, chi, k);
        break;
    }
    case T_PAPP: {
        IntervalId s = HF(&h, 4).id;
        if (fc_entails(chi, fc_endpoint(s, 0))) { forward(HF(&h, 1).id, chi, eid); break; }
        if (fc_entails(chi, fc_endpoint(s, 1))) { forward(HF(&h, 2).id, chi, eid); break; }
        Cont *k = cont_new(K_PAPP, eid, chi); k->orig = t; k->s = s;
        eval_request(HF(&h, 3).id, chi, k);
        break;
    }
    case T_GLUE_TYPE:
        if (fc_entails(chi, HF(&h, 1).id)) forward(HF(&h, 2).id, chi, eid);
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLUE_INTRO:
        if (fc_entails(chi, HF(&h, 1).id)) forward(HF(&h, 4).id, chi, eid);
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_UNGLUE:
        if (fc_entails(chi, HF(&h, 1).id)) forward(mk_app(mk_fst(HF(&h, 3).id), HF(&h, 4).id), chi, eid);
        else { Cont *k = cont_new(K_UNGLUE, eid, chi); k->orig = t; eval_request(HF(&h, 4).id, chi, k); }
        break;
    case T_SYSTEM:
        eval_system_head(t, &h, chi, eid);
        break;
    case T_TCALL: {
        /* §43: consume this frame; allocate APPLY_TRANSFORM(id,dir,σ) with
         * REF(a) on its principal port and CONTINUE_REFERENCE(K) on its
         * result; K stays RUNNING, its suspended evaluation is now owned by
         * the receiver. Connecting the principal ports enqueues the pair
         * before this job finishes. */
        uint64_t id; int dir; MapId sigma; RefId a;
        require(compiler_decode_call(&h, &id, &dir, &sigma, &a), "malformed TRANSFORM_CALL");
        Payload P = {0}; P.a = id; P.b = (uint64_t)dir; P.c = sigma;
        NodeId op = net_operation(&E.net, OP_APPLY_TRANSFORM, P);
        Payload Pr = {0}; Pr.ref = a;
        NodeId d = net_descriptor(&E.net, D_REF, Pr);
        Payload Pk = {0}; Pk.a = eid; Pk.face = chi;
        int8_t pol[1] = { -1 };
        NodeId cr = net_node(&E.net, A_CONTINUE_REFERENCE, 1, pol, Pk);
        net_connect(&E.net, op, 1, cr, 0);
        net_connect(&E.net, op, 0, d, 0);
        break;
    }
    case T_COMP: {
        FaceId phi = HF(&h, 1).id;
        if (fc_entails(chi, phi)) {            /* tube coverage first */
            forward(apply_dim_binder(t, 0, 2, iv_one()), chi, eid);
            break;
        }
        DimOpen fam = resolve_dim_binder(t, 0, 0);
        DimOpen tube = resolve_dim_binder(t, 0, 2);
        require(fam.j == tube.j, "family and tube must share the composition dimension");
        Cont *k = cont_new(K_COMP_FAMILY, eid, chi);
        k->orig = t; k->j = fam.j; k->tube = tube.body; k->phi = phi; k->cap = HF(&h, 3).id;
        eval_request(fam.body, chi, k);
        break;
    }
    }
    head_free(&h);
}

/* rebuild an eliminator around a new scrutinee (system distribution) */
static RefId rebuild_elim(const Cont *k, RefId scrut) {
    Head h; open_ref(k->orig, &h);
    RefId out = 0;
    switch (k->kind) {
    case K_APP: out = mk_app(scrut, HF(&h, 1).id); break;
    case K_FST: out = mk_fst(scrut); break;
    case K_SND: out = mk_snd(scrut); break;
    case K_PAPP: {
        DimOpen B = resolve_dim_binder(k->orig, 0, 0);
        out = mk_papp_lv(levels_first(h.levels), B.j, B.body, HF(&h, 1).id, HF(&h, 2).id, scrut, HF(&h, 4).id);
        break;
    }
    case K_UNGLUE: out = mk_unglue_lv(levels_first(h.levels), HF(&h, 0).id, HF(&h, 1).id, HF(&h, 2).id, HF(&h, 3).id, scrut); break;
    default: die("rebuild of a non-eliminator");
    }
    head_free(&h);
    return out;
}

/* Act branchwise: demand each guarded term under chi ∧ phi_k; the join box
 * publishes the reconstructed guarded result once every box is full (§12,
 * §26). Each box has one producer; the last arrival publishes. */
static void publish_branchwise(EntryId dest, FaceId chi, size_t n, const FaceId *faces, const RefId *terms) {
    Gather *g = calloc(1, sizeof *g);
    require(g, "out of memory");
    g->dest = dest; g->n = n;
    g->faces = malloc((n ? n : 1) * sizeof(FaceId));
    g->results = calloc(n ? n : 1, sizeof(EvalResult *));
    require(g->faces && g->results, "out of memory");
    if (n) memcpy(g->faces, faces, n * sizeof(FaceId));
    pthread_mutex_init(&g->mu, NULL);
    pthread_mutex_lock(&E.join_mu); g->slot = E.joins.len; vec_push(&E.joins, g); pthread_mutex_unlock(&E.join_mu);
    if (n == 0) { gather_free(g); publish(dest, result_system(mk_system(0, NULL, NULL), 0, NULL, NULL)); return; }
    for (size_t i = 0; i < n; i++) {
        Cont *k = cont_new(K_BRANCH, dest, fc_meet(chi, faces[i]));
        k->gather = g; k->branch = i; k->orig = terms[i];
        eval_request(terms[i], k->chi, k);
    }
}

static void resume_branch(Cont *k, EvalResult *r) {
    Gather *g = k->gather;
    pthread_mutex_lock(&g->mu);
    g->results[k->branch] = r;
    if (r->cls == R_INVALID || r->cls == R_NO_OBSERVATION) g->failed = true;
    bool full = (++g->arrived == g->n);
    pthread_mutex_unlock(&g->mu);
    if (!full) return;                          /* the join is enabled only when every box is full */
    EntryId dest = g->dest;
    if (g->failed) {
        /* select the failure by original branch order, independent of arrival order */
        EvalResult *out = NULL;
        for (size_t i = 0; i < g->n && !out; i++) {
            EvalResult *b = g->results[i];
            if (b->cls == R_INVALID) out = b;
            else if (b->cls == R_NO_OBSERVATION) out = result_invalid("branch under an inconsistent guard");
        }
        gather_free(g);
        publish(dest, out);
        return;
    }
    /* reconstruct: nested system results are flattened under conjoined guards */
    Words fs, ts; words_init(&fs); words_init(&ts);
    for (size_t i = 0; i < g->n; i++) {
        EvalResult *b = g->results[i];
        if (b->cls == R_SYSTEM) {
            for (size_t j = 0; j < b->nbr; j++) { words_push(&fs, fc_meet(g->faces[i], b->faces[j])); words_push(&ts, b->terms[j]); }
        } else { words_push(&fs, g->faces[i]); words_push(&ts, b->ref); }
    }
    gather_free(g);
    RefId owner = mk_system(fs.n, fs.w, ts.w);
    EvalResult *res = result_system(owner, fs.n, fs.w, ts.w);
    words_free(&fs); words_free(&ts);
    publish(dest, res);
}

static void distribute(const Cont *k, const EvalResult *sys) {
    RefId *terms = malloc((sys->nbr ? sys->nbr : 1) * sizeof(RefId));
    require(terms, "out of memory");
    for (size_t i = 0; i < sys->nbr; i++) terms[i] = rebuild_elim(k, sys->terms[i]);
    publish_branchwise(k->dest, k->chi, sys->nbr, sys->faces, terms);
    free(terms);
}

static void resume_comp_family(Cont *k, EvalResult *r) {
    if (r->cls == R_NEUTRAL) { publish(k->dest, result_new(R_NEUTRAL, k->orig)); return; }
    if (r->cls == R_SYSTEM) {
        /* branch available along the whole j line: outer guard ∀j.phi_k */
        FaceId *faces = malloc((r->nbr ? r->nbr : 1) * sizeof(FaceId));
        RefId *terms = malloc((r->nbr ? r->nbr : 1) * sizeof(RefId));
        require(faces && terms, "out of memory");
        size_t kept = 0; FaceId uni = fc_false();
        for (size_t i = 0; i < r->nbr; i++) {
            FaceId g = fc_forall(k->j, r->faces[i]);
            if (fc_is_false(fc_meet(k->chi, g))) continue;
            faces[kept] = g;
            { Head ho; open_ref(k->orig, &ho); uint64_t lv = levels_first(ho.levels); if (ho.levels == LEVELS_NONE) lv = LEVEL_NONE; head_free(&ho);
              terms[kept] = mk_comp_lv(lv, k->j, r->terms[i], k->phi, k->tube, k->cap); }
            kept++;
            uni = fc_join(uni, g);
        }
        if (!fc_entails(k->chi, uni)) { free(faces); free(terms); publish(k->dest, result_invalid("type-family system has no branch along the whole composition line")); return; }
        for (size_t i = 0; i < kept; i++) if (fc_entails(k->chi, faces[i])) { RefId ti = terms[i]; free(faces); free(terms); forward(ti, k->chi, k->dest); return; }
        publish_branchwise(k->dest, k->chi, kept, faces, terms);
        free(faces); free(terms);
        return;
    }
    /* introduction: capture the retained components of the exposed head
     * and instantiate the one fixed clause (§53–§54); the producer entry's
     * face is the clause's source annotation κ */
    RefId out = comp_clause(k->j, r->ref, k->phi, k->tube, k->cap, eval_entry_b(k->dest));
    if (!out) { publish(k->dest, result_invalid("composition in a family whose head is not a type former or lacks its universe annotation")); return; }
    forward(out, k->chi, k->dest);
}

static void resume(Cont *k, uint64_t v) {
    EvalResult *r = (EvalResult *)(uintptr_t)v;
    switch (k->kind) {
    case K_FRAME: FAM[k->fam].resume(k, v); return;
    case K_ROOT: {
        RootBox *b = k->root;
        pthread_mutex_lock(&b->mu); b->result = v; b->done = true; pthread_cond_broadcast(&b->cv); pthread_mutex_unlock(&b->mu);
        /* wake clients waiting for either their root or quiescence */
        pthread_mutex_lock(&E.q_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.q_mu);
        rootbox_release(b);
        return;
    }
    case K_EXTERNAL: k->ext_fn(k->ext_ctx, r); return;
    case K_BRANCH: resume_branch(k, r); return;
    default: break;
    }
    if (r->cls == R_NO_OBSERVATION || r->cls == R_INVALID) { publish(k->dest, r); return; }
    if (k->kind == K_FORWARD) { publish(k->dest, r); return; }
    if (k->kind == K_COMP_FAMILY) { resume_comp_family(k, r); return; }
    if (r->cls == R_NEUTRAL) { publish(k->dest, result_new(R_NEUTRAL, k->orig)); return; }
    if (r->cls == R_SYSTEM) { distribute(k, r); return; }
    /* introduction under an eliminator */
    Head h; open_ref(r->ref, &h);
    switch (k->kind) {
    case K_APP:
        if (h.tag != T_LAM) { publish(k->dest, result_invalid("application of a non-function introduction")); break; }
        forward(apply_term_binder(r->ref, 0, 1, k->a), k->chi, k->dest);
        break;
    case K_FST: case K_SND:
        if (h.tag != T_PAIR) { publish(k->dest, result_invalid("projection of a non-pair introduction")); break; }
        forward(HF(&h, k->kind == K_FST ? 0 : 1).id, k->chi, k->dest);
        break;
    case K_PAPP:
        if (h.tag != T_PLAM) { publish(k->dest, result_invalid("path application of a non-path introduction")); break; }
        forward(apply_dim_binder(r->ref, 0, 0, k->s), k->chi, k->dest);
        break;
    case K_UNGLUE:
        if (h.tag != T_GLUE_INTRO) { publish(k->dest, result_invalid("unglue of a non-glue introduction")); break; }
        forward(HF(&h, 5).id, k->chi, k->dest);
        break;
    default: die("unreachable continuation kind");
    }
    head_free(&h);
}

/* one elementary frame step, or one local rule of the evaluator's net
 * (counted in the net's rule classes, not as an evaluator step) */
static void execute(Task t) {
    if (t.kind == TK_PAIR) { net_step_pair(&E.net, t.pair); return; }
    add_count(&E.ev.eval_step);
    if (t.kind == TK_EVAL) { evaluate(t.entry); return; }
    Cont *k = t.k;
    if (k->next) { Cont *rest = k->next; k->next = NULL; if (rest != INLINE_CLAIM) deliver(rest, t.v, t.src); }   /* hand the chain on: one delivery per job */
    if (k->kind == K_FRAME) __atomic_add_fetch(&FAM[k->fam].steps, 1, __ATOMIC_RELAXED);
    else __atomic_add_fetch(&FAM[F_WHNF].steps, 1, __ATOMIC_RELAXED);
    k->keep = false;
    resume(k, t.v);
    if (!k->keep) cont_release(k);                 /* single consumer: released once resumed */
}

/* §43 FORWARD_RESULT(K): the receiver's request; delivery publishes into K */
void eval_forward_result(EntryId K, RefId v) { forward(v, eval_entry_b(K), K); }

static void *worker_main(void *arg) {
    (void)arg;
    pthread_mutex_lock(&E.q_mu);
    for (;;) {
        Task t;
        while (!E.stop && !pop_locked(&t)) pthread_cond_wait(&E.q_cv, &E.q_mu);   /* take_job */
        if (E.stop) break;
        pthread_mutex_unlock(&E.q_mu);
        execute(t);                      /* all child jobs are enqueued before the job finishes */
        finish_job();
        pthread_mutex_lock(&E.q_mu);
    }
    pthread_mutex_unlock(&E.q_mu);
    return NULL;
}

size_t eval_run(void) {
    if (E.nworkers) {
        /* wait until outstanding == 0 (no queued, reserved or executing job) */
        pthread_mutex_lock(&E.q_mu);
        size_t before = __atomic_load_n(&E.ev.eval_step, __ATOMIC_SEQ_CST);
        while (E.outstanding > 0) pthread_cond_wait(&E.idle_cv, &E.q_mu);
        size_t n = __atomic_load_n(&E.ev.eval_step, __ATOMIC_SEQ_CST) - before;
        pthread_mutex_unlock(&E.q_mu);
        return n;
    }
    size_t n = 0;
    for (;;) {
        Task t;
        pthread_mutex_lock(&E.q_mu);
        bool got = pop_locked(&t);
        pthread_mutex_unlock(&E.q_mu);
        if (!got) break;
        execute(t);
        finish_job();
        n++;
    }
    return n;
}

/* drive the queue until the root continuation of `box` is resumed, or the
 * machine is quiescent (a stuck demand); returns whether it was resumed */
static bool drive_root(RootBox *box, uint64_t *out) {
    if (E.nworkers) {
        /* wait for this root, or for quiescence of the whole machine (stuck) */
        pthread_mutex_lock(&E.q_mu);
        for (;;) {
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            if (d || E.outstanding == 0) break;
            pthread_cond_wait(&E.idle_cv, &E.q_mu);
        }
        pthread_mutex_unlock(&E.q_mu);
    } else {
        /* no pool: this client runs the queue; while another client thread
         * is still executing a job (its publication may resume this root, or
         * enqueue more work), wait for the root or for quiescence rather
         * than reporting a stuck demand */
        for (;;) {
            eval_run();
            pthread_mutex_lock(&E.q_mu);
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            bool queued = E.qlen > 0 || net_pending_pairs_locked(&E.net) > 0;
            if (d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
            if (!queued) pthread_cond_wait(&E.idle_cv, &E.q_mu);
            pthread_mutex_unlock(&E.q_mu);
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

uint64_t family_run(Family f, uint64_t a, uint64_t b, WhnfStatus *status) {
    Cont *root; RootBox *box = root_new(&root, 0);
    family_request(f, a, b, root);
    uint64_t v = 0;
    bool done = drive_root(box, &v);
    if (status) *status = done ? W_OK : W_STUCK;
    return done ? v : 0;
}

EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status) {
    Cont *root; RootBox *box = root_new(&root, chi);
    eval_request(t, chi, root);
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

EvalResult *whnf_in(RefId t, ContextId ctx, WhnfStatus *status) {
    uint64_t culprit;
    OccStatus os = occurrence_validate(t, ctx, &culprit);
    if (os != OCC_VALID) {
        static const char *msgs[] = { "", "free term variable not declared in the occurrence context", "free dimension not declared in the occurrence context",
                                      "declared type differs from the variable's declaration", "context assumption does not entail the required face" };
        EvalResult *r = result_invalid(msgs[os]);
        if (status) *status = W_INVALID;
        return r;
    }
    return whnf(t, context_assumption(ctx), status);
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

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
    Cont *frame;              /* the evaluator frame awaiting every branch */
    size_t pending;           /* branches outstanding, plus one until the frame has issued them all */
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
static Family F_INTERN;
static void intern_step(Cont *k, uint64_t v);

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
    v.duplicate_step = __atomic_load_n(&E.ev.duplicate_step, __ATOMIC_SEQ_CST);
    v.intern = __atomic_load_n(&E.ev.intern, __ATOMIC_SEQ_CST);
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
Family family_lookup(const char *name) {
    for (size_t f = F_WHNF + 1; f < n_fam; f++) if (strcmp(FAM[f].name, name) == 0) return (Family)f;
    return 0;
}
Family family_define(const char *name, FamResume step, size_t loc_size, bool pure) {
    Family f = family_register(name, NULL, step);
    FAM[f].loc_size = loc_size; FAM[f].pure = pure;
    return f;
}

static void *worker_main(void *arg);
static void evaluator_init(void);

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
    F_INTERN = family_define("intern", intern_step, sizeof(InternState), false);
    dnf_families_init();
    subst_families_init();
    construct_families_init();
    scope_families_init();
    template_families_init();
    evaluator_init();
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

static Entry *ENT(EntryId e) { return (Entry *)chunked_at(&E.entries, e - 1); }
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
    uint64_t w[4] = { f, a, b, FAM[f].pure ? (machine_generation() | (1ULL << 63)) : global_env_version() };
    EntryId id = interner_intern(&E.keys, w, 4, NULL);
    chunked_at(&E.entries, id - 1);
    return id;
}

EntryId eval_entry_lookup(RefId t, FaceId chi) {
    uint64_t w[4] = { F_WHNF, t, fc_project(chi, ref_support(t)), global_env_version() };
    return interner_find(&E.keys, w, 4);
}
EntryState eval_entry_state(EntryId e) {
    Cont *h = __atomic_load_n(&ENT(e)->head, __ATOMIC_ACQUIRE);
    return h == NULL ? E_UNEVALUATED : h == ENTRY_READY ? E_READY : E_RUNNING;
}
FaceId eval_entry_face(EntryId e) { return eval_entry_b(e); }
size_t eval_entry_count(void) { return interner_count(&E.keys); }
bool eval_entry_live(EntryId e) { return interner_live(&E.keys, e); }
bool eval_entry_is_observation(EntryId e) { return eval_entry_live(e) && eval_entry_family(e) == F_WHNF; }
size_t eval_entry_runs(EntryId e) { return __atomic_load_n(&ENT(e)->runs, __ATOMIC_ACQUIRE); }
RefId eval_entry_ref(EntryId e) { return eval_entry_a(e); }
void eval_entry_events(EntryId e, size_t *req, size_t *dl, size_t *pub) {
    Entry *x = ENT(e);
    *req = __atomic_load_n(&x->n_req, __ATOMIC_ACQUIRE); *dl = __atomic_load_n(&x->n_deliver, __ATOMIC_ACQUIRE); *pub = __atomic_load_n(&x->n_pub, __ATOMIC_ACQUIRE);
}
size_t eval_running_count(void) { size_t c = 0, n = eval_entry_count(); for (size_t i = 1; i <= n; i++) if (eval_entry_live(i) && eval_entry_state(i) == E_RUNNING) c++; return c; }
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
    require(f >= F_WHNF && f < n_fam && FAM[f].resume, "unregistered family");
    request_entry(entry_intern(f, a, b), k);
}

/* ---------------- frame programs ----------------
 * A scheduled frame's step schedules its continuation (a request, the
 * subroutine's first step, its own next step, a publication or the parent's
 * resumption). An inline frame's step records its outcome for the inline
 * driver, which runs the same step functions on the calling thread. */
/* A scheduled step that reschedules its own frame records that here, before
 * the frame can be resumed elsewhere; the executing job reads only this
 * thread-local flag after the step (never the frame, which may already be
 * running on another worker). */
static __thread Cont *tl_step_frame; static __thread bool tl_kept;
static void keep_frame(Cont *k) { if (k == tl_step_frame) tl_kept = true; }
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
    keep_frame(k);
    family_request(f, a, b, k);
}
void frame_call(Cont *k, Cont *child) {
    require(child->kind == K_FRAME && child->dest == 0 && child->inl == k->inl, "a subroutine frame of this caller");
    if (k->inl) { inline_out(IN_CALL, 0, 0, 0, 0, child); return; }
    child->parent = k; keep_frame(k);
    enqueue_resume(child, 0);
}
void frame_yield(Cont *k) {
    if (k->inl) { inline_out(IN_YIELD, 0, 0, 0, 0, NULL); return; }
    keep_frame(k);
    enqueue_resume(k, 0);
}
void frame_finish(Cont *k, uint64_t v) {
    if (k->inl) { inline_out(IN_FINISH, 0, 0, 0, v, NULL); return; }
    if (k->parent) { Cont *p = k->parent; k->parent = NULL; enqueue_resume(p, v); return; }
    family_publish(k->dest, v);
}
/* the step hands its entry to another owner (the evaluator's net, §43): the
 * frame ends, the entry stays running, and the owner publishes it later */
static void frame_end_unpublished(Cont *k) { require(!k->inl, "an inline frame cannot hand its entry over"); }

/* the interning subroutine: a bounded advance of the insertion per step */
#define INTERN_BUDGET 8
static void intern_step(Cont *k, uint64_t v) {
    (void)v;
    InternState *s = k->loc;
    if (!intern_advance(s, INTERN_BUDGET)) { frame_yield(k); return; }
    bool *created = (bool *)(uintptr_t)k->w[0];
    if (created) *created = s->created;
    add_count(&E.ev.intern);
    frame_finish(k, s->result);
}
Cont *intern_sub(const Cont *caller, Interner *t, WordBuf *buf, bool *created) {
    Cont *k = frame_sub(F_INTERN, caller);
    intern_begin(k->loc, t, NULL, buf, buf->n);
    k->w[0] = (uint64_t)(uintptr_t)created;
    return k;
}

/* drive one inline frame (and the subroutines it calls) to its value. The
 * steps of a claimed producer are steps of the relation like any scheduled
 * step and are counted in W; a key computed without publication (it was
 * running elsewhere) is a duplicate and counts only in its family's steps. */
static uint64_t inline_drive(Cont *k, bool counted) {
    InOut saved = tl_out;
    VEC(Cont *) callers = { 0 };
    uint64_t v = 0, result = 0;
    for (;;) {
        tl_out.kind = IN_NONE;
        __atomic_add_fetch(&FAM[k->fam].steps, 1, __ATOMIC_RELAXED);
        if (k->fam == F_INTERN) { }
        else if (counted) add_count(&E.ev.eval_step); else add_count(&E.ev.duplicate_step);
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
        out = inline_drive(k, claimed);
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
    FaceId eta = fc_project(chi, ref_support(t));
    request_entry(entry_intern(F_WHNF, t, eta), k);
}


/* ---------------- the evaluator: a frame program ----------------
 * WHNF(t, χ) (χ projected to t's support) is a frame family like every
 * other: each step does a constant amount of work and awaits its operands
 * from their families (fields, binder application, face tests, projections,
 * constructions) and its sub-observations through the observation
 * subroutine. A branchwise result is a join: the frame issues one branch per
 * step and is resumed by the last arrival (§12, §26). */
static Family F_OBS, F_FWD, F_FIELDF, F_BINDERF, F_CONSTRUCTF, F_HEADF, F_FCENTF, F_FCPROJF, F_FCMEETF, F_FCJOINF, F_FCFORALLF, F_FCENDF;
#define RES(x) ((EvalResult *)(uintptr_t)(x))
#define RV(r) ((uint64_t)(uintptr_t)(r))
static uint64_t binder_rec(Sort sort, BinderSlot slot, FieldIndex field, uint64_t image) { uint64_t e[4] = { sort, slot, field, image }; return interner_intern(&M.keys, e, 4, NULL); }
/* a construction request (construct.c) made by the evaluator: no declared face */
static uint64_t creq(Tag tag, uint64_t payload, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b) {
    Words w; words_init(&w);
    words_push(&w, tag); words_push(&w, payload); words_push(&w, levels); words_push(&w, 0); words_push(&w, 0); words_push(&w, 0); words_push(&w, nf);
    for (size_t q = 0; q < nf; q++) { words_push(&w, f[q].kind); words_push(&w, f[q].slot); words_push(&w, f[q].id); }
    words_push(&w, nb);
    for (size_t q = 0; q < nb; q++) { words_push(&w, b[q].sort); words_push(&w, b[q].formal); words_push(&w, b[q].domain_field); }
    uint64_t id = interner_intern(&M.keys, w.w, w.n, NULL);
    words_free(&w);
    return id;
}
static Cont *obs_sub(const Cont *k, RefId x, FaceId chi) { Cont *c = frame_sub(F_OBS, k); c->w[0] = x; c->w[1] = chi; return c; }

/* observe x under χ: no observation on the false face; an invalid occurrence
 * outside x's required face; otherwise the producer (x, π_S(x) χ) */
static void obs_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    RefId x = k->w[0]; FaceId chi = k->w[1];
    FR_BEGIN(k);
    if (fc_is_false(chi)) FR_FINISH(k, RV(result_new(R_NO_OBSERVATION, x)));
    FR_AWAIT(k, r, F_FCENTF, chi, ref_required(x));
    if (r != 2) FR_FINISH(k, RV(result_invalid("occurrence outside its required face")));
    FR_AWAIT(k, r, F_FCPROJF, chi, ref_support(x));
    FR_AWAIT(k, r, F_WHNF, x, r);
    FR_FINISH(k, r);
    FR_END(k);
}
/* the receiver of a transform call publishes the observation of v into K */
static void fwd_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_CALL(k, r, obs_sub(k, k->w[0], k->w[1]));
    FR_FINISH(k, r);
    FR_END(k);
}

static Gather *gather_new(size_t n, Cont *frame) {
    Gather *g = calloc(1, sizeof *g);
    require(g, "out of memory");
    g->frame = frame; g->n = n; g->pending = n + 1;
    g->faces = malloc((n ? n : 1) * sizeof(FaceId));
    g->results = calloc(n ? n : 1, sizeof(EvalResult *));
    require(g->faces && g->results, "out of memory");
    pthread_mutex_init(&g->mu, NULL);
    pthread_mutex_lock(&E.join_mu); g->slot = E.joins.len; vec_push(&E.joins, g); pthread_mutex_unlock(&E.join_mu);
    return g;
}
static bool gather_arrive(Gather *g) {
    pthread_mutex_lock(&g->mu);
    bool last = --g->pending == 0;
    pthread_mutex_unlock(&g->mu);
    return last;
}
/* branch i: observe term under χ_i; its value arrives at the join */
static void branch_start(Gather *g, size_t i, RefId term, FaceId chi_i) {
    Cont *bk = cont_new(K_BRANCH, 0, chi_i);
    bk->gather = g; bk->branch = i; bk->orig = term;
    Cont *ob = frame_new(F_OBS, 0); ob->w[0] = term; ob->w[1] = chi_i; ob->parent = bk;
    enqueue_resume(ob, 0);
}
static void resume_branch(Cont *k, EvalResult *r) {
    Gather *g = k->gather;
    pthread_mutex_lock(&g->mu);
    g->results[k->branch] = r;
    if (r->cls == R_INVALID || r->cls == R_NO_OBSERVATION) g->failed = true;
    g->arrived++;
    pthread_mutex_unlock(&g->mu);
    if (gather_arrive(g)) enqueue_resume(g->frame, 0);     /* the join is enabled when every box is full */
}
/* the frame has issued every branch: it waits for the last arrival (or
 * continues at once if they all arrived) */
static void frame_await_gather(Cont *k, Gather *g) {
    keep_frame(k);
    if (gather_arrive(g)) enqueue_resume(k, 0);
}
#define FR_JOIN(k, g) do { (k)->pc = __LINE__; frame_await_gather((k), (g)); return; case __LINE__:; } while (0)

typedef struct {
    Tag tag; uint64_t levels, payload, a1, a3, a4, x;
    EvalResult *res;
    size_t n, q, kept, m; FaceId uni, g; FaceId *faces; RefId *terms;
    DimVarId j; RefId fam, tube, cap; FaceId phi;
    Gather *gath; Words fs, ts;
} WhLoc;
static void wh_free(WhLoc *L) { free(L->faces); free(L->terms); L->faces = NULL; L->terms = NULL; }
static void wh_alloc(WhLoc *L, size_t n) {
    L->faces = malloc((n ? n : 1) * sizeof(FaceId)); L->terms = malloc((n ? n : 1) * sizeof(RefId));
    require(L->faces && L->terms, "out of memory");
}
static bool intro_tag(Tag t) { return t == T_UNIVERSE || t == T_PI || t == T_SIGMA || t == T_LAM || t == T_PAIR || t == T_PATH || t == T_PLAM; }
static bool elim_tag(Tag t) { return t == T_APP || t == T_FST || t == T_SND || t == T_PAPP || t == T_UNGLUE; }

static void whnf_step(Cont *k, uint64_t v) {
    WhLoc *L = FR_LOC(k, WhLoc);
    RefId t = k->w[0]; FaceId chi = k->w[1];
    uint64_t r = 0;
    FR_BEGIN(k);
    if (ref_is_var(t)) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
    L->tag = ref_tag(t);
    if (intro_tag(L->tag)) FR_FINISH(k, RV(result_new(R_INTRODUCTION, t)));

    if (L->tag == T_GLOBAL) {
        /* a declared symbol without a body is an opaque constant: neutral */
        FR_AWAIT(k, L->payload, F_HEADF, t, 0);
        if (!global_body((SymbolId)L->payload)) FR_FINISH(k, RV(result_new(R_NEUTRAL, t)));
        L->x = unfold_global(t);
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
                { Field f[1] = { { F_REF, NO_SLOT, L->a3 } }; FR_AWAIT(k, L->x, F_CONSTRUCTF, creq(T_FST, 0, LEVELS_NONE, 1, f, 0, NULL), 0); }
                { Field f[2] = { { F_REF, NO_SLOT, L->x }, { F_REF, NO_SLOT, L->a4 } }; FR_AWAIT(k, L->x, F_CONSTRUCTF, creq(T_APP, 0, LEVELS_NONE, 2, f, 0, NULL), 0); }
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
            /* distribute: the eliminator rebuilt around each branch */
            L->n = L->res->nbr; wh_alloc(L, L->n);
            FR_AWAIT(k, L->levels, F_HEADF, t, 1);
            for (L->q = 0; L->q < L->n; L->q++) {
                L->faces[L->q] = L->res->faces[L->q];
                if (L->tag == T_APP) { Field f[2] = { { F_REF, NO_SLOT, L->res->terms[L->q] }, { F_REF, NO_SLOT, L->a1 } }; FR_AWAIT(k, r, F_CONSTRUCTF, creq(T_APP, 0, LEVELS_NONE, 2, f, 0, NULL), 0); }
                else if (L->tag == T_FST || L->tag == T_SND) { Field f[1] = { { F_REF, NO_SLOT, L->res->terms[L->q] } }; FR_AWAIT(k, r, F_CONSTRUCTF, creq(L->tag, 0, LEVELS_NONE, 1, f, 0, NULL), 0); }
                else if (L->tag == T_PAPP) {
                    L->j = binder_dim_var(t, 0);
                    FR_AWAIT(k, L->fam, F_BINDERF, t, binder_rec(S_DIM, 0, 0, iv_var(L->j)));
                    FR_AWAIT(k, L->a1, F_FIELDF, t, 1);
                    FR_AWAIT(k, L->a3, F_FIELDF, t, 2);
                    { Field f[5] = { { F_REF, 0, L->fam }, { F_REF, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, L->res->terms[L->q] }, { F_INTERVAL, NO_SLOT, L->a4 } };
                      Binder b[1] = { { S_DIM, L->j, NO_FIELD } };
                      FR_AWAIT(k, r, F_CONSTRUCTF, creq(T_PAPP, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 1, b), 0); }
                } else {
                    FR_AWAIT(k, L->fam, F_FIELDF, t, 0);
                    FR_AWAIT(k, L->a3, F_FIELDF, t, 2);
                    FR_AWAIT(k, L->tube, F_FIELDF, t, 3);
                    { Field f[5] = { { F_REF, NO_SLOT, L->fam }, { F_FACE, NO_SLOT, L->a1 }, { F_REF, NO_SLOT, L->a3 }, { F_REF, NO_SLOT, L->tube }, { F_REF, NO_SLOT, L->res->terms[L->q] } };
                      FR_AWAIT(k, r, F_CONSTRUCTF, creq(T_UNGLUE, 0, levels_pack(levels_first(L->levels), LEVEL_NONE), 5, f, 0, NULL), 0); }
                }
                L->terms[L->q] = r;
            }
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
        L->n = tnode_nfields(ref_tnode(t)) / 2; wh_alloc(L, L->n);
        L->kept = 0; L->uni = fc_false();
        for (L->q = 0; L->q < L->n; L->q++) {
            FR_AWAIT(k, L->phi, F_FIELDF, t, 2 * L->q);
            FR_AWAIT(k, r, F_FCMEETF, chi, L->phi);
            if (fc_is_false(r)) continue;                       /* inconsistent branch dropped */
            FR_AWAIT(k, L->x, F_FIELDF, t, 2 * L->q + 1);
            FR_AWAIT(k, r, F_FCENTF, chi, L->phi);
            if (r == 2) { wh_free(L); goto forward_x; }
            L->faces[L->kept] = L->phi; L->terms[L->kept] = L->x; L->kept++;
            FR_AWAIT(k, L->uni, F_FCJOINF, L->uni, L->phi);
        }
        FR_AWAIT(k, r, F_FCENTF, chi, L->uni);
        if (r != 2) { wh_free(L); FR_FINISH(k, RV(result_invalid("system does not cover the ambient face"))); }
        L->res = result_system(t, L->kept, L->faces, L->terms);
        wh_free(L);
        FR_FINISH(k, RV(L->res));
    }

    if (L->tag == T_TCALL) {
        /* §43: allocate APPLY_TRANSFORM(id,dir,σ) with REF(a) on its principal
         * port and CONTINUE_REFERENCE(K) on its result; K stays running and
         * its evaluation is now owned by the receiver */
        Head h; open_ref(t, &h);
        uint64_t id; int dir; MapId sigma; RefId a;
        require(compiler_decode_call(&h, &id, &dir, &sigma, &a), "malformed TRANSFORM_CALL");
        Payload P = {0}; P.a = id; P.b = (uint64_t)dir; P.c = sigma;
        NodeId op = net_operation(&E.net, OP_APPLY_TRANSFORM, P);
        Payload Pr = {0}; Pr.ref = a;
        NodeId d = net_descriptor(&E.net, D_REF, Pr);
        Payload Pk = {0}; Pk.a = k->dest; Pk.face = chi;
        int8_t pol[1] = { -1 };
        NodeId cr = net_node(&E.net, A_CONTINUE_REFERENCE, 1, pol, Pk);
        net_connect(&E.net, op, 1, cr, 0);
        net_connect(&E.net, op, 0, d, 0);
        frame_end_unpublished(k);
        return;
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
            /* a branch available along the whole j line: outer guard ∀j.φ_k */
            L->n = L->res->nbr; wh_alloc(L, L->n);
            L->kept = 0; L->uni = fc_false();
            for (L->q = 0; L->q < L->n; L->q++) {
                FR_AWAIT(k, L->g, F_FCFORALLF, L->res->faces[L->q], L->j);
                FR_AWAIT(k, r, F_FCMEETF, chi, L->g);
                if (fc_is_false(r)) continue;
                {   uint64_t lv = L->levels == LEVELS_NONE ? LEVEL_NONE : levels_first(L->levels);
                    Field f[4] = { { F_REF, 0, L->res->terms[L->q] }, { F_FACE, NO_SLOT, L->phi }, { F_REF, 0, L->tube }, { F_REF, NO_SLOT, L->cap } };
                    Binder b[1] = { { S_DIM, L->j, NO_FIELD } };
                    FR_AWAIT(k, r, F_CONSTRUCTF, creq(T_COMP, 0, levels_pack(lv, LEVEL_NONE), 4, f, 1, b), 0); }
                L->faces[L->kept] = L->g; L->terms[L->kept] = r; L->kept++;
                FR_AWAIT(k, L->uni, F_FCJOINF, L->uni, L->g);
            }
            FR_AWAIT(k, r, F_FCENTF, chi, L->uni);
            if (r != 2) { wh_free(L); FR_FINISH(k, RV(result_invalid("type-family system has no branch along the whole composition line"))); }
            for (L->q = 0; L->q < L->kept; L->q++) {
                FR_AWAIT(k, r, F_FCENTF, chi, L->faces[L->q]);
                if (r == 2) { L->x = L->terms[L->q]; wh_free(L); goto forward_x; }
            }
            goto branchwise;
        }
        /* an introduction: the one fixed clause, at the producer's face κ = χ (§53–§54) */
        L->x = comp_clause(L->j, L->res->ref, L->phi, L->tube, L->cap, chi);
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
        FR_AWAIT(k, r, F_CONSTRUCTF, creq(T_SYSTEM, 0, LEVELS_NONE, 0, NULL, 0, NULL), 0);
        FR_FINISH(k, RV(result_system(r, 0, NULL, NULL)));
    }
    L->gath = gather_new(L->kept, k);
    for (L->q = 0; L->q < L->kept; L->q++) L->gath->faces[L->q] = L->faces[L->q];
    for (L->q = 0; L->q < L->kept; L->q++) {
        FR_AWAIT(k, r, F_FCMEETF, chi, L->faces[L->q]);
        branch_start(L->gath, L->q, L->terms[L->q], r);
    }
    wh_free(L);
    FR_JOIN(k, L->gath);
    if (L->gath->failed) {
        /* the failure selected by original branch order, independent of arrival order */
        for (L->q = 0; L->q < L->gath->n; L->q++) {
            EvalResult *b = L->gath->results[L->q];
            if (b->cls == R_INVALID) { gather_free(L->gath); FR_FINISH(k, RV(b)); }
            if (b->cls == R_NO_OBSERVATION) { gather_free(L->gath); FR_FINISH(k, RV(result_invalid("branch under an inconsistent guard"))); }
            FR_YIELD(k);
        }
    }
    /* nested system results are flattened under conjoined guards */
    words_init(&L->fs); words_init(&L->ts);
    for (L->q = 0; L->q < L->gath->n; L->q++) {
        L->res = L->gath->results[L->q];
        if (L->res->cls == R_SYSTEM) {
            for (L->m = 0; L->m < L->res->nbr; L->m++) {
                FR_AWAIT(k, r, F_FCMEETF, L->gath->faces[L->q], L->res->faces[L->m]);
                words_push(&L->fs, r); words_push(&L->ts, L->res->terms[L->m]);
            }
        } else { words_push(&L->fs, L->gath->faces[L->q]); words_push(&L->ts, L->res->ref); FR_YIELD(k); }
    }
    gather_free(L->gath); L->gath = NULL;
    {   Field *f = malloc((2 * L->fs.n + 1) * sizeof(Field)); require(f, "out of memory");
        for (size_t q = 0; q < L->fs.n; q++) { f[2 * q] = (Field){ F_FACE, NO_SLOT, L->fs.w[q] }; f[2 * q + 1] = (Field){ F_REF, NO_SLOT, L->ts.w[q] }; }
        L->x = creq(T_SYSTEM, L->fs.n, LEVELS_NONE, 2 * L->fs.n, f, 0, NULL);
        free(f); }
    FR_AWAIT(k, r, F_CONSTRUCTF, L->x, 0);
    L->res = result_system(r, L->fs.n, L->fs.w, L->ts.w);
    words_free(&L->fs); words_free(&L->ts);
    FR_FINISH(k, RV(L->res));
    FR_END(k);
}

/* the evaluator family and its operand families (registered by eval_init) */
static void evaluator_init(void) {
    FAM[F_WHNF].name = "whnf"; FAM[F_WHNF].start = NULL; FAM[F_WHNF].resume = whnf_step;
    FAM[F_WHNF].loc_size = sizeof(WhLoc); FAM[F_WHNF].pure = false;
    F_OBS = family_define("whnf.observe", obs_step, 0, false);
    F_FWD = family_define("whnf.forward", fwd_step, 0, false);
    F_FIELDF = family_lookup("field"); F_BINDERF = family_lookup("binder"); F_CONSTRUCTF = family_lookup("construct"); F_HEADF = family_lookup("head.annotation");
    F_FCENTF = family_lookup("fc.entails"); F_FCPROJF = family_lookup("fc.project"); F_FCMEETF = family_lookup("fc.meet");
    F_FCJOINF = family_lookup("fc.join"); F_FCFORALLF = family_lookup("fc.forall"); F_FCENDF = family_lookup("fc.endpoint");
    require(F_FIELDF && F_HEADF && F_FCENDF, "the evaluator's operand families are registered first");
}

static void evaluate(EntryId eid) {
    Entry *e = ENT(eid);
    require(__atomic_fetch_add(&e->runs, 1, __ATOMIC_ACQ_REL) == 0, "a key is evaluated by exactly one task");
    Family f = eval_entry_family(eid);
    __atomic_add_fetch(&FAM[f].steps, 1, __ATOMIC_RELAXED);
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
        pthread_mutex_lock(&E.q_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.q_mu);
        rootbox_release(b);
        return;
    }
    if (k->kind == K_EXTERNAL) { k->ext_fn(k->ext_ctx, r); return; }
    if (k->kind == K_BRANCH) { resume_branch(k, r); return; }
    die("unreachable continuation kind");
}

/* one elementary frame step, or one local rule of the evaluator's net
 * (counted in the net's rule classes, not as an evaluator step) */
static void execute(Task t) {
    if (t.kind == TK_PAIR) { net_step_pair(&E.net, t.pair); return; }
    /* the interning subroutine's units are the record lookup itself (like the
     * key lookup of a request): their number depends on what the table holds,
     * so they are not steps of W; each completed insertion is one event */
    if (!(t.kind == TK_RESUME && t.k->kind == K_FRAME && t.k->fam == F_INTERN)) add_count(&E.ev.eval_step);
    if (t.kind == TK_EVAL) { evaluate(t.entry); return; }
    Cont *k = t.k;
    if (k->next) { Cont *rest = k->next; k->next = NULL; if (rest != INLINE_CLAIM) deliver(rest, t.v, t.src); }   /* hand the chain on: one delivery per job */
    if (k->kind == K_FRAME) __atomic_add_fetch(&FAM[k->fam].steps, 1, __ATOMIC_RELAXED);
    else __atomic_add_fetch(&FAM[F_WHNF].steps, 1, __ATOMIC_RELAXED);
    Cont *sf = tl_step_frame; bool sk = tl_kept;
    tl_step_frame = k; tl_kept = false;
    resume(k, t.v);
    bool kept = tl_kept;
    tl_step_frame = sf; tl_kept = sk;
    if (!kept) cont_release(k);                    /* single consumer: released once resumed */
}

/* §43 FORWARD_RESULT(K): the receiver's request; delivery publishes into K */
void eval_forward_result(EntryId K, RefId v) {
    Cont *fk = frame_new(F_FWD, K); fk->w[0] = v; fk->w[1] = eval_entry_b(K);
    enqueue_resume(fk, 0);
}

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

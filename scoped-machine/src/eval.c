#include "eval.h"
#include <sys/mman.h>
#define ROOTS_CAP ((size_t)1 << 24)
#include "lib.h"
#include "net.h"
#include "compiler.h"
#include "reuse.h"
#include "fine.h"
#include "kcont.h"

/* ---------------- continuations, joins, results ----------------
 *
 * Ownership (§19–§20): a continuation is single-consumer and is freed when
 * it has been resumed; a join box is freed when it publishes; a published
 * result is owned by its READY cache entry for the life of the machine (the
 * entry retains it), and a control result delivered without an entry is
 * rooted in the machine's result list. Nothing is reclaimed while a live
 * root, entry, descriptor or continuation can still reach it. */

typedef enum {
    K_ROOT = 1, K_FORWARD, K_APP, K_FST, K_SND, K_PAPP, K_UNGLUE, K_COMP_FAMILY, K_BRANCH, K_EXTERNAL
} ContKind;

typedef struct {
    EntryId dest;
    size_t n, arrived;
    FaceId *faces;
    EvalResult **results;
    bool failed;
    pthread_mutex_t mu;
    size_t slot;              /* index in the live-join registry */
} Gather;

typedef struct {
    pthread_mutex_t mu; pthread_cond_t cv;
    bool done; EvalResult *result;
    int refs;                 /* client + root continuation; the last one frees */
} RootBox;

static void rootbox_release(RootBox *b) {
    pthread_mutex_lock(&b->mu);
    int left = --b->refs;
    pthread_mutex_unlock(&b->mu);
    if (left == 0) { pthread_mutex_destroy(&b->mu); pthread_cond_destroy(&b->cv); free(b); }
}

struct Cont {
    ContKind kind;
    EntryId dest;       /* entry to publish into (not for ROOT/EXTERNAL) */
    FaceId chi;         /* ambient face of the demanding evaluation */
    RefId orig;         /* the eliminator / composition reference, retained */
    RefId a;            /* APP argument */
    IntervalId s;       /* PAPP interval */
    DimVarId j;         /* COMP: the symbolic dimension */
    RefId tube;         /* COMP: tube body at j */
    FaceId phi;         /* COMP: tube face */
    RefId cap;          /* COMP: cap */
    Gather *gather; size_t branch;   /* BRANCH */
    RootBox *root;                   /* ROOT */
    ExternalDeliver ext_fn; void *ext_ctx; void (*ext_free)(void *);   /* EXTERNAL */
    uint64_t prefix;                 /* §78: receipt of the rules applied before this request was issued (FORWARD) */
    EntryId child;                   /* the entry this continuation waits on */
};

/* a job: EVALUATE(entry), RESUME(k, r), or a NET_PAIR of the evaluator's net (§43) */
typedef struct { bool is_resume, is_pair; EntryId entry; Cont *k; EvalResult *r; Active pair; } Task;
typedef struct { VEC(EntryId) entries; VEC(RefId) refs; } ShapeSide;

static struct {
    /* cache (§76.3): base key (shape, projected face) → head of the chain of
     * historical entries; per shape: its entries at every face and the
     * references requested with that shape (for the edge index) */
    Interner keys;                 /* (shape, face) → base id */
    Chunked heads;                 /* EntryId head per base id-1 */
    Interner shape_ids;            /* shape → dense slot */
    Chunked shape_side;            /* ShapeSide per slot-1 */
    Interner receipts;             /* receipt records */
    Chunked entries;               /* Entry per EntryId-1, non-moving */
    size_t n_entries;              /* under entries_mu */
    pthread_mutex_t entries_mu;    /* key lookup / entry creation */
    /* ready jobs (a multiset) */
    VEC(Task) queue; size_t qhead;
    pthread_mutex_t q_mu; pthread_cond_t q_cv, idle_cv;
    size_t outstanding;            /* §35: queued jobs + executing jobs (+ reserved launches) */
    bool stop;
    pthread_t *workers; size_t nworkers;
    /* rooted results (immutable payloads) */
    EvalResult *results; pthread_mutex_t res_mu;
    /* live joins: a join that never fills (stuck children) is dismantled at teardown */
    VEC(Gather *) joins; pthread_mutex_t join_mu;
    /* the evaluator's net (§43): APPLY_TRANSFORM / CONTINUE_REFERENCE pairs
     * are jobs of this scheduler (one outstanding count) */
    Net net; SchedPolicy pair_policy;
    /* §60 trace: root / external consumer occurrences in request order */
    VEC(EntryId) roots; pthread_mutex_t roots_mu;
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

static void *worker_main(void *arg);

void eval_init(void) {
    memset(&E, 0, sizeof E);
    pthread_mutex_init(&E.roots_mu, NULL);
    E.roots.cap = ROOTS_CAP;   /* root occurrences in one fixed reservation: recorded under roots_mu without growth */
    E.roots.data = mmap(NULL, ROOTS_CAP * sizeof(EntryId), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    require(E.roots.data != MAP_FAILED, "eval: roots reservation");
    interner_init(&E.keys); chunked_init(&E.heads, sizeof(EntryId));
    interner_init(&E.shape_ids); chunked_init(&E.shape_side, sizeof(ShapeSide));
    interner_init(&E.receipts);
    chunked_init(&E.entries, sizeof(Entry));
    pthread_mutex_init(&E.entries_mu, NULL);
    pthread_mutex_init(&E.q_mu, NULL);
    pthread_cond_init(&E.q_cv, NULL);
    pthread_cond_init(&E.idle_cv, NULL);
    pthread_mutex_init(&E.res_mu, NULL);
    pthread_mutex_init(&E.join_mu, NULL);
    net_init(&E.net);
    net_share_scheduler(&E.net, &E.q_mu, &E.q_cv, &E.outstanding);
    E.net.policy = 1;   /* pairs FIFO by default */
}

/* a new definition environment retires every observation: the memo, the
 * results and the pending pairs; the scheduler configuration survives */
void eval_reset(void) {
    /* the session boundary requires quiescence: work a client left queued or
     * executing (a conversion that returned while its sibling job was still
     * running under a worker pool) is drained first — it is finite and
     * belongs to the retiring session; then no job may be outstanding */
    eval_run();
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
    pthread_mutex_destroy(&g->mu); free(g->faces); free(g->results); free(g); fine_bump(FC_CELLS_RELEASED);
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

void eval_free(void) {
    stop_workers();
    if (E.roots.data) munmap(E.roots.data, ROOTS_CAP * sizeof(EntryId));
    E.roots.data = NULL; E.roots.len = E.roots.cap = 0; pthread_mutex_destroy(&E.roots_mu);
    net_free(&E.net);           /* after the workers: a pending pair is a job */
    for (size_t i = 0; i < E.n_entries; i++) {
        Entry *e = ENT(i + 1);
        for (size_t w = 0; w < e->waiters.len; w++) {                 /* suspended forever: stuck demands */
            Cont *k = e->waiters.data[w];
            if (k->kind == K_EXTERNAL && k->ext_free) k->ext_free(k->ext_ctx);
            if (k->kind == K_ROOT) rootbox_release(k->root);
            free(k);
        }
        vec_free(&e->waiters);
        vec_free(&e->deps); vec_free(&e->gdeps);
        pthread_mutex_destroy(&e->mu);
    }
    { size_t ns = interner_count(&E.shape_ids); for (size_t i = 0; i < ns; i++) { ShapeSide *ss = chunked_peek(&E.shape_side, i); if (ss) { vec_free(&ss->entries); vec_free(&ss->refs); } } }
    interner_free(&E.keys); chunked_free(&E.heads);
    interner_free(&E.shape_ids); chunked_free(&E.shape_side);
    interner_free(&E.receipts);
    chunked_free(&E.entries);
    for (EvalResult *r = E.results, *n; r; r = n) { n = r->all_next; free(r->faces); free(r->terms); free(r); }
    E.results = NULL;
    /* dismantle suspended joins (their branch continuations were waiters of stuck entries) */
    for (size_t i = 0; i < E.joins.len; i++) if (E.joins.data[i]) { Gather *g = E.joins.data[i]; pthread_mutex_destroy(&g->mu); free(g->faces); free(g->results); free(g); }
    vec_free(&E.joins);
    pthread_mutex_destroy(&E.join_mu);
    vec_free(&E.queue);
    pthread_mutex_destroy(&E.entries_mu); pthread_mutex_destroy(&E.q_mu); pthread_mutex_destroy(&E.res_mu);
    pthread_cond_destroy(&E.q_cv); pthread_cond_destroy(&E.idle_cv);
    memset(&E, 0, sizeof E);
}

static Cont *cont_new(ContKind kind, EntryId dest, FaceId chi) {
    Cont *k = calloc(1, sizeof *k);
    require(k, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    k->kind = kind; k->dest = dest; k->chi = chi;
    return k;
}
static void cont_release(Cont *k) { fine_bump(FC_CELLS_RELEASED); free(k); }

Cont *cont_external(ExternalDeliver fn, void *ctx, void (*free_ctx)(void *)) {
    Cont *k = cont_new(K_EXTERNAL, 0, 0);
    k->ext_fn = fn; k->ext_ctx = ctx; k->ext_free = free_ctx;
    return k;
}

static EvalResult *result_new(ResultClass cls, RefId ref) {
    EvalResult *r = calloc(1, sizeof *r);
    require(r, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    r->cls = cls; r->ref = ref;
    pthread_mutex_lock(&E.res_mu);
    r->all_next = E.results; E.results = r;
    pthread_mutex_unlock(&E.res_mu);
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

/* §35 quiescence protocol: outstanding = queued + executing. A launch
 * reserves its job (outstanding += 1) while the entry lock is held, so no
 * observer can see the key RUNNING with outstanding == 0; the job itself is
 * put on the queue after the entry lock is released. */
static void reserve_job(void) { pthread_mutex_lock(&E.q_mu); E.outstanding++; pthread_mutex_unlock(&E.q_mu); }
static void enqueue_reserved(Task t) {
    fine_bump(FC_QUEUE_OPS); fine_bump(FC_LOCK_ATTEMPTS);
    pthread_mutex_lock(&E.q_mu);
    vec_push(&E.queue, t);
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void enqueue(Task t) {
    fine_bump(FC_QUEUE_OPS); fine_bump(FC_LOCK_ATTEMPTS);
    pthread_mutex_lock(&E.q_mu);
    E.outstanding++;
    vec_push(&E.queue, t);
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void finish_job(void) {
    pthread_mutex_lock(&E.q_mu);
    require(E.outstanding > 0, "finish without outstanding job");
    if (--E.outstanding == 0) pthread_cond_broadcast(&E.idle_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void enqueue_resume(Cont *k, EvalResult *r) { Task t; memset(&t, 0, sizeof t); t.is_resume = true; t.k = k; t.r = r; enqueue(t); }

/* pick the next job under q_mu according to the policy */
static bool pop_locked(Task *out) {
    fine_bump(FC_QUEUE_OPS);
    size_t npairs = net_pending_pairs_locked(&E.net);
    bool have_jobs = E.qhead < E.queue.len;
    if (!have_jobs) { E.queue.len = 0; E.qhead = 0; }
    if (npairs) {
        /* two queues, each with its own policy; which queue goes first is
         * itself a policy choice (FIFO: jobs first, LIFO: pairs first,
         * RANDOM: a coin) */
        bool pairs_first = !have_jobs || E.policy == POL_LIFO || (E.policy == POL_RANDOM && (rng_next() & 1));
        if (pairs_first) { memset(out, 0, sizeof *out); out->is_pair = true; require(net_pop_pair_locked(&E.net, &out->pair), "pair queue"); return true; }
    }
    if (!have_jobs) return false;
    size_t pick = E.qhead;
    if (E.policy == POL_LIFO) pick = E.queue.len - 1;
    else if (E.policy == POL_RANDOM) pick = E.qhead + (size_t)(rng_next() % (E.queue.len - E.qhead));
    *out = E.queue.data[pick];
    E.queue.data[pick] = E.queue.data[E.qhead];
    E.qhead++;
    if (E.qhead == E.queue.len) { E.queue.len = 0; E.qhead = 0; }
    return true;
}

/* ---------------- entries ---------------- */

/* ---- receipts (§78.1) ---- */
static uint64_t rc(uint64_t a, uint64_t b, uint64_t c, uint64_t d, size_t n) { uint64_t w[4] = { a, b, c, d }; return interner_intern(&E.receipts, w, n, NULL); }
static uint64_t rc_refl(RefId t) { return rc(RC_REFL, t, 0, 0, 2); }
static uint64_t rc_seq(uint64_t a, uint64_t b) { if (!a) return b; if (!b) return a; return rc(RC_SEQ, a, b, 0, 3); }
static uint64_t rc_rule(uint64_t rule, uint64_t x, uint64_t y) { return rc(RC_RULE, rule, x, y, 4); }
const uint64_t *eval_receipt_words(uint64_t r, size_t *n) { return interner_get(&E.receipts, r, n); }

/* ---- dependency validity (§79.2) ---- */
static bool gdeps_valid_locked(const Entry *e) {
    reuse_bump(REUSE_DEPENDENCY_CHECK);
    for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) if (global_revision(e->gdeps.data[k]) != e->gdeps.data[k + 1]) return false;
    return true;
}
static void gdeps_add(Entry *e, SymbolId sym, uint64_t rev) {
    for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) if (e->gdeps.data[k] == sym) { require(e->gdeps.data[k + 1] == rev, "a producer read two revisions of one symbol"); return; }
    vec_push(&e->gdeps, sym); vec_push(&e->gdeps, rev);
}

static ShapeSide *shape_side_locked(ShapeId s, bool create) {
    uint64_t w[1] = { s };
    uint64_t slot = create ? interner_intern(&E.shape_ids, w, 1, NULL) : interner_find(&E.shape_ids, w, 1);
    if (!slot) return NULL;
    return (ShapeSide *)chunked_at(&E.shape_side, slot - 1);
}
/* the entry of the chain under (shape, face) that is reusable now: a READY
 * answer whose recorded dependencies are current, or a producer still
 * running in the current environment snapshot; 0 when none */
static EntryId chain_pick_locked(EntryId head) {
    uint64_t env = global_env_version();
    for (EntryId e = head; e; e = ENT(e)->next_alt) {
        Entry *x = ENT(e);
        pthread_mutex_lock(&x->mu);
        EntryState st = x->state; bool ok = st == E_READY ? gdeps_valid_locked(x) : x->env == env;
        pthread_mutex_unlock(&x->mu);
        if (ok) return e;
    }
    return 0;
}
static EntryId entry_intern(RefId t, FaceId eta) {
    ShapeId s = shape_of(t);
    uint64_t w[2] = { s, eta };
    bool created;
    pthread_mutex_lock(&E.entries_mu);
    ShapeSide *ss = shape_side_locked(s, true);
    { bool have = false; for (size_t k = 0; k < ss->refs.len; k++) if (ss->refs.data[k] == t) { have = true; break; } if (!have) vec_push(&ss->refs, t); }
    uint64_t base = interner_intern(&E.keys, w, 2, &created);
    EntryId *head = (EntryId *)chunked_at(&E.heads, base - 1);
    if (created) *head = 0;
    EntryId id = *head ? chain_pick_locked(*head) : 0;
    if (!id) {
        id = ++E.n_entries; fine_bump(FC_CELLS_ALLOCATED);
        Entry *e = (Entry *)chunked_at(&E.entries, id - 1);
        memset(e, 0, sizeof *e);
        e->ref = t; e->face = eta; e->state = E_UNEVALUATED; e->env = global_env_version(); e->shape = s;
        e->next_alt = *head; *head = id;
        pthread_mutex_init(&e->mu, NULL);
        vec_push(&ss->entries, id);
    }
    pthread_mutex_unlock(&E.entries_mu);
    return id;
}

EntryId eval_entry_lookup(RefId t, FaceId chi) {
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    uint64_t w[2] = { shape_of(t), fc_project(chi, S, n) };
    pthread_mutex_lock(&E.entries_mu);
    uint64_t base = interner_find(&E.keys, w, 2);
    EntryId id = base ? chain_pick_locked(*(EntryId *)chunked_at(&E.heads, base - 1)) : 0;
    pthread_mutex_unlock(&E.entries_mu);
    return id;
}
ShapeId eval_entry_shape(EntryId e) { return ENT(e)->shape; }
RefId eval_entry_residual(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); RefId r = x->state == E_READY ? x->residual : 0; pthread_mutex_unlock(&x->mu); return r; }
uint64_t eval_entry_receipt(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); uint64_t r = x->state == E_READY ? x->receipt : 0; pthread_mutex_unlock(&x->mu); return r; }
size_t eval_entry_gdeps(EntryId e, const uint64_t **pairs) { Entry *x = ENT(e); *pairs = x->gdeps.data; return x->gdeps.len / 2; }
bool eval_entry_deps_valid(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); bool ok = gdeps_valid_locked(x); pthread_mutex_unlock(&x->mu); return ok; }
EntryId eval_entry_adapter_source(EntryId e) { return ENT(e)->adapter_src; }
bool eval_entry_is_alias(EntryId e) { return ENT(e)->is_alias; }

/* §78.3–78.4: a completed receipt this new producer can continue from.
 * (a) the same shape at a weaker face (restriction is the identity
 * substitution with an entailment premise); (b) a recorded instantiation
 * edge dest = reindex(src, σ) whose source has a completed answer at a face
 * entailed by this one. The candidate must make progress: its continuation
 * key must differ from this key. Dependencies of the source must be current. */
static bool adapter_candidate(Entry *src_e, EntryId src, MapId sigma, FaceId eta, ShapeId s, RefId *out, uint64_t *prefix) {
    pthread_mutex_lock(&src_e->mu);
    bool ok = src_e->state == E_READY && src_e->residual && gdeps_valid_locked(src_e);
    RefId residual = src_e->residual; FaceId sface = src_e->face;
    pthread_mutex_unlock(&src_e->mu);
    if (!ok) return false;
    FaceId need = map_is_identity(sigma) ? sface : fc_reindex(sface, sigma);
    if (!fc_entails(eta, need)) return false;
    RefId r = map_is_identity(sigma) ? residual : reindex(residual, sigma);
    size_t n; const uint64_t *S = dimset_get(ref_support(r), &n);
    FaceId reta = fc_project(eta, S, n);
    if (reta == eta && shape_of(r) == s) return false;                    /* no progress: would wait on itself */
    if (!fc_entails(reta, ref_required(r))) return false;
    *out = r; *prefix = map_is_identity(sigma) ? rc(RC_RESTRICT, src, eta, 0, 3) : rc(RC_SPEC, src, sigma, 0, 3);
    return true;
}
/* the candidates are visited by a cursor: each acquisition of entries_mu
 * examines one position (an entry of this shape, a reference of this shape,
 * an instantiation edge, an entry of the edge's source shape) and the
 * candidate is tested outside the lock (lock-section audit: the former
 * collection of every candidate under entries_mu) */
typedef struct { int phase; size_t k, q, j; bool have_src; ShapeId src_shape; RefId src_ref; } AdapterCursor;
static int adapter_next_locked(AdapterCursor *c, RefId t, ShapeId s, EntryId self, EntryId *e, uint64_t *m) {
    ShapeSide *ss = shape_side_locked(s, false);
    if (!ss) return 0;
    if (c->phase == 0) {
        if (c->k < ss->entries.len) { EntryId x = ss->entries.data[c->k++]; if (x == self) return 2; *e = x; *m = map_identity(); return 1; }
        c->phase = 1; c->k = c->q = c->j = 0; return 2;
    }
    if (c->k > ss->refs.len) return 0;
    RefId r = c->k < ss->refs.len ? ss->refs.data[c->k] : t;
    const uint64_t *pairs; size_t np = instantiation_edges(r, &pairs);
    if (c->q >= np) { c->k++; c->q = c->j = 0; c->have_src = false; return 2; }
    if (!c->have_src) { c->src_ref = pairs[2 * c->q]; return 3; }   /* the source's shape is computed outside the lock */
    ShapeSide *src_side = shape_side_locked(c->src_shape, false);
    if (!src_side || c->j >= src_side->entries.len) { c->q++; c->j = 0; c->have_src = false; return 2; }
    *e = src_side->entries.data[c->j++]; *m = pairs[2 * c->q + 1];
    return 1;
}
static bool find_adapter(RefId t, ShapeId s, FaceId eta, EntryId self, RefId *out, uint64_t *prefix, EntryId *src_out) {
    AdapterCursor c = {0};
    for (;;) {
        EntryId e = 0; uint64_t m = 0;
        pthread_mutex_lock(&E.entries_mu);
        int st = adapter_next_locked(&c, t, s, self, &e, &m);
        pthread_mutex_unlock(&E.entries_mu);
        fine_bump(FC_ADAPTER_STEPS);
        if (st == 0) return false;
        if (st == 3) { c.src_shape = shape_of(c.src_ref); c.have_src = true; continue; }
        if (st == 1 && adapter_candidate(ENT(e), e, m, eta, s, out, prefix)) { *src_out = e; return true; }
    }
}
EntryState eval_entry_state(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); EntryState s = x->state; pthread_mutex_unlock(&x->mu); return s; }
FaceId eval_entry_face(EntryId e) { return ENT(e)->face; }
size_t eval_entry_count(void) { pthread_mutex_lock(&E.entries_mu); size_t n = E.n_entries; pthread_mutex_unlock(&E.entries_mu); return n; }
size_t eval_entry_runs(EntryId e) { return ENT(e)->runs; }
RefId eval_entry_ref(EntryId e) { return ENT(e)->ref; }
void eval_entry_events(EntryId e, size_t *req, size_t *deliver, size_t *pub) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); *req = x->n_req; *deliver = x->n_deliver; *pub = x->n_pub; pthread_mutex_unlock(&x->mu); }
size_t eval_running_count(void) { size_t c = 0, n = eval_entry_count(); for (size_t i = 1; i <= n; i++) if (eval_entry_state(i) == E_RUNNING) c++; return c; }
size_t eval_task_count(void) { return __atomic_load_n(&E.tasks_created, __ATOMIC_SEQ_CST); }
size_t eval_entry_deps(EntryId e, EntryId **out) {
    Entry *x = ENT(e); pthread_mutex_lock(&x->mu);
    size_t n = x->deps.len; *out = n ? malloc(n * sizeof(EntryId)) : NULL; require(!n || *out, "out of memory");
    if (n) memcpy(*out, x->deps.data, n * sizeof(EntryId));
    pthread_mutex_unlock(&x->mu); return n;
}
uint64_t eval_entry_env(EntryId e) { return ENT(e)->env; }
size_t eval_entry_steps(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); size_t s = x->steps; pthread_mutex_unlock(&x->mu); return s; }
size_t eval_root_occurrences(EntryId **out) {
    pthread_mutex_lock(&E.roots_mu);
    size_t n = E.roots.len; *out = n ? malloc(n * sizeof(EntryId)) : NULL; require(!n || *out, "out of memory");
    if (n) memcpy(*out, E.roots.data, n * sizeof(EntryId));
    pthread_mutex_unlock(&E.roots_mu); return n;
}

/* DELIVER is counted here, on the common delivery path, for ready hits and
 * for publication alike; the resumed frame step is counted when the RESUME
 * job executes (EVAL_STEP). Delivery never happens under an entry lock. */
static void deliver(Cont *k, EvalResult *r) { add_count(&E.ev.deliver); enqueue_resume(k, r); }

/* publication: the result, the answer's residual and receipt, and the
 * dependency set (direct reads ∪ the READY children's recorded reads, §79.1) */
static void publish_with(EntryId eid, EvalResult *r, RefId residual, uint64_t receipt) {
    Entry *e = ENT(eid);
    require(r->cls != R_NO_OBSERVATION, "no observation is never a published value");
    bool success = r->cls != R_INVALID;
    /* children's dependencies, collected outside the entry lock */
    pthread_mutex_lock(&e->mu);
    size_t nd = e->deps.len; EntryId *kids = nd ? malloc(nd * sizeof(EntryId)) : NULL; require(!nd || kids, "out of memory");
    if (nd) memcpy(kids, e->deps.data, nd * sizeof(EntryId));
    pthread_mutex_unlock(&e->mu);
    VEC(uint64_t) acc = {0};
    for (size_t i = 0; i < nd; i++) {
        Entry *c = ENT(kids[i]); if (c == e) continue;
        pthread_mutex_lock(&c->mu);
        if (c->state == E_READY) for (size_t k = 0; k + 1 < c->gdeps.len; k += 2) { vec_push(&acc, c->gdeps.data[k]); vec_push(&acc, c->gdeps.data[k + 1]); }
        pthread_mutex_unlock(&c->mu);
    }
    free(kids);
    fine_bump(FC_LOCK_ATTEMPTS); pthread_mutex_lock(&e->mu);
    require(e->state == E_RUNNING, "publish into an entry that is not running");
    for (size_t k = 0; k + 1 < acc.len; k += 2) gdeps_add(e, acc.data[k], acc.data[k + 1]);
    vec_free(&acc);
    pthread_mutex_unlock(&e->mu);
    /* §76.3 / §78: the residual is head-normal under this face by
     * construction (an introduction, or an eliminator rebuilt around a
     * neutral residual); its own key receives the same answer without
     * running a body — an alias publication. A key already claimed by
     * another producer is left alone. The alias is published before the
     * source becomes READY, so a consumer woken by the source's answer finds
     * the residual's key already answered (no window in which the source is
     * observable and its residual key is not). */
    if (success && residual && residual != e->ref) {
        size_t ns; const uint64_t *S = dimset_get(ref_support(residual), &ns);
        FaceId reta = fc_project(e->face, S, ns);
        if (fc_entails(reta, ref_required(residual))) {
            EntryId aid = entry_intern(residual, reta);
            if (aid != eid) {
                Entry *a = ENT(aid);
                pthread_mutex_lock(&a->mu);
                if (a->state == E_UNEVALUATED) {
                    pthread_mutex_lock(&e->mu); for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) gdeps_add(a, e->gdeps.data[k], e->gdeps.data[k + 1]); pthread_mutex_unlock(&e->mu);
                    /* §93 (R1): the alias answers at its own boundary — a distinct
                     * immutable descriptor whose head is the residual itself (system
                     * branches retained); the source's original expression stays in
                     * the source result and provenance, never at a smaller or
                     * weaker-faced key */
                    a->result = r->cls == R_SYSTEM ? result_system(residual, r->nbr, r->faces, r->terms) : result_new(r->cls, residual);
                    a->residual = residual; a->receipt = rc_refl(residual); a->is_alias = true;
                    __atomic_store_n(&a->state, E_READY, __ATOMIC_RELEASE);
                }
                pthread_mutex_unlock(&a->mu);
            }
        }
    }
    fine_bump(FC_LOCK_ATTEMPTS); pthread_mutex_lock(&e->mu);
    e->result = r;
    e->residual = success ? residual : 0; e->receipt = success ? receipt : 0;
    e->n_pub++;
    e->n_deliver += e->waiters.len;
    __atomic_store_n(&e->state, E_READY, __ATOMIC_RELEASE);
    Cont **ws = e->waiters.data; size_t n = e->waiters.len;
    e->waiters.data = NULL; e->waiters.len = e->waiters.cap = 0;
    pthread_mutex_unlock(&e->mu);
    add_count(&E.ev.publish);
    for (size_t i = 0; i < n; i++) { fine_bump(FC_WAITERS_DELIVERED); deliver(ws[i], r); }
    free(ws);
}
/* a result that is its own residual (introduction, free neutral, system) */
static void publish(EntryId eid, EvalResult *r) { publish_with(eid, r, r->ref, r->ref ? rc_refl(r->ref) : 0); }
static RefId residual_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); RefId r = c->residual; pthread_mutex_unlock(&c->mu); return r; }
static uint64_t receipt_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); uint64_t r = c->receipt; pthread_mutex_unlock(&c->mu); return r; }

static bool validate_occurrence(RefId t, FaceId chi) {
    /* the ambient face must entail the reference's required face (which
     * already folds in the required faces of its free variables) */
    return fc_entails(chi, ref_required(t));
}

void eval_request(RefId t, FaceId chi, Cont *k) {
    if (fc_is_false(chi)) { deliver(k, result_new(R_NO_OBSERVATION, t)); return; }
    if (!validate_occurrence(t, chi)) { deliver(k, result_invalid("occurrence outside its required face")); return; }
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    FaceId eta = fc_project(chi, S, n);
    EntryId eid = entry_intern(t, eta);
    Entry *e = ENT(eid);
    k->child = eid;
    add_count(&E.ev.request);
    /* §60 trace: the consumer occurrence (owner, slot, requested key) */
    if (k->kind == K_ROOT || k->kind == K_EXTERNAL) { pthread_mutex_lock(&E.roots_mu); require(E.roots.len < E.roots.cap, "eval: roots reservation exhausted"); E.roots.data[E.roots.len++] = eid; pthread_mutex_unlock(&E.roots_mu); }
    else { Entry *o = ENT(k->dest); pthread_mutex_lock(&o->mu); vec_push(&o->deps, eid); pthread_mutex_unlock(&o->mu); }
    /* readiness check and waiter registration under the same lock (§10) */
    fine_bump(FC_LOCK_ATTEMPTS); pthread_mutex_lock(&e->mu);
    e->n_req++;
    if (e->state == E_READY) {
        EvalResult *r = e->result;
        e->n_deliver++;
        pthread_mutex_unlock(&e->mu);
        add_count(&E.ev.ready_hit); reuse_bump(REUSE_READY_HIT); fine_bump(FC_WAITERS_DELIVERED);
        deliver(k, r);                       /* after unlock */
        return;
    }
    if (e->state == E_RUNNING) {
        vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
        pthread_mutex_unlock(&e->mu);
        add_count(&E.ev.running_hit); reuse_bump(REUSE_RUNNING_JOIN);
        return;
    }
    /* §78.3–78.4: before the body runs, look for a completed receipt this
     * producer can continue from (computed outside the entry lock; the
     * launcher installs it) */
    pthread_mutex_unlock(&e->mu);
    RefId ad = 0; uint64_t adp = 0; EntryId ads = 0;
    bool have_ad = find_adapter(t, e->shape, eta, eid, &ad, &adp, &ads);
    pthread_mutex_lock(&e->mu);
    if (e->state == E_READY) { EvalResult *r = e->result; e->n_deliver++; pthread_mutex_unlock(&e->mu); add_count(&E.ev.ready_hit); reuse_bump(REUSE_READY_HIT); deliver(k, r); return; }
    if (e->state == E_RUNNING) { vec_push(&e->waiters, k); pthread_mutex_unlock(&e->mu); add_count(&E.ev.running_hit); reuse_bump(REUSE_RUNNING_JOIN); return; }
    if (have_ad) { e->adapter = ad; e->adapter_prefix = adp; e->adapter_src = ads; }
    /* U → R({c}) + EVAL(K) is one transition (§26): the task is enqueued
     * before RUNNING can be observed by anyone else, so no requester can see
     * a running key whose evaluator is not yet runnable. */
    e->state = E_RUNNING;
    vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
    reserve_job();                       /* outstanding += 1 before RUNNING can be observed */
    pthread_mutex_unlock(&e->mu);
    add_count(&E.ev.launch);
    add_count(&E.tasks_created);
    Task job; memset(&job, 0, sizeof job); job.entry = eid;
    enqueue_reserved(job);               /* enqueue after the entry lock is released */
}

static void forward(RefId t, FaceId chi, EntryId dest) { eval_request(t, chi, cont_new(K_FORWARD, dest, chi)); }
/* forward with the receipt of the rules applied so far (§78.2) */
static void forward_rc(RefId t, FaceId chi, EntryId dest, uint64_t prefix) { Cont *k = cont_new(K_FORWARD, dest, chi); k->prefix = prefix; eval_request(t, chi, k); }

/* ---------------- dispatch ---------------- */

static void eval_system_head(RefId t, const Head *h, FaceId chi, EntryId dest) {
    size_t nb = h->n / 2;
    FaceId *faces = malloc((nb ? nb : 1) * sizeof(FaceId));
    RefId *terms = malloc((nb ? nb : 1) * sizeof(RefId));
    require(faces && terms, "out of memory");
    size_t kept = 0;
    FaceId uni = fc_false();
    for (size_t k = 0; k < nb; k++) {
        FaceId phi = h->f[2 * k].id;
        RefId tk = h->f[2 * k + 1].id;
        if (fc_is_false(fc_meet(chi, phi))) continue;           /* inconsistent branch dropped */
        if (fc_entails(chi, phi)) { free(faces); free(terms); reuse_bump(REUSE_SYSTEM_RULE); forward_rc(tk, chi, dest, rc_rule(RR_SYSTEM, phi, 0)); return; }
        faces[kept] = phi; terms[kept] = tk; kept++;
        uni = fc_join(uni, phi);
    }
    if (!fc_entails(chi, uni)) { free(faces); free(terms); publish(dest, result_invalid("system does not cover the ambient face")); return; }
    reuse_bump(REUSE_SYSTEM_RULE);
    publish_with(dest, result_system(t, kept, faces, terms), t, rc_rule(RR_SYSTEM, 0, 0));
    free(faces); free(terms);
}

static void evaluate(EntryId eid) {
    Entry *e = ENT(eid);
    pthread_mutex_lock(&e->mu);
    require(e->state == E_RUNNING && e->runs == 0, "a key is evaluated by exactly one task");
    e->runs++;
    pthread_mutex_unlock(&e->mu);
    RefId t = e->ref;
    FaceId chi = e->face;      /* evaluate under the key's face, not a requester's */
    if (e->adapter) {
        /* §78.3: continue from the completed receipt: observe the specialized
         * / restricted residual; its own further reduction is ordinary work */
        reuse_bump(REUSE_RECEIPT_INSTANCE);
        forward_rc(e->adapter, chi, eid, e->adapter_prefix);
        return;
    }
    reuse_bump(REUSE_EVAL_BODY);
    if (ref_is_var(t)) { publish(eid, result_new(R_NEUTRAL, t)); return; }
    Head h; open_ref(t, &h);
    switch (h.tag) {
    case T_UNIVERSE: case T_PI: case T_SIGMA: case T_LAM: case T_PAIR: case T_PATH: case T_PLAM:
        publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLOBAL: {
        /* a declared symbol without a body is an opaque constant: neutral;
         * either way the observed revision is a dependency of the answer (§79.1) */
        SymbolId sym = (SymbolId)h.payload; uint64_t rev = global_revision(sym);
        pthread_mutex_lock(&e->mu); gdeps_add(e, sym, rev); pthread_mutex_unlock(&e->mu);
        if (!global_body(sym)) publish(eid, result_new(R_NEUTRAL, t));
        else { reuse_bump(REUSE_GLOBAL_UNFOLD); forward_rc(unfold_global(t), chi, eid, rc_rule(RR_UNFOLD, sym, rev)); }
        break;
    }
    case T_APP: {
        Cont *k = cont_new(K_APP, eid, chi); k->orig = t; k->a = h.f[1].id;
        eval_request(h.f[0].id, chi, k);
        break;
    }
    case T_FST: case T_SND: {
        Cont *k = cont_new(h.tag == T_FST ? K_FST : K_SND, eid, chi); k->orig = t;
        eval_request(h.f[0].id, chi, k);
        break;
    }
    case T_PAPP: {
        IntervalId s = h.f[4].id;
        if (fc_entails(chi, fc_endpoint(s, 0))) { reuse_bump(REUSE_ENDPOINT); forward_rc(h.f[1].id, chi, eid, rc_rule(RR_ENDPOINT, 0, 0)); break; }
        if (fc_entails(chi, fc_endpoint(s, 1))) { reuse_bump(REUSE_ENDPOINT); forward_rc(h.f[2].id, chi, eid, rc_rule(RR_ENDPOINT, 1, 0)); break; }
        Cont *k = cont_new(K_PAPP, eid, chi); k->orig = t; k->s = s;
        eval_request(h.f[3].id, chi, k);
        break;
    }
    case T_GLUE_TYPE:
        if (fc_entails(chi, h.f[1].id)) { reuse_bump(REUSE_GLUE_RULE); forward_rc(h.f[2].id, chi, eid, rc_rule(RR_GLUE, h.f[1].id, 0)); }
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_GLUE_INTRO:
        if (fc_entails(chi, h.f[1].id)) { reuse_bump(REUSE_GLUE_RULE); forward_rc(h.f[4].id, chi, eid, rc_rule(RR_GLUE, h.f[1].id, 1)); }
        else publish(eid, result_new(R_INTRODUCTION, t));
        break;
    case T_UNGLUE:
        if (fc_entails(chi, h.f[1].id)) { reuse_bump(REUSE_GLUE_RULE); forward_rc(mk_app(mk_fst(h.f[3].id), h.f[4].id), chi, eid, rc_rule(RR_GLUE, h.f[1].id, 2)); }
        else { Cont *k = cont_new(K_UNGLUE, eid, chi); k->orig = t; eval_request(h.f[4].id, chi, k); }
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
        FaceId phi = h.f[1].id;
        if (fc_entails(chi, phi)) {            /* tube coverage first */
            reuse_bump(REUSE_COMP_EXPAND);
            forward_rc(apply_dim_binder(t, 0, 2, iv_one()), chi, eid, rc_rule(RR_COMP_TUBE, phi, 0));
            break;
        }
        DimOpen fam = resolve_dim_binder(t, 0, 0);
        DimOpen tube = resolve_dim_binder(t, 0, 2);
        require(fam.j == tube.j, "family and tube must share the composition dimension");
        Cont *k = cont_new(K_COMP_FAMILY, eid, chi);
        k->orig = t; k->j = fam.j; k->tube = tube.body; k->phi = phi; k->cap = h.f[3].id;
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
    case K_APP: out = mk_app(scrut, h.f[1].id); break;
    case K_FST: out = mk_fst(scrut); break;
    case K_SND: out = mk_snd(scrut); break;
    case K_PAPP: {
        DimOpen B = resolve_dim_binder(k->orig, 0, 0);
        out = mk_papp_lv(levels_first(h.levels), B.j, B.body, h.f[1].id, h.f[2].id, scrut, h.f[4].id);
        break;
    }
    case K_UNGLUE: out = mk_unglue_lv(levels_first(h.levels), h.f[0].id, h.f[1].id, h.f[2].id, h.f[3].id, scrut); break;
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
    require(g, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
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
    reuse_bump(REUSE_SYSTEM_RULE);
    publish_with(dest, res, owner, rc_rule(RR_SYSTEM_DIST, 0, 0));
}

static void distribute(const Cont *k, const EvalResult *sys) {
    RefId *terms = malloc((sys->nbr ? sys->nbr : 1) * sizeof(RefId));
    require(terms, "out of memory");
    for (size_t i = 0; i < sys->nbr; i++) terms[i] = rebuild_elim(k, sys->terms[i]);
    publish_branchwise(k->dest, k->chi, sys->nbr, sys->faces, terms);
    free(terms);
}

static void resume_comp_family(Cont *k, EvalResult *r) {
    if (r->cls == R_NEUTRAL) {
        /* rebuild the composition around the residual family: no re-evaluation of the family */
        Head ho; open_ref(k->orig, &ho); uint64_t lv = levels_first(ho.levels); if (ho.levels == LEVELS_NONE) lv = LEVEL_NONE; head_free(&ho);
        RefId fam_res = residual_of(k->child);
        RefId residual = fam_res ? mk_comp_lv(lv, k->j, fam_res, k->phi, k->tube, k->cap) : k->orig;
        publish_with(k->dest, result_new(R_NEUTRAL, k->orig), residual, rc_rule(RR_CONG_COMP, receipt_of(k->child), 0));
        return;
    }
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
    RefId out = comp_clause(k->j, r->ref, k->phi, k->tube, k->cap, ENT(k->dest)->face);
    if (!out) { publish(k->dest, result_invalid("composition in a family whose head is not a type former or lacks its universe annotation")); return; }
    reuse_bump(REUSE_COMP_EXPAND);
    forward_rc(out, k->chi, k->dest, rc_seq(rc_rule(RR_CONG_COMP, receipt_of(k->child), 0), rc_rule(RR_COMP_EXPAND, 0, 0)));
}

static void resume(Cont *k, EvalResult *r) {
    switch (k->kind) {
    case K_ROOT: {
        RootBox *b = k->root;
        pthread_mutex_lock(&b->mu); b->result = r; b->done = true; pthread_cond_broadcast(&b->cv); pthread_mutex_unlock(&b->mu);
        /* wake clients waiting for either their root or quiescence */
        pthread_mutex_lock(&E.q_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.q_mu);
        rootbox_release(b);
        return;
    }
    case K_EXTERNAL: k->ext_fn(k->ext_ctx, r); return;
    case K_BRANCH: resume_branch(k, r); return;
    default: break;
    }
    if (r->cls == R_NO_OBSERVATION || r->cls == R_INVALID) { publish_with(k->dest, r, 0, 0); return; }
    if (k->kind == K_FORWARD) { publish_with(k->dest, r, residual_of(k->child), rc_seq(k->prefix, receipt_of(k->child))); return; }
    if (k->kind == K_COMP_FAMILY) { resume_comp_family(k, r); return; }
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    uint64_t cong = rc_rule(cong_of[k->kind], receipt_of(k->child), 0);
    if (r->cls == R_NEUTRAL) {
        /* §78.2: the residual is the eliminator rebuilt around the scrutinee's residual */
        RefId sres = residual_of(k->child);
        publish_with(k->dest, result_new(R_NEUTRAL, k->orig), sres ? rebuild_elim(k, sres) : k->orig, cong);
        return;
    }
    if (r->cls == R_SYSTEM) { distribute(k, r); return; }
    /* introduction under an eliminator */
    Head h; open_ref(r->ref, &h);
    switch (k->kind) {
    case K_APP:
        if (h.tag != T_LAM) { publish(k->dest, result_invalid("application of a non-function introduction")); break; }
        reuse_bump(REUSE_BETA);
        forward_rc(apply_term_binder(r->ref, 0, 1, k->a), k->chi, k->dest, rc_seq(cong, rc_rule(RR_BETA, 0, 0)));
        break;
    case K_FST: case K_SND:
        if (h.tag != T_PAIR) { publish(k->dest, result_invalid("projection of a non-pair introduction")); break; }
        reuse_bump(k->kind == K_FST ? REUSE_FST : REUSE_SND);
        forward_rc(h.f[k->kind == K_FST ? 0 : 1].id, k->chi, k->dest, rc_seq(cong, rc_rule(k->kind == K_FST ? RR_FST : RR_SND, 0, 0)));
        break;
    case K_PAPP:
        if (h.tag != T_PLAM) { publish(k->dest, result_invalid("path application of a non-path introduction")); break; }
        reuse_bump(REUSE_PATH_BETA);
        forward_rc(apply_dim_binder(r->ref, 0, 0, k->s), k->chi, k->dest, rc_seq(cong, rc_rule(RR_PATH_BETA, 0, 0)));
        break;
    case K_UNGLUE:
        if (h.tag != T_GLUE_INTRO) { publish(k->dest, result_invalid("unglue of a non-glue introduction")); break; }
        reuse_bump(REUSE_GLUE_RULE);
        forward_rc(h.f[5].id, k->chi, k->dest, rc_seq(cong, rc_rule(RR_GLUE, 0, 3)));
        break;
    default: die("unreachable continuation kind");
    }
    head_free(&h);
}

/* one elementary frame step, or one local rule of the evaluator's net
 * (counted in the net's rule classes, not as an evaluator step) */
static void execute_task(Task t);
static void execute(Task t) {
    /* §94: an evaluator task is owned, unfinished work of the thread running
     * it; a kernel continuation may suspend inside it (its stack retains the
     * task, the entry stays RUNNING, the outstanding count is held) and is
     * marked `in_eval` so a waiter can name it as its dependency */
    KCont *k = kc_current(); bool outer = k && !k->in_eval; if (outer) k->in_eval = true;
    execute_task(t);
    if (outer) k->in_eval = false;
}
/* §94: a wait for the machine's progress — a continuation yields, naming a
 * continuation suspended inside an evaluator task when there is one (its
 * job is then driven as this job's dependency); a plain thread waits */
static void eval_wait_locked(void) {
    KCont *k = kc_current();
    if (!k) { pthread_cond_wait(&E.idle_cv, &E.q_mu); return; }
    KCont *held[4]; size_t n = kc_suspended_in_eval(held, 4);
    kc_wait(&E.idle_cv, &E.q_mu, n ? held[0] : NULL);
}
static void execute_task(Task t) {
    if (t.is_pair) { net_step_pair(&E.net, t.pair); return; }
    add_count(&E.ev.eval_step);
    { EntryId owner = t.is_resume ? t.k->dest : t.entry;    /* §60 trace: the frame step belongs to the producer it advances */
      if (owner && !(t.is_resume && (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL))) { Entry *o = ENT(owner); pthread_mutex_lock(&o->mu); o->steps++; pthread_mutex_unlock(&o->mu); } }
    if (t.is_resume) { resume(t.k, t.r); cont_release(t.k); }   /* single consumer: released once resumed */
    else evaluate(t.entry);
}

/* §43 FORWARD_RESULT(K): the receiver's request; delivery publishes into K */
void eval_forward_result(EntryId K, RefId v) { forward_rc(v, ENT(K)->face, K, rc_rule(RR_IDENTITY_APPLY, v, 0)); }

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
        while (E.outstanding > 0) eval_wait_locked();
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

EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status) {
    RootBox *box = calloc(1, sizeof *box); require(box, "out of memory");
    pthread_mutex_init(&box->mu, NULL); pthread_cond_init(&box->cv, NULL); box->refs = 2;
    Cont *root = cont_new(K_ROOT, 0, chi);
    root->root = box;
    eval_request(t, chi, root);
    if (E.nworkers) {
        /* wait for this root, or for quiescence of the whole machine (stuck) */
        pthread_mutex_lock(&E.q_mu);
        for (;;) {
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            if (d || E.outstanding == 0) break;
            eval_wait_locked();
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
            bool queued = E.qhead < E.queue.len || net_pending_pairs_locked(&E.net) > 0;
            if (d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
            if (!queued) eval_wait_locked();
            pthread_mutex_unlock(&E.q_mu);
        }
    }
    pthread_mutex_lock(&box->mu);
    bool done = box->done; EvalResult *out = box->result;
    pthread_mutex_unlock(&box->mu);
    /* a stuck root keeps its continuation as a waiter; the box survives
     * until that continuation is resumed or the machine is freed */
    rootbox_release(box);
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

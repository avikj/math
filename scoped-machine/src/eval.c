#include "eval.h"
#include <sys/mman.h>
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
    int refs;                 /* LIVE-CUT-ADOPTION §5: the creator and every branch Cut retain the join; the last release frees it */
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
    RefId req;                       /* the reference this continuation requested (§84.2: a child's prefix is lifted only when it is a fact about this exact reference) */
    EntryId child;                   /* the entry this continuation waits on */
    EntryId prefix_premise;          /* BRANCH: immutable READY scrutinee used by its guarded entry receipt */
    /* LIVE-CUT-ADOPTION: a producer-owned request is a ticket of a Cut (its
     * logical slot); `gen` is the ticket's generation (requested residual,
     * prefix receipt and dependency certificate). In a resume view, `aq` /
     * `ad` carry the winning ticket's prefix receipt and certificate. */
    struct Cut *cut; struct Gen *gen;
    uint64_t aq;
};

/* a job: EVALUATE(entry), RESUME(k, r), or a NET_PAIR of the evaluator's net (§43) */
/* op (LIVE-CUT-ADOPTION): 0 for the jobs above; subscription, history replay,
 * publication notice, proposal preparation, installation, the replacement
 * request and instantiation-edge watches are administrative jobs of the same
 * scheduler, each one bounded step owned by the Cut's producer */
enum { OP_NONE = 0, OP_SUB, OP_REPLAY, OP_FACTNOTE, OP_PREPARE, OP_INSTALL, OP_REQUEST, OP_EDGE, OP_EXT };
typedef struct { bool is_resume, is_pair, is_notify; EntryId entry; Cont *k; EvalResult *r; Active pair; const struct PrefixFact *fact; size_t idx, limit; bool catchup;
                 uint8_t op; void *p, *p2; RefId r1, r2; uint64_t sigma; } Task;   /* is_notify: §84.2 deliver `fact` of `entry` to its waiter `idx` (one waiter per task) */
typedef struct { VEC(EntryId) entries; VEC(RefId) refs;
                 struct Sub *subs; const struct PrefixFact *sfacts;   /* LIVE-CUT-ADOPTION §2: subscriptions and committed facts of this shape, newest first (under sub_mu) */
               } ShapeSide;

/* ---- LIVE-CUT-ADOPTION records ----
 * Gen: one generation of a Cut — its residual r with key face, the receipt
 * q : s0 ⇒* r (0 = REFL), the dependency certificate, the generation it
 * replaced, and the owner's occurrence ordinal of its request. Immutable once
 * installed except the occurrence ordinal (written under the owner's lock).
 * The generation token is the record's identity, retained by the Cut, its
 * ticket, its subscriptions and every proposal captured at it (no reuse of a
 * live identity; no counter). */
typedef struct Gen {
    int refs;
    RefId r; FaceId eta; uint64_t q;
    uint64_t *d; size_t nd;
    struct Gen *prev;
    size_t dep_idx; bool have_dep;
    bool dead;              /* superseded or resumed: its subscriptions are detached lazily */
} Gen;
typedef enum { CUT_WAITING = 0, CUT_RESUMING, CUT_CLOSED } CutState;
typedef struct Cut {
    int refs; pthread_mutex_t mu;
    EntryId owner; RefId s0; FaceId psi;
    Cont K;                 /* immutable resume recipe (no ticket fields) */
    Gather *join;           /* K_BRANCH: the retained join handle */
    CutState state; Gen *cur;
    size_t installs;
} Cut;
/* a subscription: owned by its predecessor's next pointer (or the shape head) and by each job at it;
 * a node owns its next pointer's reference, so a detached node still leads into the list */
typedef struct Sub { int refs; Cut *cut; Gen *gen; uint64_t sigma; struct Sub *next; } Sub;
typedef struct Proposal {
    Cut *cut; Gen *gen; const struct PrefixFact *f; uint64_t sigma;
    int phase; size_t k; bool revalidating;
    RefId v; FaceId veta; uint64_t adrc, q; Words d; uint64_t stamp;
} Proposal;
typedef struct { int state; RefId v; FaceId veta; uint64_t adrc; } PrepMemo;   /* state: 0 absent, 1 applicable, 2 inapplicable, 3 being computed (a join) */
static void ticket_release(Cont *k);
static void sub_unref(Sub *n);
static void eval_edge_hook(RefId dest, RefId src, uint64_t sigma);

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
    Chunked qtab; size_t qhead, qtail;   /* V21 R4: a segmented queue over monotone positions; consumed chunks are retired */
    pthread_mutex_t q_mu; pthread_cond_t q_cv, idle_cv;
    size_t outstanding;            /* §35: queued jobs + executing jobs (+ reserved launches) */
    bool stop;
    pthread_t *workers; size_t nworkers;
    /* rooted results (immutable payloads) */
    EvalResult *results; pthread_mutex_t res_mu;
    /* LIVE-CUT-ADOPTION: subscriptions (per shape, newest first) and their
     * publication partition (one lock, constant sections); every subscription
     * node for teardown; the shared preparation cache; held jobs (scheduler
     * policy); counters */
    pthread_mutex_t sub_mu; size_t live_subs;
    Interner prep_keys; Chunked prep_tab; pthread_mutex_t prep_mu;
    pthread_mutex_t held_mu; Task *held; size_t nheld, capheld;
    bool (*hold)(const EvalTaskInfo *, void *); void *hold_ctx;
    bool live;
    /* jobs of another layer (eval_job): their own FIFO of the same scheduler, taken only by plain threads
     * (never by an evaluation nested inside a kernel continuation), counted apart from `outstanding` */
    struct ExtNode *ext_head, *ext_tail; size_t ext_n;
    XCount cevx[sizeof(EvalCutEvents) / sizeof(size_t)];
    /* the evaluator's net (§43): APPLY_TRANSFORM / CONTINUE_REFERENCE pairs
     * are jobs of this scheduler (one outstanding count) */
    Net net; SchedPolicy pair_policy;
    /* §60 trace: root / external consumer occurrences in request order */
    Chunked roots_tab; size_t n_roots; pthread_mutex_t roots_mu;   /* V21 R4: extensible, stable */
    /* counters */
    XCount tasks_created;
    XCount evx[sizeof(EvalEvents) / sizeof(size_t)];      /* V23 R5: exact event counts (EvalEvents field order) */
    SchedPolicy policy; uint64_t rng;
    /* §84.2 committed prefix facts (immutable; reclaimed with the machine) */
    PrefixFact *facts; uint64_t fact_ids; XCount pevx[sizeof(EvalPrefixEvents) / sizeof(size_t)];
} E;

/* V23 R5: the evaluator's event counts are exact (xcount.h); the public
 * structs are checked word projections of them */
#define XSLOT(arr, T, f) (&E.arr[offsetof(T, f) / sizeof(size_t)])
#define XINC(arr, T, f) xc_inc(XSLOT(arr, T, f))
static void xproject(const XCount *a, size_t *out, size_t n, const char *what) { for (size_t i = 0; i < n; i++) out[i] = (size_t)xs_u64_checked(xc_snap(&a[i]), what); }
EvalEvents eval_events(void) {
    EvalEvents v; xproject(E.evx, (size_t *)&v, sizeof v / sizeof(size_t), "evaluator event");
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
#define NETX(f) (size_t)xs_u64_checked(xc_snap2((const uint64_t *)&E.net.f, &E.net.f##_cx), "net event")
    v.apply = NETX(n_apply); v.continue_ref = NETX(n_continue); v.op = NETX(n_op); v.eval_deliver = NETX(n_eval_deliver); v.retries = NETX(retries);
#undef NETX
    return v;
}
static uint64_t rng_next(void) { E.rng ^= E.rng << 13; E.rng ^= E.rng >> 7; E.rng ^= E.rng << 17; return E.rng; }

static void *worker_main(void *arg);

void eval_init(void) {
    memset(&E, 0, sizeof E);
    pthread_mutex_init(&E.roots_mu, NULL);
    chunked_init(&E.roots_tab, sizeof(EntryId)); E.n_roots = 0;
    interner_init(&E.keys); chunked_init(&E.heads, sizeof(EntryId));
    interner_init(&E.shape_ids); chunked_init(&E.shape_side, sizeof(ShapeSide));
    interner_init(&E.receipts);
    chunked_init(&E.entries, sizeof(Entry));
    pthread_mutex_init(&E.entries_mu, NULL);
    pthread_mutex_init(&E.q_mu, NULL);
    chunked_init(&E.qtab, sizeof(Task)); E.qhead = E.qtail = 0;
    pthread_cond_init(&E.q_cv, NULL);
    pthread_cond_init(&E.idle_cv, NULL);
    pthread_mutex_init(&E.res_mu, NULL);
    pthread_mutex_init(&E.sub_mu, NULL); pthread_mutex_init(&E.prep_mu, NULL); pthread_mutex_init(&E.held_mu, NULL);
    interner_init(&E.prep_keys); chunked_init(&E.prep_tab, sizeof(PrepMemo));
    net_init(&E.net);
    net_share_scheduler(&E.net, &E.q_mu, &E.q_cv, &E.outstanding);
    E.net.policy = 1;   /* pairs FIFO by default */
    term_edge_hook = eval_edge_hook;
    __atomic_store_n(&E.live, true, __ATOMIC_RELEASE);
    kc_session(KC_MOD_EVAL, true);
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
static void gather_ref(Gather *g) { __atomic_add_fetch(&g->refs, 1, __ATOMIC_RELAXED); }
static void gather_unref(Gather *g) {
    if (!g || __atomic_sub_fetch(&g->refs, 1, __ATOMIC_ACQ_REL) != 0) return;
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

static void task_discard(Task t);
typedef struct ExtNode { Task t; struct ExtNode *next; } ExtNode;
static void ext_push(Task t);
void eval_free(void) {
    stop_workers();
    __atomic_store_n(&E.live, false, __ATOMIC_RELEASE);
    if (term_edge_hook == eval_edge_hook) term_edge_hook = NULL;
    chunked_free(&E.roots_tab); E.n_roots = 0; pthread_mutex_destroy(&E.roots_mu);
    net_free(&E.net);           /* after the workers: a pending pair is a job */
    /* LIVE-CUT-ADOPTION §5 teardown (closed-session precondition: no client
     * can still use these objects): unrun and held jobs and pending tickets
     * are retired without any semantic delivery */
    for (size_t i = E.qhead; i < E.qtail; i++) task_discard(*(Task *)chunked_get(&E.qtab, i));
    E.qhead = E.qtail;
    for (ExtNode *x = E.ext_head, *nx; x; x = nx) { nx = x->next; free(x); }
    E.ext_head = E.ext_tail = NULL; E.ext_n = 0;
    for (size_t i = 0; i < E.nheld; i++) task_discard(E.held[i]);
    free(E.held); E.held = NULL; E.nheld = E.capheld = 0;
    for (size_t i = 0; i < E.n_entries; i++) {
        Entry *e = ENT(i + 1);
        for (size_t w = 0; w < e->waiters.len; w++) {                 /* suspended forever: stuck demands */
            Cont *k = e->waiters.data[w];
            if (k->cut) { XINC(cevx, EvalCutEvents, retired_tickets); ticket_release(k); continue; }
            if (k->kind == K_EXTERNAL && k->ext_free) k->ext_free(k->ext_ctx);
            if (k->kind == K_ROOT) rootbox_release(k->root);
            free(k);
        }
        vec_free(&e->waiters);
    }
    { size_t ns = interner_count(&E.shape_ids); for (size_t i = 0; i < ns; i++) { ShapeSide *ss = chunked_peek(&E.shape_side, i); if (ss && ss->subs) { Sub *h = ss->subs; ss->subs = NULL; sub_unref(h); } } }
    for (size_t i = 0; i < E.n_entries; i++) {
        Entry *e = ENT(i + 1);
        vec_free(&e->deps); vec_free(&e->dep_hist); vec_free(&e->gdeps);
        reuse_scope_unref(e->scope);
        pthread_mutex_destroy(&e->mu);
    }
    { size_t ns = interner_count(&E.shape_ids); for (size_t i = 0; i < ns; i++) { ShapeSide *ss = chunked_peek(&E.shape_side, i); if (ss) { vec_free(&ss->entries); vec_free(&ss->refs); } } }
    interner_free(&E.keys); chunked_free(&E.heads);
    interner_free(&E.shape_ids); chunked_free(&E.shape_side);
    interner_free(&E.receipts);
    chunked_free(&E.entries);
    for (EvalResult *r = E.results, *n; r; r = n) { n = r->all_next; free(r->faces); free(r->terms); free(r); }
    E.results = NULL;
    for (PrefixFact *f = E.facts, *n; f; f = n) { n = f->all_next; free((void *)f->gdeps); free(f); }
    E.facts = NULL;
    interner_free(&E.prep_keys); chunked_free(&E.prep_tab);
    pthread_mutex_destroy(&E.sub_mu); pthread_mutex_destroy(&E.prep_mu); pthread_mutex_destroy(&E.held_mu);
    chunked_free(&E.qtab); E.qhead = E.qtail = 0;
    pthread_mutex_destroy(&E.entries_mu); pthread_mutex_destroy(&E.q_mu); pthread_mutex_destroy(&E.res_mu);
    pthread_cond_destroy(&E.q_cv); pthread_cond_destroy(&E.idle_cv);
    memset(&E, 0, sizeof E);
    reuse_scope_reclaim();
    kc_session(KC_MOD_EVAL, false);
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

/* ---- LIVE-CUT-ADOPTION ownership: generations, Cuts, tickets, subscriptions ---- */
static void gen_ref(Gen *g) { if (g) __atomic_add_fetch(&g->refs, 1, __ATOMIC_RELAXED); }
static void gen_unref(Gen *g) {
    while (g && __atomic_sub_fetch(&g->refs, 1, __ATOMIC_ACQ_REL) == 0) { Gen *p = g->prev; free(g->d); free(g); fine_bump(FC_CELLS_RELEASED); g = p; }
}
static Gen *gen_new(RefId r, FaceId eta, uint64_t q, uint64_t *d, size_t nd, Gen *prev) {
    Gen *g = calloc(1, sizeof *g); require(g, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    g->refs = 1; g->r = r; g->eta = eta; g->q = q; g->d = d; g->nd = nd; g->prev = prev; gen_ref(prev);
    return g;
}
static void cut_ref(Cut *c) { if (c) __atomic_add_fetch(&c->refs, 1, __ATOMIC_RELAXED); }
static void cut_unref(Cut *c) {
    if (!c || __atomic_sub_fetch(&c->refs, 1, __ATOMIC_ACQ_REL) != 0) return;
    gen_unref(c->cur); gather_unref(c->join);
    pthread_mutex_destroy(&c->mu); free(c); fine_bump(FC_CELLS_RELEASED);
    XINC(cevx, EvalCutEvents, cuts_freed);
}
/* a ticket owns one reference to its Cut and one to its generation */
static void ticket_release(Cont *k) { Cut *c = k->cut; Gen *g = k->gen; cont_release(k); gen_unref(g); cut_unref(c); }
static void sub_ref(Sub *n) { if (n) __atomic_add_fetch(&n->refs, 1, __ATOMIC_RELAXED); }
static void sub_unref(Sub *n) {   /* iterative: a freed node releases its next pointer's reference */
    while (n && __atomic_sub_fetch(&n->refs, 1, __ATOMIC_ACQ_REL) == 0) {
        Sub *nx = n->next; cut_unref(n->cut); gen_unref(n->gen); free(n); fine_bump(FC_CELLS_RELEASED);
        __atomic_sub_fetch(&E.live_subs, 1, __ATOMIC_RELAXED); XINC(cevx, EvalCutEvents, subs_freed);
        n = nx;
    }
}
static bool sub_dead(const Sub *n) { return __atomic_load_n(&n->gen->dead, __ATOMIC_ACQUIRE); }
/* under sub_mu, constant work: detach one dead node after *link (the shape head or a node's next);
 * returns the detached node, whose reference the caller drops after unlocking */
static Sub *sub_unlink_one_locked(Sub **link) {
    Sub *d = *link; if (!d || !sub_dead(d)) return NULL;
    *link = d->next; sub_ref(d->next);
    XINC(cevx, EvalCutEvents, subs_unlinked);
    return d;
}
static FaceId key_face(RefId r, FaceId psi) { size_t n; const uint64_t *S = dimset_get(ref_support(r), &n); return fc_project(psi, S, n); }
/* §2.1: commit Cut(s0, ψ, K, WAITING, g, s0, REFL, ∅); the opening
 * continuation becomes the generation-g ticket */
static void cut_open(Cont *k, RefId t, FaceId chi) {
    Cut *c = calloc(1, sizeof *c); require(c, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    pthread_mutex_init(&c->mu, NULL);
    c->refs = 1;                                  /* the ticket */
    c->owner = k->dest; c->s0 = t; c->psi = chi;
    c->K = *k; c->K.cut = NULL; c->K.gen = NULL; c->K.aq = 0;
    if (k->kind == K_BRANCH) { c->join = k->gather; gather_ref(c->join); }
    c->state = CUT_WAITING;
    c->cur = gen_new(t, key_face(t, chi), 0, NULL, 0, NULL);
    k->cut = c; k->gen = c->cur; gen_ref(k->gen);
    XINC(cevx, EvalCutEvents, cuts); XINC(cevx, EvalCutEvents, tickets);
}
static Cont *ticket_new(Cut *c, Gen *g) {
    Cont *t = calloc(1, sizeof *t); require(t, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    *t = c->K; t->cut = c; cut_ref(c); t->gen = g; gen_ref(g); t->child = 0; t->req = 0;
    return t;
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
/* the chunk the next positions need, created outside q_mu (a racing
 * candidate is retired by chunked_at); under q_mu the slot write is then a
 * stable store */
static void queue_prepare(void) { size_t at = __atomic_load_n(&E.qtail, __ATOMIC_ACQUIRE); (void)chunked_at(&E.qtab, at); (void)chunked_at(&E.qtab, at + 1); }
static void enqueue_reserved(Task t) {
    fine_bump(FC_QUEUE_OPS); fine_bump(FC_LOCK_ATTEMPTS);
    queue_prepare();
    pthread_mutex_lock(&E.q_mu);
    *(Task *)chunked_at(&E.qtab, E.qtail) = t; __atomic_store_n(&E.qtail, E.qtail + 1, __ATOMIC_RELEASE);   /* a stable slot; the chunk was created before q_mu (queue_prepare) */
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void enqueue(Task t) {
    fine_bump(FC_QUEUE_OPS); fine_bump(FC_LOCK_ATTEMPTS);
    queue_prepare();
    pthread_mutex_lock(&E.q_mu);
    E.outstanding++;
    *(Task *)chunked_at(&E.qtab, E.qtail) = t; __atomic_store_n(&E.qtail, E.qtail + 1, __ATOMIC_RELEASE);   /* a stable slot; the chunk was created before q_mu (queue_prepare) */
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
    bool have_jobs = E.qhead < E.qtail;
    if (npairs) {
        /* two queues, each with its own policy; which queue goes first is
         * itself a policy choice (FIFO: jobs first, LIFO: pairs first,
         * RANDOM: a coin) */
        bool pairs_first = !have_jobs || E.policy == POL_LIFO || (E.policy == POL_RANDOM && (rng_next() & 1));
        if (pairs_first) { memset(out, 0, sizeof *out); out->is_pair = true; require(net_pop_pair_locked(&E.net, &out->pair), "pair queue"); return true; }
    }
    if (!have_jobs) return false;
    size_t pick = E.qhead;
    if (E.policy == POL_LIFO) pick = E.qtail - 1;
    else if (E.policy == POL_RANDOM) pick = E.qhead + (size_t)(rng_next() % (E.qtail - E.qhead));
    Task *tp = (Task *)chunked_get(&E.qtab, pick), *hp = (Task *)chunked_get(&E.qtab, E.qhead);
    *out = *tp; *tp = *hp;
    E.qhead++;
    if ((E.qhead & (CHUNK_SIZE - 1)) == 0) chunked_release_chunk(&E.qtab, (E.qhead >> CHUNK_BITS) - 1);   /* a fully consumed chunk is retired */
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
static bool prefix_valid(const PrefixFact *f);
static bool adapt_residual(RefId residual, FaceId sface, MapId sigma, FaceId eta, ShapeId s, RefId *out) {
    FaceId need = map_is_identity(sigma) ? sface : fc_reindex(sface, sigma);
    if (!fc_entails(eta, need)) return false;
    RefId r = map_is_identity(sigma) ? residual : reindex(residual, sigma);
    size_t n; const uint64_t *S = dimset_get(ref_support(r), &n);
    FaceId reta = fc_project(eta, S, n);
    if (reta == eta && shape_of(r) == s) return false;
    if (!fc_entails(reta, ref_required(r))) return false;
    *out = r; return true;
}
static bool adapter_candidate(Entry *src_e, EntryId src, MapId sigma, FaceId eta, ShapeId s, RefId *out, uint64_t *prefix, const PrefixFact **fact_out) {
    pthread_mutex_lock(&src_e->mu);
    bool ok = src_e->state == E_READY && src_e->residual && gdeps_valid_locked(src_e);
    RefId residual = src_e->residual; FaceId sface = src_e->face;
    const PrefixFact *head = __atomic_load_n(&src_e->prefix_head, __ATOMIC_ACQUIRE);
    pthread_mutex_unlock(&src_e->mu);
    if (ok && adapt_residual(residual, sface, sigma, eta, s, out)) {
        *prefix = map_is_identity(sigma) ? rc(RC_RESTRICT, src, eta, 0, 3) : rc(RC_SPEC, src, sigma, 0, 3);
        *fact_out = NULL; return true;
    }
    /* A finite fact's validity is independent of its producer's final state.
     * Pin this immutable list snapshot and consider older facts when the
     * newest has inapplicable premises/face or makes no progress. */
    for (const PrefixFact *f = head; f; f = f->next) {
        fine_bump(FC_ADAPTER_STEPS);
        if (!prefix_valid(f) || !adapt_residual(f->residual, f->face, sigma, eta, s, out)) continue;
        *prefix = map_is_identity(sigma) ? rc(RC_PREFIX_RESTRICT, f->id, eta, 0, 3) : rc(RC_PREFIX_SPEC, f->id, sigma, 0, 3);
        *fact_out = f; return true;
    }
    return false;
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
static bool find_adapter(RefId t, ShapeId s, FaceId eta, EntryId self, RefId *out, uint64_t *prefix, EntryId *src_out, const PrefixFact **fact_out) {
    AdapterCursor c = {0};
    for (;;) {
        EntryId e = 0; uint64_t m = 0;
        pthread_mutex_lock(&E.entries_mu);
        int st = adapter_next_locked(&c, t, s, self, &e, &m);
        pthread_mutex_unlock(&E.entries_mu);
        fine_bump(FC_ADAPTER_STEPS);
        if (st == 0) return false;
        if (st == 3) { c.src_shape = shape_of(c.src_ref); c.have_src = true; continue; }
        if (st == 1 && adapter_candidate(ENT(e), e, m, eta, s, out, prefix, fact_out)) { *src_out = e; return true; }
    }
}
EntryState eval_entry_state(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); EntryState s = x->state; pthread_mutex_unlock(&x->mu); return s; }
FaceId eval_entry_face(EntryId e) { return ENT(e)->face; }
size_t eval_entry_count(void) { pthread_mutex_lock(&E.entries_mu); size_t n = E.n_entries; pthread_mutex_unlock(&E.entries_mu); return n; }
size_t eval_entry_runs(EntryId e) { return ENT(e)->runs; }
RefId eval_entry_ref(EntryId e) { return ENT(e)->ref; }
void eval_entry_events(EntryId e, size_t *req, size_t *deliver, size_t *pub) {
    Entry *x = ENT(e); pthread_mutex_lock(&x->mu);
    XSnap a = { x->n_req, x->n_req_cx }, b = { x->n_deliver, x->n_deliver_cx }, c = { x->n_pub, x->n_pub_cx };
    pthread_mutex_unlock(&x->mu);
    *req = (size_t)xs_u64_checked(a, "requests"); *deliver = (size_t)xs_u64_checked(b, "deliveries"); *pub = (size_t)xs_u64_checked(c, "publications");
}
size_t eval_running_count(void) { size_t c = 0, n = eval_entry_count(); for (size_t i = 1; i <= n; i++) if (eval_entry_state(i) == E_RUNNING) c++; return c; }
size_t eval_task_count(void) { return (size_t)xs_u64_checked(xc_snap(&E.tasks_created), "evaluator tasks"); }
size_t eval_entry_active_deps(EntryId e, EntryId **out) {
    Entry *x = ENT(e); pthread_mutex_lock(&x->mu);
    size_t n = 0; EntryId *o = malloc((x->deps.len ? x->deps.len : 1) * sizeof(EntryId)); require(o, "out of memory");
    for (size_t i = 0; i < x->deps.len; i++) if (!x->dep_hist.data[i]) o[n++] = x->deps.data[i];
    pthread_mutex_unlock(&x->mu); *out = o; return n;
}
size_t eval_entry_deps(EntryId e, EntryId **out) {
    Entry *x = ENT(e); pthread_mutex_lock(&x->mu);
    size_t n = x->deps.len; *out = n ? malloc(n * sizeof(EntryId)) : NULL; require(!n || *out, "out of memory");
    if (n) memcpy(*out, x->deps.data, n * sizeof(EntryId));
    pthread_mutex_unlock(&x->mu); return n;
}
uint64_t eval_entry_env(EntryId e) { return ENT(e)->env; }
size_t eval_entry_steps(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); XSnap s = { x->steps, x->steps_carry }; pthread_mutex_unlock(&x->mu); return (size_t)xs_u64_checked(s, "producer steps"); }
size_t eval_root_occurrences(EntryId **out) {
    pthread_mutex_lock(&E.roots_mu);
    size_t n = E.n_roots; *out = n ? malloc(n * sizeof(EntryId)) : NULL; require(!n || *out, "out of memory");
    for (size_t i = 0; i < n; i++) (*out)[i] = *(EntryId *)chunked_get(&E.roots_tab, i);   /* inspection (tests): a copy of the trace */
    pthread_mutex_unlock(&E.roots_mu); return n;
}

/* DELIVER is counted here, on the common delivery path, for ready hits and
 * for publication alike; the resumed frame step is counted when the RESUME
 * job executes (EVAL_STEP). Delivery never happens under an entry lock. */
static void deliver(Cont *k, EvalResult *r) { XINC(evx, EvalEvents, deliver); enqueue_resume(k, r); }

/* publication: the result, the answer's residual and receipt, and the
 * dependency set (direct reads ∪ the READY children's recorded reads, §79.1) */
static void publish_with(EntryId eid, EvalResult *r, RefId residual, uint64_t receipt) {
    Entry *e = ENT(eid);
    require(r->cls != R_NO_OBSERVATION, "no observation is never a published value");
    bool success = r->cls != R_INVALID;
    /* children's dependencies, collected outside the entry lock */
    pthread_mutex_lock(&e->mu);
    size_t nall = e->deps.len, nd = 0; EntryId *kids = nall ? malloc(nall * sizeof(EntryId)) : NULL; require(!nall || kids, "out of memory");
    for (size_t i = 0; i < nall; i++) if (!e->dep_hist.data[i]) kids[nd++] = e->deps.data[i];   /* active-slot edges only (LIVE-CUT-ADOPTION §5) */
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
    xl_add((uint64_t *)&e->n_pub, &e->n_pub_cx, 1);
    xl_add((uint64_t *)&e->n_deliver, &e->n_deliver_cx, e->waiters.len);
    __atomic_store_n(&e->state, E_READY, __ATOMIC_RELEASE);
    Cont **ws = e->waiters.data; size_t n = e->waiters.len;
    e->waiters.data = NULL; e->waiters.len = e->waiters.cap = 0;
    pthread_mutex_unlock(&e->mu);
    XINC(evx, EvalEvents, publish);
    for (size_t i = 0; i < n; i++) { fine_bump(FC_WAITERS_DELIVERED); deliver(ws[i], r); }
    free(ws);
}
/* a result that is its own residual (introduction, free neutral, system) */
static void publish(EntryId eid, EvalResult *r) { publish_with(eid, r, r->ref, r->ref ? rc_refl(r->ref) : 0); }
static RefId residual_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); RefId r = c->residual; pthread_mutex_unlock(&c->mu); return r; }
static uint64_t receipt_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); uint64_t r = c->receipt; pthread_mutex_unlock(&c->mu); return r; }
/* the slot's receipt s0 ⇒* (child's answer): the winning ticket's prefix, then the child's own receipt */
static uint64_t child_rc(const Cont *k) { return rc_seq(k->aq, receipt_of(k->child)); }

static bool validate_occurrence(RefId t, FaceId chi) {
    /* the ambient face must entail the reference's required face (which
     * already folds in the required faces of its free variables) */
    return fc_entails(chi, ref_required(t));
}

static Task prefix_catchup_locked(EntryId eid, Entry *e, size_t idx) {
    Task t; memset(&t, 0, sizeof t);
    t.fact = __atomic_load_n(&e->prefix_head, __ATOMIC_ACQUIRE);
    if (t.fact) {
        t.is_notify = true; t.entry = eid; t.idx = idx; t.limit = idx + 1; t.catchup = true;
        reserve_job();
    }
    return t;
}
static void request_inner(RefId t, FaceId chi, Cont *k);
static void sub_enqueue(Cut *c, Gen *g);
/* LIVE-CUT-ADOPTION §2: a producer-owned request opens its Cut (unless the
 * continuation already is a ticket of one: an installed replacement), the
 * ordinary request is issued through the ticket, and the subscription job of
 * that generation is enqueued (it watches facts; it demands nothing) */
void eval_request(RefId t, FaceId chi, Cont *k) {
    if (!k->cut && k->dest && k->kind != K_ROOT && k->kind != K_EXTERNAL) cut_open(k, t, chi);
    Cut *c = k->cut; Gen *g = k->gen;
    if (c) { cut_ref(c); gen_ref(g); }            /* the subscription job's references (the ticket may be consumed meanwhile) */
    request_inner(t, chi, k);
    if (c) sub_enqueue(c, g);
}
static void request_inner(RefId t, FaceId chi, Cont *k) {
    if (fc_is_false(chi)) { deliver(k, result_new(R_NO_OBSERVATION, t)); return; }
    if (!validate_occurrence(t, chi)) { deliver(k, result_invalid("occurrence outside its required face")); return; }
    size_t n; const uint64_t *S = dimset_get(ref_support(t), &n);
    FaceId eta = fc_project(chi, S, n);
    EntryId eid = entry_intern(t, eta);
    Entry *e = ENT(eid);
    k->child = eid; k->req = t;
    XINC(evx, EvalEvents, request);
    /* §60 trace: the consumer occurrence (owner, slot, requested key) */
    if (k->kind == K_ROOT || k->kind == K_EXTERNAL) { size_t at = __atomic_load_n(&E.n_roots, __ATOMIC_ACQUIRE); (void)chunked_at(&E.roots_tab, at); (void)chunked_at(&E.roots_tab, at + 1);   /* the chunk, outside roots_mu */
      pthread_mutex_lock(&E.roots_mu); *(EntryId *)chunked_at(&E.roots_tab, E.n_roots) = eid; __atomic_store_n(&E.n_roots, E.n_roots + 1, __ATOMIC_RELEASE); pthread_mutex_unlock(&E.roots_mu); }
    else { Entry *o = ENT(k->dest); pthread_mutex_lock(&o->mu); if (k->gen) { k->gen->dep_idx = o->deps.len; k->gen->have_dep = true; } vec_push(&o->deps, eid); vec_push(&o->dep_hist, 0); pthread_mutex_unlock(&o->mu); }
    /* readiness check and waiter registration under the same lock (§10) */
    fine_bump(FC_LOCK_ATTEMPTS); pthread_mutex_lock(&e->mu);
    xl_add((uint64_t *)&e->n_req, &e->n_req_cx, 1);
    if (e->state == E_READY) {
        EvalResult *r = e->result;
        xl_add((uint64_t *)&e->n_deliver, &e->n_deliver_cx, 1);
        pthread_mutex_unlock(&e->mu);
        XINC(evx, EvalEvents, ready_hit); reuse_bump(REUSE_READY_HIT); fine_bump(FC_WAITERS_DELIVERED);
        deliver(k, r);                       /* after unlock */
        return;
    }
    if (e->state == E_RUNNING) {
        size_t idx = e->waiters.len;
        vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
        Task replay = prefix_catchup_locked(eid, e, idx);
        pthread_mutex_unlock(&e->mu);
        if (replay.fact) enqueue_reserved(replay);
        XINC(evx, EvalEvents, running_hit); reuse_bump(REUSE_RUNNING_JOIN);
        return;
    }
    /* §78.3–78.4: before the body runs, look for a completed receipt this
     * producer can continue from (computed outside the entry lock; the
     * launcher installs it) */
    pthread_mutex_unlock(&e->mu);
    RefId ad = 0; uint64_t adp = 0; EntryId ads = 0; const PrefixFact *adf = NULL;
    bool have_ad = find_adapter(t, e->shape, eta, eid, &ad, &adp, &ads, &adf);
    pthread_mutex_lock(&e->mu);
    if (e->state == E_READY) { EvalResult *r = e->result; xl_add((uint64_t *)&e->n_deliver, &e->n_deliver_cx, 1); pthread_mutex_unlock(&e->mu); XINC(evx, EvalEvents, ready_hit); reuse_bump(REUSE_READY_HIT); deliver(k, r); return; }
    if (e->state == E_RUNNING) {
        size_t idx = e->waiters.len; vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
        Task replay = prefix_catchup_locked(eid, e, idx);
        pthread_mutex_unlock(&e->mu);
        if (replay.fact) enqueue_reserved(replay);
        XINC(evx, EvalEvents, running_hit); reuse_bump(REUSE_RUNNING_JOIN); return;
    }
    e->scope = reuse_tl_scope; reuse_scope_ref(e->scope);   /* the launching request owns this producer's work */
    if (have_ad) { e->adapter = ad; e->adapter_prefix = adp; e->adapter_src = ads; e->adapter_fact = adf; if (adf) XINC(pevx, EvalPrefixEvents, adapters); }
    /* U → R({c}) + EVAL(K) is one transition (§26): the task is enqueued
     * before RUNNING can be observed by anyone else, so no requester can see
     * a running key whose evaluator is not yet runnable. */
    e->state = E_RUNNING;
    vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
    reserve_job();                       /* outstanding += 1 before RUNNING can be observed */
    pthread_mutex_unlock(&e->mu);
    XINC(evx, EvalEvents, launch);
    xc_inc(&E.tasks_created);
    Task job; memset(&job, 0, sizeof job); job.entry = eid;
    enqueue_reserved(job);               /* enqueue after the entry lock is released */
}

static void forward(RefId t, FaceId chi, EntryId dest) { eval_request(t, chi, cont_new(K_FORWARD, dest, chi)); }
/* forward with the receipt of the rules applied so far (§78.2) */
static void prefix_publish(EntryId dest, RefId target, uint64_t receipt, const PrefixFact *parent, EntryId origin);
/* §84.2 STEP / SEQ: the destination already knows the finite derivation
 * leading to `t`; that cut is published as an immutable fact before the
 * suffix is awaited */
static void forward_rc(RefId t, FaceId chi, EntryId dest, uint64_t prefix) {
    prefix_publish(dest, t, prefix, NULL, dest);
    Cont *k = cont_new(K_FORWARD, dest, chi); k->prefix = prefix; eval_request(t, chi, k);
}

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

static void adapter_inherit(Entry *e);
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
        adapter_inherit(e);
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

/* ---------------- §84.2 committed prefixes ----------------
 *
 * A fact is prepared privately (its premises copied one pair per step), then
 * published by one release store into the producer's head while the
 * producer is RUNNING; a fact is never modified after publication. Its
 * waiters receive it one per notification job (a retained cursor): a
 * FORWARD waiter composes it after its own prefix (SEQ), an eliminator
 * waiter lifts it through its one-hole context (CONTEXT, the existing
 * eliminator-rebuilding recipe), and the result is published as the
 * waiter's own fact — only when the waiter requested exactly this
 * reference, and never back into the producer whose rule committed the
 * first step. */
static bool prefix_valid(const PrefixFact *f) {
    reuse_bump(REUSE_DEPENDENCY_CHECK);
    for (size_t k = 0; k + 1 < f->ngdeps; k += 2) { fine_bump(FC_ADAPTER_STEPS); if (global_revision(f->gdeps[k]) != f->gdeps[k + 1]) return false; }
    return true;
}
/* the (symbol, revision) pairs of x, one pair per section of x->mu; with
 * ready_only, only while x is READY (a READY entry's pairs are final) */
static void prefix_copy_pairs(Entry *x, bool ready_only, Words *out) {
    for (size_t k = 0;; k += 2) {
        pthread_mutex_lock(&x->mu);
        if ((ready_only && x->state != E_READY) || k + 1 >= x->gdeps.len) { pthread_mutex_unlock(&x->mu); return; }
        uint64_t a = x->gdeps.data[k], b = x->gdeps.data[k + 1];
        pthread_mutex_unlock(&x->mu);
        words_push(out, a); words_push(out, b); fine_bump(FC_ADAPTER_STEPS);
    }
}
/* The adapter uses its source derivation as a premise. Install that
 * immutable dependency snapshot before publishing any derived prefix or
 * requesting the residual. This evaluator owns the still-empty direct-read
 * vector; transfer ownership in one lock section rather than copying it
 * under the lock. */
static void adapter_inherit(Entry *e) {
    Words g; words_init(&g);
    if (e->adapter_fact) {
        const PrefixFact *f = e->adapter_fact;
        for (size_t k = 0; k < f->ngdeps; k++) { words_push(&g, f->gdeps[k]); fine_bump(FC_ADAPTER_STEPS); }
    } else if (e->adapter_src) prefix_copy_pairs(ENT(e->adapter_src), true, &g);
    pthread_mutex_lock(&e->mu);
    require(e->gdeps.len == 0 && e->gdeps.data == NULL, "adapter prerequisites installed before direct reads");
    e->gdeps.data = g.w; e->gdeps.len = g.n; e->gdeps.cap = g.cap;
    pthread_mutex_unlock(&e->mu);
}
static void fact_index(PrefixFact *f, ShapeId s);
static void prefix_publish_on(EntryId dest, RefId target, uint64_t receipt, const PrefixFact *parent, EntryId origin, FaceId guard, EntryId premise, bool branch, const uint64_t *xd, size_t nxd) {
    if (!dest || !receipt || !target) return;
    Entry *e = ENT(dest);
    if (target == e->ref) return;                         /* no progress: not a useful fact */
    pthread_mutex_lock(&e->mu); bool running = e->state == E_RUNNING; pthread_mutex_unlock(&e->mu);
    if (!running) return;
    /* the premises the derivation used: the producer's direct reads, the
     * READY children it consumed (as publication collects them, §79.1), and
     * the parent fact's premises for a SEQ / CONTEXT fact */
    Words g; words_init(&g);
    prefix_copy_pairs(e, false, &g);
    if (branch) { if (premise) prefix_copy_pairs(ENT(premise), true, &g); }
    else for (size_t i = 0;; i++) {
        pthread_mutex_lock(&e->mu);
        if (i >= e->deps.len) { pthread_mutex_unlock(&e->mu); break; }
        EntryId c = e->deps.data[i]; bool hist = e->dep_hist.data[i];
        pthread_mutex_unlock(&e->mu);
        fine_bump(FC_ADAPTER_STEPS);
        if (c != dest && !hist) prefix_copy_pairs(ENT(c), true, &g);
    }
    if (parent) for (size_t k = 0; k < parent->ngdeps; k++) { words_push(&g, parent->gdeps[k]); fine_bump(FC_ADAPTER_STEPS); }
    for (size_t k = 0; k < nxd; k++) { words_push(&g, xd[k]); fine_bump(FC_ADAPTER_STEPS); }   /* the slot generation's adoption certificate */
    PrefixFact *f = calloc(1, sizeof *f); require(f, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    f->src = dest; f->source = e->ref; f->face = guard; f->residual = target; f->receipt = receipt;
    f->gdeps = g.w; f->ngdeps = g.n; f->origin = origin;
    pthread_mutex_lock(&e->mu);
    if (e->state != E_RUNNING) { pthread_mutex_unlock(&e->mu); free(g.w); free(f); return; }   /* answered meanwhile: the fact is not published */
    f->id = __atomic_add_fetch(&E.fact_ids, 1, __ATOMIC_RELAXED);
    f->next = e->prefix_head;
    __atomic_store_n(&e->prefix_head, f, __ATOMIC_RELEASE);
    e->n_prefix++;
    size_t notify_limit = e->waiters.len;
    pthread_mutex_unlock(&e->mu);
    PrefixFact *h = __atomic_load_n(&E.facts, __ATOMIC_RELAXED);
    do f->all_next = h; while (!__atomic_compare_exchange_n(&E.facts, &h, f, false, __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
    if (parent) XINC(pevx, EvalPrefixEvents, lifted); else XINC(pevx, EvalPrefixEvents, published);
    Task t; memset(&t, 0, sizeof t); t.is_notify = true; t.entry = dest; t.fact = f; t.idx = 0; t.limit = notify_limit;
    enqueue(t);
    fact_index(f, e->shape);
}
static void prefix_publish(EntryId dest, RefId target, uint64_t receipt, const PrefixFact *parent, EntryId origin) {
    if (dest) prefix_publish_on(dest, target, receipt, parent, origin, ENT(dest)->face, 0, false, NULL, 0);
}
static RefId rebuild_elim(const Cont *k, RefId scrut);
/* the lift of `res` (reached from the slot's requested reference by `rcpt`)
 * through the slot's recipe: SEQ for a forwarding or join slot, CONTEXT
 * through the eliminator's one-hole context; a family rewrite must hold
 * along the whole bound dimension (∀j) */
static bool lift_through(const Cont *kc, RefId res, uint64_t rcpt, FaceId fface, RefId *target, uint64_t *receipt, FaceId *child_guard) {
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    switch (kc->kind) {
    case K_FORWARD: *target = res; *receipt = rc_seq(kc->prefix, rcpt); break;                                    /* SEQ */
    case K_APP: case K_FST: case K_SND: case K_PAPP: case K_UNGLUE:                                              /* CONTEXT */
        *target = rebuild_elim(kc, res); *receipt = rc_rule(cong_of[kc->kind], rcpt, 0); break;
    case K_COMP_FAMILY: {
        Head ho; open_ref(kc->orig, &ho); uint64_t lv = levels_first(ho.levels); if (ho.levels == LEVELS_NONE) lv = LEVEL_NONE; head_free(&ho);
        *target = mk_comp_lv(lv, kc->j, res, kc->phi, kc->tube, kc->cap); *receipt = rc_rule(RR_CONG_COMP, rcpt, 0); break;
    }
    case K_BRANCH:
        /* The branch's guarded entry receipt was captured before it was
         * launched; the join is reached only through the Cut's retained
         * handle, never through a copied pointer. */
        *target = res; *receipt = rc_seq(kc->prefix, rcpt); break;
    default: return false;
    }
    *child_guard = kc->kind == K_COMP_FAMILY ? fc_forall(kc->j, fface) : fface;
    return true;
}
/* one notification: the fact of `entry` to its waiter `idx`, then the cursor advances */
static void prefix_notify(Task t) {
    Entry *e = ENT(t.entry);
    pthread_mutex_lock(&e->mu);
    if (e->state != E_RUNNING || t.idx >= t.limit || t.idx >= e->waiters.len) { pthread_mutex_unlock(&e->mu); return; }
    Cont kc = *e->waiters.data[t.idx];       /* a copy: the waiter may be resumed and released once the lock is dropped */
    if (kc.cut) { cut_ref(kc.cut); gen_ref(kc.gen); }   /* the ticket's Cut and generation, retained for this step */
    pthread_mutex_unlock(&e->mu);
    XINC(pevx, EvalPrefixEvents, notify_steps);
    { Task n = t;
      if (t.catchup) { n.fact = t.fact->next; if (n.fact) enqueue(n); }
      else { n.idx++; if (n.idx < n.limit) enqueue(n); }
    }
    const PrefixFact *f = t.fact;
    bool live = true; uint64_t q = 0; const uint64_t *xd = NULL; size_t nxd = 0;
    if (kc.cut) {   /* only the current generation of a WAITING slot lifts (a superseded ticket's slot has moved on) */
        pthread_mutex_lock(&kc.cut->mu); live = kc.cut->state == CUT_WAITING && kc.cut->cur == kc.gen; pthread_mutex_unlock(&kc.cut->mu);
        q = kc.gen->q; xd = kc.gen->d; nxd = kc.gen->nd;
    }
    RefId target = 0; uint64_t receipt = 0; FaceId child_guard = 0;
    if (live && kc.req == f->source && kc.dest && kc.dest != f->origin && kc.dest != t.entry
        && lift_through(&kc, f->residual, rc_seq(q, f->receipt), f->face, &target, &receipt, &child_guard)) {
        FaceId guard = fc_meet(ENT(kc.dest)->face, fc_meet(kc.chi, child_guard));
        if (!fc_is_false(guard)) prefix_publish_on(kc.dest, target, receipt, f, f->origin, guard, kc.prefix_premise, kc.kind == K_BRANCH, xd, nxd);
    }
    if (kc.cut) { gen_unref(kc.gen); cut_unref(kc.cut); }
}
const PrefixFact *eval_entry_prefix(EntryId e) { return __atomic_load_n(&ENT(e)->prefix_head, __ATOMIC_ACQUIRE); }
size_t eval_entry_prefix_count(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); size_t n = x->n_prefix; pthread_mutex_unlock(&x->mu); return n; }
const PrefixFact *eval_entry_adapter_fact(EntryId e) { return ENT(e)->adapter_fact; }
bool eval_prefix_valid(const PrefixFact *f) { return f && prefix_valid(f); }
EvalPrefixEvents eval_prefix_events(void) {
    EvalPrefixEvents v; xproject(E.pevx, (size_t *)&v, sizeof v / sizeof(size_t), "prefix event");
    return v;
}

/* ---------------- LIVE-CUT-ADOPTION: subscriptions, proposals, installation, delivery ----------------
 *
 * Every step below is one job of the evaluator's scheduler, owned by the
 * Cut's producer (its reuse scope and executing continuation); no job holds
 * a lock across a variable-size traversal, and every lock section is
 * constant-size: the Cut's lock (state / generation test and the installation
 * of prepared handles), sub_mu (one list push and one head capture), an
 * entry lock (one occurrence flag, one dependency pair), prep_mu (one cache
 * record). */
static ShapeSide *shape_side(ShapeId s, bool create) { pthread_mutex_lock(&E.entries_mu); ShapeSide *ss = shape_side_locked(s, create); pthread_mutex_unlock(&E.entries_mu); return ss; }
static Task op_task(uint8_t op) { Task t; memset(&t, 0, sizeof t); t.op = op; return t; }
static bool cut_live(Cut *c, Gen *g) { pthread_mutex_lock(&c->mu); bool l = c->state == CUT_WAITING && c->cur == g; pthread_mutex_unlock(&c->mu); return l; }
static void proposal_free(Proposal *p) { words_free(&p->d); gen_unref(p->gen); cut_unref(p->cut); free(p); fine_bump(FC_CELLS_RELEASED); }

/* §2.2, publication side of the partition: under sub_mu the fact enters its
 * shape's history and the current subscriber list is captured; every
 * subscriber registered before is noticed (one per job), every later one
 * replays the fact from history — each (fact, subscription) pair exactly once */
static void fact_index(PrefixFact *f, ShapeId s) {
    ShapeSide *ss = shape_side(s, true);
    pthread_mutex_lock(&E.sub_mu);
    f->shape_next = ss->sfacts; ss->sfacts = f;
    Sub *drop = sub_unlink_one_locked(&ss->subs);
    Sub *h = ss->subs; sub_ref(h);
    pthread_mutex_unlock(&E.sub_mu);
    sub_unref(drop);
    if (h) { Task t = op_task(OP_FACTNOTE); t.p = h; t.fact = f; enqueue(t); }
}
static void sub_enqueue(Cut *c, Gen *g) { Task t = op_task(OP_SUB); t.p = c; t.p2 = g; enqueue(t); }   /* the caller's references move into the job */
/* §2.2, registration side: the subscription enters its shape's list and the
 * immutable history boundary is captured in the same section */
static void sub_register(Cut *c, Gen *g, uint64_t sigma, ShapeId s) {
    Sub *n = calloc(1, sizeof *n); require(n, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    n->refs = 1; n->cut = c; cut_ref(c); n->gen = g; gen_ref(g); n->sigma = sigma;
    __atomic_add_fetch(&E.live_subs, 1, __ATOMIC_RELAXED);
    ShapeSide *ss = shape_side(s, true);
    pthread_mutex_lock(&E.sub_mu);
    Sub *drop = sub_unlink_one_locked(&ss->subs);
    n->next = ss->subs; ss->subs = n; const PrefixFact *hist = ss->sfacts;   /* the head's reference moves to n->next */
    if (hist) sub_ref(n);
    pthread_mutex_unlock(&E.sub_mu);
    sub_unref(drop);
    XINC(cevx, EvalCutEvents, subscriptions);
    if (hist) { Task t = op_task(OP_REPLAY); t.p = n; t.fact = hist; enqueue(t); }
}
/* a fact meets a live subscription: a proposal (preparation job) is made
 * unless the fact is the slot's own (its owner's, or its current child key's,
 * which §84.2 notification lifts) */
static void consider(Sub *n, const PrefixFact *f) {
    Cut *c = n->cut; Gen *g = n->gen;
    if (!cut_live(c, g)) return;
    if (f->src == c->owner || f->origin == c->owner) return;
    Entry *src = ENT(f->src);
    if (src->ref == g->r && src->face == g->eta) return;
    Proposal *p = calloc(1, sizeof *p); require(p, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    p->cut = c; cut_ref(c); p->gen = g; gen_ref(g); p->f = f; p->sigma = n->sigma; words_init(&p->d);
    XINC(cevx, EvalCutEvents, proposals);
    Task t = op_task(OP_PREPARE); t.p = p; enqueue(t);
}
/* subscription job of one generation: the residual's own shape, then one
 * recorded instantiation edge of the residual per step */
static void sub_step(Task t) {
    Cut *c = t.p; Gen *g = t.p2;
    if (cut_live(c, g)) {
        if (t.idx == 0) { sub_register(c, g, map_identity(), shape_of(g->r)); t.idx = 1; enqueue(t); return; }
        const uint64_t *pairs; size_t np = instantiation_edges(g->r, &pairs);
        size_t e = t.idx - 1;
        if (e < np) { XINC(cevx, EvalCutEvents, edge_watches); sub_register(c, g, pairs[2 * e + 1], shape_of(pairs[2 * e])); t.idx++; enqueue(t); return; }
    }
    gen_unref(g); cut_unref(c);
}
static void replay_step(Task t) {
    Sub *n = t.p; XINC(cevx, EvalCutEvents, replays);
    consider(n, t.fact);
    if (t.fact->shape_next && !sub_dead(n) && cut_live(n->cut, n->gen)) { t.fact = t.fact->shape_next; enqueue(t); return; }
    sub_unref(n);
}
/* the job's reference moves from n to its live successor; one dead successor is detached per step */
static Sub *sub_advance(Sub *n) {
    pthread_mutex_lock(&E.sub_mu);
    Sub *drop = sub_unlink_one_locked(&n->next);
    Sub *nx = n->next; sub_ref(nx);
    pthread_mutex_unlock(&E.sub_mu);
    sub_unref(drop); sub_unref(n);
    return nx;
}
static void notice_step(Task t) {
    Sub *n = t.p; XINC(cevx, EvalCutEvents, notices);
    if (!sub_dead(n)) consider(n, t.fact);
    Sub *nx = sub_advance(n);
    if (nx) { t.p = nx; enqueue(t); }
}
/* §2: an instantiation edge recorded after a subscription: a Cut whose
 * current residual is the edge's destination watches its source shape */
static void eval_edge_hook(RefId dest, RefId src, uint64_t sigma) {
    if (!__atomic_load_n(&E.live, __ATOMIC_ACQUIRE) || !__atomic_load_n(&E.live_subs, __ATOMIC_RELAXED)) return;
    Task t = op_task(OP_EDGE); t.r1 = dest; t.r2 = src; t.sigma = sigma; enqueue(t);
}
static void edge_step(Task t) {
    Sub *n = t.p;
    if (!n) {
        ShapeSide *ss = shape_side(shape_of(t.r1), false); if (!ss) return;
        pthread_mutex_lock(&E.sub_mu); Sub *drop = sub_unlink_one_locked(&ss->subs); n = ss->subs; sub_ref(n); pthread_mutex_unlock(&E.sub_mu);
        sub_unref(drop);
        if (!n) return;
    }
    if (!sub_dead(n) && map_is_identity(n->sigma) && n->gen->r == t.r1 && cut_live(n->cut, n->gen)) { XINC(cevx, EvalCutEvents, edge_watches); sub_register(n->cut, n->gen, t.sigma, shape_of(t.r2)); }
    Sub *nx = sub_advance(n);
    if (nx) { t.p = nx; enqueue(t); }
}
/* §3 preparation, one bounded step per job, outside every lock:
 *   0  boundary correspondence s[σ] = r, required face ψ ⊢ φ[σ], adapted
 *      residual v and its key under the destination's projected face, the
 *      unchanged-key and revisited-key rejections (a shared cached result);
 *   1  one premise (symbol, revision) per step against the captured stamp;
 *   2  one dependency pair of Δq ∪ Δ(r⇒v) per step;
 *   then q' = q ; ρ and the installation job. */
static void prepare_step(Task t) {
    Proposal *p = t.p; Cut *c = p->cut; Gen *g = p->gen; const PrefixFact *f = p->f;
    XINC(cevx, EvalCutEvents, prep_steps); fine_bump(FC_ADAPTER_STEPS);
    if (!cut_live(c, g)) { proposal_free(p); return; }        /* superseded or resumed meanwhile: ownership released, nothing altered */
    if (p->phase == 0) {
        p->stamp = global_env_version();
        uint64_t key[4] = { f->id, g->r, c->psi, p->sigma };
        uint64_t id = interner_intern(&E.prep_keys, key, 4, NULL);
        (void)chunked_at(&E.prep_tab, id - 1);
        pthread_mutex_lock(&E.prep_mu);
        PrepMemo *slot = chunked_at(&E.prep_tab, id - 1); PrepMemo m = *slot;
        if (m.state == 0) slot->state = 3;                   /* this job computes it; any other joins */
        pthread_mutex_unlock(&E.prep_mu);
        if (m.state == 3) { XINC(cevx, EvalCutEvents, prep_joined); enqueue(t); return; }   /* joined: retried after the computing job publishes */
        if (m.state == 0) {
            bool ident = map_is_identity(p->sigma);
            bool ok = (ident ? f->source : reindex(f->source, p->sigma)) == g->r;
            FaceId need = 0;
            if (ok) { need = ident ? f->face : fc_reindex(f->face, p->sigma); ok = fc_entails(c->psi, need); }
            m.v = 0; m.veta = 0; m.adrc = 0;
            if (ok) {
                m.v = ident ? f->residual : reindex(f->residual, p->sigma);
                m.veta = key_face(m.v, c->psi);
                ok = !(shape_of(m.v) == shape_of(g->r) && m.veta == g->eta) && fc_entails(m.veta, ref_required(m.v));
            }
            if (ok) m.adrc = ident ? rc(RC_PREFIX_RESTRICT, f->id, g->eta, 0, 3) : rc(RC_PREFIX_SPEC, f->id, p->sigma, 0, 3);
            m.state = ok ? 1 : 2;
            pthread_mutex_lock(&E.prep_mu); *(PrepMemo *)chunked_at(&E.prep_tab, id - 1) = m; pthread_mutex_unlock(&E.prep_mu);
            XINC(cevx, EvalCutEvents, prep_computed);
        } else XINC(cevx, EvalCutEvents, prep_shared);
        bool ok = m.state == 1;
        for (Gen *h = g; ok && h; h = h->prev) if (shape_of(h->r) == shape_of(m.v) && h->eta == m.veta) ok = false;   /* no return to a key this slot already passed */
        if (!ok) { XINC(cevx, EvalCutEvents, prep_rejected); proposal_free(p); return; }
        p->v = m.v; p->veta = m.veta; p->adrc = m.adrc;
        p->phase = 1; p->k = 0; enqueue(t); return;
    }
    if (p->phase == 1) {   /* the fact's premises, then the generation's inherited certificate, against the stamp */
        if (p->k + 1 < f->ngdeps + g->nd) {
            const uint64_t *pr = p->k < f->ngdeps ? f->gdeps + p->k : g->d + (p->k - f->ngdeps);
            if (global_revision(pr[0]) != pr[1]) { xc_inc(p->revalidating ? XSLOT(cevx, EvalCutEvents, revalidation_failed) : XSLOT(cevx, EvalCutEvents, prep_rejected)); proposal_free(p); return; }
            p->k += 2; enqueue(t); return;
        }
        if (p->revalidating) { Task n = op_task(OP_INSTALL); n.p = p; enqueue(n); return; }
        p->phase = 2; p->k = 0; enqueue(t); return;
    }
    size_t total = g->nd + f->ngdeps;
    if (p->k + 1 < total) {
        const uint64_t *src = p->k < g->nd ? g->d + p->k : f->gdeps + (p->k - g->nd);
        words_push(&p->d, src[0]); words_push(&p->d, src[1]);
        p->k += 2; enqueue(t); return;
    }
    p->q = rc_seq(g->q, p->adrc);
    Task n = op_task(OP_INSTALL); n.p = p; enqueue(n);
}
/* §4 installation under the Cut's lock: WAITING, the captured generation, the
 * validated stamp (else the same proposal revalidates its premises); then the
 * prepared handles are installed, the replacement request's launch reserved,
 * and it is enqueued after unlocking. The superseded ticket stays live. */
static void install_step(Task t) {
    Proposal *p = t.p; Cut *c = p->cut;
    pthread_mutex_lock(&c->mu);
    if (c->state != CUT_WAITING) { pthread_mutex_unlock(&c->mu); XINC(cevx, EvalCutEvents, install_not_waiting); proposal_free(p); return; }
    if (c->cur != p->gen) { pthread_mutex_unlock(&c->mu); XINC(cevx, EvalCutEvents, install_stale_generation); proposal_free(p); return; }
    uint64_t now = global_env_version();
    if (now != p->stamp) {
        pthread_mutex_unlock(&c->mu);
        XINC(cevx, EvalCutEvents, revalidations);
        p->stamp = now; p->phase = 1; p->k = 0; p->revalidating = true;
        Task n = op_task(OP_PREPARE); n.p = p; enqueue(n); return;
    }
    Gen *ng = gen_new(p->v, p->veta, p->q, p->d.w, p->d.n, p->gen); words_init(&p->d);
    Gen *old = c->cur; c->cur = ng; c->installs++;
    __atomic_store_n(&old->dead, true, __ATOMIC_RELEASE);
    Cont *tk = ticket_new(c, ng);
    reserve_job();
    pthread_mutex_unlock(&c->mu);
    XINC(cevx, EvalCutEvents, installs); XINC(cevx, EvalCutEvents, tickets);
    Entry *o = ENT(c->owner);
    pthread_mutex_lock(&o->mu); if (old->have_dep && old->dep_idx < o->dep_hist.len) o->dep_hist.data[old->dep_idx] = 1; pthread_mutex_unlock(&o->mu);   /* the superseded request becomes a historical edge */
    gen_unref(old);                                  /* the Cut's reference; the new generation retains it */
    Task rq = op_task(OP_REQUEST); rq.k = tk; enqueue_reserved(rq);
    /* the owner's derived prefix (K applied to v) through the bounded publication protocol */
    const PrefixFact *f = p->f;
    FaceId need = map_is_identity(p->sigma) ? f->face : fc_reindex(f->face, p->sigma);
    RefId target = 0; uint64_t receipt = 0; FaceId cg = 0;
    if (lift_through(&c->K, ng->r, ng->q, need, &target, &receipt, &cg)) {
        FaceId guard = fc_meet(o->face, fc_meet(c->K.chi, cg));
        if (!fc_is_false(guard)) prefix_publish_on(c->owner, target, receipt, f, f->origin, guard, c->K.prefix_premise, c->K.kind == K_BRANCH, ng->d, ng->nd);
    }
    proposal_free(p);
}
static void request_step(Task t) {
    Cont *k = t.k; RefId v = k->gen->r; FaceId psi = k->cut->psi;
    eval_request(v, psi, k);                         /* a new real consumer occurrence of the owner */
}
/* a dependency pair of the winning generation's certificate; a conflicting
 * revision is kept beside the other (the answer's validity check rejects it) */
static void gdeps_add_cert(Entry *e, SymbolId sym, uint64_t rev) {
    for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) if (e->gdeps.data[k] == sym && e->gdeps.data[k + 1] == rev) return;
    vec_push(&e->gdeps, sym); vec_push(&e->gdeps, rev);
}
static void resume(Cont *k, EvalResult *r);
/* §5 delivery: consumed once; the current generation of a WAITING slot wins
 * WAITING → RESUMING and executes the recipe once; any other ticket is
 * released with no semantic resume and no parent publication */
static void cut_deliver(Cont *k, EvalResult *r) {
    Cut *c = k->cut;
    pthread_mutex_lock(&c->mu);
    bool win = c->state == CUT_WAITING && c->cur == k->gen;
    if (win) { c->state = CUT_RESUMING; __atomic_store_n(&k->gen->dead, true, __ATOMIC_RELEASE); }
    pthread_mutex_unlock(&c->mu);
    if (!win) { XINC(cevx, EvalCutEvents, deliveries_stale); ticket_release(k); return; }
    XINC(cevx, EvalCutEvents, deliveries_current);
    Gen *g = k->gen;
    if (g->nd) { Entry *o = ENT(c->owner); for (size_t i = 0; i + 1 < g->nd; i += 2) { pthread_mutex_lock(&o->mu); gdeps_add_cert(o, g->d[i], g->d[i + 1]); pthread_mutex_unlock(&o->mu); fine_bump(FC_ADAPTER_STEPS); } }
    Cont view = c->K; view.child = k->child; view.req = k->req; view.aq = g->q;
    resume(&view, r);
    pthread_mutex_lock(&c->mu); c->state = CUT_CLOSED; pthread_mutex_unlock(&c->mu);
    XINC(cevx, EvalCutEvents, resumes);
    ticket_release(k);
}
static void op_dispatch(Task t) {
    switch (t.op) {
    case OP_SUB: sub_step(t); break;
    case OP_REPLAY: replay_step(t); break;
    case OP_FACTNOTE: notice_step(t); break;
    case OP_PREPARE: prepare_step(t); break;
    case OP_INSTALL: install_step(t); break;
    case OP_REQUEST: request_step(t); break;
    case OP_EDGE: edge_step(t); break;
    case OP_EXT: ((void (*)(void *))t.p)(t.p2); break;
    default: die("unknown evaluator job");
    }
}
static EvalTaskInfo task_info(const Task *t) {
    EvalTaskInfo in; memset(&in, 0, sizeof in);
    if (t->is_pair) { in.kind = ET_PAIR; return in; }
    if (t->is_notify) { in.kind = ET_NOTIFY; in.producer = t->entry; return in; }
    if (t->is_resume) { in.kind = ET_RESUME; in.producer = t->k->kind == K_ROOT || t->k->kind == K_EXTERNAL ? 0 : t->k->dest; in.child = t->k->child; in.ticket = t->k->cut != NULL; return in; }
    switch (t->op) {
    case OP_NONE: in.kind = ET_EVALUATE; in.producer = t->entry; break;
    case OP_SUB: in.kind = ET_SUBSCRIBE; in.producer = ((Cut *)t->p)->owner; break;
    case OP_REPLAY: in.kind = ET_REPLAY; in.producer = ((Sub *)t->p)->cut->owner; in.fact = t->fact; break;
    case OP_FACTNOTE: in.kind = ET_NOTICE; in.producer = ((Sub *)t->p)->cut->owner; in.fact = t->fact; break;
    case OP_PREPARE: in.kind = ET_PREPARE; in.producer = ((Proposal *)t->p)->cut->owner; in.fact = ((Proposal *)t->p)->f; break;
    case OP_INSTALL: in.kind = ET_INSTALL; in.producer = ((Proposal *)t->p)->cut->owner; in.fact = ((Proposal *)t->p)->f; break;
    case OP_REQUEST: in.kind = ET_REQUEST; in.producer = t->k->dest; in.ticket = true; break;
    case OP_EDGE: in.kind = ET_EDGE; break;
    case OP_EXT: in.kind = ET_EXTERNAL; in.tag = (int)t->idx; break;
    }
    return in;
}
/* teardown of a job that will never run (closed-session precondition) */
static void task_discard(Task t) {
    if (t.is_resume) {
        Cont *k = t.k;
        if (k->cut) { XINC(cevx, EvalCutEvents, retired_tickets); ticket_release(k); return; }
        if (k->kind == K_EXTERNAL && k->ext_free) k->ext_free(k->ext_ctx);
        if (k->kind == K_ROOT) rootbox_release(k->root);
        free(k); return;
    }
    switch (t.op) {
    case OP_SUB: gen_unref(t.p2); cut_unref(t.p); break;
    case OP_REPLAY: case OP_FACTNOTE: case OP_EDGE: sub_unref(t.p); break;
    case OP_PREPARE: case OP_INSTALL: proposal_free(t.p); break;
    case OP_REQUEST: XINC(cevx, EvalCutEvents, retired_tickets); ticket_release(t.k); break;
    default: break;
    }
}
/* scheduler policy: a held job is set aside (not outstanding) */
static bool hold_take(Task t) {
    bool (*h)(const EvalTaskInfo *, void *) = __atomic_load_n(&E.hold, __ATOMIC_ACQUIRE);
    if (!h) return false;
    EvalTaskInfo in = task_info(&t);
    if (!h(&in, E.hold_ctx)) return false;
    pthread_mutex_lock(&E.held_mu);
    if (E.nheld == E.capheld) {
        size_t nc = E.capheld ? 2 * E.capheld : 16;
        pthread_mutex_unlock(&E.held_mu);
        Task *nb = malloc(nc * sizeof(Task)); require(nb, "out of memory");   /* the larger buffer is made outside the lock */
        pthread_mutex_lock(&E.held_mu);
        if (E.nheld == E.capheld && nc > E.capheld) { if (E.nheld) memcpy(nb, E.held, E.nheld * sizeof(Task)); free(E.held); E.held = nb; E.capheld = nc; nb = NULL; }
        free(nb);
        if (E.nheld == E.capheld) { pthread_mutex_unlock(&E.held_mu); return hold_take(t); }
    }
    E.held[E.nheld++] = t;
    pthread_mutex_unlock(&E.held_mu);
    return true;
}
void eval_set_hold(bool (*pred)(const EvalTaskInfo *, void *), void *ctx) { E.hold_ctx = ctx; __atomic_store_n(&E.hold, pred, __ATOMIC_RELEASE); }
size_t eval_held_count(void) { pthread_mutex_lock(&E.held_mu); size_t n = E.nheld; pthread_mutex_unlock(&E.held_mu); return n; }
size_t eval_release_held(void) {
    pthread_mutex_lock(&E.held_mu); Task *h = E.held; size_t n = E.nheld; E.held = NULL; E.nheld = E.capheld = 0; pthread_mutex_unlock(&E.held_mu);
    for (size_t i = 0; i < n; i++) { if (h[i].op == OP_EXT) ext_push(h[i]); else enqueue(h[i]); }
    free(h); return n;
}
static void ext_push(Task t) {
    ExtNode *n = malloc(sizeof *n); require(n, "out of memory"); n->t = t; n->next = NULL;   /* made before q_mu */
    pthread_mutex_lock(&E.q_mu);
    if (E.ext_tail) E.ext_tail->next = n; else E.ext_head = n;
    E.ext_tail = n; E.ext_n++;
    pthread_cond_signal(&E.q_cv);
    pthread_mutex_unlock(&E.q_mu);
}
void eval_job(void (*fn)(void *), void *arg, int tag) { Task t = op_task(OP_EXT); t.p = (void *)fn; t.p2 = arg; t.idx = (size_t)tag; ext_push(t); }
/* under q_mu; the node is freed by the caller after unlocking */
static ExtNode *pop_ext_locked(Task *out) {
    if (kc_current() || !E.ext_head) return NULL;
    ExtNode *n = E.ext_head; E.ext_head = n->next; if (!E.ext_head) E.ext_tail = NULL;
    *out = n->t; return n;
}
static void finish_ext(void) {
    pthread_mutex_lock(&E.q_mu);
    require(E.ext_n > 0, "finish without an outstanding external job");
    if (--E.ext_n == 0 && E.outstanding == 0) pthread_cond_broadcast(&E.idle_cv);
    pthread_mutex_unlock(&E.q_mu);
}
static void finish_any(const Task *t) { if (t->op == OP_EXT) finish_ext(); else finish_job(); }
EvalCutEvents eval_cut_events(void) {
    EvalCutEvents v; xproject(E.cevx, (size_t *)&v, sizeof v / sizeof(size_t), "cut event");
    return v;
}

/* Act branchwise: demand each guarded term under chi ∧ phi_k; the join box
 * publishes the reconstructed guarded result once every box is full (§12,
 * §26). Each box has one producer; the last arrival publishes. */
static void publish_branchwise(EntryId dest, FaceId chi, size_t n, const FaceId *faces, const RefId *terms, EntryId premise, uint64_t congruence) {
    Gather *g = calloc(1, sizeof *g);
    require(g, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    g->dest = dest; g->n = n;
    g->faces = malloc((n ? n : 1) * sizeof(FaceId));
    g->results = calloc(n ? n : 1, sizeof(EvalResult *));
    require(g->faces && g->results, "out of memory");
    if (n) memcpy(g->faces, faces, n * sizeof(FaceId));
    pthread_mutex_init(&g->mu, NULL);
    g->refs = 1;                               /* the creator; each branch Cut retains the join (LIVE-CUT-ADOPTION §5) */
    if (n == 0) { gather_unref(g); publish(dest, result_system(mk_system(0, NULL, NULL), 0, NULL, NULL)); return; }
    for (size_t i = 0; i < n; i++) {
        Cont *k = cont_new(K_BRANCH, dest, fc_meet(chi, faces[i]));
        k->gather = g; k->branch = i; k->orig = terms[i];
        k->prefix_premise = premise;
        k->prefix = rc_seq(congruence, rc_rule(RR_SYSTEM_BRANCH, terms[i], faces[i]));
        eval_request(terms[i], k->chi, k);
    }
    gather_unref(g);
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
        publish(dest, out);                     /* the join's storage stays with its retaining Cuts */
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
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    publish_branchwise(k->dest, k->chi, sys->nbr, sys->faces, terms, k->child, rc_rule(cong_of[k->kind], child_rc(k), 0));
    free(terms);
}

static void resume_comp_family(Cont *k, EvalResult *r) {
    if (r->cls == R_NEUTRAL) {
        /* rebuild the composition around the residual family: no re-evaluation of the family */
        Head ho; open_ref(k->orig, &ho); uint64_t lv = levels_first(ho.levels); if (ho.levels == LEVELS_NONE) lv = LEVEL_NONE; head_free(&ho);
        RefId fam_res = residual_of(k->child);
        RefId residual = fam_res ? mk_comp_lv(lv, k->j, fam_res, k->phi, k->tube, k->cap) : k->orig;
        publish_with(k->dest, result_new(R_NEUTRAL, k->orig), residual, rc_rule(RR_CONG_COMP, child_rc(k), 0));
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
        publish_branchwise(k->dest, k->chi, kept, faces, terms, k->child, rc_rule(RR_CONG_COMP, child_rc(k), 0));
        free(faces); free(terms);
        return;
    }
    /* introduction: capture the retained components of the exposed head
     * and instantiate the one fixed clause (§53–§54); the producer entry's
     * face is the clause's source annotation κ */
    RefId out = comp_clause(k->j, r->ref, k->phi, k->tube, k->cap, ENT(k->dest)->face);
    if (!out) { publish(k->dest, result_invalid("composition in a family whose head is not a type former or lacks its universe annotation")); return; }
    reuse_bump(REUSE_COMP_EXPAND);
    forward_rc(out, k->chi, k->dest, rc_seq(rc_rule(RR_CONG_COMP, child_rc(k), 0), rc_rule(RR_COMP_EXPAND, 0, 0)));
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
    if (k->kind == K_FORWARD) { publish_with(k->dest, r, residual_of(k->child), rc_seq(k->prefix, child_rc(k))); return; }
    if (k->kind == K_COMP_FAMILY) { resume_comp_family(k, r); return; }
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    uint64_t cong = rc_rule(cong_of[k->kind], child_rc(k), 0);
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
/* V21 R2: the continuations executing evaluator tasks, each with the producer
 * whose task it runs (a node on the executing stack, linked while it runs):
 * a waiter names the one advancing the producer it actually awaits */
typedef struct ExecNode { KCont *k; uint64_t job; EntryId owner; struct ExecNode *prev, *next; } ExecNode;
static ExecNode *exec_head; static pthread_mutex_t exec_mu = PTHREAD_MUTEX_INITIALIZER;
typedef struct { ExecNode *node; EntryId owner; KCont *prev_kc; uint64_t prev_job; } ExecUndo;
/* unlink the stack-resident node and restore the producer's executing
 * continuation: the normal return path, and (V23 R3) the release a cancelled
 * continuation runs before its stack is unwound */
static void exec_undo(void *p) {
    ExecUndo *u = p;
    if (u->owner) { Entry *o = ENT(u->owner); __atomic_store_n(&o->exec_job, u->prev_job, __ATOMIC_RELEASE); __atomic_store_n(&o->exec_kc, u->prev_kc, __ATOMIC_RELEASE); }
    ExecNode *n = u->node;
    pthread_mutex_lock(&exec_mu); if (n->prev) n->prev->next = n->next; else exec_head = n->next; if (n->next) n->next->prev = n->prev; pthread_mutex_unlock(&exec_mu);
}
static void execute(Task t) {
    /* §94: an evaluator task is owned, unfinished work of the thread running
     * it; a kernel continuation may suspend inside it (its stack retains the
     * task, the entry stays RUNNING, the outstanding count is held). The
     * producer whose task it runs records the continuation (exec_kc) */
    KCont *k = kc_current(); bool outer = k && !k->in_eval; if (outer) k->in_eval = true;
    EntryId owner = t.is_pair || t.is_notify ? 0 : t.op ? task_info(&t).producer : t.is_resume ? (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL ? 0 : t.k->dest) : t.entry;
    ExecNode node = { k, k ? k->job : 0, owner, NULL, NULL };
    ExecUndo undo = { &node, owner, NULL, 0 }; KCleanup cl;
    if (k) {
        pthread_mutex_lock(&exec_mu); node.next = exec_head; if (exec_head) exec_head->prev = &node; exec_head = &node; pthread_mutex_unlock(&exec_mu);
        if (owner) { Entry *o = ENT(owner); undo.prev_kc = __atomic_exchange_n(&o->exec_kc, k, __ATOMIC_ACQ_REL); undo.prev_job = __atomic_exchange_n(&o->exec_job, k->job, __ATOMIC_ACQ_REL); }
        kc_cleanup_push(&cl, exec_undo, &undo);
    }
    execute_task(t);
    if (k) { kc_cleanup_pop(&cl); exec_undo(&undo); }
    if (outer) k->in_eval = false;
}
/* V21 R2: the continuation that can advance the publication of `want`: one
 * executing a task of `want`, or of a RUNNING producer `want` (transitively)
 * consumes. A retained traversal over the actual consumer occurrences, one
 * entry per step (FC_ADAPTER_STEPS); no unrelated task is ever named. */
static KCont *producer_owner(EntryId want, uint64_t *job) {
    if (!want) return NULL;
    Words stack, seen; words_init(&stack); words_init(&seen);
    words_push(&stack, want);
    KCont *found = NULL;
    while (stack.n && !found) {
        EntryId e = stack.w[--stack.n];
        bool dup = false; for (size_t i = 0; i < seen.n && !dup; i++) { fine_bump(FC_ADAPTER_STEPS); dup = seen.w[i] == e; }
        if (dup) continue;
        words_push(&seen, e);
        Entry *x = ENT(e);
        KCont *k = __atomic_load_n(&x->exec_kc, __ATOMIC_ACQUIRE);
        if (k) { found = k; *job = __atomic_load_n(&x->exec_job, __ATOMIC_ACQUIRE); break; }
        for (size_t i = 0;; i++) {
            pthread_mutex_lock(&x->mu);
            bool more = x->state == E_RUNNING && i < x->deps.len; EntryId c = more ? x->deps.data[i] : 0; bool hist = more && x->dep_hist.data[i];
            pthread_mutex_unlock(&x->mu);
            fine_bump(FC_ADAPTER_STEPS);
            if (!more) break;
            if (hist) continue;                          /* a superseded request is not awaited work */
            Entry *cx = ENT(c); pthread_mutex_lock(&cx->mu); bool running = cx->state == E_RUNNING; pthread_mutex_unlock(&cx->mu);
            if (running) words_push(&stack, c);
        }
    }
    words_free(&stack); words_free(&seen);
    return found;
}
/* §94 / V21 R2: a wait for the machine's progress. A continuation waiting
 * for the publication of a producer names the continuation advancing it
 * (`producer_owner`, computed by the caller before taking q_mu); a wait for
 * quiescence names a continuation executing a task, every one of which
 * quiescence requires. A plain thread waits on the condition. The caller
 * re-checks its predicate after the call. */
static void eval_wait_locked_for(KCont *on, uint64_t on_job) {
    KCont *k = kc_current();
    if (!k) { pthread_cond_wait(&E.idle_cv, &E.q_mu); return; }
    kc_wait_job(&E.idle_cv, &E.q_mu, on, on_job);
}
static void eval_wait_locked(void) {
    KCont *on = NULL; uint64_t job = 0;
    if (kc_current()) {
        pthread_mutex_lock(&exec_mu);
        for (ExecNode *n = exec_head; n && !on; n = n->next) if (n->k != kc_current()) { on = n->k; job = n->job; }
        pthread_mutex_unlock(&exec_mu);
    }
    eval_wait_locked_for(on, job);
}
static void execute_task(Task t) {
    if (t.is_pair) { net_step_pair(&E.net, t.pair); return; }
    if (t.is_notify) { prefix_notify(t); return; }   /* §84.2 administrative work: not an evaluator frame step */
    if (t.op) {                                       /* LIVE-CUT-ADOPTION administrative jobs, charged to the Cut's producer */
        EntryId ow = task_info(&t).producer;
        ReuseScope *prev = ow ? reuse_scope_enter(ENT(ow)->scope) : reuse_tl_scope;
        op_dispatch(t);
        reuse_scope_leave(prev);
        return;
    }
    XINC(evx, EvalEvents, eval_step);
    { EntryId owner = t.is_resume ? t.k->dest : t.entry;    /* §60 trace: the frame step belongs to the producer it advances */
      if (owner && !(t.is_resume && (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL))) { Entry *o = ENT(owner); pthread_mutex_lock(&o->mu); xl_add(&o->steps, &o->steps_carry, 1); pthread_mutex_unlock(&o->mu); } }
    /* V21 R3: the task's events are charged to the scope owning its producer */
    EntryId owner = t.is_resume ? (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL ? 0 : t.k->dest) : t.entry;
    ReuseScope *prev = owner ? reuse_scope_enter(ENT(owner)->scope) : reuse_tl_scope;
    if (t.is_resume) {
        if (t.k->cut) cut_deliver(t.k, t.r);                     /* a ticket: consumed once, the slot resumes at most once */
        else { resume(t.k, t.r); cont_release(t.k); }            /* single consumer: released once resumed */
    }
    else evaluate(t.entry);
    reuse_scope_leave(prev);
}

/* §43 FORWARD_RESULT(K): the receiver's request; delivery publishes into K */
void eval_forward_result(EntryId K, RefId v) { forward_rc(v, ENT(K)->face, K, rc_rule(RR_IDENTITY_APPLY, v, 0)); }

static void *worker_main(void *arg) {
    (void)arg;
    pthread_mutex_lock(&E.q_mu);
    for (;;) {
        Task t;
        ExtNode *xn = NULL;
        while (!E.stop && !pop_locked(&t) && !(xn = pop_ext_locked(&t))) pthread_cond_wait(&E.q_cv, &E.q_mu);   /* take_job */
        if (E.stop) break;
        pthread_mutex_unlock(&E.q_mu);
        free(xn);
        if (hold_take(t)) { finish_any(&t); pthread_mutex_lock(&E.q_mu); continue; }
        execute(t);                      /* all child jobs are enqueued before the job finishes */
        finish_any(&t);
        pthread_mutex_lock(&E.q_mu);
    }
    pthread_mutex_unlock(&E.q_mu);
    return NULL;
}

size_t eval_run(void) {
    if (E.nworkers) {
        /* wait until outstanding == 0 (no queued, reserved or executing job) */
        pthread_mutex_lock(&E.q_mu);
        size_t before = eval_events().eval_step;
        while (E.outstanding > 0 || (!kc_current() && E.ext_n > 0)) eval_wait_locked();
        size_t n = eval_events().eval_step - before;
        pthread_mutex_unlock(&E.q_mu);
        return n;
    }
    size_t n = 0;
    for (;;) {
        Task t;
        pthread_mutex_lock(&E.q_mu);
        ExtNode *xn = NULL;
        bool got = pop_locked(&t) || (xn = pop_ext_locked(&t)) != NULL;
        pthread_mutex_unlock(&E.q_mu);
        free(xn);
        if (!got) break;
        if (hold_take(t)) { finish_any(&t); continue; }
        execute(t);
        finish_any(&t);
        n++;
    }
    return n;
}
/* the sequential scheduler under a budget: at most `max_jobs` jobs */
size_t eval_run_budget(size_t max_jobs) {
    require(!E.nworkers, "a budgeted run drives the sequential scheduler");
    size_t n = 0;
    while (n < max_jobs) {
        Task t;
        pthread_mutex_lock(&E.q_mu);
        ExtNode *xn = NULL;
        bool got = pop_locked(&t) || (xn = pop_ext_locked(&t)) != NULL;
        pthread_mutex_unlock(&E.q_mu);
        free(xn);
        if (!got) break;
        if (hold_take(t)) { finish_any(&t); continue; }
        execute(t);
        finish_any(&t);
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
    EntryId root_entry = eval_entry_lookup(t, chi);   /* the producer this root awaits (the root continuation itself may already be resumed and released) */
    if (E.nworkers) {
        /* wait for this root, or for quiescence of the whole machine (stuck) */
        for (;;) {
            uint64_t job = 0; KCont *on = kc_current() ? producer_owner(root_entry, &job) : NULL;   /* outside q_mu: entry locks precede it */
            pthread_mutex_lock(&E.q_mu);
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            if (d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
            eval_wait_locked_for(on, job);
            pthread_mutex_unlock(&E.q_mu);
        }
    } else {
        /* no pool: this client runs the queue; while another client thread
         * is still executing a job (its publication may resume this root, or
         * enqueue more work), wait for the root or for quiescence rather
         * than reporting a stuck demand */
        for (;;) {
            eval_run();
            uint64_t job = 0; KCont *on = kc_current() ? producer_owner(root_entry, &job) : NULL;
            pthread_mutex_lock(&E.q_mu);
            pthread_mutex_lock(&box->mu); bool d = box->done; pthread_mutex_unlock(&box->mu);
            bool queued = E.qhead < E.qtail || net_pending_pairs_locked(&E.net) > 0 || (!kc_current() && E.ext_head);
            if (d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
            if (!queued) eval_wait_locked_for(on, job);
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

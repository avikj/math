#include "eval.h"
#include <sys/mman.h>
#include "lib.h"
#include "net.h"
#include "compiler.h"
#include "reuse.h"
#include "fine.h"
#include "event.h"

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
enum { OP_NONE = 0, OP_SUB, OP_REPLAY, OP_FACTNOTE, OP_PREPARE, OP_INSTALL, OP_REQUEST, OP_EDGE, OP_EXT, OP_CHILDWATCH, OP_RELEASE };
typedef struct { bool is_resume, is_pair, is_notify; EntryId entry; Cont *k; EvalResult *r; Active pair; const struct PrefixFact *fact; size_t idx, limit; bool catchup;
                 uint8_t op; void *p, *p2; RefId r1, r2; uint64_t sigma; } Task;   /* is_notify: §84.2 deliver `fact` of `entry` to its waiter `idx` (one waiter per task) */
/* the references of a shape, in insertion order: a node is appended once (its (shape, ref) key's creator) under entries_mu, read without a lock */
typedef struct RefNode { RefId r; struct RefNode *next; } RefNode;
typedef struct ShapeSide { EntryId ent_head, ent_tail; RefNode *ref_head, *ref_tail;   /* append-only lists: O(1) under entries_mu, walked without it */
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
    bool dead;              /* superseded or resumed: the killing event releases its watches (OP_RELEASE); the hollow nodes are unlinked lazily */
    struct Sub *watch;      /* its live subscriptions, linked under sub_mu (non-owning: a freed node unlinks itself) */
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
typedef struct Sub { int refs; Cut *cut; Gen *gen; uint64_t sigma; struct Sub *next; EntryId owner; struct Sub *gnext, **gpprev; } Sub;   /* cut/gen: NULL once released (hollow), read and cleared under sub_mu; owner: the Cut's owner, immutable */
/* HANDOFF §12 PreparedAdoption: the retained Cut and the captured (generation g, residual u = g->r, guard
 * ψ = cut->psi); the pinned immutable fact P = (φ, s, r, ρ, Δ) and its simultaneous map σ with the exact
 * boundary correspondence; ψ ⊢ φ[σ]; the checked connector χ : u ⇒* s[σ] (REFL when s[σ] = u, else the
 * receipt of a committed fact of u's own shape from u to s[σ], whose guard ψ entails and whose premises
 * join the certificate); q' = q ; χ ; ρ[σ]; the residual v = r[σ] under its key face; the union
 * certificate Δq ∪ Δχ ∪ Δ; the snapshot it was validated against; and the preallocated replacement
 * generation and ticket, installed or released whole. */
typedef struct PreparedAdoption {
    Cut *cut; Gen *gen; const struct PrefixFact *f; uint64_t sigma;
    int phase; size_t k; bool revalidating;
    RefId v; FaceId veta; uint64_t adrc, q; Words d; uint64_t stamp;
    const struct PrefixFact *conn;      /* the connector's fact (NULL: χ = REFL) */
    const struct PrefixFact *scan;      /* connector search cursor (one fact per step) */
    Gen *ng; Cont *tk;                  /* preallocated replacement */
} PreparedAdoption;
typedef PreparedAdoption Proposal;
typedef struct { int state; RefId v; FaceId veta; uint64_t adrc; bool direct; } PrepMemo;   /* state: 0 absent, 1 applicable, 2 inapplicable, 3 being computed (a join); direct: s[σ] = r (else a connector is needed) */
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
    Interner shape_refs;           /* (shape, ref): the key's creator appends the ref to its shape's list */
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
    size_t idle_workers;   /* workers waiting for a job, their ambient labels published */
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
    bool no_adopt;           /* live adoption disabled (the base evaluator: tests of its schedule independence) */
    /* §84.2 committed prefix facts (immutable; reclaimed with the machine) */
    PrefixFact *facts; uint64_t fact_ids; XCount pevx[sizeof(EvalPrefixEvents) / sizeof(size_t)];
} E;

/* V23 R5: the evaluator's event counts are exact (xcount.h); the public
 * structs are checked word projections of them */
#define XSLOT(arr, T, f) (&E.arr[offsetof(T, f) / sizeof(size_t)])
static unsigned EVB_cevx, EVB_evx, EVB_pevx, EVB_tasks;   /* HANDOFF §7: the event families' dimensions in the primitive stream */
#define XEV(arr, slotp) ev_add(EVB_##arr + (unsigned)((slotp) - E.arr), 1)
#define XINC(arr, T, f) do { xc_inc(XSLOT(arr, T, f)); XEV(arr, XSLOT(arr, T, f)); } while (0)
static void xproject(const XCount *a, size_t *out, size_t n, const char *what) { for (size_t i = 0; i < n; i++) out[i] = (size_t)xs_u64_checked(xc_snap(&a[i]), what); }
EvalEvents eval_events(void) {
    EvalEvents v; xproject(E.evx, (size_t *)&v, sizeof v / sizeof(size_t), "evaluator event");
    return v;
}
void eval_set_policy(SchedPolicy p, uint64_t seed) { E.policy = p; E.rng = seed ? seed : 0x9E3779B97F4A7C15ULL; }
void eval_set_adoption(bool on) { E.no_adopt = !on; }
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
    EVB_cevx = ev_family("eval.cut", sizeof(EvalCutEvents) / sizeof(size_t), E.cevx);
    EVB_evx = ev_family("eval.events", sizeof(EvalEvents) / sizeof(size_t), E.evx);
    EVB_pevx = ev_family("eval.prefix", sizeof(EvalPrefixEvents) / sizeof(size_t), E.pevx);
    EVB_tasks = ev_family("eval.tasks", 1, &E.tasks_created);
    pthread_mutex_init(&E.roots_mu, NULL);
    chunked_init(&E.roots_tab, sizeof(EntryId)); E.n_roots = 0;
    interner_init(&E.keys); chunked_init(&E.heads, sizeof(EntryId));
    interner_init(&E.shape_ids); chunked_init(&E.shape_side, sizeof(ShapeSide)); interner_init(&E.shape_refs);
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
    size_t w = E.nworkers; SchedPolicy p = E.policy, pp = E.pair_policy; uint64_t rng = E.rng; int np = E.net.policy; uint64_t nrng = E.net.rng; bool na = E.no_adopt;
    eval_free(); eval_init();
    E.policy = p; E.pair_policy = pp; E.rng = rng; E.net.policy = np; E.net.rng = nrng; E.no_adopt = na;
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
    { size_t ns = interner_count(&E.shape_ids); for (size_t i = 0; i < ns; i++) { ShapeSide *ss = chunked_peek(&E.shape_side, i); if (ss) { RefNode *n = ss->ref_head; while (n) { RefNode *x = n->next; free(n); n = x; } ss->ref_head = ss->ref_tail = NULL; } } }
    interner_free(&E.shape_refs);
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
static void sub_gunlink_locked(Sub *n) { if (!n->gpprev) return; *n->gpprev = n->gnext; if (n->gnext) n->gnext->gpprev = n->gpprev; n->gnext = NULL; n->gpprev = NULL; }
static void sub_unref(Sub *n) {   /* iterative: a freed node releases its next pointer's reference */
    while (n && __atomic_sub_fetch(&n->refs, 1, __ATOMIC_ACQ_REL) == 0) {
        pthread_mutex_lock(&E.sub_mu); sub_gunlink_locked(n); Cut *c = n->cut; Gen *g = n->gen; n->cut = NULL; n->gen = NULL; pthread_mutex_unlock(&E.sub_mu);
        Sub *nx = n->next; cut_unref(c); gen_unref(g); free(n); fine_bump(FC_CELLS_RELEASED);
        __atomic_sub_fetch(&E.live_subs, 1, __ATOMIC_RELAXED); XINC(cevx, EvalCutEvents, subs_freed);
        n = nx;
    }
}
static bool sub_dead_locked(const Sub *n) { return !n->gen || __atomic_load_n(&n->gen->dead, __ATOMIC_ACQUIRE); }
/* a reader's pin: the watch's Cut and generation with one reference each, or false for a released watch (constant work under sub_mu) */
static bool sub_pin(Sub *n, Cut **c, Gen **g) {
    pthread_mutex_lock(&E.sub_mu);
    bool live = n->gen && !__atomic_load_n(&n->gen->dead, __ATOMIC_ACQUIRE);
    if (live) { *c = n->cut; *g = n->gen; cut_ref(*c); gen_ref(*g); }
    pthread_mutex_unlock(&E.sub_mu);
    return live;
}
static void sub_unpin(Cut *c, Gen *g) { gen_unref(g); cut_unref(c); }
/* under sub_mu, constant work: detach one dead node after *link (the shape head or a node's next);
 * returns the detached node, whose reference the caller drops after unlocking */
static Sub *sub_unlink_one_locked(Sub **link) {
    Sub *d = *link; if (!d || !sub_dead_locked(d)) return NULL;
    *link = d->next; sub_ref(d->next);
    XINC(cevx, EvalCutEvents, subs_unlinked);
    return d;
}
#define key_face_PARAMS(X) X(RefId, r) X(FaceId, psi)
KF_DECL(key_face, FaceId, key_face_PARAMS, FaceId f;)
KF_STEP(key_face) { KF_BEGIN(key_face); { size_t n; const uint64_t *S = dimset_get(ref_support(F->r), &n); KF_CALL(fc_project, &F->f, F->psi, S, n); } KF_RET(F->f); KF_END; }
/* §2.1: commit Cut(s0, ψ, K, WAITING, g, s0, REFL, ∅); the opening
 * continuation becomes the generation-g ticket */
#define cut_open_PARAMS(X) X(Cont *, k) X(RefId, t) X(FaceId, chi)
KF_DECL(cut_open, void, cut_open_PARAMS, FaceId eta;)
KF_STEP(cut_open) {
    KF_BEGIN(cut_open);
    KF_CALL(key_face, &F->eta, F->t, F->chi);
    {
        Cont *k = F->k;
        Cut *c = calloc(1, sizeof *c); require(c, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
        pthread_mutex_init(&c->mu, NULL);
        c->refs = 1;                                  /* the ticket */
        c->owner = k->dest; c->s0 = F->t; c->psi = F->chi;
        c->K = *k; c->K.cut = NULL; c->K.gen = NULL; c->K.aq = 0;
        if (k->kind == K_BRANCH) { c->join = k->gather; gather_ref(c->join); }
        c->state = CUT_WAITING;
        c->cur = gen_new(F->t, F->eta, 0, NULL, 0, NULL);
        k->cut = c; k->gen = c->cur; gen_ref(k->gen);
    }
    XINC(cevx, EvalCutEvents, cuts); XINC(cevx, EvalCutEvents, tickets);
    KF_RETV();
    KF_END;
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
/* the receipt records are interned: frame families (kframe.h) */
#define rc_PARAMS(X) X(uint64_t, a) X(uint64_t, b) X(uint64_t, c) X(uint64_t, d) X(size_t, n)
KF_DECL(rc, uint64_t, rc_PARAMS, uint64_t w[4]; uint64_t id;)
KF_STEP(rc) { KF_BEGIN(rc); F->w[0] = F->a; F->w[1] = F->b; F->w[2] = F->c; F->w[3] = F->d; KF_CALL(interner_intern, &F->id, &E.receipts, F->w, F->n, NULL); KF_RET(F->id); KF_END; }
#define rc_refl_PARAMS(X) X(RefId, t)
KF_DECL(rc_refl, uint64_t, rc_refl_PARAMS, uint64_t id;)
KF_STEP(rc_refl) { KF_BEGIN(rc_refl); KF_CALL(rc, &F->id, RC_REFL, F->t, 0, 0, 2); KF_RET(F->id); KF_END; }
#define rc_seq_PARAMS(X) X(uint64_t, a) X(uint64_t, b)
KF_DECL(rc_seq, uint64_t, rc_seq_PARAMS, uint64_t id;)
KF_STEP(rc_seq) { KF_BEGIN(rc_seq); if (!F->a) KF_RET(F->b); if (!F->b) KF_RET(F->a); KF_CALL(rc, &F->id, RC_SEQ, F->a, F->b, 0, 3); KF_RET(F->id); KF_END; }
#define rc_rule_PARAMS(X) X(uint64_t, rule) X(uint64_t, x) X(uint64_t, y)
KF_DECL(rc_rule, uint64_t, rc_rule_PARAMS, uint64_t id;)
KF_STEP(rc_rule) { KF_BEGIN(rc_rule); KF_CALL(rc, &F->id, RC_RULE, F->rule, F->x, F->y, 4); KF_RET(F->id); KF_END; }
/* the synchronous drivers, for the sections that already hold a lock (nothing suspends there) */
static uint64_t rc_refl_now(RefId t) { uint64_t r; KStack *s_ = kf_sync_begin(); rc_refl_push(s_, &r, t); kf_sync_run(s_); kf_sync_end(s_); return r; }
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

/* a shape's side record: its slot interned outside every lock (stable address) */
#define shape_side_get_PARAMS(X) X(ShapeId, s) X(bool, create)
KF_DECL(shape_side_get, ShapeSide *, shape_side_get_PARAMS, uint64_t w[1]; uint64_t slot;)
KF_STEP(shape_side_get) {
    KF_BEGIN(shape_side_get);
    F->w[0] = F->s;
    if (F->create) KF_CALL(interner_intern, &F->slot, &E.shape_ids, F->w, 1, NULL); else KF_CALL(interner_find, &F->slot, &E.shape_ids, F->w, 1);
    if (!F->slot) KF_RET(NULL);
    KF_CALL(chunked_prepare, NULL, &E.shape_side, F->slot - 1);
    KF_RET((ShapeSide *)chunked_at(&E.shape_side, F->slot - 1));
    KF_END;
}
/* the entry of the chain under (shape, face) that is reusable now: a READY
 * answer whose recorded dependencies are current, or a producer still
 * running in the current environment snapshot; 0 when none. The chain is
 * walked from `head` down to `stop` (exclusive) without entries_mu: links are
 * written once; each entry's state is read under its own lock (constant) and
 * a READY answer's dependencies — immutable once it is READY — are checked
 * after it, one pair per transition. */
#define chain_pick_PARAMS(X) X(EntryId, head) X(EntryId, stop)
KF_DECL(chain_pick, EntryId, chain_pick_PARAMS, uint64_t env; EntryId e; bool ok, ready; const uint64_t *g; size_t ng, k;)
KF_STEP(chain_pick) {
    KF_BEGIN(chain_pick);
    F->env = global_env_version();
    for (F->e = F->head; F->e && F->e != F->stop; F->e = __atomic_load_n(&ENT(F->e)->next_alt, __ATOMIC_ACQUIRE)) {
        { Entry *x = ENT(F->e);
          pthread_mutex_lock(&x->mu);
          F->ready = x->state == E_READY; F->ok = F->ready || x->env == F->env;
          if (F->ready) { F->g = x->gdeps.data; F->ng = x->gdeps.len; }
          pthread_mutex_unlock(&x->mu); }
        if (F->ready) {
            reuse_bump(REUSE_DEPENDENCY_CHECK);
            for (F->k = 0; F->k + 1 < F->ng; F->k += 2) { if (global_revision(F->g[F->k]) != F->g[F->k + 1]) { F->ok = false; break; } fine_bump(FC_CLAIM_STEPS); KF_SAFE(); }
        }
        if (F->ok) KF_RET(F->e);
        fine_bump(FC_ADAPTER_STEPS); KF_SAFE();
    }
    KF_RET(0);
    KF_END;
}
/* find or create the entry of (t, η): the shape, the shape's side, the
 * (shape, ref) and (shape, face) keys and the chain walk all happen outside
 * entries_mu; the lock covers the creation only — a head that moved since
 * the walk sends the walk over the newcomers first */
#define entry_intern_PARAMS(X) X(RefId, t) X(FaceId, eta)
KF_DECL(entry_intern, EntryId, entry_intern_PARAMS, ShapeId s; ShapeSide *ss; uint64_t w[2], rw[2]; uint64_t base, rid; bool created, rcreated; EntryId head, seen, id; size_t at;)
KF_STEP(entry_intern) {
    KF_BEGIN(entry_intern);
    KF_CALL(shape_of, &F->s, F->t);
    KF_CALL(shape_side_get, &F->ss, F->s, true);
    F->rw[0] = F->s; F->rw[1] = F->t;
    KF_CALL(interner_intern, &F->rid, &E.shape_refs, F->rw, 2, &F->rcreated);
    if (F->rcreated) {   /* the first registration of t under its shape appends it (one node, O(1) under the lock) */
        RefNode *n = malloc(sizeof *n); require(n, "out of memory"); n->r = F->t; n->next = NULL;
        pthread_mutex_lock(&E.entries_mu);
        if (F->ss->ref_tail) __atomic_store_n(&F->ss->ref_tail->next, n, __ATOMIC_RELEASE); else __atomic_store_n(&F->ss->ref_head, n, __ATOMIC_RELEASE);
        F->ss->ref_tail = n;
        pthread_mutex_unlock(&E.entries_mu);
    }
    F->w[0] = F->s; F->w[1] = F->eta;
    KF_CALL(interner_intern, &F->base, &E.keys, F->w, 2, &F->created);
    KF_CALL(chunked_prepare, NULL, &E.heads, F->base - 1);
    F->seen = 0;
    for (;;) {
        F->head = __atomic_load_n((EntryId *)chunked_at(&E.heads, F->base - 1), __ATOMIC_ACQUIRE);
        KF_CALL(chain_pick, &F->id, F->head, F->seen);
        if (F->id) KF_RET(F->id);
        F->at = __atomic_load_n(&E.n_entries, __ATOMIC_ACQUIRE); KF_CALL(chunked_prepare, NULL, &E.entries, F->at); KF_CALL(chunked_prepare, NULL, &E.entries, F->at + 1);
        pthread_mutex_lock(&E.entries_mu);
        { EntryId *head = (EntryId *)chunked_at(&E.heads, F->base - 1);
          if (*head != F->head) { pthread_mutex_unlock(&E.entries_mu); F->seen = F->head; continue; }   /* newcomers: walked before creating */
          EntryId id = E.n_entries + 1; fine_bump(FC_CELLS_ALLOCATED);
          Entry *e = (Entry *)chunked_at(&E.entries, id - 1);
          memset(e, 0, sizeof *e);
          e->ref = F->t; e->face = F->eta; e->state = E_UNEVALUATED; e->env = global_env_version(); e->shape = F->s; e->sside = F->ss;
          e->next_alt = *head;
          pthread_mutex_init(&e->mu, NULL);
          __atomic_store_n(&E.n_entries, id, __ATOMIC_RELEASE);
          __atomic_store_n(head, id, __ATOMIC_RELEASE);
          if (F->ss->ent_tail) __atomic_store_n(&ENT(F->ss->ent_tail)->shape_next, id, __ATOMIC_RELEASE); else __atomic_store_n(&F->ss->ent_head, id, __ATOMIC_RELEASE);
          F->ss->ent_tail = id;
          F->id = id; }
        pthread_mutex_unlock(&E.entries_mu);
        KF_RET(F->id);
    }
    KF_END;
}

KF_DECL_EXT(eval_entry_lookup, EntryId, eval_entry_lookup_PARAMS, uint64_t w[2]; uint64_t base; EntryId id;)
KF_STEP(eval_entry_lookup) {
    KF_BEGIN(eval_entry_lookup);
    KF_CALL(shape_of, &F->w[0], F->t);
    { size_t n; const uint64_t *S = dimset_get(ref_support(F->t), &n); KF_CALL(fc_project, &F->w[1], F->chi, S, n); }
    KF_CALL(interner_find, &F->base, &E.keys, F->w, 2);
    if (!F->base) KF_RET(0);
    { EntryId *hp = chunked_peek(&E.heads, F->base - 1); if (!hp) KF_RET(0); F->id = __atomic_load_n(hp, __ATOMIC_ACQUIRE); }
    KF_CALL(chain_pick, &F->id, F->id, 0);
    KF_RET(F->id);
    KF_END;
}
KF_SYNC_DEF(eval_entry_lookup, EntryId, eval_entry_lookup_PARAMS, eval_entry_lookup(RefId t, FaceId chi))
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
static void prefix_valid_push(KStack *ks, bool *ret, const PrefixFact *f);
#define adapt_residual_PARAMS(X) X(RefId, residual) X(FaceId, sface) X(MapId, sigma) X(FaceId, eta) X(ShapeId, s) X(RefId *, out)
KF_DECL(adapt_residual, bool, adapt_residual_PARAMS, FaceId need, reta; bool ok; RefId r; ShapeId rs;)
KF_STEP(adapt_residual) {
    KF_BEGIN(adapt_residual);
    if (map_is_identity(F->sigma)) F->need = F->sface; else KF_CALL(fc_reindex, &F->need, F->sface, F->sigma);
    KF_CALL(fc_entails, &F->ok, F->eta, F->need);
    if (!F->ok) KF_RET(false);
    if (map_is_identity(F->sigma)) F->r = F->residual; else KF_CALL(reindex, &F->r, F->residual, F->sigma);
    { size_t n; const uint64_t *S = dimset_get(ref_support(F->r), &n); KF_CALL(fc_project, &F->reta, F->eta, S, n); }
    if (F->reta == F->eta) { KF_CALL(shape_of, &F->rs, F->r); if (F->rs == F->s) KF_RET(false); }
    KF_CALL(fc_entails, &F->ok, F->reta, ref_required(F->r));
    if (!F->ok) KF_RET(false);
    *F->out = F->r; KF_RET(true);
    KF_END;
}
#define adapter_candidate_PARAMS(X) X(Entry *, src_e) X(EntryId, src) X(MapId, sigma) X(FaceId, eta) X(ShapeId, s) X(RefId *, out) X(uint64_t *, prefix) X(const PrefixFact **, fact_out)
KF_DECL(adapter_candidate, bool, adapter_candidate_PARAMS, bool ok, adapted, valid; RefId residual; FaceId sface; const PrefixFact *head, *f;)
KF_STEP(adapter_candidate) {
    KF_BEGIN(adapter_candidate);
    pthread_mutex_lock(&F->src_e->mu);
    F->ok = F->src_e->state == E_READY && F->src_e->residual && gdeps_valid_locked(F->src_e);
    F->residual = F->src_e->residual; F->sface = F->src_e->face;
    F->head = __atomic_load_n(&F->src_e->prefix_head, __ATOMIC_ACQUIRE);
    pthread_mutex_unlock(&F->src_e->mu);
    if (F->ok) {
        KF_CALL(adapt_residual, &F->adapted, F->residual, F->sface, F->sigma, F->eta, F->s, F->out);
        if (F->adapted) {
            if (map_is_identity(F->sigma)) KF_CALL(rc, F->prefix, RC_RESTRICT, F->src, F->eta, 0, 3); else KF_CALL(rc, F->prefix, RC_SPEC, F->src, F->sigma, 0, 3);
            *F->fact_out = NULL; KF_RET(true);
        }
    }
    /* A finite fact's validity is independent of its producer's final state.
     * Pin this immutable list snapshot and consider older facts when the
     * newest has inapplicable premises/face or makes no progress. */
    for (F->f = F->head; F->f; F->f = F->f->next) {
        fine_bump(FC_ADAPTER_STEPS);
        KF_CALL(prefix_valid, &F->valid, F->f);
        if (!F->valid) continue;
        KF_CALL(adapt_residual, &F->adapted, F->f->residual, F->f->face, F->sigma, F->eta, F->s, F->out);
        if (!F->adapted) continue;
        if (map_is_identity(F->sigma)) KF_CALL(rc, F->prefix, RC_PREFIX_RESTRICT, F->f->id, F->eta, 0, 3); else KF_CALL(rc, F->prefix, RC_PREFIX_SPEC, F->f->id, F->sigma, 0, 3);
        *F->fact_out = F->f; KF_RET(true);
    }
    KF_RET(false);
    KF_END;
}
/* the candidates are visited by a cursor over append-only lists read
 * without a lock (an entry of this shape, a reference of this shape, an
 * instantiation edge of it, an entry of the edge's source shape), one
 * position per transition; each candidate is tested by its own family */
typedef struct { int phase; EntryId ent; bool started; const RefNode *ref; bool ref_started, at_t, have_edges, have_src; RefId r; const uint64_t *pairs; size_t np, q; ShapeId src_shape; RefId src_ref; ShapeSide *src_side; EntryId sent; bool sent_started; } AdapterCursor;
/* 0: exhausted; 1: candidate (*e, *m); 2: advanced; 3: the edge source's shape side is needed; 4: the edges of c->r are needed */
static int adapter_next(AdapterCursor *c, RefId t, ShapeSide *ss, EntryId self, MapId ident, EntryId *e, uint64_t *m) {
    if (!ss) return 0;
    if (c->phase == 0) {
        EntryId x = c->started ? __atomic_load_n(&ENT(c->ent)->shape_next, __ATOMIC_ACQUIRE) : __atomic_load_n(&ss->ent_head, __ATOMIC_ACQUIRE);
        if (!x) { c->phase = 1; return 2; }
        c->ent = x; c->started = true;
        if (x == self) return 2;
        *e = x; *m = ident; return 1;
    }
    if (!c->have_edges) {   /* the next reference of the shape, then t itself */
        if (c->at_t) return 0;
        const RefNode *n = c->ref_started ? (c->ref ? __atomic_load_n(&c->ref->next, __ATOMIC_ACQUIRE) : NULL) : __atomic_load_n(&ss->ref_head, __ATOMIC_ACQUIRE);
        if (c->ref_started && !c->ref) n = NULL;
        c->ref_started = true;
        if (n) { c->ref = n; c->r = n->r; } else { c->ref = NULL; c->at_t = true; c->r = t; }
        return 4;
    }
    if (c->q >= c->np) { c->have_edges = false; c->have_src = false; return 2; }
    if (!c->have_src) { c->src_ref = c->pairs[2 * c->q]; c->sent_started = false; return 3; }
    { EntryId x = !c->src_side ? 0 : c->sent_started ? __atomic_load_n(&ENT(c->sent)->shape_next, __ATOMIC_ACQUIRE) : __atomic_load_n(&c->src_side->ent_head, __ATOMIC_ACQUIRE);
      if (!x) { c->q++; c->have_src = false; return 2; }
      c->sent = x; c->sent_started = true;
      *e = x; *m = c->pairs[2 * c->q + 1]; return 1; }
}
#define find_adapter_PARAMS(X) X(RefId, t) X(ShapeId, s) X(FaceId, eta) X(EntryId, self) X(RefId *, out) X(uint64_t *, prefix) X(EntryId *, src_out) X(const PrefixFact **, fact_out)
KF_DECL(find_adapter, bool, find_adapter_PARAMS, AdapterCursor c; EntryId e; uint64_t m; int st; bool ok; ShapeSide *ss; MapId ident;)
KF_STEP(find_adapter) {
    KF_BEGIN(find_adapter);
    KF_CALL(shape_side_get, &F->ss, F->s, false);
    KF_CALL0(map_identity, &F->ident);
    for (;;) {
        F->e = 0; F->m = 0;
        F->st = adapter_next(&F->c, F->t, F->ss, F->self, F->ident, &F->e, &F->m);
        fine_bump(FC_ADAPTER_STEPS);
        if (F->st == 0) KF_RET(false);
        if (F->st == 4) { F->c.q = 0; KF_CALL(instantiation_edges, &F->c.np, F->c.r, &F->c.pairs); F->c.have_edges = true; continue; }
        if (F->st == 3) { KF_CALL(shape_of, &F->c.src_shape, F->c.src_ref); KF_CALL(shape_side_get, &F->c.src_side, F->c.src_shape, false); F->c.have_src = true; continue; }
        if (F->st == 1) {
            KF_CALL(adapter_candidate, &F->ok, ENT(F->e), F->e, F->m, F->eta, F->s, F->out, F->prefix, F->fact_out);
            if (F->ok) { *F->src_out = F->e; KF_RET(true); }
        } else KF_SAFE();
    }
    KF_END;
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
/* HANDOFF §7 realization support: the producers whose actual work an entry's answer rests on — the entry
 * and, transitively, every producer it requested (historical requests included: their work happened). As
 * sorted occurrence identities, so supports of different consumers combine by set union and a shared
 * producer is counted once. */
size_t eval_entry_support(EntryId e, uint64_t **out) {
    Words stack, seen; words_init(&stack); words_init(&seen);
    words_push(&stack, e);
    while (stack.n) {
        EntryId x = stack.w[--stack.n];
        bool dup = false; for (size_t i = 0; i < seen.n && !dup; i++) dup = seen.w[i] == OCC(OCC_ENTRY, x);
        if (dup) continue;
        words_push(&seen, OCC(OCC_ENTRY, x));
        Entry *ex = ENT(x);
        for (size_t i = 0;; i++) { pthread_mutex_lock(&ex->mu); bool more = i < ex->deps.len; EntryId c = more ? ex->deps.data[i] : 0; pthread_mutex_unlock(&ex->mu); if (!more) break; words_push(&stack, c); }
    }
    words_free(&stack);
    size_t n = seen.n; uint64_t *v = (malloc)((n ? n : 1) * sizeof *v); require(v, "out of memory");
    memcpy(v, seen.w, n * sizeof *v); words_free(&seen);
    ev_occ_sort(v, &n);
    *out = v; return n;
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
#define publish_with_PARAMS(X) X(EntryId, eid) X(EvalResult *, r) X(RefId, residual) X(uint64_t, receipt)
KF_DECL(publish_with, void, publish_with_PARAMS, bool success, ok; FaceId reta; EntryId aid; uint64_t arc;)
static void publish_collect(EntryId eid, Entry *e);
static void publish_final(EntryId eid, Entry *e, EvalResult *r, RefId residual, uint64_t receipt, bool success);
KF_STEP(publish_with) {
    KF_BEGIN(publish_with);
    {
        Entry *e = ENT(F->eid);
        require(F->r->cls != R_NO_OBSERVATION, "no observation is never a published value");
        F->success = F->r->cls != R_INVALID;
        publish_collect(F->eid, e);
    }
    /* §76.3 / §78: the residual is head-normal under this face by
     * construction (an introduction, or an eliminator rebuilt around a
     * neutral residual); its own key receives the same answer without
     * running a body — an alias publication. A key already claimed by
     * another producer is left alone. The alias is published before the
     * source becomes READY, so a consumer woken by the source's answer finds
     * the residual's key already answered (no window in which the source is
     * observable and its residual key is not). */
    if (F->success && F->residual && F->residual != ENT(F->eid)->ref) {
        { size_t ns; const uint64_t *S = dimset_get(ref_support(F->residual), &ns); KF_CALL(fc_project, &F->reta, ENT(F->eid)->face, S, ns); }
        KF_CALL(fc_entails, &F->ok, F->reta, ref_required(F->residual));
        if (F->ok) {
            KF_CALL(entry_intern, &F->aid, F->residual, F->reta);
            if (F->aid != F->eid) {
                Entry *a = ENT(F->aid), *e = ENT(F->eid); EvalResult *r = F->r;
                pthread_mutex_lock(&a->mu);
                if (a->state == E_UNEVALUATED) {
                    pthread_mutex_lock(&e->mu); for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) gdeps_add(a, e->gdeps.data[k], e->gdeps.data[k + 1]); pthread_mutex_unlock(&e->mu);
                    /* §93 (R1): the alias answers at its own boundary — a distinct
                     * immutable descriptor whose head is the residual itself (system
                     * branches retained); the source's original expression stays in
                     * the source result and provenance, never at a smaller or
                     * weaker-faced key */
                    a->result = r->cls == R_SYSTEM ? result_system(F->residual, r->nbr, r->faces, r->terms) : result_new(r->cls, F->residual);
                    a->residual = F->residual; a->receipt = rc_refl_now(F->residual); a->is_alias = true;
                    __atomic_store_n(&a->state, E_READY, __ATOMIC_RELEASE);
                }
                pthread_mutex_unlock(&a->mu);
            }
        }
    }
    publish_final(F->eid, ENT(F->eid), F->r, F->residual, F->receipt, F->success);
    KF_RETV();
    KF_END;
}
/* children's dependencies, collected outside the entry lock */
static void publish_collect(EntryId eid, Entry *e) {
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
    (void)eid;
}
static void publish_final(EntryId eid, Entry *e, EvalResult *r, RefId residual, uint64_t receipt, bool success) {
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
    (void)eid;
}
/* a result that is its own residual (introduction, free neutral, system) */
#define publish_PARAMS(X) X(EntryId, eid) X(EvalResult *, r)
KF_DECL(publish, void, publish_PARAMS, uint64_t rcpt;)
KF_STEP(publish) {
    KF_BEGIN(publish);
    F->rcpt = 0;
    if (F->r->ref) KF_CALL(rc_refl, &F->rcpt, F->r->ref);
    KF_CALL(publish_with, NULL, F->eid, F->r, F->r->ref, F->rcpt);
    KF_RETV();
    KF_END;
}
static RefId residual_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); RefId r = c->residual; pthread_mutex_unlock(&c->mu); return r; }
static uint64_t receipt_of(EntryId child) { Entry *c = ENT(child); pthread_mutex_lock(&c->mu); uint64_t r = c->receipt; pthread_mutex_unlock(&c->mu); return r; }
/* the slot's receipt s0 ⇒* (child's answer): the winning ticket's prefix, then the child's own receipt */
#define child_rc_PARAMS(X) X(const Cont *, k)
KF_DECL(child_rc, uint64_t, child_rc_PARAMS, uint64_t r;)
KF_STEP(child_rc) { KF_BEGIN(child_rc); KF_CALL(rc_seq, &F->r, F->k->aq, receipt_of(F->k->child)); KF_RET(F->r); KF_END; }

static Task prefix_catchup_locked(EntryId eid, Entry *e, size_t idx) {
    Task t; memset(&t, 0, sizeof t);
    t.fact = __atomic_load_n(&e->prefix_head, __ATOMIC_ACQUIRE);
    if (t.fact) {
        t.is_notify = true; t.entry = eid; t.idx = idx; t.limit = idx + 1; t.catchup = true;
        reserve_job();
    }
    return t;
}
static void request_inner_push(KStack *ks, void *ret, RefId t, FaceId chi, Cont *k);
static void sub_enqueue(Cut *c, Gen *g);
/* LIVE-CUT-ADOPTION §2: a producer-owned request opens its Cut (unless the
 * continuation already is a ticket of one: an installed replacement), the
 * ordinary request is issued through the ticket, and the subscription job of
 * that generation is enqueued (it watches facts; it demands nothing) */
KF_DECL_EXT(eval_request, void, eval_request_PARAMS, Cut *c; Gen *g;)
KF_STEP(eval_request) {
    KF_BEGIN(eval_request);
    if (!F->k->cut && F->k->dest && F->k->kind != K_ROOT && F->k->kind != K_EXTERNAL) KF_CALL(cut_open, NULL, F->k, F->t, F->chi);
    F->c = F->k->cut; F->g = F->k->gen;
    if (F->c) { cut_ref(F->c); gen_ref(F->g); }            /* the subscription job's references (the ticket may be consumed meanwhile) */
    KF_CALL(request_inner, NULL, F->t, F->chi, F->k);
    if (F->c) sub_enqueue(F->c, F->g);
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(eval_request, eval_request_PARAMS, eval_request(RefId t, FaceId chi, Cont *k))
/* the readiness check and waiter registration under the entry lock (§10): true when the request was answered or joined */
static bool request_join_locked(Entry *e, EntryId eid, Cont *k) {
    if (e->state == E_READY) {
        EvalResult *r = e->result;
        xl_add((uint64_t *)&e->n_deliver, &e->n_deliver_cx, 1);
        pthread_mutex_unlock(&e->mu);
        XINC(evx, EvalEvents, ready_hit); reuse_bump(REUSE_READY_HIT); fine_bump(FC_WAITERS_DELIVERED);
        deliver(k, r);                       /* after unlock */
        return true;
    }
    if (e->state == E_RUNNING) {
        size_t idx = e->waiters.len;
        vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
        Task replay = prefix_catchup_locked(eid, e, idx);
        pthread_mutex_unlock(&e->mu);
        if (replay.fact) enqueue_reserved(replay);
        XINC(evx, EvalEvents, running_hit); reuse_bump(REUSE_RUNNING_JOIN);
        return true;
    }
    return false;
}
#define request_inner_PARAMS(X) X(RefId, t) X(FaceId, chi) X(Cont *, k)
KF_DECL(request_inner, void, request_inner_PARAMS, bool ok, have_ad; FaceId eta; EntryId eid; EvalResult *res; RefId ad; uint64_t adp; EntryId ads; const PrefixFact *adf;)
KF_STEP(request_inner) {
    KF_BEGIN(request_inner);
    if (fc_is_false(F->chi)) { deliver(F->k, result_new(R_NO_OBSERVATION, F->t)); KF_RETV(); }
    KF_CALL(fc_entails, &F->ok, F->chi, ref_required(F->t));   /* the ambient face must entail the reference's required face (which already folds in the required faces of its free variables) */
    if (!F->ok) { deliver(F->k, result_invalid("occurrence outside its required face")); KF_RETV(); }
    { size_t n; const uint64_t *S = dimset_get(ref_support(F->t), &n); KF_CALL(fc_project, &F->eta, F->chi, S, n); }
    KF_CALL(entry_intern, &F->eid, F->t, F->eta);
    {
        Cont *k = F->k; EntryId eid = F->eid; Entry *e = ENT(eid);
        k->child = eid; k->req = F->t;
        XINC(evx, EvalEvents, request);
        /* §60 trace: the consumer occurrence (owner, slot, requested key) */
        if (k->kind == K_ROOT || k->kind == K_EXTERNAL) { size_t at = __atomic_load_n(&E.n_roots, __ATOMIC_ACQUIRE); (void)chunked_at(&E.roots_tab, at); (void)chunked_at(&E.roots_tab, at + 1);   /* the chunk, outside roots_mu */
          pthread_mutex_lock(&E.roots_mu); *(EntryId *)chunked_at(&E.roots_tab, E.n_roots) = eid; __atomic_store_n(&E.n_roots, E.n_roots + 1, __ATOMIC_RELEASE); pthread_mutex_unlock(&E.roots_mu); }
        else { Entry *o = ENT(k->dest); pthread_mutex_lock(&o->mu); if (k->gen) { k->gen->dep_idx = o->deps.len; k->gen->have_dep = true; } vec_push(&o->deps, eid); vec_push(&o->dep_hist, 0); pthread_mutex_unlock(&o->mu); }
        /* readiness check and waiter registration under the same lock (§10) */
        fine_bump(FC_LOCK_ATTEMPTS); pthread_mutex_lock(&e->mu);
        xl_add((uint64_t *)&e->n_req, &e->n_req_cx, 1);
        if (request_join_locked(e, eid, k)) KF_RETV();
        /* §78.3–78.4: before the body runs, look for a completed receipt this
         * producer can continue from (computed outside the entry lock; the
         * launcher installs it) */
        pthread_mutex_unlock(&e->mu);
    }
    F->ad = 0; F->adp = 0; F->ads = 0; F->adf = NULL;
    KF_CALL(find_adapter, &F->have_ad, F->t, ENT(F->eid)->shape, F->eta, F->eid, &F->ad, &F->adp, &F->ads, &F->adf);
    {
        Cont *k = F->k; EntryId eid = F->eid; Entry *e = ENT(eid);
        pthread_mutex_lock(&e->mu);
        if (request_join_locked(e, eid, k)) KF_RETV();
        e->scope = reuse_tl_scope; reuse_scope_ref(e->scope);   /* the launching request owns this producer's work */
        if (F->have_ad) { e->adapter = F->ad; e->adapter_prefix = F->adp; e->adapter_src = F->ads; e->adapter_fact = F->adf; if (F->adf) XINC(pevx, EvalPrefixEvents, adapters); }
        /* U → R({c}) + EVAL(K) is one transition (§26): the task is enqueued
         * before RUNNING can be observed by anyone else, so no requester can see
         * a running key whose evaluator is not yet runnable. */
        e->state = E_RUNNING;
        vec_push(&e->waiters, k); fine_bump(FC_CONTS_REGISTERED);
        reserve_job();                       /* outstanding += 1 before RUNNING can be observed */
        pthread_mutex_unlock(&e->mu);
        XINC(evx, EvalEvents, launch);
        xc_inc(&E.tasks_created); ev_add(EVB_tasks, 1);
        Task job; memset(&job, 0, sizeof job); job.entry = eid;
        enqueue_reserved(job);               /* enqueue after the entry lock is released */
    }
    KF_RETV();
    KF_END;
}

#define forward_PARAMS(X) X(RefId, t) X(FaceId, chi) X(EntryId, dest)
KF_DECL(forward, void, forward_PARAMS, )
KF_STEP(forward) { KF_BEGIN(forward); KF_CALL(eval_request, NULL, F->t, F->chi, cont_new(K_FORWARD, F->dest, F->chi)); KF_RETV(); KF_END; }
/* forward with the receipt of the rules applied so far (§78.2) */
static void prefix_publish_push(KStack *ks, void *ret, EntryId dest, RefId target, uint64_t receipt, const PrefixFact *parent, EntryId origin);
/* §84.2 STEP / SEQ: the destination already knows the finite derivation
 * leading to `t`; that cut is published as an immutable fact before the
 * suffix is awaited */
#define forward_rc_PARAMS(X) X(RefId, t) X(FaceId, chi) X(EntryId, dest) X(uint64_t, prefix)
KF_DECL(forward_rc, void, forward_rc_PARAMS, Cont *k;)
KF_STEP(forward_rc) {
    KF_BEGIN(forward_rc);
    KF_CALL(prefix_publish, NULL, F->dest, F->t, F->prefix, NULL, F->dest);
    F->k = cont_new(K_FORWARD, F->dest, F->chi); F->k->prefix = F->prefix;
    KF_CALL(eval_request, NULL, F->t, F->chi, F->k);
    KF_RETV();
    KF_END;
}

/* ---------------- dispatch ---------------- */

#define eval_system_head_PARAMS(X) X(RefId, t) X(const Head *, h) X(FaceId, chi) X(EntryId, dest)
KF_DECL_DROP(eval_system_head, void, eval_system_head_PARAMS, eval_system_head_drop, size_t nb, kept, k; FaceId *faces; RefId *terms; FaceId uni, m, phi; RefId tk; bool ent; uint64_t rr;)
static void eval_system_head_drop(eval_system_head_F *F) { free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; }
KF_STEP(eval_system_head) {
    KF_BEGIN(eval_system_head);
    F->nb = F->h->n / 2;
    F->faces = malloc((F->nb ? F->nb : 1) * sizeof(FaceId));
    F->terms = malloc((F->nb ? F->nb : 1) * sizeof(RefId));
    require(F->faces && F->terms, "out of memory");
    F->kept = 0;
    KF_CALL0(fc_false, &F->uni);
    for (F->k = 0; F->k < F->nb; F->k++) {
        F->phi = F->h->f[2 * F->k].id;
        F->tk = F->h->f[2 * F->k + 1].id;
        KF_CALL(fc_meet, &F->m, F->chi, F->phi);
        if (fc_is_false(F->m)) continue;           /* inconsistent branch dropped */
        KF_CALL(fc_entails, &F->ent, F->chi, F->phi);
        if (F->ent) {
            free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; reuse_bump(REUSE_SYSTEM_RULE);
            KF_CALL(rc_rule, &F->rr, RR_SYSTEM, F->phi, 0);
            KF_CALL(forward_rc, NULL, F->tk, F->chi, F->dest, F->rr);
            KF_RETV();
        }
        F->faces[F->kept] = F->phi; F->terms[F->kept] = F->tk; F->kept++;
        KF_CALL(fc_join, &F->uni, F->uni, F->phi);
    }
    KF_CALL(fc_entails, &F->ent, F->chi, F->uni);
    if (!F->ent) { free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; KF_CALL(publish, NULL, F->dest, result_invalid("system does not cover the ambient face")); KF_RETV(); }
    reuse_bump(REUSE_SYSTEM_RULE);
    KF_CALL(rc_rule, &F->rr, RR_SYSTEM, 0, 0);
    KF_CALL(publish_with, NULL, F->dest, result_system(F->t, F->kept, F->faces, F->terms), F->t, F->rr);
    free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL;
    KF_RETV();
    KF_END;
}

static void adapter_inherit_push(KStack *ks, void *ret, Entry *e);
#define evaluate_PARAMS(X) X(EntryId, eid)
KF_DECL_DROP(evaluate, void, evaluate_PARAMS, evaluate_drop, Entry *e; RefId t, x; FaceId chi; Head h; uint64_t rr, rr2; Cont *k; FaceId fe; bool ent; IntervalId one; DimOpen fam, tube; RefId app, fst; bool ok; uint64_t id; int dir; MapId sigma; RefId a;)
static void evaluate_drop(evaluate_F *F) { head_free(&F->h); }
KF_STEP(evaluate) {
    KF_BEGIN(evaluate);
    F->e = ENT(F->eid);
    pthread_mutex_lock(&F->e->mu);
    require(F->e->state == E_RUNNING && F->e->runs == 0, "a key is evaluated by exactly one task");
    F->e->runs++;
    pthread_mutex_unlock(&F->e->mu);
    F->t = F->e->ref;
    F->chi = F->e->face;      /* evaluate under the key's face, not a requester's */
    if (F->e->adapter) {
        /* §78.3: continue from the completed receipt: observe the specialized
         * / restricted residual; its own further reduction is ordinary work */
        KF_CALL(adapter_inherit, NULL, F->e);
        reuse_bump(REUSE_RECEIPT_INSTANCE);
        KF_CALL(forward_rc, NULL, F->e->adapter, F->chi, F->eid, F->e->adapter_prefix);
        KF_RETV();
    }
    reuse_bump(REUSE_EVAL_BODY);
    if (ref_is_var(F->t)) { KF_CALL(publish, NULL, F->eid, result_new(R_NEUTRAL, F->t)); KF_RETV(); }
    KF_CALL(open_ref, NULL, F->t, &F->h);
    switch (F->h.tag) {
    case T_UNIVERSE: case T_PI: case T_SIGMA: case T_LAM: case T_PAIR: case T_PATH: case T_PLAM:
        KF_CALL(publish, NULL, F->eid, result_new(R_INTRODUCTION, F->t));
        break;
    case T_GLOBAL: {
        /* a declared symbol without a body is an opaque constant: neutral;
         * either way the observed revision is a dependency of the answer (§79.1) */
        F->id = (SymbolId)F->h.payload; F->rr2 = global_revision((SymbolId)F->id);
        pthread_mutex_lock(&F->e->mu); gdeps_add(F->e, (SymbolId)F->id, F->rr2); pthread_mutex_unlock(&F->e->mu);
        if (!global_body((SymbolId)F->id)) KF_CALL(publish, NULL, F->eid, result_new(R_NEUTRAL, F->t));
        else {
            reuse_bump(REUSE_GLOBAL_UNFOLD);
            KF_CALL(rc_rule, &F->rr, RR_UNFOLD, F->id, F->rr2);
            KF_CALL(unfold_global, &F->x, F->t);
            KF_CALL(forward_rc, NULL, F->x, F->chi, F->eid, F->rr);
        }
        break;
    }
    case T_APP: {
        F->k = cont_new(K_APP, F->eid, F->chi); F->k->orig = F->t; F->k->a = F->h.f[1].id;
        KF_CALL(eval_request, NULL, F->h.f[0].id, F->chi, F->k);
        break;
    }
    case T_FST: case T_SND: {
        F->k = cont_new(F->h.tag == T_FST ? K_FST : K_SND, F->eid, F->chi); F->k->orig = F->t;
        KF_CALL(eval_request, NULL, F->h.f[0].id, F->chi, F->k);
        break;
    }
    case T_PAPP: {
        IntervalId s = F->h.f[4].id;
        KF_CALL(fc_endpoint, &F->fe, s, 0); KF_CALL(fc_entails, &F->ent, F->chi, F->fe);
        if (F->ent) { reuse_bump(REUSE_ENDPOINT); KF_CALL(rc_rule, &F->rr, RR_ENDPOINT, 0, 0); KF_CALL(forward_rc, NULL, F->h.f[1].id, F->chi, F->eid, F->rr); break; }
        KF_CALL(fc_endpoint, &F->fe, F->h.f[4].id, 1); KF_CALL(fc_entails, &F->ent, F->chi, F->fe);
        if (F->ent) { reuse_bump(REUSE_ENDPOINT); KF_CALL(rc_rule, &F->rr, RR_ENDPOINT, 1, 0); KF_CALL(forward_rc, NULL, F->h.f[2].id, F->chi, F->eid, F->rr); break; }
        F->k = cont_new(K_PAPP, F->eid, F->chi); F->k->orig = F->t; F->k->s = F->h.f[4].id;
        KF_CALL(eval_request, NULL, F->h.f[3].id, F->chi, F->k);
        break;
    }
    case T_GLUE_TYPE:
        KF_CALL(fc_entails, &F->ent, F->chi, F->h.f[1].id);
        if (F->ent) { reuse_bump(REUSE_GLUE_RULE); KF_CALL(rc_rule, &F->rr, RR_GLUE, F->h.f[1].id, 0); KF_CALL(forward_rc, NULL, F->h.f[2].id, F->chi, F->eid, F->rr); }
        else KF_CALL(publish, NULL, F->eid, result_new(R_INTRODUCTION, F->t));
        break;
    case T_GLUE_INTRO:
        KF_CALL(fc_entails, &F->ent, F->chi, F->h.f[1].id);
        if (F->ent) { reuse_bump(REUSE_GLUE_RULE); KF_CALL(rc_rule, &F->rr, RR_GLUE, F->h.f[1].id, 1); KF_CALL(forward_rc, NULL, F->h.f[4].id, F->chi, F->eid, F->rr); }
        else KF_CALL(publish, NULL, F->eid, result_new(R_INTRODUCTION, F->t));
        break;
    case T_UNGLUE:
        KF_CALL(fc_entails, &F->ent, F->chi, F->h.f[1].id);
        if (F->ent) {
            reuse_bump(REUSE_GLUE_RULE);
            KF_CALL(mk_fst, &F->fst, F->h.f[3].id); KF_CALL(mk_app, &F->app, F->fst, F->h.f[4].id);
            KF_CALL(rc_rule, &F->rr, RR_GLUE, F->h.f[1].id, 2);
            KF_CALL(forward_rc, NULL, F->app, F->chi, F->eid, F->rr);
        }
        else { F->k = cont_new(K_UNGLUE, F->eid, F->chi); F->k->orig = F->t; KF_CALL(eval_request, NULL, F->h.f[4].id, F->chi, F->k); }
        break;
    case T_SYSTEM:
        KF_CALL(eval_system_head, NULL, F->t, &F->h, F->chi, F->eid);
        break;
    case T_TCALL: {
        /* §43: consume this frame; allocate APPLY_TRANSFORM(id,dir,σ) with
         * REF(a) on its principal port and CONTINUE_REFERENCE(K) on its
         * result; K stays RUNNING, its suspended evaluation is now owned by
         * the receiver. Connecting the principal ports enqueues the pair
         * before this job finishes. */
        KF_CALL(compiler_decode_call, &F->ok, &F->h, &F->id, &F->dir, &F->sigma, &F->a);
        require(F->ok, "malformed TRANSFORM_CALL");
        {
            Payload P = {0}; P.a = F->id; P.b = (uint64_t)F->dir; P.c = F->sigma;
            NodeId op = net_operation(&E.net, OP_APPLY_TRANSFORM, P);
            Payload Pr = {0}; Pr.ref = F->a;
            NodeId d = net_descriptor(&E.net, D_REF, Pr);
            Payload Pk = {0}; Pk.a = F->eid; Pk.face = F->chi;
            int8_t pol[1] = { -1 };
            NodeId cr = net_node(&E.net, A_CONTINUE_REFERENCE, 1, pol, Pk);
            net_connect(&E.net, op, 1, cr, 0);
            net_connect(&E.net, op, 0, d, 0);
        }
        break;
    }
    case T_COMP: {
        KF_CALL(fc_entails, &F->ent, F->chi, F->h.f[1].id);
        if (F->ent) {            /* tube coverage first */
            reuse_bump(REUSE_COMP_EXPAND);
            KF_CALL0(iv_one, &F->one);
            KF_CALL(apply_dim_binder, &F->x, F->t, 0, 2, F->one);
            KF_CALL(rc_rule, &F->rr, RR_COMP_TUBE, F->h.f[1].id, 0);
            KF_CALL(forward_rc, NULL, F->x, F->chi, F->eid, F->rr);
            break;
        }
        KF_CALL(resolve_dim_binder, &F->fam, F->t, 0, 0);
        KF_CALL(resolve_dim_binder, &F->tube, F->t, 0, 2);
        require(F->fam.j == F->tube.j, "family and tube must share the composition dimension");
        F->k = cont_new(K_COMP_FAMILY, F->eid, F->chi);
        F->k->orig = F->t; F->k->j = F->fam.j; F->k->tube = F->tube.body; F->k->phi = F->h.f[1].id; F->k->cap = F->h.f[3].id;
        KF_CALL(eval_request, NULL, F->fam.body, F->chi, F->k);
        break;
    }
    }
    head_free(&F->h);
    KF_RETV();
    KF_END;
}

/* rebuild an eliminator around a new scrutinee (system distribution) */
#define rebuild_elim_PARAMS(X) X(const Cont *, k) X(RefId, scrut)
KF_DECL_DROP(rebuild_elim, RefId, rebuild_elim_PARAMS, rebuild_elim_drop, Head h; RefId out; DimOpen B;)
static void rebuild_elim_drop(rebuild_elim_F *F) { head_free(&F->h); }
KF_STEP(rebuild_elim) {
    KF_BEGIN(rebuild_elim);
    KF_CALL(open_ref, NULL, F->k->orig, &F->h);
    F->out = 0;
    switch (F->k->kind) {
    case K_APP: KF_CALL(mk_app, &F->out, F->scrut, F->h.f[1].id); break;
    case K_FST: KF_CALL(mk_fst, &F->out, F->scrut); break;
    case K_SND: KF_CALL(mk_snd, &F->out, F->scrut); break;
    case K_PAPP: {
        KF_CALL(resolve_dim_binder, &F->B, F->k->orig, 0, 0);
        KF_CALL(mk_papp_lv, &F->out, levels_first(F->h.levels), F->B.j, F->B.body, F->h.f[1].id, F->h.f[2].id, F->scrut, F->h.f[4].id);
        break;
    }
    case K_UNGLUE: KF_CALL(mk_unglue_lv, &F->out, levels_first(F->h.levels), F->h.f[0].id, F->h.f[1].id, F->h.f[2].id, F->h.f[3].id, F->scrut); break;
    default: die("rebuild of a non-eliminator");
    }
    head_free(&F->h);
    KF_RET(F->out);
    KF_END;
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
#define prefix_valid_PARAMS(X) X(const PrefixFact *, f)
KF_DECL(prefix_valid, bool, prefix_valid_PARAMS, size_t k;)
KF_STEP(prefix_valid) {
    KF_BEGIN(prefix_valid);
    reuse_bump(REUSE_DEPENDENCY_CHECK);
    for (F->k = 0; F->k + 1 < F->f->ngdeps; F->k += 2) { fine_bump(FC_ADAPTER_STEPS); if (global_revision(F->f->gdeps[F->k]) != F->f->gdeps[F->k + 1]) KF_RET(false); KF_SAFE(); }
    KF_RET(true);
    KF_END;
}
/* the (symbol, revision) pairs of x, one pair per section of x->mu; with
 * ready_only, only while x is READY (a READY entry's pairs are final) */
#define prefix_copy_pairs_PARAMS(X) X(Entry *, x) X(bool, ready_only) X(Words *, out)
KF_DECL(prefix_copy_pairs, void, prefix_copy_pairs_PARAMS, size_t k;)
KF_STEP(prefix_copy_pairs) {
    KF_BEGIN(prefix_copy_pairs);
    for (F->k = 0;; F->k += 2) {
        pthread_mutex_lock(&F->x->mu);
        if ((F->ready_only && F->x->state != E_READY) || F->k + 1 >= F->x->gdeps.len) { pthread_mutex_unlock(&F->x->mu); KF_RETV(); }
        { uint64_t a = F->x->gdeps.data[F->k], b = F->x->gdeps.data[F->k + 1];
          pthread_mutex_unlock(&F->x->mu);
          words_push(F->out, a); words_push(F->out, b); fine_bump(FC_ADAPTER_STEPS); }
        KF_SAFE();
    }
    KF_END;
}
/* The adapter uses its source derivation as a premise. Install that
 * immutable dependency snapshot before publishing any derived prefix or
 * requesting the residual. This evaluator owns the still-empty direct-read
 * vector; transfer ownership in one lock section rather than copying it
 * under the lock. */
#define adapter_inherit_PARAMS(X) X(Entry *, e)
KF_DECL_DROP(adapter_inherit, void, adapter_inherit_PARAMS, adapter_inherit_drop, Words g; size_t k;)
static void adapter_inherit_drop(adapter_inherit_F *F) { words_free(&F->g); }
KF_STEP(adapter_inherit) {
    KF_BEGIN(adapter_inherit);
    words_init(&F->g);
    if (F->e->adapter_fact) {
        for (F->k = 0; F->k < F->e->adapter_fact->ngdeps; F->k++) { words_push(&F->g, F->e->adapter_fact->gdeps[F->k]); fine_bump(FC_ADAPTER_STEPS); KF_SAFE(); }
    } else if (F->e->adapter_src) KF_CALL(prefix_copy_pairs, NULL, ENT(F->e->adapter_src), true, &F->g);
    pthread_mutex_lock(&F->e->mu);
    require(F->e->gdeps.len == 0 && F->e->gdeps.data == NULL, "adapter prerequisites installed before direct reads");
    F->e->gdeps.data = F->g.w; F->e->gdeps.len = F->g.n; F->e->gdeps.cap = F->g.cap;
    pthread_mutex_unlock(&F->e->mu);
    words_init(&F->g);   /* ownership moved */
    KF_RETV();
    KF_END;
}
static void fact_index(PrefixFact *f, ShapeSide *ss);
static Task op_task(uint8_t op);
#define prefix_publish_on_PARAMS(X) X(EntryId, dest) X(RefId, target) X(uint64_t, receipt) X(const PrefixFact *, parent) X(EntryId, origin) X(FaceId, guard) X(EntryId, premise) X(bool, branch) X(const uint64_t *, xd) X(size_t, nxd)
KF_DECL_DROP(prefix_publish_on, void, prefix_publish_on_PARAMS, prefix_publish_on_drop, Entry *e; Words g; size_t i, k;)
static void prefix_publish_on_drop(prefix_publish_on_F *F) { words_free(&F->g); }
static void prefix_publish_finish(prefix_publish_on_F *F);
KF_STEP(prefix_publish_on) {
    KF_BEGIN(prefix_publish_on);
    if (!F->dest || !F->receipt || !F->target) KF_RETV();
    F->e = ENT(F->dest);
    if (F->target == F->e->ref) KF_RETV();                         /* no progress: not a useful fact */
    { pthread_mutex_lock(&F->e->mu); bool running = F->e->state == E_RUNNING; pthread_mutex_unlock(&F->e->mu); if (!running) KF_RETV(); }
    /* the premises the derivation used: the producer's direct reads, the
     * READY children it consumed (as publication collects them, §79.1), and
     * the parent fact's premises for a SEQ / CONTEXT fact */
    words_init(&F->g);
    KF_CALL(prefix_copy_pairs, NULL, F->e, false, &F->g);
    if (F->branch) { if (F->premise) KF_CALL(prefix_copy_pairs, NULL, ENT(F->premise), true, &F->g); }
    else for (F->i = 0;; F->i++) {
        pthread_mutex_lock(&F->e->mu);
        if (F->i >= F->e->deps.len) { pthread_mutex_unlock(&F->e->mu); break; }
        { EntryId c = F->e->deps.data[F->i]; bool hist = F->e->dep_hist.data[F->i];
          pthread_mutex_unlock(&F->e->mu);
          fine_bump(FC_ADAPTER_STEPS);
          if (c != F->dest && !hist) { F->k = c; KF_CALL(prefix_copy_pairs, NULL, ENT((EntryId)F->k), true, &F->g); }
          else KF_SAFE(); }
    }
    if (F->parent) for (F->k = 0; F->k < F->parent->ngdeps; F->k++) { words_push(&F->g, F->parent->gdeps[F->k]); fine_bump(FC_ADAPTER_STEPS); KF_SAFE(); }
    for (F->k = 0; F->k < F->nxd; F->k++) { words_push(&F->g, F->xd[F->k]); fine_bump(FC_ADAPTER_STEPS); KF_SAFE(); }   /* the slot generation's adoption certificate */
    prefix_publish_finish(F);
    KF_RETV();
    KF_END;
}
static void prefix_publish_finish(prefix_publish_on_F *F) {
    Entry *e = F->e; Words g = F->g; words_init(&F->g);
    PrefixFact *f = calloc(1, sizeof *f); require(f, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    f->src = F->dest; f->source = e->ref; f->face = F->guard; f->residual = F->target; f->receipt = F->receipt;
    f->gdeps = g.w; f->ngdeps = g.n; f->origin = F->origin;
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
    if (F->parent) XINC(pevx, EvalPrefixEvents, lifted); else XINC(pevx, EvalPrefixEvents, published);
    Task t; memset(&t, 0, sizeof t); t.is_notify = true; t.entry = F->dest; t.fact = f; t.idx = 0; t.limit = notify_limit;
    enqueue(t);
    fact_index(f, e->sside);
    /* HANDOFF §12: a slot waiting on this producer may adopt a later fact about the producer's committed residual,
     * through this fact as its connector: each waiting ticket registers a watch on that residual's shape */
    if (!E.no_adopt) { Task w = op_task(OP_CHILDWATCH); w.entry = F->dest; w.fact = f; w.idx = 0; w.limit = notify_limit; enqueue(w); }
}
#define prefix_publish_PARAMS(X) X(EntryId, dest) X(RefId, target) X(uint64_t, receipt) X(const PrefixFact *, parent) X(EntryId, origin)
KF_DECL(prefix_publish, void, prefix_publish_PARAMS, )
KF_STEP(prefix_publish) {
    KF_BEGIN(prefix_publish);
    if (F->dest) KF_CALL(prefix_publish_on, NULL, F->dest, F->target, F->receipt, F->parent, F->origin, ENT(F->dest)->face, 0, false, NULL, 0);
    KF_RETV();
    KF_END;
}
/* the lift of `res` (reached from the slot's requested reference by `rcpt`)
 * through the slot's recipe: SEQ for a forwarding or join slot, CONTEXT
 * through the eliminator's one-hole context; a family rewrite must hold
 * along the whole bound dimension (∀j) */
#define lift_through_PARAMS(X) X(const Cont *, kc) X(RefId, res) X(uint64_t, rcpt) X(FaceId, fface) X(RefId *, target) X(uint64_t *, receipt) X(FaceId *, child_guard)
KF_DECL_DROP(lift_through, bool, lift_through_PARAMS, lift_through_drop, Head ho; uint64_t lv;)
static void lift_through_drop(lift_through_F *F) { head_free(&F->ho); }
KF_STEP(lift_through) {
    KF_BEGIN(lift_through);
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    switch (F->kc->kind) {
    case K_FORWARD: *F->target = F->res; KF_CALL(rc_seq, F->receipt, F->kc->prefix, F->rcpt); break;                                    /* SEQ */
    case K_APP: case K_FST: case K_SND: case K_PAPP: case K_UNGLUE:                                              /* CONTEXT */
        KF_CALL(rebuild_elim, F->target, F->kc, F->res); KF_CALL(rc_rule, F->receipt, cong_of[F->kc->kind], F->rcpt, 0); break;
    case K_COMP_FAMILY: {
        KF_CALL(open_ref, NULL, F->kc->orig, &F->ho); F->lv = levels_first(F->ho.levels); if (F->ho.levels == LEVELS_NONE) F->lv = LEVEL_NONE; head_free(&F->ho);
        KF_CALL(mk_comp_lv, F->target, F->lv, F->kc->j, F->res, F->kc->phi, F->kc->tube, F->kc->cap); KF_CALL(rc_rule, F->receipt, RR_CONG_COMP, F->rcpt, 0); break;
    }
    case K_BRANCH:
        /* The branch's guarded entry receipt was captured before it was
         * launched; the join is reached only through the Cut's retained
         * handle, never through a copied pointer. */
        *F->target = F->res; KF_CALL(rc_seq, F->receipt, F->kc->prefix, F->rcpt); break;
    default: KF_RET(false);
    }
    if (F->kc->kind == K_COMP_FAMILY) KF_CALL(fc_forall, F->child_guard, F->kc->j, F->fface); else *F->child_guard = F->fface;
    KF_RET(true);
    KF_END;
}
/* one notification: the fact of `entry` to its waiter `idx`, then the cursor advances */
#define prefix_notify_PARAMS(X) X(Task, t)
KF_DECL(prefix_notify, void, prefix_notify_PARAMS, Cont kc; bool live, ok; uint64_t q, r1; const uint64_t *xd; size_t nxd; RefId target; uint64_t receipt; FaceId child_guard, g1, guard;)
KF_STEP(prefix_notify) {
    KF_BEGIN(prefix_notify);
    {
        Entry *e = ENT(F->t.entry);
        pthread_mutex_lock(&e->mu);
        if (e->state != E_RUNNING || F->t.idx >= F->t.limit || F->t.idx >= e->waiters.len) { pthread_mutex_unlock(&e->mu); KF_RETV(); }
        F->kc = *e->waiters.data[F->t.idx];       /* a copy: the waiter may be resumed and released once the lock is dropped */
        if (F->kc.cut) { cut_ref(F->kc.cut); gen_ref(F->kc.gen); }   /* the ticket's Cut and generation, retained for this step */
        pthread_mutex_unlock(&e->mu);
    }
    XINC(pevx, EvalPrefixEvents, notify_steps);
    { Task n = F->t;
      if (F->t.catchup) { n.fact = F->t.fact->next; if (n.fact) enqueue(n); }
      else { n.idx++; if (n.idx < n.limit) enqueue(n); }
    }
    F->live = true; F->q = 0; F->xd = NULL; F->nxd = 0;
    if (F->kc.cut) {   /* only the current generation of a WAITING slot lifts (a superseded ticket's slot has moved on) */
        pthread_mutex_lock(&F->kc.cut->mu); F->live = F->kc.cut->state == CUT_WAITING && F->kc.cut->cur == F->kc.gen; pthread_mutex_unlock(&F->kc.cut->mu);
        F->q = F->kc.gen->q; F->xd = F->kc.gen->d; F->nxd = F->kc.gen->nd;
    }
    F->target = 0; F->receipt = 0; F->child_guard = 0;
    if (F->live && F->kc.req == F->t.fact->source && F->kc.dest && F->kc.dest != F->t.fact->origin && F->kc.dest != F->t.entry) {
        KF_CALL(rc_seq, &F->r1, F->q, F->t.fact->receipt);
        KF_CALL(lift_through, &F->ok, &F->kc, F->t.fact->residual, F->r1, F->t.fact->face, &F->target, &F->receipt, &F->child_guard);
        if (F->ok) {
            KF_CALL(fc_meet, &F->g1, F->kc.chi, F->child_guard);
            KF_CALL(fc_meet, &F->guard, ENT(F->kc.dest)->face, F->g1);
            if (!fc_is_false(F->guard)) KF_CALL(prefix_publish_on, NULL, F->kc.dest, F->target, F->receipt, F->t.fact, F->t.fact->origin, F->guard, F->kc.prefix_premise, F->kc.kind == K_BRANCH, F->xd, F->nxd);
        }
    }
    if (F->kc.cut) { gen_unref(F->kc.gen); cut_unref(F->kc.cut); }
    KF_RETV();
    KF_END;
}
const PrefixFact *eval_entry_prefix(EntryId e) { return __atomic_load_n(&ENT(e)->prefix_head, __ATOMIC_ACQUIRE); }
size_t eval_entry_prefix_count(EntryId e) { Entry *x = ENT(e); pthread_mutex_lock(&x->mu); size_t n = x->n_prefix; pthread_mutex_unlock(&x->mu); return n; }
const PrefixFact *eval_entry_adapter_fact(EntryId e) { return ENT(e)->adapter_fact; }
bool eval_prefix_valid(const PrefixFact *f) { if (!f) return false; bool r; KStack *s_ = kf_sync_begin(); prefix_valid_push(s_, &r, f); kf_sync_run(s_); kf_sync_end(s_); return r; }
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
static Task op_task(uint8_t op) { Task t; memset(&t, 0, sizeof t); t.op = op; return t; }
static bool cut_live(Cut *c, Gen *g) { pthread_mutex_lock(&c->mu); bool l = c->state == CUT_WAITING && c->cur == g; pthread_mutex_unlock(&c->mu); return l; }
static void ticket_release(Cont *k);
static void proposal_free(Proposal *p) { if (p->tk) ticket_release(p->tk); if (p->ng) gen_unref(p->ng); words_free(&p->d); gen_unref(p->gen); cut_unref(p->cut); free(p); fine_bump(FC_CELLS_RELEASED); }

/* §2.2, publication side of the partition: under sub_mu the fact enters its
 * shape's history and the current subscriber list is captured; every
 * subscriber registered before is noticed (one per job), every later one
 * replays the fact from history — each (fact, subscription) pair exactly once */
static void fact_index(PrefixFact *f, ShapeSide *ss) {
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
static void sub_register(Cut *c, Gen *g, uint64_t sigma, ShapeSide *ss) {   /* ss: the watched shape's side (shape_side_get) */
    Sub *n = calloc(1, sizeof *n); require(n, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    n->refs = 1; n->cut = c; n->gen = g; n->sigma = sigma; n->owner = c->owner;
    pthread_mutex_lock(&E.sub_mu);
    /* a generation already killed takes no watch: its release job has run or will find nothing
     * (the killer marks it dead before taking this lock to release) */
    if (__atomic_load_n(&g->dead, __ATOMIC_ACQUIRE)) { pthread_mutex_unlock(&E.sub_mu); free(n); fine_bump(FC_CELLS_RELEASED); return; }
    cut_ref(c); gen_ref(g); __atomic_add_fetch(&E.live_subs, 1, __ATOMIC_RELAXED);
    n->gnext = g->watch; if (g->watch) g->watch->gpprev = &n->gnext; g->watch = n; n->gpprev = &g->watch;   /* the generation's watch list (non-owning) */
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
    if (E.no_adopt) return;
    Cut *c; Gen *g;
    if (!sub_pin(n, &c, &g)) return;   /* a released watch */
    if (!cut_live(c, g) || f->src == c->owner || f->origin == c->owner) { sub_unpin(c, g); return; }
    Entry *src = ENT(f->src);
    if (src->ref == g->r && src->face == g->eta) { sub_unpin(c, g); return; }
    Proposal *p = calloc(1, sizeof *p); require(p, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    p->cut = c; p->gen = g; p->f = f; p->sigma = n->sigma; words_init(&p->d);   /* the pin's references move into the proposal */
    XINC(cevx, EvalCutEvents, proposals);
    Task t = op_task(OP_PREPARE); t.p = p; enqueue(t);
}
/* the event that kills a generation releases its watches: one job, one watch per step (constant work under sub_mu) */
static void gen_release_watches(Gen *g) {
    pthread_mutex_lock(&E.sub_mu); bool any = g->watch != NULL; pthread_mutex_unlock(&E.sub_mu);   /* dead is set: no watch joins after this section */
    if (!any) return;
    gen_ref(g); Task t = op_task(OP_RELEASE); t.p2 = g; enqueue(t);
}
static void release_step(Task t) {
    Gen *g = t.p2;
    pthread_mutex_lock(&E.sub_mu);
    Sub *n = g->watch; Cut *c = NULL; Gen *ng = NULL;
    if (n) { sub_gunlink_locked(n); c = n->cut; ng = n->gen; n->cut = NULL; n->gen = NULL; }
    bool more = g->watch != NULL;
    pthread_mutex_unlock(&E.sub_mu);
    if (n) { XINC(cevx, EvalCutEvents, subs_released); cut_unref(c); gen_unref(ng); }
    if (more) { enqueue(t); return; }
    gen_unref(g);
}
/* subscription job of one generation: the residual's own shape, then one
 * recorded instantiation edge of the residual per step */
#define sub_step_PARAMS(X) X(Task, t)
KF_DECL(sub_step, void, sub_step_PARAMS, MapId ident; ShapeId sh; size_t e, np; const uint64_t *pairs; ShapeSide *ss;)
KF_STEP(sub_step) {
    KF_BEGIN(sub_step);
    {
        Cut *c = F->t.p; Gen *g = F->t.p2;
        if (cut_live(c, g)) {
            if (F->t.idx == 0) { KF_CALL0(map_identity, &F->ident); KF_CALL(shape_of, &F->sh, ((Gen *)F->t.p2)->r); KF_CALL(shape_side_get, &F->ss, F->sh, true); sub_register(F->t.p, F->t.p2, F->ident, F->ss); F->t.idx = 1; enqueue(F->t); KF_RETV(); }
            KF_CALL(instantiation_edges, &F->np, g->r, &F->pairs);
            F->e = F->t.idx - 1;
            if (F->e < F->np) { XINC(cevx, EvalCutEvents, edge_watches); KF_CALL(shape_of, &F->sh, F->pairs[2 * F->e]); KF_CALL(shape_side_get, &F->ss, F->sh, true); sub_register(F->t.p, F->t.p2, F->pairs[2 * F->e + 1], F->ss); F->t.idx++; enqueue(F->t); KF_RETV(); }
        }
    }
    gen_unref(F->t.p2); cut_unref(F->t.p);
    KF_RETV();
    KF_END;
}
static void replay_step(Task t) {
    Sub *n = t.p; XINC(cevx, EvalCutEvents, replays);
    consider(n, t.fact);
    if (t.fact->shape_next) { Cut *c; Gen *g; if (sub_pin(n, &c, &g)) { bool live = cut_live(c, g); sub_unpin(c, g); if (live) { t.fact = t.fact->shape_next; enqueue(t); return; } } }
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
    consider(n, t.fact);   /* a released or dead watch makes no proposal */
    Sub *nx = sub_advance(n);
    if (nx) { t.p = nx; enqueue(t); }
}
/* §2: an instantiation edge recorded after a subscription: a Cut whose
 * current residual is the edge's destination watches its source shape */
static void eval_edge_hook(RefId dest, RefId src, uint64_t sigma) {
    if (!__atomic_load_n(&E.live, __ATOMIC_ACQUIRE) || !__atomic_load_n(&E.live_subs, __ATOMIC_RELAXED)) return;
    Task t = op_task(OP_EDGE); t.r1 = dest; t.r2 = src; t.sigma = sigma; enqueue(t);
}
#define edge_step_PARAMS(X) X(Task, t)
KF_DECL_DROP(edge_step, void, edge_step_PARAMS, edge_step_drop, Sub *n; ShapeId sh; Cut *pc; Gen *pg; ShapeSide *ss;)
static void edge_step_drop(edge_step_F *F) { if (F->pc) { sub_unpin(F->pc, F->pg); F->pc = NULL; } }
KF_STEP(edge_step) {
    KF_BEGIN(edge_step);
    F->n = F->t.p;
    if (!F->n) {
        KF_CALL(shape_of, &F->sh, F->t.r1);
        KF_CALL(shape_side_get, &F->ss, F->sh, false);
        { ShapeSide *ss = F->ss; if (!ss) KF_RETV();
          pthread_mutex_lock(&E.sub_mu); Sub *drop = sub_unlink_one_locked(&ss->subs); F->n = ss->subs; sub_ref(F->n); pthread_mutex_unlock(&E.sub_mu);
          sub_unref(drop); }
        if (!F->n) KF_RETV();
    }
    if (map_is_identity(F->n->sigma) && sub_pin(F->n, &F->pc, &F->pg)) {
        if (F->pg->r == F->t.r1 && cut_live(F->pc, F->pg)) { XINC(cevx, EvalCutEvents, edge_watches); KF_CALL(shape_of, &F->sh, F->t.r2); KF_CALL(shape_side_get, &F->ss, F->sh, true); sub_register(F->pc, F->pg, F->t.sigma, F->ss); }
        sub_unpin(F->pc, F->pg); F->pc = NULL;
    }
    { Sub *nx = sub_advance(F->n);
      if (nx) { Task t = F->t; t.p = nx; enqueue(t); } }
    KF_RETV();
    KF_END;
}
/* §3 preparation, one bounded step per job, outside every lock:
 *   0  boundary correspondence s[σ] = r, required face ψ ⊢ φ[σ], adapted
 *      residual v and its key under the destination's projected face, the
 *      unchanged-key and revisited-key rejections (a shared cached result);
 *   1  one premise (symbol, revision) per step against the captured stamp;
 *   2  one dependency pair of Δq ∪ Δ(r⇒v) per step;
 *   then q' = q ; ρ and the installation job. */
#define prepare_step_PARAMS(X) X(Task, t)
KF_DECL(prepare_step, void, prepare_step_PARAMS, Proposal *p; Cut *c; Gen *g; const PrefixFact *f, *hf; uint64_t key[4], id; PrepMemo m; bool ident, ok; RefId src, target; FaceId need; ShapeId s1, s2; EntryId ce; Gen *h; uint64_t q1;)
KF_STEP(prepare_step) {
    KF_BEGIN(prepare_step);
    F->p = F->t.p; F->c = F->p->cut; F->g = F->p->gen; F->f = F->p->f;
    XINC(cevx, EvalCutEvents, prep_steps); fine_bump(FC_ADAPTER_STEPS);
    if (!cut_live(F->c, F->g)) { proposal_free(F->p); KF_RETV(); }        /* superseded or resumed meanwhile: ownership released, nothing altered */
    if (F->p->phase == 0) {
        F->p->stamp = global_env_version();
        F->key[0] = F->f->id; F->key[1] = F->g->r; F->key[2] = F->c->psi; F->key[3] = F->p->sigma;
        KF_CALL(interner_intern, &F->id, &E.prep_keys, F->key, 4, NULL);
        (void)chunked_at(&E.prep_tab, F->id - 1);
        pthread_mutex_lock(&E.prep_mu);
        { PrepMemo *slot = chunked_at(&E.prep_tab, F->id - 1); F->m = *slot;
          if (F->m.state == 0) slot->state = 3; }                   /* this job computes it; any other joins */
        pthread_mutex_unlock(&E.prep_mu);
        if (F->m.state == 3) { XINC(cevx, EvalCutEvents, prep_joined); enqueue(F->t); KF_RETV(); }   /* joined: retried after the computing job publishes */
        if (F->m.state == 0) {
            F->ident = map_is_identity(F->p->sigma);
            if (F->ident) F->src = F->f->source; else KF_CALL(reindex, &F->src, F->f->source, F->p->sigma);
            F->m.direct = F->src == F->g->r;
            if (F->ident) F->need = F->f->face; else KF_CALL(fc_reindex, &F->need, F->f->face, F->p->sigma);
            KF_CALL(fc_entails, &F->ok, F->c->psi, F->need);
            F->m.v = 0; F->m.veta = 0; F->m.adrc = 0;
            if (F->ok) {
                if (F->ident) F->m.v = F->f->residual; else KF_CALL(reindex, &F->m.v, F->f->residual, F->p->sigma);
                KF_CALL(key_face, &F->m.veta, F->m.v, F->c->psi);
                KF_CALL(shape_of, &F->s1, F->m.v); KF_CALL(shape_of, &F->s2, F->g->r);
                F->ok = !(F->s1 == F->s2 && F->m.veta == F->g->eta);
                if (F->ok) KF_CALL(fc_entails, &F->ok, F->m.veta, ref_required(F->m.v));
            }
            if (F->ok) { if (F->ident) KF_CALL(rc, &F->m.adrc, RC_PREFIX_RESTRICT, F->f->id, F->g->eta, 0, 3); else KF_CALL(rc, &F->m.adrc, RC_PREFIX_SPEC, F->f->id, F->p->sigma, 0, 3); }
            F->m.state = F->ok ? 1 : 2;
            pthread_mutex_lock(&E.prep_mu); *(PrepMemo *)chunked_at(&E.prep_tab, F->id - 1) = F->m; pthread_mutex_unlock(&E.prep_mu);
            XINC(cevx, EvalCutEvents, prep_computed);
        } else XINC(cevx, EvalCutEvents, prep_shared);
        F->ok = F->m.state == 1;
        for (F->h = F->g; F->ok && F->h; F->h = F->h->prev) { KF_CALL(shape_of, &F->s2, F->h->r); KF_CALL(shape_of, &F->s1, F->m.v); if (F->s2 == F->s1 && F->h->eta == F->m.veta) F->ok = false; }   /* no return to a key this slot already passed */
        if (!F->ok) { XINC(cevx, EvalCutEvents, prep_rejected); proposal_free(F->p); KF_RETV(); }
        F->p->v = F->m.v; F->p->veta = F->m.veta; F->p->adrc = F->m.adrc;
        if (!F->m.direct) {   /* the fact's source is not the current residual: a connector u ⇒* s[σ] is required —
                               * a committed fact of the slot's own child producer (source u), searched one per step */
            KF_CALL(eval_entry_lookup, &F->ce, F->g->r, F->g->eta);
            F->p->scan = F->ce ? eval_entry_prefix(F->ce) : NULL;
            F->p->phase = 4; enqueue(F->t); KF_RETV();
        }
        F->p->phase = 1; F->p->k = 0; enqueue(F->t); KF_RETV();
    }
    if (F->p->phase == 4) {   /* connector search: one committed fact of the child producer per step */
        XINC(cevx, EvalCutEvents, connector_steps);
        { const PrefixFact *h = F->p->scan;
          if (!h) { XINC(cevx, EvalCutEvents, connector_missing); XINC(cevx, EvalCutEvents, prep_rejected); proposal_free(F->p); KF_RETV(); }   /* two facts from one old source do not supply it */
          F->p->scan = h->next; F->hf = h; }
        if (map_is_identity(F->p->sigma)) F->target = F->f->source; else KF_CALL(reindex, &F->target, F->f->source, F->p->sigma);
        F->ok = F->hf != F->f && F->hf->source == F->g->r && F->hf->residual == F->target;
        if (F->ok) KF_CALL(fc_entails, &F->ok, F->c->psi, F->hf->face);
        if (F->ok) { F->p->conn = F->hf; F->p->phase = 1; F->p->k = 0; XINC(cevx, EvalCutEvents, connectors); }
        enqueue(F->t); KF_RETV();
    }
    if (F->p->phase == 1) {   /* the fact's premises, the connector's premises, then the generation's inherited certificate, against the stamp */
        Proposal *p = F->p; const PrefixFact *f = F->f; Gen *g = F->g;
        size_t nc = p->conn ? p->conn->ngdeps : 0;
        if (p->k + 1 < f->ngdeps + nc + g->nd) {
            const uint64_t *pr = p->k < f->ngdeps ? f->gdeps + p->k : p->k < f->ngdeps + nc ? p->conn->gdeps + (p->k - f->ngdeps) : g->d + (p->k - f->ngdeps - nc);
            if (global_revision(pr[0]) != pr[1]) { { XCount *sl = p->revalidating ? XSLOT(cevx, EvalCutEvents, revalidation_failed) : XSLOT(cevx, EvalCutEvents, prep_rejected); xc_inc(sl); XEV(cevx, sl); } proposal_free(p); KF_RETV(); }
            p->k += 2; enqueue(F->t); KF_RETV();
        }
        if (p->revalidating) { Task n = op_task(OP_INSTALL); n.p = p; enqueue(n); KF_RETV(); }
        p->phase = 2; p->k = 0; enqueue(F->t); KF_RETV();
    }
    {
        Proposal *p = F->p; const PrefixFact *f = F->f; Gen *g = F->g;
        size_t ncon = p->conn ? p->conn->ngdeps : 0;
        size_t total = g->nd + ncon + f->ngdeps;
        if (p->k + 1 < total) {
            const uint64_t *src = p->k < g->nd ? g->d + p->k : p->k < g->nd + ncon ? p->conn->gdeps + (p->k - g->nd) : f->gdeps + (p->k - g->nd - ncon);
            words_push(&p->d, src[0]); words_push(&p->d, src[1]);
            p->k += 2; enqueue(F->t); KF_RETV();
        }
    }
    /* q' = q ; χ ; ρ[σ] */
    if (F->p->conn) { KF_CALL(rc_seq, &F->q1, F->g->q, F->p->conn->receipt); KF_CALL(rc_seq, &F->p->q, F->q1, F->p->adrc); }
    else KF_CALL(rc_seq, &F->p->q, F->g->q, F->p->adrc);
    /* the replacement generation and its ticket are prepared here, so installation only links them */
    F->p->ng = gen_new(F->p->v, F->p->veta, F->p->q, F->p->d.w, F->p->d.n, F->p->gen); words_init(&F->p->d);
    F->p->tk = ticket_new(F->c, F->p->ng);
    { Task n = op_task(OP_INSTALL); n.p = F->p; enqueue(n); }
    KF_RETV();
    KF_END;
}
/* §4 installation under the Cut's lock: WAITING, the captured generation, the
 * validated stamp (else the same proposal revalidates its premises); then the
 * prepared handles are installed, the replacement request's launch reserved,
 * and it is enqueued after unlocking. The superseded ticket stays live. */
#define install_step_PARAMS(X) X(Task, t)
KF_DECL(install_step, void, install_step_PARAMS, Proposal *p; Cut *c; Gen *ng; Gen *old; Entry *o; FaceId need, g1, guard; RefId target; uint64_t receipt; FaceId cg; bool ok;)
KF_STEP(install_step) {
    KF_BEGIN(install_step);
    F->p = F->t.p; F->c = F->p->cut;
    {
        Proposal *p = F->p; Cut *c = F->c;
        pthread_mutex_lock(&c->mu);
        if (c->state != CUT_WAITING) { pthread_mutex_unlock(&c->mu); XINC(cevx, EvalCutEvents, install_not_waiting); proposal_free(p); KF_RETV(); }
        if (c->cur != p->gen) { pthread_mutex_unlock(&c->mu); XINC(cevx, EvalCutEvents, install_stale_generation); proposal_free(p); KF_RETV(); }
        uint64_t now = global_env_version();
        if (now != p->stamp) {
            pthread_mutex_unlock(&c->mu);
            XINC(cevx, EvalCutEvents, revalidations);
            p->stamp = now; p->phase = 1; p->k = 0; p->revalidating = true;
            Task n = op_task(OP_PREPARE); n.p = p; enqueue(n); KF_RETV();
        }
        Gen *ng = p->ng; Cont *tk = p->tk; p->ng = NULL; p->tk = NULL;   /* the prepared handles move into the Cut and the request */
        Gen *old = c->cur; c->cur = ng; c->installs++;
        __atomic_store_n(&old->dead, true, __ATOMIC_RELEASE);
        reserve_job();
        pthread_mutex_unlock(&c->mu);
        gen_release_watches(old);                        /* the superseding event releases the old generation's watches */
        XINC(cevx, EvalCutEvents, installs); XINC(cevx, EvalCutEvents, tickets);
        Entry *o = ENT(c->owner);
        pthread_mutex_lock(&o->mu); if (old->have_dep && old->dep_idx < o->dep_hist.len) o->dep_hist.data[old->dep_idx] = 1; pthread_mutex_unlock(&o->mu);   /* the superseded request becomes a historical edge */
        gen_unref(old);                                  /* the Cut's reference; the new generation retains it */
        Task rq = op_task(OP_REQUEST); rq.k = tk; enqueue_reserved(rq);
        F->ng = ng; F->o = o;
    }
    /* the owner's derived prefix (K applied to v) through the bounded publication protocol */
    if (map_is_identity(F->p->sigma)) F->need = F->p->f->face; else KF_CALL(fc_reindex, &F->need, F->p->f->face, F->p->sigma);
    F->target = 0; F->receipt = 0; F->cg = 0;
    KF_CALL(lift_through, &F->ok, &F->c->K, F->ng->r, F->ng->q, F->need, &F->target, &F->receipt, &F->cg);
    if (F->ok) {
        KF_CALL(fc_meet, &F->g1, F->c->K.chi, F->cg);
        KF_CALL(fc_meet, &F->guard, F->o->face, F->g1);
        if (!fc_is_false(F->guard)) KF_CALL(prefix_publish_on, NULL, F->c->owner, F->target, F->receipt, F->p->f, F->p->f->origin, F->guard, F->c->K.prefix_premise, F->c->K.kind == K_BRANCH, F->ng->d, F->ng->nd);
    }
    proposal_free(F->p);
    KF_RETV();
    KF_END;
}
#define childwatch_step_PARAMS(X) X(Task, t)
KF_DECL_DROP(childwatch_step, void, childwatch_step_PARAMS, childwatch_step_drop, Cut *c; Gen *g; bool more; MapId ident; ShapeId sh; ShapeSide *ss;)
static void childwatch_step_drop(childwatch_step_F *F) { if (F->c) { gen_unref(F->g); cut_unref(F->c); F->c = NULL; } }
KF_STEP(childwatch_step) {
    KF_BEGIN(childwatch_step);
    {
        Entry *e = ENT(F->t.entry);
        if (F->t.idx >= F->t.limit) KF_RETV();
        pthread_mutex_lock(&e->mu);
        Cont *k = F->t.idx < e->waiters.len ? e->waiters.data[F->t.idx] : NULL;
        F->c = k && k->cut ? k->cut : NULL; F->g = F->c ? k->gen : NULL;
        if (F->c) { cut_ref(F->c); gen_ref(F->g); }
        F->more = F->t.idx + 1 < e->waiters.len;
        pthread_mutex_unlock(&e->mu);
    }
    if (F->c) {
        if (F->g->r == ENT(F->t.entry)->ref && cut_live(F->c, F->g)) {
            XINC(cevx, EvalCutEvents, child_watches);
            KF_CALL0(map_identity, &F->ident); KF_CALL(shape_of, &F->sh, F->t.fact->residual); KF_CALL(shape_side_get, &F->ss, F->sh, true);
            sub_register(F->c, F->g, F->ident, F->ss);
        }
        gen_unref(F->g); cut_unref(F->c); F->c = NULL;
    }
    if (F->more) { Task n = F->t; n.idx++; enqueue(n); }
    KF_RETV();
    KF_END;
}
#define request_step_PARAMS(X) X(Task, t)
KF_DECL(request_step, void, request_step_PARAMS, )
KF_STEP(request_step) {
    KF_BEGIN(request_step);
    KF_CALL(eval_request, NULL, F->t.k->gen->r, F->t.k->cut->psi, F->t.k);    /* a new real consumer occurrence of the owner */
    KF_RETV();
    KF_END;
}
/* a dependency pair of the winning generation's certificate; a conflicting
 * revision is kept beside the other (the answer's validity check rejects it) */
static void gdeps_add_cert(Entry *e, SymbolId sym, uint64_t rev) {
    for (size_t k = 0; k + 1 < e->gdeps.len; k += 2) if (e->gdeps.data[k] == sym && e->gdeps.data[k + 1] == rev) return;
    vec_push(&e->gdeps, sym); vec_push(&e->gdeps, rev);
}
static void resume_push(KStack *ks, void *ret, Cont *k, EvalResult *r);
/* §5 delivery: consumed once; the current generation of a WAITING slot wins
 * WAITING → RESUMING and executes the recipe once; any other ticket is
 * released with no semantic resume and no parent publication */
#define cut_deliver_PARAMS(X) X(Cont *, k) X(EvalResult *, r)
KF_DECL(cut_deliver, void, cut_deliver_PARAMS, Cut *c; Gen *g; Cont view; size_t i;)
KF_STEP(cut_deliver) {
    KF_BEGIN(cut_deliver);
    F->c = F->k->cut;
    {
        pthread_mutex_lock(&F->c->mu);
        bool win = F->c->state == CUT_WAITING && F->c->cur == F->k->gen;
        if (win) { F->c->state = CUT_RESUMING; __atomic_store_n(&F->k->gen->dead, true, __ATOMIC_RELEASE); }
        pthread_mutex_unlock(&F->c->mu);
        if (!win) { XINC(cevx, EvalCutEvents, deliveries_stale); ticket_release(F->k); KF_RETV(); }
    }
    gen_release_watches(F->k->gen);                      /* the resuming event releases the generation's watches */
    XINC(cevx, EvalCutEvents, deliveries_current);
    F->g = F->k->gen;
    if (F->g->nd) { Entry *o = ENT(F->c->owner); for (F->i = 0; F->i + 1 < F->g->nd; F->i += 2) { pthread_mutex_lock(&o->mu); gdeps_add_cert(o, F->g->d[F->i], F->g->d[F->i + 1]); pthread_mutex_unlock(&o->mu); fine_bump(FC_ADAPTER_STEPS); KF_SAFE(); o = ENT(F->c->owner); } }
    F->view = F->c->K; F->view.child = F->k->child; F->view.req = F->k->req; F->view.aq = F->g->q;
    KF_CALL(resume, NULL, &F->view, F->r);
    pthread_mutex_lock(&F->c->mu); F->c->state = CUT_CLOSED; pthread_mutex_unlock(&F->c->mu);
    XINC(cevx, EvalCutEvents, resumes);
    ticket_release(F->k);
    KF_RETV();
    KF_END;
}
#define op_dispatch_PARAMS(X) X(Task, t)
KF_DECL(op_dispatch, void, op_dispatch_PARAMS, )
KF_STEP(op_dispatch) {
    KF_BEGIN(op_dispatch);
    switch (F->t.op) {
    case OP_SUB: KF_CALL(sub_step, NULL, F->t); break;
    case OP_REPLAY: replay_step(F->t); break;
    case OP_FACTNOTE: notice_step(F->t); break;
    case OP_PREPARE: KF_CALL(prepare_step, NULL, F->t); break;
    case OP_INSTALL: KF_CALL(install_step, NULL, F->t); break;
    case OP_REQUEST: KF_CALL(request_step, NULL, F->t); break;
    case OP_EDGE: KF_CALL(edge_step, NULL, F->t); break;
    case OP_CHILDWATCH: KF_CALL(childwatch_step, NULL, F->t); break;
    case OP_RELEASE: release_step(F->t); break;
    case OP_EXT: ((void (*)(void *))F->t.p)(F->t.p2); break;   /* a job of another layer (taken only by plain threads, never inside an engine step) */
    default: die("unknown evaluator job");
    }
    KF_RETV();
    KF_END;
}
static EvalTaskInfo task_info(const Task *t) {
    EvalTaskInfo in; memset(&in, 0, sizeof in);
    if (t->is_pair) { in.kind = ET_PAIR; return in; }
    if (t->is_notify) { in.kind = ET_NOTIFY; in.producer = t->entry; return in; }
    if (t->is_resume) { in.kind = ET_RESUME; in.producer = t->k->kind == K_ROOT || t->k->kind == K_EXTERNAL ? 0 : t->k->dest; in.child = t->k->child; in.ticket = t->k->cut != NULL; return in; }
    switch (t->op) {
    case OP_NONE: in.kind = ET_EVALUATE; in.producer = t->entry; break;
    case OP_SUB: in.kind = ET_SUBSCRIBE; in.producer = ((Cut *)t->p)->owner; break;
    case OP_REPLAY: in.kind = ET_REPLAY; in.producer = ((Sub *)t->p)->owner; in.fact = t->fact; break;
    case OP_FACTNOTE: in.kind = ET_NOTICE; in.producer = ((Sub *)t->p)->owner; in.fact = t->fact; break;
    case OP_PREPARE: in.kind = ET_PREPARE; in.producer = ((Proposal *)t->p)->cut->owner; in.fact = ((Proposal *)t->p)->f; break;
    case OP_INSTALL: in.kind = ET_INSTALL; in.producer = ((Proposal *)t->p)->cut->owner; in.fact = ((Proposal *)t->p)->f; break;
    case OP_REQUEST: in.kind = ET_REQUEST; in.producer = t->k->dest; in.ticket = true; break;
    case OP_EDGE: in.kind = ET_EDGE; break;
    case OP_CHILDWATCH: in.kind = ET_SUBSCRIBE; in.producer = t->entry; break;
    case OP_EXT: in.kind = ET_EXTERNAL; in.tag = (int)t->idx; break;
    case OP_RELEASE: in.kind = ET_RELEASE; break;
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
    case OP_RELEASE: gen_unref(t.p2); break;
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
    if (kf_tl || !E.ext_head) return NULL;
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
#define publish_branchwise_PARAMS(X) X(EntryId, dest) X(FaceId, chi) X(size_t, n) X(const FaceId *, faces) X(const RefId *, terms) X(EntryId, premise) X(uint64_t, congruence)
KF_DECL(publish_branchwise, void, publish_branchwise_PARAMS, Gather *g; size_t i; Cont *k; RefId sys; uint64_t r1;)
KF_STEP(publish_branchwise) {
    KF_BEGIN(publish_branchwise);
    F->g = calloc(1, sizeof *F->g);
    require(F->g, "out of memory"); fine_bump(FC_CELLS_ALLOCATED);
    F->g->dest = F->dest; F->g->n = F->n;
    F->g->faces = malloc((F->n ? F->n : 1) * sizeof(FaceId));
    F->g->results = calloc(F->n ? F->n : 1, sizeof(EvalResult *));
    require(F->g->faces && F->g->results, "out of memory");
    if (F->n) memcpy(F->g->faces, F->faces, F->n * sizeof(FaceId));
    pthread_mutex_init(&F->g->mu, NULL);
    F->g->refs = 1;                               /* the creator; each branch Cut retains the join (LIVE-CUT-ADOPTION §5) */
    if (F->n == 0) { gather_unref(F->g); KF_CALL(mk_system, &F->sys, 0, NULL, NULL); KF_CALL(publish, NULL, F->dest, result_system(F->sys, 0, NULL, NULL)); KF_RETV(); }
    for (F->i = 0; F->i < F->n; F->i++) {
        { FaceId m; KF_CALL(fc_meet, &F->r1, F->chi, F->faces[F->i]); m = F->r1; F->k = cont_new(K_BRANCH, F->dest, m); }
        F->k->gather = F->g; F->k->branch = F->i; F->k->orig = F->terms[F->i];
        F->k->prefix_premise = F->premise;
        KF_CALL(rc_rule, &F->r1, RR_SYSTEM_BRANCH, F->terms[F->i], F->faces[F->i]);
        KF_CALL(rc_seq, &F->k->prefix, F->congruence, F->r1);
        KF_CALL(eval_request, NULL, F->terms[F->i], F->k->chi, F->k);
    }
    gather_unref(F->g);
    KF_RETV();
    KF_END;
}

#define resume_branch_PARAMS(X) X(Cont *, k) X(EvalResult *, r)
KF_DECL_DROP(resume_branch, void, resume_branch_PARAMS, resume_branch_drop, Gather *g; EntryId dest; EvalResult *out; size_t i, j; Words fs, ts; FaceId m; RefId owner; uint64_t rr;)
static void resume_branch_drop(resume_branch_F *F) { words_free(&F->fs); words_free(&F->ts); }
KF_STEP(resume_branch) {
    KF_BEGIN(resume_branch);
    F->g = F->k->gather;
    {
        pthread_mutex_lock(&F->g->mu);
        F->g->results[F->k->branch] = F->r;
        if (F->r->cls == R_INVALID || F->r->cls == R_NO_OBSERVATION) F->g->failed = true;
        bool full = (++F->g->arrived == F->g->n);
        pthread_mutex_unlock(&F->g->mu);
        if (!full) KF_RETV();                          /* the join is enabled only when every box is full */
    }
    F->dest = F->g->dest;
    if (F->g->failed) {
        /* select the failure by original branch order, independent of arrival order */
        F->out = NULL;
        for (size_t i = 0; i < F->g->n && !F->out; i++) {
            EvalResult *b = F->g->results[i];
            if (b->cls == R_INVALID) F->out = b;
            else if (b->cls == R_NO_OBSERVATION) F->out = result_invalid("branch under an inconsistent guard");
        }
        KF_CALL(publish, NULL, F->dest, F->out);                     /* the join's storage stays with its retaining Cuts */
        KF_RETV();
    }
    /* reconstruct: nested system results are flattened under conjoined guards */
    words_init(&F->fs); words_init(&F->ts);
    for (F->i = 0; F->i < F->g->n; F->i++) {
        if (F->g->results[F->i]->cls == R_SYSTEM) {
            for (F->j = 0; F->j < F->g->results[F->i]->nbr; F->j++) { KF_CALL(fc_meet, &F->m, F->g->faces[F->i], F->g->results[F->i]->faces[F->j]); words_push(&F->fs, F->m); words_push(&F->ts, F->g->results[F->i]->terms[F->j]); }
        } else { words_push(&F->fs, F->g->faces[F->i]); words_push(&F->ts, F->g->results[F->i]->ref); }
    }
    KF_CALL(mk_system, &F->owner, F->fs.n, F->fs.w, F->ts.w);
    F->out = result_system(F->owner, F->fs.n, F->fs.w, F->ts.w);
    words_free(&F->fs); words_free(&F->ts);
    reuse_bump(REUSE_SYSTEM_RULE);
    KF_CALL(rc_rule, &F->rr, RR_SYSTEM_DIST, 0, 0);
    KF_CALL(publish_with, NULL, F->dest, F->out, F->owner, F->rr);
    KF_RETV();
    KF_END;
}

#define distribute_PARAMS(X) X(const Cont *, k) X(const EvalResult *, sys)
KF_DECL_DROP(distribute, void, distribute_PARAMS, distribute_drop, RefId *terms; size_t i; uint64_t c1, c2;)
static void distribute_drop(distribute_F *F) { free(F->terms); F->terms = NULL; }
KF_STEP(distribute) {
    KF_BEGIN(distribute);
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    F->terms = malloc((F->sys->nbr ? F->sys->nbr : 1) * sizeof(RefId));
    require(F->terms, "out of memory");
    for (F->i = 0; F->i < F->sys->nbr; F->i++) KF_CALL(rebuild_elim, &F->terms[F->i], F->k, F->sys->terms[F->i]);
    KF_CALL(child_rc, &F->c1, F->k);
    KF_CALL(rc_rule, &F->c2, cong_of[F->k->kind], F->c1, 0);
    KF_CALL(publish_branchwise, NULL, F->k->dest, F->k->chi, F->sys->nbr, F->sys->faces, F->terms, F->k->child, F->c2);
    free(F->terms); F->terms = NULL;
    KF_RETV();
    KF_END;
}

#define resume_comp_family_PARAMS(X) X(Cont *, k) X(EvalResult *, r)
KF_DECL_DROP(resume_comp_family, void, resume_comp_family_PARAMS, resume_comp_family_drop, Head ho; uint64_t lv; RefId fam_res, residual, out, ti; uint64_t c1, c2, c3; FaceId *faces; RefId *terms; size_t kept, i; FaceId uni, g, m; bool ent;)
static void resume_comp_family_drop(resume_comp_family_F *F) { head_free(&F->ho); free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; }
KF_STEP(resume_comp_family) {
    KF_BEGIN(resume_comp_family);
    if (F->r->cls == R_NEUTRAL) {
        /* rebuild the composition around the residual family: no re-evaluation of the family */
        KF_CALL(open_ref, NULL, F->k->orig, &F->ho); F->lv = levels_first(F->ho.levels); if (F->ho.levels == LEVELS_NONE) F->lv = LEVEL_NONE; head_free(&F->ho);
        F->fam_res = residual_of(F->k->child);
        if (F->fam_res) KF_CALL(mk_comp_lv, &F->residual, F->lv, F->k->j, F->fam_res, F->k->phi, F->k->tube, F->k->cap); else F->residual = F->k->orig;
        KF_CALL(child_rc, &F->c1, F->k); KF_CALL(rc_rule, &F->c2, RR_CONG_COMP, F->c1, 0);
        KF_CALL(publish_with, NULL, F->k->dest, result_new(R_NEUTRAL, F->k->orig), F->residual, F->c2);
        KF_RETV();
    }
    if (F->r->cls == R_SYSTEM) {
        /* branch available along the whole j line: outer guard ∀j.phi_k */
        F->faces = malloc((F->r->nbr ? F->r->nbr : 1) * sizeof(FaceId));
        F->terms = malloc((F->r->nbr ? F->r->nbr : 1) * sizeof(RefId));
        require(F->faces && F->terms, "out of memory");
        F->kept = 0; KF_CALL0(fc_false, &F->uni);
        for (F->i = 0; F->i < F->r->nbr; F->i++) {
            KF_CALL(fc_forall, &F->g, F->k->j, F->r->faces[F->i]);
            KF_CALL(fc_meet, &F->m, F->k->chi, F->g);
            if (fc_is_false(F->m)) continue;
            F->faces[F->kept] = F->g;
            KF_CALL(open_ref, NULL, F->k->orig, &F->ho); F->lv = levels_first(F->ho.levels); if (F->ho.levels == LEVELS_NONE) F->lv = LEVEL_NONE; head_free(&F->ho);
            KF_CALL(mk_comp_lv, &F->terms[F->kept], F->lv, F->k->j, F->r->terms[F->i], F->k->phi, F->k->tube, F->k->cap);
            F->kept++;
            KF_CALL(fc_join, &F->uni, F->uni, F->g);
        }
        KF_CALL(fc_entails, &F->ent, F->k->chi, F->uni);
        if (!F->ent) { free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; KF_CALL(publish, NULL, F->k->dest, result_invalid("type-family system has no branch along the whole composition line")); KF_RETV(); }
        for (F->i = 0; F->i < F->kept; F->i++) {
            KF_CALL(fc_entails, &F->ent, F->k->chi, F->faces[F->i]);
            if (F->ent) { F->ti = F->terms[F->i]; free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL; KF_CALL(forward, NULL, F->ti, F->k->chi, F->k->dest); KF_RETV(); }
        }
        KF_CALL(child_rc, &F->c1, F->k); KF_CALL(rc_rule, &F->c2, RR_CONG_COMP, F->c1, 0);
        KF_CALL(publish_branchwise, NULL, F->k->dest, F->k->chi, F->kept, F->faces, F->terms, F->k->child, F->c2);
        free(F->faces); F->faces = NULL; free(F->terms); F->terms = NULL;
        KF_RETV();
    }
    /* introduction: capture the retained components of the exposed head
     * and instantiate the one fixed clause (§53–§54); the producer entry's
     * face is the clause's source annotation κ */
    KF_CALL(comp_clause, &F->out, F->k->j, F->r->ref, F->k->phi, F->k->tube, F->k->cap, ENT(F->k->dest)->face);
    if (!F->out) { KF_CALL(publish, NULL, F->k->dest, result_invalid("composition in a family whose head is not a type former or lacks its universe annotation")); KF_RETV(); }
    reuse_bump(REUSE_COMP_EXPAND);
    KF_CALL(child_rc, &F->c1, F->k); KF_CALL(rc_rule, &F->c2, RR_CONG_COMP, F->c1, 0); KF_CALL(rc_rule, &F->c3, RR_COMP_EXPAND, 0, 0);
    KF_CALL(rc_seq, &F->c1, F->c2, F->c3);
    KF_CALL(forward_rc, NULL, F->out, F->k->chi, F->k->dest, F->c1);
    KF_RETV();
    KF_END;
}

#define resume_PARAMS(X) X(Cont *, k) X(EvalResult *, r)
KF_DECL_DROP(resume, void, resume_PARAMS, resume_drop, uint64_t cong, c1, c2; RefId sres, res2, x; Head h;)
static void resume_drop(resume_F *F) { head_free(&F->h); }
KF_STEP(resume) {
    KF_BEGIN(resume);
    static const uint64_t cong_of[] = { 0, 0, 0, RR_CONG_APP, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE };
    switch (F->k->kind) {
    case K_ROOT: {
        RootBox *b = F->k->root;
        pthread_mutex_lock(&b->mu); b->result = F->r; b->done = true; pthread_cond_broadcast(&b->cv); pthread_mutex_unlock(&b->mu);
        /* wake clients waiting for either their root or quiescence */
        pthread_mutex_lock(&E.q_mu); pthread_cond_broadcast(&E.idle_cv); pthread_mutex_unlock(&E.q_mu);
        rootbox_release(b);
        KF_RETV();
    }
    case K_EXTERNAL: F->k->ext_fn(F->k->ext_ctx, F->r); KF_RETV();
    case K_BRANCH: KF_CALL(resume_branch, NULL, F->k, F->r); KF_RETV();
    default: break;
    }
    if (F->r->cls == R_NO_OBSERVATION || F->r->cls == R_INVALID) { KF_CALL(publish_with, NULL, F->k->dest, F->r, 0, 0); KF_RETV(); }
    if (F->k->kind == K_FORWARD) { KF_CALL(child_rc, &F->c1, F->k); KF_CALL(rc_seq, &F->c2, F->k->prefix, F->c1); KF_CALL(publish_with, NULL, F->k->dest, F->r, residual_of(F->k->child), F->c2); KF_RETV(); }
    if (F->k->kind == K_COMP_FAMILY) { KF_CALL(resume_comp_family, NULL, F->k, F->r); KF_RETV(); }
    KF_CALL(child_rc, &F->c1, F->k);
    KF_CALL(rc_rule, &F->cong, cong_of[F->k->kind], F->c1, 0);
    if (F->r->cls == R_NEUTRAL) {
        /* §78.2: the residual is the eliminator rebuilt around the scrutinee's residual */
        F->sres = residual_of(F->k->child);
        if (F->sres) KF_CALL(rebuild_elim, &F->res2, F->k, F->sres); else F->res2 = F->k->orig;
        KF_CALL(publish_with, NULL, F->k->dest, result_new(R_NEUTRAL, F->k->orig), F->res2, F->cong);
        KF_RETV();
    }
    if (F->r->cls == R_SYSTEM) { KF_CALL(distribute, NULL, F->k, F->r); KF_RETV(); }
    /* introduction under an eliminator */
    KF_CALL(open_ref, NULL, F->r->ref, &F->h);
    switch (F->k->kind) {
    case K_APP:
        if (F->h.tag != T_LAM) { KF_CALL(publish, NULL, F->k->dest, result_invalid("application of a non-function introduction")); break; }
        reuse_bump(REUSE_BETA);
        KF_CALL(apply_term_binder, &F->x, F->r->ref, 0, 1, F->k->a);
        KF_CALL(rc_rule, &F->c1, RR_BETA, 0, 0); KF_CALL(rc_seq, &F->c2, F->cong, F->c1);
        KF_CALL(forward_rc, NULL, F->x, F->k->chi, F->k->dest, F->c2);
        break;
    case K_FST: case K_SND:
        if (F->h.tag != T_PAIR) { KF_CALL(publish, NULL, F->k->dest, result_invalid("projection of a non-pair introduction")); break; }
        reuse_bump(F->k->kind == K_FST ? REUSE_FST : REUSE_SND);
        KF_CALL(rc_rule, &F->c1, F->k->kind == K_FST ? RR_FST : RR_SND, 0, 0); KF_CALL(rc_seq, &F->c2, F->cong, F->c1);
        KF_CALL(forward_rc, NULL, F->h.f[F->k->kind == K_FST ? 0 : 1].id, F->k->chi, F->k->dest, F->c2);
        break;
    case K_PAPP:
        if (F->h.tag != T_PLAM) { KF_CALL(publish, NULL, F->k->dest, result_invalid("path application of a non-path introduction")); break; }
        reuse_bump(REUSE_PATH_BETA);
        KF_CALL(apply_dim_binder, &F->x, F->r->ref, 0, 0, F->k->s);
        KF_CALL(rc_rule, &F->c1, RR_PATH_BETA, 0, 0); KF_CALL(rc_seq, &F->c2, F->cong, F->c1);
        KF_CALL(forward_rc, NULL, F->x, F->k->chi, F->k->dest, F->c2);
        break;
    case K_UNGLUE:
        if (F->h.tag != T_GLUE_INTRO) { KF_CALL(publish, NULL, F->k->dest, result_invalid("unglue of a non-glue introduction")); break; }
        reuse_bump(REUSE_GLUE_RULE);
        KF_CALL(rc_rule, &F->c1, RR_GLUE, 0, 3); KF_CALL(rc_seq, &F->c2, F->cong, F->c1);
        KF_CALL(forward_rc, NULL, F->h.f[5].id, F->k->chi, F->k->dest, F->c2);
        break;
    default: die("unreachable continuation kind");
    }
    head_free(&F->h);
    KF_RETV();
    KF_END;
}

/* one elementary frame step, or one local rule of the evaluator's net
 * (counted in the net's rule classes, not as an evaluator step) */
static void execute_task_push(KStack *ks, void *ret, Task t);
/* the engine stacks executing evaluator tasks, each with the producer whose
 * task it runs (a node in the executing frame, linked while it runs): a
 * waiter names the stack advancing the producer it actually awaits. A stack
 * may suspend inside a task: the task stays owned by it (the entry stays
 * RUNNING, the outstanding count is held) and the node stays linked. */
typedef struct ExecNode { KStack *k; uint64_t job; EntryId owner; struct ExecNode *prev, *next; } ExecNode;
static ExecNode *exec_head; static pthread_mutex_t exec_mu = PTHREAD_MUTEX_INITIALIZER;
#define execute_PARAMS(X) X(Task, t)
KF_DECL_DROP(execute, void, execute_PARAMS, execute_drop, ExecNode node; bool linked, outer; EntryId owner; KStack *prev_ks, *k; uint64_t prev_job;)
/* unlink the node and restore the producer's executing stack: the normal
 * return path, and the release a dropped stack performs */
static void exec_unlink(execute_F *F) {
    if (!F->linked) return;
    if (F->owner) { Entry *o = ENT(F->owner); __atomic_store_n(&o->exec_job, F->prev_job, __ATOMIC_RELEASE); __atomic_store_n(&o->exec_ks, F->prev_ks, __ATOMIC_RELEASE); }
    ExecNode *n = &F->node;
    pthread_mutex_lock(&exec_mu); if (n->prev) n->prev->next = n->next; else exec_head = n->next; if (n->next) n->next->prev = n->prev; pthread_mutex_unlock(&exec_mu);
    F->linked = false;
}
static void execute_drop(execute_F *F) { exec_unlink(F); if (F->outer && F->k) F->k->in_eval = false; }
KF_STEP(execute) {
    KF_BEGIN(execute);
    F->k = ks->sync ? NULL : ks;                  /* an engine stack running this task */
    F->outer = F->k && !F->k->in_eval; if (F->outer) F->k->in_eval = true;
    F->owner = F->t.is_pair || F->t.is_notify ? 0 : F->t.op ? task_info(&F->t).producer : F->t.is_resume ? (F->t.k->kind == K_ROOT || F->t.k->kind == K_EXTERNAL ? 0 : F->t.k->dest) : F->t.entry;
    if (F->k) {
        F->node.k = F->k; F->node.job = F->k->job; F->node.owner = F->owner; F->node.prev = NULL;
        pthread_mutex_lock(&exec_mu); F->node.next = exec_head; if (exec_head) exec_head->prev = &F->node; exec_head = &F->node; pthread_mutex_unlock(&exec_mu);
        if (F->owner) { Entry *o = ENT(F->owner); F->prev_ks = __atomic_exchange_n(&o->exec_ks, F->k, __ATOMIC_ACQ_REL); F->prev_job = __atomic_exchange_n(&o->exec_job, F->k->job, __ATOMIC_ACQ_REL); }
        F->linked = true;
    }
    KF_CALL(execute_task, NULL, F->t);
    exec_unlink(F);
    if (F->outer) F->k->in_eval = false;
    KF_RETV();
    KF_END;
}
static void execute_sync(Task t) { KStack *s_ = kf_sync_begin(); execute_push(s_, NULL, t); kf_sync_run(s_); kf_sync_end(s_); }
/* the engine stack that can advance the publication of `want`: one
 * executing a task of `want`, or of a RUNNING producer `want` (transitively)
 * consumes. A retained traversal over the actual consumer occurrences, one
 * entry per step (FC_ADAPTER_STEPS); no unrelated task is ever named. */
#define producer_owner_PARAMS(X) X(EntryId, want) X(uint64_t *, job)
KF_DECL_DROP(producer_owner, KStack *, producer_owner_PARAMS, producer_owner_drop, Words stack, seen; KStack *found; EntryId e; size_t i; bool dup;)
static void producer_owner_drop(producer_owner_F *F) { words_free(&F->stack); words_free(&F->seen); }
KF_STEP(producer_owner) {
    KF_BEGIN(producer_owner);
    if (!F->want) KF_RET(NULL);
    words_init(&F->stack); words_init(&F->seen);
    words_push(&F->stack, F->want);
    F->found = NULL;
    while (F->stack.n && !F->found) {
        F->e = F->stack.w[--F->stack.n];
        F->dup = false; for (F->i = 0; F->i < F->seen.n && !F->dup; F->i++) { fine_bump(FC_ADAPTER_STEPS); F->dup = F->seen.w[F->i] == F->e; KF_SAFE(); }
        if (F->dup) continue;
        words_push(&F->seen, F->e);
        { Entry *x = ENT(F->e);
          KStack *k = __atomic_load_n(&x->exec_ks, __ATOMIC_ACQUIRE);
          if (k) { F->found = k; *F->job = __atomic_load_n(&x->exec_job, __ATOMIC_ACQUIRE); break; } }
        for (F->i = 0;; F->i++) {
            Entry *x = ENT(F->e);
            pthread_mutex_lock(&x->mu);
            bool more = x->state == E_RUNNING && F->i < x->deps.len; EntryId c = more ? x->deps.data[F->i] : 0; bool hist = more && x->dep_hist.data[F->i];
            pthread_mutex_unlock(&x->mu);
            fine_bump(FC_ADAPTER_STEPS);
            if (!more) break;
            if (!hist) {                          /* a superseded request is not awaited work */
                Entry *cx = ENT(c); pthread_mutex_lock(&cx->mu); bool running = cx->state == E_RUNNING; pthread_mutex_unlock(&cx->mu);
                if (running) words_push(&F->stack, c);
            }
            KF_SAFE();
        }
    }
    words_free(&F->stack); words_free(&F->seen);
    KF_RET(F->found);
    KF_END;
}
/* a wait for the machine's progress under q_mu: an engine stack suspends
 * with the stack it needs (named by the caller, computed before taking q_mu)
 * — one transition; a plain computation publishes its ambient label and
 * waits on the condition. The caller re-checks its predicate after it. */
#define EVAL_WAIT(on, job) do { if (!kf_wait_suspends(ks, (on))) ev_quiesce(); KF_WAIT(&E.idle_cv, &E.q_mu, (on), (job)); } while (0)
/* a wait for quiescence names a stack executing a task (every one of which quiescence requires) */
static KStack *exec_other(KStack *self, uint64_t *job) {
    KStack *on = NULL; *job = 0;
    if (self->sync) return NULL;
    pthread_mutex_lock(&exec_mu);
    for (ExecNode *n = exec_head; n && !on; n = n->next) if (n->k != self) { on = n->k; *job = n->job; }
    pthread_mutex_unlock(&exec_mu);
    return on;
}
/* HANDOFF §6: each job is one primitive event (its kind, owner, occurrence); its label is the transitions it takes */
static void execute_task_body_push(KStack *ks, void *ret, Task t);
#define execute_task_PARAMS(X) X(Task, t)
KF_DECL(execute_task, void, execute_task_PARAMS, )
KF_STEP(execute_task) {
    KF_BEGIN(execute_task);
    {
        Task t = F->t;
        EvKind kind = t.is_pair ? EK_NET_PAIR : t.op == OP_EXT ? (t.idx >= 0x4E00 && t.idx < 0x4F00 ? EK_EFFECT_JOB : t.idx == 0x4C00 ? EK_CHAIN_STEP : EK_EVAL_TASK) : EK_EVAL_TASK;
        EntryId oe = t.is_notify ? t.entry : t.op ? (t.op == OP_EXT ? 0 : task_info(&t).producer) : t.is_resume ? (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL ? 0 : t.k->dest) : t.entry;
        uint64_t occ = t.is_pair ? OCC(OCC_NODE, t.pair.node) : oe ? OCC(OCC_ENTRY, oe) : 0;
        ev_begin(kind, occ, 0);   /* a unit left open by a suspension is carried by the suspended stack (kframe.c) */
    }
    KF_CALL(execute_task_body, NULL, F->t);
    ev_end();
    KF_RETV();
    KF_END;
}
#define execute_task_body_PARAMS(X) X(Task, t)
KF_DECL(execute_task_body, void, execute_task_body_PARAMS, ReuseScope *prev;)
KF_STEP(execute_task_body) {
    KF_BEGIN(execute_task_body);
    if (F->t.is_pair) { KF_CALL(net_step_pair, NULL, &E.net, F->t.pair); KF_RETV(); }   /* the net family (net.c) */
    if (F->t.is_notify) { KF_CALL(prefix_notify, NULL, F->t); KF_RETV(); }   /* §84.2 administrative work: not an evaluator frame step */
    if (F->t.op) {                                       /* LIVE-CUT-ADOPTION administrative jobs, charged to the Cut's producer */
        { EntryId ow = task_info(&F->t).producer;
          F->prev = ow ? reuse_scope_enter(ENT(ow)->scope) : reuse_tl_scope; }
        KF_CALL(op_dispatch, NULL, F->t);
        reuse_scope_leave(F->prev);
        KF_RETV();
    }
    XINC(evx, EvalEvents, eval_step);
    { Task t = F->t; EntryId owner = t.is_resume ? t.k->dest : t.entry;    /* §60 trace: the frame step belongs to the producer it advances */
      if (owner && !(t.is_resume && (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL))) { Entry *o = ENT(owner); pthread_mutex_lock(&o->mu); xl_add(&o->steps, &o->steps_carry, 1); pthread_mutex_unlock(&o->mu); } }
    /* V21 R3: the task's events are charged to the scope owning its producer */
    { Task t = F->t; EntryId owner = t.is_resume ? (t.k->kind == K_ROOT || t.k->kind == K_EXTERNAL ? 0 : t.k->dest) : t.entry;
      F->prev = owner ? reuse_scope_enter(ENT(owner)->scope) : reuse_tl_scope; }
    if (F->t.is_resume) {
        if (F->t.k->cut) KF_CALL(cut_deliver, NULL, F->t.k, F->t.r);                     /* a ticket: consumed once, the slot resumes at most once */
        else { KF_CALL(resume, NULL, F->t.k, F->t.r); cont_release(F->t.k); }            /* single consumer: released once resumed */
    }
    else KF_CALL(evaluate, NULL, F->t.entry);
    reuse_scope_leave(F->prev);
    KF_RETV();
    KF_END;
}

/* §43 FORWARD_RESULT(K): the receiver's request; delivery publishes into K */
KF_DECL_EXT(eval_forward_result, void, eval_forward_result_PARAMS, uint64_t rr;)
KF_STEP(eval_forward_result) {
    KF_BEGIN(eval_forward_result);
    KF_CALL(rc_rule, &F->rr, RR_IDENTITY_APPLY, F->v, 0);
    KF_CALL(forward_rc, NULL, F->v, ENT(F->K)->face, F->K, F->rr);
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(eval_forward_result, eval_forward_result_PARAMS, eval_forward_result(EntryId K, RefId v))

static __thread bool tl_eval_worker;
static void *worker_main(void *arg) {
    (void)arg;
    tl_eval_worker = true;
    pthread_mutex_lock(&E.q_mu);
    for (;;) {
        Task t;
        ExtNode *xn = NULL;
        while (!E.stop && !pop_locked(&t) && !(xn = pop_ext_locked(&t))) {   /* take_job; the ambient label is published before waiting */
            ev_quiesce();
            E.idle_workers++; pthread_cond_broadcast(&E.idle_cv);
            pthread_cond_wait(&E.q_cv, &E.q_mu);
            E.idle_workers--;
        }
        if (E.stop) break;
        pthread_mutex_unlock(&E.q_mu);
        free(xn);
        if (hold_take(t)) { finish_any(&t); pthread_mutex_lock(&E.q_mu); continue; }
        execute_sync(t);                 /* all child jobs are enqueued before the job finishes */
        finish_any(&t);
        pthread_mutex_lock(&E.q_mu);
    }
    pthread_mutex_unlock(&E.q_mu);
    ev_quiesce();
    return NULL;
}

/* HANDOFF §7: the whole-machine comparison at quiescence. Workers take and fail a dequeue, publish their
 * ambient label and go idle inside one q_mu section, so holding q_mu while the shadows and the prefix are
 * captured gives a consistent cut of the evaluator's threads. */
size_t eval_shadow_check(bool verbose) {
    pthread_mutex_lock(&E.q_mu);
    size_t r = ev_shadow_check(NULL, verbose);
    pthread_mutex_unlock(&E.q_mu);
    return r;
}
KF_DECL_EXT(eval_run, size_t, KF_NOPARAMS, size_t n, before; Task t; KStack *on; uint64_t job;)
KF_STEP(eval_run) {
    KF_BEGIN(eval_run);
    if (E.nworkers) {
        /* wait until outstanding == 0 (no queued, reserved or executing job) */
        pthread_mutex_lock(&E.q_mu);
        F->before = eval_events().eval_step;
        /* quiescence: no queued, reserved or executing job, and every worker idle with its stream published
         * (a run nested in a worker's job or in an engine computation does not wait for its own thread) */
        while (E.outstanding > 0 || (!kf_tl && E.ext_n > 0) || (!kf_tl && !tl_eval_worker && E.idle_workers < E.nworkers)) { F->on = exec_other(ks, &F->job); EVAL_WAIT(F->on, F->job); }
        F->n = eval_events().eval_step - F->before;
        pthread_mutex_unlock(&E.q_mu);
        KF_RET(F->n);
    }
    F->n = 0;
    for (;;) {
        {
            pthread_mutex_lock(&E.q_mu);
            ExtNode *xn = NULL;
            bool got = pop_locked(&F->t) || (xn = pop_ext_locked(&F->t)) != NULL;
            pthread_mutex_unlock(&E.q_mu);
            free(xn);
            if (!got) break;
        }
        if (hold_take(F->t)) { finish_any(&F->t); continue; }
        KF_CALL(execute, NULL, F->t);
        finish_any(&F->t);
        F->n++;
    }
    KF_RET(F->n);
    KF_END;
}
size_t eval_run(void) { size_t r; KStack *s_ = kf_sync_begin(); eval_run_push(s_, &r); kf_sync_run(s_); kf_sync_end(s_); return r; }
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
        execute_sync(t);
        finish_any(&t);
        n++;
    }
    return n;
}

KF_DECL_EXT_DROP(whnf, EvalResult *, whnf_PARAMS, whnf_drop, RootBox *box; Cont *root; EntryId root_entry; KStack *on; uint64_t job; bool d, done; size_t ran; EvalResult *out;)
/* a dropped observation releases its reference to the root box; the root continuation keeps the other */
static void whnf_drop(whnf_F *F) { if (F->box) { rootbox_release(F->box); F->box = NULL; } }
KF_STEP(whnf) {
    KF_BEGIN(whnf);
    F->box = calloc(1, sizeof *F->box); require(F->box, "out of memory");
    pthread_mutex_init(&F->box->mu, NULL); pthread_cond_init(&F->box->cv, NULL); F->box->refs = 2;
    F->root = cont_new(K_ROOT, 0, F->chi);
    F->root->root = F->box;
    KF_CALL(eval_request, NULL, F->t, F->chi, F->root);
    KF_CALL(eval_entry_lookup, &F->root_entry, F->t, F->chi);   /* the producer this root awaits (the root continuation itself may already be resumed and released) */
    if (E.nworkers) {
        /* wait for this root, or for quiescence of the whole machine (stuck) */
        for (;;) {
            F->job = 0; F->on = NULL;
            if (!ks->sync) KF_CALL(producer_owner, &F->on, F->root_entry, &F->job);   /* outside q_mu: entry locks precede it */
            pthread_mutex_lock(&E.q_mu);
            pthread_mutex_lock(&F->box->mu); F->d = F->box->done; pthread_mutex_unlock(&F->box->mu);
            if (F->d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
            EVAL_WAIT(F->on, F->job);
            pthread_mutex_unlock(&E.q_mu);
        }
    } else {
        /* no pool: this computation runs the queue; while another client is
         * still executing a job (its publication may resume this root, or
         * enqueue more work), wait for the root or for quiescence rather
         * than reporting a stuck demand */
        for (;;) {
            KF_CALL0(eval_run, &F->ran);
            F->job = 0; F->on = NULL;
            if (!ks->sync) KF_CALL(producer_owner, &F->on, F->root_entry, &F->job);
            pthread_mutex_lock(&E.q_mu);
            pthread_mutex_lock(&F->box->mu); F->d = F->box->done; pthread_mutex_unlock(&F->box->mu);
            { bool queued = E.qhead < E.qtail || net_pending_pairs_locked(&E.net) > 0 || (!kf_tl && E.ext_head);
              if (F->d || E.outstanding == 0) { pthread_mutex_unlock(&E.q_mu); break; }
              if (!queued) EVAL_WAIT(F->on, F->job); }
            pthread_mutex_unlock(&E.q_mu);
        }
    }
    pthread_mutex_lock(&F->box->mu);
    F->done = F->box->done; F->out = F->box->result;
    pthread_mutex_unlock(&F->box->mu);
    /* a stuck root keeps its continuation as a waiter; the box survives
     * until that continuation is resumed or the machine is freed */
    rootbox_release(F->box); F->box = NULL;
    if (!F->done) { if (F->status) *F->status = W_STUCK; KF_RET(NULL); }
    if (F->status) {
        if (F->out->cls == R_NO_OBSERVATION) *F->status = W_NO_OBSERVATION;
        else if (F->out->cls == R_INVALID) *F->status = W_INVALID;
        else *F->status = W_OK;
    }
    KF_RET(F->out);
    KF_END;
}
KF_SYNC_DEF(whnf, EvalResult *, whnf_PARAMS, whnf(RefId t, FaceId chi, WhnfStatus *status))

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

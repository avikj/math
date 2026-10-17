/* effect.c — see effect.h and EFFECT-AUTHORITY.md §§2–4, 8–10. */
#include "effect.h"
#include "work.h"
#include "fine.h"
#include "lib.h"
#include <string.h>
#include <sched.h>

struct EffSchema { const char *name; ContextId G; FaceId kappa; RefId In, Out, R; int port_role; EffSchema *all_next; };
/* a head cell: AVAILABLE(head) when res == NULL, else RESERVED(res, slot) —
 * interpreted by the descriptor's state (RESERVING: unavailable, the former
 * head; COMMITTED: its successor; ABORTED: the former head) */
typedef struct EffCell { uint64_t id; pthread_mutex_t mu; const EffHead *head; EffCommit *res; size_t slot; } EffCell;
struct EffHead { uint64_t id; EffAuthority *auth; EffPort *port; RefId state; const EffOcc *producer; const EffHead *pred; bool consumed; EffHead *all_next; };
struct EffAuthority { uint64_t id; const EffHead *genesis; const char *name; ContextId G; FaceId kappa; RefId type; EffCell cell; EffPort **outbox; size_t nout, capout; EffAuthority *all_next; };
struct EffPort { uint64_t id; const EffOcc *issuer; size_t slot; RefId payload; EffAuthority *recipient, *refund_to; const EffHead *token; EffCell cell; bool emitted; EffPort *all_next, *pub_next; };
struct EffCap { uint64_t id; EffAuthority *auth; EffCap *all_next; };
typedef struct { XCount prepare_steps, audit_units, reservations, waits, commit, finalizes, deliveries, emits; } OccWork;
struct EffOcc {
    uint64_t id; EffSchema *schema; EffCommit *d;
    RefId s, t, witness, edge;          /* the admitted judgment p : R s t */
    uint64_t *assume; size_t nassume; uint64_t env;
    EffPort **ports; size_t nports;
    OccWork work;
    EffOcc *all_next;
};
typedef struct { int kind; EffAuthority *auth; EffPort *port; const EffHead *expected; } EffIn;   /* kind 0 head, 1 port */
typedef struct { EffAuthority *auth; RefId state; } EffOutH;
typedef struct { RefId payload; EffAuthority *recipient, *refund_to; } EffOutP;
struct EffProposal {
    EffSchema *schema; uint64_t ns, request;
    EffIn *in; size_t nin, capin; EffOutH *oh; size_t noh, capoh; EffOutP *op; size_t nop, capop;
    RefId witness; EffCap **caps; size_t ncaps, capcaps;
};
/* a client's delivery obligation: owned by the registry until teardown; the job that performs it marks it done */
typedef struct Delivery { EffDeliver k; void *ctx; EffOutcome o; EffOcc *occ; struct Delivery *next, *all_next; bool done; } Delivery;
typedef struct { EffCommit *d; size_t k; bool emit; } FinArg;
enum { D_PREPARING = 0, D_RESERVING, D_COMMITTED, D_ABORTED, D_INVALID };
struct EffCommit {
    EffProposal *P; int state; bool unresolved; const char *why; const EffOcc *holder;
    pthread_mutex_t mu; Delivery *waiters; EffCommit **joined; size_t njoined, capjoined;
    int phase; size_t k;                 /* preparation phase and cursor; reservation cursor */
    OpId audit; RefId s, t, edge;
    XCount wprep, waudit;                /* preparation work before the occurrence record exists (moved into it at phase 6) */
    uint64_t *assume; size_t nassume;
    size_t *order;                       /* inputs sorted by cell identity */
    EffCell **cells; const EffHead **expected; EffHead **succ;   /* per sorted input */
    FinArg *fin, *emit;                  /* the finalization / emission job arguments (owned, preallocated) */
    EffOcc *occ;
    EffCommit *all_next, *unres_next; bool in_unres;
};

static struct {
    pthread_mutex_t mu;                  /* registries, request index, history: constant sections */
    pthread_mutex_t commit_mu;           /* serializes the commit transition with the cut sequence */
    uint64_t ids, cut_seq;               /* cut_seq: odd while a commit transition is in progress */
    EffSchema *schemas; EffAuthority *auths; EffHead *heads; EffPort *ports, *published; EffCap *caps; EffOcc *occs; EffCommit *commits, *unres;
    Delivery *deliveries;
    WordMap index;                       /* (ns, request) -> descriptor */
    ChainMapT *resmap; WordMap stepocc;  /* the resource reading: B, and step cell -> occurrence */
    const EffOcc **hist; size_t nhist, caphist;
    XCount ev[sizeof(EffEvents) / sizeof(size_t)];
    bool live;
} X;
#define EV(f) xc_inc(&X.ev[offsetof(EffEvents, f) / sizeof(size_t)])
static uint64_t fresh_id(void) { return __atomic_add_fetch(&X.ids, 1, __ATOMIC_RELAXED); }
#define GROW(arr, n, cap) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 4; (arr) = realloc((arr), (cap) * sizeof *(arr)); require((arr), "out of memory"); } } while (0)

void effect_init(void) { memset(&X, 0, sizeof X); pthread_mutex_init(&X.mu, NULL); pthread_mutex_init(&X.commit_mu, NULL); wordmap_init(&X.index); wordmap_init(&X.stepocc); X.live = true; }
static void proposal_free(EffProposal *P) { free(P->in); free(P->oh); free(P->op); free(P->caps); free(P); }
void effect_free(void) {
    if (!X.live) return;
    for (EffCommit *d = X.commits, *n; d; d = n) {
        n = d->all_next;
        proposal_free(d->P);
        free(d->joined); free(d->order); free(d->cells); free(d->expected); free(d->succ); free(d->assume); free(d->fin); free(d->emit);
        if (d->audit) op_release(d->audit);
        pthread_mutex_destroy(&d->mu); free(d);
    }
    for (Delivery *v = X.deliveries, *n; v; v = n) { n = v->all_next; free(v); }
    for (EffOcc *e = X.occs, *n; e; e = n) { n = e->all_next; free(e->ports); free(e->assume); free(e); }
    for (EffPort *m = X.ports, *n; m; m = n) { n = m->all_next; pthread_mutex_destroy(&m->cell.mu); free(m); }
    for (EffAuthority *a = X.auths, *n; a; a = n) { n = a->all_next; free(a->outbox); pthread_mutex_destroy(&a->cell.mu); free(a); }
    for (EffHead *h = X.heads, *n; h; h = n) { n = h->all_next; free(h); }
    for (EffCap *c = X.caps, *n; c; c = n) { n = c->all_next; free(c); }
    for (EffSchema *s = X.schemas, *n; s; s = n) { n = s->all_next; free(s); }
    free(X.hist); wordmap_free(&X.index); wordmap_free(&X.stepocc); pthread_mutex_destroy(&X.mu); pthread_mutex_destroy(&X.commit_mu);
    memset(&X, 0, sizeof X);
}
EffEvents eff_events(void) { EffEvents v; size_t *d = (size_t *)&v; for (size_t i = 0; i < sizeof v / sizeof(size_t); i++) d[i] = (size_t)xs_u64_checked(xc_snap(&X.ev[i]), "effect event"); return v; }

/* ---------------- records ---------------- */
EffSchema *eff_schema(const char *name, ContextId G, FaceId kappa, RefId In, RefId Out, RefId R, int port_role) {
    EffSchema *s = calloc(1, sizeof *s); require(s, "out of memory");
    s->name = name; s->G = G; s->kappa = kappa; s->In = In; s->Out = Out; s->R = R; s->port_role = port_role;
    pthread_mutex_lock(&X.mu); s->all_next = X.schemas; X.schemas = s; pthread_mutex_unlock(&X.mu);
    return s;
}
static EffHead *head_new(EffAuthority *a, EffPort *m, RefId state, const EffOcc *producer, const EffHead *pred, bool consumed) {
    EffHead *h = calloc(1, sizeof *h); require(h, "out of memory");
    h->id = fresh_id(); h->auth = a; h->port = m; h->state = state; h->producer = producer; h->pred = pred; h->consumed = consumed;
    pthread_mutex_lock(&X.mu); h->all_next = X.heads; X.heads = h; pthread_mutex_unlock(&X.mu);
    return h;
}
static void cell_init(EffCell *c, const EffHead *h) { c->id = fresh_id(); pthread_mutex_init(&c->mu, NULL); c->head = h; c->res = NULL; c->slot = 0; }
EffAuthority *eff_genesis(const char *name, ContextId G, FaceId kappa, RefId state, RefId type, EffCap **owner) {
    EffAuthority *a = calloc(1, sizeof *a); require(a, "out of memory");
    a->id = fresh_id(); a->name = name; a->G = G; a->kappa = kappa; a->type = type;
    a->genesis = head_new(a, NULL, state, NULL, NULL, false); cell_init(&a->cell, a->genesis);
    EffCap *c = calloc(1, sizeof *c); require(c, "out of memory"); c->id = fresh_id(); c->auth = a;
    pthread_mutex_lock(&X.mu); a->all_next = X.auths; X.auths = a; c->all_next = X.caps; X.caps = c; pthread_mutex_unlock(&X.mu);
    if (owner) *owner = c;
    return a;
}
const char *eff_authority_name(const EffAuthority *a) { return a->name; }
/* a capability is valid when it was issued by its authority's boundary (registry membership) */
static bool cap_valid(const EffCap *c, const EffAuthority *a) {
    bool ok = false; pthread_mutex_lock(&X.mu);
    for (EffCap *x = X.caps; x && !ok; x = x->all_next) ok = x == c && x->auth == a;
    pthread_mutex_unlock(&X.mu); return ok;
}

EffProposal *eff_proposal(EffSchema *s, uint64_t ns, uint64_t request) { EffProposal *P = calloc(1, sizeof *P); require(P, "out of memory"); P->schema = s; P->ns = ns; P->request = request; return P; }
void eff_in_head(EffProposal *P, EffAuthority *a, const EffHead *expected) { GROW(P->in, P->nin, P->capin); P->in[P->nin++] = (EffIn){ 0, a, NULL, expected }; }
void eff_in_port(EffProposal *P, EffPort *m) { GROW(P->in, P->nin, P->capin); P->in[P->nin++] = (EffIn){ 1, NULL, m, m ? m->token : NULL }; }
void eff_out_head(EffProposal *P, EffAuthority *a, RefId state) { GROW(P->oh, P->noh, P->capoh); P->oh[P->noh++] = (EffOutH){ a, state }; }
void eff_out_port(EffProposal *P, RefId payload, EffAuthority *recipient, EffAuthority *refund_to) { GROW(P->op, P->nop, P->capop); P->op[P->nop++] = (EffOutP){ payload, recipient, refund_to }; }
void eff_witness(EffProposal *P, RefId p) { P->witness = p; }
void eff_cap(EffProposal *P, EffCap *c) { GROW(P->caps, P->ncaps, P->capcaps); P->caps[P->ncaps++] = c; }
void eff_proposal_free(EffProposal *P) { if (P) proposal_free(P); }
EffProposal *eff_proposal_reindex(const EffProposal *P, MapId sigma, uint64_t request) {
    EffProposal *Q = eff_proposal(P->schema, P->ns, request);
    for (size_t i = 0; i < P->nin; i++) { GROW(Q->in, Q->nin, Q->capin); Q->in[Q->nin++] = P->in[i]; }
    for (size_t i = 0; i < P->noh; i++) eff_out_head(Q, P->oh[i].auth, reindex(P->oh[i].state, sigma));
    for (size_t i = 0; i < P->nop; i++) eff_out_port(Q, reindex(P->op[i].payload, sigma), P->op[i].recipient, P->op[i].refund_to);
    Q->witness = P->witness ? reindex(P->witness, sigma) : 0;
    for (size_t i = 0; i < P->ncaps; i++) eff_cap(Q, P->caps[i]);
    return Q;
}
/* the anchored proposal data, including its explicit authorization premises */
static bool same_anchor(const EffProposal *a, const EffProposal *b) {
    if (a->schema != b->schema || a->nin != b->nin || a->noh != b->noh || a->nop != b->nop || a->witness != b->witness || a->ncaps != b->ncaps) return false;
    for (size_t i = 0; i < a->nin; i++) if (a->in[i].kind != b->in[i].kind || a->in[i].auth != b->in[i].auth || a->in[i].port != b->in[i].port || a->in[i].expected != b->in[i].expected) return false;
    for (size_t i = 0; i < a->noh; i++) if (a->oh[i].auth != b->oh[i].auth || a->oh[i].state != b->oh[i].state) return false;
    for (size_t i = 0; i < a->nop; i++) if (a->op[i].payload != b->op[i].payload || a->op[i].recipient != b->op[i].recipient || a->op[i].refund_to != b->op[i].refund_to) return false;
    for (size_t i = 0; i < a->ncaps; i++) if (a->caps[i] != b->caps[i]) return false;
    return true;
}

/* ---------------- jobs ---------------- */
static void prepare_job(void *p);
static void reserve_job(void *p);
static void commit_job(void *p);
static void finalize_job(void *p);
static void deliver_job(void *p) {
    Delivery *v = p;
    if (v->occ) xc_inc(&v->occ->work.deliveries); else EV(deliveries_unattributed);
    EV(deliveries); v->done = true; v->k(v->ctx, v->o);
}
static Delivery *delivery_new(EffDeliver k, void *ctx) {
    Delivery *v = calloc(1, sizeof *v); require(v, "out of memory"); v->k = k; v->ctx = ctx;
    pthread_mutex_lock(&X.mu); v->all_next = X.deliveries; X.deliveries = v; pthread_mutex_unlock(&X.mu);
    return v;
}
static EffOutcome outcome_of(EffCommit *d) {
    int st = __atomic_load_n(&d->state, __ATOMIC_ACQUIRE);        /* the state first: why / holder / occurrence are written before its release */
    EffOutcome o = { EO_PENDING, NULL, NULL, NULL };
    if (st == D_COMMITTED) { o.kind = EO_ACCEPTED; o.receipt = d->occ; }
    else if (st == D_ABORTED) { o.kind = EO_CONFLICT; o.holder = d->holder; o.why = d->why; }
    else if (st == D_INVALID) { o.kind = EO_INVALID; o.why = d->why; }
    return o;
}
static void deliver(Delivery *v, EffOutcome o, EffOcc *occ) { v->o = o; v->occ = occ; eval_job(deliver_job, v, EFF_TAG_DELIVER); }
/* a terminal transition: deliver to the attached clients (one job each) and wake the descriptors joined on this one */
static void settle(EffCommit *d) {
    pthread_mutex_lock(&d->mu);
    Delivery *w = d->waiters; d->waiters = NULL;
    EffCommit **j = d->joined; size_t nj = d->njoined; d->joined = NULL; d->njoined = d->capjoined = 0;
    pthread_mutex_unlock(&d->mu);
    EffOutcome o = outcome_of(d);
    while (w) { Delivery *n = w->next; deliver(w, o, o.kind == EO_ACCEPTED ? d->occ : NULL); w = n; }
    for (size_t i = 0; i < nj; i++) eval_job(reserve_job, j[i], EFF_TAG_RESERVE);   /* recheck that cell */
    free(j);
}

EffCommit *eff_request(EffProposal *P, EffDeliver k, void *ctx) {
    EV(requests);
    uint64_t key[2] = { P->ns, P->request }, have = 0;
    Delivery *v = k ? delivery_new(k, ctx) : NULL;
    pthread_mutex_lock(&X.mu);
    if (wordmap_get(&X.index, key, 2, &have)) {
        EffCommit *d = (EffCommit *)(uintptr_t)have;
        pthread_mutex_unlock(&X.mu);
        if (!same_anchor(d->P, P)) { EV(request_conflicts); EffOutcome o = { EO_REQUEST_CONFLICT, NULL, NULL, "request identity reused with different anchored proposal data" }; proposal_free(P); if (v) deliver(v, o, NULL); return d; }
        proposal_free(P); EV(joins);
        if (!v) return d;
        pthread_mutex_lock(&d->mu);
        int st = __atomic_load_n(&d->state, __ATOMIC_ACQUIRE);
        bool terminal = st == D_COMMITTED || st == D_ABORTED || st == D_INVALID;
        if (!terminal) { v->next = d->waiters; d->waiters = v; }
        pthread_mutex_unlock(&d->mu);
        if (terminal) deliver(v, outcome_of(d), st == D_COMMITTED ? d->occ : NULL);   /* the same receipt; no second occurrence */
        return d;
    }
    EffCommit *d = calloc(1, sizeof *d); require(d, "out of memory");
    d->P = P; pthread_mutex_init(&d->mu, NULL); d->state = D_PREPARING; d->waiters = v;
    wordmap_put(&X.index, key, 2, (uint64_t)(uintptr_t)d);
    d->all_next = X.commits; X.commits = d;
    pthread_mutex_unlock(&X.mu);
    EV(prepares);
    eval_job(prepare_job, d, EFF_TAG_PREPARE);
    return d;
}
EffOutcomeKind eff_commit_state(const EffCommit *d) { return outcome_of((EffCommit *)d).kind; }
bool eff_commit_unresolved(const EffCommit *d) { return __atomic_load_n(&d->unresolved, __ATOMIC_ACQUIRE); }
/* the descriptors whose required proof was pending keep their clients; a new attempt re-runs their audits */
size_t eff_retry(void) {
    pthread_mutex_lock(&X.mu); EffCommit *u = X.unres; X.unres = NULL;
    size_t n = 0; for (EffCommit *d = u; d; d = d->unres_next) { d->in_unres = false; n++; }
    pthread_mutex_unlock(&X.mu);
    while (u) { EffCommit *nx = u->unres_next; __atomic_store_n(&u->unresolved, false, __ATOMIC_RELEASE); u->phase = 3; eval_job(prepare_job, u, EFF_TAG_AUDIT); u = nx; }
    return n;
}

static void invalid(EffCommit *d, const char *why) { d->why = why; EV(invalid); __atomic_store_n(&d->state, D_INVALID, __ATOMIC_RELEASE); settle(d); }
static RefId tuple(const RefId *xs, size_t n) { if (!n) return 0; RefId t = xs[n - 1]; for (size_t i = n - 1; i-- > 0; ) t = mk_pair(xs[i], t); return t; }
static bool occ_accepted(const EffOcc *e) { return __atomic_load_n(&e->d->state, __ATOMIC_ACQUIRE) == D_COMMITTED; }

/* PREPARE_EFFECT: one phase step per job
 *   0  interface, one input per step: unique cells, a port issued by an accepted occurrence, the port role,
 *      authorization (a valid issued capability of the required authority)
 *   1  outputs, exactly: one successor head per consumed head's authority and no other output head; a
 *      consumed port's authority receives a successor head; output ports name their recipient
 *   2  the judgment: s = tuple of input states, t = tuple of output states and port payloads, R s t
 *   3,4,5  the audits of s : In, t : Out, p : R s t — one engine unit per job
 *   6  pin the environment snapshot; prepare the occurrence, its (unpublished) ports, successor heads,
 *      consumed-port markers, the reservation order and the job arguments */
static int audit_step(EffCommit *d, RefId e, RefId E) {
    EffSchema *s = d->P->schema;
    if (!d->audit) { d->audit = op_proof_audit(s->G, s->kappa, e, E); EV(audits); }
    EV(audit_units); xc_inc(&d->waudit);
    if (op_status(d->audit) == OP_RUNNING) op_step(d->audit, 1);
    size_t na = 0; const uint64_t *as = NULL;
    int v = op_audit_verdict(d->audit, &na, &as);
    if (v < 0) return -1;
    if (v == PU_ASSUMED && na) { uint64_t *m = realloc(d->assume, (d->nassume + na) * sizeof *m); require(m, "out of memory"); memcpy(m + d->nassume, as, na * sizeof *m); d->assume = m; d->nassume += na; }
    op_release(d->audit); d->audit = 0;
    return v;
}
static void prepare_job(void *p) {
    EffCommit *d = p; EffProposal *P = d->P; EffSchema *S = P->schema;
    EV(prepare_steps); xc_inc(&d->wprep);
    switch (d->phase) {
    case 0: {
        if (d->k >= P->nin) { d->phase = 1; d->k = 0; break; }
        EffIn *in = &P->in[d->k];
        if (in->kind && (!in->port || !occ_accepted(in->port->issuer))) { invalid(d, "the input port was not issued by an accepted occurrence"); return; }
        if (!in->kind && !in->auth) { invalid(d, "an input head names no authority"); return; }
        EffCell *c = in->kind ? &in->port->cell : &in->auth->cell;
        for (size_t j = 0; j < d->k; j++) { EffCell *cj = P->in[j].kind ? &P->in[j].port->cell : &P->in[j].auth->cell; if (cj == c) { invalid(d, "an input occurrence appears twice"); return; } }
        EffAuthority *need = in->kind ? (S->port_role == EFF_PORT_REFUND ? in->port->refund_to : in->port->recipient) : in->auth;
        if (!need) { invalid(d, "the port names no authority for this consumption"); return; }
        bool ok = false; for (size_t j = 0; j < P->ncaps && !ok; j++) ok = cap_valid(P->caps[j], need);
        if (!ok) { invalid(d, "no valid capability issued by the required authority"); return; }
        d->k++; break;
    }
    case 1: {
        size_t heads = 0;
        for (size_t i = 0; i < P->nin; i++) if (!P->in[i].kind) {
            size_t succ = 0; for (size_t j = 0; j < P->noh; j++) succ += P->oh[j].auth == P->in[i].auth;
            if (succ != 1) { invalid(d, succ ? "two successor heads for one consumed head" : "a consumed head has no successor head for its authority"); return; }
            heads++;
        }
        if (heads != P->noh) { invalid(d, "an output head for an authority whose head is not consumed"); return; }
        for (size_t j = 0; j < P->nop; j++) if (!P->op[j].recipient) { invalid(d, "an output port names no recipient"); return; }
        for (size_t i = 0; i < P->nin; i++) if (P->in[i].kind) {
            EffAuthority *to = S->port_role == EFF_PORT_REFUND ? P->in[i].port->refund_to : P->in[i].port->recipient;
            bool has = false; for (size_t j = 0; j < P->noh && !has; j++) has = P->oh[j].auth == to;
            if (!has) { invalid(d, "a consumed port's authority receives no successor head"); return; }
        }
        if (!P->witness) { invalid(d, "no edge witness"); return; }
        d->phase = 2; break;
    }
    case 2: {
        RefId *xs = malloc((P->nin + 1) * sizeof *xs), *ys = malloc((P->noh + P->nop + 1) * sizeof *ys); require(xs && ys, "out of memory");
        for (size_t i = 0; i < P->nin; i++) xs[i] = P->in[i].kind ? P->in[i].port->payload : P->in[i].expected->state;
        for (size_t i = 0; i < P->noh; i++) ys[i] = P->oh[i].state;
        for (size_t i = 0; i < P->nop; i++) ys[P->noh + i] = P->op[i].payload;
        d->s = tuple(xs, P->nin); d->t = tuple(ys, P->noh + P->nop); free(xs); free(ys);
        d->edge = mk_app(mk_app(S->R, d->s), d->t);
        d->phase = 3; break;
    }
    case 3: case 4: case 5: {
        RefId e = d->phase == 3 ? d->s : d->phase == 4 ? d->t : P->witness, E = d->phase == 3 ? S->In : d->phase == 4 ? S->Out : d->edge;
        int v = audit_step(d, e, E);
        if (v < 0) { eval_job(prepare_job, d, EFF_TAG_AUDIT); return; }          /* the audit continues next unit */
        if (v == PU_INVALID) { invalid(d, d->phase == 5 ? "the edge witness is not admitted at R(s,t)" : "a state is not admitted at its interface type"); return; }
        if (v == PU_PENDING || v == PU_UNRESOLVED) {                            /* stays pending, its clients attached; eff_retry re-runs the audits */
            d->why = "a required proof is pending";
            pthread_mutex_lock(&X.mu); if (!d->in_unres) { d->in_unres = true; d->unres_next = X.unres; X.unres = d; } pthread_mutex_unlock(&X.mu);
            __atomic_store_n(&d->unresolved, true, __ATOMIC_RELEASE); EV(unresolved);
            return;
        }
        d->phase++; break;
    }
    case 6: {
        size_t n = P->nin;
        d->order = malloc((n ? n : 1) * sizeof *d->order); d->cells = malloc((n ? n : 1) * sizeof *d->cells);
        d->expected = malloc((n ? n : 1) * sizeof *d->expected); d->succ = malloc((n ? n : 1) * sizeof *d->succ);
        d->fin = calloc(n ? n : 1, sizeof *d->fin); d->emit = calloc(P->nop ? P->nop : 1, sizeof *d->emit);
        require(d->order && d->cells && d->expected && d->succ && d->fin && d->emit, "out of memory");
        EffOcc *e = calloc(1, sizeof *e); require(e, "out of memory");
        e->id = fresh_id(); e->schema = S; e->d = d; e->s = d->s; e->t = d->t; e->witness = P->witness; e->edge = d->edge;
        e->assume = d->assume; e->nassume = d->nassume; d->assume = NULL; d->nassume = 0; e->env = global_env_version();
        e->nports = P->nop; e->ports = calloc(P->nop ? P->nop : 1, sizeof *e->ports); require(e->ports, "out of memory");
        for (size_t i = 0; i < P->nop; i++) {
            EffPort *m = calloc(1, sizeof *m); require(m, "out of memory");
            m->id = fresh_id(); m->issuer = e; m->slot = i; m->payload = P->op[i].payload; m->recipient = P->op[i].recipient; m->refund_to = P->op[i].refund_to;
            m->token = head_new(NULL, m, m->payload, e, NULL, false); cell_init(&m->cell, m->token);   /* reachable only after acceptance */
            e->ports[i] = m;
            d->emit[i] = (FinArg){ d, i, true };
        }
        for (size_t i = 0; i < n; i++) d->order[i] = i;
        for (size_t i = 1; i < n; i++) for (size_t j = i; j > 0; j--) {               /* the fixed total order of cell identities */
            EffCell *a = P->in[d->order[j - 1]].kind ? &P->in[d->order[j - 1]].port->cell : &P->in[d->order[j - 1]].auth->cell;
            EffCell *b = P->in[d->order[j]].kind ? &P->in[d->order[j]].port->cell : &P->in[d->order[j]].auth->cell;
            if (a->id < b->id) break;
            size_t t = d->order[j - 1]; d->order[j - 1] = d->order[j]; d->order[j] = t;
        }
        for (size_t r = 0; r < n; r++) {
            EffIn *in = &P->in[d->order[r]];
            d->cells[r] = in->kind ? &in->port->cell : &in->auth->cell;
            d->expected[r] = in->expected;
            if (in->kind) d->succ[r] = head_new(NULL, in->port, in->port->payload, e, in->expected, true);   /* the consumed marker */
            else { RefId st = 0; for (size_t j = 0; j < P->noh; j++) if (P->oh[j].auth == in->auth) st = P->oh[j].state; d->succ[r] = head_new(in->auth, NULL, st, e, in->expected, false); }
            d->fin[r] = (FinArg){ d, r, false };
        }
        pthread_mutex_lock(&X.mu); e->all_next = X.occs; X.occs = e; for (size_t i = 0; i < P->nop; i++) { e->ports[i]->all_next = X.ports; X.ports = e->ports[i]; } pthread_mutex_unlock(&X.mu);
        xc_add_snap(&e->work.prepare_steps, xc_take(&d->wprep)); xc_add_snap(&e->work.audit_units, xc_take(&d->waudit));
        d->occ = e; d->k = 0;
        __atomic_store_n(&d->state, D_RESERVING, __ATOMIC_RELEASE);
        eval_job(n ? reserve_job : commit_job, d, n ? EFF_TAG_RESERVE : EFF_TAG_COMMIT);
        return;
    }
    }
    eval_job(prepare_job, d, d->phase >= 3 && d->phase <= 5 ? EFF_TAG_AUDIT : EFF_TAG_PREPARE);
}

static void abort_commit(EffCommit *d, const EffOcc *holder, const char *why) {
    d->holder = holder; d->why = why;           /* only this descriptor's own job leaves RESERVING: written before the release */
    int exp = D_RESERVING;
    if (!__atomic_compare_exchange_n(&d->state, &exp, D_ABORTED, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return;
    EV(aborts);
    for (size_t r = 0; r < d->k; r++) eval_job(finalize_job, &d->fin[r], EFF_TAG_FINALIZE);   /* rollback of the cells it reserved */
    settle(d);
}
/* RESERVE_NEXT(D, k): one input cell per job, under its lock only */
static void reserve_job(void *p) {
    EffCommit *d = p;
    if (__atomic_load_n(&d->state, __ATOMIC_ACQUIRE) != D_RESERVING) return;
    size_t r = d->k; EffCell *c = d->cells[r];
    EV(reservations); xc_inc(&d->occ->work.reservations);
    pthread_mutex_lock(&c->mu);
    if (!c->res) {
        if (c->head == d->expected[r]) {
            c->res = d; c->slot = r;
            pthread_mutex_unlock(&c->mu);
            d->k++;
            eval_job(d->k == d->P->nin ? commit_job : reserve_job, d, d->k == d->P->nin ? EFF_TAG_COMMIT : EFF_TAG_RESERVE);
            return;
        }
        const EffOcc *holder = c->head->producer;
        pthread_mutex_unlock(&c->mu);
        abort_commit(d, holder, "an expected input head is no longer current");   /* an operational conflict, not a mathematical inequality */
        return;
    }
    EffCommit *o = c->res; size_t os = c->slot;
    int st = __atomic_load_n(&o->state, __ATOMIC_ACQUIRE);
    if (st == D_RESERVING) {
        pthread_mutex_unlock(&c->mu);
        pthread_mutex_lock(&o->mu);
        bool still = __atomic_load_n(&o->state, __ATOMIC_ACQUIRE) == D_RESERVING;
        if (still) { GROW(o->joined, o->njoined, o->capjoined); o->joined[o->njoined++] = d; }   /* a predicate wait on that descriptor's progress */
        pthread_mutex_unlock(&o->mu);
        EV(waits); xc_inc(&d->occ->work.waits);
        if (!still) eval_job(reserve_job, d, EFF_TAG_RESERVE);
        return;
    }
    /* a terminal reservation: one finalization step (help), then retry this input */
    c->head = st == D_COMMITTED ? o->succ[os] : o->expected[os]; c->res = NULL;
    pthread_mutex_unlock(&c->mu);
    EV(helps);
    eval_job(reserve_job, d, EFF_TAG_RESERVE);
}
/* the one acceptance event: the state transition, inside the cut sequence (readers retry across it) */
static void commit_job(void *p) {
    EffCommit *d = p;
    EffOcc *e = d->occ;
    pthread_mutex_lock(&X.commit_mu);
    __atomic_add_fetch(&X.cut_seq, 1, __ATOMIC_ACQ_REL);
    int exp = D_RESERVING;
    bool won = __atomic_compare_exchange_n(&d->state, &exp, D_COMMITTED, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
    if (won) {   /* the accepted ports become reachable in the same section */
        pthread_mutex_lock(&X.mu);
        GROW(X.hist, X.nhist, X.caphist); X.hist[X.nhist++] = e;
        for (size_t i = 0; i < e->nports; i++) { e->ports[i]->pub_next = X.published; X.published = e->ports[i]; }
        pthread_mutex_unlock(&X.mu);
    }
    __atomic_add_fetch(&X.cut_seq, 1, __ATOMIC_ACQ_REL);
    pthread_mutex_unlock(&X.commit_mu);
    if (!won) return;
    EV(commits); xc_inc(&e->work.commit);
    for (size_t r = 0; r < d->P->nin; r++) eval_job(finalize_job, &d->fin[r], EFF_TAG_FINALIZE);
    for (size_t i = 0; i < e->nports; i++) eval_job(finalize_job, &d->emit[i], EFF_TAG_EMIT);
    settle(d);
}
/* FINALIZE(D, k): materialize the reservation (successor if committed, former head if aborted); EMIT(E, slot) */
static void finalize_job(void *p) {
    FinArg *a = p; EffCommit *d = a->d; size_t r = a->k;
    if (a->emit) {   /* EMIT: the committed port's description to its endpoint's outbox */
        EffPort *m = d->occ->ports[r];
        EffAuthority *to = m->recipient;
        pthread_mutex_lock(&to->cell.mu); GROW(to->outbox, to->nout, to->capout); to->outbox[to->nout++] = m; __atomic_store_n(&m->emitted, true, __ATOMIC_RELEASE); pthread_mutex_unlock(&to->cell.mu);
        EV(emits); xc_inc(&d->occ->work.emits);
        return;
    }
    EffCell *c = d->cells[r];
    pthread_mutex_lock(&c->mu);
    if (c->res == d && c->slot == r) { c->head = __atomic_load_n(&d->state, __ATOMIC_ACQUIRE) == D_COMMITTED ? d->succ[r] : d->expected[r]; c->res = NULL; }
    pthread_mutex_unlock(&c->mu);
    EV(finalizes); xc_inc(&d->occ->work.finalizes);
}

/* ---------------- readings ---------------- */
static const EffHead *cell_logical(EffCell *c) {
    pthread_mutex_lock(&c->mu);
    const EffHead *h = c->head;
    if (c->res) h = __atomic_load_n(&c->res->state, __ATOMIC_ACQUIRE) == D_COMMITTED ? c->res->succ[c->slot] : c->res->expected[c->slot];
    pthread_mutex_unlock(&c->mu);
    return h;
}
const EffHead *eff_head(EffAuthority *a) { return cell_logical(&a->cell); }
RefId eff_head_state(const EffHead *h) { return h->state; }
const EffOcc *eff_head_producer(const EffHead *h) { return h->producer; }
bool eff_port_open(EffPort *m) { return occ_accepted(m->issuer) && !cell_logical(&m->cell)->consumed; }
const EffOcc *eff_port_consumer(EffPort *m) { const EffHead *h = cell_logical(&m->cell); return h->consumed ? h->producer : NULL; }
size_t eff_ports(EffPort ***out) {   /* the ports of accepted occurrences */
    pthread_mutex_lock(&X.mu); size_t n = 0; for (EffPort *m = X.published; m; m = m->pub_next) n++;
    EffPort **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); size_t i = n; for (EffPort *m = X.published; m; m = m->pub_next) v[--i] = m;
    pthread_mutex_unlock(&X.mu); *out = v; return n;
}
size_t eff_authorities(EffAuthority ***out) {
    pthread_mutex_lock(&X.mu); size_t n = 0; for (EffAuthority *a = X.auths; a; a = a->all_next) n++;
    EffAuthority **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); size_t i = n; for (EffAuthority *a = X.auths; a; a = a->all_next) v[--i] = a;
    pthread_mutex_unlock(&X.mu); *out = v; return n;
}
/* a consistent cut: every logical head and every open port, read between two equal even values of the commit sequence */
bool eff_cut_snapshot(EffCut *out) {
    for (;;) {
        uint64_t s1 = __atomic_load_n(&X.cut_seq, __ATOMIC_ACQUIRE);
        if (s1 & 1) { sched_yield(); continue; }
        EffAuthority **as; size_t na = eff_authorities(&as);
        EffPort **ps; size_t np = eff_ports(&ps);
        const EffHead **hs = malloc((na ? na : 1) * sizeof *hs); EffPort **open = malloc((np ? np : 1) * sizeof *open); require(hs && open, "out of memory");
        for (size_t i = 0; i < na; i++) hs[i] = cell_logical(&as[i]->cell);
        size_t no = 0; for (size_t i = 0; i < np; i++) if (!cell_logical(&ps[i]->cell)->consumed) open[no++] = ps[i];
        free(ps);
        if (__atomic_load_n(&X.cut_seq, __ATOMIC_ACQUIRE) == s1) { out->nheads = na; out->auth = as; out->head = hs; out->nopen = no; out->open = open; return true; }
        free(as); free(hs); free(open);
    }
}
void eff_cut_free(EffCut *c) { free(c->auth); free(c->head); free(c->open); memset(c, 0, sizeof *c); }
RefId eff_port_payload(const EffPort *m) { return m->payload; }
EffAuthority *eff_port_recipient(const EffPort *m) { return m->recipient; }
const EffOcc *eff_port_issuer(const EffPort *m) { return m->issuer; }
uint64_t eff_occ_id(const EffOcc *e) { return e->id; }
bool eff_occ_accepted(const EffOcc *e) { return occ_accepted(e); }
const char *eff_occ_schema(const EffOcc *e) { return e->schema->name; }
size_t eff_occ_nports(const EffOcc *e) { return occ_accepted(e) ? e->nports : 0; }
EffPort *eff_occ_port(const EffOcc *e, size_t slot) { return occ_accepted(e) && slot < e->nports ? e->ports[slot] : NULL; }
RefId eff_receipt_observe(const EffOcc *e, int field) {
    require(occ_accepted(e), "receipt observation of an occurrence that was not accepted");
    switch (field) { case EFF_FIELD_WITNESS: return e->witness; case EFF_FIELD_SOURCE: return e->s; case EFF_FIELD_TARGET: return e->t; case EFF_FIELD_EDGE_TYPE: return e->edge; }
    return 0;
}
size_t eff_occ_inputs(const EffOcc *e, const EffOcc **producers, size_t max) {
    size_t n = e->d->P->nin; for (size_t r = 0; r < n && r < max; r++) producers[r] = e->d->expected[r]->producer;
    return n;
}
size_t eff_occ_assumptions(const EffOcc *e, const uint64_t **syms) { *syms = e->assume; return e->nassume; }
uint64_t eff_occ_env(const EffOcc *e) { return e->env; }
EffOccWork eff_occ_work(const EffOcc *e) {
    EffOccWork w; w.prepare_steps = xc_snap(&e->work.prepare_steps); w.audit_units = xc_snap(&e->work.audit_units); w.reservations = xc_snap(&e->work.reservations);
    w.waits = xc_snap(&e->work.waits); w.commit = xc_snap(&e->work.commit); w.finalizes = xc_snap(&e->work.finalizes); w.deliveries = xc_snap(&e->work.deliveries); w.emits = xc_snap(&e->work.emits);
    return w;
}
/* the preparation work of descriptors that have no occurrence record (settled invalid, or pending) */
void eff_unattributed(XSnap *prep, XSnap *audit) {
    XCount p = {0}, a = {0};
    pthread_mutex_lock(&X.mu);
    for (EffCommit *d = X.commits; d; d = d->all_next) if (!d->occ) { xc_add_snap(&p, xc_snap(&d->wprep)); xc_add_snap(&a, xc_snap(&d->waudit)); }
    pthread_mutex_unlock(&X.mu);
    *prep = xc_snap(&p); *audit = xc_snap(&a);
}
size_t eff_pending_emissions(void) {   /* committed outputs not yet emitted: obligations a durable boundary would have to retain */
    size_t n = 0; pthread_mutex_lock(&X.mu);
    for (EffPort *m = X.published; m; m = m->pub_next) if (!__atomic_load_n(&m->emitted, __ATOMIC_ACQUIRE)) n++;
    pthread_mutex_unlock(&X.mu); return n;
}
bool eff_receipt_view(const EffOcc *e, MapId sigma, size_t slot, RefId claimed_payload, EffAuthority *claimed_recipient, EffView *out, const char **why) {
    if (!occ_accepted(e)) { *why = "not an accepted occurrence"; return false; }
    if (slot >= e->nports) { *why = "no such port occurrence"; return false; }
    EffPort *m = e->ports[slot];
    if (claimed_recipient != m->recipient) { *why = "the view changes the recipient without a boundary transport"; return false; }
    RefId moved = reindex(m->payload, sigma);
    if (moved != m->payload) { *why = "the map changes the resource payload: not a view of this occurrence"; return false; }
    if (claimed_payload != moved) { *why = "the claimed payload is not the transported payload"; return false; }
    out->occ = e; out->sigma = sigma; out->slot = slot; out->payload = moved; out->recipient = m->recipient;
    return true;
}
bool eff_view_reindex(const EffView *v, MapId tau, EffView *out, const char **why) {
    return eff_receipt_view(v->occ, compose(v->sigma, tau), v->slot, reindex(v->payload, tau), v->recipient, out, why);
}
size_t eff_outbox(EffAuthority *a, EffPort ***out) {
    pthread_mutex_lock(&a->cell.mu); size_t n = a->nout; EffPort **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); if (n) memcpy(v, a->outbox, n * sizeof *v); pthread_mutex_unlock(&a->cell.mu);
    *out = v; return n;
}
size_t eff_occurrences(const EffOcc ***out) {
    pthread_mutex_lock(&X.mu); size_t n = 0; for (EffOcc *e = X.occs; e; e = e->all_next) n++;
    const EffOcc **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); size_t i = n; for (EffOcc *e = X.occs; e; e = e->all_next) v[--i] = e;
    pthread_mutex_unlock(&X.mu); *out = v; return n;
}
size_t eff_history(const EffOcc ***out) {
    pthread_mutex_lock(&X.mu); size_t n = X.nhist; const EffOcc **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); if (n) memcpy(v, X.hist, n * sizeof *v); pthread_mutex_unlock(&X.mu);
    *out = v; return n;
}

/* ---------------- resource occurrences and the incidence reading ---------------- */
static EffRes res_head(const EffHead *h) { EffRes r = { 0, h->id, h->state, h->auth }; return r; }
static EffRes res_port(const EffPort *m) { EffRes r = { 1, m->id, m->payload, m->recipient }; return r; }
size_t eff_occ_consumed(const EffOcc *e, EffRes *out, size_t max) {
    EffCommit *d = e->d; size_t n = d->P->nin;
    for (size_t r = 0; r < n && r < max; r++) { EffIn *in = &d->P->in[d->order[r]]; out[r] = in->kind ? res_port(in->port) : res_head(d->expected[r]); }
    return n;
}
size_t eff_occ_produced(const EffOcc *e, EffRes *out, size_t max) {
    EffCommit *d = e->d; size_t n = 0;
    for (size_t r = 0; r < d->P->nin; r++) if (!d->P->in[d->order[r]].kind) { if (n < max) out[n] = res_head(d->succ[r]); n++; }
    for (size_t i = 0; i < e->nports; i++) { if (n < max) out[n] = res_port(e->ports[i]); n++; }
    return n;
}
size_t eff_cut_resources(const EffCut *c, EffRes *out, size_t max) {
    size_t n = 0;
    for (size_t i = 0; i < c->nheads; i++) { if (n < max) out[n] = res_head(c->head[i]); n++; }
    for (size_t i = 0; i < c->nopen; i++) { if (n < max) out[n] = res_port(c->open[i]); n++; }
    return n;
}
size_t eff_genesis_resources(EffRes *out, size_t max) {
    EffAuthority **as; size_t na = eff_authorities(&as);
    for (size_t i = 0; i < na && i < max; i++) out[i] = res_head(as[i]->genesis);
    free(as); return na;
}
CellId eff_res_cell(const EffRes *r) { return cell_declared(EFF_NS_RES, ((uint64_t)r->kind << 63) | r->id, 0, chain_zero(0), NULL); }
ChainId eff_resources_chain(const EffRes *r, size_t n) {
    CellId *c = malloc((n ? n : 1) * sizeof *c); ModId *m = malloc((n ? n : 1) * sizeof *m); require(c && m, "out of memory");
    for (size_t k = 0; k < n; k++) { c[k] = eff_res_cell(&r[k]); m[k] = mod_int(zx_i64(1)); }
    ChainId out = chain_from(0, n, c, m); free(c); free(m); return out;
}
CellId eff_event_cell(const EffOcc *e) {
    require(occ_accepted(e), "only an accepted occurrence is an event of the incidence complex");
    EffRes in[16], outp[16]; size_t ni = eff_occ_consumed(e, in, 16), no = eff_occ_produced(e, outp, 16);
    require(ni <= 16 && no <= 16, "event arity");
    ChainId b = chain_sub(eff_resources_chain(outp, no), eff_resources_chain(in, ni));
    const char *why = NULL; CellId x = cell_declared(EFF_NS_EVENT, e->id, 1, b, &why);
    if (!x) die("event admission: %s", why ? why : "?");
    return x;
}
ChainId eff_cut_chain(const EffCut *c) {
    size_t n = eff_cut_resources(c, NULL, 0); EffRes *r = malloc((n ? n : 1) * sizeof *r); require(r, "out of memory");
    eff_cut_resources(c, r, n); ChainId b = eff_resources_chain(r, n); free(r); return b;
}
CellId eff_state_cell(ChainId b0) { return cell_presented(EFF_NS_STATE, b0, 0, NULL, NULL); }
static ChainId resmap_act(void *ctx, CellId x) {
    (void)ctx; uint64_t ns; uint64_t tag = cell_tag(x, &ns);
    if (ns == EFF_NS_STATE) return (ChainId)tag;                                   /* B_0(s): the state's exposed occurrences */
    require(ns == EFF_NS_STEP, "the resource reading maps execution states and steps");
    uint64_t key[1] = { x }, v = 0; require(wordmap_get(&X.stepocc, key, 1, &v), "a step of a replayed execution");
    const EffOcc *e = (const EffOcc *)(uintptr_t)v;
    return chain_gen(eff_event_cell(e), mod_int(zx_i64(1)));                       /* B_1(e): the event */
}
ChainMapT *eff_resource_map(void) {
    pthread_mutex_lock(&X.mu); if (!X.resmap) X.resmap = chainmap_new(resmap_act, NULL, 0); ChainMapT *F = X.resmap; pthread_mutex_unlock(&X.mu);
    return F;
}
const EffOcc *eff_step_occurrence(CellId step) { uint64_t key[1] = { step }, v = 0; return wordmap_get(&X.stepocc, key, 1, &v) ? (const EffOcc *)(uintptr_t)v : NULL; }
bool eff_execution(EffExecution *out, const char **why) {
    const EffOcc **h; size_t n = eff_history(&h);
    memset(out, 0, sizeof *out);
    out->states = malloc((n + 1) * sizeof *out->states); out->steps = malloc((n ? n : 1) * sizeof *out->steps); out->occ = malloc((n ? n : 1) * sizeof *out->occ);
    require(out->states && out->steps && out->occ, "out of memory");
    size_t ng = eff_genesis_resources(NULL, 0); EffRes *g = malloc((ng ? ng : 1) * sizeof *g); require(g, "out of memory");
    eff_genesis_resources(g, ng); ChainId cur = eff_resources_chain(g, ng); free(g);
    out->states[0] = eff_state_cell(cur);
    for (size_t k = 0; k < n; k++) {
        EffRes in[16], pr[16]; size_t ni = eff_occ_consumed(h[k], in, 16), np = eff_occ_produced(h[k], pr, 16);
        for (size_t r = 0; r < ni; r++) {
            ModId c = chain_coef(cur, eff_res_cell(&in[r]));
            if (mod_is_zero(c)) { if (why) *why = "a replayed input occurrence is not exposed at its cut"; free(h); eff_execution_free(out); return false; }
        }
        cur = chain_add(chain_sub(cur, eff_resources_chain(in, ni)), eff_resources_chain(pr, np));
        out->states[k + 1] = eff_state_cell(cur);
        CellId f[2] = { out->states[k], out->states[k + 1] };
        out->steps[k] = cell_presented(EFF_NS_STEP, h[k]->id, 1, f, why);
        if (!out->steps[k]) { free(h); eff_execution_free(out); return false; }
        out->occ[k] = h[k];
        uint64_t key[1] = { out->steps[k] }; wordmap_put(&X.stepocc, key, 1, (uint64_t)(uintptr_t)h[k]);
    }
    out->n = n; free(h);
    return true;
}
void eff_execution_free(EffExecution *x) { free(x->states); free(x->steps); free(x->occ); memset(x, 0, sizeof *x); }

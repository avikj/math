/* effect.c — see effect.h and EFFECT-AUTHORITY.md §§2–4, 8–10. */
#include "effect.h"
#include "work.h"
#include "fine.h"
#include "lib.h"
#include <string.h>

struct EffSchema { const char *name; ContextId G; FaceId kappa; RefId In, Out, R; int port_role; EffSchema *all_next; };
/* a head cell: AVAILABLE(head) when res == NULL, else RESERVED(res, slot) —
 * interpreted by the descriptor's state (RESERVING: unavailable; COMMITTED:
 * its successor; ABORTED: the former head) */
typedef struct EffCell { uint64_t id; pthread_mutex_t mu; const EffHead *head; EffCommit *res; size_t slot; } EffCell;
struct EffHead { uint64_t id; EffAuthority *auth; EffPort *port; RefId state; const EffOcc *producer; const EffHead *pred; bool consumed; EffHead *all_next; };
struct EffAuthority { uint64_t id; const char *name; ContextId G; FaceId kappa; RefId type; EffCell cell; EffPort **outbox; size_t nout, capout; EffAuthority *all_next; };
struct EffPort { uint64_t id; const EffOcc *issuer; size_t slot; RefId payload; EffAuthority *recipient, *refund_to; const EffHead *token; EffCell cell; bool emitted; EffPort *all_next; };   /* token: its unconsumed head */
struct EffCap { uint64_t id; EffAuthority *auth; EffCap *all_next; };
typedef struct { XCount prepare_steps, audit_units, reservations, waits, commit, finalizes, deliveries, emits; } OccWork;
struct EffOcc {
    uint64_t id; EffSchema *schema; EffCommit *d;
    RefId s, t, witness, edge;          /* the admitted judgment p : R s t */
    uint64_t *assume; size_t nassume; uint64_t env;
    EffPort **ports; size_t nports;
    bool accepted;                      /* set at the commit transition (atomic) */
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
typedef struct Waiter { EffDeliver k; void *ctx; struct Waiter *next; } Waiter;
enum { D_PREPARING = 0, D_RESERVING, D_COMMITTED, D_ABORTED, D_INVALID };
struct EffCommit {
    EffProposal *P; int state; bool unresolved; const char *why; const EffOcc *holder;
    pthread_mutex_t mu; Waiter *waiters; EffCommit **joined; size_t njoined, capjoined;
    int phase; size_t k;                 /* preparation phase and cursor; reservation cursor */
    OpId audit; RefId s, t, edge;
    XCount wprep, waudit;                /* preparation work before the occurrence record exists (moved into it at phase 6) */
    uint64_t *assume; size_t nassume;
    size_t *order;                       /* inputs sorted by cell identity */
    EffCell **cells; const EffHead **expected; EffHead **succ;   /* per sorted input */
    EffOcc *occ;
    EffCommit *all_next;
};

static struct {
    pthread_mutex_t mu;                  /* registries, request index, history: constant sections */
    uint64_t ids;
    EffSchema *schemas; EffAuthority *auths; EffHead *heads; EffPort *ports; EffCap *caps; EffOcc *occs; EffCommit *commits;
    WordMap index;                       /* (ns, request) -> descriptor */
    const EffOcc **hist; size_t nhist, caphist;
    XCount ev[sizeof(EffEvents) / sizeof(size_t)];
    bool live;
} X;
#define EV(f) xc_inc(&X.ev[offsetof(EffEvents, f) / sizeof(size_t)])
static uint64_t fresh_id(void) { return __atomic_add_fetch(&X.ids, 1, __ATOMIC_RELAXED); }
#define GROW(arr, n, cap) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 4; (arr) = realloc((arr), (cap) * sizeof *(arr)); require((arr), "out of memory"); } } while (0)

void effect_init(void) { memset(&X, 0, sizeof X); pthread_mutex_init(&X.mu, NULL); wordmap_init(&X.index); X.live = true; }
void effect_free(void) {
    if (!X.live) return;
    for (EffCommit *d = X.commits, *n; d; d = n) {
        n = d->all_next;
        for (Waiter *w = d->waiters, *wn; w; w = wn) { wn = w->next; free(w); }
        EffProposal *P = d->P; free(P->in); free(P->oh); free(P->op); free(P->caps); free(P);
        free(d->joined); free(d->order); free(d->cells); free(d->expected); free(d->succ); free(d->assume);
        if (d->audit) op_release(d->audit);
        pthread_mutex_destroy(&d->mu); free(d);
    }
    for (EffOcc *e = X.occs, *n; e; e = n) { n = e->all_next; free(e->ports); free(e->assume); free(e); }
    for (EffPort *m = X.ports, *n; m; m = n) { n = m->all_next; pthread_mutex_destroy(&m->cell.mu); free(m); }
    for (EffAuthority *a = X.auths, *n; a; a = n) { n = a->all_next; free(a->outbox); pthread_mutex_destroy(&a->cell.mu); free(a); }
    for (EffHead *h = X.heads, *n; h; h = n) { n = h->all_next; free(h); }
    for (EffCap *c = X.caps, *n; c; c = n) { n = c->all_next; free(c); }
    for (EffSchema *s = X.schemas, *n; s; s = n) { n = s->all_next; free(s); }
    free(X.hist); wordmap_free(&X.index); pthread_mutex_destroy(&X.mu);
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
    cell_init(&a->cell, head_new(a, NULL, state, NULL, NULL, false));
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
void eff_in_port(EffProposal *P, EffPort *m) { GROW(P->in, P->nin, P->capin); P->in[P->nin++] = (EffIn){ 1, NULL, m, m->token }; }
void eff_out_head(EffProposal *P, EffAuthority *a, RefId state) { GROW(P->oh, P->noh, P->capoh); P->oh[P->noh++] = (EffOutH){ a, state }; }
void eff_out_port(EffProposal *P, RefId payload, EffAuthority *recipient, EffAuthority *refund_to) { GROW(P->op, P->nop, P->capop); P->op[P->nop++] = (EffOutP){ payload, recipient, refund_to }; }
void eff_witness(EffProposal *P, RefId p) { P->witness = p; }
void eff_cap(EffProposal *P, EffCap *c) { GROW(P->caps, P->ncaps, P->capcaps); P->caps[P->ncaps++] = c; }
EffProposal *eff_proposal_reindex(const EffProposal *P, MapId sigma, uint64_t request) {
    EffProposal *Q = eff_proposal(P->schema, P->ns, request);
    for (size_t i = 0; i < P->nin; i++) { GROW(Q->in, Q->nin, Q->capin); Q->in[Q->nin++] = P->in[i]; }
    for (size_t i = 0; i < P->noh; i++) eff_out_head(Q, P->oh[i].auth, reindex(P->oh[i].state, sigma));
    for (size_t i = 0; i < P->nop; i++) eff_out_port(Q, reindex(P->op[i].payload, sigma), P->op[i].recipient, P->op[i].refund_to);
    Q->witness = P->witness ? reindex(P->witness, sigma) : 0;
    for (size_t i = 0; i < P->ncaps; i++) eff_cap(Q, P->caps[i]);
    return Q;
}
static void proposal_free(EffProposal *P) { free(P->in); free(P->oh); free(P->op); free(P->caps); free(P); }
void eff_proposal_free(EffProposal *P) { if (P) proposal_free(P); }
static bool same_anchor(const EffProposal *a, const EffProposal *b) {
    if (a->schema != b->schema || a->nin != b->nin || a->noh != b->noh || a->nop != b->nop || a->witness != b->witness) return false;
    for (size_t i = 0; i < a->nin; i++) if (a->in[i].kind != b->in[i].kind || a->in[i].auth != b->in[i].auth || a->in[i].port != b->in[i].port || a->in[i].expected != b->in[i].expected) return false;
    for (size_t i = 0; i < a->noh; i++) if (a->oh[i].auth != b->oh[i].auth || a->oh[i].state != b->oh[i].state) return false;
    for (size_t i = 0; i < a->nop; i++) if (a->op[i].payload != b->op[i].payload || a->op[i].recipient != b->op[i].recipient || a->op[i].refund_to != b->op[i].refund_to) return false;
    return true;
}

/* ---------------- jobs ---------------- */
static void prepare_job(void *p);
static void reserve_job(void *p);
static void commit_job(void *p);
typedef struct { EffCommit *d; size_t k; bool emit; } FinArg;
static void finalize_job(void *p);
typedef struct { EffDeliver k; void *ctx; EffOutcome o; EffOcc *occ; } DelArg;
static void deliver_job(void *p) { DelArg *a = p; if (a->occ) xc_inc(&a->occ->work.deliveries); EV(deliveries); a->k(a->ctx, a->o); free(a); }
static EffOutcome outcome_of(EffCommit *d) {
    EffOutcome o = { EO_PENDING, NULL, NULL, d->why };
    int st = __atomic_load_n(&d->state, __ATOMIC_ACQUIRE);
    if (st == D_COMMITTED) { o.kind = EO_ACCEPTED; o.receipt = d->occ; }
    else if (st == D_ABORTED) { o.kind = EO_CONFLICT; o.holder = d->holder; }
    else if (st == D_INVALID) o.kind = EO_INVALID;
    return o;
}
static void deliver_to(EffDeliver k, void *ctx, EffOutcome o, EffOcc *occ) {
    DelArg *a = calloc(1, sizeof *a); require(a, "out of memory"); a->k = k; a->ctx = ctx; a->o = o; a->occ = occ;
    eval_job(deliver_job, a, EFF_TAG_DELIVER);
}
/* a terminal transition: deliver to the attached clients (one job each) and wake the descriptors joined on this one */
static void settle(EffCommit *d) {
    pthread_mutex_lock(&d->mu);
    Waiter *w = d->waiters; d->waiters = NULL;
    EffCommit **j = d->joined; size_t nj = d->njoined; d->joined = NULL; d->njoined = d->capjoined = 0;
    pthread_mutex_unlock(&d->mu);
    EffOutcome o = outcome_of(d);
    while (w) { Waiter *n = w->next; deliver_to(w->k, w->ctx, o, o.kind == EO_ACCEPTED ? d->occ : NULL); free(w); w = n; }
    for (size_t i = 0; i < nj; i++) eval_job(reserve_job, j[i], EFF_TAG_RESERVE);   /* recheck that cell */
    free(j);
}

EffCommit *eff_request(EffProposal *P, EffDeliver k, void *ctx) {
    EV(requests);
    uint64_t key[2] = { P->ns, P->request }, have = 0;
    pthread_mutex_lock(&X.mu);
    if (wordmap_get(&X.index, key, 2, &have)) {
        EffCommit *d = (EffCommit *)(uintptr_t)have;
        pthread_mutex_unlock(&X.mu);
        if (!same_anchor(d->P, P)) { EV(request_conflicts); EffOutcome o = { EO_REQUEST_CONFLICT, NULL, NULL, "request identity reused with different anchored proposal data" }; proposal_free(P); if (k) deliver_to(k, ctx, o, NULL); return d; }
        proposal_free(P); EV(joins);
        if (!k) return d;
        pthread_mutex_lock(&d->mu);
        int st = __atomic_load_n(&d->state, __ATOMIC_ACQUIRE);
        bool terminal = st == D_COMMITTED || st == D_ABORTED || st == D_INVALID;
        if (!terminal) { Waiter *w = calloc(1, sizeof *w); require(w, "out of memory"); w->k = k; w->ctx = ctx; w->next = d->waiters; d->waiters = w; }
        pthread_mutex_unlock(&d->mu);
        if (terminal) deliver_to(k, ctx, outcome_of(d), st == D_COMMITTED ? d->occ : NULL);   /* the same receipt; no second occurrence */
        return d;
    }
    EffCommit *d = calloc(1, sizeof *d); require(d, "out of memory");
    d->P = P; pthread_mutex_init(&d->mu, NULL); d->state = D_PREPARING;
    if (k) { Waiter *w = calloc(1, sizeof *w); require(w, "out of memory"); w->k = k; w->ctx = ctx; d->waiters = w; }
    wordmap_put(&X.index, key, 2, (uint64_t)(uintptr_t)d);
    d->all_next = X.commits; X.commits = d;
    pthread_mutex_unlock(&X.mu);
    EV(prepares);
    eval_job(prepare_job, d, EFF_TAG_PREPARE);
    return d;
}
EffOutcomeKind eff_commit_state(const EffCommit *d) { return outcome_of((EffCommit *)d).kind; }
bool eff_commit_unresolved(const EffCommit *d) { return __atomic_load_n(&d->unresolved, __ATOMIC_ACQUIRE); }

static void invalid(EffCommit *d, const char *why) { d->why = why; EV(invalid); __atomic_store_n(&d->state, D_INVALID, __ATOMIC_RELEASE); settle(d); }
static RefId tuple(const RefId *xs, size_t n) { if (!n) return 0; RefId t = xs[n - 1]; for (size_t i = n - 1; i-- > 0; ) t = mk_pair(xs[i], t); return t; }
static const EffHead *cell_logical(EffCell *c, bool *reserved);

/* PREPARE_EFFECT: one phase step per job
 *   0  interface, one input per step: unique cells, port role, authorization (a valid issued capability)
 *   1  outputs: each consumed head has a successor head for its authority
 *   2  the judgment: s = tuple of input states, t = tuple of output states and port payloads, R s t
 *   3,4,5  the audits of s : In, t : Out, p : R s t — one engine unit per job
 *   6  pin the environment snapshot; prepare the occurrence, successor heads, consumed-port markers and the reservation order */
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
        EffCell *c = in->kind ? &in->port->cell : &in->auth->cell;
        for (size_t j = 0; j < d->k; j++) { EffCell *cj = P->in[j].kind ? &P->in[j].port->cell : &P->in[j].auth->cell; if (cj == c) { invalid(d, "an input occurrence appears twice"); return; } }
        EffAuthority *need = in->kind ? (S->port_role == EFF_PORT_REFUND ? in->port->refund_to : in->port->recipient) : in->auth;
        if (!need) { invalid(d, "the port names no authority for this consumption"); return; }
        bool ok = false; for (size_t j = 0; j < P->ncaps && !ok; j++) ok = cap_valid(P->caps[j], need);
        if (!ok) { invalid(d, "no valid capability issued by the required authority"); return; }
        d->k++; break;
    }
    case 1: {
        for (size_t i = 0; i < P->nin; i++) if (!P->in[i].kind) {
            bool succ = false; for (size_t j = 0; j < P->noh && !succ; j++) succ = P->oh[j].auth == P->in[i].auth;
            if (!succ) { invalid(d, "a consumed head has no successor head for its authority"); return; }
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
        if (v == PU_PENDING || v == PU_UNRESOLVED) { __atomic_store_n(&d->unresolved, true, __ATOMIC_RELEASE); EV(unresolved); d->why = "a required proof is pending"; return; }   /* stays pending with its continuation */
        d->phase++; break;
    }
    case 6: {
        size_t n = P->nin;
        d->order = malloc((n ? n : 1) * sizeof *d->order); d->cells = malloc((n ? n : 1) * sizeof *d->cells);
        d->expected = malloc((n ? n : 1) * sizeof *d->expected); d->succ = malloc((n ? n : 1) * sizeof *d->succ);
        require(d->order && d->cells && d->expected && d->succ, "out of memory");
        EffOcc *e = calloc(1, sizeof *e); require(e, "out of memory");
        e->id = fresh_id(); e->schema = S; e->d = d; e->s = d->s; e->t = d->t; e->witness = P->witness; e->edge = d->edge;
        e->assume = d->assume; e->nassume = d->nassume; d->assume = NULL; d->nassume = 0; e->env = global_env_version();
        e->nports = P->nop; e->ports = calloc(P->nop ? P->nop : 1, sizeof *e->ports); require(e->ports, "out of memory");
        for (size_t i = 0; i < P->nop; i++) {
            EffPort *m = calloc(1, sizeof *m); require(m, "out of memory");
            m->id = fresh_id(); m->issuer = e; m->slot = i; m->payload = P->op[i].payload; m->recipient = P->op[i].recipient; m->refund_to = P->op[i].refund_to;
            m->token = head_new(NULL, m, m->payload, e, NULL, false); cell_init(&m->cell, m->token);   /* its unconsumed token: readable only after acceptance */
            e->ports[i] = m;
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
    for (size_t r = 0; r < d->k; r++) { FinArg *a = malloc(sizeof *a); require(a, "out of memory"); a->d = d; a->k = r; a->emit = false; eval_job(finalize_job, a, EFF_TAG_FINALIZE); }   /* rollback of the cells it reserved */
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
/* the one acceptance event */
static void commit_job(void *p) {
    EffCommit *d = p;
    int exp = D_RESERVING;
    if (!__atomic_compare_exchange_n(&d->state, &exp, D_COMMITTED, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return;
    EffOcc *e = d->occ;
    __atomic_store_n(&e->accepted, true, __ATOMIC_RELEASE);
    EV(commits); xc_inc(&e->work.commit);
    pthread_mutex_lock(&X.mu); GROW(X.hist, X.nhist, X.caphist); X.hist[X.nhist++] = e; pthread_mutex_unlock(&X.mu);
    for (size_t r = 0; r < d->P->nin; r++) { FinArg *a = malloc(sizeof *a); require(a, "out of memory"); a->d = d; a->k = r; a->emit = false; eval_job(finalize_job, a, EFF_TAG_FINALIZE); }
    for (size_t i = 0; i < e->nports; i++) { FinArg *a = malloc(sizeof *a); require(a, "out of memory"); a->d = d; a->k = i; a->emit = true; eval_job(finalize_job, a, EFF_TAG_EMIT); }
    settle(d);
}
/* FINALIZE(D, k): materialize the reservation (successor if committed, former head if aborted); EMIT for k = -1-slot */
static void finalize_job(void *p) {
    FinArg *a = p; EffCommit *d = a->d; size_t r = a->k; bool emit = a->emit; free(a);
    if (emit) {   /* EMIT(E, slot): the committed port's description to its endpoint's outbox */
        EffPort *m = d->occ->ports[r];
        EffAuthority *to = m->recipient;
        pthread_mutex_lock(&to->cell.mu); GROW(to->outbox, to->nout, to->capout); to->outbox[to->nout++] = m; m->emitted = true; pthread_mutex_unlock(&to->cell.mu);
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
static const EffHead *cell_logical(EffCell *c, bool *reserved) {
    pthread_mutex_lock(&c->mu);
    const EffHead *h = c->head; bool res = false;
    if (c->res) {
        int st = __atomic_load_n(&c->res->state, __ATOMIC_ACQUIRE);
        if (st == D_COMMITTED) h = c->res->succ[c->slot];
        else { h = c->res->expected[c->slot]; res = st == D_RESERVING; }
    }
    pthread_mutex_unlock(&c->mu);
    if (reserved) *reserved = res;
    return h;
}
const EffHead *eff_head(EffAuthority *a) { return cell_logical(&a->cell, NULL); }
RefId eff_head_state(const EffHead *h) { return h->state; }
const EffOcc *eff_head_producer(const EffHead *h) { return h->producer; }
bool eff_port_open(EffPort *m) { if (!__atomic_load_n(&m->issuer->accepted, __ATOMIC_ACQUIRE)) return false; return !cell_logical(&m->cell, NULL)->consumed; }
const EffOcc *eff_port_consumer(EffPort *m) { const EffHead *h = cell_logical(&m->cell, NULL); return h->consumed ? h->producer : NULL; }
size_t eff_ports(EffPort ***out) {
    pthread_mutex_lock(&X.mu); size_t n = 0; for (EffPort *m = X.ports; m; m = m->all_next) n++;
    EffPort **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); size_t i = n; for (EffPort *m = X.ports; m; m = m->all_next) v[--i] = m;
    pthread_mutex_unlock(&X.mu); *out = v; return n;
}
size_t eff_authorities(EffAuthority ***out) {
    pthread_mutex_lock(&X.mu); size_t n = 0; for (EffAuthority *a = X.auths; a; a = a->all_next) n++;
    EffAuthority **v = malloc((n ? n : 1) * sizeof *v); require(v, "out of memory"); size_t i = n; for (EffAuthority *a = X.auths; a; a = a->all_next) v[--i] = a;
    pthread_mutex_unlock(&X.mu); *out = v; return n;
}
RefId eff_port_payload(const EffPort *m) { return m->payload; }
EffAuthority *eff_port_recipient(const EffPort *m) { return m->recipient; }
const EffOcc *eff_port_issuer(const EffPort *m) { return m->issuer; }
uint64_t eff_occ_id(const EffOcc *e) { return e->id; }
bool eff_occ_accepted(const EffOcc *e) { return __atomic_load_n(&e->accepted, __ATOMIC_ACQUIRE); }
const char *eff_occ_schema(const EffOcc *e) { return e->schema->name; }
size_t eff_occ_nports(const EffOcc *e) { return e->nports; }
EffPort *eff_occ_port(const EffOcc *e, size_t slot) { return slot < e->nports ? e->ports[slot] : NULL; }
RefId eff_receipt_observe(const EffOcc *e, int field) {
    require(eff_occ_accepted(e), "receipt observation of an occurrence that was not accepted");
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
bool eff_receipt_view(const EffOcc *e, MapId sigma, size_t slot, RefId claimed_payload, EffAuthority *claimed_recipient, EffView *out, const char **why) {
    if (!eff_occ_accepted(e)) { *why = "not an accepted occurrence"; return false; }
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

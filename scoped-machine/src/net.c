#include "net.h"
#include "reuse.h"
#include "fine.h"
#include "lib.h"
#include "compiler.h"

/* ------------------------------------------------------------------ */
/* nodes and wiring                                                     */

static void *net_worker_main(void *arg);

void net_init(Net *n) {
    memset(n, 0, sizeof *n);
    n->rng = 0x9E3779B97F4A7C15ULL;
    chunked_init(&n->nodes, sizeof(Node));
    pthread_mutex_init(&n->alloc_mu, NULL);
    pthread_mutex_init(&n->act_mu, NULL);
    pthread_cond_init(&n->act_cv, NULL);
    pthread_cond_init(&n->idle_cv, NULL);
    pthread_mutex_init(&n->trace_mu, NULL);
}
size_t net_trace_count(Net *n) { pthread_mutex_lock(&n->trace_mu); size_t c = n->trace.len; pthread_mutex_unlock(&n->trace_mu); return c; }
NetTraceEvent net_trace_get(Net *n, size_t i) { pthread_mutex_lock(&n->trace_mu); NetTraceEvent e = n->trace.data[i]; pthread_mutex_unlock(&n->trace_mu); return e; }

static void net_stop_workers(Net *n) {
    if (!n->nworkers) return;
    pthread_mutex_lock(&n->act_mu);
    n->stop = true;
    pthread_cond_broadcast(&n->act_cv);
    pthread_mutex_unlock(&n->act_mu);
    for (size_t i = 0; i < n->nworkers; i++) pthread_join(n->workers[i], NULL);
    free(n->workers); n->workers = NULL; n->nworkers = 0; n->stop = false;
}

typedef struct { Net *net; } WorkerArg;

void net_set_workers(Net *n, size_t workers) {
    net_stop_workers(n);
    if (!workers) return;
    n->workers = calloc(workers, sizeof(pthread_t));
    require(n->workers, "out of memory");
    n->nworkers = workers;
    for (size_t i = 0; i < workers; i++) require(pthread_create(&n->workers[i], NULL, net_worker_main, n) == 0, "cannot start net worker");
}

static Node *N(const Net *n, NodeId id) { require(id, "bad node id 0"); return (Node *)chunked_get(&n->nodes, id); }
Node *net_node_ptr(const Net *n, NodeId a) { return N(n, a); }
size_t net_node_count(Net *n) { pthread_mutex_lock(&n->alloc_mu); size_t c = n->nnodes; pthread_mutex_unlock(&n->alloc_mu); return c; }

void net_free(Net *n) {
    net_stop_workers(n);
    vec_free(&n->trace); pthread_mutex_destroy(&n->trace_mu);
    for (size_t i = 1; i <= n->nnodes; i++) {
        Node *x = N(n, (NodeId)i);
        free(x->peer); free(x->polarity);
        if (x->head) { head_free(x->head); free(x->head); }
        pthread_mutex_destroy(&x->mu);
    }
    chunked_free(&n->nodes); vec_free(&n->active);
    pthread_mutex_destroy(&n->alloc_mu); pthread_mutex_destroy(&n->act_mu);
    pthread_cond_destroy(&n->act_cv); pthread_cond_destroy(&n->idle_cv);
}

NodeId net_node(Net *n, NodeKind kind, uint8_t nports, const int8_t *polarity, Payload p) {
    /* the node is fully initialized before its id is published */
    pthread_mutex_lock(&n->alloc_mu);
    NodeId id = (NodeId)(n->nnodes + 1);
    Node *x = (Node *)chunked_at(&n->nodes, id);
    memset(x, 0, sizeof *x);
    x->kind = kind; x->live = true; x->nports = nports; x->p = p; x->gen = 1;
    x->peer = calloc(nports ? nports : 1, sizeof(Endpoint));
    x->polarity = malloc((nports ? nports : 1) * sizeof(int8_t));
    require(x->peer && x->polarity, "out of memory");
    memcpy(x->polarity, polarity, nports);
    pthread_mutex_init(&x->mu, NULL);
    n->nnodes = id;
    pthread_mutex_unlock(&n->alloc_mu);
    return id;
}

static bool is_descriptor(NodeKind k) { return k >= D_REF && k <= D_TYPED_PARTIAL; }
static bool is_operation(NodeKind k) { return k >= OP_REINDEX_TERM && k <= OP_TYPED_PARTIAL_GUARD; }

NodeId net_descriptor(Net *n, NodeKind kind, Payload p) {
    require(is_descriptor(kind), "not a descriptor kind");
    int8_t pol[1] = { +1 };
    return net_node(n, kind, 1, pol, p);
}

NodeId net_operation(Net *n, NodeKind kind, Payload p) {
    require(is_operation(kind), "not an operation kind");
    int8_t pol[2] = { -1, +1 };
    return net_node(n, kind, 2, pol, p);
}

static NodeId net_pending(Net *n) { Payload p = {0}; int8_t pol[1] = { +1 }; return net_node(n, (NodeKind)0, 1, pol, p); }

bool net_is_live(const Net *n, NodeId a) {
    if (!a) return false;
    Node *x = (Node *)chunked_get(&n->nodes, a);
    pthread_mutex_lock(&x->mu);
    bool live = x->live;
    pthread_mutex_unlock(&x->mu);
    return live;
}

/* new active pairs created inside a replacement are collected here and
 * enqueued after the replacement's locks are released */
typedef VEC(Active) ActiveVec;
static __thread ActiveVec *tls_pending = NULL;

static void push_active(Net *n, NodeId a, uint64_t gen) {
    Active it = { a, gen };
    if (tls_pending) { vec_push(tls_pending, it); return; }
    if (n->shared.mu) {
        pthread_mutex_lock(n->shared.mu);
        (*n->shared.outstanding)++;
        vec_push(&n->active, it);
        pthread_cond_signal(n->shared.cv);
        pthread_mutex_unlock(n->shared.mu);
        return;
    }
    pthread_mutex_lock(&n->act_mu);
    n->outstanding++;
    vec_push(&n->active, it);
    pthread_cond_signal(&n->act_cv);
    pthread_mutex_unlock(&n->act_mu);
}
void net_share_scheduler(Net *n, pthread_mutex_t *mu, pthread_cond_t *cv, size_t *outstanding) {
    n->shared.mu = mu; n->shared.cv = cv; n->shared.outstanding = outstanding;
}
size_t net_pending_pairs_locked(const Net *n) { return n->active.len; }
static void net_finish_job(Net *n) {
    pthread_mutex_lock(&n->act_mu);
    require(n->outstanding > 0, "net finish without outstanding job");
    if (--n->outstanding == 0) pthread_cond_broadcast(&n->idle_cv);
    pthread_mutex_unlock(&n->act_mu);
}

/* Callers hold the owner locks of a and b unless the node is fresh (private
 * to the replacement) or the net is quiescent (client wiring). */
void net_connect(Net *n, NodeId a, uint16_t pa, NodeId b, uint16_t pb) {
    Node *x = N(n, a), *y = N(n, b);
    require(x->live && y->live, "connecting a retired node");
    require(pa < x->nports && pb < y->nports, "port out of range");
    require(x->polarity[pa] + y->polarity[pb] == 0, "polarity violation: only opposite polarities connect");
    x->peer[pa].node = b; x->peer[pa].port = pb;
    y->peer[pb].node = a; y->peer[pb].port = pa;
    if (pa == 0 && pb == 0) push_active(n, a, x->gen);
}

void net_disconnect(Net *n, NodeId a, uint16_t pa) {
    Node *x = N(n, a);
    Endpoint q = x->peer[pa];
    x->peer[pa].node = 0;
    if (q.node) N(n, q.node)->peer[q.port].node = 0;
}

Endpoint net_peer(const Net *n, NodeId a, uint16_t pa) { return N(n, a)->peer[pa]; }

static void retire(Net *n, NodeId a) {
    Node *x = N(n, a);
    x->live = false;                 /* under the owner lock */
    __atomic_add_fetch(&x->gen, 1, __ATOMIC_ACQ_REL);
    for (uint16_t k = 0; k < x->nports; k++) x->peer[k].node = 0;
}

static void count(size_t *c) { __atomic_add_fetch(c, 1, __ATOMIC_RELAXED); }

/* ------------------------------------------------------------------ */
/* local replacement with explicit boundary (§20)                       */

typedef struct {
    NodeId removed[4]; size_t nrem;
    /* for each removed node's auxiliary port: the fresh endpoint that takes
     * its place, or a connector to another removed aux port */
    struct { NodeId node; uint16_t port; Endpoint fresh; Endpoint connector; bool has_fresh; } wires[32];
    size_t nw;
    size_t closed_cycles;
} Replacement;

static void rep_init(Replacement *r) { memset(r, 0, sizeof *r); }
static void rep_remove(Replacement *r, NodeId a) { require(r->nrem < 4, "too many removed nodes"); r->removed[r->nrem++] = a; }
static bool rep_is_removed(const Replacement *r, NodeId a) { for (size_t i = 0; i < r->nrem; i++) if (r->removed[i] == a) return true; return false; }
static void rep_fresh(Replacement *r, NodeId a, uint16_t pa, NodeId b, uint16_t pb) {
    require(r->nw < 32, "too many boundary wires");
    r->wires[r->nw].node = a; r->wires[r->nw].port = pa;
    r->wires[r->nw].fresh.node = b; r->wires[r->nw].fresh.port = pb; r->wires[r->nw].has_fresh = true;
    r->nw++;
}
__attribute__((unused)) static void rep_connector(Replacement *r, NodeId a, uint16_t pa, NodeId b, uint16_t pb) {
    require(r->nw < 32, "too many boundary wires");
    r->wires[r->nw].node = a; r->wires[r->nw].port = pa;
    r->wires[r->nw].connector.node = b; r->wires[r->nw].connector.port = pb; r->wires[r->nw].has_fresh = false;
    r->nw++;
}
static int rep_find(const Replacement *r, NodeId a, uint16_t pa) {
    for (size_t i = 0; i < r->nw; i++) if (r->wires[i].node == a && r->wires[i].port == pa) return (int)i;
    return -1;
}

/* Every removed auxiliary port must be listed exactly once. Removed
 * principal ports are internal to the redex. Each fresh endpoint is joined
 * to the surviving endpoint reached by following old wires through
 * connectors; a path that returns to its origin is a closed wire component. */
static void rep_commit(Net *n, Replacement *r) {
    fine_bump(FC_NET_ACTIONS);
    /* validate: every aux port of every removed node is covered */
    for (size_t i = 0; i < r->nrem; i++) {
        Node *x = N(n, r->removed[i]);
        for (uint16_t k = 1; k < x->nports; k++) require(rep_find(r, r->removed[i], k) >= 0, "replacement leaves a removed auxiliary port unaccounted");
    }
    /* snapshot old peers before retiring */
    Endpoint *old = malloc((r->nw ? r->nw : 1) * sizeof(Endpoint));
    require(old, "out of memory");
    for (size_t i = 0; i < r->nw; i++) old[i] = N(n, r->wires[i].node)->peer[r->wires[i].port];
    bool *done = calloc(r->nw ? r->nw : 1, sizeof(bool));
    for (size_t i = 0; i < r->nw; i++) {
        if (!r->wires[i].has_fresh || done[i]) continue;
        /* follow from the old peer of this port */
        Endpoint q = old[i];
        size_t guard = 0;
        for (;;) {
            require(guard++ < 1000, "replacement path does not terminate");
            if (!q.node) { done[i] = true; break; }                    /* free end: fresh endpoint stays free */
            if (!rep_is_removed(r, q.node) || q.port == 0) {
                /* survivor (a removed principal is internal: it cannot be a boundary peer) */
                require(!rep_is_removed(r, q.node), "redex principal reached through a boundary path");
                net_connect(n, r->wires[i].fresh.node, r->wires[i].fresh.port, q.node, q.port);
                done[i] = true;
                break;
            }
            int j = rep_find(r, q.node, q.port);
            require(j >= 0, "removed aux without wiring");
            if (r->wires[j].has_fresh) {
                if ((size_t)j == i) { r->closed_cycles++; done[i] = true; break; }
                net_connect(n, r->wires[i].fresh.node, r->wires[i].fresh.port, r->wires[j].fresh.node, r->wires[j].fresh.port);
                done[i] = done[j] = true;
                break;
            }
            /* connector: continue from the partner's old peer */
            int pj = rep_find(r, r->wires[j].connector.node, r->wires[j].connector.port);
            require(pj >= 0, "dangling connector");
            done[j] = true;
            if (done[pj] && (size_t)pj != i) { break; }
            done[pj] = true;
            q = old[pj];
            if (q.node == r->wires[i].node && q.port == r->wires[i].port) { r->closed_cycles++; break; }
        }
    }
    free(done); free(old);
    for (size_t i = 0; i < r->nrem; i++) retire(n, r->removed[i]);
}

/* ------------------------------------------------------------------ */
/* rule helpers                                                         */

static NodeId status_node(Net *n, uint64_t code, FaceId face, RefId ref) {
    Payload p = {0}; p.a = code; p.face = face; p.ref = ref;
    return net_descriptor(n, D_STATUS, p);
}
enum { ST_NOT_COVERED = 0, ST_COVERED = 1, ST_NO_OBSERVATION = 2, ST_SORT_MISMATCH = 3, ST_INVALID_MAP = 4 };

/* one-result rule: replace OP (principal at port 0, result at port 1) and
 * its consumed descriptor by a fresh result descriptor D */
static void one_result(Net *n, NodeId op, NodeId data, NodeId result) {
    Replacement r; rep_init(&r);
    rep_remove(&r, op); rep_remove(&r, data);
    rep_fresh(&r, op, 1, result, 0);
    rep_commit(n, &r);
}

static NodeId desc_ref(Net *n, RefId t) { Payload p = {0}; p.ref = t; return net_descriptor(n, D_REF, p); }
static NodeId desc_face(Net *n, FaceId f) { Payload p = {0}; p.face = f; return net_descriptor(n, D_FACE, p); }
static NodeId desc_interval(Net *n, IntervalId r) { Payload p = {0}; p.a = r; return net_descriptor(n, D_INTERVAL, p); }
static NodeId desc_map(Net *n, MapId m, FaceId src, FaceId tgt) { Payload p = {0}; p.a = m; p.b = src; p.c = tgt; return net_descriptor(n, D_MAP, p); }
static NodeId desc_binder(Net *n, NodeKind kind, RefId owner, BinderSlot slot, FieldIndex field, FieldIndex guard) {
    Payload p = {0}; p.a = owner; p.b = slot; p.c = field; p.d = guard; return net_descriptor(n, kind, p);
}
static NodeId desc_partial(Net *n, FaceId f, RefId t) { Payload p = {0}; p.face = f; p.ref = t; return net_descriptor(n, D_PARTIAL, p); }
static NodeId desc_recipe(Net *n, RefId t) {
    Payload p = {0}; p.ref = t;
    NodeId d = net_descriptor(n, D_HEAD_RECIPE, p);
    Node *x = N(n, d);
    x->head = malloc(sizeof(Head)); require(x->head, "out of memory");
    open_ref(t, x->head);
    x->tag = x->head->is_var ? 0 : x->head->tag;
    return d;
}

/* ------------------------------------------------------------------ */
/* materializing a head (§19)                                            */

static NodeId materialize(Net *n, const Head *h) {
    Payload p = {0}; p.ref = h->owner;
    if (h->is_var) {
        int8_t pol[1] = { +1 };
        p.a = h->var;
        NodeId hd = net_node(n, A_HEAD, 1, pol, p);
        N(n, hd)->tag = 0;
        return hd;
    }
    if (h->tag == T_SYSTEM) {
        /* HEAD_SYSTEM with one negative aux attached to a BRANCH list */
        int8_t pol[2] = { +1, -1 };
        NodeId hd = net_node(n, A_HEAD, 2, pol, p);
        N(n, hd)->tag = T_SYSTEM;
        size_t nb = h->n / 2;
        int8_t polnil[1] = { +1 }, polcons[3] = { +1, -1, -1 }, polbr[3] = { +1, -1, -1 };
        Payload e = {0};
        NodeId tail = net_node(n, A_BRANCH_NIL, 1, polnil, e);
        for (size_t k = nb; k-- > 0;) {
            NodeId br = net_node(n, A_BRANCH, 3, polbr, e);
            net_connect(n, br, 1, desc_face(n, h->f[2 * k].id), 0);
            net_connect(n, br, 2, desc_ref(n, h->f[2 * k + 1].id), 0);
            NodeId cons = net_node(n, A_BRANCH_CONS, 3, polcons, e);
            net_connect(n, cons, 1, br, 0);
            net_connect(n, cons, 2, tail, 0);
            tail = cons;
        }
        net_connect(n, hd, 1, tail, 0);
        return hd;
    }
    int8_t *pol = malloc(h->n + 1); require(pol, "out of memory");
    pol[0] = +1; for (size_t k = 0; k < h->n; k++) pol[k + 1] = -1;
    NodeId hd = net_node(n, A_HEAD, (uint8_t)(h->n + 1), pol, p);
    free(pol);
    N(n, hd)->tag = h->tag;
    for (size_t k = 0; k < h->n; k++) {
        const HField *f = &h->f[k];
        NodeId d;
        if (f->is_binder) {
            if (h->tag == T_COMP && k == 2) d = desc_binder(n, D_PARTIAL_DIM_BINDER, h->owner, f->slot, f->index, 1);
            else d = desc_binder(n, f->sort == S_TERM ? D_TERM_BINDER : D_DIM_BINDER, h->owner, f->slot, f->index, NO_FIELD);
        } else if (f->kind == F_REF) {
            /* partial fields: Glue fibre/equivalence under alpha, glue intro fibre term */
            bool partial = (h->tag == T_GLUE_TYPE && (k == 2 || k == 3)) ||
                           (h->tag == T_GLUE_INTRO && (k == 2 || k == 3 || k == 4)) ||
                           (h->tag == T_UNGLUE && (k == 2 || k == 3));
            d = partial ? desc_partial(n, h->f[1].id, f->id) : desc_ref(n, f->id);
        } else if (f->kind == F_INTERVAL) d = desc_interval(n, f->id);
        else d = desc_face(n, f->id);
        net_connect(n, hd, (uint16_t)(k + 1), d, 0);
    }
    return hd;
}

/* ------------------------------------------------------------------ */
/* evaluation agents                                                     */

typedef struct { Net *net; NodeId pending; } EvalCtx;

static void lock_two(Net *n, NodeId a, NodeId b) {
    if (a == b) { pthread_mutex_lock(&N(n, a)->mu); return; }
    if (a < b) { pthread_mutex_lock(&N(n, a)->mu); pthread_mutex_lock(&N(n, b)->mu); }
    else { pthread_mutex_lock(&N(n, b)->mu); pthread_mutex_lock(&N(n, a)->mu); }
}
static void unlock_two(Net *n, NodeId a, NodeId b) {
    pthread_mutex_unlock(&N(n, a)->mu);
    if (a != b) pthread_mutex_unlock(&N(n, b)->mu);
}

static void flush_pending(Net *n, ActiveVec *pend) {
    if (!pend->len) { vec_free(pend); return; }
    if (n->shared.mu) {
        pthread_mutex_lock(n->shared.mu);
        for (size_t i = 0; i < pend->len; i++) { (*n->shared.outstanding)++; vec_push(&n->active, pend->data[i]); }
        pthread_cond_broadcast(n->shared.cv);
        pthread_mutex_unlock(n->shared.mu);
        vec_free(pend);
        return;
    }
    pthread_mutex_lock(&n->act_mu);
    for (size_t i = 0; i < pend->len; i++) { n->outstanding++; vec_push(&n->active, pend->data[i]); }
    pthread_cond_broadcast(&n->act_cv);
    pthread_mutex_unlock(&n->act_mu);
    vec_free(pend);
}

/* Publication of a result into the net: runs on an evaluation worker. The
 * pending node is replaced by the result descriptor; its single boundary
 * endpoint (the consumer) is locked together with it, in id order, and
 * revalidated after locking. */
static void net_eval_deliver(void *ctx, EvalResult *r) {
    EvalCtx *c = ctx;
    Net *n = c->net;
    NodeId pend = c->pending;
    free(c);
    for (;;) {
        Node *x = N(n, pend);
        pthread_mutex_lock(&x->mu);
        if (!x->live) { pthread_mutex_unlock(&x->mu); return; }   /* consumer released the endpoint */
        Endpoint q = x->peer[0];
        pthread_mutex_unlock(&x->mu);
        if (q.node) lock_two(n, pend, q.node); else pthread_mutex_lock(&x->mu);
        if (!x->live) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); return; }
        if (x->peer[0].node != q.node || x->peer[0].port != q.port) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); count(&n->retries); fine_bump(FC_NET_RETRIES); continue; }
        ActiveVec pending = {0}; tls_pending = &pending;
        Payload p = {0}; p.a = (uint64_t)(uintptr_t)r; p.ref = r->ref;
        NodeId d = net_descriptor(n, r->cls == R_NO_OBSERVATION ? D_STATUS : D_EVAL_RESULT, p);
        if (r->cls == R_NO_OBSERVATION) N(n, d)->p.a = ST_NO_OBSERVATION;
        retire(n, pend);
        if (q.node) net_connect(n, d, 0, q.node, q.port);
        count(&n->rewrites); count(&n->n_eval_deliver);
        tls_pending = NULL;
        if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu);
        flush_pending(n, &pending);
        return;
    }
}

/* ------------------------------------------------------------------ */
/* the rule table                                                        */

static NodeId copy_descriptor(Net *n, const Node *x) {
    NodeId d = net_descriptor(n, x->kind, x->p);
    if (x->head) {
        Node *y = N(n, d);
        y->head = malloc(sizeof(Head)); require(y->head, "out of memory");
        open_ref(x->head->owner, y->head);   /* same owner handle; the recipe is recomputed, not the construction */
        y->tag = x->tag;
    }
    return d;
}

/* Rules snapshot the node records they read: allocating a node may move the
 * node array, so no Node* is held across an allocation. */
static void rule_dup_data(Net *n, NodeId dup, NodeId data) {
    Node xs = *N(n, data); const Node *x = &xs;
    NodeId d1 = copy_descriptor(n, x), d2 = copy_descriptor(n, x);
    Replacement r; rep_init(&r);
    rep_remove(&r, dup); rep_remove(&r, data);
    rep_fresh(&r, dup, 1, d1, 0);
    rep_fresh(&r, dup, 2, d2, 0);
    rep_commit(n, &r);
}

static void rule_erase_data(Net *n, NodeId er, NodeId data) {
    Replacement r; rep_init(&r);
    rep_remove(&r, er); rep_remove(&r, data);
    rep_commit(n, &r);
}

/* duplicate / erase a materialized shell fieldwise with local agents */
static void rule_dup_shell(Net *n, NodeId dup, NodeId sh) {
    Node xs = *N(n, sh); const Node *x = &xs;
    uint8_t np = x->nports;
    int8_t *pol = malloc(np); memcpy(pol, x->polarity, np);
    NodeId s1 = net_node(n, x->kind, np, pol, x->p), s2 = net_node(n, x->kind, np, pol, x->p);
    free(pol);
    N(n, s1)->tag = x->tag; N(n, s2)->tag = x->tag;
    Replacement r; rep_init(&r);
    rep_remove(&r, dup); rep_remove(&r, sh);
    rep_fresh(&r, dup, 1, s1, 0);
    rep_fresh(&r, dup, 2, s2, 0);
    int8_t pdup[3] = { -1, +1, +1 }; Payload e = {0};
    for (uint16_t k = 1; k < np; k++) {
        NodeId d = net_node(n, A_DUP, 3, pdup, e);
        net_connect(n, d, 1, s1, k);
        net_connect(n, d, 2, s2, k);
        rep_fresh(&r, sh, k, d, 0);
    }
    rep_commit(n, &r);
}

static void rule_erase_shell(Net *n, NodeId er, NodeId sh) {
    Node xs = *N(n, sh); const Node *x = &xs;
    Replacement r; rep_init(&r);
    rep_remove(&r, er); rep_remove(&r, sh);
    int8_t per[1] = { -1 }; Payload e = {0};
    for (uint16_t k = 1; k < x->nports; k++) rep_fresh(&r, sh, k, net_node(n, A_ERASE, 1, per, e), 0);
    rep_commit(n, &r);
}

/* §55 operand records in the key interner: [n, (sort,id,type,level,required)*] and [n, (sort,id)*] */
uint64_t net_capture_decls(size_t n, const CaptureDecl *d) {
    Words w; words_init(&w); words_push(&w, 0xCA9); words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, d[k].sort); words_push(&w, d[k].id); words_push(&w, d[k].type); words_push(&w, d[k].level); words_push(&w, d[k].required); }
    uint64_t id = interner_intern(&M.keys, w.w, w.n, NULL); words_free(&w); return id;
}
uint64_t net_scope_args(size_t n, const Val *a) {
    Words w; words_init(&w); words_push(&w, 0xA96); words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, a[k].sort); words_push(&w, a[k].id); }
    uint64_t id = interner_intern(&M.keys, w.w, w.n, NULL); words_free(&w); return id;
}
static size_t capture_decls_get(uint64_t h, CaptureDecl **result) {
    size_t n; const uint64_t *w = interner_get(&M.keys, h, &n); require(n >= 2 && w[0] == 0xCA9, "not a capture telescope");
    size_t m = (size_t)w[1]; require(n >= 2 && m <= (n - 2) / 5 && n == 2 + 5 * m, "malformed capture telescope");
    require(m <= SIZE_MAX / sizeof(CaptureDecl), "capture telescope allocation overflow");
    CaptureDecl *out = m ? malloc(m * sizeof *out) : NULL; *result = out;
    for (size_t k = 0; k < m; k++) { out[k].sort = (Sort)w[2 + 5 * k]; out[k].id = w[3 + 5 * k]; out[k].type = w[4 + 5 * k]; out[k].level = w[5 + 5 * k]; out[k].required = w[6 + 5 * k]; }
    return m;
}
static size_t scope_args_get(uint64_t h, Val **result) {
    size_t n; const uint64_t *w = interner_get(&M.keys, h, &n); require(n >= 2 && w[0] == 0xA96, "not a scope argument list");
    size_t m = (size_t)w[1]; require(n >= 2 && m <= (n - 2) / 2 && n == 2 + 2 * m, "malformed scope argument list");
    require(m <= SIZE_MAX / sizeof(Val), "scope argument allocation overflow");
    Val *out = m ? malloc(m * sizeof *out) : NULL; *result = out;
    for (size_t k = 0; k < m; k++) { out[k].sort = (ValSort)w[2 + 2 * k]; out[k].id = w[3 + 2 * k]; }
    return m;
}
static NodeId desc_scope(Net *n, ScopeId S) { Payload p = {0}; p.a = S; return net_descriptor(n, D_SCOPE, p); }
static NodeId desc_typed_partial(Net *n, RefId body, RefId type, uint64_t level, FaceId guard) { Payload p = {0}; p.ref = body; p.b = type; p.c = level; p.face = guard; return net_descriptor(n, D_TYPED_PARTIAL, p); }

static void rule_op(Net *n, NodeId op, NodeId data) {
    Node os = *N(n, op), ds = *N(n, data);
    const Node *o = &os, *d = &ds;
    NodeKind k = o->kind, dk = d->kind;
    Payload P = o->p, Q = d->p;
    NodeId res = 0;
#define WANT(kind) do { if (dk != (kind)) { res = status_node(n, ST_SORT_MISMATCH, 0, 0); goto out; } } while (0)
    switch (k) {
    case OP_REINDEX_TERM: WANT(D_REF); res = desc_ref(n, reindex(Q.ref, P.a)); break;
    case OP_REINDEX_INTERVAL: WANT(D_INTERVAL); res = desc_interval(n, iv_reindex(Q.a, P.a)); break;
    case OP_REINDEX_FACE: WANT(D_FACE); res = desc_face(n, fc_reindex(Q.face, P.a)); break;
    case OP_COMPOSE_MAP: WANT(D_MAP); res = desc_map(n, compose(P.a, Q.a), 0, 0); break;
    case OP_RESTRICT_MAP: {
        WANT(D_MAP);
        FaceId src = Q.b ? Q.b : fc_true(), tgt = Q.c ? Q.c : fc_true();
        res = desc_map(n, Q.a, fc_meet(src, fc_reindex(P.face, Q.a)), fc_meet(tgt, P.face));
        break;
    }
    case OP_LIFT_TERM: case OP_LIFT_DIMENSION: {
        WANT(D_MAP);
        RefId owner = P.a; BinderSlot slot = (BinderSlot)P.b;
        /* lifting is defined for a raw view's own map; a template view has
         * an environment, not a map: a status, never a raw-origin access */
        if (ref_is_var(owner) || ref_is_tview(owner) || Q.a != ref_map(owner)) { res = status_node(n, ST_INVALID_MAP, 0, 0); break; }
        Binder b = origin_binder(ref_origin(owner), slot);
        if ((k == OP_LIFT_TERM) != (b.sort == S_TERM)) { res = status_node(n, ST_SORT_MISMATCH, 0, 0); break; }
        res = desc_map(n, lifted_map(owner, slot, NULL), Q.b, Q.c);
        break;
    }
    case OP_OPEN: WANT(D_REF); res = desc_recipe(n, Q.ref); break;
    case OP_UNFOLD_GLOBAL:
        WANT(D_REF);
        if (ref_is_var(Q.ref) || ref_is_tview(Q.ref) || origin_tag(ref_origin(Q.ref)) != T_GLOBAL) { res = status_node(n, ST_SORT_MISMATCH, 0, 0); break; }
        res = desc_ref(n, unfold_global(Q.ref));
        break;
    case OP_REINDEX_TERM_BINDER: WANT(D_TERM_BINDER); res = desc_binder(n, D_TERM_BINDER, reindex(Q.a, P.a), (BinderSlot)Q.b, (FieldIndex)Q.c, NO_FIELD); break;
    case OP_REINDEX_DIM_BINDER: WANT(D_DIM_BINDER); res = desc_binder(n, D_DIM_BINDER, reindex(Q.a, P.a), (BinderSlot)Q.b, (FieldIndex)Q.c, NO_FIELD); break;
    case OP_REINDEX_PARTIAL_DIM_BINDER: WANT(D_PARTIAL_DIM_BINDER); res = desc_binder(n, D_PARTIAL_DIM_BINDER, reindex(Q.a, P.a), (BinderSlot)Q.b, (FieldIndex)Q.c, (FieldIndex)Q.d); break;
    case OP_REINDEX_PARTIAL: WANT(D_PARTIAL); res = desc_partial(n, fc_reindex(Q.face, P.a), reindex(Q.ref, P.a)); break;
    case OP_APPLY_TERM_BINDER: WANT(D_TERM_BINDER); res = desc_ref(n, apply_term_binder(Q.a, (BinderSlot)Q.b, (FieldIndex)Q.c, P.ref)); break;
    case OP_APPLY_DIM_BINDER: WANT(D_DIM_BINDER); res = desc_ref(n, apply_dim_binder(Q.a, (BinderSlot)Q.b, (FieldIndex)Q.c, P.a)); break;
    case OP_APPLY_PARTIAL_DIM_BINDER: {
        WANT(D_PARTIAL_DIM_BINDER);
        RefId owner = Q.a;
        DimOpen o = resolve_dim_binder(owner, (BinderSlot)Q.b, (FieldIndex)Q.c);
        MapId at_r = map_single_dim(o.j, P.a);
        /* both body and guard are specialized at r (the guard of a valid tube
         * is independent of the bound dimension, so this leaves it unchanged);
         * the guard is read through the uniform opened head, where the
         * owner's map or template environment is already applied (§55) */
        Head oh; open_ref(owner, &oh);
        require((size_t)Q.d < oh.n && oh.f[Q.d].kind == F_FACE, "APPLY_PARTIAL_DIM_BINDER: guard field");
        FaceId guard = fc_reindex(oh.f[Q.d].id, at_r);
        head_free(&oh);
        res = desc_partial(n, guard, reindex(o.body, at_r));
        break;
    }
    case OP_FORALL_DIMENSION: WANT(D_FACE); res = desc_face(n, fc_forall(P.a, Q.face)); break;
    case OP_PROJECT_FACE: { WANT(D_FACE); size_t m; const uint64_t *S = dimset_get(P.a, &m); res = desc_face(n, fc_project(Q.face, S, m)); break; }
    case OP_FACE_COVERAGE: WANT(D_FACE); res = status_node(n, fc_entails(P.face, Q.face) ? ST_COVERED : ST_NOT_COVERED, 0, 0); break;
    case OP_USE_PARTIAL:
        WANT(D_PARTIAL);
        if (fc_entails(P.face, Q.face)) res = desc_ref(n, Q.ref);
        else res = status_node(n, ST_NOT_COVERED, Q.face, Q.ref);      /* retains the partial payload */
        break;
    case OP_GET_SUPPORT: { WANT(D_REF); Payload p = {0}; p.a = ref_support(Q.ref); res = net_descriptor(n, D_DIMSET, p); break; }
    case OP_REINDEX_HEAD: WANT(D_HEAD_RECIPE); res = desc_recipe(n, reindex(d->head->owner, P.a)); break;
    case OP_MATERIALIZE: WANT(D_HEAD_RECIPE); res = materialize(n, d->head); break;
    case OP_APPLY_TRANSFORM: {
        /* §43: the one replacement — v := reindex(template, σ + slot ↦ a);
         * no evaluation of a, the proof, or v */
        WANT(D_REF);
        RefId body; TermVarId slot;
        require(compiler_template(P.a, (int)P.b, &body, &slot), "APPLY_TRANSFORM of an unknown compiled transform");
        MapBuilder b; mapb_init(&b);
        size_t nt = map_n_terms(P.c), nd = map_n_dims(P.c);
        for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(P.c, k, &x, &im); mapb_term(&b, x, im); }
        for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(P.c, k, &i, &im); mapb_dim(&b, i, im); }
        mapb_term(&b, slot, Q.ref);
        res = desc_ref(n, reindex(body, mapb_finish(&b)));
        count(&n->n_apply); reuse_bump(REUSE_IDENTITY_APPLY);
        { NetTraceEvent ev = { NT_APPLY_TRANSFORM, P.a, (int)P.b, P.c, Q.ref, N(n, res)->p.ref, 0 };
          Endpoint rp = o->peer[1];
          if (rp.node && N(n, rp.node)->kind == A_CONTINUE_REFERENCE) ev.K = N(n, rp.node)->p.a;
          pthread_mutex_lock(&n->trace_mu); vec_push(&n->trace, ev); pthread_mutex_unlock(&n->trace_mu); }
        break;
    }
    /* ---- §55: scope and template agents; each is one finite pure operation ---- */
    case OP_CAPTURE_REF_SCOPE: {
        WANT(D_REF);
        CaptureDecl *d; size_t m = capture_decls_get(P.a, &d);
        Val body = { VS_REF, Q.ref };
        res = desc_scope(n, capture_scope(m, d, body, P.ref, P.c, P.face));     /* P: a = Δ, ref = type, c = level, face = guard */
        free(d);
        break;
    }
    case OP_CAPTURE_FACE_SCOPE: {
        WANT(D_FACE);
        CaptureDecl *d; size_t m = capture_decls_get(P.a, &d);
        Val body = { VS_FACE, Q.face };
        res = desc_scope(n, capture_scope(m, d, body, 0, LEVEL_NONE, fc_true()));
        free(d);
        break;
    }
    case OP_CAPTURE_INTERVAL_SCOPE: {
        WANT(D_INTERVAL);
        CaptureDecl *d; size_t m = capture_decls_get(P.a, &d);
        Val body = { VS_INTERVAL, Q.a };
        res = desc_scope(n, capture_scope(m, d, body, 0, LEVEL_NONE, fc_true()));
        free(d);
        break;
    }
    case OP_REINDEX_SCOPE: WANT(D_SCOPE); res = desc_scope(n, reindex_scope(Q.a, P.a)); break;
    case OP_APPLY_SCOPE: {
        WANT(D_SCOPE);
        Val *args; size_t m = scope_args_get(P.a, &args);
        TypedPartial tp = apply_scope(Q.a, m, args); free(args);
        if (tp.body.sort == VS_REF) res = desc_typed_partial(n, tp.body.id, tp.type, tp.level, tp.guard);
        else if (tp.body.sort == VS_FACE) res = desc_face(n, tp.body.id);
        else res = desc_interval(n, tp.body.id);
        break;
    }
    case OP_FORALL_SCOPE: {
        WANT(D_SCOPE);
        if (scope_arity(Q.a) != 1 || scope_local(Q.a, 0).sort != S_DIM || scope_body(Q.a).sort != VS_FACE) { res = status_node(n, ST_SORT_MISMATCH, 0, 0); break; }
        res = desc_face(n, forall_scope(Q.a));
        break;
    }
    case OP_REINDEX_TEMPLATE_ENV: { WANT(D_TEMPLATE_ENV); Payload p = {0}; p.a = tenv_reindex(Q.a, P.a); res = net_descriptor(n, D_TEMPLATE_ENV, p); break; }
    case OP_INSTANTIATE_TEMPLATE: WANT(D_TEMPLATE_ENV); res = desc_ref(n, tenv_instantiate(P.a, Q.a)); break;
    case OP_REINDEX_TYPED_PARTIAL: WANT(D_TYPED_PARTIAL); res = desc_typed_partial(n, reindex(Q.ref, P.a), Q.b ? reindex(Q.b, P.a) : 0, Q.c, fc_reindex(Q.face, P.a)); break;
    case OP_USE_TYPED_PARTIAL:
        WANT(D_TYPED_PARTIAL);
        if (fc_entails(P.face, Q.face)) res = desc_ref(n, Q.ref);
        else { res = status_node(n, ST_NOT_COVERED, Q.face, Q.ref); N(n, res)->p.b = Q.b; N(n, res)->p.c = Q.c; }   /* retains the typed partial */
        break;
    case OP_TYPED_PARTIAL_TYPE: WANT(D_TYPED_PARTIAL); res = desc_ref(n, Q.b); break;      /* retained as type data, not observed */
    case OP_TYPED_PARTIAL_GUARD: WANT(D_TYPED_PARTIAL); res = desc_face(n, Q.face); break;
    case OP_EVAL: {
        WANT(D_REF);
        /* the result endpoint transfers into the continuation; the request
         * descriptors retire. */
        NodeId pend = net_pending(n);
        EvalCtx *ctx = malloc(sizeof *ctx); require(ctx, "out of memory");
        ctx->net = n; ctx->pending = pend;
        one_result(n, op, data, pend);
        eval_request(Q.ref, P.face, cont_external(net_eval_deliver, ctx, free));
        return;
    }
    default: die("unknown operation");
    }
out:
#undef WANT
    one_result(n, op, data, res);
}

static bool is_shell(NodeKind k) { return k == A_HEAD || k == A_BRANCH_NIL || k == A_BRANCH_CONS || k == A_BRANCH; }

/* apply the rule for an oriented, validated, fully locked active pair */
static bool apply_rule(Net *n, NodeId neg, NodeId pos) {
    Node *ng = N(n, neg), *ps = N(n, pos);
    if (ng->kind == A_ROOT || ps->kind == (NodeKind)0) return false;   /* observation root / pending: no rule */
    if (is_operation(ng->kind)) {
        if (is_descriptor(ps->kind)) { rule_op(n, neg, pos); count(&n->n_op); return true; }
        /* an operation meeting a shell is a sort mismatch */
        Replacement r; rep_init(&r);
        rep_remove(&r, neg);
        rep_fresh(&r, neg, 1, status_node(n, ST_SORT_MISMATCH, 0, 0), 0);
        rep_commit(n, &r);
        int8_t per[1] = { -1 }; Payload e = {0};
        net_connect(n, net_node(n, A_ERASE, 1, per, e), 0, pos, 0);
        count(&n->n_op);
        return true;
    }
    if (ng->kind == A_DUP) {
        if (is_descriptor(ps->kind)) rule_dup_data(n, neg, pos);
        else if (is_shell(ps->kind)) rule_dup_shell(n, neg, pos);
        else return false;
        count(&n->n_dup);
        return true;
    }
    if (ng->kind == A_ERASE) {
        if (is_descriptor(ps->kind)) rule_erase_data(n, neg, pos);
        else if (is_shell(ps->kind)) rule_erase_shell(n, neg, pos);
        else return false;
        count(&n->n_erase);
        return true;
    }
    if (ng->kind == A_CONTINUE_REFERENCE) {
        /* §43 receiver: CONTINUE_REFERENCE(K) -- REF(v)  →  REQ(key(v, face K), FORWARD_RESULT(K)).
         * The shells retire after the parent's suspended evaluation has been
         * transferred to the request's continuation. */
        if (ps->kind != D_REF) return false;
        EntryId K = (EntryId)ng->p.a; RefId v = ps->p.ref;
        Replacement r; rep_init(&r);
        rep_remove(&r, neg); rep_remove(&r, pos);
        rep_commit(n, &r);
        { NetTraceEvent ev = { NT_CONTINUE_REFERENCE, 0, 0, 0, 0, v, K };
          pthread_mutex_lock(&n->trace_mu); vec_push(&n->trace, ev); pthread_mutex_unlock(&n->trace_mu); }
        count(&n->n_continue);          /* counted before the forward publication: a reader woken by the result sees the rule event (ordering race fixed) */
        eval_forward_result(K, v);
        return true;
    }
    return false;
}

static int cmp_nodeid(const void *a, const void *b) { NodeId x = *(const NodeId *)a, y = *(const NodeId *)b; return x < y ? -1 : x > y ? 1 : 0; }

/* One candidate active pair. Returns true when a replacement was committed. */
static bool step(Net *n, Active cand) {
    NodeId a = cand.node;
    for (int attempt = 0; attempt < 64; attempt++) {
        Node *x = N(n, a);
        pthread_mutex_lock(&x->mu);
        if (!x->live || x->gen != cand.gen) { pthread_mutex_unlock(&x->mu); return false; }
        Endpoint q = x->peer[0];
        pthread_mutex_unlock(&x->mu);
        if (!q.node || q.port != 0) return false;
        NodeId b = q.node;
        /* lock the redex owners in id order and validate the pair */
        lock_two(n, a, b);
        Node *y = N(n, b);
        bool valid = x->live && y->live && x->gen == cand.gen && x->peer[0].node == b && x->peer[0].port == 0 && y->peer[0].node == a && y->peer[0].port == 0;
        if (!valid) { unlock_two(n, a, b); if (!x->live || x->gen != cand.gen) return false; count(&n->retries); fine_bump(FC_NET_RETRIES); continue; }
        uint64_t gen_b = y->gen;
        /* collect the surviving boundary: every auxiliary neighbour of a and b */
        NodeId set[64]; Endpoint exp[64]; uint64_t expgen[64]; size_t ns = 0;
        set[ns++] = a; set[ns++] = b;
        Node *two[2] = { x, y };
        for (int t = 0; t < 2; t++)
            for (uint16_t k = 1; k < two[t]->nports; k++) {
                Endpoint e = two[t]->peer[k];
                if (!e.node || e.node == a || e.node == b) continue;
                require(ns < 64, "redex boundary too large");
                set[ns] = e.node; exp[ns] = e; expgen[ns] = __atomic_load_n(&N(n, e.node)->gen, __ATOMIC_ACQUIRE); ns++;
            }
        unlock_two(n, a, b);
        /* lock the whole affected set in a consistent total order */
        NodeId sorted[64]; memcpy(sorted, set, ns * sizeof(NodeId));
        qsort(sorted, ns, sizeof(NodeId), cmp_nodeid);
        size_t nu = 0;
        for (size_t i = 0; i < ns; i++) if (nu == 0 || sorted[nu - 1] != sorted[i]) sorted[nu++] = sorted[i];
        for (size_t i = 0; i < nu; i++) pthread_mutex_lock(&N(n, sorted[i])->mu);
        /* revalidate the redex and its boundary */
        bool ok = x->live && y->live && x->gen == cand.gen && y->gen == gen_b && x->peer[0].node == b && x->peer[0].port == 0 && y->peer[0].node == a && y->peer[0].port == 0;
        for (size_t i = 2; i < ns && ok; i++) {
            Node *z = N(n, set[i]);
            if (!z->live || z->gen != expgen[i]) ok = false;
            else { NodeId back = z->peer[exp[i].port].node; if (back != a && back != b) ok = false; }   /* the boundary port still faces the redex */
        }
        /* and that a's and b's aux peers are still the recorded ones */
        if (ok) {
            size_t idx = 2;
            for (int t = 0; t < 2 && ok; t++)
                for (uint16_t k = 1; k < two[t]->nports && ok; k++) {
                    Endpoint e = two[t]->peer[k];
                    if (!e.node || e.node == a || e.node == b) { if (e.node) continue; else continue; }
                    if (idx >= ns || e.node != exp[idx].node || e.port != exp[idx].port) ok = false;
                    idx++;
                }
            if (ok && idx != ns) ok = false;
        }
        if (!ok) {
            for (size_t i = 0; i < nu; i++) pthread_mutex_unlock(&N(n, sorted[i])->mu);
            if (!x->live || x->gen != cand.gen) return false;
            count(&n->retries); fine_bump(FC_NET_RETRIES);
            continue;
        }
        /* orient: negative principal (agent) vs positive principal (data/shell) */
        NodeId neg = x->polarity[0] < 0 ? a : b, pos = x->polarity[0] < 0 ? b : a;
        ActiveVec pending = {0}; tls_pending = &pending;
        bool did = apply_rule(n, neg, pos);
        if (did) count(&n->rewrites);
        tls_pending = NULL;
        for (size_t i = 0; i < nu; i++) pthread_mutex_unlock(&N(n, sorted[i])->mu);
        flush_pending(n, &pending);
        return did;
    }
    return false;
}

bool net_step_pair(Net *n, Active a) { return step(n, a); }
bool net_pop_pair_locked(Net *n, Active *out) {
    if (!n->active.len) return false;
    size_t pick = n->active.len - 1;
    if (n->policy == 1) pick = 0;
    else if (n->policy == 2) { n->rng ^= n->rng << 13; n->rng ^= n->rng >> 7; n->rng ^= n->rng << 17; pick = (size_t)(n->rng % n->active.len); }
    *out = n->active.data[pick];
    n->active.data[pick] = n->active.data[n->active.len - 1];
    n->active.len--;
    return true;
}

static bool pop_active_locked(Net *n, Active *out) {
    if (!n->active.len) return false;
    size_t pick = n->active.len - 1;
    if (n->policy == 1) pick = 0;
    else if (n->policy == 2) { n->rng ^= n->rng << 13; n->rng ^= n->rng >> 7; n->rng ^= n->rng << 17; pick = (size_t)(n->rng % n->active.len); }
    *out = n->active.data[pick];
    n->active.data[pick] = n->active.data[n->active.len - 1];
    n->active.len--;
    return true;
}

static void *net_worker_main(void *arg) {
    Net *n = arg;
    pthread_mutex_lock(&n->act_mu);
    for (;;) {
        Active it;
        while (!n->stop && !pop_active_locked(n, &it)) pthread_cond_wait(&n->act_cv, &n->act_mu);
        if (n->stop) break;
        pthread_mutex_unlock(&n->act_mu);
        step(n, it);                     /* new active pairs are flushed (enqueued) inside step */
        net_finish_job(n);
        pthread_mutex_lock(&n->act_mu);
    }
    pthread_mutex_unlock(&n->act_mu);
    return NULL;
}

size_t net_run(Net *n) {
    if (n->nworkers) {
        pthread_mutex_lock(&n->act_mu);
        size_t before = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        while (n->outstanding > 0) pthread_cond_wait(&n->idle_cv, &n->act_mu);
        size_t after = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        pthread_mutex_unlock(&n->act_mu);
        return after - before;
    }
    size_t c = 0;
    for (;;) {
        Active it;
        pthread_mutex_lock(&n->act_mu);
        bool got = pop_active_locked(n, &it);
        pthread_mutex_unlock(&n->act_mu);
        if (!got) break;
        if (step(n, it)) c++;
        net_finish_job(n);
    }
    return c;
}

/* Drive both schedulers to joint quiescence: a round in which neither the
 * net nor the evaluator performed any work, each having drained its own
 * ready multiset with all its workers idle. */
size_t net_run_with_eval(Net *n) {
    size_t total = 0;
    for (;;) {
        size_t before = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        size_t c = net_run(n);
        size_t e = eval_run();
        size_t after = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        total += c;
        if (c == 0 && e == 0 && after == before) break;
    }
    return total;
}

bool net_root_read(const Net *n, NodeId root, NodeKind *kind, Payload *p) {
    const Node *x = N(n, root);
    if (!x->live || x->kind != A_ROOT) return false;
    Endpoint q = x->peer[0];
    if (!q.node) return false;
    const Node *y = N(n, q.node);
    if (kind) *kind = y->kind;
    if (p) *p = y->p;
    return true;
}

/* ------------------------------------------------------------------ */
/* tests                                                                 */

static int tp = 0, tf = 0;
#define TCHECK(c, msg) do { if (c) tp++; else { tf++; printf("  FAIL (net): %s\n", msg); } } while (0)

static NodeId mk_root(Net *n) { int8_t pol[1] = { -1 }; Payload e = {0}; return net_node(n, A_ROOT, 1, pol, e); }

/* wire op.result → root, op.principal → data.principal, run, read root */
static bool run_op(Net *n, NodeKind opk, Payload P, NodeKind dk, Payload Q, NodeKind *outk, Payload *outp) {
    NodeId op = net_operation(n, opk, P), d = net_descriptor(n, dk, Q), root = mk_root(n);
    net_connect(n, op, 1, root, 0);
    net_connect(n, op, 0, d, 0);
    net_run_with_eval(n);
    return net_root_read(n, root, outk, outp);
}

void test_net(void) {
    printf("== §19–20 scope agents and local replacement\n");
    Net net; net_init(&net);
    if (getenv("CUBICAL_WORKERS")) net_set_workers(&net, (size_t)atoi(getenv("CUBICAL_WORKERS")));
    RefId U = mk_universe(0);
    RefId A = ref_var(declare_term(U, fc_true()));
    TermVarId x = declare_term(A, fc_true());
    RefId a = ref_var(declare_term(A, fc_true()));
    RefId id = mk_lam_lv(0, x, A, ref_var(x));
    NodeKind ok; Payload op, P = {0}, Q = {0};

    /* REINDEX_TERM */
    P.a = map_single_term(x, a); Q.ref = ref_var(x);
    TCHECK(run_op(&net, OP_REINDEX_TERM, P, D_REF, Q, &ok, &op) && ok == D_REF && op.ref == a, "REINDEX_TERM");
    /* sort mismatch is a status, not a value */
    Q.a = iv_one();
    TCHECK(run_op(&net, OP_REINDEX_TERM, P, D_INTERVAL, Q, &ok, &op) && ok == D_STATUS && op.a == ST_SORT_MISMATCH, "sort mismatch → status");
    /* OPEN then APPLY_TERM_BINDER through descriptors */
    Q = (Payload){0}; Q.ref = id; P = (Payload){0};
    TCHECK(run_op(&net, OP_OPEN, P, D_REF, Q, &ok, &op) && ok == D_HEAD_RECIPE, "OPEN gives a head recipe");
    P.ref = a; Q = (Payload){0}; Q.a = id; Q.b = 0; Q.c = 1;
    TCHECK(run_op(&net, OP_APPLY_TERM_BINDER, P, D_TERM_BINDER, Q, &ok, &op) && ok == D_REF && op.ref == a, "APPLY_TERM_BINDER");
    /* LIFT_TERM requires the owner's own map */
    P = (Payload){0}; P.a = id; P.b = 0; Q = (Payload){0}; Q.a = map_single_term(x, a);
    TCHECK(run_op(&net, OP_LIFT_TERM, P, D_MAP, Q, &ok, &op) && ok == D_STATUS && op.a == ST_INVALID_MAP, "LIFT_TERM with an unrelated map is a validation error");
    Q.a = map_identity();
    TCHECK(run_op(&net, OP_LIFT_TERM, P, D_MAP, Q, &ok, &op) && ok == D_MAP && map_n_terms(op.a) == 1, "LIFT_TERM with the owner's map gives the lifted map");
    /* faces */
    DimVarId i = declare_dim(), j = declare_dim();
    P = (Payload){0}; P.a = i; Q = (Payload){0}; Q.face = fc_join(fc_lit(i, 0), fc_lit(j, 0));
    TCHECK(run_op(&net, OP_FORALL_DIMENSION, P, D_FACE, Q, &ok, &op) && op.face == fc_lit(j, 0), "FORALL_DIMENSION");
    uint64_t Sj[1] = { j }; P.a = dimset_make(Sj, 1); Q.face = fc_meet(fc_lit(i, 0), fc_lit(j, 0));
    TCHECK(run_op(&net, OP_PROJECT_FACE, P, D_FACE, Q, &ok, &op) && op.face == fc_lit(j, 0), "PROJECT_FACE");
    P = (Payload){0}; P.face = fc_lit(i, 0); Q.face = fc_join(fc_lit(i, 0), fc_lit(j, 0));
    TCHECK(run_op(&net, OP_FACE_COVERAGE, P, D_FACE, Q, &ok, &op) && ok == D_STATUS && op.a == ST_COVERED, "FACE_COVERAGE covered");
    P.face = fc_true(); Q = (Payload){0}; Q.face = fc_lit(i, 0); Q.ref = a;
    TCHECK(run_op(&net, OP_USE_PARTIAL, P, D_PARTIAL, Q, &ok, &op) && ok == D_STATUS && op.a == ST_NOT_COVERED && op.ref == a, "USE_PARTIAL not covered retains the partial payload");
    P.face = fc_lit(i, 0);
    TCHECK(run_op(&net, OP_USE_PARTIAL, P, D_PARTIAL, Q, &ok, &op) && ok == D_REF && op.ref == a, "USE_PARTIAL covered yields the term");
    /* support */
    RefId pth = ref_var(declare_term(mk_path_const(0, A, a, a), fc_true()));
    RefId at_i = mk_papp_lv(0, j, A, a, a, pth, iv_var(i));
    P = (Payload){0}; Q = (Payload){0}; Q.ref = at_i;
    TCHECK(run_op(&net, OP_GET_SUPPORT, P, D_REF, Q, &ok, &op) && ok == D_DIMSET && dimset_contains(op.a, i) && !dimset_contains(op.a, j), "GET_SUPPORT");

    /* §55 scope / template agents: capture, reindex, apply, forall; template
     * environments; typed partials. Each is one pure replacement that agrees
     * with the host operation. */
    { CaptureDecl dl[1] = { { S_DIM, i, 0, LEVEL_NONE, fc_true() } };
      size_t orgS = interner_count(&M.origins);
      P = (Payload){0}; P.a = net_capture_decls(1, dl); P.ref = A; P.c = 0; P.face = fc_true();
      Q = (Payload){0}; Q.ref = at_i;
      TCHECK(run_op(&net, OP_CAPTURE_REF_SCOPE, P, D_REF, Q, &ok, &op) && ok == D_SCOPE, "CAPTURE_REF_SCOPE gives a scope");
      ScopeId S = op.a;
      Val body = { VS_REF, at_i };
      TCHECK(S == capture_scope(1, dl, body, A, 0, fc_true()), "the captured scope is the host capture");
      Q = (Payload){0}; Q.a = S; P = (Payload){0}; P.a = map_single_term(x, a);
      TCHECK(run_op(&net, OP_REINDEX_SCOPE, P, D_SCOPE, Q, &ok, &op) && ok == D_SCOPE && op.a == reindex_scope(S, map_single_term(x, a)), "REINDEX_SCOPE");
      Val args[1] = { { VS_INTERVAL, iv_one() } };
      P = (Payload){0}; P.a = net_scope_args(1, args);
      TCHECK(run_op(&net, OP_APPLY_SCOPE, P, D_SCOPE, Q, &ok, &op) && ok == D_TYPED_PARTIAL && op.ref == reindex_dim(at_i, i, iv_one()) && op.b == A, "APPLY_SCOPE gives the typed partial at the argument");
      Payload tpart = op;
      P = (Payload){0}; P.face = fc_true();
      TCHECK(run_op(&net, OP_USE_TYPED_PARTIAL, P, D_TYPED_PARTIAL, tpart, &ok, &op) && ok == D_REF && op.ref == tpart.ref, "USE_TYPED_PARTIAL under a covering face");
      TCHECK(run_op(&net, OP_TYPED_PARTIAL_TYPE, P, D_TYPED_PARTIAL, tpart, &ok, &op) && ok == D_REF && op.ref == A, "TYPED_PARTIAL_TYPE retains the type");
      TCHECK(run_op(&net, OP_TYPED_PARTIAL_GUARD, P, D_TYPED_PARTIAL, tpart, &ok, &op) && ok == D_FACE && op.face == fc_true(), "TYPED_PARTIAL_GUARD");
      /* a face scope and its ∀ */
      P = (Payload){0}; P.a = net_capture_decls(1, dl); Q = (Payload){0}; Q.face = fc_join(fc_lit(i, 0), fc_lit(j, 0));
      TCHECK(run_op(&net, OP_CAPTURE_FACE_SCOPE, P, D_FACE, Q, &ok, &op) && ok == D_SCOPE, "CAPTURE_FACE_SCOPE");
      Q = (Payload){0}; Q.a = op.a; P = (Payload){0};
      TCHECK(run_op(&net, OP_FORALL_SCOPE, P, D_SCOPE, Q, &ok, &op) && ok == D_FACE && op.face == fc_lit(j, 0), "FORALL_SCOPE agrees with FORALL_DIMENSION");
      /* template environments: reindex then instantiate equals the reindexed view */
      RefId rf = mk_refl(0, A, ref_var(x));
      Q = (Payload){0}; Q.a = tenv_of(rf); P = (Payload){0}; P.a = map_single_term(x, a);
      TCHECK(run_op(&net, OP_REINDEX_TEMPLATE_ENV, P, D_TEMPLATE_ENV, Q, &ok, &op) && ok == D_TEMPLATE_ENV, "REINDEX_TEMPLATE_ENV");
      Q = (Payload){0}; Q.a = op.a; P = (Payload){0}; P.a = tnode_of(rf);
      TCHECK(run_op(&net, OP_INSTANTIATE_TEMPLATE, P, D_TEMPLATE_ENV, Q, &ok, &op) && ok == D_REF && op.ref == mk_refl(0, A, a), "INSTANTIATE_TEMPLATE of the reindexed environment is the specialized view");
      TCHECK(interner_count(&M.origins) == orgS, "no scope or template rule allocated an origin"); }

    /* duplication copies handles: no new interned records */
    size_t refs0 = interner_count(&M.refs), org0 = interner_count(&M.origins);
    int8_t pdup[3] = { -1, +1, +1 }; Payload e = {0};
    NodeId dup = net_node(&net, A_DUP, 3, pdup, e);
    NodeId r1 = mk_root(&net), r2 = mk_root(&net);
    net_connect(&net, dup, 1, r1, 0); net_connect(&net, dup, 2, r2, 0);
    Q = (Payload){0}; Q.ref = id;
    net_connect(&net, dup, 0, net_descriptor(&net, D_REF, Q), 0);
    net_run(&net);
    Payload p1, p2;
    TCHECK(net_root_read(&net, r1, &ok, &p1) && net_root_read(&net, r2, NULL, &p2) && ok == D_REF && p1.ref == id && p2.ref == id, "duplicated descriptors share the payload handle");
    TCHECK(interner_count(&M.refs) == refs0 && interner_count(&M.origins) == org0, "duplication allocates no origin, body or reference");
    /* erasure retires the descriptor */
    int8_t per[1] = { -1 };
    NodeId er = net_node(&net, A_ERASE, 1, per, e);
    NodeId dd = net_descriptor(&net, D_REF, Q);
    net_connect(&net, er, 0, dd, 0);
    net_run(&net);
    TCHECK(!net_is_live(&net, dd) && !net_is_live(&net, er), "erasure retires descriptor and eraser");

    /* materialize a system head into BRANCH_CONS / BRANCH wiring */
    FaceId fs[2] = { fc_lit(i, 0), fc_lit(i, 1) }; RefId ts[2] = { a, a };
    RefId sys = mk_system(2, fs, ts);
    NodeId recipe = desc_recipe(&net, sys);
    NodeId mat = net_operation(&net, OP_MATERIALIZE, e), root = mk_root(&net);
    net_connect(&net, mat, 1, root, 0); net_connect(&net, mat, 0, recipe, 0);
    net_run(&net);
    Endpoint h = net_peer(&net, root, 0);
    bool shape = net_is_live(&net, h.node) && net_node_ptr(&net, h.node)->kind == A_HEAD && net_node_ptr(&net, h.node)->tag == T_SYSTEM;
    if (shape) {
        Endpoint l = net_peer(&net, h.node, 1);
        shape = net_node_ptr(&net, l.node)->kind == A_BRANCH_CONS;
        Endpoint br = net_peer(&net, l.node, 1);
        shape = shape && net_node_ptr(&net, br.node)->kind == A_BRANCH && net_node_ptr(&net, net_peer(&net, br.node, 1).node)->kind == D_FACE && net_node_ptr(&net, net_peer(&net, br.node, 2).node)->kind == D_REF;
        Endpoint l2 = net_peer(&net, l.node, 2);
        shape = shape && net_node_ptr(&net, l2.node)->kind == A_BRANCH_CONS && net_node_ptr(&net, net_peer(&net, l2.node, 2).node)->kind == A_BRANCH_NIL;
    }
    TCHECK(shape, "SYSTEM materializes as HEAD → CONS(BRANCH(FACE,REF), CONS(BRANCH, NIL))");
    /* duplicate the shell fieldwise, then erase one copy */
    refs0 = interner_count(&M.refs); org0 = interner_count(&M.origins);
    NodeId dup2 = net_node(&net, A_DUP, 3, pdup, e);
    NodeId ra = mk_root(&net), rb = mk_root(&net);
    net_connect(&net, dup2, 1, ra, 0); net_connect(&net, dup2, 2, rb, 0);
    /* detach root from head, attach dup */
    net_disconnect(&net, root, 0);
    net_connect(&net, dup2, 0, h.node, 0);
    size_t live_before = 0; for (size_t k = 1; k <= net_node_count(&net); k++) if (net_is_live(&net, (NodeId)k)) live_before++;
    net_run(&net);
    Endpoint ha = net_peer(&net, ra, 0), hb = net_peer(&net, rb, 0);
    TCHECK(net_is_live(&net, ha.node) && net_is_live(&net, hb.node) && net_node_ptr(&net, ha.node)->kind == A_HEAD && net_node_ptr(&net, hb.node)->kind == A_HEAD && ha.node != hb.node, "shell duplication yields two shells");
    TCHECK(interner_count(&M.refs) == refs0 && interner_count(&M.origins) == org0, "shell duplication still allocates nothing in the tables");
    NodeId er2 = net_node(&net, A_ERASE, 1, per, e);
    net_disconnect(&net, rb, 0);
    net_connect(&net, er2, 0, hb.node, 0);
    net_run(&net);
    size_t live_after = 0; for (size_t k = 1; k <= net_node_count(&net); k++) if (net_is_live(&net, (NodeId)k)) live_after++;
    TCHECK(!net_is_live(&net, hb.node) && live_after < live_before + 20, "erasing a shell retires it and its fields");
    /* every live port is either free or connected to a live node of opposite polarity */
    bool wiring_ok = true;
    for (size_t k = 1; k <= net_node_count(&net); k++) {
        Node *nd = net_node_ptr(&net, (NodeId)k);
        if (!nd->live) continue;
        for (uint16_t q = 0; q < nd->nports; q++) {
            Endpoint pe = nd->peer[q];
            if (!pe.node) continue;
            Node *o = net_node_ptr(&net, pe.node);
            if (!o->live || o->peer[pe.port].node != k || o->peer[pe.port].port != q || o->polarity[pe.port] + nd->polarity[q] != 0) wiring_ok = false;
        }
    }
    TCHECK(wiring_ok, "all surviving wiring is symmetric, live and polarity-correct");

    /* EVAL agents: two requests for one key share one evaluation task */
    size_t tasks0 = eval_task_count();
    RefId t = mk_app(id, mk_pair(a, a));
    NodeId e1 = net_operation(&net, OP_EVAL, (Payload){ .face = fc_true() }), e2 = net_operation(&net, OP_EVAL, (Payload){ .face = fc_lit(i, 0) });
    NodeId q1 = mk_root(&net), q2 = mk_root(&net);
    net_connect(&net, e1, 1, q1, 0); net_connect(&net, e2, 1, q2, 0);
    Q = (Payload){0}; Q.ref = t;
    net_connect(&net, e1, 0, net_descriptor(&net, D_REF, Q), 0);
    net_connect(&net, e2, 0, net_descriptor(&net, D_REF, Q), 0);
    net_run_with_eval(&net);
    Payload o1, o2; NodeKind k1, k2;
    bool got = net_root_read(&net, q1, &k1, &o1) && net_root_read(&net, q2, &k2, &o2);
    TCHECK(got && k1 == D_EVAL_RESULT && k2 == D_EVAL_RESULT && o1.a == o2.a && ((EvalResult *)(uintptr_t)o1.a)->cls == R_INTRODUCTION, "both EVAL agents receive the same result payload");
    (void)tasks0;
    TCHECK(eval_entry_lookup(t, fc_true()) == eval_entry_lookup(t, fc_lit(i, 0)) && eval_entry_runs(eval_entry_lookup(t, fc_true())) == 1, "one evaluation task for the shared key");
    /* false face: explicit host control result */
    NodeId e3 = net_operation(&net, OP_EVAL, (Payload){ .face = fc_false() }), q3 = mk_root(&net);
    net_connect(&net, e3, 1, q3, 0); net_connect(&net, e3, 0, net_descriptor(&net, D_REF, Q), 0);
    net_run_with_eval(&net);
    TCHECK(net_root_read(&net, q3, &k1, &o1) && k1 == D_STATUS && o1.a == ST_NO_OBSERVATION, "EVAL on the false face emits a no-observation status, not a term");

    printf("  net: %zu rewrites\n", net.rewrites);
    net_free(&net);
    printf("  %d net checks passed, %d failed\n", tp, tf);
    if (tf) exit(1);
}

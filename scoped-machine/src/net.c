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

#include "xcount.h"
_Static_assert(sizeof(size_t) == sizeof(uint64_t), "net counts: a word is the low digit");

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
        if (x->peer[0].node != q.node || x->peer[0].port != q.port) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); xc_add2((uint64_t *)&n->retries, &n->retries_cx, 1); fine_bump(FC_NET_RETRIES); continue; }
        ActiveVec pending = {0}; tls_pending = &pending;
        Payload p = {0}; p.a = (uint64_t)(uintptr_t)r; p.ref = r->ref;
        NodeId d = net_descriptor(n, r->cls == R_NO_OBSERVATION ? D_STATUS : D_EVAL_RESULT, p);
        if (r->cls == R_NO_OBSERVATION) N(n, d)->p.a = ST_NO_OBSERVATION;
        retire(n, pend);
        if (q.node) net_connect(n, d, 0, q.node, q.port);
        xc_add2((uint64_t *)&n->rewrites, &n->rewrites_cx, 1); xc_add2((uint64_t *)&n->n_eval_deliver, &n->n_eval_deliver_cx, 1);
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

/* §94 lowering: an operation rule's kernel work (reindex, compose, face
 * operations, binder application, scope/template operations, opening a head)
 * is computed into an OpSpec from snapshots of the two nodes BEFORE the
 * redex and its boundary are locked; under the locks the commit only creates
 * the result node and rewires (a fixed amount of net work). A spec computed
 * for a pair whose nodes changed meanwhile is discarded with the retry (its
 * values are pure, interned results). */
static __thread RefId tls_eval_ref; static __thread FaceId tls_eval_face; static __thread void *tls_eval_ctx;   /* an EVAL rule's deferred request */
enum { SP_DESC = 1, SP_STATUS, SP_RECIPE, SP_MATERIALIZE, SP_APPLY, SP_EVAL };
typedef struct OpSpec { int kind; NodeKind dk; Payload p; Head *head; uint64_t ap_id; int ap_dir; MapId ap_map; RefId ap_arg; RefId ev_ref; FaceId ev_face; } OpSpec;
static void sp_desc(OpSpec *s, NodeKind k, Payload p) { s->kind = SP_DESC; s->dk = k; s->p = p; }
static void sp_status(OpSpec *s, uint64_t code, FaceId face, RefId ref) { Payload p = {0}; p.a = code; p.face = face; p.ref = ref; s->kind = SP_STATUS; s->dk = D_STATUS; s->p = p; }
static void sp_ref(OpSpec *s, RefId t) { Payload p = {0}; p.ref = t; sp_desc(s, D_REF, p); }
static void sp_face(OpSpec *s, FaceId f) { Payload p = {0}; p.face = f; sp_desc(s, D_FACE, p); }
static void sp_interval(OpSpec *s, IntervalId r) { Payload p = {0}; p.a = r; sp_desc(s, D_INTERVAL, p); }
static void sp_map(OpSpec *s, MapId m, FaceId src, FaceId tgt) { Payload p = {0}; p.a = m; p.b = src; p.c = tgt; sp_desc(s, D_MAP, p); }
static void sp_binder(OpSpec *s, NodeKind kind, RefId owner, BinderSlot slot, FieldIndex field, FieldIndex guard) { Payload p = {0}; p.a = owner; p.b = slot; p.c = field; p.d = guard; sp_desc(s, kind, p); }
static void sp_partial(OpSpec *s, FaceId f, RefId t) { Payload p = {0}; p.face = f; p.ref = t; sp_desc(s, D_PARTIAL, p); }
static void sp_scope(OpSpec *s, ScopeId S) { Payload p = {0}; p.a = S; sp_desc(s, D_SCOPE, p); }
static void sp_typed_partial(OpSpec *s, RefId body, RefId type, uint64_t level, FaceId guard) { Payload p = {0}; p.ref = body; p.b = type; p.c = level; p.face = guard; sp_desc(s, D_TYPED_PARTIAL, p); }
__attribute__((unused)) static void sp_recipe(OpSpec *s, RefId t) {
    Payload p = {0}; p.ref = t; s->kind = SP_RECIPE; s->dk = D_HEAD_RECIPE; s->p = p;
    s->head = malloc(sizeof(Head)); require(s->head, "out of memory"); open_ref(t, s->head);   /* opened before the locks */
}
static void spec_discard(OpSpec *s) { if (s->head) { head_free(s->head); free(s->head); s->head = NULL; } }
/* the operation rule's kernel work: a frame family (kframe.h), computed
 * outside every node lock; every kernel procedure it uses is a resume point */
#define op_compute_PARAMS(X) X(const Node *, o) X(const Node *, d) X(OpSpec *, out)
KF_DECL_DROP(op_compute, void, op_compute_PARAMS, op_compute_drop,
    NodeKind k, dk; Payload P, Q; OpSpec sp; RefId r1, r2; FaceId f1, f2, f3; IntervalId i1; MapId m1; bool b1;
    Head *rh; Head oh; DimOpen o2; MapBuilder mb; CaptureDecl *cd; Val *args; size_t m, mk, mt, md; TypedPartial tp; ScopeId sc; uint64_t u1; TermVarId slot;)
static void op_compute_drop(op_compute_F *F) {
    spec_discard(&F->sp);
    if (F->rh) { head_free(F->rh); free(F->rh); F->rh = NULL; }
    head_free(&F->oh); words_free(&F->mb.t); words_free(&F->mb.d);
    free(F->cd); F->cd = NULL; free(F->args); F->args = NULL;
}
/* a head recipe opened before the locks: the opened head moves into the spec */
#define SP_RECIPE_F(t) do { F->rh = malloc(sizeof(Head)); require(F->rh, "out of memory"); memset(F->rh, 0, sizeof(Head)); \
        KF_CALL(open_ref, NULL, (t), F->rh); { Payload p_ = {0}; p_.ref = (t); F->sp.kind = SP_RECIPE; F->sp.dk = D_HEAD_RECIPE; F->sp.p = p_; F->sp.head = F->rh; F->rh = NULL; } } while (0)
KF_STEP(op_compute) {
    KF_BEGIN(op_compute);
    F->k = F->o->kind; F->dk = F->d->kind;
    F->P = F->o->p; F->Q = F->d->p;
    memset(&F->sp, 0, sizeof F->sp);
#define WANT(kind) do { if (F->dk != (kind)) { sp_status(&F->sp, ST_SORT_MISMATCH, 0, 0); goto out; } } while (0)
    switch (F->k) {
    case OP_REINDEX_TERM: WANT(D_REF); KF_CALL(reindex, &F->r1, F->Q.ref, F->P.a); sp_ref(&F->sp, F->r1); break;
    case OP_REINDEX_INTERVAL: WANT(D_INTERVAL); KF_CALL(iv_reindex, &F->i1, F->Q.a, F->P.a); sp_interval(&F->sp, F->i1); break;
    case OP_REINDEX_FACE: WANT(D_FACE); KF_CALL(fc_reindex, &F->f1, F->Q.face, F->P.a); sp_face(&F->sp, F->f1); break;
    case OP_COMPOSE_MAP: WANT(D_MAP); KF_CALL(compose, &F->m1, F->P.a, F->Q.a); sp_map(&F->sp, F->m1, 0, 0); break;
    case OP_RESTRICT_MAP: {
        WANT(D_MAP);
        if (F->Q.b) F->f1 = F->Q.b; else KF_CALL0(fc_true, &F->f1);
        if (F->Q.c) F->f2 = F->Q.c; else KF_CALL0(fc_true, &F->f2);
        KF_CALL(fc_reindex, &F->f3, F->P.face, F->Q.a);
        KF_CALL(fc_meet, &F->f1, F->f1, F->f3);
        KF_CALL(fc_meet, &F->f2, F->f2, F->P.face);
        sp_map(&F->sp, F->Q.a, F->f1, F->f2);
        break;
    }
    case OP_LIFT_TERM: case OP_LIFT_DIMENSION: {
        WANT(D_MAP);
        /* lifting is defined for a raw view's own map; a template view has
         * an environment, not a map: a status, never a raw-origin access */
        { RefId owner = F->P.a; BinderSlot slot = (BinderSlot)F->P.b;
          if (ref_is_var(owner) || ref_is_tview(owner) || F->Q.a != ref_map(owner)) { sp_status(&F->sp, ST_INVALID_MAP, 0, 0); break; }
          Binder b = origin_binder(ref_origin(owner), slot);
          if ((F->k == OP_LIFT_TERM) != (b.sort == S_TERM)) { sp_status(&F->sp, ST_SORT_MISMATCH, 0, 0); break; } }
        KF_CALL(lifted_map, &F->m1, F->P.a, (BinderSlot)F->P.b, NULL);
        sp_map(&F->sp, F->m1, F->Q.b, F->Q.c);
        break;
    }
    case OP_OPEN: WANT(D_REF); SP_RECIPE_F(F->Q.ref); break;
    case OP_UNFOLD_GLOBAL:
        WANT(D_REF);
        if (ref_is_var(F->Q.ref) || ref_is_tview(F->Q.ref) || origin_tag(ref_origin(F->Q.ref)) != T_GLOBAL) { sp_status(&F->sp, ST_SORT_MISMATCH, 0, 0); break; }
        KF_CALL(unfold_global, &F->r1, F->Q.ref); sp_ref(&F->sp, F->r1);
        break;
    case OP_REINDEX_TERM_BINDER: WANT(D_TERM_BINDER); KF_CALL(reindex, &F->r1, F->Q.a, F->P.a); sp_binder(&F->sp, D_TERM_BINDER, F->r1, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c, NO_FIELD); break;
    case OP_REINDEX_DIM_BINDER: WANT(D_DIM_BINDER); KF_CALL(reindex, &F->r1, F->Q.a, F->P.a); sp_binder(&F->sp, D_DIM_BINDER, F->r1, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c, NO_FIELD); break;
    case OP_REINDEX_PARTIAL_DIM_BINDER: WANT(D_PARTIAL_DIM_BINDER); KF_CALL(reindex, &F->r1, F->Q.a, F->P.a); sp_binder(&F->sp, D_PARTIAL_DIM_BINDER, F->r1, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c, (FieldIndex)F->Q.d); break;
    case OP_REINDEX_PARTIAL: WANT(D_PARTIAL); KF_CALL(fc_reindex, &F->f1, F->Q.face, F->P.a); KF_CALL(reindex, &F->r1, F->Q.ref, F->P.a); sp_partial(&F->sp, F->f1, F->r1); break;
    case OP_APPLY_TERM_BINDER: WANT(D_TERM_BINDER); KF_CALL(apply_term_binder, &F->r1, F->Q.a, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c, F->P.ref); sp_ref(&F->sp, F->r1); break;
    case OP_APPLY_DIM_BINDER: WANT(D_DIM_BINDER); KF_CALL(apply_dim_binder, &F->r1, F->Q.a, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c, F->P.a); sp_ref(&F->sp, F->r1); break;
    case OP_APPLY_PARTIAL_DIM_BINDER: {
        WANT(D_PARTIAL_DIM_BINDER);
        KF_CALL(resolve_dim_binder, &F->o2, F->Q.a, (BinderSlot)F->Q.b, (FieldIndex)F->Q.c);
        KF_CALL(map_single_dim, &F->m1, F->o2.j, F->P.a);
        /* both body and guard are specialized at r (the guard of a valid tube
         * is independent of the bound dimension, so this leaves it unchanged);
         * the guard is read through the uniform opened head, where the
         * owner's map or template environment is already applied (§55) */
        KF_CALL(open_ref, NULL, F->Q.a, &F->oh);
        require((size_t)F->Q.d < F->oh.n && F->oh.f[F->Q.d].kind == F_FACE, "APPLY_PARTIAL_DIM_BINDER: guard field");
        F->f2 = F->oh.f[F->Q.d].id;
        head_free(&F->oh);
        KF_CALL(fc_reindex, &F->f1, F->f2, F->m1);
        KF_CALL(reindex, &F->r1, F->o2.body, F->m1);
        sp_partial(&F->sp, F->f1, F->r1);
        break;
    }
    case OP_FORALL_DIMENSION: WANT(D_FACE); KF_CALL(fc_forall, &F->f1, F->P.a, F->Q.face); sp_face(&F->sp, F->f1); break;
    case OP_PROJECT_FACE: { WANT(D_FACE); { size_t m; const uint64_t *S = dimset_get(F->P.a, &m); KF_CALL(fc_project, &F->f1, F->Q.face, S, m); } sp_face(&F->sp, F->f1); break; }
    case OP_FACE_COVERAGE: WANT(D_FACE); KF_CALL(fc_entails, &F->b1, F->P.face, F->Q.face); sp_status(&F->sp, F->b1 ? ST_COVERED : ST_NOT_COVERED, 0, 0); break;
    case OP_USE_PARTIAL:
        WANT(D_PARTIAL);
        KF_CALL(fc_entails, &F->b1, F->P.face, F->Q.face);
        if (F->b1) sp_ref(&F->sp, F->Q.ref);
        else sp_status(&F->sp, ST_NOT_COVERED, F->Q.face, F->Q.ref);      /* retains the partial payload */
        break;
    case OP_GET_SUPPORT: { WANT(D_REF); Payload p = {0}; p.a = ref_support(F->Q.ref); sp_desc(&F->sp, D_DIMSET, p); break; }
    case OP_REINDEX_HEAD: WANT(D_HEAD_RECIPE); KF_CALL(reindex, &F->r1, F->d->head->owner, F->P.a); SP_RECIPE_F(F->r1); break;
    case OP_MATERIALIZE: WANT(D_HEAD_RECIPE); F->sp.kind = SP_MATERIALIZE; break;
    case OP_APPLY_TRANSFORM: {
        /* §43: the one replacement — v := reindex(template, σ + slot ↦ a);
         * no evaluation of a, the proof, or v */
        WANT(D_REF);
        require(compiler_template(F->P.a, (int)F->P.b, &F->r2, &F->slot), "APPLY_TRANSFORM of an unknown compiled transform");
        mapb_init(&F->mb);
        F->mt = map_n_terms(F->P.c); F->md = map_n_dims(F->P.c);
        KF_MAPB_RESERVE(&F->mb, F->mt + 1, F->md);
        for (F->mk = 0; F->mk < F->mt; F->mk++) { TermVarId x; RefId im; map_term_entry(F->P.c, F->mk, &x, &im); mapb_term(&F->mb, x, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
        for (F->mk = 0; F->mk < F->md; F->mk++) { DimVarId i; IntervalId im; map_dim_entry(F->P.c, F->mk, &i, &im); mapb_dim(&F->mb, i, im); fine_bump(FC_MAP_ENTRIES); KF_SAFE(); }
        mapb_term(&F->mb, F->slot, F->Q.ref);
        KF_CALL(mapb_finish, &F->m1, &F->mb);
        KF_CALL(reindex, &F->r1, F->r2, F->m1);
        sp_ref(&F->sp, F->r1); F->sp.kind = SP_APPLY; F->sp.ap_id = F->P.a; F->sp.ap_dir = (int)F->P.b; F->sp.ap_map = F->P.c; F->sp.ap_arg = F->Q.ref;
        break;
    }
    /* ---- §55: scope and template agents; each is one finite pure operation ---- */
    case OP_CAPTURE_REF_SCOPE: {
        WANT(D_REF);
        F->m = capture_decls_get(F->P.a, &F->cd);
        { Val body = { VS_REF, F->Q.ref }; KF_CALL(capture_scope, &F->sc, F->m, F->cd, body, F->P.ref, F->P.c, F->P.face); }     /* P: a = Δ, ref = type, c = level, face = guard */
        sp_scope(&F->sp, F->sc);
        free(F->cd); F->cd = NULL;
        break;
    }
    case OP_CAPTURE_FACE_SCOPE: {
        WANT(D_FACE);
        F->m = capture_decls_get(F->P.a, &F->cd);
        KF_CALL0(fc_true, &F->f1);
        { Val body = { VS_FACE, F->Q.face }; KF_CALL(capture_scope, &F->sc, F->m, F->cd, body, 0, LEVEL_NONE, F->f1); }
        sp_scope(&F->sp, F->sc);
        free(F->cd); F->cd = NULL;
        break;
    }
    case OP_CAPTURE_INTERVAL_SCOPE: {
        WANT(D_INTERVAL);
        F->m = capture_decls_get(F->P.a, &F->cd);
        KF_CALL0(fc_true, &F->f1);
        { Val body = { VS_INTERVAL, F->Q.a }; KF_CALL(capture_scope, &F->sc, F->m, F->cd, body, 0, LEVEL_NONE, F->f1); }
        sp_scope(&F->sp, F->sc);
        free(F->cd); F->cd = NULL;
        break;
    }
    case OP_REINDEX_SCOPE: WANT(D_SCOPE); KF_CALL(reindex_scope, &F->sc, F->Q.a, F->P.a); sp_scope(&F->sp, F->sc); break;
    case OP_APPLY_SCOPE: {
        WANT(D_SCOPE);
        F->m = scope_args_get(F->P.a, &F->args);
        KF_CALL(apply_scope, &F->tp, F->Q.a, F->m, F->args); free(F->args); F->args = NULL;
        if (F->tp.body.sort == VS_REF) sp_typed_partial(&F->sp, F->tp.body.id, F->tp.type, F->tp.level, F->tp.guard);
        else if (F->tp.body.sort == VS_FACE) sp_face(&F->sp, F->tp.body.id);
        else sp_interval(&F->sp, F->tp.body.id);
        break;
    }
    case OP_FORALL_SCOPE: {
        WANT(D_SCOPE);
        if (scope_arity(F->Q.a) != 1 || scope_local(F->Q.a, 0).sort != S_DIM || scope_body(F->Q.a).sort != VS_FACE) { sp_status(&F->sp, ST_SORT_MISMATCH, 0, 0); break; }
        KF_CALL(forall_scope, &F->f1, F->Q.a); sp_face(&F->sp, F->f1);
        break;
    }
    case OP_REINDEX_TEMPLATE_ENV: { WANT(D_TEMPLATE_ENV); KF_CALL(tenv_reindex, &F->u1, F->Q.a, F->P.a); { Payload p = {0}; p.a = F->u1; sp_desc(&F->sp, D_TEMPLATE_ENV, p); } break; }
    case OP_INSTANTIATE_TEMPLATE: WANT(D_TEMPLATE_ENV); KF_CALL(tenv_instantiate, &F->r1, F->P.a, F->Q.a); sp_ref(&F->sp, F->r1); break;
    case OP_REINDEX_TYPED_PARTIAL:
        WANT(D_TYPED_PARTIAL);
        KF_CALL(reindex, &F->r1, F->Q.ref, F->P.a);
        F->r2 = 0; if (F->Q.b) KF_CALL(reindex, &F->r2, F->Q.b, F->P.a);
        KF_CALL(fc_reindex, &F->f1, F->Q.face, F->P.a);
        sp_typed_partial(&F->sp, F->r1, F->r2, F->Q.c, F->f1);
        break;
    case OP_USE_TYPED_PARTIAL:
        WANT(D_TYPED_PARTIAL);
        KF_CALL(fc_entails, &F->b1, F->P.face, F->Q.face);
        if (F->b1) sp_ref(&F->sp, F->Q.ref);
        else { sp_status(&F->sp, ST_NOT_COVERED, F->Q.face, F->Q.ref); F->sp.p.b = F->Q.b; F->sp.p.c = F->Q.c; }   /* retains the typed partial */
        break;
    case OP_TYPED_PARTIAL_TYPE: WANT(D_TYPED_PARTIAL); sp_ref(&F->sp, F->Q.b); break;      /* retained as type data, not observed */
    case OP_TYPED_PARTIAL_GUARD: WANT(D_TYPED_PARTIAL); sp_face(&F->sp, F->Q.face); break;
    case OP_EVAL: WANT(D_REF); F->sp.kind = SP_EVAL; F->sp.ev_ref = F->Q.ref; F->sp.ev_face = F->P.face; break;
    default: die("unknown operation");
    }
out:
#undef WANT
    *F->out = F->sp; F->sp.head = NULL;   /* the opened head (if any) moves into the caller's spec */
    KF_RETV();
    KF_END;
}
static void op_compute(const Node *o, const Node *d, OpSpec *out) { KStack *s_ = kf_sync_begin(); op_compute_push(s_, NULL, o, d, out); kf_sync_run(s_); kf_sync_end(s_); }
static void op_commit(Net *n, NodeId op, NodeId data, OpSpec *sp) {
    NodeId res = 0;
    switch (sp->kind) {
    case SP_DESC: case SP_STATUS: res = net_descriptor(n, sp->dk, sp->p); break;
    case SP_RECIPE: { res = net_descriptor(n, D_HEAD_RECIPE, sp->p); Node *x = N(n, res); x->head = sp->head; sp->head = NULL; x->tag = x->head->is_var ? 0 : x->head->tag; break; }
    case SP_MATERIALIZE: res = materialize(n, N(n, data)->head); break;
    case SP_APPLY: {
        res = net_descriptor(n, D_REF, sp->p);
        xc_add2((uint64_t *)&n->n_apply, &n->n_apply_cx, 1); reuse_bump(REUSE_IDENTITY_APPLY);
        NetTraceEvent ev = { NT_APPLY_TRANSFORM, sp->ap_id, sp->ap_dir, sp->ap_map, sp->ap_arg, sp->p.ref, 0 };
        Endpoint rp = N(n, op)->peer[1];
        if (rp.node && N(n, rp.node)->kind == A_CONTINUE_REFERENCE) ev.K = N(n, rp.node)->p.a;
        pthread_mutex_lock(&n->trace_mu); vec_push(&n->trace, ev); pthread_mutex_unlock(&n->trace_mu);
        break;
    }
    case SP_EVAL: {
        /* the result endpoint transfers into the continuation; the request descriptors retire */
        NodeId pend = net_pending(n);
        EvalCtx *ctx = malloc(sizeof *ctx); require(ctx, "out of memory");
        ctx->net = n; ctx->pending = pend;
        one_result(n, op, data, pend);
        tls_eval_ref = sp->ev_ref; tls_eval_face = sp->ev_face; tls_eval_ctx = ctx;   /* the request itself is issued after the locks are released */
        return;
    }
    default: die("unknown operation spec");
    }
    one_result(n, op, data, res);
}
static void rule_op(Net *n, NodeId op, NodeId data, OpSpec *pre) {
    OpSpec sp;
    if (pre) sp = *pre;
    else op_compute(N(n, op), N(n, data), &sp);
    op_commit(n, op, data, &sp);
    if (pre) pre->head = sp.head;   /* consumed by the commit (NULL) */
}

static __thread EntryId tls_forward_K; static __thread RefId tls_forward_v;   /* a CONTINUE_REFERENCE rule's deferred request */
/* the deferred-request and pending-pair slots are computation-local (kframe.h): a suspended step carries them */
static void *a_pending(void) { return &tls_pending; }
static void *a_eval_ref(void) { return &tls_eval_ref; }
static void *a_eval_face(void) { return &tls_eval_face; }
static void *a_eval_ctx(void) { return &tls_eval_ctx; }
static void *a_fwd_K(void) { return &tls_forward_K; }
static void *a_fwd_v(void) { return &tls_forward_v; }
static void release_eval_ctx(void *p) { void *c = *(void **)p; if (c) free(c); *(void **)p = NULL; }
__attribute__((constructor)) static void net_ctx_register(void) {
    kf_ctx_register(a_pending, sizeof tls_pending, NULL, NULL);
    kf_ctx_register(a_eval_ref, sizeof tls_eval_ref, NULL, NULL);
    kf_ctx_register(a_eval_face, sizeof tls_eval_face, NULL, NULL);
    kf_ctx_register(a_eval_ctx, sizeof tls_eval_ctx, NULL, release_eval_ctx);
    kf_ctx_register(a_fwd_K, sizeof tls_forward_K, NULL, NULL);
    kf_ctx_register(a_fwd_v, sizeof tls_forward_v, NULL, NULL);
}
static bool is_shell(NodeKind k) { return k == A_HEAD || k == A_BRANCH_NIL || k == A_BRANCH_CONS || k == A_BRANCH; }

/* apply the rule for an oriented, validated, fully locked active pair */
static bool apply_rule(Net *n, NodeId neg, NodeId pos, OpSpec *pre) {
    Node *ng = N(n, neg), *ps = N(n, pos);
    if (ng->kind == A_ROOT || ps->kind == (NodeKind)0) return false;   /* observation root / pending: no rule */
    if (is_operation(ng->kind)) {
        if (is_descriptor(ps->kind)) { rule_op(n, neg, pos, pre); xc_add2((uint64_t *)&n->n_op, &n->n_op_cx, 1); return true; }
        /* an operation meeting a shell is a sort mismatch */
        Replacement r; rep_init(&r);
        rep_remove(&r, neg);
        rep_fresh(&r, neg, 1, status_node(n, ST_SORT_MISMATCH, 0, 0), 0);
        rep_commit(n, &r);
        int8_t per[1] = { -1 }; Payload e = {0};
        net_connect(n, net_node(n, A_ERASE, 1, per, e), 0, pos, 0);
        xc_add2((uint64_t *)&n->n_op, &n->n_op_cx, 1);
        return true;
    }
    if (ng->kind == A_DUP) {
        if (is_descriptor(ps->kind)) rule_dup_data(n, neg, pos);
        else if (is_shell(ps->kind)) rule_dup_shell(n, neg, pos);
        else return false;
        xc_add2((uint64_t *)&n->n_dup, &n->n_dup_cx, 1);
        return true;
    }
    if (ng->kind == A_ERASE) {
        if (is_descriptor(ps->kind)) rule_erase_data(n, neg, pos);
        else if (is_shell(ps->kind)) rule_erase_shell(n, neg, pos);
        else return false;
        xc_add2((uint64_t *)&n->n_erase, &n->n_erase_cx, 1);
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
        xc_add2((uint64_t *)&n->n_continue, &n->n_continue_cx, 1);          /* counted before the forward publication: a reader woken by the result sees the rule event (ordering race fixed) */
        /* the receiver's request is evaluator work (entry lookup, shape, prefix
         * publication): it is issued after the redex's locks are released */
        tls_forward_K = K; tls_forward_v = v;
        return true;
    }
    return false;
}

static int cmp_nodeid(const void *a, const void *b) { NodeId x = *(const NodeId *)a, y = *(const NodeId *)b; return x < y ? -1 : x > y ? 1 : 0; }

/* One candidate active pair. Returns true when a replacement was committed.
 * A frame family (kframe.h): the operation rule's kernel work runs between
 * the two locked sections as a child frame; the retries are transitions
 * (suspension points, outside every lock). */
KF_DECL_EXT_DROP(net_step_pair, bool, net_step_pair_PARAMS, net_step_drop,
    NodeId set_s[64], sorted_s[64]; Endpoint exp_s[64]; uint64_t expgen_s[64];
    NodeId *set, *sorted; Endpoint *exp; uint64_t *expgen; size_t cap, ns, nu; bool result, have_spec, did;
    NodeId x_id, b; Node *x, *y; uint64_t gen_b; Node xs, ys; OpSpec spec; ActiveVec pending;)
static void net_step_drop(net_step_pair_F *F) {
    spec_discard(&F->spec);
    if (F->set && F->set != F->set_s) { free(F->set); free(F->sorted); free(F->exp); free(F->expgen); }
    F->set = NULL; vec_free(&F->pending);
}
KF_STEP(net_step_pair) {
    KF_BEGIN(net_step_pair);
    F->x_id = F->a.node;
    /* the boundary arrays: a fixed fast path, extended for a node of larger arity (no arity cap) */
    F->set = F->set_s; F->sorted = F->sorted_s; F->exp = F->exp_s; F->expgen = F->expgen_s; F->cap = 64;
    F->result = false;
    for (;;) {   /* a retry follows another thread's committed replacement: progress is global */
        Net *n = F->n; NodeId a = F->x_id;
        F->x = N(n, a);
        pthread_mutex_lock(&F->x->mu);
        if (!F->x->live || F->x->gen != F->a.gen) { pthread_mutex_unlock(&F->x->mu); F->result = false; break; }
        Endpoint q = F->x->peer[0];
        pthread_mutex_unlock(&F->x->mu);
        if (!q.node || q.port != 0) { F->result = false; break; }
        F->b = q.node;
        /* lock the redex owners in id order and validate the pair */
        lock_two(n, a, F->b);
        F->y = N(n, F->b);
        { Node *x = F->x, *y = F->y; NodeId b = F->b;
          bool valid = x->live && y->live && x->gen == F->a.gen && x->peer[0].node == b && x->peer[0].port == 0 && y->peer[0].node == a && y->peer[0].port == 0;
          if (!valid) {
              unlock_two(n, a, b);
              if (!x->live || x->gen != F->a.gen) { F->result = false; break; }
              xc_add2((uint64_t *)&n->retries, &n->retries_cx, 1); fine_bump(FC_NET_RETRIES);
              KF_SAFE();
              continue;
          }
          F->gen_b = y->gen;
          /* collect the surviving boundary: every auxiliary neighbour of a and b */
          size_t need = 2 + (size_t)x->nports + (size_t)y->nports;
          if (need > F->cap) {
              if (F->set != F->set_s) { free(F->set); free(F->sorted); free(F->exp); free(F->expgen); }
              F->cap = need; F->set = malloc(F->cap * sizeof *F->set); F->sorted = malloc(F->cap * sizeof *F->sorted); F->exp = malloc(F->cap * sizeof *F->exp); F->expgen = malloc(F->cap * sizeof *F->expgen);
              require(F->set && F->sorted && F->exp && F->expgen, "out of memory");
          }
          F->ns = 0;
          F->set[F->ns++] = a; F->set[F->ns++] = b;
          Node *two[2] = { x, y };
          for (int t = 0; t < 2; t++)
              for (uint16_t k = 1; k < two[t]->nports; k++) {
                  Endpoint e = two[t]->peer[k];
                  if (!e.node || e.node == a || e.node == b) continue;
                  F->set[F->ns] = e.node; F->exp[F->ns] = e; F->expgen[F->ns] = __atomic_load_n(&N(n, e.node)->gen, __ATOMIC_ACQUIRE); F->ns++;
              }
          /* snapshots of the pair (their payloads are fixed while their generations are) */
          F->xs = *x; F->ys = *y;
          unlock_two(n, a, b); }
        /* an operation rule's kernel work is computed here, outside every node lock */
        memset(&F->spec, 0, sizeof F->spec); F->have_spec = false;
        { const Node *negs = F->xs.polarity[0] < 0 ? &F->xs : &F->ys, *poss = F->xs.polarity[0] < 0 ? &F->ys : &F->xs;
          if (is_operation(negs->kind) && is_descriptor(poss->kind)) { F->have_spec = true; KF_CALL(op_compute, NULL, negs, poss, &F->spec); } }
        {
            Net *n = F->n; NodeId a = F->x_id, b = F->b; Node *x = F->x, *y = F->y;
            NodeId *set = F->set, *sorted = F->sorted; Endpoint *exp = F->exp; uint64_t *expgen = F->expgen; size_t ns = F->ns;
            /* lock the whole affected set in a consistent total order */
            memcpy(sorted, set, ns * sizeof(NodeId));
            qsort(sorted, ns, sizeof(NodeId), cmp_nodeid);
            size_t nu = 0;
            for (size_t i = 0; i < ns; i++) if (nu == 0 || sorted[nu - 1] != sorted[i]) sorted[nu++] = sorted[i];
            F->nu = nu;
            for (size_t i = 0; i < nu; i++) pthread_mutex_lock(&N(n, sorted[i])->mu);
            /* revalidate the redex and its boundary */
            bool ok = x->live && y->live && x->gen == F->a.gen && y->gen == F->gen_b && x->peer[0].node == b && x->peer[0].port == 0 && y->peer[0].node == a && y->peer[0].port == 0;
            for (size_t i = 2; i < ns && ok; i++) {
                Node *z = N(n, set[i]);
                if (!z->live || z->gen != expgen[i]) ok = false;
                else { NodeId back = z->peer[exp[i].port].node; if (back != a && back != b) ok = false; }   /* the boundary port still faces the redex */
            }
            /* and that a's and b's aux peers are still the recorded ones */
            if (ok) {
                size_t idx = 2;
                Node *two[2] = { x, y };
                for (int t = 0; t < 2 && ok; t++)
                    for (uint16_t k = 1; k < two[t]->nports && ok; k++) {
                        Endpoint e = two[t]->peer[k];
                        if (!e.node || e.node == a || e.node == b) continue;
                        if (idx >= ns || e.node != exp[idx].node || e.port != exp[idx].port) ok = false;
                        idx++;
                    }
                if (ok && idx != ns) ok = false;
            }
            if (!ok) {
                for (size_t i = 0; i < nu; i++) pthread_mutex_unlock(&N(n, sorted[i])->mu);
                spec_discard(&F->spec);
                if (!x->live || x->gen != F->a.gen) { F->result = false; break; }
                xc_add2((uint64_t *)&n->retries, &n->retries_cx, 1); fine_bump(FC_NET_RETRIES);
                goto retry;
            }
            /* orient: negative principal (agent) vs positive principal (data/shell) */
            NodeId neg = x->polarity[0] < 0 ? a : b, pos = x->polarity[0] < 0 ? b : a;
            memset(&F->pending, 0, sizeof F->pending); tls_pending = &F->pending;
            F->did = apply_rule(n, neg, pos, F->have_spec ? &F->spec : NULL);
            spec_discard(&F->spec);
            if (F->did) xc_add2((uint64_t *)&n->rewrites, &n->rewrites_cx, 1);
            tls_pending = NULL;
            for (size_t i = 0; i < nu; i++) pthread_mutex_unlock(&N(n, sorted[i])->mu);
            /* the deferred requests are evaluator work, issued outside every node lock (synchronous: evaluator unit) */
            if (tls_eval_ctx) { void *ctx = tls_eval_ctx; RefId r = tls_eval_ref; FaceId f = tls_eval_face; tls_eval_ctx = NULL; eval_request(r, f, cont_external(net_eval_deliver, ctx, free)); }
            if (tls_forward_K) { EntryId K = tls_forward_K; RefId v = tls_forward_v; tls_forward_K = 0; tls_forward_v = 0; eval_forward_result(K, v); }
            flush_pending(n, &F->pending);
            F->result = F->did; break;
        }
    retry:
        KF_SAFE();
    }
    if (F->set != F->set_s) { free(F->set); free(F->sorted); free(F->exp); free(F->expgen); }
    F->set = NULL;
    KF_RET(F->result);
    KF_END;
}
KF_SYNC_DEF(net_step_pair, bool, net_step_pair_PARAMS, net_step_pair(Net *n, Active a))
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
        net_step_pair(n, it);            /* new active pairs are flushed (enqueued) inside the step */
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
        if (net_step_pair(n, it)) c++;
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

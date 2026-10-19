#include "net.h"
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
}

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
        if (x->peer[0].node != q.node || x->peer[0].port != q.port) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); count(&n->retries); continue; }
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
        *y->head = *x->head;                 /* the same recipe (an immutable record) */
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

/* ---- operations: each one a frame of the one protocol ----
 * An operation meeting its descriptor is replaced at once by a pending
 * endpoint; a net.op frame computes the result by awaiting the operation
 * families (no host computation inside the rule), and its value — the result
 * descriptor, or a privately built materialized subnet — is connected at the
 * pending endpoint by the same delivery as an evaluation result. */
typedef struct { NodeKind kind; Payload p; bool has_head; Head head; NodeId node; } NetRes;
typedef struct { Net *net; NodeId pending; } OpCtx;

/* connect d at the pending endpoint's consumer (locked with it, in id order,
 * revalidated after locking) */
static void deliver_node(Net *n, NodeId pend, NodeId d, bool eval_result) {
    for (;;) {
        Node *x = N(n, pend);
        pthread_mutex_lock(&x->mu);
        if (!x->live) { pthread_mutex_unlock(&x->mu); return; }   /* consumer released the endpoint */
        Endpoint q = x->peer[0];
        pthread_mutex_unlock(&x->mu);
        if (q.node) lock_two(n, pend, q.node); else pthread_mutex_lock(&x->mu);
        if (!x->live) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); return; }
        if (x->peer[0].node != q.node || x->peer[0].port != q.port) { if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu); count(&n->retries); continue; }
        ActiveVec pending = {0}; tls_pending = &pending;
        retire(n, pend);
        if (q.node) net_connect(n, d, 0, q.node, q.port);
        count(&n->rewrites); if (eval_result) count(&n->n_eval_deliver);
        tls_pending = NULL;
        if (q.node) unlock_two(n, pend, q.node); else pthread_mutex_unlock(&x->mu);
        flush_pending(n, &pending);
        return;
    }
}
static void net_op_deliver(void *ctx, EvalResult *r) {
    OpCtx *c = ctx; Net *n = c->net; NodeId pend = c->pending; free(c);
    NetRes *res = (NetRes *)(void *)r;
    NodeId d = res->node;
    if (!d) {
        d = net_descriptor(n, res->kind, res->p);
        if (res->has_head) {
            Node *y = N(n, d);
            y->head = malloc(sizeof(Head)); require(y->head, "out of memory");
            *y->head = res->head; y->tag = res->head.is_var ? 0 : res->head.tag;
        }
    }
    free(res);
    deliver_node(n, pend, d, false);
}

static Family F_NETOP, Fn_REINDEX, Fn_IVRE, Fn_FCRE, Fn_COMPOSE, Fn_FCMEET, Fn_FCENT, Fn_FCFORALL, Fn_FCPROJ, Fn_CENV, Fn_FIELD, Fn_BINDER,
              Fn_REFVAR, Fn_OVERRIDE, Fn_HEAD, Fn_UNFOLD, Fn_CAPTURE, Fn_TREF, Fn_TIV, Fn_TFC, Fn_TSCOPE, Fn_CINST, Fn_ENVOF, Fn_TVMAKE;
typedef struct {
    Net *net; NodeKind k; Payload P, Q; Head h;
    uint64_t a, b, c; size_t q, nf; Join *J; WordBuf w; bool created;
    NodeId hd, tail;
} OpLoc;
static uint64_t RV_(NetRes *r) { return (uint64_t)(uintptr_t)r; }
static NetRes *nres(NodeKind kind, Payload p) { NetRes *r = calloc(1, sizeof *r); require(r, "out of memory"); r->kind = kind; r->p = p; return r; }
static NetRes *nstat(uint64_t code, FaceId face, RefId ref) { Payload p = {0}; p.a = code; p.face = face; p.ref = ref; return nres(D_STATUS, p); }
static NetRes *nref(RefId t) { Payload p = {0}; p.ref = t; return nres(D_REF, p); }
static NetRes *nface(FaceId f) { Payload p = {0}; p.face = f; return nres(D_FACE, p); }
static NetRes *niv(IntervalId r) { Payload p = {0}; p.a = r; return nres(D_INTERVAL, p); }
static NetRes *nmap(MapId m, FaceId src, FaceId tgt) { Payload p = {0}; p.a = m; p.b = src; p.c = tgt; return nres(D_MAP, p); }
static NetRes *nscope(ScopeId S) { Payload p = {0}; p.a = S; return nres(D_SCOPE, p); }
static NetRes *ntyped(RefId body, RefId type, uint64_t level, FaceId guard) { Payload p = {0}; p.ref = body; p.b = type; p.c = level; p.face = guard; return nres(D_TYPED_PARTIAL, p); }
static uint64_t key3(uint64_t a, uint64_t b, uint64_t c) { uint64_t w[3] = { a, b, c }; return interner_intern(&M.keys, w, 3, NULL); }
static uint64_t key4(uint64_t a, uint64_t b, uint64_t c, uint64_t d) { uint64_t w[4] = { a, b, c, d }; return interner_intern(&M.keys, w, 4, NULL); }

static void netop_step(Cont *k, uint64_t v) {
    OpLoc *L = FR_LOC(k, OpLoc);
    Net *n = L->net;
    uint64_t r = 0;
    FR_BEGIN(k);
    if (L->k == OP_REINDEX_TERM) { FR_AWAIT(k, r, Fn_REINDEX, L->Q.ref, L->P.a); FR_FINISH(k, RV_(nref(r))); }
    if (L->k == OP_REINDEX_INTERVAL) { FR_AWAIT(k, r, Fn_IVRE, L->Q.a, L->P.a); FR_FINISH(k, RV_(niv(r))); }
    if (L->k == OP_REINDEX_FACE) { FR_AWAIT(k, r, Fn_FCRE, L->Q.face, L->P.a); FR_FINISH(k, RV_(nface(r))); }
    if (L->k == OP_COMPOSE_MAP) { FR_AWAIT(k, r, Fn_COMPOSE, L->P.a, L->Q.a); FR_FINISH(k, RV_(nmap(r, 0, 0))); }
    if (L->k == OP_RESTRICT_MAP) {
        FR_AWAIT(k, L->a, Fn_FCRE, L->P.face, L->Q.a);
        FR_AWAIT(k, L->a, Fn_FCMEET, L->Q.b ? L->Q.b : fc_true(), L->a);
        FR_AWAIT(k, L->b, Fn_FCMEET, L->Q.c ? L->Q.c : fc_true(), L->P.face);
        FR_FINISH(k, RV_(nmap(L->Q.a, L->a, L->b)));
    }
    if (L->k == OP_LIFT_TERM || L->k == OP_LIFT_DIMENSION) {
        /* lifting is defined for a construction's own environment map; a
         * template instance interprets programs, it has no map: a status */
        {   RefId owner = L->P.a; BinderSlot slot = (BinderSlot)L->P.b;
            if (ref_is_var(owner) || !tview_is_construction(owner) || slot >= tnode_nbinders(ref_tnode(owner))) FR_FINISH(k, RV_(nstat(ST_INVALID_MAP, 0, 0)));
            if ((L->k == OP_LIFT_TERM) != (tnode_binder_sort(ref_tnode(owner), slot) == S_TERM)) FR_FINISH(k, RV_(nstat(ST_SORT_MISMATCH, 0, 0))); }
        FR_AWAIT(k, L->a, Fn_CENV, ref_tenv(L->P.a), 0);
        if (L->Q.a != L->a) FR_FINISH(k, RV_(nstat(ST_INVALID_MAP, 0, 0)));
        if (L->k == OP_LIFT_TERM) {
            FR_AWAIT(k, L->b, Fn_FIELD, L->P.a, tnode_binder_domain(ref_tnode(L->P.a), (BinderSlot)L->P.b));
            L->c = binder_term_var(L->P.a, (BinderSlot)L->P.b, L->b);
            FR_AWAIT(k, L->c, Fn_REFVAR, L->c, 0);
        } else L->c = iv_var(binder_dim_var(L->P.a, (BinderSlot)L->P.b));
        {   uint64_t atom = obound_id((uint32_t)(tnode_nparams(ref_tnode(L->P.a)) + tnode_binder_local(ref_tnode(L->P.a), (BinderSlot)L->P.b)));
            FR_AWAIT(k, r, Fn_OVERRIDE, L->a, key3(L->k == OP_LIFT_TERM ? S_TERM : S_DIM, atom, L->c)); }
        FR_FINISH(k, RV_(nmap(r, L->Q.b, L->Q.c)));
    }
    if (L->k == OP_OPEN || L->k == OP_REINDEX_HEAD) {
        if (L->k == OP_REINDEX_HEAD) { FR_AWAIT(k, L->a, Fn_REINDEX, L->h.owner, L->P.a); }
        else L->a = L->Q.ref;
        memset(&L->h, 0, sizeof L->h); L->h.owner = L->a;
        if (ref_is_var(L->a)) { L->h.is_var = true; L->h.var = ref_var_id(L->a); }
        else {
            L->h.tag = ref_tag(L->a); L->h.tnode = ref_tnode(L->a); L->h.tenv = ref_tenv(L->a); L->h.n = tnode_nfields(ref_tnode(L->a));
            FR_AWAIT(k, L->h.payload, Fn_HEAD, L->a, 0);
            FR_AWAIT(k, L->h.levels, Fn_HEAD, L->a, 1);
        }
        {   Payload p = {0}; p.ref = L->a; NetRes *res = nres(D_HEAD_RECIPE, p); res->has_head = true; res->head = L->h; FR_FINISH(k, RV_(res)); }
    }
    if (L->k == OP_UNFOLD_GLOBAL) {
        if (ref_is_var(L->Q.ref) || ref_tag(L->Q.ref) != T_GLOBAL) FR_FINISH(k, RV_(nstat(ST_SORT_MISMATCH, 0, 0)));
        FR_AWAIT(k, r, Fn_UNFOLD, L->Q.ref, 0);
        FR_FINISH(k, RV_(nref(r)));
    }
    if (L->k == OP_REINDEX_TERM_BINDER || L->k == OP_REINDEX_DIM_BINDER || L->k == OP_REINDEX_PARTIAL_DIM_BINDER) {
        FR_AWAIT(k, r, Fn_REINDEX, L->Q.a, L->P.a);
        {   Payload p = L->Q; p.a = r;
            FR_FINISH(k, RV_(nres(L->k == OP_REINDEX_TERM_BINDER ? D_TERM_BINDER : L->k == OP_REINDEX_DIM_BINDER ? D_DIM_BINDER : D_PARTIAL_DIM_BINDER, p))); }
    }
    if (L->k == OP_REINDEX_PARTIAL) {
        FR_AWAIT(k, L->a, Fn_FCRE, L->Q.face, L->P.a);
        FR_AWAIT(k, L->b, Fn_REINDEX, L->Q.ref, L->P.a);
        { Payload p = {0}; p.face = L->a; p.ref = L->b; FR_FINISH(k, RV_(nres(D_PARTIAL, p))); }
    }
    if (L->k == OP_APPLY_TERM_BINDER) { FR_AWAIT(k, r, Fn_BINDER, L->Q.a, key4(S_TERM, L->Q.b, L->Q.c, L->P.ref)); FR_FINISH(k, RV_(nref(r))); }
    if (L->k == OP_APPLY_DIM_BINDER) { FR_AWAIT(k, r, Fn_BINDER, L->Q.a, key4(S_DIM, L->Q.b, L->Q.c, L->P.a)); FR_FINISH(k, RV_(nref(r))); }
    if (L->k == OP_APPLY_PARTIAL_DIM_BINDER) {
        /* the body at r; the guard is an ordinary field (the binder's fresh
         * dimension cannot occur in it, so its specialization at r is itself) */
        require((size_t)L->Q.d < tnode_nfields(ref_tnode(L->Q.a)) && tnode_field_kind(ref_tnode(L->Q.a), L->Q.d) == F_FACE, "APPLY_PARTIAL_DIM_BINDER: guard field");
        FR_AWAIT(k, L->a, Fn_BINDER, L->Q.a, key4(S_DIM, L->Q.b, L->Q.c, L->P.a));
        FR_AWAIT(k, L->b, Fn_FIELD, L->Q.a, L->Q.d);
        { Payload p = {0}; p.face = L->b; p.ref = L->a; FR_FINISH(k, RV_(nres(D_PARTIAL, p))); }
    }
    if (L->k == OP_FORALL_DIMENSION) { FR_AWAIT(k, r, Fn_FCFORALL, L->Q.face, L->P.a); FR_FINISH(k, RV_(nface(r))); }
    if (L->k == OP_PROJECT_FACE) { FR_AWAIT(k, r, Fn_FCPROJ, L->Q.face, L->P.a); FR_FINISH(k, RV_(nface(r))); }
    if (L->k == OP_FACE_COVERAGE) { FR_AWAIT(k, r, Fn_FCENT, L->P.face, L->Q.face); FR_FINISH(k, RV_(nstat(r == 2 ? ST_COVERED : ST_NOT_COVERED, 0, 0))); }
    if (L->k == OP_USE_PARTIAL) {
        FR_AWAIT(k, r, Fn_FCENT, L->P.face, L->Q.face);
        FR_FINISH(k, RV_(r == 2 ? nref(L->Q.ref) : nstat(ST_NOT_COVERED, L->Q.face, L->Q.ref)));   /* retains the partial payload */
    }
    if (L->k == OP_MATERIALIZE) {
        /* the fields' values as one join; the shell built privately, one node
         * per step, and connected once at the pending endpoint */
        {   Payload p = {0}; p.ref = L->h.owner;
            if (L->h.is_var) {
                int8_t pol[1] = { +1 }; p.a = L->h.var;
                L->hd = net_node(n, A_HEAD, 1, pol, p); N(n, L->hd)->tag = 0;
                NetRes *res = nres(0, p); res->node = L->hd; FR_FINISH(k, RV_(res));
            } }
        L->nf = L->h.n;
        L->J = join_new(k, L->nf);
        for (L->q = 0; L->q < L->nf; L->q++) {
            if (tnode_field_slot(L->h.tnode, L->q) != NO_SLOT) join_fill(L->J, L->q, 0);
            else join_request(L->J, L->q, Fn_FIELD, L->h.owner, L->q);
            if (L->q + 1 < L->nf) FR_YIELD(k);
        }
        FR_JOIN(k, L->J);
        if (L->h.tag == T_SYSTEM) {
            /* HEAD_SYSTEM with one negative aux attached to a BRANCH list */
            {   Payload e = {0}; int8_t polnil[1] = { +1 };
                L->tail = net_node(n, A_BRANCH_NIL, 1, polnil, e); }
            for (L->q = L->nf / 2; L->q-- > 0;) {
                {   Payload e = {0}; int8_t polcons[3] = { +1, -1, -1 }, polbr[3] = { +1, -1, -1 };
                    NodeId br = net_node(n, A_BRANCH, 3, polbr, e);
                    net_connect(n, br, 1, desc_face(n, join_value(L->J, 2 * L->q)), 0);
                    net_connect(n, br, 2, desc_ref(n, join_value(L->J, 2 * L->q + 1)), 0);
                    NodeId cons = net_node(n, A_BRANCH_CONS, 3, polcons, e);
                    net_connect(n, cons, 1, br, 0);
                    net_connect(n, cons, 2, L->tail, 0);
                    L->tail = cons; }
                FR_YIELD(k);
            }
            {   Payload p = {0}; p.ref = L->h.owner; int8_t pol[2] = { +1, -1 };
                L->hd = net_node(n, A_HEAD, 2, pol, p); N(n, L->hd)->tag = T_SYSTEM;
                net_connect(n, L->hd, 1, L->tail, 0); }
        } else {
            require(L->nf + 1 <= 255, "materialized head arity");
            {   int8_t pol[256]; pol[0] = +1; for (size_t q = 0; q < L->nf; q++) pol[q + 1] = -1;
                Payload p = {0}; p.ref = L->h.owner;
                L->hd = net_node(n, A_HEAD, (uint8_t)(L->nf + 1), pol, p); N(n, L->hd)->tag = L->h.tag; }
            for (L->q = 0; L->q < L->nf; L->q++) {
                {   TNodeId Q = L->h.tnode; Tag tag = L->h.tag; size_t q = L->q;
                    BinderSlot bs = tnode_field_slot(Q, q); FieldKind kd = tnode_field_kind(Q, q);
                    uint64_t val = join_value(L->J, q);
                    NodeId d;
                    if (bs != NO_SLOT) {
                        if (tag == T_COMP && q == 2) d = desc_binder(n, D_PARTIAL_DIM_BINDER, L->h.owner, bs, (FieldIndex)q, 1);
                        else d = desc_binder(n, tnode_binder_sort(Q, bs) == S_TERM ? D_TERM_BINDER : D_DIM_BINDER, L->h.owner, bs, (FieldIndex)q, NO_FIELD);
                    } else if (kd == F_REF) {
                        /* partial fields: Glue fibre/equivalence under alpha, glue intro fibre term */
                        bool partial = (tag == T_GLUE_TYPE && (q == 2 || q == 3)) || (tag == T_GLUE_INTRO && (q == 2 || q == 3 || q == 4)) || (tag == T_UNGLUE && (q == 2 || q == 3));
                        d = partial ? desc_partial(n, join_value(L->J, 1), val) : desc_ref(n, val);
                    } else if (kd == F_INTERVAL) d = desc_interval(n, val);
                    else d = desc_face(n, val);
                    net_connect(n, L->hd, (uint16_t)(q + 1), d, 0); }
                FR_YIELD(k);
            }
        }
        join_free(L->J); L->J = NULL;
        { Payload e = {0}; NetRes *res = nres(0, e); res->node = L->hd; FR_FINISH(k, RV_(res)); }
    }
    if (L->k == OP_APPLY_TRANSFORM) {
        /* §43: v := reindex(template, σ + slot ↦ a); no evaluation of a, the proof, or v */
        {   RefId body; TermVarId slot;
            require(compiler_template(L->P.a, (int)L->P.b, &body, &slot), "APPLY_TRANSFORM of an unknown compiled transform");
            L->b = body; L->c = slot; }
        FR_AWAIT(k, L->a, Fn_OVERRIDE, L->P.c, key3(S_TERM, L->c, L->Q.ref));
        FR_AWAIT(k, r, Fn_REINDEX, L->b, L->a);
        count(&n->n_apply);
        FR_FINISH(k, RV_(nref(r)));
    }
    if (L->k == OP_CAPTURE_REF_SCOPE || L->k == OP_CAPTURE_FACE_SCOPE || L->k == OP_CAPTURE_INTERVAL_SCOPE) {
        /* the capture request: the telescope Δ (payload a), then the body and
         * (for a reference) the result type, level and guard */
        {   size_t m; const uint64_t *dw = interner_get(&M.keys, L->P.a, &m); require(dw[0] == 0xCA9, "not a capture telescope");
            wordbuf_init(&L->w);
            for (size_t q = 1; q < m; q++) wordbuf_push(&L->w, dw[q]);
            if (L->k == OP_CAPTURE_REF_SCOPE) { wordbuf_push(&L->w, VS_REF); wordbuf_push(&L->w, L->Q.ref); wordbuf_push(&L->w, L->P.ref); wordbuf_push(&L->w, L->P.c); wordbuf_push(&L->w, L->P.face); }
            else if (L->k == OP_CAPTURE_FACE_SCOPE) { wordbuf_push(&L->w, VS_FACE); wordbuf_push(&L->w, L->Q.face); wordbuf_push(&L->w, 0); wordbuf_push(&L->w, LEVEL_NONE); wordbuf_push(&L->w, fc_true()); }
            else { wordbuf_push(&L->w, VS_INTERVAL); wordbuf_push(&L->w, L->Q.a); wordbuf_push(&L->w, 0); wordbuf_push(&L->w, LEVEL_NONE); wordbuf_push(&L->w, fc_true()); } }
        FR_CALL(k, L->a, intern_sub(k, &M.keys, &L->w, &L->created));
        FR_AWAIT(k, r, Fn_CAPTURE, L->a, 0);
        FR_FINISH(k, RV_(nscope(r)));
    }
    if (L->k == OP_REINDEX_SCOPE) {
        if (map_is_identity(L->P.a)) FR_FINISH(k, RV_(nscope(L->Q.a)));
        FR_AWAIT(k, r, Fn_TSCOPE, L->Q.a, trav_key(TR_RE, 0, L->P.a));
        FR_FINISH(k, RV_(nscope(r)));
    }
    if (L->k == OP_APPLY_SCOPE) {
        {   size_t m; const uint64_t *aw = interner_get(&M.keys, L->P.a, &m); require(aw[0] == 0xA96, "not a scope argument list");
            require(aw[1] == scope_arity(L->Q.a), "scope application arity");
            wordbuf_init(&L->w);
            for (size_t q = 2; q < m; q++) wordbuf_push(&L->w, aw[q]); }
        FR_CALL(k, L->a, intern_sub(k, &M.keys, &L->w, &L->created));
        L->a = trav_key(TR_APPLY, 0, L->a);
        {   Val b = scope_body(L->Q.a);
            L->J = join_new(k, 3);
            join_request(L->J, 0, b.sort == VS_REF ? Fn_TREF : b.sort == VS_INTERVAL ? Fn_TIV : Fn_TFC, b.id, L->a);
            if (scope_type(L->Q.a)) join_request(L->J, 1, Fn_TREF, scope_type(L->Q.a), L->a); else join_fill(L->J, 1, 0);
            join_request(L->J, 2, Fn_TFC, scope_guard(L->Q.a), L->a); }
        FR_JOIN(k, L->J);
        {   Val b = scope_body(L->Q.a); NetRes *res;
            if (b.sort == VS_REF) res = ntyped(join_value(L->J, 0), join_value(L->J, 1), scope_level(L->Q.a), join_value(L->J, 2));
            else if (b.sort == VS_FACE) res = nface(join_value(L->J, 0));
            else res = niv(join_value(L->J, 0));
            join_free(L->J); L->J = NULL;
            FR_FINISH(k, RV_(res)); }
    }
    if (L->k == OP_FORALL_SCOPE) {
        if (scope_arity(L->Q.a) != 1 || scope_local(L->Q.a, 0).sort != S_DIM || scope_body(L->Q.a).sort != VS_FACE) FR_FINISH(k, RV_(nstat(ST_SORT_MISMATCH, 0, 0)));
        FR_AWAIT(k, r, Fn_FCFORALL, scope_body(L->Q.a).id, bound_id(0, 0));
        FR_AWAIT(k, r, Fn_TFC, r, trav_key(TR_LOWER, 0, 0));
        FR_FINISH(k, RV_(nface(r)));
    }
    if (L->k == OP_REINDEX_TEMPLATE_ENV) {
        L->nf = tenv_size(L->Q.a);
        L->J = join_new(k, L->nf);
        for (L->q = 0; L->q < L->nf; L->q++) {
            {   uint64_t slot; TVal val; tenv_entry(L->Q.a, L->q, &slot, &val);
                if (val.sort == PS_LEVEL) join_fill(L->J, L->q, val.id);
                else if (val.sort == PS_REF) join_request(L->J, L->q, Fn_REINDEX, val.id, L->P.a);
                else if (val.sort == PS_INTERVAL) join_request(L->J, L->q, Fn_IVRE, val.id, L->P.a);
                else if (val.sort == PS_FACE) join_request(L->J, L->q, Fn_FCRE, val.id, L->P.a);
                else join_request(L->J, L->q, Fn_TSCOPE, val.id, trav_key(TR_RE, 0, L->P.a)); }
            if (L->q + 1 < L->nf) FR_YIELD(k);
        }
        FR_JOIN(k, L->J);
        wordbuf_init(&L->w);
        for (L->q = 0; L->q < L->nf; L->q++) {
            { uint64_t slot; TVal val; tenv_entry(L->Q.a, L->q, &slot, &val); wordbuf_push(&L->w, slot); wordbuf_push(&L->w, val.sort); wordbuf_push(&L->w, join_value(L->J, L->q)); }
            FR_YIELD(k);
        }
        join_free(L->J); L->J = NULL;
        FR_CALL(k, r, intern_sub(k, &M.tenvs, &L->w, &L->created));
        { Payload p = {0}; p.a = r; FR_FINISH(k, RV_(nres(D_TEMPLATE_ENV, p))); }
    }
    if (L->k == OP_INSTANTIATE_TEMPLATE) {
        if (tnode_is_construction(L->P.a)) { FR_AWAIT(k, r, Fn_CINST, L->P.a, L->Q.a); FR_FINISH(k, RV_(nref(r))); }
        FR_AWAIT(k, L->a, Fn_ENVOF, L->P.a, L->Q.a);
        FR_AWAIT(k, r, Fn_TVMAKE, L->P.a, L->a);
        FR_FINISH(k, RV_(nref(r)));
    }
    if (L->k == OP_REINDEX_TYPED_PARTIAL) {
        L->J = join_new(k, 3);
        join_request(L->J, 0, Fn_REINDEX, L->Q.ref, L->P.a);
        if (L->Q.b) join_request(L->J, 1, Fn_REINDEX, L->Q.b, L->P.a); else join_fill(L->J, 1, 0);
        join_request(L->J, 2, Fn_FCRE, L->Q.face, L->P.a);
        FR_JOIN(k, L->J);
        {   NetRes *res = ntyped(join_value(L->J, 0), join_value(L->J, 1), L->Q.c, join_value(L->J, 2));
            join_free(L->J); L->J = NULL; FR_FINISH(k, RV_(res)); }
    }
    if (L->k == OP_USE_TYPED_PARTIAL) {
        FR_AWAIT(k, r, Fn_FCENT, L->P.face, L->Q.face);
        if (r == 2) FR_FINISH(k, RV_(nref(L->Q.ref)));
        { NetRes *res = nstat(ST_NOT_COVERED, L->Q.face, L->Q.ref); res->p.b = L->Q.b; res->p.c = L->Q.c; FR_FINISH(k, RV_(res)); }   /* retains the typed partial */
    }
    die("net.op: unknown operation");
    FR_END(k);
}

void net_families_init(void) {
    Fn_REINDEX = family_lookup("reindex"); Fn_IVRE = family_lookup("iv.reindex"); Fn_FCRE = family_lookup("fc.reindex"); Fn_COMPOSE = family_lookup("map.compose");
    Fn_FCMEET = family_lookup("fc.meet"); Fn_FCENT = family_lookup("fc.entails"); Fn_FCFORALL = family_lookup("fc.forall"); Fn_FCPROJ = family_lookup("fc.project");
    Fn_CENV = family_lookup("construction.envmap"); Fn_FIELD = family_lookup("field"); Fn_BINDER = family_lookup("binder"); Fn_REFVAR = family_lookup("ref.var");
    Fn_OVERRIDE = family_lookup("map.override"); Fn_HEAD = family_lookup("head.annotation"); Fn_UNFOLD = family_lookup("global.unfold");
    Fn_CAPTURE = family_lookup("scope.capture"); Fn_TREF = family_lookup("trav.ref"); Fn_TIV = family_lookup("trav.interval"); Fn_TFC = family_lookup("trav.face");
    Fn_TSCOPE = family_lookup("trav.scope"); Fn_CINST = family_lookup("construction.instance"); Fn_ENVOF = family_lookup("template.envof"); Fn_TVMAKE = family_lookup("template.view");
    require(Fn_TVMAKE && Fn_UNFOLD && Fn_CAPTURE, "the operation families are registered first");
    F_NETOP = family_define("net.op", netop_step, sizeof(OpLoc), false);
}

static void rule_op(Net *n, NodeId op, NodeId data) {
    Node os = *N(n, op), ds = *N(n, data);
    const Node *o = &os, *d = &ds;
    NodeKind k = o->kind, dk = d->kind;
    Payload P = o->p, Q = d->p;
    /* the operand sort each operation consumes; a mismatch is a status */
    NodeKind want = 0;
    if (k == OP_REINDEX_TERM || k == OP_OPEN || k == OP_UNFOLD_GLOBAL || k == OP_GET_SUPPORT || k == OP_APPLY_TRANSFORM || k == OP_CAPTURE_REF_SCOPE || k == OP_EVAL) want = D_REF;
    else if (k == OP_REINDEX_INTERVAL || k == OP_CAPTURE_INTERVAL_SCOPE) want = D_INTERVAL;
    else if (k == OP_REINDEX_FACE || k == OP_FORALL_DIMENSION || k == OP_PROJECT_FACE || k == OP_FACE_COVERAGE || k == OP_CAPTURE_FACE_SCOPE) want = D_FACE;
    else if (k == OP_COMPOSE_MAP || k == OP_RESTRICT_MAP || k == OP_LIFT_TERM || k == OP_LIFT_DIMENSION) want = D_MAP;
    else if (k == OP_REINDEX_TERM_BINDER || k == OP_APPLY_TERM_BINDER) want = D_TERM_BINDER;
    else if (k == OP_REINDEX_DIM_BINDER || k == OP_APPLY_DIM_BINDER) want = D_DIM_BINDER;
    else if (k == OP_REINDEX_PARTIAL_DIM_BINDER || k == OP_APPLY_PARTIAL_DIM_BINDER) want = D_PARTIAL_DIM_BINDER;
    else if (k == OP_REINDEX_PARTIAL || k == OP_USE_PARTIAL) want = D_PARTIAL;
    else if (k == OP_REINDEX_HEAD || k == OP_MATERIALIZE) want = D_HEAD_RECIPE;
    else if (k == OP_REINDEX_SCOPE || k == OP_APPLY_SCOPE || k == OP_FORALL_SCOPE) want = D_SCOPE;
    else if (k == OP_REINDEX_TEMPLATE_ENV || k == OP_INSTANTIATE_TEMPLATE) want = D_TEMPLATE_ENV;
    else if (k == OP_REINDEX_TYPED_PARTIAL || k == OP_USE_TYPED_PARTIAL || k == OP_TYPED_PARTIAL_TYPE || k == OP_TYPED_PARTIAL_GUARD) want = D_TYPED_PARTIAL;
    else die("unknown operation");
    if (dk != want) { one_result(n, op, data, status_node(n, ST_SORT_MISMATCH, 0, 0)); return; }
    /* operations that read their payload only */
    if (k == OP_GET_SUPPORT) { Payload p = {0}; p.a = ref_support(Q.ref); one_result(n, op, data, net_descriptor(n, D_DIMSET, p)); return; }
    if (k == OP_TYPED_PARTIAL_TYPE) { one_result(n, op, data, desc_ref(n, Q.b)); return; }      /* retained as type data, not observed */
    if (k == OP_TYPED_PARTIAL_GUARD) { one_result(n, op, data, desc_face(n, Q.face)); return; }
    NodeId pend = net_pending(n);
    one_result(n, op, data, pend);
    if (k == OP_EVAL) {
        /* the result endpoint transfers into the continuation; the request
         * descriptors retire */
        EvalCtx *ctx = malloc(sizeof *ctx); require(ctx, "out of memory");
        ctx->net = n; ctx->pending = pend;
        eval_request(Q.ref, P.face, cont_external(net_eval_deliver, ctx, free));
        return;
    }
    Cont *f = frame_new(F_NETOP, 0);
    OpLoc *L = f->loc;
    L->net = n; L->k = k; L->P = P; L->Q = Q;
    if (d->head) L->h = *d->head;
    OpCtx *ctx = malloc(sizeof *ctx); require(ctx, "out of memory");
    ctx->net = n; ctx->pending = pend;
    frame_launch(f, cont_external(net_op_deliver, ctx, free));
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
        eval_forward_result(K, v);
        count(&n->n_continue);
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
        if (!valid) { unlock_two(n, a, b); if (!x->live || x->gen != cand.gen) return false; count(&n->retries); continue; }
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
            count(&n->retries);
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

static size_t net_run_pairs(Net *n) {
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
 * ready multiset with all its workers idle.  Every operation is a request of
 * the one protocol (net.op frames, evaluation), so running the net is running
 * both: there is no net-only quiescence that leaves operations pending. */
size_t net_run(Net *n) {
    size_t total = 0;
    for (;;) {
        size_t before = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        size_t c = net_run_pairs(n);
        size_t e = eval_run();
        size_t after = __atomic_load_n(&n->rewrites, __ATOMIC_SEQ_CST);
        total += c;
        if (c == 0 && e == 0 && after == before) break;
    }
    return total;
}

size_t net_run_with_eval(Net *n) { return net_run(n); }

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
    Q.a = tview_env_map(id);
    TCHECK(run_op(&net, OP_LIFT_TERM, P, D_MAP, Q, &ok, &op) && ok == D_MAP && map_n_terms(op.a) == map_n_terms(Q.a) + 1, "LIFT_TERM with the owner's environment map gives the lifted map");
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
      size_t orgS = interner_count(&M.tnodes);
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
      TCHECK(interner_count(&M.tnodes) == orgS, "no scope or template rule allocated a node"); }

    /* duplication copies handles: no new interned records */
    size_t refs0 = interner_count(&M.refs), org0 = interner_count(&M.tnodes);
    int8_t pdup[3] = { -1, +1, +1 }; Payload e = {0};
    NodeId dup = net_node(&net, A_DUP, 3, pdup, e);
    NodeId r1 = mk_root(&net), r2 = mk_root(&net);
    net_connect(&net, dup, 1, r1, 0); net_connect(&net, dup, 2, r2, 0);
    Q = (Payload){0}; Q.ref = id;
    net_connect(&net, dup, 0, net_descriptor(&net, D_REF, Q), 0);
    net_run(&net);
    Payload p1, p2;
    TCHECK(net_root_read(&net, r1, &ok, &p1) && net_root_read(&net, r2, NULL, &p2) && ok == D_REF && p1.ref == id && p2.ref == id, "duplicated descriptors share the payload handle");
    TCHECK(interner_count(&M.refs) == refs0 && interner_count(&M.tnodes) == org0, "duplication allocates no node, body or reference");
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
    refs0 = interner_count(&M.refs); org0 = interner_count(&M.tnodes);
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
    TCHECK(interner_count(&M.refs) == refs0 && interner_count(&M.tnodes) == org0, "shell duplication still allocates nothing in the tables");
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

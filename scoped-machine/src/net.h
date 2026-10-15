/* net.h — scope agents on immutable handles (§19–20).
 *
 * Nodes carry polarized ports. Data descriptors have a positive principal
 * port and an immutable payload handle; one-result operation agents have a
 * negative principal port and a positive result auxiliary. A rule rewires
 * every surviving boundary endpoint exactly once and connects only opposite
 * polarities. Duplicating a descriptor copies its handle, never the origin,
 * body, substitution images, or evaluation entries.
 */
#ifndef CUBICAL_NET_H
#define CUBICAL_NET_H

#include "eval.h"

typedef uint32_t NodeId;      /* 0 = none */
typedef struct { NodeId node; uint16_t port; } Endpoint;

typedef enum {
    /* data descriptors (positive principal, no auxiliaries) */
    D_REF = 1, D_MAP, D_INTERVAL, D_FACE, D_TERM_BINDER, D_DIM_BINDER, D_PARTIAL,
    D_PARTIAL_DIM_BINDER, D_CONTEXT, D_HEAD_RECIPE, D_DIMSET, D_EVAL_RESULT, D_STATUS,
    /* one-result operations (negative principal, aux 1 = positive result) */
    OP_REINDEX_TERM, OP_REINDEX_INTERVAL, OP_REINDEX_FACE, OP_COMPOSE_MAP, OP_RESTRICT_MAP,
    OP_LIFT_TERM, OP_LIFT_DIMENSION, OP_OPEN, OP_UNFOLD_GLOBAL, OP_REINDEX_TERM_BINDER,
    OP_REINDEX_DIM_BINDER, OP_REINDEX_PARTIAL_DIM_BINDER, OP_REINDEX_PARTIAL,
    OP_APPLY_TERM_BINDER, OP_APPLY_DIM_BINDER, OP_APPLY_PARTIAL_DIM_BINDER,
    OP_FORALL_DIMENSION, OP_PROJECT_FACE, OP_FACE_COVERAGE, OP_USE_PARTIAL, OP_GET_SUPPORT,
    OP_REINDEX_HEAD, OP_MATERIALIZE, OP_EVAL,
    /* structural agents */
    A_DUP,        /* negative principal; aux 1,2 positive results */
    A_ERASE,      /* negative principal */
    A_HEAD,       /* materialized constructor: positive principal, negative field auxiliaries */
    A_BRANCH_NIL, A_BRANCH_CONS, A_BRANCH,
    A_ROOT        /* observation root: one negative port */
} NodeKind;

/* payload records held by descriptors / parameters held by operations */
typedef struct {
    uint64_t a, b, c, d;      /* handles / small integers, meaning per kind */
    FaceId face;
    RefId ref;
} Payload;

typedef struct {
    NodeKind kind;
    bool live;
    uint8_t nports;           /* port 0 = principal */
    Endpoint *peer;           /* per port; node 0 = free */
    int8_t *polarity;         /* +1 / -1 per port */
    Payload p;
    Head *head;               /* materialized recipe (A_HEAD / D_HEAD_RECIPE) */
    Tag tag;
    uint64_t gen;             /* generation: bumped at retirement; stale handles are detected */
    pthread_mutex_t mu;       /* owner lock: guards live, peer[], and the fields above */
} Node;

typedef struct { NodeId node; uint64_t gen; } Active;

/* Nodes live in non-moving storage and are never freed during a run, so a
 * worker holding a NodeId can always dereference it (pinning is trivial);
 * generations detect stale identity. A replacement locks the redex owners
 * and every surviving boundary owner in a consistent total order (by id),
 * revalidates the redex and its boundary, installs, publishes and retires,
 * then enqueues the new active pairs after releasing the locks (§20). */
typedef struct {
    Chunked nodes; size_t nnodes;
    pthread_mutex_t alloc_mu;
    VEC(Active) active;       /* candidate active pairs (by one member, with generation) */
    pthread_mutex_t act_mu; pthread_cond_t act_cv, idle_cv;
    size_t outstanding; bool stop;   /* §35: queued + executing active pairs */
    pthread_t *workers; size_t nworkers;
    size_t rewrites;
    /* local rule instances by class (diamond-balanced event classes), committed only */
    size_t n_op, n_dup, n_erase, n_eval_deliver;
    size_t retries;           /* diagnostics: replacements abandoned after revalidation */
    int policy;               /* 0 LIFO, 1 FIFO, 2 random (sequential selection only) */
    uint64_t rng;
} Net;

void net_init(Net *n);
void net_free(Net *n);
NodeId net_descriptor(Net *n, NodeKind kind, Payload p);
NodeId net_operation(Net *n, NodeKind kind, Payload p);
NodeId net_node(Net *n, NodeKind kind, uint8_t nports, const int8_t *polarity, Payload p);
void net_connect(Net *n, NodeId a, uint16_t pa, NodeId b, uint16_t pb);
void net_disconnect(Net *n, NodeId a, uint16_t pa);   /* client-side: free a port (quiescent net) */
Endpoint net_peer(const Net *n, NodeId a, uint16_t pa);
bool net_is_live(const Net *n, NodeId a);
Node *net_node_ptr(const Net *n, NodeId a);           /* quiescent inspection only */
size_t net_node_count(Net *n);
void net_set_workers(Net *n, size_t workers);          /* 0 = sequential */
/* run local rules until no active pair remains; returns rewrite count */
size_t net_run(Net *n);
/* evaluation requests suspended in the cache are resumed by the eval
 * scheduler; this drives both until quiescent */
size_t net_run_with_eval(Net *n);
/* read a result descriptor's payload through a root's negative port */
bool net_root_read(const Net *n, NodeId root, NodeKind *kind, Payload *p);

void test_net(void);

#endif

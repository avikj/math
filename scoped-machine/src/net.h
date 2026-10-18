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
#include "template.h"

typedef uint64_t NodeId;      /* 0 = none */
typedef struct { NodeId node; uint16_t port; } Endpoint;

typedef enum {
    /* data descriptors (positive principal, no auxiliaries) */
    D_REF = 1, D_MAP, D_INTERVAL, D_FACE, D_TERM_BINDER, D_DIM_BINDER, D_PARTIAL,
    D_PARTIAL_DIM_BINDER, D_CONTEXT, D_HEAD_RECIPE, D_DIMSET, D_EVAL_RESULT, D_STATUS,
    D_SCOPE, D_TEMPLATE_ENV, D_TYPED_PARTIAL,      /* §55: a = ScopeId / TEnvId; typed partial: ref = body, b = type, c = level, face = guard */
    /* one-result operations (negative principal, aux 1 = positive result) */
    OP_REINDEX_TERM, OP_REINDEX_INTERVAL, OP_REINDEX_FACE, OP_COMPOSE_MAP, OP_RESTRICT_MAP,
    OP_LIFT_TERM, OP_LIFT_DIMENSION, OP_OPEN, OP_UNFOLD_GLOBAL, OP_REINDEX_TERM_BINDER,
    OP_REINDEX_DIM_BINDER, OP_REINDEX_PARTIAL_DIM_BINDER, OP_REINDEX_PARTIAL,
    OP_APPLY_TERM_BINDER, OP_APPLY_DIM_BINDER, OP_APPLY_PARTIAL_DIM_BINDER,
    OP_FORALL_DIMENSION, OP_PROJECT_FACE, OP_FACE_COVERAGE, OP_USE_PARTIAL, OP_GET_SUPPORT,
    OP_REINDEX_HEAD, OP_MATERIALIZE, OP_APPLY_TRANSFORM, OP_EVAL,
    /* §55 scope / template operations (payload conventions in net.c) */
    OP_CAPTURE_REF_SCOPE, OP_CAPTURE_FACE_SCOPE, OP_CAPTURE_INTERVAL_SCOPE, OP_REINDEX_SCOPE, OP_APPLY_SCOPE, OP_FORALL_SCOPE,
    OP_REINDEX_TEMPLATE_ENV, OP_INSTANTIATE_TEMPLATE, OP_REINDEX_TYPED_PARTIAL, OP_USE_TYPED_PARTIAL, OP_TYPED_PARTIAL_TYPE, OP_TYPED_PARTIAL_GUARD,
    /* structural agents */
    A_DUP,        /* negative principal; aux 1,2 positive results */
    A_ERASE,      /* negative principal */
    A_CONTINUE_REFERENCE,   /* §43 receiver: negative principal, no auxiliaries; payload a = parent entry */
    A_HEAD,       /* materialized constructor: positive principal, negative field auxiliaries */
    A_BRANCH_NIL, A_BRANCH_CONS, A_BRANCH,
    A_ROOT        /* observation root: one negative port */
} NodeKind;

/* §55 operand records: a capture telescope Δ and a scope argument list are
 * immutable interned payloads (handles), never wires */
uint64_t net_capture_decls(size_t n, const CaptureDecl *d);      /* OP_CAPTURE_*: payload a */
uint64_t net_scope_args(size_t n, const Val *args);              /* OP_APPLY_SCOPE: payload a */

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

typedef enum { NT_APPLY_TRANSFORM = 1, NT_CONTINUE_REFERENCE } NetTraceKind;
typedef struct { NetTraceKind kind; uint64_t transform; int dir; MapId sigma; RefId arg, result; uint64_t K; } NetTraceEvent;

/* Nodes live in non-moving storage and are never freed during a run, so a
 * worker holding a NodeId can always dereference it (pinning is trivial);
 * generations detect stale identity. A replacement locks the redex owners
 * and every surviving boundary owner in a consistent total order (by id),
 * revalidates the redex and its boundary, installs, publishes and retires,
 * then enqueues the new active pairs after releasing the locks (§20). */
typedef struct Net {
    Chunked nodes; size_t nnodes;
    pthread_mutex_t alloc_mu;
    VEC(Active) active;       /* candidate active pairs (by one member, with generation) */
    pthread_mutex_t act_mu; pthread_cond_t act_cv, idle_cv;
    size_t outstanding; bool stop;   /* §35: queued + executing active pairs */
    pthread_t *workers; size_t nworkers;
    size_t rewrites; const struct XCarry *rewrites_cx;   /* V23 R5: each count is exact — the word is its low digit, the list its carries (xcount.h) */
    /* local rule instances by class (diamond-balanced event classes), committed only */
    size_t n_op, n_dup, n_erase, n_eval_deliver; const struct XCarry *n_op_cx, *n_dup_cx, *n_erase_cx, *n_eval_deliver_cx;
    size_t n_apply, n_continue; const struct XCarry *n_apply_cx, *n_continue_cx;   /* §43/§45: APPLY_TRANSFORM and CONTINUE_REFERENCE rule events */
    size_t retries; const struct XCarry *retries_cx;   /* diagnostics: replacements abandoned after revalidation */
    /* §73.3(1): identity applications of the actual run, in commit order.
     * APPLY: (transform, dir, σ, argument, result reference, receiving
     * producer key K when the result port is a CONTINUE_REFERENCE(K));
     * CONTINUE: (K, forwarded reference). */
    VEC(NetTraceEvent) trace; pthread_mutex_t trace_mu;
    /* §43: when shared is set, pending active pairs are jobs of the shared
     * scheduler: pushes count in *shared.outstanding under *shared.mu and
     * signal *shared.cv; the shared scheduler pops them (net_pop_pair) and
     * steps them (net_step_pair) and does its own finish accounting. */
    struct { pthread_mutex_t *mu; pthread_cond_t *cv; size_t *outstanding; } shared;
    int policy;               /* 0 LIFO, 1 FIFO, 2 random (sequential selection only) */
    uint64_t rng;
} Net;

void net_init(Net *n);
void net_free(Net *n);
size_t net_trace_count(Net *n);
NetTraceEvent net_trace_get(Net *n, size_t i);
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
void net_share_scheduler(Net *n, pthread_mutex_t *mu, pthread_cond_t *cv, size_t *outstanding);
bool net_pop_pair_locked(Net *n, Active *out);         /* caller holds shared.mu */
size_t net_pending_pairs_locked(const Net *n);
bool net_step_pair(Net *n, Active a);                  /* one candidate pair; true when a replacement was committed */
#define net_step_pair_PARAMS(X) X(Net *, n) X(Active, a)
KF_PROTO(net_step_pair, bool, net_step_pair_PARAMS);  /* the same step as a frame family (kframe.h) */
/* run local rules until no active pair remains; returns rewrite count */
size_t net_run(Net *n);
/* evaluation requests suspended in the cache are resumed by the eval
 * scheduler; this drives both until quiescent */
size_t net_run_with_eval(Net *n);
/* read a result descriptor's payload through a root's negative port */
bool net_root_read(const Net *n, NodeId root, NodeKind *kind, Payload *p);

void test_net(void);

#endif

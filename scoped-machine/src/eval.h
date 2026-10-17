/* eval.h — face-sensitive evaluation cache and weak-head evaluator (§10–13).
 *
 *   observation = whnf(reference, ambient_face)
 *   EvalKey(t, chi) = (t, π_{S(t)}(chi))
 *
 * Evaluation is asynchronous: a demand for another key suspends a
 * continuation; the scheduler never blocks on a running key. A reentrant
 * demand for a running key is left suspended and is never published as a
 * neutral or ready result.
 */
#ifndef CUBICAL_EVAL_H
#define CUBICAL_EVAL_H

#include "term.h"
#include "shape.h"
struct Net;

typedef enum {
    R_INTRODUCTION = 1,
    R_NEUTRAL,
    R_SYSTEM,
    R_NO_OBSERVATION,   /* host control status: ambient face is false */
    R_INVALID           /* host control status: invalid occurrence / ill-typed demand */
} ResultClass;

typedef struct EvalResult {
    ResultClass cls;
    RefId ref;          /* INTRODUCTION/NEUTRAL: reference whose open() is the head;
                         * SYSTEM: the owner system reference */
    size_t nbr;         /* SYSTEM: covered, consistent branches */
    FaceId *faces;
    RefId *terms;
    const char *message;/* INVALID: diagnostic */
    struct EvalResult *all_next;   /* every result, for teardown (an intrusive list: no growth under res_mu) */
} EvalResult;

typedef uint64_t EntryId;
typedef enum { E_UNEVALUATED = 0, E_RUNNING, E_READY } EntryState;

typedef struct Cont Cont;

typedef struct {
    RefId ref;
    FaceId face;        /* the projected face the entry is evaluated under */
    EntryState state;
    EvalResult *result; /* present exactly when READY */
    VEC(Cont *) waiters;
    size_t runs;        /* EVALUATE tasks executed for this key (must be ≤ 1) */
    size_t n_req, n_deliver, n_pub;   /* per-key event counts (for schedule comparison) */
    size_t steps;       /* §60 trace: EVALUATE/RESUME frame steps charged to this producer */
    uint64_t env;       /* the environment version at the key's creation (§79.2: a running producer stays tied to its snapshot) */
    VEC(EntryId) deps;  /* §60 trace: consumer occurrences owned by this producer, in request order (slot = index): the historical request edges */
    VEC(uint8_t) dep_hist;   /* LIVE-CUT-ADOPTION §5: 1 when the occurrence at that index was superseded by an adoption (historical, not an active-slot edge) */
    /* §76.3 / §78 / §79: the structural computation identity, the historical
     * chain under the same (shape, face), the answer's residual and receipt,
     * and the symbol revisions the answer actually read */
    ShapeId shape;
    EntryId next_alt;
    RefId residual; uint64_t receipt;
    VEC(uint64_t) gdeps;        /* pairs (symbol, revision) */
    RefId adapter; uint64_t adapter_prefix; EntryId adapter_src;   /* §78.3–78.4: continue from a completed receipt instead of evaluating the body */
    bool is_alias;              /* §76.3: published as the residual of another producer's answer; it never ran a body */
    struct PrefixFact *prefix_head;   /* §84.2: the latest committed prefix fact of this producer (immutable facts, newest first; published with release) */
    size_t n_prefix;                  /* facts published (under mu) */
    const struct PrefixFact *adapter_fact;   /* the immutable prefix fact this producer continued from, or NULL */
    struct KCont *exec_kc; uint64_t exec_job;   /* V21 R2: the continuation (and its job) executing a task of this producer now, or NULL */
    struct ReuseScope *scope;         /* V21 R3: the accounting owner of this producer's tasks (the launching request's scope), referenced */
    pthread_mutex_t mu; /* guards state, result, waiters and the counters above */
} Entry;

typedef enum { W_OK = 0, W_NO_OBSERVATION, W_INVALID, W_STUCK } WhnfStatus;

void eval_init(void);
void eval_free(void);
void eval_reset(void);           /* retire all observations; keep workers and policies (new environment session) */

/* Request the observation of t under chi; k receives the result. */
void eval_request(RefId t, FaceId chi, Cont *k);
/* Synchronous driver: request, run the scheduler, return the root result.
 * W_STUCK: the runnable queue emptied with the root still pending (cyclic
 * or otherwise suspended demand); nothing was published for it. */
EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status);

/* Observation of an occurrence (§2): validates the occurrence against its
 * context (declared variables and dimensions, declared types by identity,
 * assumption entails the required face) and then observes under the
 * context's assumption. An invalid occurrence yields W_INVALID. */
EvalResult *whnf_in(RefId t, ContextId ctx, WhnfStatus *status);

/* run queued evaluation tasks until the queue is empty; returns tasks run.
 * With a worker pool, waits until the ready multiset is empty and every
 * worker is idle. */
size_t eval_run(void);
/* start n worker threads (0 = sequential, the default); replaces any pool */
void eval_set_workers(size_t n);
size_t eval_workers(void);

/* Interaction-work vector (§26–§29). REQUEST is one event class whatever the
 * entry state; the hit counters are diagnostics only (not diamond-balanced). */
typedef struct {
    size_t request;      /* REQ events (entry formed; false-face and invalid requests excluded) */
    size_t eval_step;    /* evaluator frame steps: EVALUATE and RESUME jobs executed */
    size_t publish;      /* PUB events */
    size_t deliver;      /* DELIVER events (ready hit or publication) */
    size_t ready_hit, running_hit, launch;   /* diagnostics */
} EvalEvents;
EvalEvents eval_events(void);

/* Job selection policy of the sequential scheduler. The abstract machine's
 * reductions commute (§25–§27), so the event vector and the observed normal
 * form (up to renaming of allocated identities) must not depend on it. */
typedef enum { POL_FIFO = 0, POL_LIFO, POL_RANDOM } SchedPolicy;
void eval_set_policy(SchedPolicy p, uint64_t seed);
/* §43: the evaluator's net holds the APPLY_TRANSFORM / CONTINUE_REFERENCE
 * pairs as jobs of the same scheduler (one outstanding count); the pair queue
 * has its own selection policy */
void eval_set_pair_policy(SchedPolicy p, uint64_t seed);
typedef struct { size_t apply, continue_ref, op, eval_deliver, retries; } EvalNetEvents;
EvalNetEvents eval_net_events(void);
struct Net *eval_net(void);
void eval_forward_result(EntryId K, RefId v);        /* the receiver's request (net rule) */

/* cache introspection (tests) */
EntryId eval_entry_lookup(RefId t, FaceId chi);     /* 0 when absent */
EntryState eval_entry_state(EntryId e);
FaceId eval_entry_face(EntryId e);
size_t eval_entry_count(void);
size_t eval_entry_runs(EntryId e);
size_t eval_running_count(void);
RefId eval_entry_ref(EntryId e);
void eval_entry_events(EntryId e, size_t *req, size_t *deliver, size_t *pub);                    /* entries currently RUNNING */
size_t eval_task_count(void);                       /* EVALUATE tasks created so far */

/* §60 / §73 trace of the actual run: every request is a consumer occurrence
 * (owner producer key or 0 for a root/external request, slot = its ordinal
 * among the owner's occurrences, requested key). Root occurrences are
 * numbered globally in request order. */
size_t eval_entry_deps(EntryId e, EntryId **out);   /* copies the owner's occurrences; caller frees *out */
size_t eval_entry_steps(EntryId e);
uint64_t eval_entry_env(EntryId e);
ShapeId eval_entry_shape(EntryId e);
/* §78: the answer's residual (the expression after the established
 * reduction prefix) and its reduction receipt; 0 for an unsuccessful or
 * unpublished entry */
RefId eval_entry_residual(EntryId e);
uint64_t eval_entry_receipt(EntryId e);
size_t eval_entry_gdeps(EntryId e, const uint64_t **pairs);   /* (symbol, revision) pairs the answer read */
bool eval_entry_deps_valid(EntryId e);                       /* every recorded revision is current */
EntryId eval_entry_adapter_source(EntryId e);                /* the entry whose receipt this producer continued from, or 0 */
bool eval_entry_is_alias(EntryId e);
/* receipt records: [RC_REFL, t] | [RC_SEQ, first, then] | [RC_RULE, rule, x, y] | [RC_RESTRICT, source entry, face] | [RC_SPEC, source entry, map]
 * | [RC_PREFIX_RESTRICT, prefix fact, face] | [RC_PREFIX_SPEC, prefix fact, map] (§84.2: an adapter from an immutable committed prefix) */
enum { RC_REFL = 1, RC_SEQ, RC_RULE, RC_RESTRICT, RC_SPEC, RC_PREFIX_RESTRICT, RC_PREFIX_SPEC };
enum { RR_CONG_APP = 1, RR_CONG_FST, RR_CONG_SND, RR_CONG_PAPP, RR_CONG_UNGLUE, RR_CONG_COMP, RR_BETA, RR_FST, RR_SND, RR_PATH_BETA, RR_ENDPOINT, RR_UNFOLD, RR_GLUE, RR_SYSTEM, RR_SYSTEM_DIST, RR_COMP_TUBE, RR_COMP_EXPAND, RR_IDENTITY_APPLY, RR_SYSTEM_BRANCH };
const uint64_t *eval_receipt_words(uint64_t receipt, size_t *n);

/* §84.2 committed prefixes. A prefix fact is the immutable judgment
 * face ⊢ source ⇒* residual, with its receipt and the (symbol, revision)
 * premises the derivation used; a RUNNING producer publishes one at each
 * forwarding cut (STEP / SEQ) and lifts a child's fact through its pending
 * eliminator (CONTEXT). A fact is not a READY answer: the completed-answer
 * accessors above are unchanged. */
typedef struct PrefixFact {
    uint64_t id;                 /* 1, 2, ... in publication order (machine-wide) */
    EntryId src;                 /* the producer that published it */
    RefId source; FaceId face;   /* the judgment's source and face (the producer's key face) */
    RefId residual;              /* the cut it reached */
    uint64_t receipt;            /* the receipt DAG of source ⇒* residual */
    const uint64_t *gdeps; size_t ngdeps;   /* (symbol, revision) pairs the derivation used */
    EntryId origin;              /* the producer whose own rule committed the first step (a lift never returns to it) */
    struct PrefixFact *next;     /* the producer's previous fact */
    struct PrefixFact *all_next; /* every fact, for teardown */
    const struct PrefixFact *shape_next;   /* LIVE-CUT-ADOPTION: the previous fact of the same source shape (the subscription index) */
} PrefixFact;
const PrefixFact *eval_entry_prefix(EntryId e);              /* the latest committed prefix of e, or NULL (pinned: facts are immutable) */
size_t eval_entry_prefix_count(EntryId e);
const PrefixFact *eval_entry_adapter_fact(EntryId e);        /* the prefix fact this producer continued from, or NULL */
bool eval_prefix_valid(const PrefixFact *f);                 /* every recorded revision is current */
typedef struct { size_t published, lifted, notify_steps, adapters; } EvalPrefixEvents;
EvalPrefixEvents eval_prefix_events(void);
size_t eval_root_occurrences(EntryId **out);        /* copies the root occurrence list; caller frees *out */

/* LIVE-CUT-ADOPTION. Every producer-owned request slot (an eliminator's
 * child, a forwarding request, each join slot, the net's suspended
 * subrequest) is a Cut: source s0, occurrence face, immutable resume recipe,
 * state WAITING | RESUMING | CLOSED, its current generation (residual r,
 * receipt q : s0 ⇒* r, dependency certificate) and owned tickets. A fact of
 * another producer whose source is r (or reindexes to r along a recorded
 * instantiation edge) at a face the occurrence entails is prepared as a
 * proposal outside every lock and installed under the Cut's lock only if the
 * Cut is still WAITING at the captured generation and the environment stamp
 * is the validated one (a changed stamp revalidates the premises first). The
 * installation issues an ordinary request for the adapted residual through a
 * new ticket; a delivery resumes the slot only for the current generation
 * (WAITING → RESUMING once); a superseded ticket's delivery is consumed with
 * no semantic resume. */
typedef struct {
    size_t cuts, subscriptions, replays, notices, edge_watches;
    size_t proposals, prep_steps, prep_computed, prep_shared, prep_rejected;
    size_t installs, install_stale_generation, install_not_waiting, revalidations, revalidation_failed;
    size_t tickets, deliveries_current, deliveries_stale, resumes, retired_tickets, cuts_freed;
} EvalCutEvents;
EvalCutEvents eval_cut_events(void);
size_t eval_entry_active_deps(EntryId e, EntryId **out);   /* the active-slot edges (historical edges excluded); caller frees *out */
/* scheduler policy (tests): a held job is set aside (not outstanding) until
 * released; a budgeted run executes at most n jobs (sequential scheduler) */
typedef enum { ET_EVALUATE = 1, ET_RESUME, ET_NOTIFY, ET_PAIR, ET_SUBSCRIBE, ET_REPLAY, ET_NOTICE, ET_PREPARE, ET_INSTALL, ET_REQUEST, ET_EDGE } EvalTaskKind;
typedef struct { EvalTaskKind kind; EntryId producer; EntryId child; bool ticket; const struct PrefixFact *fact; } EvalTaskInfo;   /* fact: the proposal's fact (PREPARE / INSTALL), the noticed or replayed fact */
void eval_set_hold(bool (*pred)(const EvalTaskInfo *, void *), void *ctx);
size_t eval_release_held(void);
size_t eval_held_count(void);
size_t eval_run_budget(size_t max_jobs);

/* continuation constructors used by the net layer */
typedef void (*ExternalDeliver)(void *ctx, EvalResult *r);
Cont *cont_external(ExternalDeliver fn, void *ctx, void (*free_ctx)(void *));   /* free_ctx releases ctx if never delivered */

void print_result(const EvalResult *r, FILE *f);

#endif

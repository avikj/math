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

typedef enum {
    R_INTRODUCTION = 1,
    R_NEUTRAL,
    R_SYSTEM,
    R_NO_OBSERVATION,   /* host control status: ambient face is false */
    R_INVALID           /* host control status: invalid occurrence / ill-typed demand */
} ResultClass;

typedef struct {
    ResultClass cls;
    RefId ref;          /* INTRODUCTION/NEUTRAL: reference whose open() is the head;
                         * SYSTEM: the owner system reference */
    size_t nbr;         /* SYSTEM: covered, consistent branches */
    FaceId *faces;
    RefId *terms;
    const char *message;/* INVALID: diagnostic */
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
} Entry;

typedef enum { W_OK = 0, W_NO_OBSERVATION, W_INVALID, W_STUCK } WhnfStatus;

void eval_init(void);
void eval_free(void);

/* Request the observation of t under chi; k receives the result. */
void eval_request(RefId t, FaceId chi, Cont *k);
/* Synchronous driver: request, run the scheduler, return the root result.
 * W_STUCK: the runnable queue emptied with the root still pending (cyclic
 * or otherwise suspended demand); nothing was published for it. */
EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status);

/* run queued evaluation tasks until the queue is empty; returns tasks run */
size_t eval_run(void);

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
typedef enum { SCHED_FIFO = 0, SCHED_LIFO, SCHED_RANDOM } SchedPolicy;
void eval_set_policy(SchedPolicy p, uint64_t seed);

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

/* continuation constructors used by the net layer */
typedef void (*ExternalDeliver)(void *ctx, EvalResult *r);
Cont *cont_external(ExternalDeliver fn, void *ctx);

void print_result(const EvalResult *r, FILE *f);

#endif

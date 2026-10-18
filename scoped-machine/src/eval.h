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
    struct EvalResult *next_alloc;   /* the machine's list of rooted results */
} EvalResult;

typedef enum { W_OK = 0, W_NO_OBSERVATION, W_INVALID, W_STUCK } WhnfStatus;
typedef uint64_t EntryId;
typedef enum { E_UNEVALUATED = 0, E_RUNNING, E_READY } EntryState;

/* ---- the one execution protocol (§26), for every operation family ----
 *
 * A producer key is (family, a, b, environment version). Its entry moves
 * U → R → D by compare-and-swap on `head`: NULL is U; the first requester
 * installs itself as the only waiter and launches the one evaluator; later
 * requesters push onto the waiter stack; publication stores the value and
 * exchanges the stack for ENTRY_READY. Each delivery is its own job. Every
 * transition is a bounded number of word operations. */
typedef uint32_t Family;
enum { F_WHNF = 1, F_MAX = 64 };

typedef struct Cont Cont;
typedef struct Gather Gather;
typedef struct RootBox RootBox;
typedef void (*ExternalDeliver)(void *ctx, EvalResult *r);

typedef enum {
    K_ROOT = 1, K_FORWARD, K_APP, K_FST, K_SND, K_PAPP, K_UNGLUE, K_COMP_FAMILY, K_BRANCH, K_EXTERNAL,
    K_FRAME            /* a family frame: resumed by its family's resume function */
} ContKind;

/* A continuation is single-consumer. A frame (K_FRAME) is the retained state
 * of one producer of a family between two of its steps: program counter and
 * bounded locals (w, and a fixed-size locals record of its family). A frame
 * that requests its next child sets `keep` in its resume function and is
 * reused as that child's continuation. A subroutine frame has no entry: it
 * returns its value to its parent frame. */
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
    /* K_FRAME */
    Family fam; uint32_t pc; bool keep;
    bool inl;           /* driven by the synchronous inline driver (family_call) */
    uint64_t w[8];
    void *loc;          /* the family's locals record (loc_size bytes, zeroed), or NULL */
    Cont *parent;       /* subroutine frame: the frame its value returns to */
    Cont *next;         /* link in an entry's waiter stack / a delivery chain */
};

typedef struct {
    Cont *head;         /* NULL: U; ENTRY_READY: D; otherwise R with this waiter stack */
    uint64_t value;     /* published result (an EvalResult* for F_WHNF) */
    size_t runs;        /* evaluator tasks executed for this key (must be ≤ 1) */
    size_t n_req, n_deliver, n_pub;   /* per-key event counts (for schedule comparison) */
    EntryState state;   /* diagnostic mirror of head */
} Entry;

typedef void (*FamStart)(EntryId e, uint64_t a, uint64_t b);
typedef void (*FamResume)(Cont *k, uint64_t v);
/* register a family (once per process, before use); returns its id */
Family family_register(const char *name, FamStart start, FamResume resume);
/* request the producer (f,a,b); k receives its value */
void family_request(Family f, uint64_t a, uint64_t b, Cont *k);
/* publish the value of a running entry (from its evaluator's last step) */
void family_publish(EntryId e, uint64_t v);
/* a fresh frame of family f whose producer publishes into dest */
Cont *frame_new(Family f, EntryId dest);
/* synchronous driver: request (f,a,b) and run jobs until it publishes */
uint64_t family_run(Family f, uint64_t a, uint64_t b, WhnfStatus *status);
Family eval_entry_family(EntryId e);
uint64_t eval_entry_a(EntryId e);
uint64_t eval_entry_b(EntryId e);
size_t family_steps(Family f);       /* evaluator and resume steps executed for family f */

/* ---- frame programs ----
 * A frame family is defined by one step function `step(k, v)`: the frame's
 * program counter selects where it continues, v is the value its last
 * child (producer or subroutine) delivered, 0 at the first step. A step does
 * a bounded amount of work and ends in exactly one of
 *   frame_request(k, f, a, b)   await the producer (f, a, b)
 *   frame_call(k, child)        await the subroutine frame `child`
 *   frame_yield(k)              continue at the next step
 *   frame_finish(k, v)          publish v (producer) / return v (subroutine)
 * The producer key of a frame family is (f, a, b) and its frame starts with
 * w[0] = a, w[1] = b. A pure family's key does not include the definition
 * environment version: its value depends on its operands alone. */
Family family_define(const char *name, FamResume step, size_t loc_size, bool pure);
Family family_lookup(const char *name);           /* 0 when not registered */
void frame_request(Cont *k, Family f, uint64_t a, uint64_t b);
void frame_call(Cont *k, Cont *child);
void frame_yield(Cont *k);
void frame_finish(Cont *k, uint64_t v);
Cont *frame_sub(Family f, const Cont *caller);    /* a subroutine frame of family f for caller */
/* The synchronous driver (PLAN §5) for code that is not yet a frame program,
 * valid inside and outside jobs, never blocking: a ready key returns its
 * value; an unevaluated key is claimed and its producer is driven to
 * publication on this thread (waiters that arrive meanwhile are delivered by
 * that publication); a key running elsewhere is computed on this thread
 * without publication. It drives the same step functions. */
uint64_t family_call(Family f, uint64_t a, uint64_t b);

/* the interning subroutine: inserts the record held by *buf into t (the
 * buffer's pages are released), returning its id; *created (when non-NULL,
 * in storage that outlives the call) tells whether it was new */
Cont *intern_sub(const Cont *caller, Interner *t, WordBuf *buf, bool *created);
/* the set, interval and face families (dnfam.c), registered by eval_init */
void dnf_families_init(void);
void subst_families_init(void);   /* maps and substitution (subst.c) */

/* program-counter macros for step functions (the step's value parameter is
 * named v; one macro use per source line) */
#define FR_BEGIN(k) switch ((k)->pc) { case 0:;
#define FR_AWAIT(k, var, f, a, b) do { (k)->pc = __LINE__; frame_request((k), (f), (a), (b)); return; case __LINE__:; (var) = v; } while (0)
#define FR_CALL(k, var, child) do { (k)->pc = __LINE__; frame_call((k), (child)); return; case __LINE__:; (var) = v; } while (0)
#define FR_YIELD(k) do { (k)->pc = __LINE__; frame_yield(k); return; case __LINE__:; } while (0)
#define FR_FINISH(k, val) do { frame_finish((k), (val)); return; } while (0)
#define FR_END(k) } die("frame program ended without finishing (pc %u)", (unsigned)(k)->pc)
#define FR_LOC(k, T) ((T *)(k)->loc)


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
size_t eval_entry_count(void);                       /* entry ids reserved (some may be unused after a lost insertion race) */
bool eval_entry_live(EntryId e);                    /* e names a key */
bool eval_entry_is_observation(EntryId e);          /* a live F_WHNF key */
size_t eval_entry_runs(EntryId e);
size_t eval_running_count(void);
RefId eval_entry_ref(EntryId e);
void eval_entry_events(EntryId e, size_t *req, size_t *deliver, size_t *pub);                    /* entries currently RUNNING */
size_t eval_task_count(void);                       /* EVALUATE tasks created so far */

/* continuation constructors used by the net layer */
Cont *cont_external(ExternalDeliver fn, void *ctx, void (*free_ctx)(void *));   /* free_ctx releases ctx if never delivered */

void print_result(const EvalResult *r, FILE *f);

#endif

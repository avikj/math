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
#include "count.h"

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
enum { F_WHNF = 1, F_MAX = 128 };

typedef struct Cont Cont;
typedef struct Join Join;
typedef struct RootBox RootBox;
typedef void (*ExternalDeliver)(void *ctx, EvalResult *r);

typedef enum {
    K_ROOT = 1, K_JOIN, K_EXTERNAL,
    K_FRAME            /* a family frame: resumed by its family's step function */
} ContKind;

/* A continuation is single-consumer. A frame (K_FRAME) is the retained state
 * of one producer of a family between two of its steps: program counter and
 * bounded locals (w, and a fixed-size locals record of its family). A frame
 * that requests its next child marks itself kept (the executing job's flag)
 * and is reused as that child's continuation. A subroutine or launched frame
 * has no entry: it returns its value to its parent continuation. */
struct Cont {
    ContKind kind;
    EntryId dest;       /* entry to publish into (not for ROOT/EXTERNAL) */
    EntryId owner;      /* FRAME: the entry whose producer this frame serves (0: a host-driven frame) */
    FaceId chi;         /* ambient face of the demanding evaluation */
    Join *join; size_t box;          /* JOIN: the join and the box */
    RootBox *root;                   /* ROOT */
    ExternalDeliver ext_fn; void *ext_ctx; void (*ext_free)(void *);   /* EXTERNAL */
    /* K_FRAME */
    Family fam; uint32_t pc;
    uint64_t w[8];
    void *loc;          /* the family's locals record (loc_size bytes, zeroed), or NULL */
    Cont *parent;       /* subroutine frame: the frame its value returns to */
    Cont *next;         /* link in an entry's waiter stack / a delivery chain */
    bool disposed;      /* teardown: its owned resources were released (a join frame is reached once per box) */
};

typedef struct {
    Cont *head;         /* NULL: U; ENTRY_READY: D; otherwise R with this waiter stack */
    uint64_t value;     /* published result (an EvalResult* for F_WHNF) */
    size_t runs;        /* evaluator tasks executed for this key (must be ≤ 1) */
    Count work;         /* steps of its producer's frame and subroutines (exact) */
    EntryId *deps; size_t ndeps, capdeps;   /* the entries its producer requested */
    int ledger_lk;      /* work and deps: written by the producer's frames, which may run concurrently (branches) */
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
/* The synchronous embedding for an external caller (never inside a counted
 * step, where a request suspends the frame): submit the root (f, a, b) and
 * drive the ordinary scheduler until it is delivered. */
uint64_t family_call(Family f, uint64_t a, uint64_t b);

/* the interning subroutine: inserts the record held by *buf into t (the
 * buffer's pages are released), returning its id; *created (when non-NULL,
 * in storage that outlives the call) tells whether it was new */
Cont *intern_sub(const Cont *caller, Interner *t, WordBuf *buf, bool *created);
/* the set, interval and face families (dnfam.c), registered by eval_init */
void dnf_families_init(void);
void subst_families_init(void);   /* maps and substitution (subst.c) */
void construct_families_init(void);   /* constructions, fields, binders, variables (construct.c) */

/* program-counter macros for step functions (the step's value parameter is
 * named v; one macro use per source line; never inside a nested switch
 * statement, whose case labels would capture the resumption points) */
#define FR_BEGIN(k) switch ((k)->pc) { case 0:;
#define FR_AWAIT(k, var, f, a, b) do { (k)->pc = __LINE__; frame_request((k), (f), (a), (b)); return; case __LINE__:; (var) = v; } while (0)
#define FR_CALL(k, var, child) do { (k)->pc = __LINE__; frame_call((k), (child)); return; case __LINE__:; (var) = v; } while (0)
#define FR_YIELD(k) do { (k)->pc = __LINE__; frame_yield(k); return; case __LINE__:; } while (0)
#define FR_FINISH(k, val) do { frame_finish((k), (val)); return; } while (0)
#define FR_END(k) } die("frame program ended without finishing (pc %u)", (unsigned)(k)->pc)
#define FR_LOC(k, T) ((T *)(k)->loc)

/* joins: a frame issues independent demands (one per step) into the boxes of
 * a join, then awaits all of them with FR_JOIN; box i holds the value of
 * demand i. A demand is a producer request or a subroutine call. */
Join *join_new(Cont *frame, size_t n);
void join_request(Join *j, size_t i, Family f, uint64_t a, uint64_t b);
void join_call(Join *j, size_t i, Cont *child);
uint64_t join_value(const Join *j, size_t i);
void join_fill(Join *j, size_t i, uint64_t v);   /* a box whose value needs no demand */
void join_free(Join *j);
void *frame_mem(size_t bytes);               /* frame-owned block: released by frame_mem_free, or at teardown if the frame is stuck */
void frame_mem_free(void *p);
void frame_await_join(Cont *k, Join *j);
void frame_launch(Cont *f, Cont *parent);      /* run frame f; its value resumes parent (any continuation) */
uint64_t frame_run(Cont *f, WhnfStatus *status);
uint64_t family_run_budget(Family f, uint64_t a, uint64_t b, size_t budget, WhnfStatus *status);   /* at most budget jobs (0: unlimited) */
/* subroutines for frames: an observation under pins (value: EvalResult*),
 * a construction request (value: RefId), a request record already built */
Cont *observe_sub(const Cont *caller, RefId x, FaceId chi, uint64_t pins);
Cont *construct_sub(const Cont *caller, Tag tag, uint64_t payload, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b);
Cont *construct_buf_sub(const Cont *caller, WordBuf *w);   /* outside jobs: a detached frame driven to its value */
#define FR_JOIN(k, j) do { (k)->pc = __LINE__; frame_await_join((k), (j)); return; case __LINE__:; } while (0)


void eval_init(void);
void eval_free(void);
void eval_reset(void);           /* retire all observations; keep workers and policies (new environment session) */

/* Request the observation of t under chi; k receives the result. */
void eval_request(RefId t, FaceId chi, Cont *k);                       /* under the current revisions of t's premises */
void eval_request_pinned(RefId t, FaceId chi, uint64_t pins, Cont *k);  /* under a pin set (pins.h) */
/* Synchronous driver: request, run the scheduler, return the root result.
 * W_STUCK: the runnable queue emptied with the root still pending (cyclic
 * or otherwise suspended demand); nothing was published for it. */
EvalResult *whnf(RefId t, FaceId chi, WhnfStatus *status);
EvalResult *whnf_pinned(RefId t, FaceId chi, uint64_t pins, WhnfStatus *status);

/* Observation of an occurrence (§2): validates the occurrence against its
 * context (declared variables and dimensions, declared types by identity,
 * assumption entails the required face) and then observes under the
 * context's assumption. An invalid occurrence yields W_INVALID. */

/* run queued evaluation tasks until the queue is empty; returns tasks run.
 * With a worker pool, waits until the ready multiset is empty and every
 * worker is idle. */
void eval_run(void);
/* start n worker threads (0 = sequential, the default); replaces any pool */
void eval_set_workers(size_t n);
size_t eval_workers(void);

/* Readings (§60): protocol events and steps per family, exact counts kept
 * in one shard per executing thread and summed on demand (count.h). */
typedef enum { RD_REQUEST, RD_DELIVER, RD_PUBLISH, RD_LAUNCH, RD_STEP, RD_STEPS } Reading;   /* RD_STEPS: of family f */
void eval_reading(Reading r, Family f, Exact *out);   /* out += the reading */
/* work of a set of producers (§60, EFFECT-AUTHORITY §8): the union of their
 * dependency supports, each producer's work counted once; *support is the
 * number of producers in the union. Outside jobs, over completed producers. */
void eval_work(size_t n, const EntryId *roots, Exact *out, size_t *support);
EntryId eval_entry_find(Family f, uint64_t a, uint64_t b);   /* the entry of a key, 0 if never requested */


/* cache introspection (tests) */
EntryState eval_entry_state(EntryId e);
size_t eval_entry_count(void);                       /* entry ids reserved (some may be unused after a lost insertion race) */
bool eval_entry_live(EntryId e);                    /* e names a key */
size_t eval_entry_runs(EntryId e);

/* an external receiver of a root request */
Cont *cont_external(ExternalDeliver fn, void *ctx, void (*free_ctx)(void *));   /* free_ctx releases ctx if never delivered */

void print_result(const EvalResult *r, FILE *f);

#endif

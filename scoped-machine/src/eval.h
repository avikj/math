/* eval.h — the one execution protocol and the weak-head evaluator (§10–13, §26).
 *
 *   observation = whnf(reference, ambient_face)
 *   EvalKey(t, chi) = (t, π_{S(t)}(chi))
 *
 * Every computation is a producer keyed by (family, a, b). Its entry moves
 * U → R → D by compare-and-swap on `head`: NULL is U; the first requester
 * installs the one producer; a launch installs it with no waiter (R(∅));
 * later requesters push onto the waiter stack; publication stores the value
 * and exchanges the stack for READY. Each delivery is its own job. A value
 * is an interned record or a word; an entry is the only box a value is
 * returned to.
 */
#ifndef CUBICAL_EVAL_H
#define CUBICAL_EVAL_H

#include "term.h"
#include "count.h"
#include "families.h"

typedef enum {
    R_INTRODUCTION = 1,
    R_NEUTRAL,
    R_SYSTEM,
    R_NO_OBSERVATION,   /* host control status: ambient face is false */
    R_INVALID           /* host control status: invalid occurrence / ill-typed demand */
} ResultClass;

/* An observation's value is the interned record
 *   [class, (face, term)*, ref, message]
 * (the branches of a SYSTEM result; ref the head reference, or the owner
 * system of a SYSTEM; message the diagnostic of INVALID). EvalResult is
 * its decoded view; br points into the record. */
typedef struct {
    ResultClass cls;
    RefId ref;
    size_t nbr;
    const uint64_t *br;     /* face of branch q: br[2q]; term: br[2q+1] */
    const char *message;
} EvalResult;
EvalResult res_get(uint64_t v);

typedef enum { W_OK = 0, W_NO_OBSERVATION, W_INVALID, W_STUCK } WhnfStatus;
typedef uint64_t EntryId;
typedef enum { E_UNEVALUATED = 0, E_RUNNING, E_READY } EntryState;

typedef uint32_t Family;
enum { F_MAX = 128 };

/* A frame is the retained state of one producer of a family between two of
 * its steps: program counter and bounded locals (w, and a fixed-size locals
 * record of its family). A frame that requests its next child marks itself
 * kept (the executing job's flag) and is reused as that child's
 * continuation. A subroutine frame has no entry: it returns its value to its
 * parent frame. The frame is the only continuation form. */
typedef struct Cont Cont;
struct Cont {
    EntryId dest;       /* entry to publish into (0: a subroutine or a host frame) */
    EntryId owner;      /* the entry whose producer this frame serves (0: a host frame) */
    Family fam; uint32_t pc;
    uint64_t w[8];
    void *loc;          /* the family's locals record (loc_size bytes, zeroed), or NULL */
    Cont *parent;       /* subroutine frame: the frame its value returns to */
    Cont *next;         /* link in an entry's waiter stack / a delivery chain */
};

typedef struct DepNode { EntryId e; struct DepNode *next; } DepNode;
typedef struct {
    Cont *head;         /* NULL: U; ENTRY_READY: D; ENTRY_LAUNCHED: R(∅); otherwise R with this waiter stack */
    uint64_t value;     /* published result */
    size_t runs;        /* evaluator tasks executed for this key (must be ≤ 1) */
    Count work;         /* steps of its producer's frame and subroutines (exact; single writer) */
    DepNode *deps;      /* the entries its producer requested or launched (pushed by its one producer) */
} Entry;

typedef void (*FamResume)(Cont *k, uint64_t v);

/* ---- frame programs ----
 * A frame family is defined by one step function `step(k, v)`: the frame's
 * program counter selects where it continues, v is the value its last
 * child (producer or subroutine) delivered, 0 at the first step. A step does
 * a bounded amount of work and ends in exactly one of
 *   frame_request(k, f, a, b)   await the producer (f, a, b)
 *   frame_call(k, child)        await the subroutine frame `child`
 *   frame_yield(k)              continue at the next step
 *   frame_finish(k, v)          publish v (producer) / return v (subroutine)
 * A step may also launch a bounded number of producers (family_launch):
 * independent demands are launched first and then awaited, every launched
 * key before the frame finishes (a parent publishes only after every child
 * it launched has delivered). The producer key of a frame family is
 * (f, a, b) and its frame starts with w[0] = a, w[1] = b. */
void family_define(Family f, const char *name, FamResume step, size_t loc_size);   /* a fixed family (families.h) */
Family family_new(const char *name, FamResume step, size_t loc_size);         /* a family defined at run time */
void frame_request(Cont *k, Family f, uint64_t a, uint64_t b);
void frame_call(Cont *k, Cont *child);
void frame_yield(Cont *k);
void frame_finish(Cont *k, uint64_t v);
void family_launch(Family f, uint64_t a, uint64_t b);   /* inside a step: start (f, a, b) without awaiting it */
Cont *frame_sub(Family f, const Cont *caller);    /* a subroutine frame of family f for caller */

/* Root driving (never inside a counted step, where a request suspends the
 * frame): an outside caller requests the root key with a host frame and
 * drives the ordinary scheduler until the key is published. */
uint64_t family_run(Family f, uint64_t a, uint64_t b, WhnfStatus *status);
uint64_t family_call(Family f, uint64_t a, uint64_t b);   /* family_run that must complete */
/* a root bounded by the work of its own dependency support: the value when
 * the root completes with W(support) ≤ budget, otherwise W_STUCK (its work
 * stays with the machine); budget 0 is unlimited */
uint64_t family_run_budget(Family f, uint64_t a, uint64_t b, size_t budget, WhnfStatus *status);
Family eval_entry_family(EntryId e);
uint64_t eval_entry_a(EntryId e);
uint64_t eval_entry_b(EntryId e);

/* the interning subroutine: inserts the record held by *buf into t (the
 * buffer's pages are released), returning its id; *created (when non-NULL,
 * in storage that outlives the call) tells whether it was new */
Cont *intern_sub(const Cont *caller, Interner *t, WordBuf *buf, bool *created);
void dnf_families_init(void);
void subst_families_init(void);
void construct_families_init(void);

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

/* the observation family: key (t, observe_key(χ, φ, P)) observes t under
 * χ ∧ φ (φ = 0: none) bound to the pin set P (pins.h); its value is a
 * result record */
uint64_t observe_key(FaceId chi, FaceId phi, uint64_t pins);
/* a construction request as a subroutine (value: RefId): a fixed-shape tag
 * at operands ids by the schema (term.h), or a written request record */
Cont *mk_tag_sub(const Cont *caller, Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal);
#define MK_SUB(k, tag, payload, levels, formal, ...) mk_tag_sub((k), (tag), (payload), (levels), sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ }, (formal))
Cont *construct_buf_sub(const Cont *caller, WordBuf *w);

/* one lifetime: the evaluator lives and dies with the machine */
void eval_init(void);
void eval_free(void);

/* Root observation: W_STUCK when the root did not complete (a cyclic or
 * otherwise suspended demand); pins 0 reads the current revisions of t's
 * premises once. */
EvalResult whnf(RefId t, FaceId chi, WhnfStatus *status);
EvalResult whnf_pinned(RefId t, FaceId chi, uint64_t pins, WhnfStatus *status);

/* run queued jobs until none is left (with a pool: until quiescent) */
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
 * number of producers in the union */
void eval_work(size_t n, const EntryId *roots, Exact *out, size_t *support);
EntryId eval_entry_find(Family f, uint64_t a, uint64_t b);   /* the entry of a key, 0 if never requested */

/* cache introspection */
EntryState eval_entry_state(EntryId e);
size_t eval_entry_count(void);
bool eval_entry_live(EntryId e);
size_t eval_entry_runs(EntryId e);

void print_result(EvalResult r, FILE *f);

#endif

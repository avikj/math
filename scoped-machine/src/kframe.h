/* kframe.h — the kernel's control state as explicit frames (HANDOFF §15).
 *
 * A kernel procedure that recurses, loops over input-sized data, or waits is
 * a frame family: a record holding its operands, its locals and owned
 * temporaries, a program counter (the resume point: a label address and its
 * phase number) and its return destination. A frame stack (KStack) is an
 * ordinary heap object: it can be stepped by any thread, inspected (family
 * and phase of every frame), and dropped.
 *
 *   STEP   the driver runs the top frame's step function from its program
 *          counter until it returns (KS_DONE: its result is written to its
 *          destination and the frame is popped), requests a child (KS_CALL:
 *          the child is the new top), yields (KS_YIELD: the grant is spent)
 *          or waits (KS_WAIT: it registered the stack it needs).
 *   RESUME the next grant continues the top frame at its program counter.
 *   DROP   destruction pops every frame, running its family's drop (which
 *          releases the owned fields valid at its phase); nothing of the
 *          unfinished program is evaluated.
 *
 * A grant of n transitions runs steps until n fine transitions were taken
 * (checked at the driver between steps and at the KF_SAFE points inside
 * loops) and the thread holds no lock; KF_UNBOUNDED runs to completion (the
 * synchronous drivers). The synchronous API of each family drives the same
 * frames on a stack of the calling thread, so there is one implementation of
 * each procedure; nesting depth is heap frames, never the native stack.
 *
 * The dynamic per-computation state some kernel modules keep in thread-local
 * variables (the checker's frame stack, the current origin's levels, the
 * required-scope context, the evaluator's deferred requests, the accounting
 * owner, the open event units) belongs to the computation: a stack that is
 * suspended carries it, and it is restored on whichever thread resumes it.
 */
#ifndef CUBICAL_KFRAME_H
#define CUBICAL_KFRAME_H
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <pthread.h>
#include "xcount.h"

#define KF_UNBOUNDED ((size_t)-1)
typedef enum { KS_DONE = 0, KS_CALL, KS_YIELD, KS_WAIT } KStatus;
typedef enum { KO_PENDING = 0, KO_OK, KO_INVALID, KO_UNRESOLVED } KOutcome;   /* a settled verdict, or an attempt-local one (retried in a new attempt) */

typedef struct KF KF;
typedef struct KStack KStack;
typedef KStatus (*KFStep)(KStack *ks, KF *f);
typedef void (*KFDrop)(KF *f);              /* releases the owned fields of a frame at its current phase */
typedef struct KFamily { const char *name; KFStep step; KFDrop drop; uint32_t size; } KFamily;
struct KF { const KFamily *fam; void *pc; KF *up; uint32_t phase; uint32_t bytes; };

typedef struct KFPage KFPage;
typedef struct KFCtx KFCtx;
struct KStack {
    KF *top;                    /* the running frame (NULL: complete) */
    KFPage *page;               /* frame storage: LIFO in host pages */
    size_t depth, max_depth;    /* frames on the stack */
    size_t budget, used;        /* the current grant and the transitions taken under it */
    int lock_base;              /* mutexes the granting thread held when the grant began (the driver's own; a step suspends only at this depth) */
    uint64_t steps; const XCarry *steps_carry;   /* transitions over the whole computation: exact (kf_steps) */
    bool sync;                  /* driven to completion by the calling thread (waits block on their condition) */
    bool started, done, cancel, scoped;
    uint64_t job;               /* the engine job owning this stack (0: none) */
    struct ReuseScope *acct;    /* the accounting owner of its work */
    KStack *blocked_on;         /* the last suspension was a wait needing this stack (compared, never dereferenced) */
    uint64_t blocked_job;
    bool blocked;               /* the last suspension was a wait */
    bool in_eval;               /* suspended inside an evaluator task (that task's ownership is held by this stack) */
    uint64_t arg[6], out[4]; bool ok; const char *why; KOutcome outcome;   /* an engine kernel call: operands and result */
    KFCtx *ctx;                 /* the suspended computation's dynamic state */
    KStack *sync_prev;          /* the next free synchronous record of this thread */
    KStack *sync_next_all;      /* every synchronous record of this thread (released at its exit) */
    const char *due_fam; int due_counter, due_locks;   /* KF_REPORT: where the grant was spent (the stretch an overrun report names) */
};

/* the stack being stepped on this thread (NULL outside any step) */
extern __thread KStack *kf_tl;
extern __thread int kf_lock_depth;          /* mutexes held by this thread (common.h wrappers) */
extern __thread int kf_last_counter;
void kf_overrun_note(const KStack *s);   /* KF_REPORT: a granted stack ran KF_OVERRUN_AT transitions past its grant (top frame, counter) */
enum { KF_OVERRUN_AT = 64 };
static inline void kf_tick(int c) {
    KStack *s = kf_tl; if (!s) return;
    kf_last_counter = c; s->used++;
    if (__builtin_expect(s->used == s->budget, 0) && !s->sync) { s->due_fam = s->top ? s->top->fam->name : "-"; s->due_counter = c; s->due_locks = kf_lock_depth - s->lock_base; }
    if (__builtin_expect(s->used == s->budget + KF_OVERRUN_AT, 0) && !s->sync && s->budget != KF_UNBOUNDED) kf_overrun_note(s); s->steps++; if (__builtin_expect(s->steps == XC_HALF, 0)) { s->steps_carry = xc_carry_push(s->steps_carry); s->steps = 0; }
}
static inline void kf_tickn(int c, uint64_t n) { KStack *s = kf_tl; if (!s) return; kf_last_counter = c; s->used += n; xl_add(&s->steps, &s->steps_carry, n); }
static inline XSnap kf_steps(const KStack *s) { XSnap r = { s->steps, s->steps_carry }; return r; }
/* the mutexes held beyond the granting driver's own (inside an engine step), or all of them (elsewhere) */
static inline int kf_locks_held(void) { return kf_lock_depth - (kf_tl ? kf_tl->lock_base : 0); }
/* a grant is spent: the next safe point suspends (never while a lock is held) */
static inline bool kf_due(const KStack *s) { return s && !s->sync && s->budget != KF_UNBOUNDED && s->used >= s->budget && kf_lock_depth == s->lock_base; }

/* frames */
void *kf_push(KStack *ks, const KFamily *fam);   /* a zeroed frame of fam->size bytes on top of ks */
/* stacks */
KStack *kf_new(void);                       /* an engine stack (host record) */
void kf_free(KStack *ks);                   /* a complete stack, or an unstarted one */
void kf_cancel(KStack *ks);                 /* DROP: pops every frame (each family's drop), discards its suspended state, frees the record */
size_t kf_grant(KStack *ks, size_t budget); /* runs up to `budget` transitions (or to completion); returns the transitions taken */
static inline bool kf_done(const KStack *ks) { return ks->done; }
/* synchronous drivers: a stack of the calling thread, run to completion */
KStack *kf_sync_begin(void);
void kf_sync_run(KStack *ks);
void kf_sync_end(KStack *ks);
/* inspection */
typedef void (*KFVisit)(void *ctx, size_t level, const char *family, uint32_t phase);
size_t kf_inspect(const KStack *ks, KFVisit v, void *ctx);   /* innermost first; returns the depth */
typedef struct { uint64_t stacks, frames, grants, suspends, waits, cancelled, dropped_frames, sync_runs, sync_in_step; size_t live_stacks, live_pages, max_depth; } KfStats;   /* max_depth: the deepest frame stack so far (heap frames, not native stack) */
KfStats kf_stats(void);

/* computation-local state: a module registers each thread-local variable that
 * belongs to the computation (with its initial bytes and a release for a
 * discarded copy); a stack suspended on one thread resumes with it on another */
void kf_ctx_register(void *(*addr)(void), size_t size, const void *init, void (*release)(void *copy));
/* the event units a step leaves open are carried by the suspended stack (event.c) */

/* waits: under an engine stack the wait suspends the stack (one transition,
 * with the stack it needs when known); on a synchronous stack or a plain
 * thread it is the condition wait. The caller holds `mu` and re-checks its
 * condition afterwards, exactly as after pthread_cond_wait. Inside a step
 * use KF_WAIT (a frame resume point); kf_wait_plain is for code that is not
 * a frame and is never reached from an engine step. */
static inline bool kf_wait_suspends(const KStack *s, const KStack *on) { return s && !s->sync && (s->budget != KF_UNBOUNDED || on); }
void kf_wait_prepare(KStack *s, KStack *on, uint64_t on_job);   /* records the dependency and charges the wait */
void kf_wait_resumed(KStack *s);
void kf_wait_plain(pthread_cond_t *cv, pthread_mutex_t *mu);

/* ---- frame-family definitions ----
 *
 *   #define foo_PARAMS(X) X(RefId, t) X(FaceId, C)
 *   KF_DECL(foo, RefId, foo_PARAMS, uint64_t i; RefId r;)      // locals
 *   KF_STEP(foo) { KF_BEGIN(foo);  ... F->t ... KF_CALL(bar, &F->r, F->t); ... KF_RET(F->r); KF_END; }
 *   KF_SYNC_DEF(foo, RefId, foo_PARAMS, foo(RefId t, FaceId C))  // the synchronous API
 *
 * Inside a step, F is the frame and ks the stack. A resume point (KF_CALL,
 * KF_SAFE, KF_WAIT) may be placed anywhere in structured control flow,
 * including loop and switch bodies: every local lives in F. */
#define KF_CAT_(a, b) a##b
#define KF_CAT(a, b) KF_CAT_(a, b)
#define KF_FIELD(T, n) T n;
#define KF_PARAM(T, n) , T n
#define KF_ASSIGN(T, n) F_->n = n;
#define KF_ARG(T, n) , n
#define KF_NOPARAMS(X)
#define KF_DECL_(name, R, PARAMS, LINK, PLINK, ...) \
    typedef struct { KF kh; R *kret; PARAMS(KF_FIELD) __VA_ARGS__ } name##_F; \
    static KStatus name##_step(KStack *ks, KF *kf_); \
    LINK const KFamily name##_fam = { #name, name##_step, NULL, sizeof(name##_F) }; \
    LINK PLINK void name##_push(KStack *ks, R *kret_ PARAMS(KF_PARAM)) { name##_F *F_ = kf_push(ks, &name##_fam); F_->kret = kret_; PARAMS(KF_ASSIGN) (void)F_; }
#define KF_DECL(name, R, PARAMS, ...) KF_DECL_(name, R, PARAMS, static, inline, __VA_ARGS__)
#define KF_DECL_EXT(name, R, PARAMS, ...) KF_DECL_(name, R, PARAMS, , , __VA_ARGS__)     /* push visible to other units (KF_PROTO in a header) */
#define KF_DECL_DROP_(name, R, PARAMS, DROP, LINK, PLINK, ...) \
    typedef struct { KF kh; R *kret; PARAMS(KF_FIELD) __VA_ARGS__ } name##_F; \
    static KStatus name##_step(KStack *ks, KF *kf_); static void DROP(name##_F *F); \
    static void DROP##_kf_(KF *f) { DROP((name##_F *)f); } \
    LINK const KFamily name##_fam = { #name, name##_step, DROP##_kf_, sizeof(name##_F) }; \
    LINK PLINK void name##_push(KStack *ks, R *kret_ PARAMS(KF_PARAM)) { name##_F *F_ = kf_push(ks, &name##_fam); F_->kret = kret_; PARAMS(KF_ASSIGN) (void)F_; }
#define KF_DECL_DROP(name, R, PARAMS, DROP, ...) KF_DECL_DROP_(name, R, PARAMS, DROP, static, inline, __VA_ARGS__)       /* DROP(name_F *F): releases F's owned fields */
#define KF_DECL_EXT_DROP(name, R, PARAMS, DROP, ...) KF_DECL_DROP_(name, R, PARAMS, DROP, , , __VA_ARGS__)
#define KF_PROTO(name, R, PARAMS) void name##_push(KStack *ks, R *kret_ PARAMS(KF_PARAM))
#define KF_STEP(name) static KStatus name##_step(KStack *ks, KF *kf_)
#define KF_BEGIN(name) name##_F *const F = (name##_F *)kf_; (void)ks; if (F->kh.pc) goto *F->kh.pc
#define KF_END return KS_DONE
/* resume points */
#define KF_SUSPEND_(n, st) do { F->kh.pc = &&KF_CAT(kf_l_, n); F->kh.phase = (n); return (st); KF_CAT(kf_l_, n):; } while (0)
#define KF_CALL_(n, callee, ret, ...) do { callee##_push(ks, (ret), __VA_ARGS__); KF_SUSPEND_(n, KS_CALL); } while (0)
#define KF_CALL(callee, ...) KF_CALL_(__COUNTER__, callee, __VA_ARGS__)          /* KF_CALL(callee, &F->dest, args...) */
#define KF_CALLP_(n, push, ...) do { (push)(ks, __VA_ARGS__); KF_SUSPEND_(n, KS_CALL); } while (0)
#define KF_CALLP(push, ...) KF_CALLP_(__COUNTER__, push, __VA_ARGS__)               /* through a push-function pointer: KF_CALLP(p, &F->dest, args...) */
#define KF_CALL0_(n, callee, ret) do { callee##_push(ks, (ret)); KF_SUSPEND_(n, KS_CALL); } while (0)
#define KF_CALL0(callee, ret) KF_CALL0_(__COUNTER__, callee, ret)               /* a family without operands */
#define KF_SAFE_(n) do { if (kf_due(ks)) KF_SUSPEND_(n, KS_YIELD); } while (0)
#define KF_SAFE() KF_SAFE_(__COUNTER__)                                         /* a suspension point inside a loop */
#define KF_WAIT_(n, cv, mu, on, job) do { \
        if (kf_wait_suspends(ks, (on))) { kf_wait_prepare(ks, (on), (job)); pthread_mutex_unlock(mu); KF_SUSPEND_(n, KS_WAIT); kf_wait_resumed(ks); pthread_mutex_lock(mu); } \
        else kf_wait_plain((cv), (mu)); } while (0)
#define KF_WAIT(cv, mu, on, job) KF_WAIT_(__COUNTER__, cv, mu, on, job)
#define KF_RET(v) do { if (F->kret) *F->kret = (v); return KS_DONE; } while (0)
#define KF_RETV() return KS_DONE
/* the synchronous API of a family: the same frames on the calling thread's stack */
#define KF_SYNC_DEF(name, R, PARAMS, SIG) \
    R SIG { R r_; KStack *s_ = kf_sync_begin(); name##_push(s_, &r_ PARAMS(KF_ARG)); kf_sync_run(s_); kf_sync_end(s_); return r_; }
#define KF_SYNC_VOID_DEF(name, PARAMS, SIG) \
    void SIG { KStack *s_ = kf_sync_begin(); name##_push(s_, NULL PARAMS(KF_ARG)); kf_sync_run(s_); kf_sync_end(s_); }
#endif

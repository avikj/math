/* kstack.h — nesting depth independent of the native stack.
 *
 * The kernel's recursive procedures (checking, conversion, inference, shape
 * construction, validation, template interpretation, scoped traversal) call
 * KSTACK_CALL at their entry: when the remaining room on the current stack
 * segment is below KSTACK_RESERVE, the call continues on a fresh segment of
 * the same thread (a host allocation of KSTACK_SEG bytes, switched to with
 * swapcontext; thread-local state, held locks and the continuation identity
 * are unchanged because the thread is), and the segment is returned when the
 * call returns. Nesting therefore consumes resident segments and ends only
 * at an actual resource condition; no fixed native stack size or thread
 * count bounds the depth. This is a control-flow device: every call and
 * return of the algorithm is unchanged. */
#ifndef CUBICAL_KSTACK_H
#define CUBICAL_KSTACK_H
#include <stddef.h>
#include <stdbool.h>
#define KSTACK_RESERVE ((size_t)256 << 10)     /* room kept on a segment before a call moves to the next */
#define KSTACK_SEG     ((size_t)2 << 20)      /* bytes per added segment (a growth policy, not a depth bound) */
bool kstack_low(void);                        /* the current segment has less than KSTACK_RESERVE left */
void kstack_run(void (*fn)(void *), void *arg);   /* fn(arg) on a fresh segment of this thread */
size_t kstack_segments(void);                 /* segments added so far on this thread (diagnostics) */
/* V23 R3 cancellation return path: the innermost unwind target of this
 * thread. A kernel continuation's base (kcont.c run_one) and every segment's
 * entry install one; a cancelled continuation longjmps to the innermost, and
 * a segment that was left by cancellation returns to its parent segment by
 * the ordinary switch, releases its mapping, and continues the unwind to the
 * parent's target. No jump crosses a segment boundary. */
extern __thread void *kstack_unwind;        /* a jmp_buf * (kept untyped: this header precedes the feature macros in some units) */
size_t kstack_live_segments(void);           /* segments currently mapped, all threads */
#endif

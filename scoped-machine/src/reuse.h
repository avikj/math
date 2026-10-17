#ifndef CUBICAL_REUSE_H
#define CUBICAL_REUSE_H
#include "common.h"
#include "reuse_stats.h"
#include "xcount.h"
void reuse_bump(ReuseCounter c);
void reuse_reset_all(void);    /* machine teardown only */

/* V21 R3: exclusive attribution. A scope is the accounting owner of the work
 * executed on its behalf: a kernel call (its continuation), and every
 * evaluator task of a producer that call launched. Each counted event is
 * added to the global counter and, once, to the scope current on the thread
 * executing it. Closing a scope folds its counts exactly once (each count is
 * taken by one atomic exchange); an event arriving after the close is folded
 * by its own exchange into the late totals (`reuse_scope_late`). */
typedef struct ReuseScope {
    XCount c[REUSE_COUNTER_COUNT];   /* V23 R5: exact */
    int phase;                       /* the owner's ledger phase */
    int closed;                      /* atomic */
    int refs;                        /* atomic: the owner + every producer entry it launched */
    struct ReuseScope *all_next;
} ReuseScope;
extern __thread ReuseScope *reuse_tl_scope;
ReuseScope *reuse_scope_new(int phase);                 /* refs = 1 */
void reuse_scope_ref(ReuseScope *s);
void reuse_scope_unref(ReuseScope *s);                  /* storage is retained until reuse_scope_reclaim */
ReuseScope *reuse_scope_enter(ReuseScope *s);           /* returns the previous scope */
void reuse_scope_leave(ReuseScope *prev);
XSnap reuse_scope_take(ReuseScope *s, ReuseCounter c);      /* atomically take the counts not yet folded (exact) */
void reuse_scope_close(ReuseScope *s);
uint64_t reuse_scope_late(int phase, ReuseCounter c);   /* events folded after their scope closed, per phase (checked word projection) */
XSnap reuse_scope_late_snap(int phase, ReuseCounter c);
XSnap reuse_snap(ReuseCounter c);                      /* exact global count */
void reuse_seed(ReuseCounter c, uint64_t low);         /* tests: a valid boundary state */
void reuse_scope_reclaim(void);                          /* machine teardown: free unreferenced scopes */
#define REUSE_PHASES 8
#endif

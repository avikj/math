/* kcont.h — kernel continuations (§94: the kernel's own loops as units).
 *
 * A kernel call requested by a unit of the work engine does not run to
 * completion inside that unit. It runs on its own continuation: a thread
 * whose stack is the retained continuation, which performs one *transition*
 * per granted step and then hands control back. A transition is one fine
 * step of the kernel's instrumented loops (fine.h: one field opened, one map
 * entry visited, one checker frame, one face operation, one DNF clause step,
 * one hash/probe/compare/copy …) — `fine_bump` is the transition point. The
 * continuation yields only when it holds no mutex (every mutex acquisition in
 * the kernel is counted per thread by the wrappers in common.h), so a
 * suspended continuation never blocks another thread on a lock it owns.
 *
 * A grant of n steps runs the continuation until n transitions were taken or
 * the call completed; a grant of KC_UNBOUNDED runs it to completion in one
 * hand-off (the synchronous drivers). Exactly one continuation is in
 * progress at a time (`kc_active`): the engine starts the next only when the
 * current one has completed, so interleaved checker claims cannot wait on
 * each other across suspended continuations.
 */
#ifndef CUBICAL_KCONT_H
#define CUBICAL_KCONT_H
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <pthread.h>

#define KC_UNBOUNDED ((size_t)-1)

typedef struct KCont KCont;
typedef void (*KFn)(KCont *k);

struct KCont {
    pthread_t thread; pthread_mutex_t mu; pthread_cond_t cv;
    int state;                  /* 0 waiting for a grant, 1 running, 2 completed */
    size_t budget, used;        /* the current grant and the transitions taken under it */
    uint64_t steps;             /* transitions over the whole call */
    KFn fn; uint64_t arg[6];    /* the call */
    uint64_t out[4]; bool ok; const char *why;   /* its result */
    bool started;
};

KCont *kc_new(KFn fn, const uint64_t *args, size_t nargs);   /* the thread is created at the first grant */
size_t kc_grant(KCont *k, size_t budget);   /* run up to `budget` transitions (or to completion); returns the transitions taken */
bool kc_done(const KCont *k);
void kc_free(KCont *k);                     /* completes the call if it is not finished (unbounded grant); the thread parks for reuse */
void kc_shutdown(void);                     /* joins the parked continuation threads (engine teardown) */

/* called from fine_bump on every thread; a transition point of the running continuation */
extern __thread KCont *kc_tl;
extern __thread int kc_lock_depth;
void kc_tick(void);
#endif

/* reuse.c — the §74.2 counter contract: semantic producer/rule starts and the
 * reuse administration that is counted separately. Counts are incremented
 * atomically at the rule sites (evaluator, checker, compiler, work engine)
 * when the rule actually executes, never when a cached result is delivered;
 * they are monotone until machine teardown. */
#include "common.h"
#include "reuse_stats.h"

static uint64_t counters[REUSE_COUNTER_COUNT];

void reuse_bump(ReuseCounter c) { __atomic_add_fetch(&counters[c], 1, __ATOMIC_RELAXED); }
void reuse_reset_all(void) { for (int i = 0; i < REUSE_COUNTER_COUNT; i++) __atomic_store_n(&counters[i], 0, __ATOMIC_SEQ_CST); }
uint64_t reuse_count(ReuseCounter c) { return __atomic_load_n(&counters[c], __ATOMIC_SEQ_CST); }

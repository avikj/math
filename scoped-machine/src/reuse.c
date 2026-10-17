/* reuse.c — the §74.2 counter contract: semantic producer/rule starts and the
 * reuse administration that is counted separately. Counts are incremented
 * atomically at the rule sites (evaluator, checker, compiler, work engine)
 * when the rule actually executes, never when a cached result is delivered;
 * they are monotone until machine teardown. */
#include "common.h"
#include "reuse_stats.h"
#include "reuse.h"
#include <string.h>

static uint64_t counters[REUSE_COUNTER_COUNT];

__thread ReuseScope *reuse_tl_scope;
static uint64_t late[REUSE_PHASES][REUSE_COUNTER_COUNT];
static ReuseScope *all_scopes;
void reuse_bump(ReuseCounter c) {
    __atomic_add_fetch(&counters[c], 1, __ATOMIC_RELAXED);
    ReuseScope *s = reuse_tl_scope;
    if (!s) return;
    __atomic_add_fetch(&s->c[c], 1, __ATOMIC_SEQ_CST);
    if (__atomic_load_n(&s->closed, __ATOMIC_SEQ_CST)) {   /* closed: fold this event (and any racing one) exactly once */
        uint64_t v = __atomic_exchange_n(&s->c[c], 0, __ATOMIC_SEQ_CST);
        if (v) __atomic_add_fetch(&late[s->phase][c], v, __ATOMIC_SEQ_CST);
    }
}
ReuseScope *reuse_scope_new(int phase) {
    ReuseScope *s = calloc(1, sizeof *s); require(s, "out of memory");
    s->phase = phase >= 0 && phase < REUSE_PHASES ? phase : 0; s->refs = 1;
    ReuseScope *h = __atomic_load_n(&all_scopes, __ATOMIC_RELAXED);
    do s->all_next = h; while (!__atomic_compare_exchange_n(&all_scopes, &h, s, false, __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
    return s;
}
void reuse_scope_ref(ReuseScope *s) { if (s) __atomic_add_fetch(&s->refs, 1, __ATOMIC_ACQ_REL); }
void reuse_scope_unref(ReuseScope *s) { if (s) __atomic_sub_fetch(&s->refs, 1, __ATOMIC_ACQ_REL); }
ReuseScope *reuse_scope_enter(ReuseScope *s) { ReuseScope *p = reuse_tl_scope; reuse_tl_scope = s; return p; }
void reuse_scope_leave(ReuseScope *prev) { reuse_tl_scope = prev; }
uint64_t reuse_scope_take(ReuseScope *s, ReuseCounter c) { return __atomic_exchange_n(&s->c[c], 0, __ATOMIC_SEQ_CST); }
void reuse_scope_close(ReuseScope *s) {
    __atomic_store_n(&s->closed, 1, __ATOMIC_SEQ_CST);
    for (int c = 0; c < REUSE_COUNTER_COUNT; c++) { uint64_t v = __atomic_exchange_n(&s->c[c], 0, __ATOMIC_SEQ_CST); if (v) __atomic_add_fetch(&late[s->phase][c], v, __ATOMIC_SEQ_CST); }
}
uint64_t reuse_scope_late(int phase, ReuseCounter c) { return __atomic_load_n(&late[phase][c], __ATOMIC_SEQ_CST); }
void reuse_scope_reclaim(void) {
    ReuseScope **pp = &all_scopes;
    while (*pp) { ReuseScope *s = *pp; if (__atomic_load_n(&s->refs, __ATOMIC_ACQUIRE) <= 0) { *pp = s->all_next; free(s); } else pp = &s->all_next; }
}
void reuse_reset_all(void) { for (int i = 0; i < REUSE_COUNTER_COUNT; i++) __atomic_store_n(&counters[i], 0, __ATOMIC_SEQ_CST); memset(late, 0, sizeof late); }
uint64_t reuse_count(ReuseCounter c) { return __atomic_load_n(&counters[c], __ATOMIC_SEQ_CST); }

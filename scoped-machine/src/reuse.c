/* reuse.c — the §74.2 counter contract: semantic producer/rule starts and the
 * reuse administration that is counted separately. Counts are incremented
 * atomically at the rule sites (evaluator, checker, compiler, work engine)
 * when the rule actually executes, never when a cached result is delivered;
 * they are monotone until machine teardown. */
#include "common.h"
#include "reuse_stats.h"
#include "reuse.h"
#include "event.h"
#include <string.h>

static XCount counters[REUSE_COUNTER_COUNT];

__thread ReuseScope *reuse_tl_scope;
static XCount late[REUSE_PHASES][REUSE_COUNTER_COUNT];
static ReuseScope *all_scopes;
void reuse_bump(ReuseCounter c) {
    xc_add(&counters[c], 1); ev_add(ED_REUSE + (unsigned)c, 1);
    ReuseScope *s = reuse_tl_scope;
    if (!s) return;
    xc_add(&s->c[c], 1);
    if (__atomic_load_n(&s->closed, __ATOMIC_SEQ_CST)) {   /* closed: fold this event (and any racing one) exactly once */
        XSnap v = xc_take(&s->c[c]);
        xc_add_snap(&late[s->phase][c], v);
    }
}
ReuseScope *reuse_scope_new(int phase) {
    ReuseScope *s = calloc(1, sizeof *s); require(s, "out of memory");
    s->phase = phase >= 0 && phase < REUSE_PHASES ? phase : 0; s->refs = 1;
    static uint64_t next_id = EO_SERVICE_COUNT; s->id = __atomic_add_fetch(&next_id, 1, __ATOMIC_RELAXED);
    ReuseScope *h = __atomic_load_n(&all_scopes, __ATOMIC_RELAXED);
    do s->all_next = h; while (!__atomic_compare_exchange_n(&all_scopes, &h, s, false, __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
    return s;
}
void reuse_scope_ref(ReuseScope *s) { if (s) __atomic_add_fetch(&s->refs, 1, __ATOMIC_ACQ_REL); }
void reuse_scope_unref(ReuseScope *s) { if (s) __atomic_sub_fetch(&s->refs, 1, __ATOMIC_ACQ_REL); }
ReuseScope *reuse_scope_enter(ReuseScope *s) { ReuseScope *p = reuse_tl_scope; if (p != s) { ev_owner_switch(); reuse_tl_scope = s; ev_owner_refresh(); } return p; }
void reuse_scope_leave(ReuseScope *prev) { if (reuse_tl_scope != prev) { ev_owner_switch(); reuse_tl_scope = prev; ev_owner_refresh(); } }
uint64_t reuse_scope_id(const ReuseScope *s) { return s->id; }
XSnap reuse_scope_take(ReuseScope *s, ReuseCounter c) { return xc_take(&s->c[c]); }
void reuse_scope_close(ReuseScope *s) {
    __atomic_store_n(&s->closed, 1, __ATOMIC_SEQ_CST);
    for (int c = 0; c < REUSE_COUNTER_COUNT; c++) { XSnap v = xc_take(&s->c[c]); xc_add_snap(&late[s->phase][c], v); }
}
uint64_t reuse_scope_late(int phase, ReuseCounter c) { return xs_u64_checked(xc_snap(&late[phase][c]), "reuse late total"); }
XSnap reuse_scope_late_snap(int phase, ReuseCounter c) { return xc_snap(&late[phase][c]); }
XSnap reuse_snap(ReuseCounter c) { return xc_snap(&counters[c]); }
void reuse_seed(ReuseCounter c, uint64_t low) { xc_seed(&counters[c], low); }
void reuse_scope_reclaim(void) {
    ReuseScope **pp = &all_scopes;
    while (*pp) { ReuseScope *s = *pp; if (__atomic_load_n(&s->refs, __ATOMIC_ACQUIRE) <= 0) { *pp = s->all_next; free(s); } else pp = &s->all_next; }
}
void reuse_reset_all(void) { for (int i = 0; i < REUSE_COUNTER_COUNT; i++) xc_reset(&counters[i]); for (int p = 0; p < REUSE_PHASES; p++) for (int i = 0; i < REUSE_COUNTER_COUNT; i++) xc_reset(&late[p][i]); }
uint64_t reuse_count(ReuseCounter c) { return xs_u64_checked(xc_snap(&counters[c]), "reuse count"); }   /* checked word projection */

/* xcount.h — exact actual-work counts (V23 R5, CONTINUATION-AND-COUNT-CLOSURE §C).
 *
 * An authoritative count is an exact natural
 *     value(l, B) = l + 2^63 · length(B),
 * a word-sized low digit and a persistent list of carry records, each worth
 * 2^63. An increment by n < 2^32 is one fetch-and-add on l; the adder whose
 * add leaves l ≥ 2^63 (and any adder that finds it there) normalizes under
 * the counter's stripe lock: subtract 2^63 from l and install one carry
 * record, in one locked section, so value(l, B) is unchanged by
 * normalization. Between an add and its normalization l can exceed 2^63 by
 * the in-flight increments of the other threads (each < 2^32, each adder
 * normalizes before returning), so l never wraps; a reading taken under the
 * stripe lock is exact at every instant. Nothing is propagated through a
 * word and no reading wraps, saturates or stops. A snapshot retains (l, B);
 * the exact reading folds B's length through the exact naturals. Word
 * projections are separate and checked: they report out-of-range instead
 * of inventing a small value.
 *
 * Carry records are host records (never kalloc storage: kalloc's own
 * instrumentation counts with these counters, so the counter must not
 * allocate through the allocator it instruments). */
#ifndef CUBICAL_XCOUNT_H
#define CUBICAL_XCOUNT_H
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct XCarry { const struct XCarry *next; struct XCarry *all_next; } XCarry;
typedef struct { uint64_t low; const XCarry *carry; } XCount;      /* fields accessed atomically */
typedef struct { uint64_t low; const XCarry *carry; } XSnap;       /* an immutable exact snapshot */

/* single-writer form (a field written by one owner under its own lock or thread): the low digit is a plain word, the carries a list */
#define XC_HALF ((uint64_t)1 << 63)
const XCarry *xc_carry_push(const XCarry *next);
static inline void xl_add(uint64_t *low, const XCarry **carry, uint64_t n) {   /* exact for any n: the digit stays below 2^63 between updates */
    while (n) { uint64_t room = XC_HALF - *low, step = n < room ? n : room; *low += step; n -= step; if (*low == XC_HALF) { *carry = xc_carry_push(*carry); *low = 0; } }
}
void xc_normalize2(uint64_t *low, const XCarry **carry);
void xc_add_large(uint64_t *low, const XCarry **carry, uint64_t n);
static inline void xc_add(XCount *c, uint64_t n) {
    if (__builtin_expect(n < ((uint64_t)1 << 32), 1)) {
        uint64_t old = __atomic_fetch_add(&c->low, n, __ATOMIC_RELAXED);
        if (__builtin_expect(old + n < XC_HALF, 1)) return;
        xc_normalize2(&c->low, &c->carry);
        return;
    }
    xc_add_large(&c->low, &c->carry, n);
}
static inline void xc_add2(uint64_t *low, const XCarry **carry, uint64_t n) {   /* the same protocol on a separately declared (low, carry) pair */
    if (__builtin_expect(n < ((uint64_t)1 << 32), 1)) { uint64_t old = __atomic_fetch_add(low, n, __ATOMIC_RELAXED); if (__builtin_expect(old + n < XC_HALF, 1)) return; xc_normalize2(low, carry); return; }
    xc_add_large(low, carry, n);
}
XSnap xc_snap2(const uint64_t *low, const XCarry *const *carry);                 /* exact; lock-free unless the low digit overflows */
static inline void xc_inc(XCount *c) { xc_add(c, 1); }
XSnap xc_snap(const XCount *c);                     /* consistent (low, carry-prefix) */
XSnap xc_take(XCount *c);                           /* atomically read and reset to zero (scope folding) */
void xc_add_snap(XCount *dst, XSnap s);             /* dst += value(s): the low digit, then one carry record per carry of s */
void xc_reset(XCount *c);                           /* teardown: zero (records stay owned by the module) */
void xc_seed(XCount *c, uint64_t low);              /* tests: a valid boundary state (no carries) */
size_t xs_carries(XSnap s);                         /* length(B) (units of 2^63), one record per step (native: a count of live records) */
bool xs_u64(XSnap s, uint64_t *out);                /* checked word projection: false when value ≥ 2^64 */
uint64_t xs_u64_checked(XSnap s, const char *what); /* the projection, fatal (reported) when out of range */
bool xs_eq(XSnap a, XSnap b);
/* exact difference a − b of snapshots of one counter (b taken earlier): the
 * carry prefix of b is a suffix of a's */
bool xs_delta_u64(XSnap a, XSnap b, uint64_t *out); /* checked */
#endif

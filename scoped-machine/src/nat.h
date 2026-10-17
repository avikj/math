/* nat.h — exact finite naturals (BOUNDS-COMPLETION §2).
 *
 * Word ABI: bit 63 clear — an immediate value in [0, 2^63); bit 63 set — the
 * handle of a canonical, interned, little-endian 64-bit limb record (no high
 * zero limbs; value >= 2^63). UINT64_MAX is reserved for the typed sentinels
 * (an absent level, an infinite cost) and is never a Nat. Two Nats are equal
 * iff their words are equal; the numeric order of handles is not the order
 * of values (use nat_compare). Every operation on limbs takes one fine
 * transition per limb (FC_NAT_LIMBS): inside a kernel continuation an
 * operation of any precision is a sequence of bounded transitions. */
#ifndef CUBICAL_NAT_H
#define CUBICAL_NAT_H
#include "common.h"

typedef uint64_t Nat;
#define NAT_BOX   (UINT64_C(1) << 63)
#define NAT_NONE  UINT64_MAX            /* reserved: not a Nat */
#define NAT_SMALL(x) ((Nat)(x))        /* documented immediate constructor: x < 2^63 */

static inline bool nat_is_small(Nat n) { return !(n & NAT_BOX); }
Nat nat_from_word(uint64_t w);                          /* boxes w >= 2^63 */
Nat nat_from_limbs(size_t n, const uint64_t *limbs);    /* trims high zero limbs, canonical */
const uint64_t *nat_limbs(Nat n, size_t *len, uint64_t *tmp);   /* canonical limbs (tmp: storage for an immediate's one limb) */
int nat_compare(Nat a, Nat b);                          /* -1, 0, 1 */
Nat nat_add(Nat a, Nat b);
Nat nat_sub_ge(Nat a, Nat b);                           /* premise a >= b */
Nat nat_successor(Nat a);
Nat nat_max(Nat a, Nat b);
bool nat_to_u64(Nat n, uint64_t *out);                  /* false: not representable in the requested host type */
bool nat_valid(Nat n);                                  /* an immediate, or a handle of an existing record */
size_t nat_decimal(Nat n, char *buf, size_t cap);       /* decimal text (diagnostics/export); returns the length written (truncated at cap-1) */

/* signed differences of finite costs: Zero | Positive(nonzero) | Negative(nonzero) */
typedef struct { int sign; Nat magnitude; } NatDiff;
NatDiff nat_diff(Nat a, Nat b);                         /* a - b, exact */
#endif

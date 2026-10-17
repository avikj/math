/* nat.c — exact finite naturals; see nat.h. The limb records live in one
 * process-lifetime interner (cursor probing and unlocked comparison,
 * intern.c); an operation emits its limbs one per transition and publishes
 * the canonical record through that interner. */
#include "nat.h"
#include "intern.h"
#include "fine.h"

static Interner NT;
static int nt_live;
static pthread_mutex_t nt_mu = PTHREAD_MUTEX_INITIALIZER;
static void nt_init(void) {
    if (__atomic_load_n(&nt_live, __ATOMIC_ACQUIRE)) return;
    pthread_mutex_lock(&nt_mu);
    if (!nt_live) { interner_init(&NT); __atomic_store_n(&nt_live, 1, __ATOMIC_RELEASE); }
    pthread_mutex_unlock(&nt_mu);
}
static Nat box_limbs(size_t n, const uint64_t *l) {   /* canonical, value >= 2^63 */
    nt_init();
    uint64_t id = interner_intern(&NT, l, n, NULL);
    require(id < NAT_BOX - 1, "nat: handle namespace exhausted");
    return NAT_BOX | id;
}
Nat nat_from_limbs(size_t n, const uint64_t *l) {
    while (n && l[n - 1] == 0) { n--; fine_bump(FC_NAT_LIMBS); }
    if (n == 0) return 0;
    if (n == 1 && l[0] < NAT_BOX) return l[0];
    return box_limbs(n, l);
}
Nat nat_from_word(uint64_t w) { return w < NAT_BOX ? w : box_limbs(1, &w); }
const uint64_t *nat_limbs(Nat a, size_t *len, uint64_t *tmp) {
    require(a != NAT_NONE, "nat: the reserved sentinel is not a natural");
    if (nat_is_small(a)) { *tmp = a; *len = a ? 1 : 0; return tmp; }
    nt_init();
    return interner_get(&NT, a & ~NAT_BOX, len);
}
bool nat_valid(Nat a) {
    if (a == NAT_NONE) return false;
    if (nat_is_small(a)) return true;
    return __atomic_load_n(&nt_live, __ATOMIC_ACQUIRE) && (a & ~NAT_BOX) >= 1 && (a & ~NAT_BOX) <= interner_count(&NT);
}
int nat_compare(Nat a, Nat b) {
    if (a == b) return 0;
    if (nat_is_small(a) && nat_is_small(b)) return a < b ? -1 : 1;
    uint64_t ta, tb; size_t na, nb; const uint64_t *la = nat_limbs(a, &na, &ta), *lb = nat_limbs(b, &nb, &tb);
    fine_bump(FC_NAT_LIMBS);
    if (na != nb) return na < nb ? -1 : 1;                 /* canonical lengths decide */
    for (size_t i = na; i-- > 0; ) { fine_bump(FC_NAT_LIMBS); if (la[i] != lb[i]) return la[i] < lb[i] ? -1 : 1; }
    return 0;
}
Nat nat_add(Nat a, Nat b) {
    if (nat_is_small(a) && nat_is_small(b) && a < NAT_BOX - b) return a + b;   /* the immediate fast path */
    uint64_t ta, tb; size_t na, nb; const uint64_t *la = nat_limbs(a, &na, &ta), *lb = nat_limbs(b, &nb, &tb);
    size_t n = na > nb ? na : nb;
    require(n < SIZE_MAX, "nat: limb count overflow");
    Words out; words_init(&out);
    uint64_t carry = 0;
    for (size_t i = 0; i < n; i++) {
        uint64_t x = i < na ? la[i] : 0, y = i < nb ? lb[i] : 0;
        uint64_t u = x + y, c1 = u < x, v = u + carry, c2 = v < u;
        words_push(&out, v); carry = c1 | c2; fine_bump(FC_NAT_LIMBS);
    }
    if (carry) words_push(&out, 1);
    Nat r = nat_from_limbs(out.n, out.w); words_free(&out); return r;
}
Nat nat_sub_ge(Nat a, Nat b) {
    if (nat_is_small(a) && nat_is_small(b)) { require(a >= b, "nat: subtraction premise a >= b"); return a - b; }
    uint64_t ta, tb; size_t na, nb; const uint64_t *la = nat_limbs(a, &na, &ta), *lb = nat_limbs(b, &nb, &tb);
    require(na >= nb, "nat: subtraction premise a >= b");
    Words out; words_init(&out);
    uint64_t borrow = 0;
    for (size_t i = 0; i < na; i++) {
        uint64_t x = la[i], y = i < nb ? lb[i] : 0;
        uint64_t u = y + borrow, c = u < y;
        words_push(&out, x - u); borrow = c | (x < u); fine_bump(FC_NAT_LIMBS);
    }
    require(!borrow, "nat: subtraction premise a >= b");
    Nat r = nat_from_limbs(out.n, out.w); words_free(&out); return r;
}
Nat nat_successor(Nat a) { return nat_add(a, 1); }
Nat nat_max(Nat a, Nat b) { return nat_compare(a, b) >= 0 ? a : b; }
bool nat_to_u64(Nat a, uint64_t *out) {
    uint64_t t; size_t n; const uint64_t *l = nat_limbs(a, &n, &t);
    if (n > 1) return false;
    *out = n ? l[0] : 0; return true;
}
NatDiff nat_diff(Nat a, Nat b) {
    NatDiff d; int c = nat_compare(a, b);
    d.sign = c; d.magnitude = c == 0 ? 0 : c > 0 ? nat_sub_ge(a, b) : nat_sub_ge(b, a);
    return d;
}
size_t nat_decimal(Nat a, char *buf, size_t cap) {
    if (!cap) return 0;
    uint64_t t; size_t n; const uint64_t *l = nat_limbs(a, &n, &t);
    if (n <= 1) { int k = snprintf(buf, cap, "%llu", (unsigned long long)(n ? l[0] : 0)); return k < 0 ? 0 : (size_t)k < cap ? (size_t)k : cap - 1; }
    /* repeated division by 10^19 of a working copy (diagnostic/export text) */
    uint64_t *w = malloc(n * sizeof *w); require(w, "out of memory"); for (size_t i = 0; i < n; i++) w[i] = l[i];
    char tmp[64]; Words parts; words_init(&parts); size_t m = n;
    while (m) {
        unsigned __int128 rem = 0;
        for (size_t i = m; i-- > 0; ) { unsigned __int128 cur = (rem << 64) | w[i]; w[i] = (uint64_t)(cur / UINT64_C(10000000000000000000)); rem = cur % UINT64_C(10000000000000000000); fine_bump(FC_NAT_LIMBS); }
        words_push(&parts, (uint64_t)rem);
        while (m && w[m - 1] == 0) m--;
    }
    size_t at = 0;
    for (size_t i = parts.n; i-- > 0 && at + 1 < cap; ) {
        int k = snprintf(tmp, sizeof tmp, i == parts.n - 1 ? "%llu" : "%019llu", (unsigned long long)parts.w[i]);
        for (int j = 0; j < k && at + 1 < cap; j++) buf[at++] = tmp[j];
    }
    buf[at] = 0; free(w); words_free(&parts); return at;
}

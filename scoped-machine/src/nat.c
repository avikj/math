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
/* the limb loops are frame families (kframe.h): one transition per limb, a suspension point after each */
#define box_limbs_PARAMS(X) X(size_t, n) X(const uint64_t *, l)
KF_DECL(box_limbs, Nat, box_limbs_PARAMS, uint64_t id;)
KF_STEP(box_limbs) {   /* canonical, value >= 2^63 */
    KF_BEGIN(box_limbs);
    nt_init();
    KF_CALL(interner_intern, &F->id, &NT, F->l, F->n, NULL);
    require(F->id < NAT_BOX - 1, "nat: handle namespace exhausted");
    KF_RET(NAT_BOX | F->id);
    KF_END;
}
KF_DECL_EXT(nat_from_limbs, Nat, nat_from_limbs_PARAMS, Nat r;)
KF_STEP(nat_from_limbs) {
    KF_BEGIN(nat_from_limbs);
    while (F->n && F->limbs[F->n - 1] == 0) { F->n--; fine_bump(FC_NAT_LIMBS); KF_SAFE(); }
    if (F->n == 0) KF_RET(0);
    if (F->n == 1 && F->limbs[0] < NAT_BOX) KF_RET(F->limbs[0]);
    KF_CALL(box_limbs, &F->r, F->n, F->limbs);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(nat_from_limbs, Nat, nat_from_limbs_PARAMS, nat_from_limbs(size_t n, const uint64_t *limbs))
Nat nat_from_word(uint64_t w) {   /* one limb: a bounded interning */
    if (w < NAT_BOX) return w;
    Nat r; KStack *s_ = kf_sync_begin(); box_limbs_push(s_, &r, 1, &w); kf_sync_run(s_); kf_sync_end(s_); return r;
}
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
KF_DECL_EXT(nat_compare, int, nat_compare_PARAMS, uint64_t ta, tb; size_t na, nb, i; const uint64_t *la, *lb;)
KF_STEP(nat_compare) {
    KF_BEGIN(nat_compare);
    if (F->a == F->b) KF_RET(0);
    if (nat_is_small(F->a) && nat_is_small(F->b)) KF_RET(F->a < F->b ? -1 : 1);
    F->la = nat_limbs(F->a, &F->na, &F->ta); F->lb = nat_limbs(F->b, &F->nb, &F->tb);
    fine_bump(FC_NAT_LIMBS);
    if (F->na != F->nb) KF_RET(F->na < F->nb ? -1 : 1);                 /* canonical lengths decide */
    for (F->i = F->na; F->i-- > 0; ) { fine_bump(FC_NAT_LIMBS); if (F->la[F->i] != F->lb[F->i]) KF_RET(F->la[F->i] < F->lb[F->i] ? -1 : 1); KF_SAFE(); }
    KF_RET(0);
    KF_END;
}
KF_SYNC_DEF(nat_compare, int, nat_compare_PARAMS, nat_compare(Nat a, Nat b))
KF_DECL_EXT_DROP(nat_add, Nat, nat_add_PARAMS, nat_add_drop, uint64_t ta, tb; size_t na, nb, n, i; const uint64_t *la, *lb; Words out; uint64_t carry; Nat r;)
static void nat_add_drop(nat_add_F *F) { words_free(&F->out); }
KF_STEP(nat_add) {
    KF_BEGIN(nat_add);
    if (nat_is_small(F->a) && nat_is_small(F->b) && F->a < NAT_BOX - F->b) KF_RET(F->a + F->b);   /* the immediate fast path */
    F->la = nat_limbs(F->a, &F->na, &F->ta); F->lb = nat_limbs(F->b, &F->nb, &F->tb);
    F->n = F->na > F->nb ? F->na : F->nb;
    require(F->n < SIZE_MAX, "nat: limb count overflow");
    words_init(&F->out); KF_CALL(words_reserve, NULL, &F->out, F->n + 1); F->carry = 0;   /* the sum's limbs: no growth inside the loop */
    for (F->i = 0; F->i < F->n; F->i++) {
        uint64_t x = F->i < F->na ? F->la[F->i] : 0, y = F->i < F->nb ? F->lb[F->i] : 0;
        uint64_t u = x + y, c1 = u < x, v = u + F->carry, c2 = v < u;
        words_push(&F->out, v); F->carry = c1 | c2; fine_bump(FC_NAT_LIMBS);
        KF_SAFE();
    }
    if (F->carry) words_push(&F->out, 1);
    KF_CALL(nat_from_limbs, &F->r, F->out.n, F->out.w);
    words_free(&F->out);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(nat_add, Nat, nat_add_PARAMS, nat_add(Nat a, Nat b))
KF_DECL_EXT_DROP(nat_sub_ge, Nat, nat_sub_ge_PARAMS, nat_sub_drop, uint64_t ta, tb; size_t na, nb, i; const uint64_t *la, *lb; Words out; uint64_t borrow; Nat r;)
static void nat_sub_drop(nat_sub_ge_F *F) { words_free(&F->out); }
KF_STEP(nat_sub_ge) {
    KF_BEGIN(nat_sub_ge);
    if (nat_is_small(F->a) && nat_is_small(F->b)) { require(F->a >= F->b, "nat: subtraction premise a >= b"); KF_RET(F->a - F->b); }
    F->la = nat_limbs(F->a, &F->na, &F->ta); F->lb = nat_limbs(F->b, &F->nb, &F->tb);
    require(F->na >= F->nb, "nat: subtraction premise a >= b");
    words_init(&F->out); KF_CALL(words_reserve, NULL, &F->out, F->na); F->borrow = 0;
    for (F->i = 0; F->i < F->na; F->i++) {
        uint64_t x = F->la[F->i], y = F->i < F->nb ? F->lb[F->i] : 0;
        uint64_t u = y + F->borrow, c = u < y;
        words_push(&F->out, x - u); F->borrow = c | (x < u); fine_bump(FC_NAT_LIMBS);
        KF_SAFE();
    }
    require(!F->borrow, "nat: subtraction premise a >= b");
    KF_CALL(nat_from_limbs, &F->r, F->out.n, F->out.w);
    words_free(&F->out);
    KF_RET(F->r);
    KF_END;
}
KF_SYNC_DEF(nat_sub_ge, Nat, nat_sub_ge_PARAMS, nat_sub_ge(Nat a, Nat b))
KF_DECL_EXT(nat_successor, Nat, nat_successor_PARAMS, Nat r;)
KF_STEP(nat_successor) { KF_BEGIN(nat_successor); KF_CALL(nat_add, &F->r, F->a, 1); KF_RET(F->r); KF_END; }
KF_SYNC_DEF(nat_successor, Nat, nat_successor_PARAMS, nat_successor(Nat a))
KF_DECL_EXT(nat_max, Nat, nat_max_PARAMS, int c;)
KF_STEP(nat_max) { KF_BEGIN(nat_max); KF_CALL(nat_compare, &F->c, F->a, F->b); KF_RET(F->c >= 0 ? F->a : F->b); KF_END; }
KF_SYNC_DEF(nat_max, Nat, nat_max_PARAMS, nat_max(Nat a, Nat b))
bool nat_to_u64(Nat a, uint64_t *out) {
    uint64_t t; size_t n; const uint64_t *l = nat_limbs(a, &n, &t);
    if (n > 1) return false;
    *out = n ? l[0] : 0; return true;
}
KF_DECL_EXT(nat_diff, NatDiff, nat_diff_PARAMS, NatDiff d; int c;)
KF_STEP(nat_diff) {
    KF_BEGIN(nat_diff);
    KF_CALL(nat_compare, &F->c, F->a, F->b);
    F->d.sign = F->c; F->d.magnitude = 0;
    if (F->c > 0) KF_CALL(nat_sub_ge, &F->d.magnitude, F->a, F->b);
    else if (F->c < 0) KF_CALL(nat_sub_ge, &F->d.magnitude, F->b, F->a);
    KF_RET(F->d);
    KF_END;
}
KF_SYNC_DEF(nat_diff, NatDiff, nat_diff_PARAMS, nat_diff(Nat a, Nat b))
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

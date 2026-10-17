/* xcount.c — see xcount.h. */
#include "xcount.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define NSTRIPES 64
static pthread_mutex_t stripes[NSTRIPES];
static pthread_once_t once = PTHREAD_ONCE_INIT;
static XCarry *all_records; static pthread_mutex_t all_mu = PTHREAD_MUTEX_INITIALIZER;
static void init_stripes(void) { for (int i = 0; i < NSTRIPES; i++) pthread_mutex_init(&stripes[i], NULL); }
static pthread_mutex_t *stripe(const void *c) { pthread_once(&once, init_stripes); return &stripes[((uintptr_t)c >> 4) % NSTRIPES]; }
static XCarry *record(const XCarry *next) {
    XCarry *r = malloc(sizeof *r);
    if (!r) { fprintf(stderr, "fatal: xcount: the host could not supply a carry record\n"); abort(); }
    r->next = next;
    pthread_mutex_lock(&all_mu); r->all_next = all_records; all_records = r; pthread_mutex_unlock(&all_mu);
    return r;
}
const XCarry *xc_carry_push(const XCarry *next) { return record(next); }
/* the digit reached 2^63: subtract 2^63 and install one carry record in one locked section (the value is unchanged) */
void xc_normalize2(uint64_t *low, const XCarry **carry) {
    pthread_mutex_t *m = stripe(low);
    pthread_mutex_lock(m);
    while (__atomic_load_n(low, __ATOMIC_RELAXED) >= XC_HALF) {
        __atomic_fetch_sub(low, XC_HALF, __ATOMIC_RELAXED);
        __atomic_store_n(carry, record(__atomic_load_n(carry, __ATOMIC_RELAXED)), __ATOMIC_RELEASE);
    }
    pthread_mutex_unlock(m);
}
void xc_add_large(uint64_t *low, const XCarry **carry, uint64_t n) {
    const uint64_t chunk = ((uint64_t)1 << 32) - 1;
    while (n) { uint64_t step = n < chunk ? n : chunk; xc_add2(low, carry, step); n -= step; }
}
XSnap xc_snap2(const uint64_t *low, const XCarry *const *carry) {
    pthread_mutex_t *m = stripe(low); XSnap s;
    pthread_mutex_lock(m);
    s.low = __atomic_load_n(low, __ATOMIC_RELAXED); s.carry = __atomic_load_n(carry, __ATOMIC_ACQUIRE);
    pthread_mutex_unlock(m);
    return s;
}
XSnap xc_snap(const XCount *c) {
    pthread_mutex_t *m = stripe(c); XSnap s;
    pthread_mutex_lock(m);
    s.low = __atomic_load_n(&c->low, __ATOMIC_RELAXED); s.carry = __atomic_load_n(&c->carry, __ATOMIC_ACQUIRE);
    pthread_mutex_unlock(m);
    return s;
}
XSnap xc_take(XCount *c) {
    pthread_mutex_t *m = stripe(c); XSnap s;
    pthread_mutex_lock(m);
    s.low = __atomic_exchange_n(&c->low, 0, __ATOMIC_ACQ_REL); s.carry = __atomic_exchange_n(&c->carry, NULL, __ATOMIC_ACQ_REL);
    pthread_mutex_unlock(m);
    return s;
}
void xc_add_snap(XCount *dst, XSnap s) {
    if (s.low) xc_add_large(&dst->low, &dst->carry, s.low);
    for (const XCarry *r = s.carry; r; r = r->next) {             /* one carry record of dst per carry of s */
        pthread_mutex_t *m = stripe(dst);
        pthread_mutex_lock(m);
        __atomic_store_n(&dst->carry, record(__atomic_load_n(&dst->carry, __ATOMIC_RELAXED)), __ATOMIC_RELEASE);
        pthread_mutex_unlock(m);
    }
}
void xc_reset(XCount *c) { pthread_mutex_t *m = stripe(c); pthread_mutex_lock(m); __atomic_store_n(&c->low, 0, __ATOMIC_RELAXED); __atomic_store_n(&c->carry, NULL, __ATOMIC_RELEASE); pthread_mutex_unlock(m); }
void xc_seed(XCount *c, uint64_t v) { pthread_mutex_t *m = stripe(&c->low); pthread_mutex_lock(m); const XCarry *k = NULL; if (v >= XC_HALF) { k = record(NULL); v -= XC_HALF; } __atomic_store_n(&c->low, v, __ATOMIC_RELAXED); __atomic_store_n(&c->carry, k, __ATOMIC_RELEASE); pthread_mutex_unlock(m); }
size_t xs_carries(XSnap s) { size_t n = 0; for (const XCarry *r = s.carry; r; r = r->next) n++; return n; }
bool xs_u64(XSnap s, uint64_t *out) {
    size_t k = xs_carries(s);
    if (k == 0) { *out = s.low; return true; }
    if (k == 1 && s.low < XC_HALF) { *out = s.low + XC_HALF; return true; }
    return false;
}
uint64_t xs_u64_checked(XSnap s, const char *what) {
    uint64_t v; if (xs_u64(s, &v)) return v;
    fprintf(stderr, "fatal: the exact count %s is %zu·2^63 + %llu, outside a machine word; read it exactly\n", what ? what : "", xs_carries(s), (unsigned long long)s.low);
    abort();
}
bool xs_eq(XSnap a, XSnap b) { unsigned __int128 x = (unsigned __int128)a.low + (unsigned __int128)xs_carries(a) * XC_HALF, y = (unsigned __int128)b.low + (unsigned __int128)xs_carries(b) * XC_HALF; return x == y; }
bool xs_delta_u64(XSnap a, XSnap b, uint64_t *out) {
    size_t k = 0; const XCarry *r = a.carry;
    while (r && r != b.carry) { r = r->next; k++; }              /* carries added since b */
    if (r != b.carry) return false;                               /* not snapshots of one counter in order */
    __int128 d = (__int128)a.low - (__int128)b.low + (__int128)k * (__int128)XC_HALF;
    if (d < 0 || d > (__int128)UINT64_MAX) return false;
    *out = (uint64_t)d; return true;
}

/* big.c — natural numbers beyond a machine word: the payload of a word cell (V_WORD, V_WPLUS)
 * whose number does not fit in 64 bits. Immutable and reference counted, like intervals. A
 * number is (s, b): b NULL means the number s; otherwise b holds it, little-endian limbs, at
 * least two, the top one nonzero. */
#include "core.h"
#include <string.h>

static Big *big_new(uint32_t n) { Big *b = malloc(sizeof(Big) + (size_t)n * sizeof(uint64_t)); b->rc = 1; b->n = n; return b; }
Big *big_retain(Big *b) { if (b) __atomic_fetch_add(&b->rc, 1, __ATOMIC_RELAXED); return b; }
void big_release(Big *b) { if (b && __atomic_sub_fetch(&b->rc, 1, __ATOMIC_ACQ_REL) == 0) free(b); }

/* the limbs of a number, without copying */
static const uint64_t *limbs(const WN *x, uint32_t *n) {
    if (x->b) { *n = x->b->n; return x->b->l; }
    *n = x->s ? 1 : 0; return &x->s;
}
/* a number from limbs (normalized: small when it fits) */
static WN from_limbs(uint64_t *l, uint32_t n) {
    while (n && !l[n - 1]) n--;
    WN r = { 0, NULL };
    if (n <= 1) { r.s = n ? l[0] : 0; return r; }
    r.b = big_new(n); memcpy(r.b->l, l, (size_t)n * sizeof(uint64_t));
    return r;
}
WN wn_small(uint64_t s) { WN r = { s, NULL }; return r; }
WN wn_copy(const WN *x) { WN r = *x; big_retain(r.b); return r; }
void wn_drop(WN *x) { big_release(x->b); x->b = NULL; x->s = 0; }
bool wn_zero(const WN *x) { return !x->b && x->s == 0; }
int wn_cmp(const WN *x, const WN *y) {
    uint32_t nx, ny; const uint64_t *a = limbs(x, &nx), *b = limbs(y, &ny);
    if (nx != ny) return nx < ny ? -1 : 1;
    for (uint32_t i = nx; i-- > 0; ) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}
WN wn_add(const WN *x, const WN *y) {
    uint32_t nx, ny; const uint64_t *a = limbs(x, &nx), *b = limbs(y, &ny);
    uint32_t n = (nx > ny ? nx : ny) + 1;
    uint64_t *l = calloc(n, sizeof(uint64_t)), c = 0;
    for (uint32_t i = 0; i < n; i++) {
        unsigned __int128 t = (unsigned __int128)(i < nx ? a[i] : 0) + (i < ny ? b[i] : 0) + c;
        l[i] = (uint64_t)t; c = (uint64_t)(t >> 64);
    }
    WN r = from_limbs(l, n); free(l); return r;
}
/* x - y when y ≤ x, else 0 */
WN wn_sub(const WN *x, const WN *y) {
    if (wn_cmp(x, y) <= 0) return wn_small(0);
    uint32_t nx, ny; const uint64_t *a = limbs(x, &nx), *b = limbs(y, &ny);
    uint64_t *l = calloc(nx, sizeof(uint64_t)), br = 0;
    for (uint32_t i = 0; i < nx; i++) {
        uint64_t bi = i < ny ? b[i] : 0;
        unsigned __int128 t = (unsigned __int128)a[i] - bi - br;
        l[i] = (uint64_t)t; br = (uint64_t)(t >> 64) ? 1 : 0;
    }
    WN r = from_limbs(l, nx); free(l); return r;
}
WN wn_succ(const WN *x) { WN one = wn_small(1); return wn_add(x, &one); }
/* decimal digits */
WN wn_parse(const char *s) {
    WN r = wn_small(0), ten = wn_small(10);
    for (; *s >= '0' && *s <= '9'; s++) {
        /* r = r*10 + d, as ten additions of r (the numbers parsed are written by hand) */
        WN acc = wn_small((uint64_t)(*s - '0'));
        for (int k = 0; k < 10; k++) { WN t = wn_add(&acc, &r); wn_drop(&acc); acc = t; }
        wn_drop(&r); r = acc;
    }
    (void)ten;
    return r;
}
void wn_print(FILE *o, const WN *x) {
    if (!x->b) { fprintf(o, "%llu", (unsigned long long)x->s); return; }
    /* repeated division by 10^19 */
    uint32_t n = x->b->n;
    uint64_t *l = malloc((size_t)n * sizeof(uint64_t)); memcpy(l, x->b->l, (size_t)n * sizeof(uint64_t));
    uint64_t *chunks = malloc(((size_t)n * 2 + 2) * sizeof(uint64_t)); int nc = 0;
    const uint64_t D = 10000000000000000000ull;
    while (n) {
        unsigned __int128 rem = 0;
        for (uint32_t i = n; i-- > 0; ) { unsigned __int128 cur = (rem << 64) | l[i]; l[i] = (uint64_t)(cur / D); rem = cur % D; }
        chunks[nc++] = (uint64_t)rem;
        while (n && !l[n - 1]) n--;
    }
    if (!nc) chunks[nc++] = 0;
    fprintf(o, "%llu", (unsigned long long)chunks[nc - 1]);
    for (int i = nc - 2; i >= 0; i--) fprintf(o, "%019llu", (unsigned long long)chunks[i]);
    free(l); free(chunks);
}

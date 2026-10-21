/* level.c — exact universe levels (term.h): a level is a word or, past the
 * word, an interned exact natural; successor and maximum of big levels are
 * families over exact signed integers, one limb per step. */
#include "eval.h"
#include "scope.h"

/* ---------------- exact signed integers ----------------
 * [sign, limb_0 .. limb_{k-1}], top limb nonzero, zero [0]. Constructors and
 * readers are host helpers; sum, product and negation are families, one limb
 * per step (limb arithmetic: common.h). */
static uint64_t z_make(int neg, size_t k, const uint64_t *mag) {
    while (k && !mag[k - 1]) k--;
    uint64_t *w = malloc((k + 1) * sizeof *w); require(w, "out of memory: an exact integer");
    w[0] = k ? (uint64_t)(neg != 0) : 0;
    for (size_t i = 0; i < k; i++) w[1 + i] = mag[i];
    uint64_t z = rq(k + 1, w); free(w); return z;
}
static uint64_t z_from_i64(int64_t v) { uint64_t m = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v; return z_make(v < 0, 1, &m); }
bool z_is_zero(uint64_t a) { size_t n; rget(a, &n); return n == 1; }
typedef struct { const uint64_t *a, *b; size_t na, nb, i, j, top; uint64_t c, neg, raw, acc; int cmp; WordBuf out; bool created; } ZLoc;
static uint64_t limb(const uint64_t *m, size_t n, size_t i) { return i < n ? m[i] : 0; }
/* z.add(a, b) */
static void zadd_step(Cont *k, uint64_t v) {
    ZLoc *L = FR_LOC(k, ZLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na); L->b = rget(k->w[1], &L->nb); L->na--; L->nb--;
    if (!L->na) FR_FINISH(k, k->w[1]);
    if (!L->nb) FR_FINISH(k, k->w[0]);
    if (L->a[0] == L->b[0]) {                                         /* one sign: the magnitudes add */
        wordbuf_init(&L->out); wordbuf_push(&L->out, L->a[0]); L->c = 0;
        for (L->i = 0; L->i < L->na || L->i < L->nb; L->i++) { wordbuf_push(&L->out, add_limb(limb(L->a + 1, L->na, L->i), limb(L->b + 1, L->nb, L->i), &L->c)); FR_YIELD(k); }
        if (L->c) wordbuf_push(&L->out, L->c);
        FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
        FR_FINISH(k, r);
    }
    /* opposite signs: compare the magnitudes from the top, then subtract the smaller */
    L->cmp = L->na < L->nb ? -1 : L->na > L->nb;
    for (L->i = L->na; !L->cmp && L->i-- > 0; ) { if (L->a[1 + L->i] != L->b[1 + L->i]) L->cmp = L->a[1 + L->i] < L->b[1 + L->i] ? -1 : 1; FR_YIELD(k); }
    if (!L->cmp) FR_FINISH(k, RQ(0));
    if (L->cmp < 0) { const uint64_t *t = L->a; L->a = L->b; L->b = t; size_t n = L->na; L->na = L->nb; L->nb = n; }
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->a[0]); L->c = 0; L->top = 0;
    for (L->i = 0; L->i < L->na; L->i++) { r = sub_limb(L->a[1 + L->i], limb(L->b + 1, L->nb, L->i), &L->c); wordbuf_push(&L->out, r); if (r) L->top = L->i + 1; FR_YIELD(k); }
    FR_CALL(k, L->raw, intern_sub(k, &M.keys, &L->out, &L->created));
    if (L->top == L->na) FR_FINISH(k, L->raw);
    wordbuf_init(&L->out);                                            /* the leading zero limbs dropped */
    for (L->i = 0; L->i <= L->top; L->i++) { size_t n; wordbuf_push(&L->out, rget(L->raw, &n)[L->i]); FR_YIELD(k); }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* z.neg(a) */
static void zneg_step(Cont *k, uint64_t v) {
    ZLoc *L = FR_LOC(k, ZLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na);
    if (L->na == 1) FR_FINISH(k, k->w[0]);
    wordbuf_init(&L->out); wordbuf_push(&L->out, !L->a[0]);
    for (L->i = 1; L->i < L->na; L->i++) { wordbuf_push(&L->out, L->a[L->i]); FR_YIELD(k); }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}

/* ---------------- universe levels: exact naturals (term.h) ---------------- */
static uint64_t level_z(uint64_t l) { return l & LEVEL_BIG ? l & ~LEVEL_BIG : z_make(0, 1, &l); }
static uint64_t level_of_z(uint64_t z) { size_t n; const uint64_t *w = rget(z, &n); return n == 1 ? 0 : n == 2 && !(w[1] & LEVEL_BIG) ? w[1] : LEVEL_BIG | z; }
bool level_succ_now(uint64_t a, uint64_t *out) {
    if (a == LEVEL_NONE || a + 1 < LEVEL_BIG) { *out = a == LEVEL_NONE ? a : a + 1; return true; }
    return false;
}
bool level_max_now(uint64_t a, uint64_t b, uint64_t *out) {
    if (a == LEVEL_NONE || b == LEVEL_NONE) { *out = LEVEL_NONE; return true; }
    if (a == b || ((a ^ b) & LEVEL_BIG)) { *out = (a & LEVEL_BIG) || a == b ? a : b; return true; }   /* a big level exceeds every word */
    if (!(a & LEVEL_BIG)) { *out = a > b ? a : b; return true; }
    return false;
}
typedef struct { uint64_t nb; } LvLoc;
static void lsucc_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_AWAIT(k, r, Fz_ADD, level_z(k->w[0]), z_from_i64(1));
    FR_FINISH(k, level_of_z(r));
    FR_END(k);
}
/* two big levels: the sign of a − b */
static void lmax_step(Cont *k, uint64_t v) {
    LvLoc *L = FR_LOC(k, LvLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_AWAIT(k, L->nb, Fz_NEG, level_z(k->w[1]), 0);
    FR_AWAIT(k, r, Fz_ADD, level_z(k->w[0]), L->nb);
    FR_FINISH(k, rword(r, 0) ? k->w[1] : k->w[0]);
    FR_END(k);
}
uint64_t level_succ(uint64_t a) { uint64_t r; return level_succ_now(a, &r) ? r : family_call(F_LSUCC, a, 0); }
void level_print(uint64_t l, FILE *f) {
    if (!(l & LEVEL_BIG)) { fprintf(f, "%llu", (unsigned long long)l); return; }
    size_t n; const uint64_t *w = rget(l & ~LEVEL_BIG, &n);
    fprintf(f, "0x%llx", (unsigned long long)w[n - 1]);
    for (size_t i = n - 1; i-- > 1; ) fprintf(f, "%016llx", (unsigned long long)w[i]);
}

void level_families_init(void) {
    family_define(Fz_ADD, "z.add", zadd_step, sizeof(ZLoc));
    family_define(Fz_NEG, "z.neg", zneg_step, sizeof(ZLoc));
    family_define(F_LSUCC, "level.succ", lsucc_step, 0);
    family_define(F_LMAX, "level.max", lmax_step, sizeof(LvLoc));
}

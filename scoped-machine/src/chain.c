/* chain.c — the additive reading (chain.h). */
#include "chain.h"
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
uint64_t z_from_limbs(int negative, size_t n, const uint64_t *limbs) { return z_make(negative, n, limbs); }
uint64_t z_from_i64(int64_t v) { uint64_t m = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v; return z_make(v < 0, 1, &m); }
bool z_is_zero(uint64_t a) { size_t n; rget(a, &n); return n == 1; }
bool z_to_i64(uint64_t a, int64_t *out) {
    size_t n; const uint64_t *w = rget(a, &n);
    if (n == 1) { *out = 0; return true; }
    if (n > 2) return false;
    if (w[0]) { if (w[1] > (uint64_t)INT64_MAX + 1) return false; *out = (int64_t)((uint64_t)0 - w[1]); }
    else { if (w[1] > (uint64_t)INT64_MAX) return false; *out = (int64_t)w[1]; }
    return true;
}
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
/* z.mul(a, b): a sum of shifted rows b · a_i, each a limb per step */
static void zmul_step(Cont *k, uint64_t v) {
    ZLoc *L = FR_LOC(k, ZLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na); L->b = rget(k->w[1], &L->nb); L->na--; L->nb--;
    L->acc = RQ(0);
    if (!L->na || !L->nb) FR_FINISH(k, L->acc);
    L->neg = L->a[0] != L->b[0];
    for (L->i = 0; L->i < L->na; L->i++) {
        if (!L->a[1 + L->i]) { FR_YIELD(k); continue; }
        wordbuf_init(&L->out); wordbuf_push(&L->out, L->neg);
        for (L->j = 0; L->j < L->i; L->j++) { wordbuf_push(&L->out, 0); FR_YIELD(k); }
        for (L->c = 0, L->j = 0; L->j < L->nb; L->j++) { wordbuf_push(&L->out, mul_limb(L->a[1 + L->i], L->b[1 + L->j], &L->c)); FR_YIELD(k); }
        if (L->c) wordbuf_push(&L->out, L->c);
        FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
        FR_AWAIT(k, L->acc, Fz_ADD, L->acc, r);
    }
    FR_FINISH(k, L->acc);
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
uint64_t z_add(uint64_t a, uint64_t b) { return family_call(Fz_ADD, a, b); }

/* ---------------- universe levels: exact naturals (term.h) ---------------- */
static uint64_t level_z(uint64_t l) { return l & LEVEL_BIG ? l & ~LEVEL_BIG : z_make(0, 1, &l); }
static uint64_t level_of_z(uint64_t z) { size_t n; const uint64_t *w = rget(z, &n); return n == 1 ? 0 : n == 2 && !(w[1] & LEVEL_BIG) ? w[1] : LEVEL_BIG | z; }
uint64_t level_from_limbs(size_t n, const uint64_t *limbs) { return level_of_z(z_make(0, n, limbs)); }
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
uint64_t level_max(uint64_t a, uint64_t b) { uint64_t r; return level_max_now(a, b, &r) ? r : family_call(F_LMAX, a, b); }
void level_print(uint64_t l, FILE *f) {
    if (!(l & LEVEL_BIG)) { fprintf(f, "%llu", (unsigned long long)l); return; }
    size_t n; const uint64_t *w = rget(l & ~LEVEL_BIG, &n);
    fprintf(f, "0x%llx", (unsigned long long)w[n - 1]);
    for (size_t i = n - 1; i-- > 1; ) fprintf(f, "%016llx", (unsigned long long)w[i]);
}
uint64_t z_neg(uint64_t a) { return family_call(Fz_NEG, a, 0); }
uint64_t z_mul(uint64_t a, uint64_t b) { return family_call(Fz_MUL, a, b); }

/* ---------------- module elements: 0-chains over unit generators ---------------- */
uint64_t m_zero(void) { return RQ(0); }
uint64_t m_unit(uint64_t unit, uint64_t z) { return z_is_zero(z) ? m_zero() : RQ(0, G_UNIT, unit, z); }
uint64_t m_add(uint64_t a, uint64_t b) { return chain_add(a, b); }
uint64_t m_scale(uint64_t z, uint64_t m) { return chain_scale(m, z); }

/* ---------------- cells ---------------- */
DimVarId cube_coord(size_t k) { KeyWord key[2] = { { KW_CONST, 9500 }, { KW_CONST, k } }; return fresh_dim_keyed(key, 2); }
uint64_t cube_view(ScopeId root, MapId params) {
    size_t n = scope_arity(root);
    for (size_t r = 0; r < n; r++) require(scope_local(root, r).sort == S_DIM, "a presented cell's locals are dimensions");
    uint64_t *w = malloc((4 + n) * sizeof *w); require(w, "out of memory: a cube view");
    w[0] = root; w[1] = n; w[2] = params; w[3] = n;
    for (size_t r = 0; r < n; r++) w[4 + r] = iv_var(cube_coord(r + 1));      /* coordinates created in order */
    uint64_t v = rq(4 + n, w); free(w); return v;
}
uint64_t cube_subst(uint64_t view, MapId sigma) {
    size_t n; const uint64_t *v = rget(view, &n);
    uint64_t *w = malloc(n * sizeof *w); require(w, "out of memory: a cube view");
    memcpy(w, v, n * sizeof *w); w[2] = compose((MapId)v[2], sigma);
    uint64_t r = rq(n, w); free(w); return r;
}
uint64_t cube_product(GenKind kx, uint64_t x, GenKind ky, uint64_t y) { return RQ(kx, x, ky, y, gen_degree(kx, x) + gen_degree(ky, y)); }
size_t gen_degree(GenKind kind, uint64_t id) {
    size_t n; const uint64_t *w = rget(id, &n);
    switch (kind) {
    case G_CUBE: return (size_t)w[1];
    case G_PROD: return (size_t)w[4];
    case G_OCC: return 1;
    case G_TWIST: return gen_degree(G_CUBE, w[0]);
    default: return 0;
    }
}
static uint64_t genrec(GenKind k, uint64_t id) { return RQ(k, id); }


/* cube.reindex(view, [m2, image_1..image_m]): the map c_k ↦ image_k
 * (one entry per step, keys ascending), then each root image reindexed */
typedef struct { const uint64_t *v, *s; size_t nv, ns, k; uint64_t map; WordBuf out; bool created; } RxLoc;
static void reindex_step(Cont *k, uint64_t v) {
    RxLoc *L = FR_LOC(k, RxLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->v = rget(k->w[0], &L->nv); L->s = rget(k->w[1], &L->ns);
    require(L->ns == 1 + L->v[1], "cube reindex: one image per coordinate");
    wordbuf_init(&L->out);
    for (L->k = 1; L->k <= L->v[1]; L->k++) {
        {   DimVarId c = cube_coord(L->k);
            if (L->s[L->k] != iv_var(c)) { wordbuf_push(&L->out, c); wordbuf_push(&L->out, PS_INTERVAL); wordbuf_push(&L->out, L->s[L->k]); } }
        FR_YIELD(k);
    }
    FR_CALL(k, L->map, intern_sub(k, &M.keys, &L->out, &L->created));
    wordbuf_init(&L->out);
    wordbuf_push(&L->out, L->v[0]); wordbuf_push(&L->out, L->s[0]); wordbuf_push(&L->out, L->v[2]); wordbuf_push(&L->out, L->v[3]);
    for (L->k = 0; L->k < L->v[3]; L->k++) {
        FR_AWAIT(k, r, F_TIV, L->v[4 + L->k], re_key(L->map));
        wordbuf_push(&L->out, r);
    }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* cell.face(gen record, [i, ε]) → gen record: a view's face map, or the
 * face of a product's component (i ≤ p: of x; otherwise of y at i − p) */
typedef struct { size_t i, j, m; int eps; uint64_t x; WordBuf out; bool created; } FcLoc;
static void face_step(Cont *k, uint64_t v) {
    FcLoc *L = FR_LOC(k, FcLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    {   size_t n; const uint64_t *g = rget(k->w[0], &n), *e = rget(k->w[1], &n); L->i = (size_t)e[0]; L->eps = (int)e[1];
        require(L->i >= 1 && L->i <= gen_degree((GenKind)g[0], g[1]), "face coordinate out of range"); }
    if (rget(k->w[0], &(size_t){0})[0] == G_PROD) {
        {   size_t n; const uint64_t *g = rget(k->w[0], &n), *p = rget(g[1], &n);
            size_t dx = gen_degree((GenKind)p[0], p[1]);
            uint64_t e[2] = { L->i <= dx ? L->i : L->i - dx, (uint64_t)L->eps };
            L->j = L->i <= dx; L->x = L->j ? genrec((GenKind)p[0], p[1]) : genrec((GenKind)p[2], p[3]);
            L->m = rq(2, e); }
        FR_AWAIT(k, r, Fc_FACE, L->x, L->m);
        {   size_t n; const uint64_t *g = rget(k->w[0], &n), *p = rget(g[1], &n), *f = rget(r, &n);
            uint64_t pr = L->j ? cube_product((GenKind)f[0], f[1], (GenKind)p[2], p[3]) : cube_product((GenKind)p[0], p[1], (GenKind)f[0], f[1]);
            FR_FINISH(k, genrec(G_PROD, pr)); }
    }
    {   size_t n; const uint64_t *g = rget(k->w[0], &n); L->x = g[1]; L->m = rget(L->x, &n)[1]; }
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->m - 1);
    for (L->j = 1; L->j <= L->m; L->j++) {
        wordbuf_push(&L->out, L->j < L->i ? iv_var(cube_coord(L->j)) : L->j == L->i ? (L->eps ? iv_one() : iv_zero()) : iv_var(cube_coord(L->j - 1)));
        FR_YIELD(k);
    }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_AWAIT(k, r, Fc_REIDX, L->x, r);
    FR_FINISH(k, genrec(G_CUBE, r));
    FR_END(k);
}

/* chain.add(c1, c2): one output term per step */
typedef struct { const uint64_t *a, *b; size_t na, nb, i, j; WordBuf out; bool created; } AddLoc;
static int gen_cmp(const uint64_t *x, const uint64_t *y) { return x[0] != y[0] ? (x[0] < y[0] ? -1 : 1) : x[1] != y[1] ? (x[1] < y[1] ? -1 : 1) : 0; }
static void add_step(Cont *k, uint64_t v) {
    AddLoc *L = FR_LOC(k, AddLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na); L->b = rget(k->w[1], &L->nb);
    require(L->na == 1 || L->nb == 1 || L->a[0] == L->b[0], "adding chains of different degrees");
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->na > 1 ? L->a[0] : L->b[0]);
    for (L->i = 1, L->j = 1; L->i < L->na || L->j < L->nb; ) {
        {   int c = L->i >= L->na ? 1 : L->j >= L->nb ? -1 : gen_cmp(L->a + L->i, L->b + L->j);
            if (c < 0) { wordbuf_push(&L->out, L->a[L->i]); wordbuf_push(&L->out, L->a[L->i + 1]); wordbuf_push(&L->out, L->a[L->i + 2]); L->i += 3; }
            else if (c > 0) { wordbuf_push(&L->out, L->b[L->j]); wordbuf_push(&L->out, L->b[L->j + 1]); wordbuf_push(&L->out, L->b[L->j + 2]); L->j += 3; }
            else {
                FR_AWAIT(k, r, Fz_ADD, L->a[L->i + 2], L->b[L->j + 2]);
                if (!z_is_zero(r)) { wordbuf_push(&L->out, L->a[L->i]); wordbuf_push(&L->out, L->a[L->i + 1]); wordbuf_push(&L->out, r); }
                L->i += 3; L->j += 3; continue;
            } }
        FR_YIELD(k);
    }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* chain.scale(c, z) */
static void scale_step(Cont *k, uint64_t v) {
    AddLoc *L = FR_LOC(k, AddLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na);
    wordbuf_init(&L->out); wordbuf_push(&L->out, L->a[0]);
    if (!z_is_zero(k->w[1]))
        for (L->i = 1; L->i < L->na; L->i += 3) {
            FR_AWAIT(k, r, Fz_MUL, k->w[1], L->a[L->i + 2]);
            wordbuf_push(&L->out, L->a[L->i]); wordbuf_push(&L->out, L->a[L->i + 1]); wordbuf_push(&L->out, r);
        }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* chain.boundary(c): for each term and coordinate, the upper and lower faces
 * with signs (−1)^(i−1) and −(−1)^(i−1); an occurrence's resource boundary;
 * nothing in degree 0 */
typedef struct { const uint64_t *c; size_t nc, t, i, n; int eps; uint64_t acc, g, z, f; } BdLoc;
static void boundary_step(Cont *k, uint64_t v) {
    BdLoc *L = FR_LOC(k, BdLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->c = rget(k->w[0], &L->nc);
    L->acc = RQ(L->c[0] ? L->c[0] - 1 : 0);
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        L->n = gen_degree((GenKind)L->c[L->t], L->c[L->t + 1]);
        if ((GenKind)L->c[L->t] == G_OCC) {
            FR_AWAIT(k, r, F_OCCB, L->c[L->t + 1], 0);
            FR_AWAIT(k, r, Fc_SCALE, r, L->c[L->t + 2]);
            FR_AWAIT(k, L->acc, Fc_ADD, L->acc, r);
            continue;
        }
        if ((GenKind)L->c[L->t] != G_CUBE && (GenKind)L->c[L->t] != G_PROD) { FR_YIELD(k); continue; }
        L->g = genrec((GenKind)L->c[L->t], L->c[L->t + 1]);
        for (L->i = 1; L->i <= L->n; L->i++)
            for (L->eps = 1; L->eps >= 0; L->eps--) {
                L->z = RQ(L->i, (uint64_t)L->eps);
                FR_AWAIT(k, L->f, Fc_FACE, L->g, L->z);
                L->z = L->c[L->t + 2];                              /* sign (−1)^(i−1), negated on the lower face */
                if (((L->i - 1) % 2) ^ !L->eps) FR_AWAIT(k, L->z, Fz_NEG, L->z, 0);
                {   size_t n; const uint64_t *f = rget(L->f, &n); L->z = RQ(L->c[0] - 1, f[0], f[1], L->z); }
                FR_AWAIT(k, L->acc, Fc_ADD, L->acc, L->z);
            }
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
/* cochain.value(a, gen record) → module: a table entry (zero if absent), or
 * for COB(b) the pairing of b with the generator's boundary */
typedef struct { const uint64_t *a; size_t na, i; uint64_t g, c; } ValLoc;
static void value_step(Cont *k, uint64_t v) {
    ValLoc *L = FR_LOC(k, ValLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->a = rget(k->w[0], &L->na);
    {   size_t n; const uint64_t *g = rget(k->w[1], &n); L->g = g[0]; L->c = g[1]; }
    if (L->a[0] == CO_COB) {
        L->c = RQ(gen_degree((GenKind)L->g, L->c), L->g, L->c, z_from_i64(1));
        if (L->na == 3) FR_AWAIT(k, r, Fc_TBOUNDARY, L->c, L->a[2]);
        else FR_AWAIT(k, r, Fc_BOUNDARY, L->c, 0);
        FR_AWAIT(k, r, Fc_PAIR, L->a[1], r);
        FR_FINISH(k, r);
    }
    for (L->i = 2; L->i < L->na; L->i += 3) {
        if (L->a[L->i] == L->g && L->a[L->i + 1] == L->c) FR_FINISH(k, L->a[L->i + 2]);
        FR_YIELD(k);
    }
    FR_FINISH(k, m_zero());
    FR_END(k);
}
/* chain.pair(a, c) = Σ z_x · a(x) */
typedef struct { const uint64_t *c; size_t nc, t; uint64_t acc; } PairLoc;
static void pair_step(Cont *k, uint64_t v) {
    PairLoc *L = FR_LOC(k, PairLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->c = rget(k->w[1], &L->nc); L->acc = m_zero();
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        FR_AWAIT(k, r, Fc_VALUE, k->w[0], genrec((GenKind)L->c[L->t], L->c[L->t + 1]));
        FR_AWAIT(k, r, Fc_SCALE, r, L->c[L->t + 2]);
        FR_AWAIT(k, L->acc, Fc_ADD, L->acc, r);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}
/* chain.map(F, c) = Σ z_x F(x); a generator without an image maps to 0 */
typedef struct { const uint64_t *f, *c; size_t nf, nc, t, i; uint64_t acc, img; } MapLoc;
static void map_step(Cont *k, uint64_t v) {
    MapLoc *L = FR_LOC(k, MapLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->f = rget(k->w[0], &L->nf); L->c = rget(k->w[1], &L->nc);
    require(L->c[0] == L->f[0] || L->nc == 1, "a chain map applied at another degree");
    L->acc = RQ(L->f[0]);
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        for (L->img = 0, L->i = 1; L->i < L->nf && !L->img; L->i += 3) {
            if (L->f[L->i] == L->c[L->t] && L->f[L->i + 1] == L->c[L->t + 1]) L->img = L->f[L->i + 2];
            FR_YIELD(k);
        }
        if (!L->img) { FR_YIELD(k); continue; }
        FR_AWAIT(k, r, Fc_SCALE, L->img, L->c[L->t + 2]);
        FR_AWAIT(k, L->acc, Fc_ADD, L->acc, r);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

/* ---------------- local coefficients ---------------- */
uint64_t perm_of(size_t n, const uint64_t *from, const uint64_t *to) {
    uint64_t *w = malloc((2 * n + 1) * sizeof *w); require(w, "out of memory");
    for (size_t i = 0; i < n; i++) { w[2 * i] = from[i]; w[2 * i + 1] = to[i]; }
    for (size_t i = 1; i < n; i++) for (size_t j = i; j > 0 && w[2 * j - 2] > w[2 * j]; j--) {
        uint64_t a = w[2 * j - 2], b = w[2 * j - 1]; w[2 * j - 2] = w[2 * j]; w[2 * j - 1] = w[2 * j + 1]; w[2 * j] = a; w[2 * j + 1] = b;
    }
    uint64_t r = rq(2 * n, w); free(w); return r;
}
static uint64_t perm_apply(uint64_t perm, uint64_t u) {
    size_t n; const uint64_t *w = rget(perm, &n);
    for (size_t i = 0; i < n; i += 2) if (w[i] == u) return w[i + 1];
    return u;
}
uint64_t local_system(ScopeId root, size_t nperm, const uint64_t *perms, size_t npairs, const uint64_t *pairs) {
    require(nperm == scope_arity(root), "one transport per dimension local");
    /* the square witness: every pair r < s named, and commuting on every unit either moves */
    for (size_t r = 0; r < nperm; r++) for (size_t s = r + 1; s < nperm; s++) {
        bool named = false;
        for (size_t q = 0; q < npairs; q++) if (pairs[2 * q] == r && pairs[2 * q + 1] == s) named = true;
        if (!named) return 0;
        size_t n1, n2; const uint64_t *a = rget(perms[r], &n1), *b = rget(perms[s], &n2);
        for (size_t i = 0; i < n1 + n2; i += 2) {
            uint64_t u = i < n1 ? a[i] : b[i - n1];
            if (perm_apply(perms[r], perm_apply(perms[s], u)) != perm_apply(perms[s], perm_apply(perms[r], u))) return 0;
        }
    }
    uint64_t *w = malloc((nperm + 2) * sizeof *w); require(w, "out of memory");
    w[0] = root; w[1] = nperm; for (size_t r = 0; r < nperm; r++) w[2 + r] = perms[r];
    uint64_t sys = rq(nperm + 2, w); free(w); return sys;
}
uint64_t twist_gen(uint64_t view, uint64_t unit) { return RQ(view, unit); }
/* chain.tboundary(c, sys): for [x, u] and each coordinate i, the upper face
 * carries T_i(u), the lower face u, with signs (−1)^(i−1) and −(−1)^(i−1) */
typedef struct { const uint64_t *c; size_t nc, t, i, q, nr, np; int eps; uint64_t acc, g, z, u, x, f, unit, perm; } TbLoc;
static void tboundary_step(Cont *k, uint64_t v) {
    TbLoc *L = FR_LOC(k, TbLoc);
    FR_BEGIN(k);
    L->c = rget(k->w[0], &L->nc);
    L->acc = RQ(L->c[0] ? L->c[0] - 1 : 0);
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        require((GenKind)L->c[L->t] == G_TWIST, "a twisted boundary of an untwisted generator");
        {   size_t n; const uint64_t *tw = rget(L->c[L->t + 1], &n); L->x = tw[0]; L->u = tw[1]; L->g = genrec(G_CUBE, L->x); }
        for (L->i = 1; L->i <= gen_degree(G_CUBE, L->x); L->i++)
            for (L->eps = 1; L->eps >= 0; L->eps--) {
                L->z = RQ(L->i, (uint64_t)L->eps);
                FR_AWAIT(k, L->f, Fc_FACE, L->g, L->z);
                L->unit = L->u;
                if (L->eps) {                                       /* the transport of the root local whose image is c_i: one local, one transport entry per step */
                    {   size_t n; const uint64_t *vw = rget(L->x, &n), *sys = rget(k->w[1], &n); require(sys[0] == vw[0], "a coordinate without its transport in this local system"); L->nr = vw[3]; }
                    for (L->q = 0; L->q < L->nr; L->q++) { size_t n; if (rget(L->x, &n)[4 + L->q] == iv_var(cube_coord(L->i))) break; FR_YIELD(k); }
                    require(L->q < L->nr, "a coordinate without its transport in this local system");
                    {   L->perm = rword(k->w[1], 2 + L->q); }
                    for (L->q = 0; L->q < (rget(L->perm, &L->np), L->np); L->q += 2) { size_t n; const uint64_t *pw = rget(L->perm, &n); if (pw[L->q] == L->u) { L->unit = pw[L->q + 1]; break; } FR_YIELD(k); }
                }
                L->z = L->c[L->t + 2];
                if (((L->i - 1) % 2) ^ !L->eps) FR_AWAIT(k, L->z, Fz_NEG, L->z, 0);
                {   size_t n; const uint64_t *f = rget(L->f, &n); L->z = RQ(L->c[0] - 1, G_TWIST, twist_gen(f[1], L->unit), L->z); }
                FR_AWAIT(k, L->acc, Fc_ADD, L->acc, L->z);
            }
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

void chain_families_init(void) {
    family_define(Fc_REIDX, "cube.reindex", reindex_step, sizeof(RxLoc));
    family_define(Fc_FACE, "cell.face", face_step, sizeof(FcLoc));
    family_define(Fc_ADD, "chain.add", add_step, sizeof(AddLoc));
    family_define(Fc_SCALE, "chain.scale", scale_step, sizeof(AddLoc));
    family_define(Fc_BOUNDARY, "chain.boundary", boundary_step, sizeof(BdLoc));
    family_define(Fc_VALUE, "cochain.value", value_step, sizeof(ValLoc));
    family_define(Fc_PAIR, "chain.pair", pair_step, sizeof(PairLoc));
    family_define(Fc_MAP, "chain.map", map_step, sizeof(MapLoc));
    family_define(Fc_TBOUNDARY, "chain.twisted_boundary", tboundary_step, sizeof(TbLoc));
    family_define(Fz_ADD, "z.add", zadd_step, sizeof(ZLoc));
    family_define(Fz_MUL, "z.mul", zmul_step, sizeof(ZLoc));
    family_define(Fz_NEG, "z.neg", zneg_step, sizeof(ZLoc));
    family_define(F_LSUCC, "level.succ", lsucc_step, 0);
    family_define(F_LMAX, "level.max", lmax_step, sizeof(LvLoc));
}

/* ---------------- synchronous drivers ---------------- */
static uint64_t terms(size_t head_n, const uint64_t *head, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *vals) {
    /* sorted by (kind, id); equal generators combined by the families' own addition */
    uint64_t *w = malloc((head_n + 3 * n + 1) * sizeof *w); require(w, "out of memory: a term list");
    for (size_t i = 0; i < head_n; i++) w[i] = head[i];
    size_t *ord = malloc((n + 1) * sizeof *ord); require(ord, "out of memory");
    for (size_t i = 0; i < n; i++) ord[i] = i;
    for (size_t i = 1; i < n; i++) for (size_t j = i; j > 0; j--) {
        size_t a = ord[j - 1], b = ord[j];
        if (kinds[a] > kinds[b] || (kinds[a] == kinds[b] && ids[a] > ids[b])) { ord[j - 1] = b; ord[j] = a; } else break;
    }
    for (size_t i = 0; i < n; i++) { size_t q = ord[i]; require(i == 0 || kinds[ord[i - 1]] != kinds[q] || ids[ord[i - 1]] != ids[q], "a repeated generator in a literal"); w[head_n + 3 * i] = kinds[q]; w[head_n + 3 * i + 1] = ids[q]; w[head_n + 3 * i + 2] = vals[q]; }
    uint64_t r = rq(head_n + 3 * n, w); free(w); free(ord); return r;
}
uint64_t chain_of(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *zs) {
    for (size_t i = 0; i < n; i++) require(!z_is_zero(zs[i]), "a zero coefficient in a chain literal");
    uint64_t h[1] = { degree }; return terms(1, h, n, kinds, ids, zs);
}
uint64_t cochain_table(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *ms) { uint64_t h[2] = { CO_TABLE, degree }; return terms(2, h, n, kinds, ids, ms); }
uint64_t cochain_cob(uint64_t a) { return RQ(CO_COB, a); }
uint64_t chain_map_table(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *images) { uint64_t h[1] = { degree }; return terms(1, h, n, kinds, ids, images); }
uint64_t cube_face(GenKind kind, uint64_t id, size_t i, int eps, GenKind *out_kind) {
    uint64_t e[2] = { i, (uint64_t)eps };
    uint64_t g = family_call(Fc_FACE, genrec(kind, id), rq(2, e));
    size_t n; const uint64_t *w = rget(g, &n); *out_kind = (GenKind)w[0]; return w[1];
}
uint64_t cube_reindex(uint64_t view, size_t m2, const IntervalId *images) {
    size_t nv; const uint64_t *v = rget(view, &nv); size_t m = (size_t)v[1];
    uint64_t *w = malloc((m + 1) * sizeof *w); require(w, "out of memory");
    w[0] = m2; for (size_t k = 0; k < m; k++) w[1 + k] = images[k];
    uint64_t s = rq(m + 1, w); free(w);
    return family_call(Fc_REIDX, view, s);
}
uint64_t chain_add(uint64_t c1, uint64_t c2) { return family_call(Fc_ADD, c1, c2); }
uint64_t chain_scale(uint64_t c, uint64_t z) { return family_call(Fc_SCALE, c, z); }
uint64_t chain_boundary(uint64_t c) { return family_call(Fc_BOUNDARY, c, 0); }
uint64_t chain_pair(uint64_t a, uint64_t c) { return family_call(Fc_PAIR, a, c); }
uint64_t chain_map(uint64_t F, uint64_t c) { return family_call(Fc_MAP, F, c); }
uint64_t chain_tboundary(uint64_t c, uint64_t sys) { require(sys, "a twisted boundary needs an admitted local system"); return family_call(Fc_TBOUNDARY, c, sys); }
uint64_t cochain_cob_local(uint64_t a, uint64_t sys) { require(sys, "a twisted differential needs an admitted local system"); uint64_t w[3] = { CO_COB, a, sys }; return rq(3, w); }
uint64_t chain_relative(uint64_t c, uint64_t I) {
    size_t nc, ni; const uint64_t *w = rget(c, &nc), *iw = rget(I, &ni);
    uint64_t *o = malloc(nc * sizeof *o); require(o, "out of memory"); size_t n = 0;
    o[n++] = w[0];
    for (size_t t = 1; t < nc; t += 3) {
        bool in = false; for (size_t q = 1; q < ni && !in; q += 3) in = iw[q] == w[t] && iw[q + 1] == w[t + 1];
        if (!in) { o[n++] = w[t]; o[n++] = w[t + 1]; o[n++] = w[t + 2]; }
    }
    uint64_t r = rq(n, o); free(o); return r;
}

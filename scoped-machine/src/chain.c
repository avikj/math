/* chain.c — the additive reading (chain.h). */
#include "chain.h"
#include "scope.h"

static uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
static const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }

/* ---------------- exact signed integers ---------------- */
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
static int mag_cmp(const uint64_t *a, size_t na, const uint64_t *b, size_t nb) {
    if (na != nb) return na < nb ? -1 : 1;
    for (size_t i = na; i-- > 0; ) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}
uint64_t z_add(uint64_t a, uint64_t b) {
    size_t na, nb; const uint64_t *wa = rget(a, &na), *wb = rget(b, &nb);
    na--; nb--;
    int sa = (int)wa[0], sb = (int)wb[0];
    size_t n = (na > nb ? na : nb) + 1;
    uint64_t *r = calloc(n, sizeof *r); require(r, "out of memory: an exact sum");
    int neg;
    if (sa == sb || !na || !nb) {
        uint64_t c = 0;
        for (size_t i = 0; i < n; i++) {
            uint64_t x = i < na ? wa[1 + i] : 0, y = i < nb ? wb[1 + i] : 0;
            uint64_t s = x + y; uint64_t c1 = s < x; uint64_t s2 = s + c; uint64_t c2 = s2 < s;
            r[i] = s2; c = c1 | c2;
        }
        neg = na ? sa : sb;
    } else {
        const uint64_t *big = wa + 1, *small = wb + 1; size_t nbig = na, nsmall = nb; neg = sa;
        if (mag_cmp(wa + 1, na, wb + 1, nb) < 0) { big = wb + 1; small = wa + 1; nbig = nb; nsmall = na; neg = sb; }
        uint64_t br = 0;
        for (size_t i = 0; i < nbig; i++) {
            uint64_t x = big[i], y = i < nsmall ? small[i] : 0;
            uint64_t d = x - y; uint64_t b1 = x < y; uint64_t d2 = d - br; uint64_t b2 = d < br;
            r[i] = d2; br = b1 | b2;
        }
    }
    uint64_t z = z_make(neg, n, r); free(r); return z;
}
uint64_t z_neg(uint64_t a) { size_t n; const uint64_t *w = rget(a, &n); return z_make(!w[0], n - 1, w + 1); }
uint64_t z_mul(uint64_t a, uint64_t b) {
    size_t na, nb; const uint64_t *wa = rget(a, &na), *wb = rget(b, &nb);
    na--; nb--;
    if (!na || !nb) return z_make(0, 0, NULL);
    uint64_t *r = calloc(na + nb, sizeof *r); require(r, "out of memory: an exact product");
    for (size_t i = 0; i < na; i++) {
        unsigned __int128 c = 0;
        for (size_t j = 0; j < nb; j++) {
            unsigned __int128 t = (unsigned __int128)wa[1 + i] * wb[1 + j] + r[i + j] + c;
            r[i + j] = (uint64_t)t; c = t >> 64;
        }
        r[i + nb] = (uint64_t)c;
    }
    uint64_t z = z_make(wa[0] != wb[0], na + nb, r); free(r); return z;
}
bool z_to_i64(uint64_t a, int64_t *out) {
    size_t n; const uint64_t *w = rget(a, &n);
    if (n == 1) { *out = 0; return true; }
    if (n > 2) return false;
    if (w[0]) { if (w[1] > (uint64_t)INT64_MAX + 1) return false; *out = (int64_t)((uint64_t)0 - w[1]); }
    else { if (w[1] > (uint64_t)INT64_MAX) return false; *out = (int64_t)w[1]; }
    return true;
}

/* ---------------- module elements ---------------- */
uint64_t m_zero(void) { return rq(0, NULL); }
uint64_t m_unit(uint64_t unit, uint64_t z) { if (z_is_zero(z)) return m_zero(); uint64_t w[2] = { unit, z }; return rq(2, w); }
uint64_t m_add(uint64_t a, uint64_t b) {
    size_t na, nb; const uint64_t *wa = rget(a, &na), *wb = rget(b, &nb);
    uint64_t *o = malloc((na + nb + 1) * sizeof *o); require(o, "out of memory: a module sum");
    size_t i = 0, j = 0, n = 0;
    while (i < na || j < nb) {
        if (j >= nb || (i < na && wa[i] < wb[j])) { o[n++] = wa[i]; o[n++] = wa[i + 1]; i += 2; }
        else if (i >= na || wb[j] < wa[i]) { o[n++] = wb[j]; o[n++] = wb[j + 1]; j += 2; }
        else { uint64_t s = z_add(wa[i + 1], wb[j + 1]); if (!z_is_zero(s)) { o[n++] = wa[i]; o[n++] = s; } i += 2; j += 2; }
    }
    uint64_t m = rq(n, o); free(o); return m;
}
uint64_t m_scale(uint64_t z, uint64_t m) {
    size_t n; const uint64_t *w = rget(m, &n);
    if (z_is_zero(z)) return m_zero();
    uint64_t *o = malloc((n + 1) * sizeof *o); require(o, "out of memory: a module scaling");
    for (size_t i = 0; i < n; i += 2) { o[i] = w[i]; o[i + 1] = z_mul(z, w[i + 1]); }
    uint64_t r = rq(n, o); free(o); return r;
}

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
uint64_t cube_product(GenKind kx, uint64_t x, GenKind ky, uint64_t y) { uint64_t w[4] = { kx, x, ky, y }; return rq(4, w); }
size_t gen_degree(GenKind kind, uint64_t id) {
    size_t n; const uint64_t *w = rget(id, &n);
    switch (kind) {
    case G_CUBE: return (size_t)w[1];
    case G_PROD: return gen_degree((GenKind)w[0], w[1]) + gen_degree((GenKind)w[2], w[3]);
    case G_OCC: return 1;
    default: return 0;
    }
}
static uint64_t genrec(GenKind k, uint64_t id) { uint64_t w[2] = { k, id }; return rq(2, w); }

static Family Fc_REIDX, Fc_FACE, Fc_ADD, Fc_SCALE, Fc_BOUNDARY, Fc_VALUE, Fc_PAIR, Fc_MAP, Fc_IVRE, Fc_OCCB;

/* cube.reindex(view, [m2, image_1..image_m]): the map c_k ↦ image_k
 * (one entry per step, keys ascending), then each root image reindexed */
typedef struct { const uint64_t *v, *s; size_t nv, ns, k, kept; uint64_t map; WordBuf out; bool created; } RxLoc;
static void reindex_step(Cont *k, uint64_t v) {
    RxLoc *L = FR_LOC(k, RxLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->v = rget(k->w[0], &L->nv); L->s = rget(k->w[1], &L->ns);
    require(L->ns == 1 + L->v[1], "cube reindex: one image per coordinate");
    wordbuf_init(&L->out); L->kept = 0;
    for (L->k = 1; L->k <= L->v[1]; L->k++) {
        {   DimVarId c = cube_coord(L->k);
            if (L->s[L->k] != iv_var(c)) { wordbuf_push(&L->out, c); wordbuf_push(&L->out, L->s[L->k]); L->kept++; } }
        FR_YIELD(k);
    }
    wordbuf_push(&L->out, 0);                                   /* no term entries */
    FR_CALL(k, L->map, intern_sub(k, &M.maps, &L->out, &L->created));
    wordbuf_init(&L->out);
    wordbuf_push(&L->out, L->v[0]); wordbuf_push(&L->out, L->s[0]); wordbuf_push(&L->out, L->v[2]); wordbuf_push(&L->out, L->v[3]);
    for (L->k = 0; L->k < L->v[3]; L->k++) {
        FR_AWAIT(k, r, Fc_IVRE, L->v[4 + L->k], L->map);
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
            else { uint64_t s = z_add(L->a[L->i + 2], L->b[L->j + 2]);
                   if (!z_is_zero(s)) { wordbuf_push(&L->out, L->a[L->i]); wordbuf_push(&L->out, L->a[L->i + 1]); wordbuf_push(&L->out, s); }
                   L->i += 3; L->j += 3; } }
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
            wordbuf_push(&L->out, L->a[L->i]); wordbuf_push(&L->out, L->a[L->i + 1]); wordbuf_push(&L->out, z_mul(k->w[1], L->a[L->i + 2]));
            FR_YIELD(k);
        }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->out, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* chain.boundary(c): for each term and coordinate, the upper and lower faces
 * with signs (−1)^(i−1) and −(−1)^(i−1); an occurrence's resource boundary;
 * nothing in degree 0 */
typedef struct { const uint64_t *c; size_t nc, t, i, n; int eps; uint64_t acc, g, z; } BdLoc;
static void boundary_step(Cont *k, uint64_t v) {
    BdLoc *L = FR_LOC(k, BdLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->c = rget(k->w[0], &L->nc);
    {   uint64_t w[1] = { L->c[0] ? L->c[0] - 1 : 0 }; L->acc = rq(1, w); }
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        L->n = gen_degree((GenKind)L->c[L->t], L->c[L->t + 1]);
        if ((GenKind)L->c[L->t] == G_OCC) {
            if (!Fc_OCCB) Fc_OCCB = family_lookup("occurrence.boundary");
            require(Fc_OCCB, "an occurrence generator without the effect layer");
            FR_AWAIT(k, r, Fc_OCCB, L->c[L->t + 1], 0);
            FR_AWAIT(k, r, Fc_SCALE, r, L->c[L->t + 2]);
            FR_AWAIT(k, L->acc, Fc_ADD, L->acc, r);
            continue;
        }
        if ((GenKind)L->c[L->t] != G_CUBE && (GenKind)L->c[L->t] != G_PROD) { FR_YIELD(k); continue; }
        L->g = genrec((GenKind)L->c[L->t], L->c[L->t + 1]);
        for (L->i = 1; L->i <= L->n; L->i++)
            for (L->eps = 1; L->eps >= 0; L->eps--) {
                {   uint64_t e[2] = { L->i, (uint64_t)L->eps }; L->z = rq(2, e); }
                FR_AWAIT(k, r, Fc_FACE, L->g, L->z);
                {   size_t n; const uint64_t *f = rget(r, &n);
                    uint64_t z = L->c[L->t + 2]; if ((L->i - 1) % 2) z = z_neg(z); if (!L->eps) z = z_neg(z);
                    uint64_t w[4] = { L->c[0] - 1, f[0], f[1], z }; L->z = rq(4, w); }
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
        {   uint64_t w[4] = { gen_degree((GenKind)L->g, L->c), L->g, L->c, z_from_i64(1) }; L->c = rq(4, w); }
        FR_AWAIT(k, r, Fc_BOUNDARY, L->c, 0);
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
        L->acc = m_add(L->acc, m_scale(L->c[L->t + 2], r));
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
    {   uint64_t w[1] = { L->f[0] }; L->acc = rq(1, w); }
    for (L->t = 1; L->t < L->nc; L->t += 3) {
        for (L->img = 0, L->i = 1; L->i < L->nf && !L->img; L->i += 3) {
            if (L->f[L->i] == L->c[L->t] && L->f[L->i + 1] == L->c[L->t + 1]) L->img = L->f[L->i + 2];
            FR_YIELD(k);
        }
        if (!L->img) continue;
        FR_AWAIT(k, r, Fc_SCALE, L->img, L->c[L->t + 2]);
        FR_AWAIT(k, L->acc, Fc_ADD, L->acc, r);
    }
    FR_FINISH(k, L->acc);
    FR_END(k);
}

void chain_families_init(void) {
    Fc_IVRE = family_lookup("iv.reindex");
    require(Fc_IVRE, "the substitution families are registered first");
    Fc_REIDX = family_define("cube.reindex", reindex_step, sizeof(RxLoc), true);
    Fc_FACE = family_define("cell.face", face_step, sizeof(FcLoc), true);
    Fc_ADD = family_define("chain.add", add_step, sizeof(AddLoc), true);
    Fc_SCALE = family_define("chain.scale", scale_step, sizeof(AddLoc), true);
    Fc_BOUNDARY = family_define("chain.boundary", boundary_step, sizeof(BdLoc), true);
    Fc_VALUE = family_define("cochain.value", value_step, sizeof(ValLoc), true);
    Fc_PAIR = family_define("chain.pair", pair_step, sizeof(PairLoc), true);
    Fc_MAP = family_define("chain.map", map_step, sizeof(MapLoc), true);
    Fc_OCCB = 0;                                         /* the effect layer's, looked up at first use */
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
uint64_t cochain_cob(uint64_t a) { uint64_t w[2] = { CO_COB, a }; return rq(2, w); }
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

/* test_chain.c — CUBICAL-STOKES-ADDENDUM §11 checks 1–6 and 9 on the
 * additive reading of presented cells (chain.h). */
#include "../src/chain.h"
#include "../src/check.h"
#include <stdio.h>

static int np, nf;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

/* a presented n-cell: n dimension locals, constant body x : A, guard true */
static ScopeId cell_root(size_t n, RefId x, RefId A) {
    LocalDecl *d = calloc(n ? n : 1, sizeof *d);
    for (size_t i = 0; i < n; i++) { d[i].sort = S_DIM; d[i].type = 0; d[i].level = LEVEL_NONE; d[i].required = fc_true(); }
    ScopeId S = scope_intern(n, d, (Val){ VS_REF, x }, A, 0, fc_true());
    free(d); return S;
}
static uint64_t one(GenKind k, uint64_t id, int64_t c) { uint64_t z = z_from_i64(c); return chain_of(gen_degree(k, id), 1, &k, &id, &z); }
static bool empty(uint64_t c) { size_t n; interner_get(&M.keys, c, &n); return n == 1; }

int main(void) {
    printf("== cubical chains, cochains and Stokes (ADDENDUM §11)\n");
    machine_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    RefId U = mk_universe(0);
    TermVarId vA = declare_term(U, fc_true()); RefId A = ref_var(vA);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);

    /* 1. two deletion orders of a codimension-two face are one view — in low
     *    dimension, above 64, and under an outer parameter substitution */
    size_t dims[3] = { 3, 7, 70 };
    for (size_t q = 0; q < 3; q++) {
        size_t n = dims[q];
        uint64_t X = cube_view(cell_root(n, x, A), map_identity());
        size_t i = 1, j = n - 1;                         /* i < j */
        GenKind k1, k2, k3, k4;
        uint64_t a = cube_face(G_CUBE, X, j, 1, &k1); a = cube_face(k1, a, i, 0, &k2);          /* d_i^0 d_j^1 */
        uint64_t b = cube_face(G_CUBE, X, i, 0, &k3); b = cube_face(k3, b, j - 1, 1, &k4);      /* d_(j−1)^1 d_i^0 */
        CHECK(a == b, "n=%zu: d_i^0 d_j^1 = d_(j-1)^1 d_i^0 as one interned view", n);
        TermVarId vy = declare_term(A, fc_true());
        MapId s = map_single_term(vx, ref_var(vy));
        uint64_t Xs = cube_subst(X, s);
        uint64_t as = cube_face(G_CUBE, Xs, j, 1, &k1); as = cube_face(k1, as, i, 0, &k2);
        uint64_t bs = cube_face(G_CUBE, Xs, i, 0, &k3); bs = cube_face(k3, bs, j - 1, 1, &k4);
        CHECK(as == bs && as == cube_subst(a, s), "n=%zu: the same under an outer parameter substitution", n);
    }

    /* 2. ∂² = 0 on symbolic cubes */
    for (size_t n = 1; n <= 5; n++) {
        uint64_t X = cube_view(cell_root(n, x, A), map_identity());
        uint64_t d1 = chain_boundary(one(G_CUBE, X, 1));
        size_t nt; interner_get(&M.keys, d1, &nt);
        CHECK((nt - 1) / 3 == 2 * n, "n=%zu: ∂x has 2n distinct faces", n);
        CHECK(empty(chain_boundary(d1)), "n=%zu: ∂²x = 0 by cancellation of identical faces", n);
    }

    /* 3. a 1×1 product: four signed edges, Leibniz with sign (−1)^p */
    {   uint64_t I1 = cube_view(cell_root(1, x, A), map_identity());
        TermVarId vz = declare_term(A, fc_true());
        uint64_t I2 = cube_view(cell_root(1, ref_var(vz), A), map_identity());
        uint64_t P = cube_product(G_CUBE, I1, G_CUBE, I2);
        uint64_t dP = chain_boundary(one(G_PROD, P, 1));
        size_t nt; interner_get(&M.keys, dP, &nt);
        CHECK((nt - 1) / 3 == 4, "∂(x×y) has four edges");
        /* (∂x)×y − x×(∂y) */
        GenKind k; uint64_t x1 = cube_face(G_CUBE, I1, 1, 1, &k), x0 = cube_face(G_CUBE, I1, 1, 0, &k);
        uint64_t y1 = cube_face(G_CUBE, I2, 1, 1, &k), y0 = cube_face(G_CUBE, I2, 1, 0, &k);
        GenKind ks[4] = { G_PROD, G_PROD, G_PROD, G_PROD };
        uint64_t ids[4] = { cube_product(G_CUBE, x1, G_CUBE, I2), cube_product(G_CUBE, x0, G_CUBE, I2), cube_product(G_CUBE, I1, G_CUBE, y1), cube_product(G_CUBE, I1, G_CUBE, y0) };
        uint64_t zs[4] = { z_from_i64(1), z_from_i64(-1), z_from_i64(-1), z_from_i64(1) };
        CHECK(dP == chain_of(1, 4, ks, ids, zs), "∂(x×y) = (∂x)×y − x×(∂y)");
        CHECK(empty(chain_boundary(dP)), "∂²(x×y) = 0"); }

    /* 4. <a, ∂c> = <da, c>: a nonconstant valuation, a coefficient above
     *    2^64, a two-unit module */
    {   uint64_t X = cube_view(cell_root(2, x, A), map_identity());
        uint64_t d = chain_boundary(one(G_CUBE, X, 1));
        size_t nt; const uint64_t *w = interner_get(&M.keys, d, &nt);
        size_t n = (nt - 1) / 3;
        GenKind *ks = malloc(n * sizeof *ks); uint64_t *ids = malloc(n * sizeof *ids), *ms = malloc(n * sizeof *ms);
        uint64_t big[2] = { 5, 3 };                                           /* 3·2^64 + 5 */
        for (size_t t = 0; t < n; t++) {
            ks[t] = (GenKind)w[1 + 3 * t]; ids[t] = w[2 + 3 * t];
            ms[t] = m_add(m_unit(0, z_mul(z_from_i64((int64_t)(t * t) + 1), z_from_limbs(0, 2, big))), m_unit(7, z_from_i64(-(int64_t)(t * t) - 1)));
        }
        uint64_t a = cochain_table(1, n, ks, ids, ms);
        uint64_t c = chain_add(one(G_CUBE, X, 2), one(G_CUBE, cube_view(cell_root(2, ref_var(vA), U), map_identity()), -3));
        uint64_t lhs = chain_pair(a, chain_boundary(c)), rhs = chain_pair(cochain_cob(a), c);
        CHECK(lhs == rhs, "<a, ∂c> = <da, c>");
        size_t nl, zn = 0; const uint64_t *lw = interner_get(&M.keys, lhs, &nl);
        const uint64_t *zw = nl == 7 ? interner_get(&M.keys, lw[3], &zn) : NULL;   /* [0, (G_UNIT, unit, z) × 2] */
        (void)zw;
        CHECK(nl == 7 && zn == 3, "the pairing is a two-unit value with an exact coefficient above 2^64");
        CHECK(chain_pair(cochain_cob(cochain_cob(a)), one(G_CUBE, cube_view(cell_root(3, x, A), map_identity()), 1)) == m_zero(), "d²a = 0 on a 3-cell");
        free(ks); free(ids); free(ms); }

    /* 6. a cycle with no filling stays a cycle; a filling gives Stokes */
    {   uint64_t S2 = cube_view(cell_root(2, x, A), map_identity());
        uint64_t z = chain_boundary(one(G_CUBE, S2, 1));                    /* a cycle: ∂z = 0 */
        CHECK(empty(chain_boundary(z)) && !empty(z), "∂z = 0 and z is not zero");
        /* the filler h = S2 with ∂h = z: <a, z> = <da, h> for a 1-cochain a */
        size_t nt; const uint64_t *w = interner_get(&M.keys, z, &nt); size_t n = (nt - 1) / 3;
        GenKind *k2 = malloc(n * sizeof *k2); uint64_t *i2 = malloc(n * sizeof *i2), *m2 = malloc(n * sizeof *m2);
        for (size_t t = 0; t < n; t++) { k2[t] = (GenKind)w[1 + 3 * t]; i2[t] = w[2 + 3 * t]; m2[t] = m_unit(0, z_from_i64((int64_t)(t * t) + 2)); }
        uint64_t a = cochain_table(1, n, k2, i2, m2);
        CHECK(chain_pair(a, z) == chain_pair(cochain_cob(a), one(G_CUBE, S2, 1)), "with a filling: <a, ∂h> = <da, h>");
        free(k2); free(i2); free(m2); }


    /* 5. local coefficients: the upper-face transport and its square witness */
    {   ScopeId R2 = cell_root(2, x, A); uint64_t X = cube_view(R2, map_identity());
        uint64_t s0 = perm_of(2, (uint64_t[]){ 10, 11 }, (uint64_t[]){ 11, 10 }), s1 = perm_of(2, (uint64_t[]){ 20, 21 }, (uint64_t[]){ 21, 20 });
        uint64_t sys = local_system(R2, 2, (uint64_t[]){ s0, s1 }, 1, (uint64_t[]){ 0, 1 });
        CHECK(sys != 0, "commuting transports with their square witness form a flat system");
        GenKind kt = G_TWIST; uint64_t g = twist_gen(X, 10), z1 = z_from_i64(1);
        uint64_t c = chain_of(2, 1, &kt, &g, &z1), d = chain_tboundary(c, sys);
        GenKind kf; uint64_t up = cube_face(G_CUBE, X, 1, 1, &kf);
        size_t nt; const uint64_t *w = interner_get(&M.keys, d, &nt); bool moved = false;
        for (size_t t = 1; t < nt; t += 3) { size_t n2; const uint64_t *tw = interner_get(&M.keys, w[t + 1], &n2); if (tw[0] == up && tw[1] == 11) moved = true; }
        CHECK(moved, "the upper 1-face carries the transported coefficient");
        CHECK(empty(chain_tboundary(d, sys)), "the twisted ∂² = 0 with the square witness");
        GenKind *ks = malloc((nt / 3) * sizeof *ks); uint64_t *ids = malloc((nt / 3) * sizeof *ids), *ms = malloc((nt / 3) * sizeof *ms); size_t n = 0;
        for (size_t t = 1; t < nt; t += 3, n++) { ks[n] = (GenKind)w[t]; ids[n] = w[t + 1]; ms[n] = m_unit(0, z_from_i64((int64_t)(n * n) + 3)); }
        uint64_t a = cochain_table(1, n, ks, ids, ms);
        CHECK(chain_pair(a, d) == chain_pair(cochain_cob_local(a, sys), c), "<a, ∂_T c> = <d_T a, c>");
        free(ks); free(ids); free(ms);
        ScopeId R3 = cell_root(2, ref_var(vA), U);
        uint64_t cyc = perm_of(3, (uint64_t[]){ 1, 2, 3 }, (uint64_t[]){ 2, 3, 1 }), sw = perm_of(2, (uint64_t[]){ 1, 2 }, (uint64_t[]){ 2, 1 });
        CHECK(local_system(R3, 2, (uint64_t[]){ cyc, sw }, 1, (uint64_t[]){ 0, 1 }) == 0, "a square witness for non-commuting transports is rejected");
        CHECK(local_system(R2, 2, (uint64_t[]){ s0, s1 }, 0, NULL) == 0, "an absent square witness is rejected"); }

    printf("  %d passed, %d failed\n", np, nf);
    check_free(); machine_free();
    return nf ? 1 : 0;
}

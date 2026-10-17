/* CUBICAL-STOKES-ADDENDUM §11, checks 1–6 and 9 (checks 7, 8 and 10 run on the
 * retained effect execution in test_effect_witness).
 *
 *   faces     1. two face-deletion orders give the same composed coordinate map,
 *                under an outer parameter substitution too, at n = 3, 8 and 70;
 *                cube-map composition (x[σ])[τ] = x[σ∘τ]
 *   d2        2. a symbolic 3-cube's ∂² cancels exactly; the shared law witness
 *                instantiated at n = 3, 4, 7, 70
 *   product   3. a 1×1 product's four signed edges (views, a presented factor,
 *                a declared factor); an oriented reversal does not cancel two
 *                performed reverse-direction occurrences in the work reading
 *   stokes    4. ⟨a,∂c⟩ = ⟨da,c⟩ for a nonconstant suspending valuation with
 *                coefficients beyond 2^128 in a three-unit module; d(da) = 0
 *   local     5. a dependent transport: upper faces carry T_i(m); coherent squares
 *                give ∂² = 0 and dd = 0; an absent or invalid square witness is
 *                rejected and the twisted ∂² defect is retained
 *   cycles    6. a cycle with no filling stays a cycle; a scalar-zero observation
 *                keeps its occurrences; a supplied filling satisfies Stokes and
 *                the original witness is unchanged
 *   work      9. measured work: a zero-defect scheduling square, a nonzero-defect
 *                replacement that keeps its shift, and a 3-cell whose faces' signed
 *                defects sum to zero
 * Run: test_stokes {faces|d2|product|stokes|local|cycles|work|all} [workers] */
#include "check.h"
#include "lib.h"
#include "compiler.h"
#include "chain.h"
#include "fine.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails;
#define EXPECT(c, ...) do { if (!(c)) { fails++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)
static size_t g_workers;
typedef struct { RefId U, A, x, y; TermVarId va, vx, vy; SymbolId loop; ContextId G; } World;
static World W;

static void start(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); chain_init();
    if (g_workers) eval_set_workers(g_workers);
    W.U = mk_universe(0);
    W.va = declare_term(W.U, fc_true()); W.A = ref_var(W.va);
    W.vx = declare_term(W.A, fc_true()); W.x = ref_var(W.vx);
    W.vy = declare_term(W.A, fc_true()); W.y = ref_var(W.vy);
    uint64_t pars[] = { W.va, W.vx };
    W.loop = define_global("stokes_loop", varset_make(pars, 2), dimset_make(NULL, 0), mk_path_const(0, W.A, W.x, W.x));
    assert(W.loop);
    CtxDecl d[] = { { S_TERM, W.va, W.U }, { S_TERM, W.vx, W.A }, { S_TERM, W.vy, W.A } };
    W.G = context_make(3, d, fc_true());
}
static void stop(void) { chain_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
static RefId p_at(IntervalId s) { return mk_papp_const(0, W.A, W.x, W.x, global_ref(W.loop), s); }
/* a symbolic presented n-cube: the loop at (d1 ∧ d2) ∨ … over n fresh dimensions */
static ScopeId cube_root(size_t n, unsigned salt) {
    DimVarId *d = malloc(n * sizeof *d); CaptureDecl *cd = calloc(n, sizeof *cd);
    IntervalId e = iv_zero();
    for (size_t k = 0; k < n; k++) { d[k] = declare_dim(); cd[k] = (CaptureDecl){ S_DIM, d[k], 0, LEVEL_NONE, fc_true() }; }
    for (size_t k = 0; k < n; k++) { IntervalId t = iv_var(d[k]); if ((k + salt) % 3 == 1 && k + 1 < n) t = iv_meet(t, iv_var(d[k + 1])); if ((k + salt) % 4 == 2) t = iv_negate(t); e = iv_join(e, t); }
    Val b = { VS_REF, p_at(e) };
    ScopeId S = capture_scope(n, cd, b, W.A, 0, fc_true());
    free(d); free(cd); return S;
}
static Zx Z(int64_t v) { return zx_i64(v); }
static ModId I(int64_t v) { return mod_int(Z(v)); }
static void pr_chain(const char *label, ChainId c) { char buf[2048]; chain_print(c, buf, sizeof buf); printf("  %s = %s\n", label, buf); }
static void pr_mod(const char *label, ModId m) { char buf[1024]; mod_print(m, buf, sizeof buf); printf("  %s = %s\n", label, buf); }

/* ---------------- 1. faces ---------------- */
static void t_faces(void) {
    start();
    size_t dims[] = { 3, 8, 70 };
    for (size_t q = 0; q < 3; q++) {
        size_t n = dims[q]; ScopeId R = cube_root(n, (unsigned)q);
        const char *why = NULL;
        EXPECT(cell_admit_root(W.G, fc_true(), R, &why) == CK_VALID, "n=%zu: the root is a checked presented cell (%s)", n, why ? why : "");
        CellId x = cell_root(R, map_identity());
        MapBuilder mb; mapb_init(&mb); mapb_term(&mb, W.vx, W.y); MapId tau = mapb_finish(&mb);
        CellId xp = cell_param(x, tau);
        size_t checked = 0, bad = 0, badp = 0, badc = 0;
        size_t stride = n > 10 ? 7 : 1;
        for (size_t i = 1; i <= n; i += stride) for (size_t j = i + 1; j <= n; j += (n > 10 ? 9 : 1)) for (int e = 0; e < 2; e++) for (int h = 0; h < 2; h++) {
            if (cell_face(cell_face(x, j, h), i, e) != cell_face(cell_face(x, i, e), j - 1, h)) bad++;
            if (cell_face(cell_face(xp, j, h), i, e) != cell_face(cell_face(xp, i, e), j - 1, h)) badp++;
            if (cell_param(cell_face(cell_face(x, j, h), i, e), tau) != cell_face(cell_face(xp, j, h), i, e)) badc++;
            checked++;
        }
        EXPECT(bad == 0 && badp == 0 && badc == 0 && checked > 0, "n=%zu: d_i^e d_j^h = d_(j-1)^h d_i^e on %zu index choices, under the parameter substitution too, and parameters commute with faces (bad %zu/%zu/%zu)", n, checked, bad, badp, badc);
        /* the composed map is one simultaneous assignment: the corner's images are literally the same words */
        ScopeId r1, r2; MapId p1, p2; size_t n1, n2; const IntervalId *im1, *im2;
        CellId L = cell_face(cell_face(x, n, 1), 1, 0), Rr = cell_face(cell_face(x, 1, 0), n - 1, 1);
        cell_view_parts(L, &r1, &p1, &n1, &im1); cell_view_parts(Rr, &r2, &p2, &n2, &im2);
        EXPECT(L == Rr && r1 == R && n1 == n && im1[0] == iv_zero() && im1[n - 1] == iv_one(), "n=%zu: the corner is one view of the same root with c_1 ↦ 0 at coordinate 1 and 1 at coordinate n", n);
        /* (x[σ])[τ] = x[σ∘τ] for a connection, a reversal and a diagonal */
        if (n == 3) {
            IntervalId sigma[3] = { iv_meet(iv_var(cube_coord(1)), iv_var(cube_coord(2))), iv_negate(iv_var(cube_coord(2))), iv_var(cube_coord(1)) };
            IntervalId t2[2] = { iv_var(cube_coord(1)), iv_var(cube_coord(1)) };   /* diagonal */
            IntervalId comp[3]; cube_map_compose(3, sigma, 2, t2, comp);
            CellId a = cell_reindex(cell_reindex(x, 2, sigma), 1, t2), b = cell_reindex(x, 1, comp);
            EXPECT(a == b, "n=3: (x[σ])[τ] = x[σ∘τ] for σ a connection/reversal, τ a diagonal");
            size_t c = 0; EXPECT(cell_degenerate(cell_reindex(x, 2, (IntervalId[]){ iv_var(cube_coord(1)), iv_var(cube_coord(1)), iv_zero() }), &c) && c == 2, "a view forgetting coordinate 2 carries its degeneracy witness (%zu)", c);
            EXPECT(cell_body(x) && cell_body(cell_face(x, 1, 0)), "views expose their bodies by substitution");
        }
        printf("faces n=%zu: %zu index choices checked, corner images shared, parameter substitution commutes\n", n, checked);
    }
    stop();
}

/* ---------------- 2. ∂² ---------------- */
static void t_d2(void) {
    start();
    ScopeId R = cube_root(3, 0); CellId x = cell_root(R, map_identity());
    ChainId g = chain_genz(x, 1);
    ChainId b1 = chain_boundary(g, NULL), b2 = chain_boundary(b1, NULL);
    EXPECT(chain_nterms(b1) == 6 && chain_is_zero(b2), "the symbolic 3-cube: ∂x has 6 faces, ∂²x = 0 exactly (%zu terms)", chain_nterms(b2));
    pr_chain("∂x", b1);
    size_t ns[] = { 3, 4, 7, 70 };
    for (size_t q = 0; q < 4; q++) {
        CellId y = cell_root(cube_root(ns[q], 1), map_identity());
        uint64_t ok = ch_run(op_law_d2(y));
        LawD2 rec = law_d2_record(ns[q]);
        EXPECT(ok == 1 && rec.instances >= 1 && rec.pairs == 2ULL * ns[q] * (ns[q] - 1), "n=%zu: the d²=0 law instance: %llu cancelling pairs verified", ns[q], (unsigned long long)rec.pairs);
        if (ns[q] <= 7) { ChainId bb = chain_boundary(chain_boundary(chain_genz(y, 3), NULL), NULL); EXPECT(chain_is_zero(bb), "n=%zu: ∂²(3x) = 0 by direct expansion", ns[q]); }
        printf("d2 n=%zu: law instance verified over %llu pairs (instances of the shared record: %llu)\n", ns[q], (unsigned long long)rec.pairs, (unsigned long long)rec.instances);
    }
    /* presented cells: the identities are admission premises */
    const char *why = NULL;
    CellId v0 = cell_presented(1, 0, 0, NULL, NULL), v1 = cell_presented(1, 1, 0, NULL, NULL), v2 = cell_presented(1, 2, 0, NULL, NULL), v3 = cell_presented(1, 3, 0, NULL, NULL);
    CellId e01 = cell_presented(2, 1, 1, (CellId[]){ v0, v1 }, NULL), e23 = cell_presented(2, 2, 1, (CellId[]){ v2, v3 }, NULL);
    CellId e02 = cell_presented(2, 3, 1, (CellId[]){ v0, v2 }, NULL), e13 = cell_presented(2, 4, 1, (CellId[]){ v1, v3 }, NULL);
    CellId sq = cell_presented(3, 1, 2, (CellId[]){ e02, e13, e01, e23 }, &why);
    CellId badsq = cell_presented(3, 2, 2, (CellId[]){ e02, e13, e23, e01 }, &why);
    EXPECT(sq && !badsq, "a presented square is admitted with consistent faces and rejected with swapped ones (%s)", why ? why : "");
    EXPECT(chain_is_zero(chain_boundary(chain_boundary(chain_genz(sq, 1), NULL), NULL)), "∂² of the presented square is 0");
    stop();
}

/* ---------------- 3. products and reversal ---------------- */
typedef struct { CellId cell[64]; int64_t w[64]; size_t n; } Weights;
static int weight_act(void *ctx, CellId x, ModId *out) { Weights *t = ctx; for (size_t k = 0; k < t->n; k++) if (t->cell[k] == x) { *out = I(t->w[k]); return 0; } *out = mod_zero(); return 0; }
static void t_product(void) {
    start();
    CellId x = cell_root(cube_root(1, 0), map_identity()), y = cell_root(cube_root(1, 2), map_identity());
    CellId xy = cell_product(x, y);
    ChainId bxy = chain_boundary(chain_genz(xy, 1), NULL);
    ChainId leib = chain_sub(chain_product(chain_boundary(chain_genz(x, 1), NULL), chain_genz(y, 1)), chain_product(chain_genz(x, 1), chain_boundary(chain_genz(y, 1), NULL)));
    EXPECT(cell_kind(xy) == CK_VIEW && cell_degree(xy) == 2 && chain_nterms(bxy) == 4 && bxy == leib, "views: ∂(x×y) has four signed edges and equals (∂x)×y − x×(∂y)");
    pr_chain("∂(x×y)", bxy);
    /* a presented factor and a declared factor */
    CellId s = cell_presented(7, 1, 0, NULL, NULL), t = cell_presented(7, 2, 0, NULL, NULL);
    CellId e = cell_presented(8, 1, 1, (CellId[]){ s, t }, NULL);
    CellId ey = cell_product(e, y);
    ChainId bey = chain_boundary(chain_genz(ey, 1), NULL);
    ChainId leib2 = chain_sub(chain_product(chain_boundary(chain_genz(e, 1), NULL), chain_genz(y, 1)), chain_product(chain_genz(e, 1), chain_boundary(chain_genz(y, 1), NULL)));
    EXPECT(chain_nterms(bey) == 4 && bey == leib2, "a presented × view product: four signed edges by the face formula, equal to Leibniz");
    CellId r0 = cell_declared(9, 1, 0, chain_zero(0), NULL), r1 = cell_declared(9, 2, 0, chain_zero(0), NULL);
    CellId ev = cell_declared(10, 1, 1, chain_sub(chain_genz(r1, 1), chain_genz(r0, 1)), NULL);
    ChainId bevy = chain_boundary(chain_genz(cell_product(ev, y), 1), NULL);
    ChainId leib3 = chain_sub(chain_product(chain_boundary(chain_genz(ev, 1), NULL), chain_genz(y, 1)), chain_product(chain_genz(ev, 1), chain_boundary(chain_genz(y, 1), NULL)));
    EXPECT(chain_nterms(bevy) == 4 && bevy == leib3, "a declared-boundary × view product: Leibniz with the product orientation");
    /* reversal: two performed occurrences in opposite directions, each with its measured work */
    TermVarId z = declare_term(W.A, fc_true());
    uint64_t b0 = reuse_count(REUSE_BETA); WhnfStatus st;
    whnf(mk_app(mk_lam_lv(0, z, W.A, mk_app(mk_lam_lv(0, z, W.A, ref_var(z)), ref_var(z))), W.x), fc_true(), &st);
    uint64_t w_fwd = reuse_count(REUSE_BETA) - b0; b0 = reuse_count(REUSE_BETA);
    whnf(mk_app(mk_lam_lv(0, z, W.A, ref_var(z)), W.y), fc_true(), &st);
    uint64_t w_rev = reuse_count(REUSE_BETA) - b0;
    CellId er = cell_presented(8, 2, 1, (CellId[]){ t, s }, NULL);
    Weights wt = { { e, er }, { (int64_t)w_fwd, (int64_t)w_rev }, 2 };
    Cochain *omega = cochain_gen(1, 1, weight_act, &wt);
    ChainId round = chain_add(chain_genz(e, 1), chain_genz(er, 1)), formal = chain_sub(chain_genz(e, 1), chain_genz(e, 1));
    ModId Wround = chain_pair(omega, round);
    Zx wr; mod_scalar(Wround, &wr);
    EXPECT(chain_is_cycle(round) && !chain_is_zero(round) && chain_is_zero(formal) && zx_eq(wr, Z((int64_t)(w_fwd + w_rev))) && wr.sign > 0,
           "the performed round trip e + e_rev is a cycle with positive work %llu + %llu; the formal e − e is the zero chain, not a reverse execution", (unsigned long long)w_fwd, (unsigned long long)w_rev);
    printf("product: four signed edges for view×view, presented×view and declared×view; round trip work %llu (forward %llu, reverse %llu)\n", (unsigned long long)(w_fwd + w_rev), (unsigned long long)w_fwd, (unsigned long long)w_rev);
    stop();
}

/* ---------------- 4. Stokes with a nonconstant, suspending, multi-unit valuation ---------------- */
typedef struct { size_t asked[1 << 12]; } Susp;
static Nat bigfrom(uint64_t seed, int limbs) { uint64_t l[4]; for (int k = 0; k < limbs; k++) { seed = seed * 6364136223846793005ULL + 1442695040888963407ULL; l[k] = seed | 1; } return nat_from_limbs((size_t)limbs, l); }
static int big_act(void *ctx, CellId x, ModId *out) {
    Susp *s = ctx; size_t h = (size_t)(x * 2654435761u) & ((1 << 12) - 1);
    if (__atomic_fetch_add(&s->asked[h], 1, __ATOMIC_RELAXED) == 0) return 1;     /* the first request suspends: the value is still being computed */
    ModId m = mod_add(mod_unit(0, zx_nat(1, bigfrom(x, 3))), mod_add(mod_unit(1, zx_nat(x & 1 ? -1 : 1, bigfrom(x ^ 0x55, 2))), mod_unit(7, zx_nat(1, nat_from_word(x * x * 977 + 3)))));
    *out = m; return 0;
}
static void t_stokes(void) {
    start();
    CellId X = cell_root(cube_root(3, 0), map_identity()), Y = cell_root(cube_root(3, 2), map_identity());
    CellId P = cell_product(cell_root(cube_root(1, 0), map_identity()), cell_root(cube_root(1, 1), map_identity()));
    Nat huge = bigfrom(42, 3);                                    /* about 2^190 */
    CellId cs[4] = { cell_face(X, 1, 0), cell_face(X, 3, 1), cell_face(Y, 2, 1), P };
    ModId co[4] = { mod_int(zx_nat(1, huge)), I(-3), mod_int(zx_nat(-1, nat_mul_exact(huge, huge))), I(5) };
    ChainId c = chain_from(2, 4, cs, co);
    Susp *s = calloc(1, sizeof *s);
    Cochain *a = cochain_gen(1, 3, big_act, s);
    bool agree = false; ModId lhs = read_defect(a, c, &agree);
    ModId rhs = chain_pair(cochain_cob(a, NULL), c);
    EXPECT(agree && lhs == rhs && mod_nterms(lhs) == 3, "⟨a,∂c⟩ = ⟨da,c⟩ in a three-unit module with coefficients beyond 2^128 (agree=%d terms %zu)", agree, mod_nterms(lhs));
    pr_mod("<a,∂c>", lhs);
    /* the pairing is linear in exact arithmetic: ⟨a, ∂(2c)⟩ = 2⟨a,∂c⟩ */
    EXPECT(read_defect(a, chain_scale(Z(2), c), NULL) == mod_scale(Z(2), lhs), "⟨a,∂(2c)⟩ = 2⟨a,∂c⟩ exactly");
    /* d(da) = 0 on 3-cells */
    Cochain *dda = cochain_cob(cochain_cob(a, NULL), NULL);
    ModId z3 = chain_pair(dda, chain_add(chain_genz(X, 7), chain_genz(Y, -2)));
    EXPECT(mod_is_zero(z3), "d(da) vanishes on 3-cells");
    ChainStats st = chain_stats();
    printf("stokes: <a,∂c> = <da,c> with |coefficients| up to 2^380; d(da) = 0; ops=%llu units=%llu shared generator values reused=%llu\n", (unsigned long long)st.ops, (unsigned long long)st.units, (unsigned long long)st.memo_hits);
    free(s);
    stop();
}

/* ---------------- 5. local coefficients ---------------- */
typedef struct { int mats[4][2][2]; bool witness; } LS;
static size_t edge_dir(CellId e) {   /* the root coordinate along which a 1-view moves */
    ScopeId r; MapId p; size_t n; const IntervalId *im; cell_view_parts(e, &r, &p, &n, &im);
    for (size_t j = 0; j < n; j++) if (im[j] == iv_var(cube_coord(1)) || im[j] == iv_negate(iv_var(cube_coord(1)))) return j;
    return 0;
}
static ModId apply_mat(int M[2][2], ModId m, bool inv) {
    Zx u0 = mod_coef(m, 0), u1 = mod_coef(m, 1);
    int a = M[0][0], b = M[0][1], c = M[1][0], d = M[1][1];
    if (inv) { int det = a * d - b * c; int ia = d * det, ib = -b * det, ic = -c * det, id = a * det; a = ia; b = ib; c = ic; d = id; }   /* det = ±1 */
    Zx n0 = zx_add(zx_mul(Z(a), u0), zx_mul(Z(b), u1)), n1 = zx_add(zx_mul(Z(c), u0), zx_mul(Z(d), u1));
    return mod_add(mod_unit(0, n0), mod_unit(1, n1));
}
static ModId ls_T(void *ctx, CellId e, ModId m, bool inv) { LS *l = ctx; return apply_mat(l->mats[edge_dir(e)], m, inv); }
static bool ls_sq(void *ctx, CellId s) { (void)s; return ((LS *)ctx)->witness; }
static int vec_act(void *ctx, CellId x, ModId *out) { (void)ctx; *out = mod_add(mod_unit(0, Z((int64_t)(x % 97) - 40)), mod_unit(1, Z((int64_t)(x % 13) + 2))); return 0; }
static void t_local(void) {
    start();
    CellId X = cell_root(cube_root(3, 0), map_identity());
    uint64_t units[2] = { 0, 1 };
    LS good = { { { { 0, 1 }, { 1, 0 } }, { { -1, 0 }, { 0, -1 } }, { { 0, -1 }, { -1, 0 } } }, true };   /* swap, −I, −swap: commuting */
    LS bad = { { { { 0, 1 }, { 1, 0 } }, { { 1, 0 }, { 0, -1 } }, { { 1, 0 }, { 0, 1 } } }, true };     /* swap and diag(1,−1) do not commute */
    LS absent = good; absent.witness = false;
    LocalSystem *Lg = localsys_new(ls_T, ls_sq, &good, 2, units), *Lb = localsys_new(ls_T, ls_sq, &bad, 2, units);
    LocalSystem *La = localsys_new(ls_T, ls_sq, &absent, 2, units), *Ln = localsys_new(ls_T, NULL, &good, 2, units);
    const char *wg = NULL, *wb = NULL, *wa = NULL, *wn = NULL;
    bool ag = localsys_admit(Lg, X, &wg), ab = localsys_admit(Lb, X, &wb), aa = localsys_admit(La, X, &wa), an = localsys_admit(Ln, X, &wn);
    EXPECT(ag && !ab && !aa && !an, "coherent squares admitted; invalid (%s), unsupplied (%s) and absent (%s) square witnesses rejected", wb ? wb : "", wa ? wa : "", wn ? wn : "");
    ModId m = mod_add(mod_unit(0, Z(2)), mod_unit(1, Z(5)));
    ChainId mx = chain_gen(X, m);
    ChainId b = chain_boundary(mx, Lg);
    ModId up1 = chain_coef(b, cell_face(X, 1, 1)), lo1 = chain_coef(b, cell_face(X, 1, 0));
    EXPECT(up1 == apply_mat(good.mats[edge_dir(cell_base_edge(X, 1))], m, false) && lo1 == mod_neg(m), "∂(m·x): the upper 1-face carries T_1(m), the lower one −m");
    pr_chain("∂(m·x)", b);
    ChainId bb = chain_boundary(b, Lg);
    EXPECT(chain_is_zero(bb), "coherent transports: the twisted ∂² vanishes");
    ChainId bbb = chain_boundary(chain_boundary(mx, Lb), Lb);
    EXPECT(!chain_is_zero(bbb), "incoherent transports: no flat interpretation; the twisted ∂² defect is retained (%zu terms)", chain_nterms(bbb));
    pr_chain("twisted ∂² (incoherent)", bbb);
    Cochain *a = cochain_gen(1, 2, vec_act, NULL);
    ModId dd = chain_pair(cochain_cob(cochain_cob(a, Lg), Lg), chain_genz(X, 1));
    ModId ddb = chain_pair(cochain_cob(cochain_cob(a, Lb), Lb), chain_genz(X, 1));
    EXPECT(mod_is_zero(dd), "coherent transports: the twisted dd vanishes on the 3-cell");
    pr_mod("twisted dd(a)(x), incoherent", ddb);
    printf("local: upper faces transported; coherent ∂² = 0 and dd = 0; incoherent ∂² has %zu nonzero terms, dd(a)(x) %s 0; rejections: %s | %s | %s\n",
           chain_nterms(bbb), mod_is_zero(ddb) ? "=" : "≠", wb ? wb : "", wa ? wa : "", wn ? wn : "");
    stop();
}

/* ---------------- 6. cycles, boundaries, observation fibres ---------------- */
static int alt_act(void *ctx, CellId x, ModId *out) { Weights *t = ctx; return weight_act(t, x, out); }
static void t_cycles(void) {
    start();
    CellId s = cell_presented(11, 0, 0, NULL, NULL), t = cell_presented(11, 1, 0, NULL, NULL);
    CellId e1 = cell_presented(12, 1, 1, (CellId[]){ s, t }, NULL), e2 = cell_presented(12, 2, 1, (CellId[]){ t, s }, NULL);
    ChainId z = chain_add(chain_genz(e1, 1), chain_genz(e2, 1));
    const char *why = NULL; BoundaryWitness bw;
    EXPECT(chain_is_cycle(z) && !boundary_witness(z, chain_zero(2), &bw, &why), "z = e1 + e2 is a cycle and the zero chain does not bound it (%s)", why ? why : "");
    Weights q = { { e1, e2 }, { 1, -1 }, 2 };
    Cochain *obs = cochain_gen(1, 1, alt_act, &q);
    ModId qz = chain_pair(obs, z);
    EXPECT(mod_is_zero(qz) && chain_nterms(z) == 2, "a scalar-zero observation of z keeps both occurrences in the chain (the fibre)");
    /* a filling, supplied: a declared 2-cell with boundary z */
    CellId h = cell_declared(13, 1, 2, z, &why);
    ChainId H = chain_genz(h, 1);
    EXPECT(h && boundary_witness(z, H, &bw, &why) && bw.z == z && bw.h == H, "the supplied filling witnesses z as a boundary");
    Weights wv = { { e1, e2 }, { 7, 11 }, 2 };
    Cochain *a = cochain_gen(1, 1, alt_act, &wv);
    bool agree = false; ModId lhs = read_defect(a, H, &agree);
    ModId az = chain_pair(a, z);
    EXPECT(agree && lhs == az && chain_is_cycle(z) && chain_nterms(z) == 2, "Stokes: ⟨a,z⟩ = ⟨da,h⟩ = 18; z is still the same cycle with its two occurrences");
    /* a presented square filling the four-edge cycle, with a nonconstant valuation */
    CellId v[4]; for (int k = 0; k < 4; k++) v[k] = cell_presented(14, (uint64_t)k, 0, NULL, NULL);
    CellId b0 = cell_presented(15, 1, 1, (CellId[]){ v[0], v[1] }, NULL), b1 = cell_presented(15, 2, 1, (CellId[]){ v[2], v[3] }, NULL);
    CellId l0 = cell_presented(15, 3, 1, (CellId[]){ v[0], v[2] }, NULL), l1 = cell_presented(15, 4, 1, (CellId[]){ v[1], v[3] }, NULL);
    CellId sq = cell_presented(16, 1, 2, (CellId[]){ l0, l1, b0, b1 }, &why);
    ChainId zsq = chain_boundary(chain_genz(sq, 1), NULL);
    Weights w4 = { { b0, b1, l0, l1 }, { 3, 10, 4, 6 }, 4 };
    Cochain *a4 = cochain_gen(1, 1, alt_act, &w4);
    bool ag2 = false; ModId d4 = read_defect(a4, chain_genz(sq, 1), &ag2);
    Zx dz; mod_scalar(d4, &dz);
    EXPECT(sq && chain_is_cycle(zsq) && ag2 && zx_eq(dz, Z(3 + 6 - 10 - 4)), "the square's boundary is a cycle; ⟨a,∂h⟩ = ⟨da,h⟩ = −5 (the defect of the comparison)");
    printf("cycles: z stays a cycle without a filling; the zero observation keeps its 2 occurrences; with the filling ⟨a,z⟩ = ⟨da,h⟩; square defect −5\n");
    stop();
}

/* ---------------- 9. measured work: scheduling, replacement, coherence ---------------- */
static uint64_t betas_of(RefId t) { uint64_t b = reuse_count(REUSE_BETA); WhnfStatus st; whnf(t, fc_true(), &st); return reuse_count(REUSE_BETA) - b; }
static RefId nest(RefId body, int k) { for (int i = 0; i < k; i++) { TermVarId z = declare_term(W.A, fc_true()); body = mk_app(mk_lam_lv(0, z, W.A, body), W.x); } return body; }
static void t_work(void) {
    /* job a and job b executed in both orders, each order in its own session */
    uint64_t wa[2], wb[2];
    for (int order = 0; order < 2; order++) {
        start();
        RefId ta = nest(W.x, 4), tb = nest(W.y, 3);
        if (order == 0) { wa[0] = betas_of(ta); wb[0] = betas_of(tb); } else { wb[1] = betas_of(tb); wa[1] = betas_of(ta); }
        stop();
    }
    start();
    RefId direct = nest(W.x, 6), replaced = nest(W.x, 2);          /* the same value; the replacement takes fewer steps */
    uint64_t k1 = betas_of(direct), k2 = betas_of(replaced);
    /* the 3-cell: coordinate 1 = job a (direct at c3 = 0, replaced at c3 = 1), coordinate 2 = job b, coordinate 3 = the replacement connector */
    CellId v[8]; for (int k = 0; k < 8; k++) v[k] = cell_presented(20, (uint64_t)k, 0, NULL, NULL);
    CellId E[3][8] = {{0}};
    Weights wt; memset(&wt, 0, sizeof wt);
    for (int d = 0; d < 3; d++) for (int k = 0; k < 8; k++) if (!(k & (1 << d))) {
        E[d][k] = cell_presented(21 + d, (uint64_t)k, 1, (CellId[]){ v[k], v[k | (1 << d)] }, NULL);
        int64_t w = d == 0 ? (int64_t)((k & 4) ? k2 : k1) : d == 1 ? (int64_t)((k & 1) ? wb[1] : wb[0]) : 0;
        wt.cell[wt.n] = E[d][k]; wt.w[wt.n] = w; wt.n++;
    }
    /* squares in coordinates (i<j) at vertex k: d_1^e = the j-edge at k + e·i, d_2^e = the i-edge at k + e·j */
    #define SQ(i, j, k, tag) cell_presented(24, (tag), 2, (CellId[]){ E[j][k], E[j][(k) | (1 << (i))], E[i][k], E[i][(k) | (1 << (j))] }, NULL)
    CellId s01_0 = SQ(0, 1, 0, 1), s01_1 = SQ(0, 1, 4, 2), s02_0 = SQ(0, 2, 0, 3), s02_1 = SQ(0, 2, 2, 4), s12_0 = SQ(1, 2, 0, 5), s12_1 = SQ(1, 2, 1, 6);
    const char *why = NULL;
    CellId K = cell_presented(25, 1, 3, (CellId[]){ s12_0, s12_1, s02_0, s02_1, s01_0, s01_1 }, &why);
    Cochain *omega = cochain_gen(1, 1, weight_act, &wt);
    Zx dsched, drep, dK; bool a1, a2;
    mod_scalar(read_defect(omega, chain_genz(s01_0, 1), &a1), &dsched);
    mod_scalar(read_defect(omega, chain_genz(s02_0, 1), &a2), &drep);
    mod_scalar(chain_pair(cochain_cob(cochain_cob(omega, NULL), NULL), chain_genz(K, 1)), &dK);
    ChainId bK = chain_boundary(chain_genz(K, 1), NULL);
    Zx sum = Z(0); for (size_t k = 0; k < chain_nterms(bK); k++) { CellId f; ModId c; chain_term(bK, k, &f, &c); Zx df; mod_scalar(read_defect(omega, chain_genz(f, 1), NULL), &df); sum = zx_add(sum, zx_mul(df, mod_coef(c, 0))); }
    EXPECT(wa[0] == wa[1] && wb[0] == wb[1], "independent jobs measured in both orders: a %llu/%llu, b %llu/%llu", (unsigned long long)wa[0], (unsigned long long)wa[1], (unsigned long long)wb[0], (unsigned long long)wb[1]);
    EXPECT(K && a1 && a2 && dsched.sign == 0, "the scheduling square has zero defect");
    EXPECT(k1 != k2 && (zx_eq(drep, Z((int64_t)k1 - (int64_t)k2)) || zx_eq(drep, Z((int64_t)k2 - (int64_t)k1))), "the replacement keeps its shift ±(%llu − %llu)", (unsigned long long)k1, (unsigned long long)k2);
    EXPECT(!zx_is_zero(drep) && zx_is_zero(dK) && zx_is_zero(sum) && chain_nterms(bK) == 6, "the 3-cell: ⟨dω, ∂K⟩ = ⟨ddω, K⟩ = 0 — the signed face defects sum to zero (replacement defect %s%llu on two opposite faces)", drep.sign < 0 ? "−" : "", (unsigned long long)(drep.sign ? (uint64_t)llabs((long long)((int64_t)k1 - (int64_t)k2)) : 0));
    printf("work: a=%llu b=%llu in both orders (scheduling defect 0); direct=%llu replaced=%llu (shift %lld kept); 3-cell defects sum to 0\n",
           (unsigned long long)wa[0], (unsigned long long)wb[0], (unsigned long long)k1, (unsigned long long)k2, (long long)((int64_t)k1 - (int64_t)k2));
    stop();
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    const char *m = argc > 1 ? argv[1] : "all";
    if (argc > 2) g_workers = (size_t)strtoull(argv[2], NULL, 10);
    bool all = !strcmp(m, "all");
    if (all || !strcmp(m, "faces")) t_faces();
    if (all || !strcmp(m, "d2")) t_d2();
    if (all || !strcmp(m, "product")) t_product();
    if (all || !strcmp(m, "stokes")) t_stokes();
    if (all || !strcmp(m, "local")) t_local();
    if (all || !strcmp(m, "cycles")) t_cycles();
    if (all || !strcmp(m, "work")) t_work();
    printf("test_stokes %s workers=%zu: %d failures\n", m, g_workers, fails);
    return fails ? 1 : 0;
}

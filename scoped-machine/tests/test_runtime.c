/* Acceptance of the runtime constructions (HANDOFF §§83–84, 96; PLAN step 5).
 *
 * Every production recipe is checked as a closed function at its type in the
 * empty context, at level tuples covering each source of a raised maximum.
 * The generic action is checked with unknown diagrams, proof and point,
 * including both inverse proofs at their full round-trip types and their
 * endpoints; runtime-computed diagrams act through the same function; the
 * adapter's exported values agree by conversion with the emitted forms. */
#include "../src/compiler.h"
#include "assoc.h"
#include <assert.h>

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static ContextId empty_ctx(void) { return context_make(0, NULL, fc_true()); }
static const char *K[] = { "", "maps_type", "maps_id", "maps_comp", "maps_inv", "singleton", "diagram_type", "zero", "node",
                           "lunit", "runit", "rinv", "linv", "assoc", "mid", "action", "equiv_maps", "cut_maps", "fibre_maps",
                           "res_type", "res_zero", "res_node", "res_action" };
static void closed(RecipeKind k, uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
    const Recipe *r = rt_recipe(k, a, b, c, d);
    const char *why = ""; uint64_t lv = 99;
    CheckStatus ts = check_is_type(empty_ctx(), fc_true(), r->type, &lv, &why);
    CheckStatus st = ts == CK_VALID ? check(empty_ctx(), fc_true(), r->value, r->type, &why) : ts;
    CHECK(st == CK_VALID && lv == r->level, "closed %s(%llu,%llu,%llu,%llu): %s %s (level %llu, expected %llu)", K[k],
          (unsigned long long)a, (unsigned long long)b, (unsigned long long)c, (unsigned long long)d, check_status_name(st), why,
          (unsigned long long)lv, (unsigned long long)r->level);
    if (st == CK_VALID) printf("  closed %s(%llu,%llu,%llu,%llu) checks\n", K[k], (unsigned long long)a, (unsigned long long)b, (unsigned long long)c, (unsigned long long)d);
    fflush(stdout);
}

int main(int argc, char **argv) {
    printf("== runtime constructions\n");
    machine_init(); eval_init(); check_init(); compiler_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *mode = argc > 1 ? argv[1] : "all";
    bool all = !strcmp(mode, "all");

    /* ---- 1. every recipe as a closed function ---- */
    if (all || !strcmp(mode, "closed")) {
        closed(RK_MAPS_TYPE, 0, 1, 0, 0); closed(RK_MAPS_ID, 0, 0, 0, 0); closed(RK_MAPS_COMP, 0, 1, 0, 0); closed(RK_MAPS_INV, 1, 0, 0, 0);
        closed(RK_SINGLETON, 0, 0, 0, 0); closed(RK_DIAGRAM_TYPE, 0, 0, 0, 0); closed(RK_ZERO, 0, 0, 0, 0);
        closed(RK_NODE, 0, 0, 0, 0); closed(RK_NODE, 1, 0, 0, 0); closed(RK_NODE, 0, 1, 0, 0); closed(RK_NODE, 0, 0, 1, 0);
        closed(RK_LUNIT, 0, 0, 0, 0); closed(RK_RUNIT, 0, 0, 0, 0); closed(RK_RINV, 0, 0, 0, 0); closed(RK_LINV, 0, 0, 0, 0);
        closed(RK_ASSOC, 0, 0, 0, 0); closed(RK_MID, 0, 0, 0, 0);
        closed(RK_ACTION, 0, 0, 0, 0); closed(RK_ACTION, 0, 1, 0, 0);
        closed(RK_EQUIV_MAPS, 0, 1, 0, 0); closed(RK_CUT_MAPS, 0, 0, 0, 0); closed(RK_FIBRE_MAPS, 0, 0, 0, 0);
        closed(RK_RES_TYPE, 0, 0, 0, 0); closed(RK_RES_ZERO, 0, 0, 0, 0); closed(RK_RES_NODE, 0, 0, 0, 0); closed(RK_RES_ACTION, 0, 0, 0, 0);
    }

    /* ---- 2. the generic action at unknown diagrams, proof and point ---- */
    if (all || !strcmp(mode, "action")) {
        RefId U0 = mk_universe(0);
        TermVarId vB = declare_term(U0, fc_true()); RefId B = ref_var(vB);
        RefId DT = rt_diagram_type(0, 0, B);
        TermVarId vL = declare_term(DT, fc_true()), vR = declare_term(DT, fc_true()); RefId L = ref_var(vL), R = ref_var(vR);
        RefId PT = mk_path_const(0, B, rt_dg_C(L), rt_dg_C(R));
        TermVarId vp = declare_term(PT, fc_true()), vy = declare_term(B, fc_true()); RefId p = ref_var(vp), y = ref_var(vy);
        RefId RL = rt_dg_R(L, y), RR = rt_dg_R(R, y);
        TermVarId vr = declare_term(RL, fc_true()), vs = declare_term(RR, fc_true()); RefId r = ref_var(vr), s = ref_var(vs);
        CtxDecl ds[7] = { { S_TERM, vB, U0 }, { S_TERM, vL, DT }, { S_TERM, vR, DT }, { S_TERM, vp, PT }, { S_TERM, vy, B }, { S_TERM, vr, RL }, { S_TERM, vs, RR } };
        ContextId G = context_make(7, ds, fc_true());
        RefId args[5] = { B, L, R, p, y };
        const Recipe *act = rt_recipe(RK_ACTION, 0, 0, 0, 0);
        RefId M = rt_inst(act, args), MA = rt_apply(act, args);
        const char *why = "";
        CHECK(check(G, fc_true(), M, rt_maps_type(0, 0, RL, RR), &why) == CK_VALID, "instantiated action : Maps(R_L y, R_R y) (%s)", why);
        CHECK(convert_term(G, fc_true(), M, MA, rt_maps_type(0, 0, RL, RR)) == CV_EQUAL, "instantiation and application of the closed action agree");
        RefId f = rt_c(M), g = rt_d(M), h = rt_h(M), k = rt_k(M);
        /* F = d_R(p⁻¹·c_L r) and G = d_L(p·c_R s), the §83.4 expressions */
        RefId CL = rt_dg_C(L), CR = rt_dg_C(R);
        RefId Fx = mk_app(rt_d(rt_dg_M(R, y)), mk_path_concat(0, B, CR, CL, y, mk_path_rev(0, B, CL, CR, p), mk_app(rt_c(rt_dg_M(L, y)), r)));
        RefId Gx = mk_app(rt_d(rt_dg_M(L, y)), mk_path_concat(0, B, CL, CR, y, p, mk_app(rt_c(rt_dg_M(R, y)), s)));
        CHECK(convert_term(G, fc_true(), mk_app(f, r), Fx, RR) == CV_EQUAL, "forward field ≡ d_R(p⁻¹·c_L r)");
        CHECK(convert_term(G, fc_true(), mk_app(g, s), Gx, RL) == CV_EQUAL, "reverse field ≡ d_L(p·c_R s)");
        RefId hr = mk_app(h, r), ks = mk_app(k, s), gfr = mk_app(g, mk_app(f, r)), fgs = mk_app(f, mk_app(g, s));
        CHECK(check(G, fc_true(), hr, mk_path_const(0, RL, gfr, r), &why) == CK_VALID, "h r : G(F r) = r (%s)", why);
        CHECK(check(G, fc_true(), ks, mk_path_const(0, RR, fgs, s), &why) == CK_VALID, "k s : F(G s) = s (%s)", why);
        CHECK(convert_term(G, fc_true(), mk_papp_const(0, RL, gfr, r, hr, iv_zero()), gfr, RL) == CV_EQUAL, "h r at 0 is G(F r)");
        CHECK(convert_term(G, fc_true(), mk_papp_const(0, RL, gfr, r, hr, iv_one()), r, RL) == CV_EQUAL, "h r at 1 is r");
        CHECK(convert_term(G, fc_true(), mk_papp_const(0, RR, fgs, s, ks, iv_zero()), fgs, RR) == CV_EQUAL, "k s at 0 is F(G s)");
        CHECK(convert_term(G, fc_true(), mk_papp_const(0, RR, fgs, s, ks, iv_one()), s, RR) == CV_EQUAL, "k s at 1 is s");
    }

    /* ---- 3. runtime-computed diagrams act through the same function ---- */
    if (all || !strcmp(mode, "computed")) {
        RefId U0 = mk_universe(0);
        TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
        TermVarId vt = declare_term(A, fc_true()), vy = declare_term(A, fc_true()); RefId t = ref_var(vt), y = ref_var(vy);
        RefId Pty = mk_path_const(0, A, t, y);
        TermVarId vq = declare_term(Pty, fc_true()); RefId q = ref_var(vq);
        CtxDecl ds[4] = { { S_TERM, vA, U0 }, { S_TERM, vt, A }, { S_TERM, vy, A }, { S_TERM, vq, Pty } };
        ContextId G = context_make(4, ds, fc_true());
        RefId DT = rt_diagram_type(0, 0, A);
        /* Q = λ x e. zero(A, x), passed through the identity function: a computed tail */
        TermVarId x = declare_term(A, fc_true()); RefId Ex = mk_path_const(0, A, t, ref_var(x)); TermVarId e = declare_term(Ex, fc_true());
        RefId za[2] = { A, ref_var(x) };
        RefId Q = mk_lam_lv(0, x, A, mk_lam_lv(0, e, Ex, rt_apply(rt_recipe(RK_ZERO, 0, 0, 0, 0), za)));
        RefId QT = mk_pi_lv(0, 1, x, A, mk_pi_lv(0, 1, e, Ex, DT));
        RefId Qc = mk_app(mk_id_fun(1, QT), Q);
        RefId na[4] = { A, A, t, Qc };
        RefId D = rt_apply(rt_recipe(RK_NODE, 0, 0, 0, 0), na);
        RefId z0[2] = { A, t };
        RefId Z = rt_apply(rt_recipe(RK_ZERO, 0, 0, 0, 0), z0);
        const char *why = "";
        CHECK(check(G, fc_true(), D, DT, &why) == CK_VALID, "computed node : Diagram(A) (%s)", why);
        CHECK(convert_term(G, fc_true(), rt_dg_C(D), t, A) == CV_EQUAL, "its centre is t");
        RefId p = mk_refl(0, A, t);
        RefId aa[5] = { A, D, Z, p, y };
        RefId M = rt_apply(rt_recipe(RK_ACTION, 0, 0, 0, 0), aa);
        RefId RD = rt_dg_R(D, y);
        CHECK(check(G, fc_true(), M, rt_maps_type(0, 0, RD, Pty), &why) == CK_VALID, "the action between computed diagrams (%s)", why);
        RefId back = mk_app(rt_d(M), q);
        WhnfStatus st; EvalResult *res = observe_checked(G, mk_fst(back), &st, &why);
        CHECK(st == W_OK && res && res->ref == t, "the reverse action's point is the centre t (status %d)", (int)st);
        res = observe_checked(G, mk_app(rt_c(M), back), &st, &why);
        CHECK(st == W_OK && res && res->cls == R_INTRODUCTION && !ref_is_var(res->ref) && ref_tag(res->ref) == T_PLAM, "forward after reverse is a path (status %d)", (int)st);
    }

    /* ---- 4. the adapter's export agrees with the emitted forms ---- */
    if (all || !strcmp(mode, "adapter")) {
        const char *why = "";
        Assoc As; assoc_build(&As, &why);
        CHECK(As.ok, "associativity compiles (%s)", why);
        if (As.ok) {
            ContextId Gy = context_extend_term(As.G, As.T.y, As.X);
            RefId y = ref_var(As.T.y);
            CHECK(diagram_validate(As.L, fc_true(), &why) == CK_VALID, "the exported left diagram checks (%s)", why);
            CHECK(convert_term(As.G, fc_true(), rt_dg_C(diagram_value(As.L)), diagram_canonical(As.L), As.X) == CV_EQUAL, "fst of the export ≡ o[ν]");
            CHECK(convert_type(Gy, fc_true(), rt_dg_R(diagram_value(As.L), y), diagram_realization(As.L)) == CV_EQUAL, "R(y) of the export ≡ the realization telescope");
            TermVarId rs; RefId c = diagram_collapse(As.L, &rs);
            ContextId Gr = context_extend_term(Gy, rs, diagram_realization(As.L));
            CHECK(check(Gr, fc_true(), c, mk_path_const(0, As.X, diagram_canonical(As.L), y), &why) == CK_VALID, "collapse r : Path(C, y) (%s)", why);
            WhnfStatus st; EvalResult *res = whnf(c, fc_true(), &st);
            CHECK(st == W_OK && res && !ref_is_var(res->ref) && ref_tag(res->ref) == T_PLAM, "the collapse computes to a path (status %d)", (int)st);
            TermVarId qs; RefId xq = diagram_expand(As.R, &qs);
            res = whnf(mk_fst(xq), fc_true(), &st);
            CHECK(st == W_OK && res && res->ref == As.mbc, "d_R(q) has first component m(b,c)");
            CHECK(As.T.maps && As.T.domain == diagram_realization(As.L), "the identity action is the instantiated generic action");
        }
    }
    printf("  %d passed, %d failed\n", np, nf);
    compiler_free(); check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}

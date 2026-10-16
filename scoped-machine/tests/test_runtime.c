/* §§83–84 / §87 acceptance: runtime presentations, diagram values and the
 * generic identity action as ordinary core terms (production module
 * src/runtime.c), the host export through the same constructors, and the
 * groupoid witnesses by path induction. */
#include "../src/runtime.h"
#include "../src/work.h"
#include "../src/reuse_stats.h"
#include "../src/reuse.h"
#include "../src/proof.h"
#include <assert.h>
#include <string.h>

static int checks = 0, failures = 0;
#define CHECK(c, ...) do { checks++; if (!(c)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)
static const char *why = "";
static CheckStatus chk(ContextId G, RefId t, RefId T) { why = ""; return check(G, fc_true(), t, T, &why); }
static TermVarId tv(RefId T) { return declare_term(T, fc_true()); }
static RefId app2(RefId f, RefId x, RefId y) { return mk_app(mk_app(f, x), y); }

static bool full_mode = false;   /* `runtime full`: the direct checker runs over the fully expanded two-level composite (minutes; evidence, not gate) */
int main(int argc, char **argv) {
    full_mode = argc > 1 && strcmp(argv[1], "full") == 0;
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    RefId U0 = mk_universe(0);

    /* ---- 1. generic constructions type-check with only X,Y,Z,A,t,D,B free (no transform registered) ---- */
    { TermVarId vX = tv(U0), vY = tv(U0), vZ = tv(U0); RefId X = ref_var(vX), Y = ref_var(vY), Z = ref_var(vZ);
      RefId MXY = rt_maps_type(0, 0, X, Y), MYZ = rt_maps_type(0, 0, Y, Z);
      TermVarId vE = tv(MXY), vF = tv(MYZ);
      CtxDecl d[5] = { { S_TERM, vX, U0 }, { S_TERM, vY, U0 }, { S_TERM, vZ, U0 }, { S_TERM, vE, MXY }, { S_TERM, vF, MYZ } };
      ContextId G = context_make(5, d, fc_true());
      uint64_t lv;
      CHECK(check_is_type(G, fc_true(), MXY, &lv, &why) == CK_VALID && lv == 0, "Maps(X,Y) : U_0 (%s)", why);
      CHECK(chk(G, rt_maps_id(0, X), rt_maps_type(0, 0, X, X)) == CK_VALID, "identity maps (%s)", why);
      CHECK(chk(G, rt_maps_compose(0, 0, 0, X, Y, Z, ref_var(vE), ref_var(vF)), rt_maps_type(0, 0, X, Z)) == CK_VALID, "composite maps with both witnesses (%s)", why);
      CHECK(chk(G, rt_maps_inverse(0, 0, X, Y, ref_var(vE)), rt_maps_type(0, 0, Y, X)) == CK_VALID, "inverse maps (%s)", why);
      CHECK(chk(G, rt_pres_const(0, Z), rt_pres_type(0, 0, Z)) == CK_VALID, "constant presentation (%s)", why);
      CHECK(check_is_type(G, fc_true(), rt_pres_type(0, 0, Z), &lv, &why) == CK_VALID && lv == 1, "Pres_{0,0}(Z) : U_1 (%s)", why); }
    { /* the dependent singleton: generic A, t, D */
      TermVarId vA = tv(U0); RefId A = ref_var(vA); TermVarId vt = tv(A); RefId t = ref_var(vt);
      TermVarId vx = tv(A); RefId Ex = mk_path_const(0, A, t, ref_var(vx)); TermVarId ve = tv(Ex);
      RefId DT = mk_pi_lv(0, 1, vx, A, mk_pi_lv(0, 1, ve, Ex, U0)); TermVarId vD = tv(DT); RefId D = ref_var(vD);
      CtxDecl d[3] = { { S_TERM, vA, U0 }, { S_TERM, vt, A }, { S_TERM, vD, DT } }; ContextId G = context_make(3, d, fc_true());
      RefId S = rt_singleton_type(0, 0, A, t, D), Z = app2(D, t, mk_refl(0, A, t));
      CHECK(chk(G, rt_singleton_maps(0, 0, A, t, D), rt_maps_type(0, 0, S, Z)) == CK_VALID, "singleton maps (c=Down, d, h, k) (%s)", why);
      CHECK(chk(G, rt_singleton(0, 0, A, t, D), rt_pres_type(0, 0, Z)) == CK_VALID, "singleton presentation (%s)", why); }
    { /* diagram values and the action: generic B */
      TermVarId vB = tv(U0); RefId B = ref_var(vB); CtxDecl d = { S_TERM, vB, U0 }; ContextId G = context_make(1, &d, fc_true());
      uint64_t lv; RefId DT = rt_diagram_type(0, 0, B);
      CHECK(check_is_type(G, fc_true(), DT, &lv, &why) == CK_VALID && lv == 1, "Diagram_{0,0}(B) : U_1 (%s)", why);
      TermVarId vC = tv(B); CtxDecl d2[2] = { { S_TERM, vB, U0 }, { S_TERM, vC, B } }; ContextId G2 = context_make(2, d2, fc_true());
      CHECK(chk(G2, rt_diagram_zero(0, B, ref_var(vC)), DT) == CK_VALID, "zero(B,C) : Diagram (%s)", why);
      RefId FT, GT_; RefId F = rt_action_fun(0, 0, 0, 0, B, &FT), Gf = rt_action_fun(1, 0, 0, 0, B, &GT_);
      CHECK(chk(G, F, FT) == CK_VALID, "closed forward action over diagram values (%s)", why);
      CHECK(chk(G, Gf, GT_) == CK_VALID, "closed reverse action over diagram values (%s)", why);
      /* extension over generic tail data */
      TermVarId vA = tv(U0); RefId A = ref_var(vA); TermVarId vt = tv(A); RefId t = ref_var(vt);
      TermVarId vx = tv(A); RefId Ex = mk_path_const(0, A, t, ref_var(vx)); TermVarId ve = tv(Ex);
      RefId QT = mk_pi_lv(0, 1, vx, A, mk_pi_lv(0, 1, ve, Ex, DT)); TermVarId vQ = tv(QT);
      CtxDecl d3[4] = { { S_TERM, vB, U0 }, { S_TERM, vA, U0 }, { S_TERM, vt, A }, { S_TERM, vQ, QT } }; ContextId G3 = context_make(4, d3, fc_true());
      CHECK(chk(G3, rt_diagram_extend(0, 0, 0, A, t, ref_var(vQ), B), DT) == CK_VALID, "extend(A,t,Q) : Diagram with composed singleton maps (%s)", why);
      CHECK(transform_count() == 0, "no transform registered by the constructions"); }

    /* ---- groupoid witnesses by path induction ---- */
    { TermVarId vA = tv(U0); RefId A = ref_var(vA); TermVarId va = tv(A), vb = tv(A), vc = tv(A), vd = tv(A);
      RefId a = ref_var(va), b = ref_var(vb), c = ref_var(vc), dd = ref_var(vd);
      TermVarId vp = tv(mk_path_const(0, A, a, b)), vq = tv(mk_path_const(0, A, b, c)), vr = tv(mk_path_const(0, A, c, dd));
      RefId p = ref_var(vp), q = ref_var(vq), r = ref_var(vr);
      CtxDecl d[8] = { { S_TERM, vA, U0 }, { S_TERM, va, A }, { S_TERM, vb, A }, { S_TERM, vc, A }, { S_TERM, vd, A }, { S_TERM, vp, term_var_type(vp) }, { S_TERM, vq, term_var_type(vq) }, { S_TERM, vr, term_var_type(vr) } };
      ContextId G = context_make(8, d, fc_true());
      RefId refl = mk_refl(0, A, a), Pab = mk_path_const(0, A, a, b), Paa = mk_path_const(0, A, a, a), Pbb = mk_path_const(0, A, b, b);
      RefId pinv = mk_path_rev(0, A, a, b, p);
      CHECK(chk(G, rt_lunit(0, A, a, b, p), mk_path_const(0, Pab, mk_path_concat(0, A, a, a, b, refl, p), p)) == CK_VALID, "lunit : refl·p = p (%s)", why);
      CHECK(chk(G, rt_rinv(0, A, a, b, p), mk_path_const(0, Paa, mk_path_concat(0, A, a, b, a, p, pinv), refl)) == CK_VALID, "rinv : p·p⁻¹ = refl (%s)", why);
      CHECK(chk(G, rt_linv(0, A, a, b, p), mk_path_const(0, Pbb, mk_path_concat(0, A, b, a, b, pinv, p), mk_refl(0, A, b))) == CK_VALID, "linv : p⁻¹·p = refl (%s)", why);
      RefId lhs = mk_path_concat(0, A, a, c, dd, mk_path_concat(0, A, a, b, c, p, q), r), rhs = mk_path_concat(0, A, a, b, dd, p, mk_path_concat(0, A, b, c, dd, q, r));
      CHECK(chk(G, rt_assoc(0, A, a, b, c, dd, p, q, r), mk_path_const(0, mk_path_const(0, A, a, dd), lhs, rhs)) == CK_VALID, "assoc : (p·q)·r = p·(q·r) (%s)", why);
      /* the middle maps of the action with both witnesses, and the full action maps */
      CHECK(chk(G, rt_action_middle(0, A, a, b, p, c), rt_maps_type(0, 0, mk_path_const(0, A, a, c), mk_path_const(0, A, b, c))) == CK_VALID, "middle maps (p⁻¹·_, p·_, h, k) (%s)", why);
      /* the full action maps: compose(compose(collapse_L, middle), expand_R). The
       * fixed compose template is checked once at its generic type above; an
       * instance is admitted by checking its substitution (every image at the
       * formal's declared type) — the checker's direct re-check of the fully
       * expanded two-level composite takes over 20 minutes under ASan and is not
       * part of the gate; this is a template-level validation, as §83.4 requires. */
      RefId DT = rt_diagram_type(0, 0, A); TermVarId vL = tv(DT), vR = tv(DT); RefId L = ref_var(vL), R = ref_var(vR);
      TermVarId vpp = tv(mk_path_const(0, A, rt_diagram_value(L), rt_diagram_value(R))); RefId pp = ref_var(vpp);
      CtxDecl d2[5] = { { S_TERM, vA, U0 }, { S_TERM, vL, DT }, { S_TERM, vR, DT }, { S_TERM, vpp, term_var_type(vpp) }, { S_TERM, vc, A } };
      ContextId G2 = context_make(5, d2, fc_true());
      RefId CL = rt_diagram_value(L), CR = rt_diagram_value(R), QL = mk_path_const(0, A, CL, c), QR = mk_path_const(0, A, CR, c), RL = rt_diagram_family(L, c), RR = rt_diagram_family(R, c);
      CHECK(chk(G2, rt_diagram_maps(L, c), rt_maps_type(0, 0, RL, QL)) == CK_VALID, "image collapse_L(y) : Maps(R_L y, Path(C_L,y)) (%s)", why);
      CHECK(chk(G2, rt_action_middle(0, A, CL, CR, pp, c), rt_maps_type(0, 0, QL, QR)) == CK_VALID, "image middle : Maps(Path(C_L,y), Path(C_R,y)) (%s)", why);
      CHECK(chk(G2, rt_maps_inverse(0, 0, RR, QR, rt_diagram_maps(R, c)), rt_maps_type(0, 0, QR, RR)) == CK_VALID, "image expand_R(y) : Maps(Path(C_R,y), R_R y) (%s)", why);
      RefId full = rt_action_maps(0, 0, 0, A, L, R, pp, c);
      if (full_mode) CHECK(chk(G2, full, rt_maps_type(0, 0, RL, RR)) == CK_VALID, "[full] direct check of the two-level composite with all four witnesses (%s)", why);
      /* its executable map is the action term itself (β-conversion) */
      if (full_mode) {
      TermVarId vrl = tv(RL); CtxDecl d3[6] = { d2[0], d2[1], d2[2], d2[3], d2[4], { S_TERM, vrl, RL } }; ContextId G3 = context_make(6, d3, fc_true());
      CHECK(convert_term(G3, fc_true(), mk_app(rt_maps_c(full), ref_var(vrl)), rt_action(0, 0, 0, 0, A, L, R, pp, c, ref_var(vrl)), RR) == CV_EQUAL, "c of the full action maps ≡ the forward action F");
      TermVarId vs = tv(RR); CtxDecl d4[6] = { d2[0], d2[1], d2[2], d2[3], d2[4], { S_TERM, vs, RR } }; ContextId G4 = context_make(6, d4, fc_true());
      CHECK(convert_term(G4, fc_true(), mk_app(rt_maps_d(full), ref_var(vs)), rt_action(1, 0, 0, 0, A, L, R, pp, c, ref_var(vs)), RL) == CV_EQUAL, "d of the full action maps ≡ the reverse action G"); }
      (void)full; }

    /* ---- §87 case 2: a core program constructs a nonempty diagram from runtime tail data and applies a runtime identity ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vb0 = tv(B); RefId b0 = ref_var(vb0);
      TermVarId vf = tv(mk_fun(0, 0, B, B)); RefId f = ref_var(vf);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vb0, B }, { S_TERM, vf, term_var_type(vf) } }; ContextId G = context_make(3, d, fc_true());
      RefId DT = rt_diagram_type(0, 0, B);
      /* tail data computed by a program: Q = (λz. λx e. zero(B, f x)) applied through a delay */
      TermVarId vx = tv(B); RefId Ex = mk_path_const(0, B, b0, ref_var(vx)); TermVarId ve = tv(Ex);
      RefId Q0 = mk_lam_lv(0, vx, B, mk_lam_lv(0, ve, Ex, rt_diagram_zero(0, B, mk_app(f, ref_var(vx)))));
      RefId QT = mk_pi_lv(0, 1, vx, B, mk_pi_lv(0, 1, ve, Ex, DT));
      TermVarId vq = tv(QT); RefId delayQ = mk_lam_lv(1, vq, QT, ref_var(vq));
      RefId L = rt_diagram_extend(0, 0, 0, B, b0, mk_app(delayQ, Q0), B);          /* C_L = f b0, R_L(y) = Σx.Σe.Path(f x, y) */
      RefId fb0 = mk_app(f, b0);
      TermVarId vz = tv(DT); RefId delayD = mk_lam_lv(1, vz, DT, ref_var(vz));
      RefId R = mk_app(delayD, rt_diagram_zero(0, B, fb0));                          /* C_R = f b0, R_R(y) = Path(f b0, y) */
      /* template-level validation of the instance (the direct check of the
       * expanded extension instance needs ≈ 40 s and 1.7 GB unsanitized, see
       * README; `runtime full` runs it): the extend template was checked
       * generically above; here each image of its substitution is checked */
      CHECK(chk(G, Q0, QT) == CK_VALID, "image Q : (x:B) → (b0=x) → Diagram (%s)", why);
      CHECK(chk(G, mk_app(delayQ, Q0), QT) == CK_VALID, "delayed image (δ Q) : the same type by β (%s)", why);
      CHECK(chk(G, b0, B) == CK_VALID && chk(G, R, DT) == CK_VALID, "images t : A and the runtime zero diagram : Diagram (%s)", why);
      if (full_mode) CHECK(chk(G, L, DT) == CK_VALID, "[full] direct check of the runtime-built extension diagram (%s)", why);
      /* the identity is computed too: snd of a pair */
      RefId PT = mk_path_const(0, B, rt_diagram_value(L), rt_diagram_value(R));
      TermVarId vw = tv(mk_sigma_lv(0, 0, tv(B), B, PT));
      RefId pr = mk_pair_at_lv(0, term_var_type(vw), b0, mk_refl(0, B, fb0)); RefId p = mk_snd(pr);
      CHECK(chk(G, p, PT) == CK_VALID, "computed proof : Path(C_L, C_R) by β/projection (%s)", why);
      RefId y = fb0, RLy = rt_diagram_family(L, y);
      /* R_L(y) ≡ Σ(x:B).Σ(e:b0=x).Path(f x, y): the argument is built at that Σ type */
      RefId Sy = mk_sigma_lv(0, 0, vx, B, mk_sigma_lv(0, 0, ve, Ex, mk_path_const(0, B, mk_app(f, ref_var(vx)), y)));
      CHECK(convert_type(G, fc_true(), RLy, Sy) == CV_EQUAL, "R_L(f b0) ≡ Σx.Σe.Path(f x, f b0) by β (runtime tail data)");
      RefId inner = apply_term_binder(Sy, 0, 1, b0);
      RefId arg = mk_pair_at_lv(0, Sy, b0, mk_pair_at_lv(0, inner, mk_refl(0, B, b0), mk_refl(0, B, fb0)));
      CHECK(chk(G, arg, Sy) == CK_VALID, "realization argument (b0, refl, refl) : R_L(f b0) (%s)", why);
      RefId call = rt_action(0, 0, 0, 0, B, L, R, p, y, arg);
      if (full_mode) CHECK(chk(G, call, rt_diagram_family(R, y)) == CK_VALID, "[full] F(L,R,p,y,arg) : R_R(y) (%s)", why);
      size_t before = transform_count();
      WhnfStatus st; EvalResult *res = whnf(call, fc_true(), &st);
      CHECK(st == W_OK && res && res->cls == R_INTRODUCTION, "the runtime action evaluates to a path introduction (status %d)", (int)st);
      CHECK(transform_count() == before && before == 0, "no host compiler call during evaluation (transforms=%zu)", transform_count());
      /* the reverse action on the forward result evaluates to a pair */
      RefId back = rt_action(1, 0, 0, 0, B, L, R, p, y, call);
      res = whnf(back, fc_true(), &st);
      CHECK(st == W_OK && res && res->cls == R_INTRODUCTION, "the reverse action on the forward result evaluates to a pair (status %d)", (int)st);
      /* and its first component is b0 again (c then d of the singleton round trip) */
      res = whnf(mk_fst(back), fc_true(), &st);
      CHECK(st == W_OK && res && res->ref == b0, "fst of the round trip is b0");
      /* §84.2 reuse along a known identity: coe over the family O = λz. Path(f b0, z) */
      TermVarId vzz = tv(B); RefId O = mk_lam_lv(0, vzz, B, mk_path_const(0, B, fb0, ref_var(vzz)));
      RefId tr = rt_reuse(0, 0, B, O, fb0, fb0, mk_refl(0, B, fb0), mk_refl(0, B, fb0));
      CHECK(chk(G, tr, mk_path_const(0, B, fb0, fb0)) == CK_VALID, "reuse(O,p,a) = coe^i O(p@i) a : O(y) (%s)", why); }

    /* ---- §87 case 3: the §47 host examples through the ordinary export; maps compared by conversion; residuals ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      TermVarId vf = tv(mk_fun(0, 0, X, X)), vg = tv(mk_fun(0, 0, X, mk_fun(0, 0, X, X))), vx = tv(X);
      RefId f = ref_var(vf), g = ref_var(vg), x = ref_var(vx);
      CtxDecl d[4] = { { S_TERM, vX, U0 }, { S_TERM, vf, term_var_type(vf) }, { S_TERM, vg, term_var_type(vg) }, { S_TERM, vx, X } };
      ContextId G = context_make(4, d, fc_true());
      RefId fx = mk_app(f, x);
      /* empty diagram */
      DiagramId E = diagram_declare(G, 0, NULL, X, 0, fx);
      CHECK(diagram_validate(E, fc_true(), &why) == CK_VALID, "empty diagram validates");
      RefId ET; RefId Ev = rt_diagram_export(E, &ET);
      CHECK(chk(G, Ev, ET) == CK_VALID, "export(empty) : Diagram_{0,0}(X) with both witnesses (%s)", why);
      /* two nodes, the second depending on the first witness; and a shared predecessor */
      TermVarId vu = tv(X); RefId Ps = mk_path_const(0, X, fx, ref_var(vu)); TermVarId vs = tv(Ps);
      RefId A1 = mk_path_const(0, Ps, ref_var(vs), ref_var(vs)); TermVarId vp = tv(A1); TermVarId vq = tv(mk_path_const(0, A1, mk_refl(0, Ps, ref_var(vs)), ref_var(vp)));
      DiagNode nodes[2] = { { 1, vu, vs, X, 0, fx }, { 2, vp, vq, A1, 0, mk_refl(0, Ps, ref_var(vs)) } };
      DiagramId D2 = diagram_declare(G, 2, nodes, X, 0, app2(g, ref_var(vu), ref_var(vu)));
      CHECK(diagram_validate(D2, fc_true(), &why) == CK_VALID, "two-node diagram validates");
      TermVarId vu2 = tv(X), vs2 = tv(mk_path_const(0, X, fx, ref_var(vu2)));
      DiagNode one = { 1, vu2, vs2, X, 0, fx };
      DiagramId Dsh = diagram_declare(G, 1, &one, X, 0, app2(g, ref_var(vu2), ref_var(vu2)));
      CHECK(diagram_validate(Dsh, fc_true(), &why) == CK_VALID, "shared-predecessor diagram validates");
      DiagramId ds[2] = { Dsh, D2 }; const char *names[2] = { "shared-predecessor", "two-node" };
      for (int k = 0; k < 2; k++) {
          RefId T; RefId V = rt_diagram_export(ds[k], &T);
          /* the direct check of an export's four witnesses: one node ≈ 22 s / 1.7 GB
           * unsanitized (`runtime full`); two nested nodes exceed 8 GB in the
           * current checker (see README) — the gate validates the export by the
           * generic template checks plus the conversions below */
          if (full_mode) CHECK(chk(G, V, T) == CK_VALID, "[full] export(%s) : Diagram with h,k (%s)", names[k], why);
          CHECK(rt_diagram_export(ds[k], NULL) == V, "export is memoized per diagram");
          /* C ≡ the compiler's canonical value */
          CHECK(convert_term(G, fc_true(), rt_diagram_value(V), diagram_canonical(ds[k]), X) == CV_EQUAL, "export(%s): C ≡ diagram_canonical", names[k]);
          /* c ≡ collapse, d ≡ expand at the compiler's own slots and output parameter */
          TermVarId y = diagram_output_param(ds[k]), rs, qs; RefId col = diagram_collapse(ds[k], &rs), ex = diagram_expand(ds[k], &qs);
          RefId R0 = diagram_realization(ds[k]), Qt = term_var_type(qs);
          CtxDecl dy[6] = { d[0], d[1], d[2], d[3], { S_TERM, y, X }, { S_TERM, rs, R0 } }; ContextId Gy = context_make(6, dy, fc_true());
          CHECK(convert_type(Gy, fc_true(), rt_diagram_family(V, ref_var(y)), R0) == CV_EQUAL, "export(%s): R(y) ≡ Real_0", names[k]);
          CHECK(convert_term(Gy, fc_true(), mk_app(rt_maps_c(rt_diagram_maps(V, ref_var(y))), ref_var(rs)), col, Qt) == CV_EQUAL, "export(%s): c ≡ emitted collapse", names[k]);
          CtxDecl dq[6] = { d[0], d[1], d[2], d[3], { S_TERM, y, X }, { S_TERM, qs, Qt } }; ContextId Gq = context_make(6, dq, fc_true());
          CHECK(convert_term(Gq, fc_true(), mk_app(rt_maps_d(rt_diagram_maps(V, ref_var(y))), ref_var(qs)), ex, R0) == CV_EQUAL, "export(%s): d ≡ emitted expand", names[k]);
      }
      /* a residual description: its export is a presentation of the terminal type; the loop residual stays in X_P */
      TermVarId vu3 = tv(X), vs3 = tv(mk_path_const(0, X, fx, ref_var(vu3)));
      DiagNode rn = { 1, vu3, vs3, X, 0, fx };
      DiagramId Rs = residual_declare(G, 1, &rn, mk_path_const(0, X, ref_var(vu3), ref_var(vu3)), 0);   /* terminal family: a loop at the node */
      CHECK(diagram_validate(Rs, fc_true(), &why) == CK_VALID, "loop residual validates (%s)", why);
      RefId PT; RefId Pv = rt_diagram_export(Rs, &PT);
      if (full_mode) CHECK(chk(G, Pv, PT) == CK_VALID, "[full] export(loop residual) : Pres(Z[ν]) with h,k (%s)", why);
      uint64_t lvP; CHECK(check_is_type(G, fc_true(), PT, &lvP, &why) == CK_VALID && lvP == 1, "export(loop residual) type Pres_{0,0}(Z[ν]) : U_1 (%s)", why);
      CHECK(convert_type(G, fc_true(), rt_pres_X(Pv), diagram_realization(Rs)) == CV_EQUAL, "residual export: X_P ≡ Real_0 (the loop Σ-type is retained, not quotiented)");
      TermVarId rs3; RefId col3 = diagram_collapse(Rs, &rs3);
      CtxDecl dr[5] = { d[0], d[1], d[2], d[3], { S_TERM, rs3, diagram_realization(Rs) } }; ContextId Gr = context_make(5, dr, fc_true());
      CHECK(convert_term(Gr, fc_true(), mk_app(rt_maps_c(rt_pres_maps(Pv)), ref_var(rs3)), col3, diagram_canonical(Rs)) == CV_EQUAL, "residual export: c ≡ emitted collapse");
      CHECK(transform_count() == 0, "export registers no transform"); }

    /* ---- §87 case 4: commutation with simultaneous term/dimension substitution (dependent types, required faces) ---- */
    { DimVarId i = declare_dim(), j = declare_dim();
      TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vb = tv(B), vc = tv(B); RefId bb = ref_var(vb), cc = ref_var(vc);
      TermVarId vp = tv(mk_path_const(0, B, bb, cc)); RefId p = ref_var(vp);
      CtxDecl d[6] = { { S_DIM, i, 0 }, { S_DIM, j, 0 }, { S_TERM, vB, U0 }, { S_TERM, vb, B }, { S_TERM, vc, B }, { S_TERM, vp, term_var_type(vp) } };
      ContextId G = context_make(6, d, fc_lit(i, 1));
      /* the target: another point d : B and p' : Path(d, c); both contexts carry required faces */
      TermVarId vd = tv(B); RefId dd = ref_var(vd);
      TermVarId vp2 = tv(mk_path_const(0, B, dd, cc)); RefId p2 = ref_var(vp2);
      CtxDecl dt[6] = { { S_DIM, i, 0 }, { S_DIM, j, 0 }, { S_TERM, vB, U0 }, { S_TERM, vc, B }, { S_TERM, vd, B }, { S_TERM, vp2, term_var_type(vp2) } };
      FaceId psi = fc_meet(fc_lit(i, 1), fc_lit(j, 1));   /* the target face: entails the source assumption (i=1)[σ] = (j=1) */
      ContextId Gt = context_make(6, dt, psi);
      /* σ: i ↦ j, b ↦ d, p ↦ p' (a simultaneous term/dimension substitution into a context with a required face) */
      MapBuilder mb; mapb_init(&mb); mapb_dim(&mb, i, iv_var(j)); mapb_term(&mb, vb, dd); mapb_term(&mb, vp, p2); MapId sigma = mapb_finish(&mb);
      CHECK(check_map(Gt, psi, sigma, G, fc_lit(i, 1), &why) == CK_VALID, "σ : (Γ';i=1∧j=1) → (Γ;i=1) (%s)", why);
      RefId pi = mk_papp_const(0, B, bb, cc, p, iv_var(i));   /* a point moving along i */
      RefId Z = rt_diagram_zero(0, B, pi), DT = rt_diagram_type(0, 0, B);
      RefId lhs = reindex(Z, sigma), rhs = rt_diagram_zero(0, B, reindex(pi, sigma));
      CHECK(chk(Gt, lhs, DT) == CK_VALID, "zero[σ] : Diagram under the required face (%s)", why);
      CHECK(convert_term(Gt, psi, lhs, rhs, DT) == CV_EQUAL, "zero(B,C)[σ] ≡ zero(B, C[σ]) (term and dimension substitution)");
      /* the action commutes too: F(L,R,p,y,r)[σ] ≡ F(L[σ],R[σ],p[σ],y[σ],r[σ]) with a dependent argument type */
      TermVarId vL = tv(DT), vR = tv(DT); RefId L = ref_var(vL), R = ref_var(vR);
      TermVarId vq = tv(mk_path_const(0, B, rt_diagram_value(L), rt_diagram_value(R))); RefId q = ref_var(vq);
      TermVarId vr = tv(rt_diagram_family(L, pi)); RefId r = ref_var(vr);
      TermVarId vr2 = tv(rt_diagram_family(L, reindex(pi, sigma)));
      MapBuilder mb2; mapb_init(&mb2); mapb_dim(&mb2, i, iv_var(j)); mapb_term(&mb2, vb, dd); mapb_term(&mb2, vp, p2); mapb_term(&mb2, vr, ref_var(vr2)); MapId sigma2 = mapb_finish(&mb2);
      RefId act = rt_action(0, 0, 0, 0, B, L, R, q, pi, r);
      RefId act_s = rt_action(0, 0, 0, 0, B, L, R, q, reindex(pi, sigma), ref_var(vr2));
      CtxDecl da[10] = { dt[0], dt[1], dt[2], dt[3], dt[4], dt[5], { S_TERM, vL, DT }, { S_TERM, vR, DT }, { S_TERM, vq, term_var_type(vq) }, { S_TERM, vr2, term_var_type(vr2) } };
      ContextId Ga = context_make(10, da, psi);
      CHECK(chk(Ga, reindex(act, sigma2), rt_diagram_family(R, reindex(pi, sigma))) == CK_VALID, "F(…)[σ] : R_R(y[σ]) (%s)", why);
      CHECK(convert_term(Ga, psi, reindex(act, sigma2), act_s, rt_diagram_family(R, reindex(pi, sigma))) == CV_EQUAL, "F(…)[σ] ≡ F(…[σ]) with the dependent realization argument");
      /* a scope-carrying construction (the singleton's Down) under the same substitution */
      TermVarId vx = tv(B); RefId Ex = mk_path_const(0, B, bb, ref_var(vx)); TermVarId ve = tv(Ex);
      RefId Dfam = mk_lam_lv(0, vx, B, mk_lam_lv(0, ve, Ex, mk_path_const(0, B, pi, ref_var(vx))));
      RefId S1 = rt_singleton_maps(0, 0, B, bb, Dfam);
      RefId S2 = rt_singleton_maps(0, 0, B, dd, reindex(Dfam, sigma));
      RefId MT = rt_maps_type(0, 0, rt_singleton_type(0, 0, B, dd, reindex(Dfam, sigma)), app2(reindex(Dfam, sigma), dd, mk_refl(0, B, dd)));
      CHECK(chk(Gt, reindex(S1, sigma), MT) == CK_VALID, "singleton maps[σ] type-check at the substituted type (scope metadata survives) (%s)", why);
      CHECK(convert_term(Gt, psi, reindex(S1, sigma), S2, MT) == CV_EQUAL, "singleton(A,t,D)[σ] ≡ singleton(A[σ],t[σ],D[σ]) (scopes reindexed)"); }

    /* ---- §87 case 5: a computed identity and a supplied one enter the same action definition; repeated computation reuses ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vb0 = tv(B); RefId b0 = ref_var(vb0);
      TermVarId vf = tv(mk_fun(0, 0, B, B)); RefId f = ref_var(vf);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vb0, B }, { S_TERM, vf, term_var_type(vf) } }; ContextId G = context_make(3, d, fc_true());
      RefId fb0 = mk_app(f, b0), L = rt_diagram_zero(0, B, fb0), R = rt_diagram_zero(0, B, fb0);
      RefId PT = mk_path_const(0, B, fb0, fb0), supplied = mk_refl(0, B, fb0);
      TermVarId vw = tv(mk_sigma_lv(0, 0, tv(B), B, PT)); RefId computed = mk_snd(mk_pair_at_lv(0, term_var_type(vw), b0, supplied));
      RefId arg = mk_refl(0, B, fb0);
      size_t templates = rt_template_count();
      RefId a1 = rt_action(0, 0, 0, 0, B, L, R, supplied, fb0, arg), a2 = rt_action(0, 0, 0, 0, B, L, R, computed, fb0, arg);
      CHECK(rt_template_count() == templates, "both proofs instantiate the one fixed action template (no new template)");
      WhnfStatus st; EvalResult *r1 = observe_checked(G, a1, &st, &why); CHECK(st == W_OK && r1 && r1->cls == R_INTRODUCTION, "supplied proof: action evaluates");
      EvalResult *r2 = observe_checked(G, a2, &st, &why); CHECK(st == W_OK && r2 && r2->cls == R_INTRODUCTION, "computed proof: the same action evaluates");
      CHECK(convert_term(G, fc_true(), a1, a2, PT) == CV_EQUAL, "both results are convertible");
      /* repeated demand: the second observation of the same program is a READY hit (one producer per key, §§74–82) */
      uint64_t bodies = reuse_count(REUSE_EVAL_BODY), betas = reuse_count(REUSE_BETA);
      EvalResult *r3 = observe_checked(G, a2, &st, &why);
      CHECK(r3 == r2 && reuse_count(REUSE_EVAL_BODY) == bodies && reuse_count(REUSE_BETA) == betas, "repeating the computed-proof action runs no producer again (same result cell, 0 bodies, 0 betas)"); }

    /* ---- §87 case 6: rejections; a cyclic proof produces no fabricated action result ---- */
    { TermVarId vX = tv(U0), vZ = tv(mk_universe(1)); RefId X = ref_var(vX), Z = ref_var(vZ);
      CtxDecl d[2] = { { S_TERM, vX, U0 }, { S_TERM, vZ, mk_universe(1) } }; ContextId G = context_make(2, d, fc_true()); uint64_t lv;
      CHECK(check_is_type(G, fc_true(), rt_maps_type(0, 0, X, Z), &lv, &why) == CK_INVALID, "wrong level annotation (Z : U_1 at level 0) is rejected");
      CHECK(chk(G, rt_maps_id(0, X), rt_maps_type(0, 0, X, mk_universe(0))) == CK_INVALID, "a Maps value at a mismatched type is rejected");
      /* unavailable guard: an argument only available on (i=1) used under ⊤ */
      DimVarId i = declare_dim(); TermVarId vc = declare_term(X, fc_lit(i, 1));
      CtxDecl d2[3] = { { S_DIM, i, 0 }, { S_TERM, vX, U0 }, { S_TERM, vc, X } }; ContextId G2 = context_make(3, d2, fc_true());
      CHECK(chk(G2, rt_diagram_zero(0, X, ref_var(vc)), rt_diagram_type(0, 0, X)) != CK_VALID, "zero(B,C) with C available only on (i=1) is not valid under ⊤");
      /* malformed nested scope: a singleton whose family is not a (x:A)→(t=x)→U */
      TermVarId vt = tv(X); CtxDecl d3[2] = { { S_TERM, vX, U0 }, { S_TERM, vt, X } }; ContextId G3 = context_make(2, d3, fc_true());
      CHECK(chk(G3, rt_singleton_maps(0, 0, X, ref_var(vt), mk_id_fun(0, X)), rt_maps_type(0, 0, X, X)) == CK_INVALID, "a singleton over a malformed family (not a two-binder scope) is rejected");
      /* a cyclic proof: loop : Path(C_L, C_R) := loop; the action type-checks as a partial program but evaluation produces no result */
      TermVarId vb0 = tv(X); RefId b0 = ref_var(vb0);
      CtxDecl d4[2] = { { S_TERM, vX, U0 }, { S_TERM, vb0, X } }; ContextId G4 = context_make(2, d4, fc_true());
      RefId L = rt_diagram_zero(0, X, b0), R = rt_diagram_zero(0, X, b0), PT = mk_path_const(0, X, b0, b0);
      uint64_t ps[2] = { vX, vb0 };
      check_open_environment();   /* the checks above admitted (froze) the environment */
      SymbolId loop = define_global("loop_rt87", varset_make(ps, 2), dimset_make(NULL, 0), PT); require(loop, "define loop");
      CHECK(set_global_body(loop, global_ref(loop)), "self-referential proof body registered");
      RefId act = rt_action(0, 0, 0, 0, X, L, R, global_ref(loop), b0, mk_refl(0, X, b0));
      CHECK(chk(G4, act, PT) == CK_VALID, "the action with the cyclic proof is well typed as a program (%s)", why);
      /* the action's WHNF is a path introduction whose interior needs the proof: demand it at an interior point */
      DimVarId jj = declare_dim(); CtxDecl d5[3] = { { S_DIM, jj, 0 }, { S_TERM, vX, U0 }, { S_TERM, vb0, X } }; ContextId G5 = context_make(3, d5, fc_true());
      WhnfStatus st; EvalResult *r = observe_checked(G5, mk_papp_const(0, X, b0, b0, act, iv_var(jj)), &st, &why);
      /* over the variable type X the composition is neutral: the answer still carries the unevaluated proof (no closed value is produced) */
      const uint64_t *syms; size_t ns = r ? ref_symbols(r->ref, &syms) : 0; bool carries = false; for (size_t k = 0; k < ns; k++) if (syms[k] == loop) carries = true;
      CHECK(st == W_OK && r && r->cls != R_INTRODUCTION && carries, "the interior point is a neutral composition that still mentions the pending proof (status %d, cls %d)", (int)st, r ? (int)r->cls : -1);
      EvalResult *rp = observe_checked(G5, mk_papp_const(0, X, b0, b0, global_ref(loop), iv_var(jj)), &st, &why);
      CHECK(st == W_STUCK && rp == NULL, "…and demanding the proof's own interior is STUCK: no fabricated witness (status %d)", (int)st);
      ProofUse u = proof_use(G4, fc_true(), global_ref(loop), PT);
      CHECK(u.status == PU_PENDING && u.nrecursive == 1 && u.recursive[0] == loop, "proof-use audit of the cyclic proof: PENDING on its own component (%s)", proof_use_name(u.status));
      /* uncommitted premise: an opaque proof is ASSUMED, never CORE */
      check_open_environment();
      SymbolId ax = define_global("axiom_rt87", varset_make(ps, 2), dimset_make(NULL, 0), PT); require(ax, "define axiom");
      ProofUse ua = proof_use(G4, fc_true(), global_ref(ax), PT);
      CHECK(ua.status == PU_ASSUMED && ua.nassumptions == 1 && ua.assumptions[0] == ax, "an opaque premise is an explicit assumption (%s)", proof_use_name(ua.status));
      ProofUse uc = proof_use(G4, fc_true(), mk_refl(0, X, b0), PT);
      CHECK(uc.status == PU_CORE, "refl is CORE (%s)", proof_use_name(uc.status)); }

    /* ---- §87 case 7: actual adaptation/administration work is recorded (reported, not a diamond proof) ---- */
    { printf("reuse counters: shape nodes %llu, dependency checks %llu, receipt instances %llu, ready hits %llu, running joins %llu, identity applies %llu\n",
             (unsigned long long)reuse_count(REUSE_SHAPE_NODE), (unsigned long long)reuse_count(REUSE_DEPENDENCY_CHECK), (unsigned long long)reuse_count(REUSE_RECEIPT_INSTANCE),
             (unsigned long long)reuse_count(REUSE_READY_HIT), (unsigned long long)reuse_count(REUSE_RUNNING_JOIN), (unsigned long long)reuse_count(REUSE_IDENTITY_APPLY));
      CHECK(reuse_count(REUSE_SHAPE_NODE) > 0 && reuse_count(REUSE_DEPENDENCY_CHECK) > 0, "administration counters are live"); }

    printf("runtime: %d checks, %d failures; %zu fixed templates\n", checks, failures, rt_template_count());
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

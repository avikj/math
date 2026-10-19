/* §47: identities as ordinary values. Declarations are right folds of node
 * ending in zero; the identity action is id_action applied; invocation is
 * application. Every check below is an ordinary judgment of the core. */
#define _POSIX_C_SOURCE 200809L
#include "reading.h"
#include "assoc.h"
#include "../src/proof.h"

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }
static Tag head_tag(EvalResult r) { if (!r.cls || ref_is_var(r.ref)) return 0; return ref_tag(r.ref); }
static RefId app3(RefId f, RefId a, RefId b, RefId c) { return mk_app(mk_app(mk_app(f, a), b), c); }

/* the number of whnf keys formed so far */
static size_t whnf_keys(void) { size_t c = 0, n = eval_entry_count(); for (EntryId e = 1; e <= n; e++) if (eval_entry_live(e) && eval_entry_family(e) == F_WHNF) c++; return c; }
int main(void) {
    printf("== §39–48 identities as ordinary values\n");
    machine_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *why = "";
    RefId U0 = mk_universe(0);

    /* ---- the associativity declaration, both orientations ---- */
    Assoc A; assoc_build(&A);
    CHECK(check(A.G, fc_true(), A.L, diagram_type(0, 0, A.X), &why) == CK_VALID, "the left diagram : Diagram(X) (%s)", why);
    CHECK(check(A.Gy, fc_true(), A.T, maps_type(0, 0, A.domain, A.codomain), &why) == CK_VALID, "id_action(X, L, R, α, y) : Maps(R_L y, R_R y) (%s)", why);
    CHECK(convert_term(A.G, fc_true(), dg_C(A.L), A.lhs, A.X) == CV_EQUAL, "C_L ≡ m(m(a,b),c)");
    { ProofUse u = proof_use(A.Gy, fc_true(), A.T, maps_type(0, 0, A.domain, A.codomain)); CHECK(u.status == PU_CORE, "the action is core evidence relative to its context (%s)", proof_status_name(u.status)); proof_use_free(&u); }
    MapId sigma = assoc_sigma(&A, A.rhs);
    RefId r = assoc_left_arg(&A, sigma);
    CHECK(check(A.G, fc_true(), r, reindex(A.domain, sigma), &why) == CK_VALID, "r_L : R_L[σ] (%s)", why);
    RefId call = assoc_call(&A, DIR_FORWARD, sigma, r);
    CHECK(check(A.G, fc_true(), call, reindex(A.codomain, sigma), &why) == CK_VALID, "F[σ](r) : R_R[σ] (%s)", why);
    WhnfStatus st; uint64_t p0 = rd(RD_PUBLISH, 0);
    EvalResult res = whnf(call, fc_true(), &st);
    CHECK(st == W_OK && res.cls == R_INTRODUCTION && head_tag(res) == T_PAIR, "forward call ⇝ a pair");
    CHECK(rd(RD_PUBLISH, 0) - p0 >= 1, "publication through the ordinary protocol");
    res = whnf(mk_fst(call), fc_true(), &st);
    CHECK(st == W_OK && res.cls == R_NEUTRAL, "its first component m(b,c) is neutral");
    RefId path = mk_snd(mk_snd(call));
    res = whnf(path, fc_true(), &st);
    CHECK(st == W_OK && head_tag(res) == T_PLAM, "the output path is a path lambda");
    DimVarId j = declare_dim();
    res = whnf(mk_papp_const(0, A.X, A.rhs, A.rhs, path, iv_var(j)), fc_lit(j, 1), &st);
    CHECK(st == W_OK, "the path at j=1 observes (status %d)", (int)st);
    uint64_t l4 = rd(RD_LAUNCH, 0); (void)whnf(call, fc_true(), &st);
    CHECK(rd(RD_LAUNCH, 0) == l4, "a repeated identical call launches no producer");
    RefId rcall = assoc_call(&A, DIR_REVERSE, sigma, assoc_right_arg(&A, sigma));
    CHECK(check(A.G, fc_true(), rcall, reindex(A.domain, sigma), &why) == CK_VALID, "G[σ](r_R) : R_L[σ] (%s)", why);
    res = whnf(mk_fst(rcall), fc_true(), &st);
    CHECK(st == W_OK && res.cls == R_NEUTRAL, "the reverse call's first component m(a,b) is neutral");
    /* the inverse proofs at the call's data */
    RefId Ms = reindex(A.T, sigma), RLs = reindex(A.domain, sigma);
    RefId gfr = maps_apply(Ms, DIR_REVERSE, maps_apply(Ms, DIR_FORWARD, r));
    CHECK(check(A.G, fc_true(), mk_app(maps_h(Ms), r), mk_path_const(0, RLs, gfr, r), &why) == CK_VALID, "h r : G(F r) = r (%s)", why);

    /* ---- dimension substitution and a strengthened face ---- */
    { DimVarId k = declare_dim();
      RefId yk = mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_var(k));
      MapId sk = assoc_sigma(&A, yk);
      DimVarId i2 = declare_dim();
      RefId w = mk_plam(i2, mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_meet(iv_var(i2), iv_var(k))));
      RefId RLk = reindex(A.domain, sk);
      RefId rk = mk_pair_at_lv(0, RLk, A.mab, mk_pair_at_lv(0, apply_term_binder(RLk, 0, 1, A.mab), mk_refl(0, A.X, A.mab), w));
      RefId callk = assoc_call(&A, DIR_FORWARD, sk, rk);
      CHECK(check(context_extend_dim(A.G, k), fc_true(), callk, reindex(A.codomain, sk), &why) == CK_VALID, "a call whose boundary depends on k checks (%s)", why);
      RefId at0 = reindex_dim(callk, k, iv_zero());
      CHECK(set_contains(ref_support(callk), k) && !set_contains(ref_support(at0), k), "the call's support follows its boundary");
      DimVarId z = declare_dim();
      (void)whnf(callk, fc_true(), &st);
      size_t n0 = whnf_keys(); (void)whnf(callk, fc_lit(z, 1), &st);
      CHECK(whnf_keys() == n0, "a face on an unrelated dimension projects away (no new key)");
      n0 = whnf_keys(); (void)whnf(callk, fc_lit(k, 0), &st);
      CHECK(st == W_OK && whnf_keys() > n0, "a face on the call's own dimension is a different key"); }

    /* ---- a higher path in the evidence ---- */
    { RefId Pt = mk_path_const(0, A.X, A.lhs, A.rhs);
      DimVarId i = declare_dim();
      RefId Hi = mk_papp_const(0, Pt, A.alpha, A.alpha, mk_refl(0, Pt, A.alpha), iv_var(i));
      RefId Ti = mk_app(mk_app(mk_app(mk_app(mk_app(id_action(0, 0, 0), A.X), A.L), A.R), Hi), A.rhs);
      RefId out = mk_plam(i, maps_apply(Ti, DIR_FORWARD, r));
      CheckStatus hs = check(A.G, fc_true(), out, mk_path_const(0, reindex(A.codomain, sigma), call, call), &why);
      CHECK(hs == CK_VALID, "⟨i⟩ F_{H@i}(r) : Path(F_α r, F_α r) (%s: %s)", check_status_name(hs), why); }


    /* ---- the empty diagram; a tail depending on its witness ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vo = tv(B); RefId o = ref_var(vo);
      CtxDecl d[2] = { { S_TERM, vB}, { S_TERM, vo} }; ContextId G = context_make(2, d, fc_true());
      uint64_t lr; RefId E = diagram_fold(0, NULL, B, 0, o, &lr);
      CHECK(lr == 0 && check(G, fc_true(), E, diagram_type(0, 0, B), &why) == CK_VALID, "the empty diagram is zero (%s)", why);
      CHECK(convert_term(G, fc_true(), dg_C(E), o, B) == CV_EQUAL, "C = o"); }
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      TermVarId vf = tv(mk_fun(0, 0, X, X)), vg = tv(mk_fun(0, 0, X, mk_fun(0, 0, X, X))), vx = tv(X);
      RefId f = ref_var(vf), g = ref_var(vg), x = ref_var(vx), fx = mk_app(f, x);
      CtxDecl d[4] = { { S_TERM, vX}, { S_TERM, vf}, { S_TERM, vg}, { S_TERM, vx} };
      ContextId G = context_make(4, d, fc_true());
      TermVarId vu = tv(X); RefId Ps = mk_path_const(0, X, fx, ref_var(vu)); TermVarId vs = tv(Ps);
      RefId A1 = mk_path_const(0, Ps, ref_var(vs), ref_var(vs));
      TermVarId vp = tv(A1); TermVarId vq = tv(mk_path_const(0, A1, mk_refl(0, Ps, ref_var(vs)), ref_var(vp)));
      DiagNode nodes[2] = { { vu, vs, X, 0, fx }, { vp, vq, A1, 0, mk_refl(0, Ps, ref_var(vs)) } };
      uint64_t lr; RefId D2 = diagram_fold(2, nodes, X, 0, m2(g, ref_var(vu), ref_var(vu)), &lr);
      CHECK(check(G, fc_true(), D2, diagram_type(0, lr, X), &why) == CK_VALID, "a second node depending on the first witness (%s)", why);
      CHECK(convert_term(G, fc_true(), dg_C(D2), m2(g, fx, fx), X) == CV_EQUAL, "C ≡ g(f x)(f x)");
      CHECK(!set_contains(ref_freevars(D2), vs) && !set_contains(ref_freevars(D2), vu), "node variables are bound in the fold"); }

    /* ---- rejections ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      TermVarId vm = tv(mk_fun(0, 0, X, mk_fun(0, 0, X, X))), va = tv(X), vb = tv(X);
      RefId m = ref_var(vm), a = ref_var(va), b = ref_var(vb), mab = m2(m, a, b);
      CtxDecl d[4] = { { S_TERM, vX}, { S_TERM, vm}, { S_TERM, va}, { S_TERM, vb} };
      ContextId G = context_make(4, d, fc_true());
      TermVarId vu = tv(U0), vs = tv(mk_path_const(1, U0, a, ref_var(vu)));
      DiagNode bad = { vu, vs, U0, 1, a };
      uint64_t lr; RefId Lb = diagram_fold(1, &bad, X, 0, mab, &lr);
      CHECK(check(G, fc_true(), Lb, diagram_type(0, lr, X), &why) == CK_INVALID, "a node whose term is not of its type is rejected (%s)", why);
      TermVarId vw = tv(mk_path_const(0, X, mab, mab));
      TermVarId vy2 = tv(X);
      ContextId Gw = context_extend_term(context_extend_term(G, vw), vy2);
      RefId Ld = diagram_fold(0, NULL, X, 0, a, &lr), Rd = diagram_fold(0, NULL, X, 0, b, &lr);
      RefId Tw = mk_app(mk_app(mk_app(mk_app(mk_app(id_action(0, 0, 0), X), Ld), Rd), ref_var(vw)), ref_var(vy2));
      CHECK(check(Gw, fc_true(), Tw, maps_type(0, 0, mk_path_const(0, X, a, ref_var(vy2)), mk_path_const(0, X, b, ref_var(vy2))), &why) == CK_INVALID, "evidence with the wrong endpoints is rejected (%s)", why); }

    /* ---- CUT_TO_PATH: the residual is retained ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vC = tv(B), vD = tv(B); RefId C = ref_var(vC), D = ref_var(vD);
      TermVarId vz = tv(B); RefId z = ref_var(vz);
      TermVarId vu = tv(mk_path_const(0, B, C, z)), vv = tv(mk_path_const(0, B, D, z));
      CtxDecl d[6] = { { S_TERM, vB}, { S_TERM, vC}, { S_TERM, vD}, { S_TERM, vz}, { S_TERM, vu}, { S_TERM, vv} };
      ContextId G = context_make(6, d, fc_true());
      RefId M = app3(cut_maps(0), B, C, D);
      Inference I = infer(G, fc_true(), M);
      CHECK(I.st == CK_VALID, "cut_maps(B, C, D) is typed (%s)", I.reason ? I.reason : "");
      RefId Cut = mk_sigma_lv(0, 0, vz, B, mk_sigma_lv(0, 0, vu, mk_path_const(0, B, C, z), mk_path_const(0, B, D, z)));
      RefId w = mk_pair_at_lv(0, Cut, z, mk_pair_at_lv(0, apply_term_binder(Cut, 0, 1, z), ref_var(vu), ref_var(vv)));
      RefId cc = maps_apply(M, DIR_FORWARD, w);
      CHECK(check(G, fc_true(), cc, mk_path_const(0, B, C, D), &why) == CK_VALID, "(z,u,v) ↦ u·v⁻¹ : C = D (%s)", why);
      res = whnf(cc, fc_true(), &st);
      CHECK(st == W_OK && head_tag(res) == T_PLAM, "u·v⁻¹ is a path");
      TermVarId vp = tv(mk_path_const(0, B, C, D)); RefId p = ref_var(vp);
      ContextId Gp = context_extend_term(G, vp);
      RefId loop = mk_path_concat(0, B, D, C, D, mk_path_rev(0, B, C, D, p), cc);
      CHECK(convert_term(Gp, fc_true(), loop, mk_refl(0, B, D), mk_path_const(0, B, D, D)) != CV_EQUAL, "the residual loop is not definitionally refl");
      res = whnf(mk_fst(maps_apply(M, DIR_REVERSE, p)), fc_true(), &st);
      CHECK(st == W_OK && res.ref == D, "h ↦ (D, h, refl D) has first component D"); }

    /* ---- COLLAPSE_FIBRE; equivalences ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vR = tv(mk_fun(0, 1, B, U0)); RefId R = ref_var(vR);
      TermVarId xb = tv(B);
      RefId Kt = mk_pi_lv(0, 0, xb, B, mk_contr(0, mk_app(R, ref_var(xb))));
      TermVarId vk = tv(Kt), vb = tv(B);
      CtxDecl d[4] = { { S_TERM, vB}, { S_TERM, vR}, { S_TERM, vk}, { S_TERM, vb} };
      ContextId G = context_make(4, d, fc_true());
      RefId M = app3(fibre_maps(0, 0), B, R, ref_var(vk));
      CHECK(infer(G, fc_true(), M).st == CK_VALID, "fibre_maps(B, R, k) is typed");
      res = whnf(maps_apply(M, DIR_FORWARD, maps_apply(M, DIR_REVERSE, ref_var(vb))), fc_true(), &st);
      CHECK(st == W_OK && res.ref == ref_var(vb), "projection ∘ section ⇝ b");
      TermVarId vk2 = tv(mk_fun(0, 0, B, B));
      CHECK(infer(context_extend_term(G, vk2), fc_true(), app3(fibre_maps(0, 0), B, R, ref_var(vk2))).st == CK_INVALID, "a non-contraction is rejected"); }
    { TermVarId vX = tv(U0), vY = tv(U0); RefId X = ref_var(vX), Y = ref_var(vY);
      TermVarId ve = tv(mk_equiv(0, 0, X, Y)), vx = tv(X);
      CtxDecl d[4] = { { S_TERM, vX}, { S_TERM, vY}, { S_TERM, ve}, { S_TERM, vx} };
      ContextId G = context_make(4, d, fc_true());
      RefId M = app3(equiv_maps(0, 0), X, Y, ref_var(ve));
      RefId fw = maps_apply(M, DIR_FORWARD, ref_var(vx));
      CHECK(check(G, fc_true(), maps_apply(M, DIR_REVERSE, fw), X, &why) == CK_VALID, "reverse(forward(x)) : X (%s)", why);
      CHECK(check(G, fc_true(), M, maps_type(0, 0, X, Y), &why) == CK_VALID, "equiv_maps(X, Y, e) : Maps(X, Y) (%s)", why);
      RefId I = app3(equiv_maps(0, 0), X, X, mk_id_equiv(0, X));
      res = whnf(maps_apply(I, DIR_REVERSE, ref_var(vx)), fc_true(), &st);
      CHECK(st == W_OK && res.ref == ref_var(vx), "reverse of IdEquiv at x ⇝ x");
      /* residual: two one-node descriptions ending in X and Y, acted on by e */
      TermVarId vf = tv(mk_fun(0, 0, X, X)), vg = tv(mk_fun(0, 0, Y, Y)), vy0 = tv(Y);
      ContextId G2 = context_extend_term(context_extend_term(context_extend_term(G, vf), vg), vy0);
      RefId fx = mk_app(ref_var(vf), ref_var(vx)), gy = mk_app(ref_var(vg), ref_var(vy0));
      TermVarId vu = tv(X), vs = tv(mk_path_const(0, X, fx, ref_var(vu))), vv = tv(Y), vt = tv(mk_path_const(0, Y, gy, ref_var(vv)));
      DiagNode ln = { vu, vs, X, 0, fx }, rn = { vv, vt, Y, 0, gy };
      uint64_t rl, rr; RefId PL = residual_fold(1, &ln, X, 0, &rl), PR = residual_fold(1, &rn, Y, 0, &rr);
      CHECK(check(G2, fc_true(), PL, res_type(0, rl), &why) == CK_VALID, "a residual description : Res(X) (%s)", why);
      RefId MR = app3(res_action(0, rl, 0, rr), PL, PR, M);
      CHECK(check(G2, fc_true(), MR, maps_type(rl, rr, res_X(PL), res_X(PR)), &why) == CK_VALID, "the residual action along e (%s)", why); }

    /* ---- a cyclic argument stays unresolved; its proof use is PENDING ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      CtxDecl d[1] = { { S_TERM, vX} }; ContextId G = context_make(1, d, fc_true());
      uint64_t px[1] = { vX };
      SymbolId loopx = define_global("loop_x", set_make(px, 1), set_make(NULL, 0), X);
      set_global_body(loopx, global_ref(loopx));
      RefId c2 = maps_apply(app3(equiv_maps(0, 0), X, X, mk_id_equiv(0, X)), DIR_FORWARD, global_ref(loopx));
      CHECK(check(G, fc_true(), c2, X, &why) == CK_VALID, "the call at the cyclic argument is well typed (%s)", why);
      res = whnf(c2, fc_true(), &st);
      CHECK(st == W_STUCK && res.cls == 0, "a demand unfolding the cyclic argument stays unresolved (status %d)", (int)st);
      ProofUse u = proof_use(G, fc_true(), c2, X); CHECK(u.status == PU_PENDING, "its proof use is PENDING (%s)", proof_status_name(u.status)); proof_use_free(&u);
      RefId cl = assoc_call(&A, DIR_FORWARD, sigma, r);
      res = whnf(cl, fc_true(), &st);
      CHECK(st == W_OK && head_tag(res) == T_PAIR, "unrelated cycles do not affect the action");
      eval_run(); }

    printf("  %d passed, %d failed\n", np, nf);
    check_free(); machine_free();
    return nf ? 1 : 0;
}

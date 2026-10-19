/* §47 verification of the identity compiler (§39–§46) as the input adapter of
 * PLAN §9.3: declarations export ordinary diagram values and actions. */
#define _POSIX_C_SOURCE 200809L
#include "assoc.h"
#include "../src/net.h"

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }
static Tag head_tag(const EvalResult *r) { if (!r || ref_is_var(r->ref)) return 0; return ref_tag(r->ref); }

int main(void) {
    printf("== §39–48 identity compiler\n");
    machine_init(); eval_init(); check_init(); compiler_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *why = "";
    RefId U0 = mk_universe(0);

    /* ---- 3. the complete associativity declaration, both orientations ---- */
    Assoc A; assoc_build(&A, &why);
    CHECK(A.ok, "associativity compiles (%s)", why);
    if (A.ok) {
        const Action *t = &A.T;
        CHECK(t->kind == EV_IDENTITY && t->maps && t->applied, "the action is an ordinary value");
        { ProofUse u = action_proof_use(t); CHECK(u.status == PU_CORE, "the action is established core evidence relative to its context (%s)", proof_status_name(u.status)); proof_use_free(&u); }
        /* the exported collapse computes the transport of w = snd(snd r) to a path */
        TermVarId rL; RefId cL = diagram_collapse(A.L, &rL);
        WhnfStatus st; EvalResult *res = whnf(cL, fc_true(), &st);
        CHECK(st == W_OK && head_tag(res) == T_PLAM, "c_L(r) computes to a path");
        /* the expansion is (m(b,c), refl, q) */
        TermVarId qR; RefId dR = diagram_expand(A.R, &qR);
        res = whnf(dR, fc_true(), &st);
        CHECK(st == W_OK && head_tag(res) == T_PAIR, "d_R(q) is a pair");
        res = whnf(mk_fst(dR), fc_true(), &st);
        CHECK(st == W_OK && res->ref == A.mbc, "its first component is m(b,c)");

        /* forward invocation: σ with y := m(a, m(b,c)); r_L = (m(a,b), refl, α) */
        MapId sigma = assoc_sigma(&A, A.rhs);
        RefId r = assoc_left_arg(&A, sigma);
        CHECK(check(A.G, fc_true(), r, reindex(t->domain, sigma), &why) == CK_VALID, "r_L : R_L[σ] (%s)", why);
        RefId call = action_call(t, DIR_FORWARD, sigma, r);
        CHECK(check(A.G, fc_true(), call, reindex(t->codomain, sigma), &why) == CK_VALID, "F(assoc)[σ](r) : R_R[σ] (%s)", why);
        Inference I = infer(A.G, fc_true(), call);
        CHECK(I.st == CK_VALID && convert_type(A.G, fc_true(), I.type, reindex(t->codomain, sigma)) == CV_EQUAL, "the call infers the codomain");
        /* execution (§46): the pair is exposed without evaluating its path */
        EvalNetEvents n0 = eval_net_events(); EvalEvents e0 = eval_events();
        res = whnf(call, fc_true(), &st);
        EvalNetEvents n1 = eval_net_events(); EvalEvents e1 = eval_events();
        CHECK(st == W_OK && res->cls == R_INTRODUCTION && head_tag(res) == T_PAIR, "forward call ⇝ a pair");
        CHECK(n1.continue_ref == n0.continue_ref, "ordinary application: no instruction, no receiver event");
        CHECK(e1.publish - e0.publish >= 1, "publication through the ordinary protocol");
        res = whnf(mk_fst(call), fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_NEUTRAL, "fst of the result observes m(b,c), a neutral");
        RefId path = mk_snd(mk_snd(call));
        res = whnf(path, fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_INTRODUCTION && head_tag(res) == T_PLAM, "the output path is a path lambda");
        DimVarId j = declare_dim();
        EvalEvents e2 = eval_events();
        res = whnf(mk_papp_const(0, A.X, A.rhs, A.rhs, path, iv_var(j)), fc_lit(j, 1), &st);
        EvalEvents e3 = eval_events();
        CHECK(st == W_OK, "the path at j=1 observes (status %d)", (int)st);
        CHECK(e3.eval_step > e2.eval_step, "its demand counts as ordinary evaluation work");
        EvalEvents e4 = eval_events();
        (void)whnf(call, fc_true(), &st);
        EvalEvents e5 = eval_events();
        CHECK(e5.launch == e4.launch, "a repeated identical call launches no producer");

        /* reverse orientation */
        RefId rr = assoc_right_arg(&A, sigma);
        RefId rcall = action_call(t, DIR_REVERSE, sigma, rr);
        CHECK(check(A.G, fc_true(), rcall, reindex(t->domain, sigma), &why) == CK_VALID, "G(assoc)[σ](r_R) : R_L[σ] (%s)", why);
        res = whnf(rcall, fc_true(), &st);
        CHECK(st == W_OK && head_tag(res) == T_PAIR, "reverse call ⇝ a pair");
        res = whnf(mk_fst(rcall), fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_NEUTRAL, "its first component is m(a,b)");

        /* ---- 5. dimension substitution and a strengthened face ---- */
        { DimVarId k = declare_dim();
          RefId yk = mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_var(k));
          MapId sk = assoc_sigma(&A, yk);
          DimVarId i2 = declare_dim();
          RefId w = mk_plam(i2, mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_meet(iv_var(i2), iv_var(k))));
          RefId RLk = reindex(t->domain, sk);
          RefId rk = mk_pair_at_lv(0, RLk, A.mab, mk_pair_at_lv(0, apply_term_binder(RLk, 0, 1, A.mab), mk_refl(0, A.X, A.mab), w));
          RefId callk = action_call(t, DIR_FORWARD, sk, rk);
          ContextId Gk = context_extend_dim(A.G, k);
          CHECK(check(Gk, fc_true(), callk, reindex(t->codomain, sk), &why) == CK_VALID, "a call whose boundary depends on k checks (%s)", why);
          /* reindexing the complete call is the call at the reindexed data */
          RefId at0 = reindex_dim(callk, k, iv_zero());
          MapId sk0 = assoc_sigma(&A, reindex_dim(yk, k, iv_zero()));
          { Head ho; open_ref(at0, &ho);
            CHECK(ho.tag == T_APP && HF(&ho, 0).id == reindex(action_function(t, DIR_FORWARD), sk0) && HF(&ho, 1).id == reindex_dim(rk, k, iv_zero()),
                  "opening reindex(call, k↦0) gives the forward map at σ;[k↦0] applied to a[k↦0]");
            head_free(&ho); }
          CHECK(dimset_contains(ref_support(callk), k) && !dimset_contains(ref_support(at0), k), "the call's support follows its boundary");
          DimVarId z = declare_dim();
          (void)whnf(callk, fc_lit(z, 1), &st);
          CHECK(eval_entry_lookup(callk, fc_true()) == eval_entry_lookup(callk, fc_lit(z, 1)) && eval_entry_lookup(callk, fc_true()) != 0, "the observation key is the call's support projection");
          (void)whnf(callk, fc_lit(k, 0), &st);
          CHECK(st == W_OK && eval_entry_lookup(callk, fc_lit(k, 0)) != eval_entry_lookup(callk, fc_true()), "a face on the call's own dimension is a different key"); }

        /* ---- 7. a higher path in the evidence parameter of the generic action ---- */
        { RefId Pt = mk_path_const(0, A.X, A.lhs, A.rhs);
          RefId H = mk_refl(0, Pt, A.alpha);
          DimVarId i = declare_dim();
          RefId Hi = mk_papp_const(0, Pt, A.alpha, A.alpha, H, iv_var(i));
          RefId args[5] = { A.X, diagram_value(A.L), diagram_value(A.R), Hi, A.rhs };
          RefId Fi = mk_app(rt_c(rt_inst(rt_recipe(RK_ACTION, 0, 0, 0, 0), args)), r);
          RefId out = mk_plam(i, Fi);
          RefId Fa = call;
          CheckStatus hs = check(A.G, fc_true(), out, mk_path_const(0, reindex(t->codomain, sigma), Fa, Fa), &why);
          CHECK(hs == CK_VALID, "⟨i⟩ F_{H@i}(r) : Path_{R_R}(F_α r, F_α r) (%s: %s)", check_status_name(hs), why); }

        /* ---- the call in a net: an EVAL consumer of REF(call) ---- */
        { Net net; net_init(&net);
          int8_t pneg[1] = { -1 }; Payload P = {0};
          NodeId root = net_node(&net, A_ROOT, 1, pneg, P);
          NodeId ev = net_operation(&net, OP_EVAL, (Payload){ .face = fc_true() });
          Payload Pr = {0}; Pr.ref = call;
          net_connect(&net, ev, 1, root, 0);
          net_connect(&net, ev, 0, net_descriptor(&net, D_REF, Pr), 0);
          net_run_with_eval(&net);
          NodeKind kk = 0; Payload outp;
          bool ok = net_root_read(&net, root, &kk, &outp);
          CHECK(ok && kk == D_EVAL_RESULT && ((EvalResult *)(uintptr_t)outp.a)->cls == R_INTRODUCTION, "an EVAL consumer of the call yields the pair at the root");
          net_free(&net); }
    }

    /* ---- 1. the empty diagram ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vo = tv(B); RefId o = ref_var(vo);
      CtxDecl d[2] = { { S_TERM, vB, U0 }, { S_TERM, vo, B } }; ContextId G = context_make(2, d, fc_true());
      DiagramId E = diagram_declare(G, 0, NULL, B, 0, o);
      CHECK(diagram_validate(E, fc_true(), &why) == CK_VALID, "empty diagram validates (%s)", why);
      TermVarId rs, qs; RefId c = diagram_collapse(E, &rs), x = diagram_expand(E, &qs);
      ContextId Gy = context_extend_term(G, diagram_output_param(E), B);
      ContextId Gr = context_extend_term(Gy, rs, term_var_type(rs)), Gq = context_extend_term(Gy, qs, term_var_type(qs));
      CHECK(convert_term(Gr, fc_true(), c, ref_var(rs), term_var_type(rs)) == CV_EQUAL && convert_term(Gq, fc_true(), x, ref_var(qs), term_var_type(qs)) == CV_EQUAL, "collapse and expand of zero are the identity on the output path type");
      CHECK(diagram_realization(E) == mk_path_const(0, B, o, ref_var(diagram_output_param(E))), "Real = Path_B(o, y)");
      CHECK(diagram_canonical(E) == o, "C = o"); }

    /* ---- 2 and 4. a tail depending on its witness; a shared predecessor ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      TermVarId vf = tv(mk_fun(0, 0, X, X)), vg = tv(mk_fun(0, 0, X, mk_fun(0, 0, X, X))), vx = tv(X);
      RefId f = ref_var(vf), g = ref_var(vg), x = ref_var(vx);
      CtxDecl d[4] = { { S_TERM, vX, U0 }, { S_TERM, vf, term_var_type(vf) }, { S_TERM, vg, term_var_type(vg) }, { S_TERM, vx, X } };
      ContextId G = context_make(4, d, fc_true());
      RefId fx = mk_app(f, x);
      /* node 0: u = f x, s : f x = u ; node 1: p = refl s : Path_{Path X (f x) u}(s, s) — its type depends on the witness */
      TermVarId vu = tv(X); TermVarId vs = tv(mk_path_const(0, X, fx, ref_var(vu)));
      RefId Ps = mk_path_const(0, X, fx, ref_var(vu));
      RefId A1 = mk_path_const(0, Ps, ref_var(vs), ref_var(vs));
      TermVarId vp = tv(A1); TermVarId vq = tv(mk_path_const(0, A1, mk_refl(0, Ps, ref_var(vs)), ref_var(vp)));
      DiagNode nodes[2] = { { 1, vu, vs, X, 0, fx }, { 2, vp, vq, A1, 0, mk_refl(0, Ps, ref_var(vs)) } };
      DiagramId D2 = diagram_declare(G, 2, nodes, X, 0, m2(g, ref_var(vu), ref_var(vu)));
      CHECK(diagram_validate(D2, fc_true(), &why) == CK_VALID, "a diagram whose second node depends on the first witness validates (%s)", why);
      TermVarId rs; RefId c = diagram_collapse(D2, &rs);
      CHECK(!varset_contains(ref_freevars(c), vs) && !varset_contains(ref_freevars(c), vu) && !varset_contains(ref_freevars(c), vp), "the emitted collapse substitutes x and e of every block (no node variable is free)");
      { WhnfStatus st; EvalResult *r2 = whnf(c, fc_true(), &st);
        CHECK(st == W_OK && head_tag(r2) == T_PLAM, "collapse of two blocks computes to a path"); }
      { RefId C = diagram_canonical(D2);
        CHECK(convert_term(G, fc_true(), C, m2(g, fx, fx), X) == CV_EQUAL, "C ≡ g(f x)(f x)");
        size_t nfx = 0, nother = 0; TEnvId E = tenv_of(C);
        for (size_t q = 0; q < tenv_size(E); q++) { uint64_t sl; TVal v; tenv_entry(E, q, &sl, &v); if (v.sort != PS_REF) continue; if (v.id == fx) nfx++; else if (!ref_is_var(v.id)) nother++; }
        CHECK(!ref_is_var(C) && nfx == 1 && nother == 0, "C = (g u u)[u ↦ f x]: one shared image, the DAG is not expanded"); }
      /* shared predecessor: one block, identical repeated images in the collapse family */
      TermVarId vu2 = tv(X); TermVarId vs2 = tv(mk_path_const(0, X, fx, ref_var(vu2)));
      DiagNode one = { 1, vu2, vs2, X, 0, fx };
      DiagramId Dsh = diagram_declare(G, 1, &one, X, 0, m2(g, ref_var(vu2), ref_var(vu2)));
      CHECK(diagram_validate(Dsh, fc_true(), &why) == CK_VALID, "shared-predecessor diagram validates (%s)", why);
      RefId csh = diagram_collapse(Dsh, &rs);
      ContextId Gs = context_extend_term(context_extend_term(G, diagram_output_param(Dsh), X), rs, diagram_realization(Dsh));
      CHECK(check(Gs, fc_true(), csh, mk_path_const(0, X, diagram_canonical(Dsh), ref_var(diagram_output_param(Dsh))), &why) == CK_VALID, "the shared-predecessor collapse checks (%s)", why); }

    /* ---- 6. rejections ---- */
    { RefId U = U0; Action act;
      TermVarId vX = tv(U); RefId X = ref_var(vX);
      TermVarId vm = tv(mk_fun(0, 0, X, mk_fun(0, 0, X, X))), va = tv(X), vb = tv(X), vc = tv(X);
      RefId m = ref_var(vm), a = ref_var(va), b = ref_var(vb), c = ref_var(vc);
      RefId mab = m2(m, a, b), mbc = m2(m, b, c);
      /* wrong endpoints: evidence m(a,b)=m(a,b) instead of the canonical values */
      TermVarId vbad = tv(mk_path_const(0, X, mab, mab));
      CtxDecl d[6] = { { S_TERM, vX, U }, { S_TERM, vm, term_var_type(vm) }, { S_TERM, va, X }, { S_TERM, vb, X }, { S_TERM, vc, X }, { S_TERM, vbad, term_var_type(vbad) } };
      ContextId G = context_make(6, d, fc_true());
      TermVarId vu = tv(X), vs = tv(mk_path_const(0, X, mab, ref_var(vu)));
      DiagNode ln = { 1, vu, vs, X, 0, mab };
      DiagramId L = diagram_declare(G, 1, &ln, X, 0, m2(m, ref_var(vu), c));
      TermVarId vv = tv(X), vt = tv(mk_path_const(0, X, mbc, ref_var(vv)));
      DiagNode rn = { 2, vv, vt, X, 0, mbc };
      DiagramId R = diagram_declare(G, 1, &rn, X, 0, m2(m, a, ref_var(vv)));
      IdentityDecl bad = { 7, G, fc_true(), X, 0, L, R, ref_var(vbad) };
      CHECK(compile_identity(&bad, &act, &why) == CK_INVALID, "wrong evidence endpoints are rejected (%s)", why);
      /* bad node type: t = a at node type U */
      TermVarId vu3 = tv(U), vs3 = tv(mk_path_const(1, U, a, ref_var(vu3)));
      DiagNode badn = { 1, vu3, vs3, U, 1, a };
      DiagramId Lb = diagram_declare(G, 1, &badn, X, 0, m2(m, a, c));
      CHECK(diagram_validate(Lb, fc_true(), &why) == CK_INVALID, "a node whose term is not of its type is rejected");
      /* unmet face: the evidence is a variable only available on (k=1) while the declaration requires ⊤ */
      DimVarId k = declare_dim();
      TermVarId vp = declare_term(mk_path_const(0, X, m2(m, mab, c), m2(m, a, mbc)), fc_lit(k, 1));
      CtxDecl d2[7] = { { S_DIM, k, 0 }, { S_TERM, vX, U }, { S_TERM, vm, term_var_type(vm) }, { S_TERM, va, X }, { S_TERM, vb, X }, { S_TERM, vc, X }, { S_TERM, vp, term_var_type(vp) } };
      ContextId G2 = context_make(7, d2, fc_true());
      TermVarId vu4 = tv(X), vs4 = tv(mk_path_const(0, X, mab, ref_var(vu4)));
      DiagNode ln2 = { 1, vu4, vs4, X, 0, mab };
      DiagramId L2 = diagram_declare(G2, 1, &ln2, X, 0, m2(m, ref_var(vu4), c));
      TermVarId vv4 = tv(X), vt4 = tv(mk_path_const(0, X, mbc, ref_var(vv4)));
      DiagNode rn2 = { 2, vv4, vt4, X, 0, mbc };
      DiagramId R2 = diagram_declare(G2, 1, &rn2, X, 0, m2(m, a, ref_var(vv4)));
      IdentityDecl unmet = { 8, G2, fc_true(), X, 0, L2, R2, ref_var(vp) };
      CHECK(compile_identity(&unmet, &act, &why) == CK_INVALID, "evidence outside the required face is rejected (%s)", why);
      IdentityDecl met = { 9, G2, fc_lit(k, 1), X, 0, L2, R2, ref_var(vp) };
      CheckStatus tm = compile_identity(&met, &act, &why);
      CHECK(tm == CK_VALID, "the same declaration under the face (k=1) compiles (%s)", why);
      if (tm == CK_VALID) CHECK(fc_entails(fc_lit(k, 1), act.required_face) && !fc_entails(fc_true(), act.required_face), "the action retains its required face");
      /* an exhausted budget is no verdict */
      check_set_budget(5);
      IdentityDecl ok = { 10, G2, fc_lit(k, 1), X, 0, L2, R2, ref_var(vp) };
      CheckStatus tu = compile_identity(&ok, &act, &why);
      check_set_budget(0);
      CHECK(tu != CK_INVALID, "a budgeted compilation of a valid declaration is valid or unresolved, never invalid"); }

    /* ---- 8. cut followed by loop conversion: the residual is retained ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vC = tv(B), vD = tv(B); RefId C = ref_var(vC), D = ref_var(vD);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vC, B }, { S_TERM, vD, B } };
      ContextId G = context_make(3, d, fc_true());
      Action cutA; CheckStatus cs = compile_cut(G, fc_true(), B, 0, C, D, &cutA, &why);
      CHECK(cs == CK_VALID, "CUT_TO_PATH compiles (%s)", why);
      if (cs == CK_VALID) {
        const Action *t = &cutA, *cut = &cutA;
        { ProofUse u = action_proof_use(cut); CHECK(u.status == PU_CORE, "CUT_TO_PATH's generic construction is core (%s)", proof_status_name(u.status)); proof_use_free(&u); }
        /* a cut (z, u, v) with neutral data */
        TermVarId vz = tv(B); RefId z = ref_var(vz);
        TermVarId vu = tv(mk_path_const(0, B, C, z)), vv = tv(mk_path_const(0, B, D, z));
        ContextId Gz = context_extend_term(context_extend_term(context_extend_term(G, vz, B), vu, term_var_type(vu)), vv, term_var_type(vv));
        RefId Cut = t->domain;
        RefId w = mk_pair_at_lv(0, Cut, z, mk_pair_at_lv(0, apply_term_binder(Cut, 0, 1, z), ref_var(vu), ref_var(vv)));
        RefId call = action_call(cut, DIR_FORWARD, map_identity(), w);
        CHECK(check(Gz, fc_true(), call, mk_path_const(0, B, C, D), &why) == CK_VALID, "CUT_TO_PATH(z,u,v) : C = D (%s)", why);
        WhnfStatus st; EvalResult *r = whnf(call, fc_true(), &st);
        CHECK(st == W_OK && head_tag(r) == T_PLAM, "u·v⁻¹ is a path");
        /* given p : C = D, the loop p⁻¹·(u·v⁻¹) : D = D is not refl */
        TermVarId vp = tv(mk_path_const(0, B, C, D)); RefId p = ref_var(vp);
        ContextId Gp = context_extend_term(Gz, vp, term_var_type(vp));
        RefId loop = mk_path_concat(0, B, D, C, D, mk_path_rev(0, B, C, D, p), call);
        CHECK(check(Gp, fc_true(), loop, mk_path_const(0, B, D, D), &why) == CK_VALID, "the residual loop checks (%s)", why);
        ConvStatus cv = convert_term(Gp, fc_true(), loop, mk_refl(0, B, D), mk_path_const(0, B, D, D));
        CHECK(cv != CV_EQUAL, "the residual is retained: not definitionally refl (%s)", conv_status_name(cv));
        /* the reverse direction (h ↦ (D, h, refl D)) */
        RefId rcall = action_call(cut, DIR_REVERSE, map_identity(), p);
        CHECK(check(Gp, fc_true(), rcall, Cut, &why) == CK_VALID, "h ↦ (D, h, refl D) : Cut (%s)", why);
        r = whnf(mk_fst(rcall), fc_true(), &st);
        CHECK(st == W_OK && r->ref == D, "its first component is D"); } }

    /* ---- 8b. explicit levels; invocation is application of a field ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      CtxDecl d[1] = { { S_TERM, vX, U0 } }; ContextId G = context_make(1, d, fc_true());
      Action eq;
      CHECK(compile_equivalence(G, fc_true(), X, 1, X, 0, mk_id_equiv(0, X), &eq, &why) == CK_INVALID, "a wrong universe annotation is rejected (%s)", why);
      CheckStatus es = compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &eq, &why);
      CHECK(es == CK_VALID, "the correctly annotated equivalence compiles (%s)", why);
      if (es == CK_VALID) {
        CHECK(eq.domain_level == 0 && eq.codomain_level == 0, "the action stores the TypeAt levels");
        CHECK(action_function(&eq, DIR_FORWARD) != action_function(&eq, DIR_REVERSE), "the two orientations are two fields of one value");
        TermVarId vx = tv(X); RefId x = ref_var(vx);
        RefId direct = action_call(&eq, DIR_FORWARD, map_identity(), x);
        CHECK(direct == mk_app(action_function(&eq, DIR_FORWARD), x), "an invocation is an ordinary application");
        TermVarId vY = tv(U0); RefId Y = ref_var(vY); TermVarId vy = tv(Y); RefId y = ref_var(vy);
        MapBuilder sb; mapb_init(&sb); mapb_term(&sb, vX, Y); mapb_term(&sb, vx, y); MapId s = mapb_finish(&sb);
        CHECK(reindex(direct, s) == action_call(&eq, DIR_FORWARD, s, y), "reindexed and direct calls are one reference");
        CtxDecl d2[2] = { { S_TERM, vX, U0 }, { S_TERM, vx, X } }; ContextId Gx = context_make(2, d2, fc_true());
        CHECK(check(Gx, fc_true(), direct, X, &why) == CK_VALID, "the call checks at the codomain (%s)", why);
        CHECK(check(Gx, fc_true(), direct, mk_universe(0), &why) == CK_INVALID, "the call at another type is rejected (%s)", why); } }

    /* ---- 9. contractible-fibre projection and section ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vR = tv(mk_fun(0, 1, B, U0)); RefId R = ref_var(vR);
      TermVarId xb = tv(B);
      RefId Kt = mk_pi_lv(0, 0, xb, B, mk_contr(0, mk_app(R, ref_var(xb))));
      TermVarId vk = tv(Kt); RefId k = ref_var(vk);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vR, term_var_type(vR) }, { S_TERM, vk, Kt } };
      ContextId G = context_make(3, d, fc_true());
      Action cfA; CheckStatus cs = compile_contractible_fibre(G, fc_true(), B, 0, R, k, &cfA, &why);
      CHECK(cs == CK_VALID, "COLLAPSE_FIBRE compiles from k (%s)", why);
      if (cs == CK_VALID) {
        const Action *t = &cfA, *cf = &cfA;
        { ProofUse u = action_proof_use(cf); CHECK(u.status == PU_CORE, "COLLAPSE_FIBRE at a contraction variable is core (%s)", proof_status_name(u.status)); proof_use_free(&u); }
        TermVarId vb = tv(B);
        ContextId Gb = context_extend_term(G, vb, B);
        RefId sec = action_call(cf, DIR_REVERSE, map_identity(), ref_var(vb));
        CHECK(check(Gb, fc_true(), sec, t->domain, &why) == CK_VALID, "section b ↦ (b, fst(k b)) : Σ(b:B).R(b) (%s)", why);
        RefId back = action_call(cf, DIR_FORWARD, map_identity(), sec);
        WhnfStatus st; EvalResult *r = whnf(back, fc_true(), &st);
        CHECK(st == W_OK && r->cls == R_NEUTRAL && r->ref == ref_var(vb), "projection ∘ section ⇝ b");
        /* a non-contraction is rejected */
        TermVarId vk2 = tv(mk_fun(0, 0, B, B));
        CtxDecl d2[3] = { { S_TERM, vB, U0 }, { S_TERM, vR, term_var_type(vR) }, { S_TERM, vk2, term_var_type(vk2) } };
        ContextId G2 = context_make(3, d2, fc_true());
        Action bad; CHECK(compile_contractible_fibre(G2, fc_true(), B, 0, R, ref_var(vk2), &bad, &why) == CK_INVALID, "k that is not a pointwise contraction is rejected (%s)", why); } }

    /* ---- equivalence and residual equivalence (§44) ---- */
    { TermVarId vX = tv(U0), vY = tv(U0); RefId X = ref_var(vX), Y = ref_var(vY);
      TermVarId ve = tv(mk_equiv(0, 0, X, Y)); RefId e = ref_var(ve);
      CtxDecl d[3] = { { S_TERM, vX, U0 }, { S_TERM, vY, U0 }, { S_TERM, ve, term_var_type(ve) } };
      ContextId G = context_make(3, d, fc_true());
      Action eqA; CheckStatus es = compile_equivalence(G, fc_true(), X, 0, Y, 0, e, &eqA, &why);
      CHECK(es == CK_VALID, "a supplied equivalence compiles (%s)", why);
      if (es == CK_VALID) {
        const Action *eq = &eqA;
        { ProofUse u = action_proof_use(eq); CHECK(u.status == PU_CORE, "the equivalence action at a variable is core (%s)", proof_status_name(u.status)); proof_use_free(&u); }
        TermVarId vx = tv(X); ContextId Gx = context_extend_term(G, vx, X);
        RefId fw = action_call(eq, DIR_FORWARD, map_identity(), ref_var(vx));
        CHECK(check(Gx, fc_true(), fw, Y, &why) == CK_VALID, "forward(x) : Y (%s)", why);
        RefId bk = action_call(eq, DIR_REVERSE, map_identity(), fw);
        CHECK(check(Gx, fc_true(), bk, X, &why) == CK_VALID, "reverse(forward(x)) : X (%s)", why);
        /* the identity equivalence: forward reduces to the argument */
        Action ideq; CheckStatus is = compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &ideq, &why);
        CHECK(is == CK_VALID, "IdEquiv compiles as an equivalence (%s)", why);
        if (is == CK_VALID) { WhnfStatus st; EvalResult *r = whnf(action_call(&ideq, DIR_REVERSE, map_identity(), ref_var(vx)), fc_true(), &st);
                    CHECK(st == W_OK && r->ref == ref_var(vx), "reverse of IdEquiv at x ⇝ x"); } }
      /* residual: two one-block descriptions ending in X and Y, related by e */
      TermVarId vf = tv(mk_fun(0, 0, X, X)), vx0 = tv(X), vg = tv(mk_fun(0, 0, Y, Y)), vy0 = tv(Y);
      CtxDecl d2[7] = { { S_TERM, vX, U0 }, { S_TERM, vY, U0 }, { S_TERM, ve, term_var_type(ve) }, { S_TERM, vf, term_var_type(vf) }, { S_TERM, vx0, X }, { S_TERM, vg, term_var_type(vg) }, { S_TERM, vy0, Y } };
      ContextId G2 = context_make(7, d2, fc_true());
      TermVarId vu = tv(X), vs = tv(mk_path_const(0, X, mk_app(ref_var(vf), ref_var(vx0)), ref_var(vu)));
      DiagNode ln = { 1, vu, vs, X, 0, mk_app(ref_var(vf), ref_var(vx0)) };
      DiagramId L = residual_declare(G2, 1, &ln, X, 0);
      TermVarId vv = tv(Y), vt = tv(mk_path_const(0, Y, mk_app(ref_var(vg), ref_var(vy0)), ref_var(vv)));
      DiagNode rn = { 2, vv, vt, Y, 0, mk_app(ref_var(vg), ref_var(vy0)) };
      DiagramId R = residual_declare(G2, 1, &rn, Y, 0);
      Action resA; CheckStatus rs = compile_residual_equivalence(G2, fc_true(), L, R, e, &resA, &why);
      CHECK(rs == CK_VALID, "a residual equivalence compiles (%s)", why);
      if (rs == CK_VALID) {
        TermVarId vr = tv(resA.domain); ContextId Gr = context_extend_term(G2, vr, resA.domain);
        RefId fwr = action_call(&resA, DIR_FORWARD, map_identity(), ref_var(vr));
        CHECK(check(Gr, fc_true(), fwr, resA.codomain, &why) == CK_VALID, "the residual action's forward map checks (%s)", why);
        CHECK(check(Gr, fc_true(), action_call(&resA, DIR_REVERSE, map_identity(), fwr), resA.domain, &why) == CK_VALID, "and its reverse (%s)", why); } }

    /* ---- 11. recursive terms without an obtainable observation ---- */
    if (A.ok) {
        MapId sigma = assoc_sigma(&A, A.rhs);
        RefId RL = reindex(A.T.domain, sigma);
        uint64_t ps[6] = { A.vX, A.vm, A.va, A.vb, A.vc, A.valpha };
        SymbolId loop = define_global("loop_r", varset_make(ps, 6), dimset_make(NULL, 0), RL);
        set_global_body(loop, global_ref(loop));
        RefId call = action_call(&A.T, DIR_FORWARD, sigma, global_ref(loop));
        WhnfStatus st; EvalResult *r = whnf(call, fc_true(), &st);
        CHECK(st == W_OK && head_tag(r) == T_PAIR, "the pair is exposed without demanding the cyclic argument");
        TermVarId vX = tv(U0); RefId X = ref_var(vX);
        CtxDecl d[1] = { { S_TERM, vX, U0 } }; ContextId G = context_make(1, d, fc_true());
        uint64_t px[1] = { vX };
        SymbolId loopx = define_global("loop_x", varset_make(px, 1), dimset_make(NULL, 0), X);
        set_global_body(loopx, global_ref(loopx));
        Action ideq; CHECK(compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &ideq, &why) == CK_VALID, "IdEquiv (%s)", why);
        RefId call2 = action_call(&ideq, DIR_FORWARD, map_identity(), global_ref(loopx));
        CHECK(check(G, fc_true(), call2, X, &why) == CK_VALID, "the call at the cyclic argument is well typed (%s)", why);
        r = whnf(call2, fc_true(), &st);
        CHECK(st == W_STUCK && r == NULL, "a demand that unfolds the cyclic argument stays unresolved (status %d): nothing published, no synthesized success", (int)st);
        { ProofUse u = proof_use(G, fc_true(), call2, X); CHECK(u.status == PU_PENDING, "and its proof use is PENDING (%s)", proof_status_name(u.status)); proof_use_free(&u); }
        eval_run();
    }

    printf("  %d passed, %d failed\n", np, nf);
    compiler_free(); check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}

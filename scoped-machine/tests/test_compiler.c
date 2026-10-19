/* §47 verification of the identity compiler (§39–§46). */
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
    CHECK(A.T != 0, "associativity compiles (%s)", why);
    if (A.T) {
        const CompiledTransform *t = transform_get(A.T);
        CHECK(t->evidence_kind == EV_IDENTITY && t->forward_body && t->reverse_body, "compiled record published");
        CHECK(certificate_verify(A.T, &why) == CK_VALID, "IDENTITY certificate re-emits the same record (%s)", why);
        /* the emitted collapse is exactly coe^i Path_X(m(s@¬i, c), y) w */
        TermVarId rL; RefId cL = diagram_collapse(A.L, &rL);
        Head h; open_ref(cL, &h);
        CHECK(h.tag == T_COMP && fc_is_false(HF(&h, 1).id), "c_L is one composition with a false tube");
        if (h.tag == T_COMP) {
            DimOpen fam = resolve_dim_binder(cL, 0, 0);
            Head hf; open_ref(fam.body, &hf);
            CHECK(hf.tag == T_PATH, "its family is a path type");
            head_free(&hf);
            RefId cap = HF(&h, 3).id; Head hc; open_ref(cap, &hc);
            CHECK(hc.tag == T_SND, "its cap is w = snd(snd r)");
            head_free(&hc);
        }
        head_free(&h);
        /* the expansion is (m(b,c), refl, q) */
        TermVarId qR; RefId dR = diagram_expand(A.R, &qR);
        open_ref(dR, &h);
        CHECK(h.tag == T_PAIR && h.n == 3 && HF(&h, 0).id == A.mbc, "d_R(q) = (m(b,c), refl, q) with its Σ annotation");
        head_free(&h);

        /* forward invocation: σ with y := m(a, m(b,c)); r_L = (m(a,b), refl, α) */
        MapId sigma = assoc_sigma(&A, A.rhs);
        RefId r = assoc_left_arg(&A, sigma);
        CHECK(check(A.G, fc_true(), r, reindex(t->domain, sigma), &why) == CK_VALID, "r_L : R_L[σ] (%s)", why);
        RefId call = mk_transform_call(A.T, DIR_FORWARD, sigma, r);
        CHECK(check(A.G, fc_true(), call, reindex(t->codomain, sigma), &why) == CK_VALID, "TRANSFORM_CALL(assoc, FORWARD, σ, r) : R_R[σ] (%s)", why);
        Inference I = infer(A.G, fc_true(), call);
        CHECK(I.st == CK_VALID && I.type == reindex(t->codomain, sigma), "the call infers the output annotation");
        /* support invariant: S(instantiated body) ⊆ S(call) */
        { MapId tau = compose(sigma, map_single_term(t->forward_argument_slot, r)); (void)tau;
          MapBuilder b; mapb_init(&b); mapb_term(&b, t->forward_argument_slot, r);
          size_t nt = map_n_terms(sigma); for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(sigma, k, &x, &im); mapb_term(&b, x, im); }
          RefId v = reindex(t->forward_body, mapb_finish(&b));
          size_t ns; const uint64_t *S = dimset_get(ref_support(v), &ns);
          bool sub = true; for (size_t k = 0; k < ns; k++) if (!dimset_contains(ref_support(call), S[k])) sub = false;
          CHECK(sub, "S(instantiated body) ⊆ S(TRANSFORM_CALL)"); }
        /* execution (§46): the pair is exposed without evaluating its path */
        EvalNetEvents n0 = eval_net_events(); EvalEvents e0 = eval_events();
        WhnfStatus st; EvalResult *res = whnf(call, fc_true(), &st);
        EvalNetEvents n1 = eval_net_events(); EvalEvents e1 = eval_events();
        CHECK(st == W_OK && res->cls == R_INTRODUCTION && head_tag(res) == T_PAIR, "forward call ⇝ a pair");
        CHECK(n1.apply - n0.apply == 1 && n1.continue_ref - n0.continue_ref == 1, "one APPLY_TRANSFORM and one CONTINUE_REFERENCE rule event (%zu, %zu)", n1.apply - n0.apply, n1.continue_ref - n0.continue_ref);
        CHECK(e1.publish - e0.publish >= 1, "publication through the ordinary protocol");
        res = whnf(mk_fst(call), fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_NEUTRAL, "fst of the result observes m(b,c), a neutral");
        RefId path = mk_snd(mk_snd(call));
        res = whnf(path, fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_INTRODUCTION && head_tag(res) == T_PLAM, "the output path is a path lambda");
        /* demanding the path at a point runs α reversal, transport and concatenation */
        DimVarId j = declare_dim();
        EvalEvents e2 = eval_events();
        res = whnf(mk_papp_const(0, A.X, A.rhs, A.rhs, path, iv_var(j)), fc_lit(j, 1), &st);
        EvalEvents e3 = eval_events();
        CHECK(st == W_OK, "the path at j=1 observes (status %d)", (int)st);
        CHECK(e3.eval_step > e2.eval_step, "its demand counts as ordinary evaluation work");
        /* repeated identical demands share entries */
        EvalEvents e4 = eval_events();
        (void)whnf(call, fc_true(), &st);
        EvalEvents e5 = eval_events();
        CHECK(e5.launch == e4.launch, "a repeated identical call launches no producer");

        /* reverse orientation */
        RefId rr = assoc_right_arg(&A, sigma);
        RefId rcall = mk_transform_call(A.T, DIR_REVERSE, sigma, rr);
        CHECK(check(A.G, fc_true(), rcall, reindex(t->domain, sigma), &why) == CK_VALID, "TRANSFORM_CALL(assoc, REVERSE, σ, r_R) : R_L[σ] (%s)", why);
        res = whnf(rcall, fc_true(), &st);
        CHECK(st == W_OK && head_tag(res) == T_PAIR, "reverse call ⇝ a pair");
        res = whnf(mk_fst(rcall), fc_true(), &st);
        CHECK(st == W_OK && res->cls == R_NEUTRAL, "its first component is m(a,b)");

        /* ---- 5. dimension substitution and a strengthened face ---- */
        { DimVarId k = declare_dim();
          /* y depends on k through a path application: y_k = α@k ; r must then be at that y */
          RefId yk = mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_var(k));
          MapId sk = assoc_sigma(&A, yk);
          /* w : m(m(a,b),c) = α@k is ⟨i⟩ α@(i∧k) */
          DimVarId i2 = declare_dim();
          RefId w = mk_plam(i2, mk_papp_const(0, A.X, A.lhs, A.rhs, A.alpha, iv_meet(iv_var(i2), iv_var(k))));
          RefId RLk = reindex(t->domain, sk);
          RefId rk = mk_pair_at_lv(0, RLk, A.mab, mk_pair_at_lv(0, apply_term_binder(RLk, 0, 1, A.mab), mk_refl(0, A.X, A.mab), w));
          RefId callk = mk_transform_call(A.T, DIR_FORWARD, sk, rk);
          CtxDecl dk[1] = { { S_DIM, k, 0 } }; ContextId Gk = context_extend_dim(A.G, k); (void)dk;
          CHECK(check(Gk, fc_true(), callk, reindex(t->codomain, sk), &why) == CK_VALID, "a call whose boundary depends on k checks (%s)", why);
          /* reindexing the complete call commutes with invocation at the reindexed data */
          RefId at0 = reindex_dim(callk, k, iv_zero());
          { Head ho; open_ref(at0, &ho);
            uint64_t id2; int dir2; MapId s2; RefId a2;
            bool dec = compiler_decode_call(&ho, &id2, &dir2, &s2, &a2);
            bool same_sigma = dec;
            for (size_t q2 = 0; dec && q2 < context_size(t->parameters); q2++) { CtxDecl dd = context_decl(t->parameters, q2); if (dd.sort == S_TERM && map_term_image(s2, dd.id) != reindex_dim(map_term_image(sk, dd.id), k, iv_zero())) same_sigma = false; }
            CHECK(dec && id2 == A.T && dir2 == DIR_FORWARD && same_sigma && a2 == reindex_dim(rk, k, iv_zero()),
                  "opening reindex(TRANSFORM_CALL, k↦0) gives (id, dir, σ;[k↦0], a[k↦0])");
            size_t np2 = context_size(t->parameters);
            CHECK(dec && HF(&ho, np2 + 1).id == reindex_dim(reindex(t->domain, sk), k, iv_zero()) && HF(&ho, np2 + 2).id == reindex_dim(reindex(t->codomain, sk), k, iv_zero()), "and its annotations are the reindexed annotations");
            head_free(&ho); }
          CHECK(dimset_contains(ref_support(callk), k) && !dimset_contains(ref_support(at0), k), "the call's support follows its boundary");
          /* a strengthened face projects onto the call's support: the same key under ⊤ and under a face on an unrelated dimension */
          DimVarId z = declare_dim();
          (void)whnf(callk, fc_lit(z, 1), &st);
          CHECK(eval_entry_lookup(callk, fc_true()) == eval_entry_lookup(callk, fc_lit(z, 1)) && eval_entry_lookup(callk, fc_true()) != 0, "the observation key is rebuilt from the reindexed call's support");
          /* under k=0 the demand is for the specialized call */
          (void)whnf(callk, fc_lit(k, 0), &st);
          CHECK(st == W_OK && eval_entry_lookup(callk, fc_lit(k, 0)) != eval_entry_lookup(callk, fc_true()), "a face on the call's own dimension is a different key"); }

        /* ---- 7. a higher path in the evidence parameter ---- */
        { const GraphPairTemplate *gp = graph_pair_get(t->identity_template);
          CHECK(gp && gp->left == A.L && gp->right == A.R, "the graph-pair template is retained");
          /* H : Path (Path X lhs rhs) α α (refl of the evidence); F_{H@i}(r) is a path from F_α(r) to F_α(r) */
          RefId Pt = mk_path_const(0, A.X, A.lhs, A.rhs);
          RefId H = mk_refl(0, Pt, A.alpha);
          DimVarId i = declare_dim();
          RefId Hi = mk_papp_const(0, Pt, A.alpha, A.alpha, H, iv_var(i));
          MapBuilder b; mapb_init(&b); mapb_term(&b, gp->P, Hi); mapb_term(&b, gp->r_left, r); mapb_term(&b, gp->y, A.rhs);
          RefId Fi = reindex(gp->forward, mapb_finish(&b));
          RefId out = mk_plam(i, Fi);
          RefId Fa = reindex(t->forward_body, compose(sigma, map_single_term(t->forward_argument_slot, r)));
          CheckStatus hs = check(A.G, fc_true(), out, mk_path_const(0, reindex(t->codomain, sigma), Fa, Fa), &why);
          CHECK(hs == CK_VALID, "⟨i⟩ F_{H@i}(r) : Path_{R_R}(F_α r, F_α r) (%s: %s)", check_status_name(hs), why); }

        /* ---- an external application pair (§43): APPLY_TRANSFORM -- REF(a), result into an EVAL consumer ---- */
        { Net net; net_init(&net);
          int8_t pneg[1] = { -1 }; Payload P = {0};
          NodeId root = net_node(&net, A_ROOT, 1, pneg, P);
          NodeId ev = net_operation(&net, OP_EVAL, (Payload){ .face = fc_true() });
          Payload Pa = {0}; Pa.a = A.T; Pa.b = DIR_FORWARD; Pa.c = sigma;
          NodeId ap = net_operation(&net, OP_APPLY_TRANSFORM, Pa);
          Payload Pr = {0}; Pr.ref = r;
          NodeId d = net_descriptor(&net, D_REF, Pr);
          net_connect(&net, ev, 1, root, 0);
          net_connect(&net, ap, 1, ev, 0);          /* the result boundary is the EVAL consumer */
          net_connect(&net, ap, 0, d, 0);
          net_run_with_eval(&net);
          NodeKind kk = 0; Payload out;
          bool ok = net_root_read(&net, root, &kk, &out);
          CHECK(ok && kk == D_EVAL_RESULT && ((EvalResult *)(uintptr_t)out.a)->cls == R_INTRODUCTION, "external APPLY_TRANSFORM feeding EVAL yields the pair at the root");
          CHECK(net.n_apply == 1, "one APPLY_TRANSFORM rule in the external net");
          /* a storing consumer retains the reference unevaluated */
          NodeId root2 = net_node(&net, A_ROOT, 1, pneg, P);
          NodeId ap2 = net_operation(&net, OP_APPLY_TRANSFORM, Pa);
          net_connect(&net, ap2, 1, root2, 0);
          net_connect(&net, ap2, 0, net_descriptor(&net, D_REF, Pr), 0);
          Family fw = F_WHNF;
          size_t b0 = family_steps(fw);
          net_run_with_eval(&net);
          size_t b1 = family_steps(fw);
          ok = net_root_read(&net, root2, &kk, &out);
          CHECK(ok && fw && kk == D_REF && b1 == b0, "a storing consumer receives REF(v) and no evaluation is demanded");
          net_free(&net); }
        /* ---- 10. duplicate demands under mixed schedulers are covered by test_schedule ---- */
    }

    /* ---- 1. the empty diagram ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB); TermVarId vo = tv(B); RefId o = ref_var(vo);
      CtxDecl d[2] = { { S_TERM, vB, U0 }, { S_TERM, vo, B } }; ContextId G = context_make(2, d, fc_true());
      DiagramId E = diagram_declare(G, 0, NULL, B, 0, o);
      CHECK(diagram_validate(E, fc_true(), &why) == CK_VALID, "empty diagram validates (%s)", why);
      TermVarId rs, qs; RefId c = diagram_collapse(E, &rs), x = diagram_expand(E, &qs);
      CHECK(c == ref_var(rs) && x == ref_var(qs), "collapse and expand are the identity on the output path type");
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
      /* the first block's transport family substitutes both x_0 and e_0 in the tail */
      Head h; open_ref(c, &h);
      CHECK(h.tag == T_COMP, "collapse of two blocks ends in the second transport");
      head_free(&h);
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
      DimOpen fam = resolve_dim_binder(csh, 0, 0);
      Head hp; open_ref(fam.body, &hp);
      RefId l = HF(&hp, 1).id; head_free(&hp);
      Head ha; open_ref(l, &ha);                                 /* app(app(g, x_i), x_i) */
      RefId arg2 = HF(&ha, 1).id; RefId inner = HF(&ha, 0).id; head_free(&ha);
      open_ref(inner, &ha); RefId arg1 = HF(&ha, 1).id; head_free(&ha);
      CHECK(arg1 == arg2, "both occurrences of the shared node use one instantiated reference s@¬i");
      CHECK(ref_support(l) != dimset_make(NULL, 0), "the family moves along i"); }

    /* ---- 6. rejections ---- */
    { size_t before = transform_count();
      RefId U = U0;
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
      CHECK(compile_identity(&bad, &why) == 0, "wrong evidence endpoints are rejected (%s)", why);
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
      CHECK(compile_identity(&unmet, &why) == 0, "evidence outside the required face is rejected (%s)", why);
      IdentityDecl met = { 9, G2, fc_lit(k, 1), X, 0, L2, R2, ref_var(vp) };
      TransformId tm = compile_identity(&met, &why);
      CHECK(tm != 0, "the same declaration under the face (k=1) compiles (%s)", why);
      if (tm) CHECK(fc_entails(fc_lit(k, 1), transform_get(tm)->required_face) && !fc_entails(fc_true(), transform_get(tm)->required_face), "the compiled record retains its required face");
      /* unresolved checking must not publish: an exhausted budget */
      check_set_budget(5);
      IdentityDecl ok = { 10, G2, fc_lit(k, 1), X, 0, L2, R2, ref_var(vp) };
      size_t n2 = transform_count();
      TransformId tu = compile_identity(&ok, &why);
      check_set_budget(0);
      CHECK(tu == 0 || transform_count() == n2 + 1, "a budgeted compilation either publishes a checked record or nothing");
      CHECK(transform_count() >= before + 1, "rejected declarations publish nothing (%zu)", transform_count() - before); }

    /* ---- 8. cut followed by loop conversion: the residual is retained ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vC = tv(B), vD = tv(B); RefId C = ref_var(vC), D = ref_var(vD);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vC, B }, { S_TERM, vD, B } };
      ContextId G = context_make(3, d, fc_true());
      TransformId cut = compile_cut(G, fc_true(), B, 0, C, D, &why);
      CHECK(cut != 0, "CUT_TO_PATH compiles (%s)", why);
      if (cut) {
        const CompiledTransform *t = transform_get(cut);
        CHECK(certificate_verify(cut, &why) == CK_VALID, "CUT certificate (%s)", why);
        /* a cut (z, u, v) with neutral data */
        TermVarId vz = tv(B); RefId z = ref_var(vz);
        TermVarId vu = tv(mk_path_const(0, B, C, z)), vv = tv(mk_path_const(0, B, D, z));
        ContextId Gz = context_extend_term(context_extend_term(context_extend_term(G, vz, B), vu, term_var_type(vu)), vv, term_var_type(vv));
        RefId Cut = t->domain;
        RefId w = mk_pair_at_lv(0, Cut, z, mk_pair_at_lv(0, apply_term_binder(Cut, 0, 1, z), ref_var(vu), ref_var(vv)));
        RefId call = mk_transform_call(cut, DIR_FORWARD, map_identity(), w);
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
        RefId rcall = mk_transform_call(cut, DIR_REVERSE, map_identity(), p);
        CHECK(check(Gp, fc_true(), rcall, Cut, &why) == CK_VALID, "h ↦ (D, h, refl D) : Cut (%s)", why);
        r = whnf(mk_fst(rcall), fc_true(), &st);
        CHECK(st == W_OK && r->ref == D, "its first component is D"); } }

    /* ---- 8b. §59.1/§59.3: explicit levels and the fixed call origin ---- */
    { TermVarId vX = tv(U0); RefId X = ref_var(vX);
      CtxDecl d[1] = { { S_TERM, vX, U0 } }; ContextId G = context_make(1, d, fc_true());
      CHECK(compile_equivalence(G, fc_true(), X, 1, X, 0, mk_id_equiv(0, X), &why) == 0, "a wrong universe annotation is rejected (%s)", why);
      TransformId eq = compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &why);
      CHECK(eq != 0, "the correctly annotated equivalence compiles (%s)", why);
      if (eq) {
        const CompiledTransform *t = transform_get(eq);
        CHECK(t->domain_level == 0 && t->codomain_level == 0, "the record stores the TypeAt levels");
        CHECK(t->generic_call[0] && t->generic_call[1] && t->generic_call[0] != t->generic_call[1], "one fixed call origin per orientation");
        TermVarId vx = tv(X); RefId x = ref_var(vx);
        RefId direct = mk_transform_call(eq, DIR_FORWARD, map_identity(), x);
        MapBuilder mb; mapb_init(&mb); mapb_term(&mb, t->forward_argument_slot, x);
        CHECK(direct == reindex(t->generic_call[0], mapb_finish(&mb)), "an invocation is a view of the fixed call origin");
        /* a type-changing specialization of the call shares the origin: one application pair */
        TermVarId vY = tv(U0); RefId Y = ref_var(vY); TermVarId vy = tv(Y); RefId y = ref_var(vy);
        MapBuilder sb; mapb_init(&sb); mapb_term(&sb, vX, Y); mapb_term(&sb, vx, y); MapId s = mapb_finish(&sb);
        CHECK(reindex(direct, s) == mk_transform_call(eq, DIR_FORWARD, s, y), "reindexed and direct calls are one reference");
        /* a wrongly annotated call is rejected by the checker */
        CtxDecl d2[2] = { { S_TERM, vX, U0 }, { S_TERM, vx, X } }; ContextId Gx = context_make(2, d2, fc_true());
        CHECK(check(Gx, fc_true(), direct, X, &why) == CK_VALID, "the call checks at the codomain (%s)", why);
        { size_t np2 = context_size(t->parameters); Field f[4];
          f[0] = (Field){ F_REF, NO_SLOT, X };
          RefId wrong = mk_tcall(eq, DIR_FORWARD, np2, f, x, X, mk_universe(0), fc_true());
          CHECK(check(Gx, fc_true(), wrong, mk_universe(0), &why) == CK_INVALID, "a call whose codomain annotation is at another level is rejected (%s)", why); } } }

    /* ---- 9. contractible-fibre projection and section ---- */
    { TermVarId vB = tv(U0); RefId B = ref_var(vB);
      TermVarId vR = tv(mk_fun(0, 1, B, U0)); RefId R = ref_var(vR);
      TermVarId xb = tv(B);
      RefId Kt = mk_pi_lv(0, 0, xb, B, mk_contr(0, mk_app(R, ref_var(xb))));
      TermVarId vk = tv(Kt); RefId k = ref_var(vk);
      CtxDecl d[3] = { { S_TERM, vB, U0 }, { S_TERM, vR, term_var_type(vR) }, { S_TERM, vk, Kt } };
      ContextId G = context_make(3, d, fc_true());
      TransformId cf = compile_contractible_fibre(G, fc_true(), B, 0, R, k, &why);
      CHECK(cf != 0, "COLLAPSE_FIBRE compiles from k (%s)", why);
      if (cf) {
        CHECK(certificate_verify(cf, &why) == CK_VALID, "CONTRACTIBLE_FIBRE certificate (%s)", why);
        const CompiledTransform *t = transform_get(cf);
        TermVarId vb = tv(B);
        ContextId Gb = context_extend_term(G, vb, B);
        RefId sec = mk_transform_call(cf, DIR_REVERSE, map_identity(), ref_var(vb));
        CHECK(check(Gb, fc_true(), sec, t->domain, &why) == CK_VALID, "section b ↦ (b, fst(k b)) : Σ(b:B).R(b) (%s)", why);
        RefId back = mk_transform_call(cf, DIR_FORWARD, map_identity(), sec);
        WhnfStatus st; EvalResult *r = whnf(back, fc_true(), &st);
        CHECK(st == W_OK && r->cls == R_NEUTRAL && r->ref == ref_var(vb), "projection ∘ section ⇝ b");
        /* a non-contraction is rejected */
        TermVarId vk2 = tv(mk_fun(0, 0, B, B));
        CtxDecl d2[3] = { { S_TERM, vB, U0 }, { S_TERM, vR, term_var_type(vR) }, { S_TERM, vk2, term_var_type(vk2) } };
        ContextId G2 = context_make(3, d2, fc_true());
        CHECK(compile_contractible_fibre(G2, fc_true(), B, 0, R, ref_var(vk2), &why) == 0, "k that is not a pointwise contraction is rejected (%s)", why); } }

    /* ---- equivalence and residual equivalence (§44) ---- */
    { TermVarId vX = tv(U0), vY = tv(U0); RefId X = ref_var(vX), Y = ref_var(vY);
      TermVarId ve = tv(mk_equiv(0, 0, X, Y)); RefId e = ref_var(ve);
      CtxDecl d[3] = { { S_TERM, vX, U0 }, { S_TERM, vY, U0 }, { S_TERM, ve, term_var_type(ve) } };
      ContextId G = context_make(3, d, fc_true());
      TransformId eq = compile_equivalence(G, fc_true(), X, 0, Y, 0, e, &why);
      CHECK(eq != 0, "a supplied equivalence compiles (%s)", why);
      if (eq) {
        CHECK(certificate_verify(eq, &why) == CK_VALID, "EQUIVALENCE certificate (%s)", why);
        TermVarId vx = tv(X); ContextId Gx = context_extend_term(G, vx, X);
        RefId fw = mk_transform_call(eq, DIR_FORWARD, map_identity(), ref_var(vx));
        CHECK(check(Gx, fc_true(), fw, Y, &why) == CK_VALID, "forward(x) : Y (%s)", why);
        RefId bk = mk_transform_call(eq, DIR_REVERSE, map_identity(), fw);
        CHECK(check(Gx, fc_true(), bk, X, &why) == CK_VALID, "reverse(forward(x)) : X (%s)", why);
        /* the identity equivalence: forward reduces to the argument */
        TransformId ideq = compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &why);
        CHECK(ideq != 0, "IdEquiv compiles as an equivalence (%s)", why);
        if (ideq) { WhnfStatus st; EvalResult *r = whnf(mk_transform_call(ideq, DIR_REVERSE, map_identity(), ref_var(vx)), fc_true(), &st);
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
      TransformId res = compile_residual_equivalence(G2, fc_true(), L, R, e, &why);
      CHECK(res != 0, "a residual equivalence compiles (%s)", why);
      if (res) CHECK(certificate_verify(res, &why) == CK_VALID, "RESIDUAL_EQUIVALENCE certificate (%s)", why); }

    /* ---- 11. recursive terms without an obtainable observation ---- */
    if (A.T) {
        const CompiledTransform *t = transform_get(A.T);
        MapId sigma = assoc_sigma(&A, A.rhs);
        RefId RL = reindex(t->domain, sigma);
        uint64_t ps[6] = { A.vX, A.vm, A.va, A.vb, A.vc, A.valpha };
        check_open_environment();          /* publication admitted (froze) the environment: open a candidate one */
        SymbolId loop = define_global("loop_r", varset_make(ps, 6), dimset_make(NULL, 0), RL);
        set_global_body(loop, global_ref(loop));
        RefId call = mk_transform_call(A.T, DIR_FORWARD, sigma, global_ref(loop));
        WhnfStatus st; EvalResult *r = whnf(call, fc_true(), &st);
        CHECK(st == W_OK && head_tag(r) == T_PAIR, "the pair is exposed without demanding the cyclic argument");
        /* a transform whose output is its argument: the identity equivalence at a cyclic argument */
        TermVarId vX = tv(U0); RefId X = ref_var(vX);
        CtxDecl d[1] = { { S_TERM, vX, U0 } }; ContextId G = context_make(1, d, fc_true());
        uint64_t px[1] = { vX };
        SymbolId loopx = define_global("loop_x", varset_make(px, 1), dimset_make(NULL, 0), X);
        set_global_body(loopx, global_ref(loopx));
        TransformId ideq = compile_equivalence(G, fc_true(), X, 0, X, 0, mk_id_equiv(0, X), &why);
        RefId call2 = mk_transform_call(ideq, DIR_FORWARD, map_identity(), global_ref(loopx));
        CHECK(check(G, fc_true(), call2, X, &why) == CK_VALID, "the call at the cyclic argument is well typed (%s)", why);
        EvalNetEvents n0 = eval_net_events();
        r = whnf(call2, fc_true(), &st);
        EvalNetEvents n1 = eval_net_events();
        CHECK(st == W_STUCK && r == NULL, "a demand that unfolds the cyclic argument stays unresolved (status %d): nothing published, no synthesized success", (int)st);
        CHECK(n1.apply - n0.apply == 1 && n1.continue_ref - n0.continue_ref == 1, "the application and receiver rules fired exactly once before the demand stalled");
        eval_run();
    }

    printf("  %d passed, %d failed\n", np, nf);
    compiler_free(); check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}

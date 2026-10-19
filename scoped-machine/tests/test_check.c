/* §33–§34 / §38 checking: accept β and the Π, Σ, Path and Glue η
 * conversions; reject incompatible declared types and unbound
 * dependencies; validate dependent substitution images, composition
 * cap/tube agreement, path endpoints, Glue map agreement, system coverage
 * and overlaps; report unresolved conversion without accepting it or
 * calling it unequal. */
#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }

/* context from a list of term variables (declared types) and dimensions */
static ContextId ctx_of(size_t nd, const DimVarId *ds, size_t nt, const TermVarId *xs, FaceId chi) {
    CtxDecl d[32]; size_t n = 0;
    for (size_t k = 0; k < nd; k++) { d[n].sort = S_DIM; d[n].id = ds[k]; n++; }
    for (size_t k = 0; k < nt; k++) { d[n].sort = S_TERM; d[n].id = xs[k]; n++; }
    return context_make(n, d, chi);
}

int main(void) {
    printf("== §33–34 checking and conversion\n");
    machine_init(); eval_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *why = "";
    RefId U0 = mk_universe(0), U1 = mk_universe(1);
    TermVarId vA = tv(U0), vB = tv(U0);
    RefId A = ref_var(vA), B = ref_var(vB);
    TermVarId va = tv(A), vb = tv(A), vbB = tv(B), vf = tv(mk_fun(0, 0, A, A)), vg = tv(mk_fun(0, 0, A, B));
    RefId a = ref_var(va), b = ref_var(vb), bB = ref_var(vbB), f = ref_var(vf), g = ref_var(vg);
    TermVarId x = tv(A), y = tv(A);
    RefId Sg = mk_sigma_lv(0, 0, x, A, B);
    TermVarId vp = tv(Sg), vq = tv(mk_path_const(0, A, a, b));
    RefId p = ref_var(vp), q = ref_var(vq);
    DimVarId k = declare_dim(), m = declare_dim();
    TermVarId base[] = { vA, vB, va, vb, vbB, vf, vg, vp, vq };
    DimVarId dims[] = { k, m };
    ContextId G = ctx_of(2, dims, 9, base, fc_true());

    /* contexts */
    CHECK(check_context(G, &why) == CK_VALID, "well-formed context: %s", why);
    { CtxDecl bad[2] = { { S_TERM, va}, { S_TERM, vA} };      /* a:A before A:U0 */
      ContextId Gb = 0; bool threw = false; (void)threw;
      /* context_make itself refuses forward references; check the checker on a legal-shaped but ill-typed one */
      (void)bad; (void)Gb; }
    { TermVarId vz = tv(a);                                              /* z : a, but a is not a type */
      TermVarId ill[] = { vA, va, vz };
      ContextId Gi = ctx_of(0, NULL, 3, ill, fc_true());
      CHECK(check_context(Gi, &why) == CK_INVALID, "a declaration whose type is not a type is rejected (%s)", why); }

    /* inference and universes */
    Inference I = infer(G, fc_true(), U0);
    CHECK(I.st == CK_VALID && I.type == U1, "U0 : U1");
    I = infer(G, fc_true(), a);
    CHECK(I.st == CK_VALID && I.type == A, "variable lookup");
    I = infer(G, fc_true(), mk_fun(0, 0, A, B));
    CHECK(I.st == CK_VALID && I.type == U0, "A → B : U0");
    I = infer(G, fc_true(), mk_pi_lv(1, 1, tv(U0), U0, U0));
    CHECK(I.st == CK_VALID && I.type == U1, "Π(X:U0).U0 : U1 (max of levels)");
    I = infer(G, fc_true(), mk_app(f, a));
    CHECK(I.st == CK_VALID && I.type == A, "f a : A");
    I = infer(G, fc_true(), mk_app(f, bB));
    CHECK(I.st == CK_INVALID, "f applied to a term of another type is rejected");
    I = infer(G, fc_true(), mk_app(a, b));
    CHECK(I.st == CK_INVALID, "application of a non-function is rejected");
    { TermVarId vu = tv(A); RefId u = ref_var(vu);                          /* not declared in G */
      I = infer(G, fc_true(), mk_app(f, u));
      CHECK(I.st == CK_INVALID, "unbound dependency is rejected (%s)", I.reason); }

    /* β and η */
    RefId id = mk_lam_lv(0, x, A, ref_var(x));
    CHECK(convert_term(G, fc_true(), mk_app(id, a), a, A) == CV_EQUAL, "β: (λx.x) a ≡ a");
    CHECK(convert_term(G, fc_true(), f, mk_lam_lv(0, y, A, mk_app(f, ref_var(y))), mk_fun(0, 0, A, A)) == CV_EQUAL, "Π η: f ≡ λy. f y");
    CHECK(convert_term(G, fc_true(), p, mk_pair(mk_fst(p), mk_snd(p)), Sg) == CV_EQUAL, "Σ η: p ≡ (fst p, snd p)");
    { DimVarId i = declare_dim();
      CHECK(convert_term(G, fc_true(), q, mk_plam(i, mk_papp_const(0, A, a, b, q, iv_var(i))), mk_path_const(0, A, a, b)) == CV_EQUAL, "Path η: q ≡ ⟨i⟩ q@i"); }
    CHECK(convert_term(G, fc_true(), a, b, A) == CV_UNEQUAL, "distinct variables are unequal");
    CHECK(convert_term(G, fc_true(), mk_app(f, a), mk_app(f, b), A) == CV_UNEQUAL, "neutral spines with unequal arguments are unequal");
    CHECK(convert_type(G, fc_true(), A, B) == CV_UNEQUAL, "distinct type variables are unequal");
    CHECK(convert_type(G, fc_true(), mk_fun(0, 0, A, A), mk_pi_lv(0, 0, y, A, A)) == CV_EQUAL, "products compare up to the bound variable");
    /* Glue η at a non-collapsed Glue type */
    { TermVarId vT = tv(U0); RefId T = ref_var(vT);
      TermVarId ve = tv(mk_equiv(0, 0, T, A)); RefId e = ref_var(ve);
      RefId Gl = mk_glue_type_lv(0, A, fc_lit(m, 1), T, e);
      TermVarId vv = tv(Gl); RefId v = ref_var(vv);
      TermVarId more[] = { vA, vB, va, vb, vbB, vf, vg, vp, vq, vT, ve, vv };
      ContextId Gg = ctx_of(2, dims, 12, more, fc_true());
      CHECK(check_context(Gg, &why) == CK_VALID, "context with Glue data: %s", why);
      I = infer(Gg, fc_true(), Gl);
      CHECK(I.st == CK_VALID && I.type == U0, "Glue type formation: %s", I.reason);
      RefId eta = mk_glue_intro_lv(0, A, fc_lit(m, 1), T, e, v, mk_unglue_lv(0, A, fc_lit(m, 1), T, e, v));
      CHECK(check(Gg, fc_true(), eta, Gl, &why) == CK_VALID, "glue[α ↦ v](unglue v) : Glue (%s)", why);
      CHECK(convert_term(Gg, fc_true(), eta, v, Gl) == CV_EQUAL, "Glue η: glue[α ↦ v](unglue v) ≡ v");
      /* Glue map agreement: glue t a requires e.map(t) ≡ a on α */
      RefId Gid = mk_glue_type_lv(0, A, fc_lit(m, 1), A, mk_id_equiv(0, A));
      CHECK(check(Gg, fc_true(), mk_glue_intro_lv(0, A, fc_lit(m, 1), A, mk_id_equiv(0, A), a, a), Gid, &why) == CK_VALID, "glue a a with the identity equivalence (%s)", why);
      CHECK(check(Gg, fc_true(), mk_glue_intro_lv(0, A, fc_lit(m, 1), A, mk_id_equiv(0, A), b, a), Gid, &why) == CK_INVALID, "glue b a is rejected: id.map(b) ≢ a (%s)", why);
      /* the library's equivalence data checks */
      CHECK(check(Gg, fc_true(), mk_id_equiv(0, A), mk_equiv(0, 0, A, A), &why) == CK_VALID, "IdEquiv(A) : Equiv(A, A) (%s)", why);
      CHECK(check(Gg, fc_true(), mk_ua(0, A, A, mk_id_equiv(0, A)), mk_path_const(0, U0, A, A), &why) == CK_VALID, "ua(IdEquiv) : Path U0 A A (%s)", why);
    }

    /* incompatible declared types */
    CHECK(check(G, fc_true(), a, B, &why) == CK_INVALID, "a : B is rejected (%s)", why);
    CHECK(check(G, fc_true(), id, mk_fun(0, 0, A, B), &why) == CK_INVALID, "λx.x : A → B is rejected (%s)", why);
    CHECK(check(G, fc_true(), id, mk_fun(0, 0, A, A), &why) == CK_VALID, "λx.x : A → A (%s)", why);
    CHECK(check(G, fc_true(), mk_pair(a, bB), mk_sigma_lv(0, 0, x, A, B), &why) == CK_VALID, "(a, b) : Σ(x:A).B (%s)", why);
    CHECK(check(G, fc_true(), mk_pair(bB, a), mk_sigma_lv(0, 0, x, A, B), &why) == CK_INVALID, "(b, a) : Σ(x:A).B is rejected");

    /* dependent substitution images */
    { TermVarId vx2 = tv(A);
      TermVarId tgt[] = { vA, vx2 };
      ContextId Gt = ctx_of(0, NULL, 2, tgt, fc_true());
      CHECK(check_map(G, fc_true(), map_single_term(vx2, a), Gt, fc_true(), &why) == CK_VALID, "σ = [x ↦ a] : G → (A:U0, x:A) (%s)", why);
      CHECK(check_map(G, fc_true(), map_single_term(vx2, bB), Gt, fc_true(), &why) == CK_INVALID, "σ = [x ↦ b:B] is rejected (%s)", why);
      /* dependent: y : P x with P : A → U0, image must be at P a */
      TermVarId vP = tv(mk_fun(0, 1, A, U0)); RefId P = ref_var(vP);
      TermVarId vx3 = tv(A), vy3 = tv(mk_app(P, ref_var(vx3)));
      TermVarId tgt2[] = { vA, vP, vx3, vy3 };
      ContextId Gt2 = ctx_of(0, NULL, 4, tgt2, fc_true());
      TermVarId vw = tv(mk_app(P, a));
      TermVarId src[] = { vA, vB, va, vb, vbB, vf, vg, vp, vq, vP, vw };
      ContextId Gs = ctx_of(2, dims, 11, src, fc_true());
      MapBuilder mb; mapb_init(&mb); mapb_term(&mb, vx3, a); mapb_term(&mb, vy3, ref_var(vw));
      CHECK(check_map(Gs, fc_true(), mapb_finish(&mb), Gt2, fc_true(), &why) == CK_VALID, "dependent image y ↦ w : P a (%s)", why);
      MapBuilder mb2; mapb_init(&mb2); mapb_term(&mb2, vx3, b); mapb_term(&mb2, vy3, ref_var(vw));
      CHECK(check_map(Gs, fc_true(), mapb_finish(&mb2), Gt2, fc_true(), &why) == CK_INVALID, "x ↦ b with y ↦ w : P a is rejected (P a ≢ P b) (%s)", why); }

    /* composition: cap/tube agreement, result type */
    { DimVarId i = declare_dim();
      FaceId k0 = fc_lit(k, 0);
      RefId good = mk_comp_lv(0, i, A, k0, a, a);
      I = infer(G, fc_true(), good);
      CHECK(I.st == CK_VALID && I.type == A, "comp^i A [(k=0) ↦ a] a : A (%s)", I.reason);
      RefId bad = mk_comp_lv(0, i, A, k0, b, a);
      I = infer(G, fc_true(), bad);
      CHECK(I.st == CK_INVALID, "tube at 0 ≢ cap is rejected (%s)", I.reason);
      RefId cpi = mk_coe_at(0, i, mk_fun(0, 0, A, B), g);
      I = infer(G, fc_true(), cpi);
      CHECK(I.st == CK_VALID && convert_type(G, fc_true(), I.type, mk_fun(0, 0, A, B)) == CV_EQUAL, "coe in A → B : A → B (%s)", I.reason);
      CHECK(check(G, fc_true(), mk_app(cpi, a), B, &why) == CK_VALID, "(coe f) a : B (%s)", why); }

    /* path endpoints */
    { DimVarId i = declare_dim();
      CHECK(check(G, fc_true(), mk_plam(i, a), mk_path_const(0, A, a, a), &why) == CK_VALID, "⟨i⟩ a : Path A a a (%s)", why);
      CHECK(check(G, fc_true(), mk_plam(i, a), mk_path_const(0, A, a, b), &why) == CK_INVALID, "⟨i⟩ a : Path A a b is rejected (%s)", why);
      I = infer(G, fc_true(), mk_papp_const(0, A, a, b, q, iv_var(k)));
      CHECK(I.st == CK_VALID && I.type == A, "q @ k : A"); }

    /* systems: coverage and overlaps */
    { FaceId k0 = fc_lit(k, 0), k1 = fc_lit(k, 1);
      FaceId fs[2] = { k0, k1 }; RefId ts[2] = { a, b };
      RefId sys = mk_system(2, fs, ts);
      ContextId Gk = context_restrict(G, fc_join(k0, k1));
      CHECK(check(Gk, fc_join(k0, k1), sys, A, &why) == CK_VALID, "[(k=0) ↦ a, (k=1) ↦ b] : A under (k=0)∨(k=1) (%s)", why);
      CHECK(check(G, fc_true(), sys, A, &why) == CK_INVALID, "the same system under true fails coverage (%s)", why);
      FaceId fs2[2] = { k0, fc_true() }; RefId ts2[2] = { a, b };
      CHECK(check(G, fc_true(), mk_system(2, fs2, ts2), A, &why) == CK_INVALID, "overlapping branches a vs b are rejected (%s)", why);
      RefId ts3[2] = { a, a };
      CHECK(check(G, fc_true(), mk_system(2, fs2, ts3), A, &why) == CK_VALID, "agreeing overlap is accepted (%s)", why);
      /* conversion under a disjunctive face: clausewise */
      CHECK(convert_term(Gk, fc_join(k0, k1), sys, mk_system(2, fs, ts), A) == CV_EQUAL, "system ≡ itself clausewise");
      RefId ts4[2] = { b, b };
      CHECK(convert_term(Gk, fc_join(k0, k1), sys, mk_system(2, fs, ts4), A) == CV_UNEQUAL, "systems differing on one clause are unequal"); }

    /* candidate-environment mutation (§57 R1): verdicts, conversions and
     * observations made before a body is registered are not reused after;
     * the correctly typed body is accepted and its value observed */
    { uint64_t params[2] = { vA, va };
      SymbolId cand = define_global("cand", varset_make(params, 2), dimset_make(NULL, 0), A);
      Inference I0 = infer(G, fc_true(), global_ref(cand));
      CHECK(I0.st == CK_VALID && I0.type == A, "an opaque candidate checks at its declaration (%s)", I0.reason);
      CHECK(convert_term(G, fc_true(), global_ref(cand), a, A) == CV_UNEQUAL, "opaque candidate vs a: UNEQUAL before the body exists");
      WhnfStatus st0; EvalResult *r0 = whnf(global_ref(cand), fc_true(), &st0);
      CHECK(st0 == W_OK && r0->cls == R_NEUTRAL, "the opaque candidate observes as a neutral");
      CHECK(set_global_body(cand, a), "the candidate environment accepts the body");
      CHECK(convert_term(G, fc_true(), global_ref(cand), a, A) == CV_EQUAL, "after the body cand := a the conversion is recomputed: EQUAL");
      WhnfStatus st1; EvalResult *r1 = whnf(global_ref(cand), fc_true(), &st1);
      CHECK(st1 == W_OK && r1->ref == a, "the observation is recomputed in the new environment");
      CHECK(check(G, fc_true(), global_ref(cand), A, &why) == CK_VALID, "the defined candidate checks (%s)", why); }

    /* checked observation validates its own judgment */
    { WhnfStatus st; EvalResult *r = observe_checked(G, mk_app(id, a), &st, &why);
      CHECK(st == W_OK && r && r->ref == a, "observe_checked: (λx.x) a ⇝ a (%s)", why);
      r = observe_checked(G, mk_app(f, bB), &st, &why);
      CHECK(st == W_INVALID && r == NULL, "observe_checked refuses an ill-typed occurrence: %s", why); }

    /* a local observation imposes no registry-wide phase boundary */
    { uint64_t params[1] = { vA };
      CHECK(define_global("after-observation", varset_make(params, 1), dimset_make(NULL, 0), A) != 0, "a checked observation leaves unrelated declarations possible");
      SymbolId ok = define_global("afteropen", varset_make(params, 1), dimset_make(NULL, 0), A);
      CHECK(ok != 0, "further declarations require no environment reopening"); }

    /* unresolved: cyclic computation */
    { SymbolId L = define_global("loopA", varset_make(NULL, 0), dimset_make(NULL, 0), A);
      /* loopA : A is declared over the empty parameter list; A is a free variable of the type, so declare it as a parameter */
      (void)L;
      uint64_t params[1] = { vA };
      SymbolId L2 = define_global("loopB", varset_make(params, 1), dimset_make(NULL, 0), A);
      set_global_body(L2, global_ref(L2));
      ConvStatus cv = convert_term(G, fc_true(), global_ref(L2), a, A);
      CHECK(cv == CV_UNRESOLVED, "comparing a cyclic computation is UNRESOLVED (got %s), neither EQUAL nor UNEQUAL", conv_status_name(cv));
      CheckStatus cs = check(G, fc_true(), mk_app(f, global_ref(L2)), A, &why);
      CHECK(cs == CK_VALID, "the cyclic term still has a declared type usable for checking (%s)", why);
      cs = check(G, fc_true(), mk_fst(global_ref(L2)), A, &why);
      CHECK(cs == CK_INVALID, "projecting a term of type A is rejected without evaluating it (%s)", why); }

    /* budget */
    check_set_budget(5);
    CHECK(check(G, fc_true(), mk_ua(0, B, B, mk_id_equiv(0, B)), mk_path_const(0, U0, B, B), &why) == CK_UNRESOLVED, "an exhausted budget is UNRESOLVED (%s)", why);
    check_set_budget(0);

    /* signature: a declared symbol with a well-typed body, and one without */
    { uint64_t params[1] = { vA };
      SymbolId Kc = define_global("Kc", varset_make(params, 1), dimset_make(NULL, 0), mk_fun(0, 0, A, mk_fun(0, 0, A, A)));
      set_global_body(Kc, mk_lam_lv(0, x, A, mk_lam_lv(0, y, A, ref_var(x))));
      CheckStatus cs = check_signature(&why);
      CHECK(cs == CK_INVALID && strstr(why, "declared type") == NULL, "signature with loopA (type A over no parameters) is rejected: %s", why);
      I = infer(G, fc_true(), mk_app(mk_app(global_ref(Kc), a), b));
      CHECK(I.st == CK_VALID && I.type == A, "Kc a b : A through the declared type (%s)", I.reason);
      CHECK(convert_term(G, fc_true(), mk_app(mk_app(global_ref(Kc), a), b), a, A) == CV_EQUAL, "Kc a b ≡ a by unfolding the registered body"); }

    /* the evaluator's composition clauses produce well-typed outputs */
    { DimVarId i = declare_dim();
      WhnfStatus st;
      TermVarId vz = tv(Sg), vT = tv(U0); RefId T = ref_var(vT);
      TermVarId ve = tv(mk_equiv(0, 0, T, A)); RefId e = ref_var(ve);
      RefId Gl = mk_glue_type_lv(0, A, fc_lit(m, 1), T, e);
      TermVarId vv = tv(Gl); RefId v = ref_var(vv);
      TermVarId vpa = tv(mk_path_const(0, A, a, a));
      TermVarId more[] = { vA, vB, va, vb, vbB, vf, vg, vp, vq, vz, vT, ve, vv, vpa };
      ContextId Gc = ctx_of(2, dims, 14, more, fc_true());
      EvalResult *r;
      r = whnf(mk_coe_at(0, i, Sg, ref_var(vz)), fc_true(), &st);
      CHECK(st == W_OK && check(Gc, fc_true(), r->ref, Sg, &why) == CK_VALID, "Σ clause output : Σ(x:A).B (%s)", why);
      r = whnf(mk_coe_at(0, i, mk_fun(0, 0, A, B), g), fc_true(), &st);
      CHECK(st == W_OK && check(Gc, fc_true(), r->ref, mk_fun(0, 0, A, B), &why) == CK_VALID, "Π clause output : A → B (%s)", why);
      r = whnf(mk_coe_at(0, i, mk_path_const(0, A, a, a), ref_var(vpa)), fc_true(), &st);
      CHECK(st == W_OK && check(Gc, fc_true(), r->ref, mk_path_const(0, A, a, a), &why) == CK_VALID, "PathP clause output : Path A a a (%s)", why);
      r = whnf(mk_coe_at(1, i, U0, A), fc_true(), &st);
      CHECK(st == W_OK && check(Gc, fc_true(), r->ref, U0, &why) == CK_VALID, "universe clause output : U0 (%s)", why);
      r = whnf(mk_coe_at(0, i, Gl, v), fc_true(), &st);
      CheckStatus gs = check(Gc, fc_true(), r->ref, Gl, &why);
      CHECK(st == W_OK && gs == CK_VALID, "Glue clause output : Glue[(m=1) ↦ (T,e)] A — %s (%s)", check_status_name(gs), why);
      /* transport along ua(id) of a type is a type */
      RefId tr = mk_coe_at(1, i, mk_papp_const(2, U1, U0, U0, mk_ua(1, U0, U0, mk_id_equiv(1, U0)), iv_var(i)), A);
      r = whnf(tr, fc_true(), &st);
      CHECK(st == W_OK && check(Gc, fc_true(), r->ref, U0, &why) == CK_VALID, "transport along ua(id) : U0 (%s)", why);
      CHECK(check(Gc, fc_true(), tr, U0, &why) == CK_VALID, "the transport itself checks by the composition rule (%s)", why);
    }

    /* audit cases */
    { /* opaque constant: neutral, compared by symbol and parameters */
      uint64_t params[1] = { vA };
      SymbolId c1 = define_global("c1", varset_make(params, 1), dimset_make(NULL, 0), A);
      CHECK(check(G, fc_true(), global_ref(c1), A, &why) == CK_VALID, "an opaque constant checks at its declared type (%s)", why);
      CHECK(convert_term(G, fc_true(), global_ref(c1), a, A) == CV_UNEQUAL, "opaque constant vs a variable: UNEQUAL, no abort");
      CHECK(convert_term(G, fc_true(), global_ref(c1), global_ref(c1), A) == CV_EQUAL, "opaque constant vs itself");
      WhnfStatus st; EvalResult *r = whnf(mk_app(f, global_ref(c1)), fc_true(), &st);
      CHECK(st == W_OK && r->cls == R_NEUTRAL, "an opaque constant observes as a neutral");
      /* a symbol whose body does not match its declaration is rejected on first use */
      SymbolId bad = define_global("badsym", varset_make(params, 1), dimset_make(NULL, 0), A);
      set_global_body(bad, U0);
      I = infer(G, fc_true(), global_ref(bad));
      CHECK(I.st == CK_INVALID, "a symbol with an ill-typed body is rejected on use (%s)", I.reason);
      /* the same comparison at two convertible but distinct Π types */
      RefId domA = mk_app(mk_lam_lv(1, tv(U0), U0, A), U0);        /* (λ_.A) U0 ≡ A */
      RefId AA2 = mk_pi_lv(0, 0, tv(domA), domA, A);
      CHECK(convert_term(G, fc_true(), f, g, mk_fun(0, 0, A, A)) == CV_UNEQUAL && convert_term(G, fc_true(), f, f, AA2) == CV_EQUAL, "fresh comparison variables are keyed by the expected type head too");
      /* lambda domain annotation must be a type even in checking mode */
      RefId notatype = mk_app(mk_lam_lv(1, tv(U0), U0, A), mk_fst(U0));
      CHECK(check(G, fc_true(), mk_lam_lv(0, tv(notatype), notatype, a), mk_fun(0, 0, A, A), &why) == CK_INVALID, "λ with an ill-formed domain annotation is rejected in check mode (%s)", why);
      /* scope is validated even under the false face */
      TermVarId vu = tv(A);
      CHECK(check(G, fc_false(), ref_var(vu), A, &why) == CK_INVALID, "unbound variable under the false face is rejected (%s)", why);
      CHECK(check(G, fc_false(), a, A, &why) == CK_VALID, "a well-scoped obligation under the false face is vacuous (%s)", why);
      DimVarId zz = declare_dim();
      CHECK(check(G, fc_lit(zz, 0), a, A, &why) == CK_INVALID, "a face over an undeclared dimension is rejected (%s)", why); }

    /* unrelated rejected definitions do not become premises of this term */
    { WhnfStatus st; EvalResult *r = observe_checked(G, mk_app(id, a), &st, &why);
      CHECK(st == W_OK && r && r->ref == a, "observe_checked remains local despite unrelated rejected declarations: %s", why);
      CHECK(check_signature(&why) == CK_INVALID, "explicit whole-signature checking reports the invalid definitions (%s)", why); }

    printf("  %d passed, %d failed\n", np, nf);
    check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}

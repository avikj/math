/* test_reuse.c — uniform reuse (§§74–82): the acceptance matrix A1–A21 of
 * §82.2 and the end-to-end run of §82.3, on the accepted machine. Semantic
 * producer/rule starts are read through the §74.2 counter contract
 * (reuse_stats.h); consumer request/delivery events are read from the
 * coarse event vector. Every positive correctness assertion is retained
 * beside the reuse assertion it refines.
 */
#include "../src/work.h"
#include "../src/reuse.h"
#include "assoc.h"
#include <string.h>
#include <pthread.h>

static int failures, checks;
#define EXPECT(c, ...) do { checks++; if (!(c)) { failures++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)
static void section(const char *s) { printf("%s\n", s); }
static RefId observe(RefId t, FaceId f) { WhnfStatus st; EvalResult *r = whnf(t, f, &st); require(st == W_OK && r, "observation failed (%d)", (int)st); return r->ref; }
static EvalResult *observe_r(RefId t, FaceId f) { WhnfStatus st; EvalResult *r = whnf(t, f, &st); require(st == W_OK && r, "observation failed (%d)", (int)st); return r; }
#define C(x) reuse_count(REUSE_##x)

typedef struct { TermVarId vA, va, vx, vy, vz, vf; RefId A, a, x, y, z, f, AA; ContextId G; } Base;
static Base base(void) {
    Base b; RefId U = mk_universe(0);
    b.vA = declare_term(U, fc_true()); b.A = ref_var(b.vA);
    b.va = declare_term(b.A, fc_true()); b.a = ref_var(b.va);
    b.vx = declare_term(b.A, fc_true()); b.x = ref_var(b.vx);
    b.vy = declare_term(b.A, fc_true()); b.y = ref_var(b.vy);
    b.vz = declare_term(b.A, fc_true()); b.z = ref_var(b.vz);
    b.AA = mk_fun(0, 0, b.A, b.A);
    b.vf = declare_term(b.AA, fc_true()); b.f = ref_var(b.vf);
    CtxDecl ds[] = { { S_TERM, b.vA, U }, { S_TERM, b.va, b.A }, { S_TERM, b.vz, b.A }, { S_TERM, b.vf, b.AA } };
    b.G = context_make(4, ds, fc_true());
    return b;
}

static void a1_a2_a3(void) {
    section("A1–A3. structural identity: direct vs specialized view, alpha renaming, raw node vs template view");
    Base b = base(); const char *why = NULL;
    RefId fn = mk_lam_lv(0, b.vx, b.A, b.x);
    RefId abstract = mk_app(fn, b.z), via_map = reindex1(abstract, b.vz, b.a), direct = mk_app(fn, b.a);
    EXPECT(via_map != direct && shape_of(via_map) == shape_of(direct), "A1: different references, one structural computation");
    uint64_t e0 = C(EVAL_BODY), beta0 = C(BETA);
    EXPECT(observe(via_map, fc_true()) == b.a, "A1: the view evaluates to a");
    uint64_t e1 = C(EVAL_BODY);
    EXPECT(e1 > e0 && C(BETA) == beta0 + 1, "A1: the first demand runs the body (one beta)");
    EvalEvents ev0 = eval_events();
    EXPECT(observe(direct, fc_true()) == b.a, "A1: the direct construction evaluates to a");
    EvalEvents ev1 = eval_events();
    EXPECT(C(EVAL_BODY) == e1 && C(BETA) == beta0 + 1 && ev1.launch == ev0.launch && ev1.request == ev0.request + 1 && ev1.deliver == ev0.deliver + 1, "A1: the second demand repeats no body/beta work; its own request and delivery remain");
    EXPECT(check(b.G, fc_true(), via_map, b.A, &why) == CK_VALID && check(b.G, fc_true(), direct, b.A, &why) == CK_VALID, "A1: both occurrence checks are valid");
    /* A2 */
    RefId g = mk_lam_lv(0, b.vy, b.A, b.y);
    RefId nested1 = mk_lam_lv(0, b.vx, b.A, mk_lam_lv(0, b.vy, b.A, b.x)), nested2 = mk_lam_lv(0, b.vz, b.A, mk_lam_lv(0, b.vx, b.A, b.z));
    RefId other = mk_lam_lv(0, b.vx, b.A, mk_lam_lv(0, b.vy, b.A, b.y));
    EXPECT(shape_of(fn) == shape_of(g) && shape_of(nested1) == shape_of(nested2) && shape_of(nested1) != shape_of(other), "A2: alpha-renamed lambdas and nested binders share a shape; a different binding structure does not");
    uint64_t beta1 = C(BETA);
    observe(mk_app(fn, b.a), fc_true());
    uint64_t e2 = C(EVAL_BODY);
    EXPECT(observe(mk_app(g, b.a), fc_true()) == b.a && C(EVAL_BODY) == e2 && C(BETA) == beta1, "A2: the renamed application shares the computation and the beta (none repeated; the first was shared with A1)");
    RefId app1 = mk_app(mk_app(nested1, b.a), b.z), app2 = mk_app(mk_app(nested2, b.a), b.z);
    EXPECT(observe(app1, fc_true()) == b.a, "A2: nested application evaluates");
    uint64_t e3 = C(EVAL_BODY), beta3 = C(BETA);
    EXPECT(observe(app2, fc_true()) == b.a && C(EVAL_BODY) == e3 && C(BETA) == beta3, "A2: the alpha-variant nested application repeats no body and no beta");
    EXPECT(convert_term(b.G, fc_true(), nested1, nested2, mk_fun(0, 0, b.A, b.AA)) == CV_EQUAL, "A2: the renamed functions are convertible");
    /* capture / slot negatives: a scope whose body mentions a wrong-depth local is rejected structurally (§50) */
    { DimVarId i = declare_dim(); ScopeId good = capture_dim1(i, b.A, mk_universe(0), 0, fc_true()); const char *r = NULL;
      EXPECT(scope_validate(good, &r), "A2: a well-formed scope validates");
      ScopeId unavailable = capture_dim1(i, b.A, mk_universe(0), 0, fc_false());
      Inference q = infer(b.G, fc_true(), mk_coe(0, unavailable, b.a));
      EXPECT(q.st == CK_INVALID, "A2: a false-only family scope used at true still rejects"); }
    /* A3: a raw constructor and a template view with the same opened construction */
    DimVarId j = declare_dim();
    RefId refl_t = mk_refl(0, b.A, b.a);                 /* template view */
    Head h; open_ref(refl_t, &h); uint64_t lv = h.levels; Tag tg = h.tag; head_free(&h);
    EXPECT(ref_is_tview(refl_t) && tg == T_PLAM, "A3: refl is a template view of a path lambda");
    RefId raw = 0;
    { /* the raw node with the same annotated construction: PLAM(j. a) at the template's level */
      term_levels_push(levels_first(lv), levels_second(lv)); raw = mk_plam(j, b.a); term_levels_pop(); }
    EXPECT(!ref_is_tview(raw) && shape_of(raw) == shape_of(refl_t), "A3: raw PLAM(j.a) and the refl template view have one shape");
    RefId pr = mk_papp_const(0, b.A, b.a, b.a, refl_t, iv_var(j)), pr2 = mk_papp_const(0, b.A, b.a, b.a, raw, iv_var(j));
    uint64_t pb0 = C(PATH_BETA);
    EXPECT(observe(pr, fc_true()) == b.a && C(PATH_BETA) == pb0 + 1, "A3: path application of the template view reduces by one path beta");
    uint64_t e4 = C(EVAL_BODY);
    EXPECT(observe(pr2, fc_true()) == b.a && C(PATH_BETA) == pb0 + 1 && C(EVAL_BODY) == e4, "A3: the raw node's application shares that computation");
    EXPECT(check(b.G, fc_true(), refl_t, mk_path_const(0, b.A, b.a, b.a), &why) == CK_VALID, "A3: the template occurrence checks on its own");
    { RefId wrong = mk_refl(1, b.A, b.a); Inference q = infer(b.G, fc_true(), wrong); EXPECT(q.st == CK_INVALID, "A3: a wrong level annotation still rejects"); }
}

static void a4_a7(void) {
    section("A4–A7. completed reductions reused under specialization and restriction; the residual is observed");
    Base b = base();
    RefId fn = mk_lam_lv(0, b.vx, b.A, b.x);
    /* A4 */
    RefId t = mk_app(fn, b.z);
    EXPECT(observe(t, fc_true()) == b.z, "A4: generic beta");
    observe(b.a, fc_true());
    uint64_t beta = C(BETA), e0 = C(EVAL_BODY), ri0 = C(RECEIPT_INSTANCE);
    RefId inst = reindex1(t, b.vz, b.a);
    EXPECT(observe(inst, fc_true()) == b.a && C(BETA) == beta && C(EVAL_BODY) == e0 && C(RECEIPT_INSTANCE) == ri0 + 1, "A4: the instance continues from the receipt: no repeated beta, no body, one receipt instantiation");
    EntryId ei = eval_entry_lookup(inst, fc_true());
    EXPECT(eval_entry_adapter_source(ei) == eval_entry_lookup(t, fc_true()) && eval_entry_residual(eval_entry_lookup(t, fc_true())) == b.z, "A4: the selected reuse edge and the generic residual are recorded");
    /* A5: a neutral residual that becomes a redex */
    TermVarId vw = declare_term(b.A, fc_true()); RefId w = ref_var(vw);
    RefId u = mk_app(b.f, w);
    EvalResult *ru = observe_r(u, fc_true());
    EXPECT(ru->cls == R_NEUTRAL && eval_entry_residual(eval_entry_lookup(u, fc_true())) == u, "A5: f z is neutral with a reflexive residual");
    uint64_t beta5 = C(BETA);
    RefId u2 = reindex1(u, b.vf, fn);
    EvalResult *ru2 = observe_r(u2, fc_true());
    EXPECT(ru2->cls == R_NEUTRAL && ru2->ref == w && C(BETA) == beta5 + 1, "A5: after f := λx.x the residual reduces (one new beta) to w; no stale NEUTRAL f w");
    /* A6: stronger face with an unused dimension */
    DimVarId i = declare_dim();
    RefId ptype = mk_path_const(0, b.A, b.a, b.a); TermVarId vp = declare_term(ptype, fc_true());
    RefId pi = mk_papp_const(0, b.A, b.a, b.a, ref_var(vp), iv_var(i));
    RefId k = mk_lam_lv(0, b.vx, b.A, b.a), kt = mk_app(k, pi);
    EXPECT(observe(kt, fc_true()) == b.a, "A6: (λx.a)(p@i) is a under true");
    uint64_t beta6 = C(BETA); EvalEvents v0 = eval_events();
    EXPECT(observe(kt, fc_lit(i, 0)) == b.a && C(BETA) == beta6, "A6: under i=0 the completed reduction is reused; no beta");
    EvalEvents v1 = eval_events();
    EXPECT(v1.request == v0.request + 1 + 1 && v1.deliver >= v0.deliver + 1, "A6: the consumer's own request/delivery and the adapter's request remain distinct events");
    EXPECT(eval_entry_lookup(pi, fc_true()) == 0, "A6: the argument was never evaluated");
    /* A7: generic path then endpoint; Glue then face collapse; no leak to the weaker face */
    EvalResult *rp = observe_r(pi, fc_true());
    EXPECT(rp->cls == R_NEUTRAL, "A7: p @ i is neutral under true");
    uint64_t ep0 = C(ENDPOINT);
    EXPECT(observe(pi, fc_lit(i, 0)) == b.a && C(ENDPOINT) == ep0 + 1, "A7: under i=0 the residual reaches the endpoint a");
    EXPECT(observe_r(pi, fc_true()) == rp, "A7: the stronger-face answer does not leak to the weaker face");
    FaceId al = fc_lit(i, 1);
    TermVarId vT = declare_term(mk_universe(0), al); RefId T = ref_var(vT);
    TermVarId ve = declare_term(mk_equiv(0, 0, T, b.A), al);
    RefId glue = mk_glue_type_lv(0, b.A, al, T, ref_var(ve));
    EvalResult *rg = observe_r(glue, fc_true());
    EXPECT(rg->cls == R_INTRODUCTION && rg->ref == glue, "A7: Glue is an introduction under true");
    uint64_t gl0 = C(GLUE_RULE);
    EvalResult *rg1 = observe_r(glue, al);
    EXPECT(rg1->cls == R_NEUTRAL && rg1->ref == T && C(GLUE_RULE) == gl0 + 1, "A7: under i=1 Glue collapses to T (one glue rule)");
    EXPECT(observe_r(glue, fc_true()) == rg, "A7: the collapse does not replace the generic answer");
}

static void a8_a9(void) {
    section("A8–A9. unrelated environment extension keeps answers; a changed dependency does not");
    Base b = base(); const char *why = NULL;
    RefId U0 = mk_universe(0), U1 = mk_universe(1);
    TermVarId vX = declare_term(U1, fc_true());
    RefId closed = mk_app(mk_lam_lv(2, vX, U1, ref_var(vX)), U0);
    EXPECT(observe(closed, fc_true()) == U0, "A8: closed term evaluates");
    uint64_t e0 = C(EVAL_BODY); EvalEvents v0 = eval_events();
    SymbolId s = define_global("unrelated_a8", varset_make(NULL, 0), dimset_make(NULL, 0), U0); require(s, "define");
    EXPECT(observe(closed, fc_true()) == U0 && C(EVAL_BODY) == e0 && eval_events().launch == v0.launch, "A8: after an unrelated declaration the answer is reused (empty dependency set)");
    /* public admission of the new environment still runs */
    ContextId E = context_make(0, NULL, fc_true());
    WhnfStatus st; EvalResult *r = observe_checked(E, closed, &st, &why);
    EXPECT(st == W_OK && r && r->ref == U0, "A8: checked observation admits the new environment and reuses the answer");
    uint64_t e_adm = C(EVAL_BODY);
    check_open_environment();
    EXPECT(eval_entry_lookup(closed, fc_true()) != 0 && observe(closed, fc_true()) == U0 && C(EVAL_BODY) == e_adm, "A8: opening a new session keeps the persistent answer");
    /* A9: opaque → body */
    uint64_t pars[2] = { b.vA, b.va };
    SymbolId g = define_global("g_a9", varset_make(pars, 2), dimset_make(NULL, 0), b.A); require(g, "define g");
    RefId gref = global_ref(g);
    EvalResult *r0 = observe_r(gref, fc_true());
    EXPECT(r0->cls == R_NEUTRAL, "A9: opaque g is neutral");
    EntryId e_old = eval_entry_lookup(gref, fc_true());
    const uint64_t *dp; size_t nd = eval_entry_gdeps(e_old, &dp);
    EXPECT(nd == 1 && dp[0] == g && dp[1] == 1, "A9: the opaque observation records the symbol at revision 1 (absent body)");
    EXPECT(convert_term(b.G, fc_true(), gref, b.a, b.A) == CV_UNEQUAL, "A9: g is not convertible to a while opaque");
    EXPECT(set_global_body(g, b.a), "A9: body set");
    EXPECT(!eval_entry_deps_valid(e_old), "A9: the old answer's dependency is no longer current");
    uint64_t un0 = C(GLOBAL_UNFOLD);
    EvalResult *r1 = observe_r(gref, fc_true());
    EXPECT(r1 != r0 && r1->cls == R_NEUTRAL && r1->ref == b.a && C(GLOBAL_UNFOLD) == un0 + 1, "A9: the new answer unfolds the body (not the old neutral)");
    EXPECT(eval_entry_lookup(gref, fc_true()) != e_old, "A9: a new producer instance, the old one retained as history");
    EXPECT(convert_term(b.G, fc_true(), gref, b.a, b.A) == CV_EQUAL, "A9: the checker's conversion is recomputed for the new dependency");
    Inference q = infer(b.G, fc_true(), gref); EXPECT(q.st == CK_VALID && q.type == b.A, "A9: inference remains correct");
}

static void a10_a11(void) {
    section("A10–A11. one semantic action per content; distinct proof paths stay distinct");
    const char *why = NULL; Assoc a; assoc_build(&a, &why); require(a.T, "assoc");
    IdentityDecl d = { 987654321, a.G, fc_true(), a.X, 0, a.L, a.R, a.alpha };
    TransformId t2 = compile_identity(&d, &why);
    EXPECT(t2 == a.T, "A10: a source label change yields the same action record");
    uint64_t src[4]; size_t ns = transform_sources(a.T, src, 4);
    EXPECT(ns == 2 && src[0] == 1 && src[1] == 987654321, "A10: both source declarations are retained as provenance (%zu)", ns);
    MapId s = assoc_sigma(&a, a.rhs); RefId arg = assoc_left_arg(&a, s);
    RefId c1 = mk_transform_call(a.T, DIR_FORWARD, s, arg), c2 = mk_transform_call(t2, DIR_FORWARD, s, arg);
    EXPECT(c1 == c2, "A10: one call computation");
    RefId r1 = observe(c1, fc_true()); uint64_t ap = C(IDENTITY_APPLY), e0 = C(EVAL_BODY);
    EXPECT(observe(c2, fc_true()) == r1 && C(IDENTITY_APPLY) == ap && C(EVAL_BODY) == e0, "A10: the second identical call has zero additional APPLY_TRANSFORM and no body");
    EXPECT(certificate_verify(a.T, &why) == CK_VALID, "A10: the certificate still verifies");
    /* A11: same endpoints, a different proof */
    TermVarId valpha2 = declare_term(mk_path_const(0, a.X, a.lhs, a.rhs), fc_true());
    ContextId G2 = context_extend_term(a.G, valpha2, term_var_type(valpha2));
    DiagNode ln = { 1, a.vu, a.vs, a.X, 0, a.mab }; DiagramId L2 = diagram_declare(G2, 1, &ln, a.X, 0, m2(a.m, ref_var(a.vu), a.c));
    DiagNode rn = { 2, a.vv, a.vt, a.X, 0, a.mbc }; DiagramId R2 = diagram_declare(G2, 1, &rn, a.X, 0, m2(a.m, a.a, ref_var(a.vv)));
    IdentityDecl d1 = { 11, G2, fc_true(), a.X, 0, L2, R2, a.alpha }, d2 = { 12, G2, fc_true(), a.X, 0, L2, R2, ref_var(valpha2) };
    TransformId T1 = compile_identity(&d1, &why); require(T1, "T1: %s", why ? why : "");
    TransformId T2 = compile_identity(&d2, &why); require(T2, "T2: %s", why ? why : "");
    EXPECT(T1 != T2, "A11: distinct proof paths between the same endpoints are distinct actions");
    const CompiledTransform *x1 = transform_get(T1), *x2 = transform_get(T2);
    EXPECT(x1->domain == x2->domain && x1->codomain == x2->codomain && x1->forward_body != x2->forward_body, "A11: same interfaces, different evidence bodies");
    MapId s2 = assoc_sigma(&a, a.rhs);
    { /* σ for T1/T2: their common output variable */
      const CompiledTransform *t = transform_get(T1); TermVarId yv = 0;
      for (size_t k = 0; k < context_size(t->parameters); k++) { CtxDecl dd = context_decl(t->parameters, k); if (dd.sort == S_TERM && !context_declares_term(G2, dd.id, NULL)) yv = dd.id; }
      s2 = map_single_term(yv, a.rhs); }
    RefId arg2 = 0; { const CompiledTransform *t = transform_get(T1); RefId RL = reindex(t->domain, s2); RefId inner = apply_term_binder(RL, 0, 1, a.mab); arg2 = mk_pair_at_lv(0, RL, a.mab, mk_pair_at_lv(0, inner, mk_refl(0, a.X, a.mab), a.alpha)); }
    RefId o1 = observe(mk_transform_call(T1, DIR_FORWARD, s2, arg2), fc_true()), o2 = observe(mk_transform_call(T2, DIR_FORWARD, s2, arg2), fc_true());
    EXPECT(o1 != o2 && ref_tag(o1) == T_PAIR && ref_tag(o2) == T_PAIR, "A11: the two actions produce different realizations (proof relevance retained)");
}

static void a12_a13(void) {
    section("A12–A13. repeated reduction / proof check repeat no producer; a changed model recomputes");
    FormulaId f = formula_one();
    for (uint64_t i = 1; i <= 8; i++) f = formula_and(f, formula_atom(atom_named(1200 + i)));
    ModelId m = model_make(12, (KindWeights){ .named = 1 }, set_empty());
    const char *why = NULL;
    WorkLedger l0 = work_ledger(); Reduction r1 = formula_reduce(f, m, &why); uint64_t rb = C(REDUCE_BODY); WorkLedger l1 = work_ledger();
    Reduction r2 = formula_reduce(f, m, &why); WorkLedger l2 = work_ledger();
    EXPECT(r1.reduced && r1.value == 8 && r2.lower == r1.lower && r2.attaining == r1.attaining && C(REDUCE_BODY) == rb, "A12: the repeated reduction is the same answer with no new body");
    EXPECT(l2.memo_lookup > l1.memo_lookup && l2.memo_deliver > l1.memo_deliver && l1.memo_lookup > l0.memo_lookup, "A12: lookup/delivery accounting of the repeat is nonzero");
    /* supplied proof check repeated */
    AtomId a = atom_named(1301), b = atom_named(1302);
    ProofId p = proof_or_bound(formula_atom(a), formula_atom(b), proof_mandatory(formula_atom(a), set_make(1, &a), m), proof_mandatory(formula_atom(b), set_make(1, &b), m));
    /* a prepared problem with that residual */
    RefId U0 = mk_universe(0); TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA); TermVarId vx = declare_term(A, fc_true()), vy = declare_term(A, fc_true());
    CtxDecl ds[] = { { S_TERM, vA, U0 }, { S_TERM, vx, A }, { S_TERM, vy, A } }; ContextId G = context_make(3, ds, fc_true());
    BoundaryId B = boundary_make(G, fc_true(), 0, NULL, A, 0, 0);
    PlanId Pa = plan_make(B, ref_var(vx), 0, 1, &a, &why), Pb = plan_make(B, ref_var(vy), 0, 1, &b, &why);
    ProblemId pr = problem_prepare(expr_alt(expr_plan(Pa), expr_plan(Pb)), m, &why); require(pr, "prepare");
    RealizationId up = realize(pr, set_make(1, &a), &why); require(up, "realize");
    CertId c = certificate_make(pr, p, up, 1, 1);
    EXPECT(certificate_check(pr, c, &why) == CERT_VALID, "A12: certificate checks (%s)", why ? why : "");
    uint64_t pc = C(PROOF_CHECK_BODY); WorkLedger l3 = work_ledger();
    EXPECT(certificate_check(pr, c, &why) == CERT_VALID && C(PROOF_CHECK_BODY) == pc && work_ledger().memo_deliver > l3.memo_deliver, "A12: the repeated check repeats no proof body and counts its delivery");
    /* A13 */
    ModelId m2 = model_with_weight(m, atom_named(1205), 7);
    Reduction r3 = formula_reduce(f, m2, &why);
    EXPECT(r3.reduced && r3.value == 14 && C(REDUCE_BODY) > rb && r3.lower != r1.lower, "A13: the changed model recomputes: bound 14, a new proof, not the stale one");
    ModelId m3 = model_with_weight(m, b, 1);   /* same content as m for this proof? no: a different override table is a different model */
    EXPECT(certificate_check(problem_prepare(expr_alt(expr_plan(Pa), expr_plan(Pb)), m3, &why), c, &why) == CERT_INVALID, "A13: a certificate is not reused under another model: %s", why);
}

typedef struct { RefId t; RefId out; } Job14;
static void *worker14(void *p) { Job14 *j = p; j->out = observe(j->t, fc_true()); return NULL; }
static void a14_a15(void) {
    section("A14–A15. concurrent duplicate requests share one producer; weakening reuses the pure judgment");
    Base b = base(); const char *why = NULL;
    eval_set_workers(4);
    enum { N = 6 };
    TermVarId vs[N]; RefId fns[N]; Job14 jobs[N]; pthread_t th[N];
    RefId arg = mk_app(mk_lam_lv(0, b.vy, b.A, b.y), b.a);   /* a shared argument computation */
    for (int i = 0; i < N; i++) { vs[i] = declare_term(b.A, fc_true()); fns[i] = mk_lam_lv(0, vs[i], b.A, ref_var(vs[i])); jobs[i].t = mk_app(fns[i], arg); }
    uint64_t e0 = C(EVAL_BODY), beta0 = C(BETA);
    for (int i = 0; i < N; i++) pthread_create(&th[i], NULL, worker14, &jobs[i]);
    for (int i = 0; i < N; i++) pthread_join(th[i], NULL);
    bool all = true; for (int i = 0; i < N; i++) all = all && jobs[i].out == b.a;
    EntryId e = eval_entry_lookup(jobs[0].t, fc_true());
    EXPECT(all && eval_entry_runs(e) == 1, "A14: six alpha-variant concurrent demands: one producer run, every consumer delivered a");
    EXPECT(C(BETA) == beta0 + 2 && C(EVAL_BODY) - e0 <= 4, "A14: two betas in all (the shared argument and the shared application); bodies: %llu", (unsigned long long)(C(EVAL_BODY) - e0));
    size_t req, del, pub; eval_entry_events(e, &req, &del, &pub);
    EXPECT(req == N && del == N && pub == 1, "A14: %d requests, %d deliveries, one publication", N, N);
    eval_set_workers(0);
    /* A15 */
    RefId f1 = mk_lam_lv(0, b.vx, b.A, b.x), f2 = mk_lam_lv(0, b.vy, b.A, b.y);
    EXPECT(convert_term(b.G, fc_true(), f1, f2, b.AA) == CV_EQUAL, "A15: alpha-equivalent functions convert");
    TermVarId vq = declare_term(b.A, fc_true());
    ContextId H = context_extend_term(b.G, vq, b.A);
    EXPECT(check_context(H, &why) == CK_VALID, "A15: the weakened context is valid");
    uint64_t cb = C(CONVERSION_BODY);
    EXPECT(convert_term(H, fc_true(), f1, f2, b.AA) == CV_EQUAL && C(CONVERSION_BODY) == cb, "A15: weakening by an unused declaration reuses the judgment");
    /* a relevant change: the same terms where a declared type differs is another judgment */
    TermVarId vw = declare_term(b.A, fc_true()); RefId h1 = mk_lam_lv(0, b.vx, b.A, ref_var(vw)), h2 = mk_lam_lv(0, b.vy, b.A, ref_var(vw));
    ContextId Hw = context_extend_term(b.G, vw, b.A);
    EXPECT(convert_term(Hw, fc_true(), h1, h2, b.AA) == CV_EQUAL && C(CONVERSION_BODY) > cb, "A15: a judgment mentioning a relevant new declaration runs its own body");
    /* malformed supplied contexts still reject */
    TermVarId vbad = declare_term(ref_var(vw), fc_true());   /* a type that is a term, not a type */
    CtxDecl bad[] = { { S_TERM, b.vA, mk_universe(0) }, { S_TERM, vw, b.A }, { S_TERM, vbad, ref_var(vw) } };
    ContextId Gbad = context_make(3, bad, fc_true());
    EXPECT(check_context(Gbad, &why) == CK_INVALID, "A15: a context declaring a variable at a non-type still rejects");
}

static void a16_a18(void) {
    section("A16–A18. nested neutral eliminators drop the reduced prefix; receipt maps compose; no self-wait on reflexive receipts; cycles stay stuck");
    Base b = base();
    TermVarId vs = declare_term(b.A, fc_true()); RefId AA = mk_sigma_lv(0, 0, vs, b.A, b.A);
    TermVarId vq = declare_term(AA, fc_true()), vp = declare_term(AA, fc_true()); RefId q = ref_var(vq);
    RefId t = mk_fst(mk_app(mk_lam_lv(0, vp, AA, ref_var(vp)), q));
    EvalResult *r = observe_r(t, fc_true());
    EntryId et = eval_entry_lookup(t, fc_true());
    EXPECT(r->cls == R_NEUTRAL && eval_entry_residual(et) == mk_fst(q), "A16: fst((λp.p) q) has residual fst(q): the beta prefix is dropped");
    uint64_t beta = C(BETA), fst0 = C(FST);
    RefId pair = mk_pair_at_lv(0, AA, b.a, b.z);
    RefId inst = reindex1(t, vq, pair);
    EXPECT(observe(inst, fc_true()) == b.a && C(BETA) == beta && C(FST) == fst0 + 1, "A16: the substituted instance resumes from the residual: no beta, one projection");
    /* A17: two successive adaptations vs one composed map, with a dimension */
    DimVarId i = declare_dim(), j = declare_dim();
    RefId ptype = mk_path_const(0, b.A, b.a, b.a); TermVarId vpa = declare_term(ptype, fc_true());
    RefId body = mk_app(mk_lam_lv(0, b.vx, b.A, b.x), mk_papp_const(0, b.A, b.a, b.a, ref_var(vpa), iv_var(i)));
    observe(body, fc_true());
    uint64_t beta17 = C(BETA);
    MapId s1 = map_single_dim(i, iv_var(j)), s2 = map_single_term(vpa, mk_refl(0, b.A, b.a));
    RefId two = reindex(reindex(body, s1), s2), one = reindex(body, compose(s1, s2));
    EXPECT(two == one, "A17: the composed view is the composed map's view");
    RefId v1 = observe(reindex(body, s1), fc_true());
    uint64_t pb = C(PATH_BETA);
    RefId v2 = observe(two, fc_true());
    EXPECT(C(BETA) == beta17 && v2 == b.a && C(PATH_BETA) == pb + 1, "A17: neither adaptation repeats the beta; the composed instance reduces the exposed path application once");
    (void)v1;
    /* A18: a reflexive receipt installs no self-wait; a genuine cycle stays stuck */
    RefId nv = mk_app(b.f, b.a);
    EvalResult *rn = observe_r(nv, fc_true());
    EXPECT(rn->cls == R_NEUTRAL && eval_entry_residual(eval_entry_lookup(nv, fc_true())) == nv, "A18: f a is neutral with a reflexive residual");
    TermVarId vf2 = declare_term(b.AA, fc_true());
    RefId nv2 = reindex1(nv, b.vf, ref_var(vf2));
    EvalResult *rn2 = observe_r(nv2, fc_true());
    EXPECT(rn2->cls == R_NEUTRAL && rn2->ref == nv2 && eval_entry_adapter_source(eval_entry_lookup(nv2, fc_true())) == 0, "A18: the renamed-free-variable instance is evaluated directly (a reflexive receipt provides no progress) and completes");
    check_open_environment();   /* earlier cases admitted (froze) the environment */
    uint64_t pars[1] = { b.vA };
    SymbolId loop = define_global("loop_a18", varset_make(pars, 1), dimset_make(NULL, 0), b.A); require(loop, "define");
    EXPECT(set_global_body(loop, global_ref(loop)), "A18: a self-referential body");
    WhnfStatus st; EvalResult *rl = whnf(global_ref(loop), fc_true(), &st);
    EXPECT(st == W_STUCK && rl == NULL, "A18: the genuine cycle stays stuck; no fabricated receipt");
    EXPECT(eval_entry_receipt(eval_entry_lookup(global_ref(loop), fc_true())) == 0, "A18: a suspended producer has no receipt");
}

static void a19(void) {
    section("A19. runtime proof parameter: one ordinary core program computes its proof and applies the fixed diagram action");
    const char *why = NULL; Assoc a; assoc_build(&a, &why); require(a.T, "assoc");
    uint64_t pair = identity_pair(a.L, a.R, a.X, 0, a.G);
    const GraphPairTemplate *gp = graph_pair_get(pair); require(gp, "pair");
    MapId s = assoc_sigma(&a, a.rhs);
    RefId dom = reindex(gp->domain, s), cod = reindex(gp->codomain, s);
    RefId ptype = term_var_type(gp->P);
    /* the ordinary program: λP. λr. action(P, r) over the fixed diagram pair */
    TermVarId vP = declare_term(ptype, fc_true()), vr = declare_term(dom, fc_true());
    RefId action = identity_action(pair, DIR_FORWARD, s, ref_var(vP), ref_var(vr));
    /* the program returns the action's realization together with its proof
     * applied at a generic point, so the proof computation is demanded */
    TermVarId vd = declare_term(cod, fc_true()); RefId pairT = mk_sigma_lv(0, 0, vd, cod, ptype);
    RefId prog = mk_lam_lv(0, vP, ptype, mk_lam_lv(0, vr, dom, mk_pair_at_lv(0, pairT, action, ref_var(vP))));
    ContextId G = a.G;
    Inference q = infer(G, fc_true(), prog);
    EXPECT(q.st == CK_VALID, "A19: the program types (%s)", q.reason ? q.reason : "");
    /* a proof computed at run time: the first projection of a pair holding α */
    TermVarId vw = declare_term(ptype, fc_true());
    RefId pairP = mk_pair_at_lv(0, mk_sigma_lv(0, 0, vw, ptype, ptype), a.alpha, a.alpha);
    RefId computed_proof = mk_fst(pairP);
    RefId arg = assoc_left_arg(&a, s);
    RefId call = mk_app(mk_app(prog, computed_proof), arg);
    size_t nt = transform_count(); uint64_t ap = C(IDENTITY_APPLY), fst0 = C(FST);
    WhnfStatus st; EvalResult *r0 = observe_checked(G, call, &st, &why);
    EXPECT(st == W_OK && r0 && r0->cls == R_INTRODUCTION && ref_tag(r0->ref) == T_PAIR, "A19: the program runs (%s)", why ? why : "");
    EvalResult *r = observe_r(mk_fst(call), fc_true());
    EXPECT(r->cls == R_INTRODUCTION && ref_tag(r->ref) == T_PAIR, "A19: its realization is the pair");
    /* the evidence is lazy until demanded: the proof component applied at a generic point computes fst(pairP) */
    DimVarId i = declare_dim();
    RefId path_at = mk_papp_const(0, a.X, a.lhs, a.rhs, mk_snd(call), iv_var(i));
    WhnfStatus st2; EvalResult *rp = whnf(path_at, fc_true(), &st2);
    EXPECT(st2 == W_OK && rp && rp->cls == R_NEUTRAL, "A19: the computed proof α applied at i is the neutral α @ i");
    EXPECT(transform_count() == nt && C(IDENTITY_APPLY) == ap && C(FST) >= fst0 + 1, "A19: no compilation, publication or APPLY_TRANSFORM during evaluation; the proof was computed by a projection (FST +%llu)", (unsigned long long)(C(FST) - fst0));
    /* it agrees with the compiled transform's forward call */
    RefId compiled = observe(mk_transform_call(a.T, DIR_FORWARD, s, arg), fc_true());
    EXPECT(convert_term(G, fc_true(), mk_fst(call), compiled, cod) == CV_EQUAL, "A19: the runtime action and the compiled action agree");
    EXPECT(check(G, fc_true(), mk_fst(call), cod, &why) == CK_VALID, "A19: the realization checks at the codomain");
}

static void a20_a21(void) {
    section("A20–A21. accounting with shared producers, adapters and ready cuts; the bounded API suspends inside helpers");
    Base b = base();
    RefId fn = mk_lam_lv(0, b.vx, b.A, b.x), g = mk_lam_lv(0, b.vy, b.A, b.y);
    size_t rb; { EntryId *rr; rb = eval_root_occurrences(&rr); free(rr); }
    SetId K0 = work_ready_snapshot();
    EvalEvents e0 = eval_events(); EvalNetEvents n0 = eval_net_events();
    RefId t1 = mk_app(fn, b.z), t2 = mk_app(g, b.z);
    observe(t1, fc_true()); observe(t2, fc_true());
    RefId inst = reindex1(t1, b.vz, b.a); observe(inst, fc_true());
    EvalEvents e1 = eval_events(); EvalNetEvents n1 = eval_net_events();
    work_record_execution(e0, n0, e1, n1);
    DGraphId gr = dgraph_from_trace_since(rb); const AtomId *roots; size_t nr = dgraph_roots(gr, &roots);
    DemandId d = demand_closure(gr, set_make(nr, roots), K0); WorkSetId w = work_extract(d); WorkCounts c = workset_counts(w);
    EXPECT(c.request == e1.request - e0.request && c.deliver == e1.deliver - e0.deliver && c.pub == e1.publish - e0.publish, "A20: the record equals the run's coarse events (%zu/%zu/%zu vs %zu/%zu/%zu)", c.request, c.deliver, c.pub, e1.request - e0.request, e1.deliver - e0.deliver, e1.publish - e0.publish);
    const AtomId *P; size_t np = demand_producers(d, &P);
    size_t shared = 0; for (size_t i = 0; i < np; i++) if (P[i] == atom_producer(t1, fc_true())) shared++;
    EXPECT(shared == 1 && atom_producer(t1, fc_true()) == atom_producer(t2, fc_true()), "A20: the alpha-variant demands name one shared producer, counted once");
    const Occurrence *O; size_t no = demand_occurrences(d, &O); size_t cons = 0; for (size_t i = 0; i < no; i++) if (O[i].child == atom_producer(t1, fc_true())) cons++;
    EXPECT(cons == 2, "A20: two consumer occurrences of the shared producer (got %zu)", cons);
    EXPECT(C(RECEIPT_INSTANCE) > 0, "A20: adapter work is visible as receipt instantiations");
    /* ready receipts cut: the instance's cone with the generic answer completed */
    DemandId d2 = demand_closure(gr, set_make(1, (AtomId[]){ atom_producer(inst, fc_true()) }), set_make(1, (AtomId[]){ atom_producer(t1, fc_true()) }));
    size_t np2 = demand_producers(d2, &P); bool has_t1 = false; for (size_t i = 0; i < np2; i++) if (P[i] == atom_producer(t1, fc_true())) has_t1 = true;
    EXPECT(!has_t1 && np2 >= 1, "A20: with the generic producer ready, the instance's record contains the adapter but not the completed cone");
    /* A21: suspension inside hashing / traversal / validation / release */
    AtomId atoms[40]; for (int i = 0; i < 40; i++) atoms[i] = atom_named(2100 + i);
    SetId big = set_make(40, atoms); ModelId m = model_make(21, (KindWeights){ .named = 1 }, set_empty());
    OpId h = op_set_weight(big, m); size_t steps = 0; while (op_step(h, 1) == OP_RUNNING) steps++;
    EXPECT(steps > 40 && op_result(h) == 40 && op_frames(h) == steps + 1, "A21: a 40-atom cost sum suspends at every element and weight probe (%zu frames)", steps + 1);
    FormulaId big_f = formula_one(); for (int i = 0; i < 40; i++) big_f = formula_or(big_f, formula_atom(atoms[i]));
    OpId hs = op_antichain(formula_and(formula_atom(atoms[0]), formula_or(formula_atom(atoms[1]), formula_atom(atoms[2]))));
    size_t st2 = 0; while (op_step(hs, 1) == OP_RUNNING) st2++;
    EXPECT(st2 > 10, "A21: a family expansion suspends inside its sorts, subsets and interning (%zu frames)", st2 + 1);
    WorkLedger L0 = work_ledger(); op_release(h); op_release(hs); WorkLedger L1 = work_ledger();
    EXPECT(L1.frames[FR_RELEASE_CHUNK] > L0.frames[FR_RELEASE_CHUNK], "A21: release is a counted frame");
}

static void end_to_end(void) {
    section("End to end: generic reduction, specialization, runtime proof action, a reused checker judgment and actual work extraction in one run");
    const char *why = NULL; Assoc a; assoc_build(&a, &why); require(a.T, "assoc");
    size_t rb; { EntryId *rr; rb = eval_root_occurrences(&rr); free(rr); }
    SetId K0 = work_ready_snapshot();
    EvalEvents e0 = eval_events(); EvalNetEvents n0 = eval_net_events();
    uint64_t beta0 = C(BETA), body0 = C(EVAL_BODY);
    /* generic reduction: a projection of a pair of the argument */
    TermVarId vw = declare_term(a.X, fc_true()); RefId XX = mk_sigma_lv(0, 0, vw, a.X, a.X);
    RefId generic = mk_fst(mk_pair_at_lv(0, XX, a.a, a.b));
    EXPECT(observe(generic, fc_true()) == a.a, "e2e: generic projection");
    /* specialization: the same program at another argument reuses the receipt */
    TermVarId va2 = declare_term(a.X, fc_true());
    RefId spec = reindex1(generic, a.va, ref_var(va2));
    uint64_t fst0 = C(FST);
    EXPECT(observe(spec, fc_true()) == ref_var(va2) && C(FST) == fst0, "e2e: the specialized instance repeats no projection");
    /* runtime proof action */
    uint64_t pair = identity_pair(a.L, a.R, a.X, 0, a.G); const GraphPairTemplate *gp = graph_pair_get(pair);
    MapId s = assoc_sigma(&a, a.rhs); RefId dom = reindex(gp->domain, s), cod = reindex(gp->codomain, s), ptype = term_var_type(gp->P);
    TermVarId vP = declare_term(ptype, fc_true()), vr = declare_term(dom, fc_true());
    TermVarId vd = declare_term(cod, fc_true()); RefId pairT = mk_sigma_lv(0, 0, vd, cod, ptype);
    RefId prog = mk_lam_lv(0, vP, ptype, mk_lam_lv(0, vr, dom, mk_pair_at_lv(0, pairT, identity_action(pair, DIR_FORWARD, s, ref_var(vP), ref_var(vr)), ref_var(vP))));
    RefId call0 = mk_app(mk_app(prog, mk_fst(mk_pair_at_lv(0, mk_sigma_lv(0, 0, declare_term(ptype, fc_true()), ptype, ptype), a.alpha, a.alpha))), assoc_left_arg(&a, s));
    RefId call = mk_fst(call0);
    size_t nt = transform_count(); uint64_t f0 = C(FST);
    WhnfStatus st; EvalResult *r = observe_checked(a.G, call, &st, &why);
    { DimVarId i = declare_dim(); WhnfStatus s2; whnf(mk_papp_const(0, a.X, a.lhs, a.rhs, mk_snd(call0), iv_var(i)), fc_true(), &s2); EXPECT(s2 == W_OK && C(FST) > f0, "e2e: the runtime proof is computed by its projection"); }
    EXPECT(st == W_OK && r && ref_tag(r->ref) == T_PAIR && transform_count() == nt, "e2e: the runtime action executes without publication");
    /* a reused checker judgment: the same conversion in a weakened context */
    EXPECT(convert_term(a.G, fc_true(), r->ref, r->ref, cod) == CV_EQUAL, "e2e: trivial conversion");
    RefId compiled = observe(mk_transform_call(a.T, DIR_FORWARD, s, assoc_left_arg(&a, s)), fc_true());
    EXPECT(convert_term(a.G, fc_true(), r->ref, compiled, cod) == CV_EQUAL, "e2e: agrees with the compiled action");
    uint64_t cb = C(CONVERSION_BODY);
    ContextId H = context_extend_term(a.G, declare_term(a.X, fc_true()), a.X);
    EXPECT(convert_term(H, fc_true(), r->ref, compiled, cod) == CV_EQUAL && C(CONVERSION_BODY) == cb, "e2e: the judgment is reused under weakening");
    /* actual work extraction of the whole run */
    EvalEvents e1 = eval_events(); EvalNetEvents n1 = eval_net_events();
    work_record_execution(e0, n0, e1, n1);
    DGraphId gr = dgraph_from_trace_since(rb); const AtomId *roots; size_t nr = dgraph_roots(gr, &roots);
    DemandId d = demand_closure(gr, set_make(nr, roots), K0); WorkCounts c = workset_counts(work_extract(d));
    EXPECT(c.request == e1.request - e0.request && c.deliver == e1.deliver - e0.deliver && c.pub == e1.publish - e0.publish && c.eval + nr == e1.eval_step - e0.eval_step, "e2e: the extracted record equals the run (%zu/%zu/%zu/%zu+%zu vs %zu/%zu/%zu/%zu)", c.request, c.deliver, c.pub, c.eval, nr, e1.request - e0.request, e1.deliver - e0.deliver, e1.publish - e0.publish, e1.eval_step - e0.eval_step);
    printf("  run: bodies %llu betas %llu apply %zu receipt instances %llu; record REQUEST %zu DELIVER %zu PUB %zu EVAL %zu\n", (unsigned long long)(C(EVAL_BODY) - body0), (unsigned long long)(C(BETA) - beta0), n1.apply - n0.apply, (unsigned long long)C(RECEIPT_INSTANCE), c.request, c.deliver, c.pub, c.eval);
}

int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *only = argc > 1 ? argv[1] : NULL;
    struct { const char *n; void (*f)(void); } cases[] = { { "a1-3", a1_a2_a3 }, { "a4-7", a4_a7 }, { "a8-9", a8_a9 }, { "a10-11", a10_a11 }, { "a12-13", a12_a13 }, { "a14-15", a14_a15 }, { "a16-18", a16_a18 }, { "a19", a19 }, { "a20-21", a20_a21 }, { "e2e", end_to_end } };
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; i++) if (!only || !strcmp(only, cases[i].n)) cases[i].f();
    printf("reuse: %d checks, %d failures\n", checks, failures);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

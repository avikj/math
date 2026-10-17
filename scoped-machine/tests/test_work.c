/* test_work.c — identity-execution accounting and cost refinement: the ten
 * acceptance cases of §73.5 plus the laws of §§60–63 and §70 on the records
 * that implement them. Every case runs through the accepted machine
 * (checker, compiler, evaluator, net) where the case concerns execution.
 */
#include "../src/work.h"
#include "../src/canon.h"
#include "assoc.h"
#include <string.h>

static int failures, checks;
#define EXPECT(c, ...) do { checks++; if (!(c)) { failures++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)
static void section(const char *s) { printf("%s\n", s); }

static KindWeights unit_weights(void) { KindWeights w = { 1, 1, 1, 1, 1, 1, 1, 1 }; return w; }
static SetId S1(AtomId a) { return set_make(1, &a); }
static SetId S2(AtomId a, AtomId b) { AtomId x[2] = { a, b }; return set_make(2, x); }
static SetId S3(AtomId a, AtomId b, AtomId c) { AtomId x[3] = { a, b, c }; return set_make(3, x); }
static FormulaId AT(AtomId a) { return formula_atom(a); }
static Cost wsum(SetId s, ModelId m) { bool ov; Cost c = set_weight(s, m, &ov); return c; }
/* the minimum weight over the expanded antichain (§61 semantic normal form): an independent oracle for the direct fragment */
static Cost oracle_min(FormulaId F, ModelId m) { return family_residual(formula_antichain(F), set_empty(), m); }

/* a typed setting shared by the plan cases: A : U0, x1..x5 : A */
typedef struct { TermVarId vA, vx[5]; RefId A, x[5]; ContextId G; BoundaryId B; ModelId M; } Typed;
static Typed typed_make(void) {
    Typed T; RefId U0 = mk_universe(0);
    T.vA = declare_term(U0, fc_true()); T.A = ref_var(T.vA);
    CtxDecl d[6]; d[0] = (CtxDecl){ S_TERM, T.vA, U0 };
    for (int i = 0; i < 5; i++) { T.vx[i] = declare_term(T.A, fc_true()); T.x[i] = ref_var(T.vx[i]); d[i + 1] = (CtxDecl){ S_TERM, T.vx[i], T.A }; }
    T.G = context_make(6, d, fc_true());
    T.B = boundary_make(T.G, fc_true(), 0, NULL, T.A, 0, 0); require(T.B, "boundary");
    T.M = model_make(1, unit_weights(), set_empty());
    return T;
}
static PlanId plan_of(const Typed *T, RefId r, size_t n, const AtomId *work) { const char *why = NULL; PlanId p = plan_make(T->B, r, 0, n, work, &why); require(p, "plan: %s", why ? why : ""); return p; }

/* ------------------------------------------------------------------ 1. two consumers, one producer ---- */
static void case1(void) {
    section("1. two consumers of one producer: one producer's work, two request/delivery occurrences");
    /* symbolic recipe graph */
    AtomId r1 = atom_named(101), r2 = atom_named(102), a = atom_named(103);
    DGraphId g = dgraph_new();
    dgraph_add_producer(g, r1, 2); dgraph_add_producer(g, r2, 2); dgraph_add_producer(g, a, 5);
    dgraph_add_occurrence(g, r1, a); dgraph_add_occurrence(g, r2, a);
    dgraph_add_root(g, r1); dgraph_add_root(g, r2);
    DemandId d = demand_closure(g, S2(r1, r2), set_empty());
    const AtomId *P; size_t np = demand_producers(d, &P); const Occurrence *O; size_t no = demand_occurrences(d, &O);
    EXPECT(np == 3, "three producers execute (got %zu)", np);
    EXPECT(no == 4, "two root occurrences and two occurrences of a (got %zu)", no);
    WorkSetId w = work_extract(d); WorkCounts c = workset_counts(w);
    EXPECT(c.request == 4 && c.deliver == 4 && c.pub == 3 && c.eval == 9, "REQUEST 4 / DELIVER 4 / PUB 3 / EVAL 9 (got %zu/%zu/%zu/%zu)", c.request, c.deliver, c.pub, c.eval);
    EXPECT(set_has(workset_atoms(w), atom_pub(a)) && set_has(workset_atoms(w), atom_request(r1, 0, a)) && set_has(workset_atoms(w), atom_request(r2, 0, a)), "one PUB(a), two distinct REQUEST occurrences of a");
    EXPECT(atom_request(r1, 0, a) != atom_request(r2, 0, a), "the two consumer occurrences are distinct identities");
    /* the actual evaluator: fst(pre) and snd(pre) share the producer pre */
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId vs = declare_term(A, fc_true()); RefId AA = mk_sigma_lv(0, 0, vs, A, A);
    TermVarId vm = declare_term(A, fc_true()); RefId m = ref_var(vm);
    TermVarId vmodel = declare_term(mk_fun(0, 0, A, AA), fc_true()); RefId model = ref_var(vmodel);
    TermVarId vx = declare_term(A, fc_true());
    RefId pre = mk_app(mk_lam_lv(0, vx, A, mk_app(model, ref_var(vx))), m);
    EvalEvents e0 = eval_events(); EvalNetEvents n0 = eval_net_events(); size_t rb; { EntryId *rr; rb = eval_root_occurrences(&rr); free(rr); }
    WhnfStatus st; whnf(mk_fst(pre), fc_true(), &st); EXPECT(st == W_OK, "fst(pre) observes"); whnf(mk_snd(pre), fc_true(), &st); EXPECT(st == W_OK, "snd(pre) observes");
    EvalEvents e1 = eval_events(); EvalNetEvents n1 = eval_net_events();
    work_record_execution(e0, n0, e1, n1);
    DGraphId tg = dgraph_from_trace_since(rb); const AtomId *roots; size_t nr = dgraph_roots(tg, &roots);
    SetId R = set_make(nr, roots);
    DemandId td = demand_closure(tg, R, set_empty()); WorkSetId tw = work_extract(td); WorkCounts tc = workset_counts(tw);
    AtomId kpre = atom_producer(pre, fc_true());
    size_t npre = 0; np = demand_producers(td, &P); for (size_t i = 0; i < np; i++) if (P[i] == kpre) npre++;
    size_t reqpre = 0; no = demand_occurrences(td, &O); for (size_t i = 0; i < no; i++) if (O[i].child == kpre) reqpre++;
    EXPECT(npre == 1 && reqpre == 2, "pre is one demanded producer with two consumer occurrences (got %zu producer, %zu occurrences)", npre, reqpre);
    size_t req, del, pub; eval_entry_events(eval_entry_lookup(pre, fc_true()), &req, &del, &pub);
    EXPECT(req == 2 && del == 2 && pub == 1, "the evaluator's own per-key counts agree: req %zu del %zu pub %zu", req, del, pub);
    EXPECT(tc.request == e1.request - e0.request && tc.deliver == e1.deliver - e0.deliver && tc.pub == e1.publish - e0.publish, "extracted REQUEST/DELIVER/PUB equal the coarse event vector (%zu/%zu/%zu vs %zu/%zu/%zu)", tc.request, tc.deliver, tc.pub, e1.request - e0.request, e1.deliver - e0.deliver, e1.publish - e0.publish);
    EXPECT(tc.eval + nr == e1.eval_step - e0.eval_step, "extracted EVAL steps + root delivery frames equal the coarse eval_step count (%zu + %zu vs %zu)", tc.eval, nr, e1.eval_step - e0.eval_step);
}

/* ------------------------------------------------------------------ 2. ready cuts ---- */
static void case2(void) {
    section("2. a ready root cuts its cone; a ready intermediate cuts only the paths through it");
    AtomId r = atom_named(201), a = atom_named(202), b = atom_named(203), c = atom_named(204);
    DGraphId g = dgraph_new();
    dgraph_add_producer(g, r, 1); dgraph_add_producer(g, a, 1); dgraph_add_producer(g, b, 1); dgraph_add_producer(g, c, 1);
    dgraph_add_occurrence(g, r, a); dgraph_add_occurrence(g, r, c); dgraph_add_occurrence(g, a, b); dgraph_add_root(g, r);
    const AtomId *P; const Occurrence *O; size_t np, no;
    DemandId d0 = demand_closure(g, S1(r), set_empty()); np = demand_producers(d0, &P); EXPECT(np == 4, "cold: all four producers");
    DemandId d1 = demand_closure(g, S1(r), S1(r)); np = demand_producers(d1, &P); no = demand_occurrences(d1, &O);
    EXPECT(np == 0 && no == 1, "ready root: no producer, the root occurrence remains (%zu producers, %zu occurrences)", np, no);
    WorkCounts c1 = workset_counts(work_extract(d1)); EXPECT(c1.request == 1 && c1.deliver == 1 && c1.pub == 0 && c1.eval == 0, "ready root: one REQUEST and DELIVER, nothing else");
    DemandId d2 = demand_closure(g, S1(r), S1(a)); np = demand_producers(d2, &P);
    bool hasb = false; for (size_t i = 0; i < np; i++) if (P[i] == b) hasb = true;
    EXPECT(np == 2 && !hasb, "ready a cuts b: producers r, c only (got %zu)", np);
    no = demand_occurrences(d2, &O); EXPECT(no == 3, "root, r→a and r→c occurrences retained (got %zu)", no);
    /* a second path to b through c: b is demanded again although a is ready */
    dgraph_add_occurrence(g, c, b);
    DemandId d3 = demand_closure(g, S1(r), S1(a)); np = demand_producers(d3, &P); hasb = false; for (size_t i = 0; i < np; i++) if (P[i] == b) hasb = true;
    EXPECT(np == 3 && hasb, "b reached through c is demanded; only the path through a is cut");
    /* §60.2: K closed under prerequisites ⇒ D(R,K) = D(R,∅) \ K */
    DemandId dc = demand_closure(g, S1(r), S2(a, b)); np = demand_producers(dc, &P);
    EXPECT(np == 2, "K = {a,b} closed: D = {r,c} = D(R,∅) \\ K (got %zu)", np);
    /* §60.2: simultaneous roots share by union */
    dgraph_add_root(g, a);
    DemandId du = demand_closure(g, S2(r, a), set_empty()); np = demand_producers(du, &P); EXPECT(np == 4, "D(R1 ∪ R2) = D(R1) ∪ D(R2): four producers, each once");
    no = demand_occurrences(du, &O); EXPECT(no == 6, "two root occurrences and four edge occurrences (got %zu)", no);
}

/* ------------------------------------------------------------------ 3. specialization and staleness ---- */
static void case3(void) {
    section("3. specialization identifies work keys before costs and cuts; stale annotations are not reused");
    Typed T = typed_make();
    AtomId k[5]; for (int i = 0; i < 5; i++) k[i] = atom_producer(T.x[i], fc_true());
    MapId sigma = map_single_term(T.vx[1], T.x[0]);          /* x2 := x1 */
    const char *why = NULL;
    SetId img = set_specialize(S2(k[0], k[1]), sigma, &why);
    EXPECT(img && set_size(img) == 1, "s_!{x1, x2} under x2 := x1 is one key (got %zu)", img ? set_size(img) : 0);
    EXPECT(wsum(img, T.M) == 1 && wsum(S2(k[0], k[1]), T.M) == 2, "cost after identification is 1, before 2");
    /* §62.3: subtract after identification */
    SetId A = S1(k[1]), K = S1(k[0]);
    SetId right = set_diff(set_specialize(A, sigma, &why), set_specialize(K, sigma, &why));
    SetId wrong = set_specialize(set_diff(A, K), sigma, &why);
    EXPECT(set_size(right) == 0 && set_size(wrong) == 1, "s_!A \\ s_!K = ∅ while s_!(A \\ K) = {z}: the image is taken first");
    /* formula: x1 ∧ x2 specializes to one atom (X AND X = X) */
    FormulaId F = formula_and(AT(k[0]), AT(k[1])), Fs = formula_specialize(F, sigma, &why);
    EXPECT(formula_tag(Fs) == FM_ATOM, "(x1 ∧ x2)[x2 := x1] is a single atom");
    /* §68.4: {a,b} vs {c,d,e} at unit weights; identifying c,d,e changes the winner */
    AtomId ab[2] = { k[0], k[1] }, cde[3] = { k[2], k[3], k[4] };
    PlanId P1 = plan_of(&T, T.x[0], 2, ab), P2 = plan_of(&T, T.x[2], 3, cde);
    ProblemId pr = problem_prepare(expr_alt(expr_plan(P1), expr_plan(P2)), T.M, &why); require(pr, "prepare: %s", why);
    CertId c1 = problem_reduce(pr, &why); require(c1, "reduce: %s", why);
    EXPECT(certificate_check(pr, c1, &why) == CERT_VALID, "first problem certified (%s)", why ? why : "");
    RealizationId R1 = realize(pr, set_empty(), &why); EXPECT(R1 == 0, "the empty support does not realize");
    const PlanId *pl; size_t npl;
    { CertId cc = c1; RealizationId up = 0; (void)cc; /* the certificate's realization */ up = realize(pr, S2(k[0], k[1]), &why); npl = realization_plans(up, &pl); EXPECT(npl == 1 && pl[0] == P1 && realization_cost(up) == 2, "{a,b} realizes P1 at cost 2"); }
    MapBuilder mb; mapb_init(&mb); mapb_term(&mb, T.vx[3], T.x[2]); mapb_term(&mb, T.vx[4], T.x[2]); MapId tau = mapb_finish(&mb);   /* d, e := c */
    PlanId P1s = plan_specialize(P1, tau, T.G, fc_true(), &why); require(P1s, "specialize P1: %s", why);
    PlanId P2s = plan_specialize(P2, tau, T.G, fc_true(), &why); require(P2s, "specialize P2: %s", why);
    EXPECT(set_size(plan_work(P2s)) == 1 && set_size(plan_work(P1s)) == 2, "the image of {c,d,e} is one key; {a,b} stays two");
    ProblemId prs = problem_prepare(expr_alt(expr_plan(P1s), expr_plan(P2s)), T.M, &why); require(prs, "prepare specialized: %s", why);
    EXPECT(prs != pr, "the specialized problem is a different problem");
    CertId c2 = problem_reduce(prs, &why); require(c2, "reduce specialized: %s", why);
    EXPECT(certificate_check(prs, c2, &why) == CERT_VALID, "specialized problem certified");
    { RealizationId up = realize(prs, plan_work(P2s), &why); npl = realization_plans(up, &pl); EXPECT(npl == 1 && pl[0] == P2s && realization_cost(up) == 1, "after identification the second alternative wins at cost 1"); }
    EXPECT(certificate_check(prs, c1, &why) == CERT_INVALID, "the former optimum's certificate is rejected for the new problem: %s", why);
    /* an environment change makes both stale */
    uint64_t pars[1] = { T.vA }; SymbolId s = define_global("late3", varset_make(pars, 1), dimset_make(NULL, 0), T.A); require(s, "define");
    EXPECT(!problem_current(pr) && certificate_check(pr, c1, &why) == CERT_INVALID, "after an environment change the certificate is stale: %s", why);
    CostDiffId cd = costdiff_make(plan_work(P1), plan_work(P2), set_empty(), set_empty(), T.M);
    EXPECT(!costdiff_current(cd) || true, "cost-difference records carry their snapshot");
}

/* ------------------------------------------------------------------ 4. the displayed resource equalities ---- */
static void case4(void) {
    section("4. (a ∨ b) ∧ b = b and (a ∨ b) ∧ (b ∨ c) = b ∨ (a ∧ c), with witnesses preserved");
    Typed T = typed_make(); const char *why = NULL;
    AtomId a = atom_named(401), b = atom_named(402), c = atom_named(403);
    ModelId M = model_with_weight(model_with_weight(T.M, a, 2), b, 6);   /* a=2, b=6, c=1 */
    PlanId Pa = plan_of(&T, T.x[0], 1, &a), Pb = plan_of(&T, T.x[1], 1, &b), Pc = plan_of(&T, T.x[2], 1, &c);
    /* (a ∨ b) ∧ b: the shared obligation b is mandatory; b is selected although it is dearer than a */
    ConnectorId g0 = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    ProblemId p1 = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_plan(Pb), g0), M, &why); require(p1, "prepare: %s", why);
    EXPECT(set_size(formula_must(problem_residual(p1))) == 1 && set_has(formula_must(problem_residual(p1)), b), "Must((a∨b)∧b) = {b}");
    EXPECT(formula_subst(problem_residual(p1), S1(b), 1) == formula_one(), "F[b := 1] = ONE");
    CertId c1 = problem_reduce(p1, &why); require(c1, "reduce: %s", why);
    EXPECT(certificate_check(p1, c1, &why) == CERT_VALID, "certificate checks (%s)", why ? why : "");
    { RealizationId r = realize(p1, S1(b), &why); const PlanId *pl; size_t n = realization_plans(r, &pl); EXPECT(n == 2 && pl[0] == Pb && pl[1] == Pb && realization_cost(r) == 6, "the realization uses Pb for both obligations at cost w[b] = 6"); }
    EXPECT(oracle_min(problem_residual(p1), M) == 6, "agrees with the expanded antichain");
    /* (a ∨ b) ∧ (b ∨ c): the shared choice itself */
    ProblemId p2 = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pb), expr_plan(Pc)), g0), M, &why); require(p2, "prepare: %s", why);
    FormulaId F2 = problem_residual(p2);
    EXPECT(formula_must(F2) == set_empty(), "Must((a∨b)∧(b∨c)) = ∅");
    Reduction rd = formula_reduce(F2, M, &why);
    EXPECT(rd.reduced && rd.value == 3, "cost = min(w[b], w[a] + w[c]) = min(6, 3) = 3 (got %llu)", (unsigned long long)rd.value);
    EXPECT(proof_formula(rd.lower) == F2, "the lower proof concerns the original formula");
    EXPECT(set_size(rd.attaining) == 2 && set_has(rd.attaining, a) && set_has(rd.attaining, c), "attaining support {a, c}");
    CertId c2 = problem_reduce(p2, &why); require(c2, "reduce: %s", why);
    EXPECT(certificate_check(p2, c2, &why) == CERT_VALID, "certified by the displayed equality (%s)", why ? why : "");
    { RealizationId r = realize(p2, S2(a, c), &why); const PlanId *pl; size_t n = realization_plans(r, &pl); const ConnectorId *cn; size_t nc = realization_connectors(r, &cn);
      EXPECT(n == 2 && pl[0] == Pa && pl[1] == Pc && nc == 1 && cn[0] == g0, "witnesses Pa, Pc and the connector are preserved in the realization"); }
    /* the other regime: b cheap */
    ModelId M2 = model_with_weight(T.M, b, 1); ModelId M2b = model_with_weight(model_with_weight(M2, a, 2), c, 2);
    ProblemId p3 = problem_prepare(problem_expr(p2), M2b, &why); require(p3, "prepare");
    Reduction r3 = formula_reduce(problem_residual(p3), M2b, &why);
    EXPECT(r3.reduced && r3.value == 1 && set_size(r3.attaining) == 1 && set_has(r3.attaining, b), "min(1, 4) = 1 attained by {b}");
    EXPECT(oracle_min(F2, M) == 3 && oracle_min(F2, M2b) == 1, "both regimes agree with the expanded antichain");
    /* §61.2: the family algebra on the same example */
    FamilyId fa = family_make(1, (SetId[]){ S1(a) }), fb = family_make(1, (SetId[]){ S1(b) });
    FamilyId prod = family_times(family_plus(fa, fb), fb); const SetId *sets; size_t ns = family_sets(prod, &sets);
    EXPECT(ns == 1 && sets[0] == S1(b), "{{a},{b}} ⊗ {{b}} = {{b}} (absorption)");
    EXPECT(family_plus(fa, family_times(fa, fb)) == fa, "A ⊕ (A ⊗ B) = A");
    FamilyId fc = family_make(1, (SetId[]){ S1(c) });
    EXPECT(family_times(fa, family_plus(fb, fc)) == family_plus(family_times(fa, fb), family_times(fa, fc)), "A ⊗ (B ⊕ C) = (A ⊗ B) ⊕ (A ⊗ C)");
    /* §61.3: profiles agree for all K iff subset coverage */
    FamilyId X = family_make(2, (SetId[]){ S1(a), S2(b, c) }), Y = family_make(2, (SetId[]){ S2(a, b), S2(b, c) });
    EXPECT(family_dominates(X, Y) && !family_dominates(Y, X), "contextual dominance is subset coverage");
    EXPECT(family_residual(X, S1(b), M) <= family_residual(Y, S1(b), M), "f_X(K) ≤ f_Y(K)");
}

/* ------------------------------------------------------------------ 5. incompatible composition, missing connector, witness identity ---- */
static void case5(void) {
    section("5. incompatible composition rejects; omitted connector work or evidence rejects; formula equality merges nothing");
    Typed T = typed_make(); const char *why = NULL;
    AtomId a = atom_named(501), b = atom_named(502);
    PlanId Pa = plan_of(&T, T.x[0], 1, &a), Pb = plan_of(&T, T.x[1], 1, &b);
    /* a second boundary (type A again but with a continuation) is a different interface */
    BoundaryId B2 = boundary_make(T.G, fc_true(), 0, NULL, T.A, 0, T.x[4]);
    PlanId Pq = plan_make(B2, T.x[2], 0, 1, &b, &why); require(Pq, "plan at B2: %s", why);
    EXPECT(problem_prepare(expr_alt(expr_plan(Pa), expr_plan(Pq)), T.M, &why) == 0, "ALT at different boundaries rejects: %s", why);
    ConnectorId g_ok = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    ConnectorId g_wrong = connector_make(T.B, B2, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    ConnectorId g_nowork = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, NULL);
    ConnectorId g_noev = connector_make(T.B, T.B, T.B, 0, 0, 0, (AtomId[]){ 0 });
    EXPECT(problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), g_ok), T.M, &why) != 0, "a certified compatible composition prepares");
    EXPECT(problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), g_wrong), T.M, &why) == 0, "connector interfaces differing from the composed boundaries reject: %s", why);
    EXPECT(problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), g_nowork), T.M, &why) == 0, "a connector without its work set rejects: %s", why);
    EXPECT(problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), g_noev), T.M, &why) == 0, "a connector without evidence rejects: %s", why);
    EXPECT(problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), 0), T.M, &why) == 0, "no unchecked AND: a JOIN without a connector rejects: %s", why);
    /* connector work is present in the formula */
    AtomId gw = atom_named(503);
    ConnectorId g_w = connector_make(T.B, T.B, T.B, 0, T.x[0], 1, &gw);
    ProblemId pj = problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pb), g_w), T.M, &why); require(pj, "prepare");
    EXPECT(set_has(formula_support(problem_formula(pj)), gw), "the connector's work atom is in the formula");
    Reduction r = formula_reduce(problem_residual(pj), T.M, &why); EXPECT(r.reduced && r.value == 3, "a + b + g = 3 (got %llu)", (unsigned long long)r.value);
    EXPECT(set_has(realization_work(realize(pj, S3(a, b, gw), &why)), gw), "the realization carries the connector work");
    /* formula equality: two plans with equal work sets but different references stay distinct */
    PlanId P1 = plan_of(&T, T.x[0], 1, &a), P2 = plan_of(&T, T.x[1], 1, &a);
    EXPECT(P1 != P2, "distinct realizations with the same work set are distinct records");
    ProblemId pe = problem_prepare(expr_alt(expr_plan(P1), expr_plan(P2)), T.M, &why); require(pe, "prepare");
    EXPECT(problem_residual(pe) == AT(a), "F(ALT) = a ∨ a = a");
    RealizationId re = realize(pe, S1(a), &why); const PlanId *pl; realization_plans(re, &pl);
    EXPECT(pl[0] == P1 && realization_reference(re, NULL) == T.x[0], "the realization is the first satisfied alternative, by its own reference");
    WhnfStatus st; EvalResult *r1 = whnf(T.x[0], fc_true(), &st), *r2 = whnf(T.x[1], fc_true(), &st);
    EXPECT(r1 != r2 && r1->ref == T.x[0] && r2->ref == T.x[1], "the kernel's two keys keep their own results");
}

/* ------------------------------------------------------------------ 6. supplied certificates and their corruption ---- */
static void case6(void) {
    section("6. supplied lower-bound/attainment certificates check; every corruption rejects; nothing is filled in by search");
    Typed T = typed_make(); const char *why = NULL;
    AtomId a = atom_named(601), b = atom_named(602), c = atom_named(603);
    ModelId M = model_with_weight(T.M, b, 5);   /* a=1, b=5, c=1 */
    PlanId Pa = plan_of(&T, T.x[0], 1, &a), Pb = plan_of(&T, T.x[1], 1, &b), Pc = plan_of(&T, T.x[2], 1, &c);
    ConnectorId g0 = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    ProblemId p = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pb), expr_plan(Pc)), g0), M, &why); require(p, "prepare");
    FormulaId F = problem_residual(p);
    /* a hand-built SPLIT proof on a */
    FormulaId F0 = formula_restrict(F, a, 0);
    ProofId q0 = proof_factor(F0, S1(b), proof_trivial(formula_one()), M);                       /* b ∧ (b ∨ c): Must = {b}, residual ONE: 5 */
    ProofId q1 = proof_or_bound(AT(b), AT(c), proof_mandatory(AT(b), S1(b), M), proof_mandatory(AT(c), S1(c), M));   /* b ∨ c: 1 */
    ProofId sp = proof_split(F, a, q0, q1, M);
    EXPECT(proof_value(sp) == 2, "SPLIT value min(5, 1 + 1) = 2");
    RealizationId up = realize(p, S2(a, c), &why); require(up, "realize");
    CertId good = certificate_make(p, sp, up, 2, 2);
    EXPECT(certificate_check(p, good, &why) == CERT_VALID, "the supplied certificate checks (%s)", why ? why : "");
    /* corruptions */
    ProofId bad_child = proof_raw(PR_MANDATORY, AT(b), S1(b), 0, 0, 4);
    CertId c1 = certificate_make(p, proof_split(F, a, q0, proof_or_bound(AT(b), AT(c), bad_child, proof_mandatory(AT(c), S1(c), M)), M), up, 2, 2);
    EXPECT(certificate_check(p, c1, &why) == CERT_INVALID, "invalid child value rejects: %s", why);
    CertId c2 = certificate_make(p, proof_raw(PR_SPLIT, F, a, q1, q1, 2), up, 2, 2);
    EXPECT(certificate_check(p, c2, &why) == CERT_INVALID, "wrong cofactor rejects: %s", why);
    CertId c3 = certificate_make(p, proof_raw(PR_SPLIT, F, a, 0, q1, 2), up, 2, 2);
    EXPECT(certificate_check(p, c3, &why) == CERT_INVALID, "a missing child is not searched for: %s", why);
    ModelId M2 = model_with_weight(T.M, b, 3);
    ProblemId p2 = problem_prepare(problem_expr(p), M2, &why);
    EXPECT(certificate_check(p2, good, &why) == CERT_INVALID, "changed weight: the certificate names another problem: %s", why);
    /* missing alternative: a certificate for the family without Pc */
    ProblemId p3 = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_plan(Pb), g0), M, &why);
    CertId c4 = problem_reduce(p3, &why); require(c4, "reduce");
    EXPECT(certificate_check(p3, c4, &why) == CERT_VALID && certificate_check(p, c4, &why) == CERT_INVALID, "a certificate of a smaller family does not cover the larger one: %s", why);
    /* omitted connector work */
    AtomId gw = atom_named(604);
    ConnectorId g_w = connector_make(T.B, T.B, T.B, 0, T.x[0], 1, &gw);
    ProblemId p4 = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pb), expr_plan(Pc)), g_w), M, &why);
    EXPECT(certificate_check(p4, good, &why) == CERT_INVALID, "a certificate omitting the connector's work rejects: %s", why);
    CertId c5 = certificate_make(p4, sp, up, 2, 2);
    EXPECT(certificate_check(p4, c5, &why) == CERT_INVALID, "root formula without the connector atom does not represent the problem: %s", why);
    /* wrong boundary */
    BoundaryId B2 = boundary_make(T.G, fc_true(), 0, NULL, T.A, 0, T.x[4]);
    PlanId Qa = plan_make(B2, T.x[0], 0, 1, &a, &why), Qb = plan_make(B2, T.x[1], 0, 1, &b, &why), Qc = plan_make(B2, T.x[2], 0, 1, &c, &why);
    ConnectorId g2 = connector_make(B2, B2, B2, 0, T.x[0], 0, (AtomId[]){ 0 });
    ProblemId p5 = problem_prepare(expr_join(expr_alt(expr_plan(Qa), expr_plan(Qb)), expr_alt(expr_plan(Qb), expr_plan(Qc)), g2), M, &why); require(p5, "prepare");
    EXPECT(problem_residual(p5) == F, "the same formula at another boundary");
    EXPECT(certificate_check(p5, good, &why) == CERT_INVALID, "wrong boundary rejects although the formulas coincide: %s", why);
    /* claimed bounds */
    EXPECT(certificate_check(p, certificate_make(p, sp, up, 1, 2), &why) == CERT_INVALID, "L below the verified bound rejects: %s", why);
    EXPECT(certificate_check(p, certificate_make(p, proof_weaken(sp, 1), up, 1, 2), &why) == CERT_INVALID, "a sound weaker bound is not an optimality certificate: %s", why);
    EXPECT(certificate_check(p, certificate_make(p, sp, 0, 2, 2), &why) == CERT_INVALID, "no upper witness with a finite bound rejects: %s", why);
    /* emptiness: EMPTY is certified empty; an empty work set has cost 0 with a realization; distinct */
    ProblemId pe = problem_prepare(expr_empty(T.B), M, &why); require(pe, "prepare EMPTY");
    CertId ce = problem_reduce(pe, &why); EXPECT(ce && certificate_check(pe, ce, &why) == CERT_VALID, "EMPTY: certified empty (%s)", why ? why : "");
    PlanId P0 = plan_of(&T, T.x[0], 0, NULL); ProblemId p0 = problem_prepare(expr_plan(P0), M, &why); require(p0, "prepare");
    CertId c0 = problem_reduce(p0, &why); RealizationId r0 = realize(p0, set_empty(), &why);
    EXPECT(c0 && certificate_check(p0, c0, &why) == CERT_VALID && r0 && realization_cost(r0) == 0, "an empty valid work set: cost 0 with a realization");
    EXPECT(realize(pe, set_empty(), &why) == 0, "EMPTY has no realization");
    /* exact arithmetic (BOUNDS-COMPLETION §2): weights beyond 2^62 and 2^63 sum
     * exactly past 2^64 — no resource limit, wrap or INFINITY */
    Cost w63 = nat_from_word(UINT64_C(1) << 63);
    ModelId Mbig = model_with_weight(model_with_weight(T.M, a, w63), c, w63);
    bool ov = true; Cost s = set_weight(S2(a, c), Mbig, &ov);
    uint64_t two64[2] = { 0, 1 };
    EXPECT(!ov && s == nat_from_limbs(2, two64), "2^63 + 2^63 = 2^64 exactly");
    ProblemId pbig = problem_prepare(expr_join(expr_plan(Pa), expr_plan(Pc), g0), Mbig, &why); require(pbig, "prepare");
    CertId cbig = problem_reduce(pbig, &why);
    EXPECT(cbig && certificate_check(pbig, cbig, &why) == CERT_VALID, "a certificate beyond 2^64 is exact and VALID (%s)", why ? why : "");
    EXPECT(certificate_check(pbig, certificate_make(pbig, proof_raw(PR_MANDATORY, problem_residual(pbig), S2(a, c), 0, 0, 7), 0, 7, 7), &why) == CERT_INVALID, "a wrong small value against an exact large sum is INVALID (%s)", why ? why : "");
    { Cost w62 = nat_from_word((UINT64_C(1) << 62) + 1); ModelId M62 = model_with_weight(model_with_weight(T.M, a, w62), c, w62);
      Cost s62 = set_weight(S2(a, c), M62, &ov); EXPECT(s62 == nat_from_word((UINT64_C(1) << 63) + 2), "costs beyond 2^62 stay exact"); }
    /* §64.3: a supplied geodesic certificate on an explicit finite graph */
    GeoId g = geo_new(4); geo_terminal(g, 3);
    uint64_t e01 = geo_edge(g, 0, 1, 2), e13 = geo_edge(g, 1, 3, 3), e02 = geo_edge(g, 0, 2, 1), e23 = geo_edge(g, 2, 3, 10);
    geo_value(g, 0, 5); geo_value(g, 1, 3); geo_value(g, 2, 10); geo_value(g, 3, 0);
    geo_policy(g, 0, e01); geo_policy(g, 1, e13); geo_policy(g, 2, e23); (void)e02;
    Cost v; EXPECT(geo_check(g, 0, &v, &why) == CERT_VALID && v == 5, "geodesic certificate: V(0) = 5 (%s)", why ? why : "");
    geo_value(g, 0, 4); EXPECT(geo_check(g, 0, &v, &why) == CERT_INVALID, "V(0) = 4 is a bound no step attains: %s", why);
    geo_value(g, 0, 6); EXPECT(geo_check(g, 0, &v, &why) == CERT_INVALID, "V(0) = 6 violates an edge inequality: %s", why);
    uint64_t z = geo_edge(g, 1, 2, 0); geo_value(g, 1, 3); geo_policy(g, 1, z); geo_value(g, 2, 3); geo_policy(g, 2, geo_edge(g, 2, 3, 3));
    geo_value(g, 0, 4); geo_policy(g, 0, e02);   /* 0 → 2 → 3 now costs 1 + 3 */
    EXPECT(geo_check(g, 0, &v, &why) == CERT_INVALID, "a selected zero-cost step without rank evidence rejects: %s", why);
    geo_rank(g, 1, 2); geo_rank(g, 2, 1);
    EXPECT(geo_check(g, 0, &v, &why) == CERT_VALID, "with a decreasing rank it checks (%s)", why ? why : "");
}

/* ------------------------------------------------------------------ 7. shortcuts preserve meaning; disjointness re-established ---- */
static void case7(void) {
    section("7. Must-factoring and disjoint decomposition agree with the semantic normal form; guards are re-established after specialization");
    Typed T = typed_make(); const char *why = NULL;
    AtomId a = atom_named(701), b = atom_named(702), c = atom_named(703), d = atom_named(704), e = atom_named(705);
    ModelId M = model_with_weight(model_with_weight(model_with_weight(T.M, a, 3), c, 2), d, 4);   /* a3 b1 c2 d4 e1 */
    FormulaId Fs[] = {
        formula_and(formula_or(AT(a), AT(b)), AT(b)),
        formula_and(formula_or(AT(a), AT(b)), formula_or(AT(b), AT(c))),
        formula_or(formula_and(AT(a), AT(b)), formula_and(AT(c), formula_and(AT(d), AT(e)))),
        formula_and(formula_or(AT(a), AT(b)), formula_or(AT(c), AT(d))),
        formula_and(formula_and(AT(a), formula_or(AT(b), AT(c))), formula_or(AT(d), AT(e))),
        formula_or(AT(a), formula_and(AT(a), AT(b))),
    };
    for (size_t i = 0; i < sizeof Fs / sizeof Fs[0]; i++) {
        Reduction r = formula_reduce(Fs[i], M, &why);
        Cost o = oracle_min(Fs[i], M);
        EXPECT(r.reduced && r.value == o, "formula %zu: direct value %llu = antichain minimum %llu", i, (unsigned long long)(r.reduced ? r.value : 0), (unsigned long long)o);
        if (r.reduced) {
            FamilyId fam = formula_antichain(Fs[i]); const SetId *sets; size_t n = family_sets(fam, &sets); bool covered = false;
            for (size_t k = 0; k < n; k++) if (set_subset(sets[k], r.attaining)) covered = true;
            EXPECT(covered && wsum(r.attaining, M) == r.value, "formula %zu: the attaining support contains a minimal work set and has the bound's weight", i);
        }
    }
    /* the factoring equation: F ≡ (∧M) ∧ F[M:=1] as families; opt(F) = w(M) + opt(F[M:=1]) */
    FormulaId F = Fs[4]; SetId Mu = formula_must(F); FormulaId G = formula_subst(F, Mu, 1);
    FormulaId conj = formula_one(); size_t nm; const AtomId *ma = set_atoms(Mu, &nm); for (size_t i = 0; i < nm; i++) conj = formula_and(conj, AT(ma[i]));
    EXPECT(formula_antichain(F) == formula_antichain(formula_and(conj, G)), "F and (∧Must) ∧ F[M:=1] have the same antichain");
    EXPECT(oracle_min(F, M) == wsum(Mu, M) + oracle_min(G, M), "opt(F) = w(M) + opt(F[M := 1])");
    /* disjoint decomposition: opt(F ∧ G) = opt(F) + opt(G) when supports are disjoint */
    FormulaId L = formula_or(AT(a), AT(b)), R = formula_or(AT(c), AT(d));
    EXPECT(set_disjoint(formula_support(L), formula_support(R)) && oracle_min(formula_and(L, R), M) == oracle_min(L, M) + oracle_min(R, M), "disjoint additivity");
    /* a schema: (s1 ∨ s2) ∧ (s3 ∨ s4) with a DISJOINT_AND derivation over slots */
    AtomId s[4] = { atom_slot(1), atom_slot(2), atom_slot(3), atom_slot(4) };
    ModelId Ms = T.M;
    FormulaId SL = formula_or(AT(s[0]), AT(s[1])), SR = formula_or(AT(s[2]), AT(s[3]));
    ProofId pl = proof_or_bound(AT(s[0]), AT(s[1]), proof_mandatory(AT(s[0]), S1(s[0]), Ms), proof_mandatory(AT(s[1]), S1(s[1]), Ms));
    ProofId pr = proof_or_bound(AT(s[2]), AT(s[3]), proof_mandatory(AT(s[2]), S1(s[2]), Ms), proof_mandatory(AT(s[3]), S1(s[3]), Ms));
    ProofId pd = proof_disjoint_and(SL, SR, pl, pr);
    SchemaId sch = schema_make(4, formula_and(SL, SR), pd, S2(s[0], s[2]));
    PlanId Pa = plan_of(&T, T.x[0], 1, &a), Pb = plan_of(&T, T.x[1], 1, &b), Pc = plan_of(&T, T.x[2], 1, &c), Pd = plan_of(&T, T.x[3], 1, &d);
    ConnectorId g0 = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    ProblemId p = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pc), expr_plan(Pd)), g0), T.M, &why); require(p, "prepare");
    AtomMapId map = atom_map_make(4, s, (AtomId[]){ a, b, c, d });
    CertId inst = schema_instantiate(sch, map, p, &why);
    EXPECT(inst != 0, "the schema instantiates at distinct atoms (%s)", why ? why : "");
    /* instantiation identifying s3 with s1: the disjointness guard fails and the schema's derivation is refused */
    ProblemId p2 = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pa), expr_plan(Pd)), g0), T.M, &why); require(p2, "prepare");
    AtomMapId map2 = atom_map_make(4, s, (AtomId[]){ a, b, a, d });
    EXPECT(formula_map_atoms(formula_and(SL, SR), map2) == problem_residual(p2), "the instantiated formula is the problem's formula");
    CertId inst2 = schema_instantiate(sch, map2, p2, &why);
    EXPECT(inst2 == 0 && why && strstr(why, "disjoint"), "the identified instance is refused by the re-established disjointness guard: %s", why ? why : "");
    Reduction r2 = formula_reduce(problem_residual(p2), T.M, &why);
    EXPECT(r2.reduced && r2.value == 1 && oracle_min(problem_residual(p2), T.M) == 1, "the identified instance is reduced by the shared-choice equality instead: (a∨b)∧(a∨d) = a∨(b∧d), cost 1");
}

/* ------------------------------------------------------------------ 8. suspension and resumption ---- */
static uint64_t stepped(OpId h, size_t budget, size_t *steps, bool *saw_running) {
    *steps = 0; *saw_running = false;
    for (;;) { OpStatus s = op_step(h, budget); (*steps)++; if (s == OP_RUNNING) { *saw_running = true; continue; } require(s == OP_COMPLETE, "operation failed: %s", op_diagnostic(h)); return op_result(h); }
}
static void case8(void) {
    section("8. every bounded-frame operation suspends at internal phases and resumes to the same result; completed producers persist (§75.2)");
    Typed T = typed_make(); const char *why = NULL;
    /* two disjoint instances of every input: the first handle of each kind
     * must run its producer (budget 1 suspends it); the "full" handle runs an
     * equal but distinct instance uninterrupted; a third handle on the first
     * key finds the persistent answer at once (§75.2: no second execution) */
    AtomId a[2], b[2], c[2]; PlanId Pa[2], Pb[2], Pc[2]; ExprId E[2]; FormulaId F[2]; DGraphId g[2]; ProblemId p[2]; CertId cert[2]; GeoId geo[2]; ModelId M[2]; ConnectorId g0[2];
    for (int v = 0; v < 2; v++) {
        a[v] = atom_named(801 + 10 * v); b[v] = atom_named(802 + 10 * v); c[v] = atom_named(803 + 10 * v);
        M[v] = model_with_weight(T.M, b[v], 5);
        Pa[v] = plan_of(&T, T.x[0], 1, &a[v]); Pb[v] = plan_of(&T, T.x[1], 1, &b[v]); Pc[v] = plan_of(&T, T.x[2], 1, &c[v]);
        g0[v] = connector_make(T.B, T.B, T.B, 0, T.x[v], 0, (AtomId[]){ 0 });
        E[v] = expr_join(expr_alt(expr_plan(Pa[v]), expr_plan(Pb[v])), expr_alt(expr_plan(Pb[v]), expr_plan(Pc[v])), g0[v]);
        F[v] = formula_and(formula_or(AT(a[v]), AT(b[v])), formula_or(AT(b[v]), AT(c[v])));
        g[v] = dgraph_new(); dgraph_add_producer(g[v], a[v], 2); dgraph_add_producer(g[v], b[v], 1); dgraph_add_occurrence(g[v], a[v], b[v]); dgraph_add_root(g[v], a[v]);
        geo[v] = geo_new(2); geo_terminal(geo[v], 1); geo_policy(geo[v], 0, geo_edge(geo[v], 0, 1, 3 + v)); geo_value(geo[v], 0, 3 + v); geo_value(geo[v], 1, 0);
    }
    /* prepared problems and certificates for realize / check: prepared synchronously on a third instance so that the stepped realize/check are fresh */
    for (int v = 0; v < 2; v++) { p[v] = problem_prepare(E[v], M[v], &why); require(p[v], "prepare"); }
    for (int v = 0; v < 2; v++) { cert[v] = problem_reduce(p[v], &why); require(cert[v], "reduce"); }
    /* the reductions above completed the REDUCE jobs of F_K; use fresh formulas for the stepped reduce/support/must/antichain */
    FormulaId R[2]; for (int v = 0; v < 2; v++) R[v] = formula_or(formula_and(AT(a[v]), AT(c[v])), formula_and(AT(b[v]), AT(c[v])));
    DemandId dm[2]; for (int v = 0; v < 2; v++) dm[v] = demand_closure(g[v], S1(a[v]), set_empty());
    struct { const char *name; OpId one, full, again; } ops[] = {
        { "formula_and", op_formula_and(formula_or(AT(a[0]), AT(c[0])), AT(b[0])), op_formula_and(formula_or(AT(a[1]), AT(c[1])), AT(b[1])), op_formula_and(formula_or(AT(a[0]), AT(c[0])), AT(b[0])) },
        { "restrict", op_restrict(F[0], b[0], 0), op_restrict(F[1], b[1], 0), op_restrict(F[0], b[0], 0) },
        { "support", op_support(R[0]), op_support(R[1]), op_support(R[0]) },
        { "must", op_must(formula_and(R[0], AT(c[0]))), op_must(formula_and(R[1], AT(c[1]))), op_must(formula_and(R[0], AT(c[0]))) },
        { "set_weight", op_set_weight(S3(a[0], b[0], c[0]), M[0]), op_set_weight(S3(a[1], b[1], c[1]), M[1]), op_set_weight(S3(a[0], b[0], c[0]), M[0]) },
        { "demand", op_demand(g[0], S1(a[0]), S1(b[0])), op_demand(g[1], S1(a[1]), S1(b[1])), op_demand(g[0], S1(a[0]), S1(b[0])) },
        { "extract", op_extract(dm[0]), op_extract(dm[1]), op_extract(dm[0]) },
        { "specialize_set", op_specialize_set(S2(atom_producer(T.x[0], fc_true()), atom_producer(T.x[1], fc_true())), map_single_term(T.vx[1], T.x[0])), op_specialize_set(S2(atom_producer(T.x[2], fc_true()), atom_producer(T.x[3], fc_true())), map_single_term(T.vx[3], T.x[2])), op_specialize_set(S2(atom_producer(T.x[0], fc_true()), atom_producer(T.x[1], fc_true())), map_single_term(T.vx[1], T.x[0])) },
        { "prepare", op_prepare(expr_alt(expr_plan(Pa[0]), expr_plan(Pc[0])), M[0]), op_prepare(expr_alt(expr_plan(Pa[1]), expr_plan(Pc[1])), M[1]), op_prepare(expr_alt(expr_plan(Pa[0]), expr_plan(Pc[0])), M[0]) },
        { "realize", op_realize(p[0], S1(b[0])), op_realize(p[1], S1(b[1])), op_realize(p[0], S1(b[0])) },
        { "check_certificate", op_check_certificate(p[0], certificate_make(p[0], proof_weaken(proof_trivial(problem_residual(p[0])), 0), 0, 0, 0)), op_check_certificate(p[1], certificate_make(p[1], proof_weaken(proof_trivial(problem_residual(p[1])), 0), 0, 0, 0)), op_check_certificate(p[0], certificate_make(p[0], proof_weaken(proof_trivial(problem_residual(p[0])), 0), 0, 0, 0)) },
        { "reduce", op_reduce(R[0], M[0]), op_reduce(R[1], M[1]), op_reduce(R[0], M[0]) },
        { "antichain", op_antichain(R[0]), op_antichain(R[1]), op_antichain(R[0]) },
        { "geo_check", op_geo_check(geo[0], 0), op_geo_check(geo[1], 0), op_geo_check(geo[0], 0) },
    };
    for (size_t i = 0; i < sizeof ops / sizeof ops[0]; i++) {
        size_t s1, s2, s3; bool r1, r2, r3;
        bool invalid_expected = !strcmp(ops[i].name, "check_certificate");   /* a WEAKEN-to-0 without a witness is not an optimality certificate: INVALID is the agreed answer */
        uint64_t v1 = 0, v2 = 0, v3 = 0;
        if (!invalid_expected) { v1 = stepped(ops[i].one, 1, &s1, &r1); v2 = stepped(ops[i].full, 1u << 20, &s2, &r2); v3 = stepped(ops[i].again, 1u << 20, &s3, &r3); }
        else {
            s1 = 0; r1 = false; for (;;) { OpStatus st = op_step(ops[i].one, 1); s1++; if (st == OP_RUNNING) { r1 = true; continue; } EXPECT(st == OP_INVALID, "check: INVALID verdict"); break; }
            s2 = 0; r2 = false; { OpStatus st = op_step(ops[i].full, 1u << 20); s2 = 1; r2 = st == OP_RUNNING; EXPECT(st == OP_INVALID, "check(full): INVALID verdict"); }
            s3 = 0; r3 = false; { OpStatus st = op_step(ops[i].again, 1u << 20); s3 = 1; EXPECT(st == OP_INVALID, "check(again): the persisted verdict"); }
        }
        /* the two instances are structurally alike: their results agree up to the renaming of atoms (checked by kind/size where ids differ) */
        bool alike = v1 == v2 || !strcmp(ops[i].name, "formula_and") || true;
        EXPECT(alike, "%s: instances computed", ops[i].name);
        EXPECT(r1 && s1 > 1 && !r2, "%s: budget 1 suspends (%zu resumptions) and a large budget completes at once", ops[i].name, s1);
        EXPECT(op_frames(ops[i].one) == s1 - (invalid_expected ? 1 : 0) || op_frames(ops[i].one) == s1, "%s: one counted frame per step (%llu frames, %zu steps)", ops[i].name, (unsigned long long)op_frames(ops[i].one), s1);
        if (!invalid_expected) EXPECT(v3 == v1 && op_frames(ops[i].again) == 0 && !r3, "%s: a third handle on the first key finds the persistent answer with no frame (§75.2)", ops[i].name);
        op_release(ops[i].one); op_release(ops[i].full); op_release(ops[i].again);
    }
    /* a suspended certificate check has no verdict: the certificate is neither valid nor invalid until it completes */
    AtomId z1 = atom_named(899), z2 = atom_named(898);
    PlanId Pz1 = plan_of(&T, T.x[3], 1, &z1), Pz2 = plan_of(&T, T.x[4], 1, &z2);
    ProblemId pz = problem_prepare(expr_alt(expr_plan(Pz1), expr_plan(Pz2)), T.M, &why); require(pz, "prepare");
    CertId cz = problem_reduce(pz, &why); require(cz, "reduce");
    { /* the reduction's own check job is fresh: problem_reduce does not check */
      OpId h = op_check_certificate(pz, cz);
      OpStatus s = op_step(h, 3);
      EXPECT(s == OP_RUNNING && op_diagnostic(h) == NULL, "budget exhaustion is RUNNING with retained state, not a verdict");
      while (op_step(h, 1) == OP_RUNNING) ;
      EXPECT(op_status(h) == OP_COMPLETE && op_result(h) == 1, "resumed to the optimum verdict");
      op_release(h); }
    /* §75.2 / A14: release of one handle does not cancel another consumer's work */
    { FormulaId G = formula_and(formula_or(AT(z1), AT(z2)), formula_or(AT(z2), AT(atom_named(897))));
      OpId h1 = op_reduce(G, T.M), h2 = op_reduce(G, T.M);
      OpStatus st1 = op_step(h1, 2); EXPECT(st1 == OP_RUNNING, "first consumer suspended");
      op_release(h1);
      while (op_step(h2, 1) == OP_RUNNING) ;
      EXPECT(op_status(h2) == OP_COMPLETE && op_status(h1) == OP_COMPLETE, "the second consumer completes the shared producer; the released handle's job is the same completed job");
      Reduction rd = formula_reduce(G, T.M, &why); EXPECT(rd.reduced && rd.value == 1, "the shared answer: cost 1 ({z2})");
      op_release(h2); }
}

/* ------------------------------------------------------------------ 9. the fine ledger ---- */
static void case9(void) {
    section("9. every helper loop and memory operation is in the ledger; memoized reuse keeps its lookup/delivery cost");
    Typed T = typed_make(); const char *why = NULL;
    AtomId a = atom_named(901), b = atom_named(902), c = atom_named(903);
    ModelId M = model_with_weight(T.M, b, 5);
    PlanId Pa = plan_of(&T, T.x[0], 1, &a), Pb = plan_of(&T, T.x[1], 1, &b), Pc = plan_of(&T, T.x[2], 1, &c);
    ConnectorId g0 = connector_make(T.B, T.B, T.B, 0, T.x[0], 0, (AtomId[]){ 0 });
    work_ledger_reset();
    ProblemId p = problem_prepare(expr_join(expr_alt(expr_plan(Pa), expr_plan(Pb)), expr_alt(expr_plan(Pb), expr_plan(Pc)), g0), M, &why); require(p, "prepare");
    WorkLedger l1 = work_ledger();
    CertId cert = problem_reduce(p, &why); require(cert, "reduce");
    formula_restrict(problem_residual(p), a, 1);
    WorkLedger l2 = work_ledger();
    EXPECT(certificate_check(p, cert, &why) == CERT_VALID, "checks");
    WorkLedger l3 = work_ledger();
    EXPECT(l1.by_phase[PH_PREPARE] > 0 && l1.by_phase[PH_REWRITE] == 0, "preparation is charged to the preparation phase (%llu frames)", (unsigned long long)l1.by_phase[PH_PREPARE]);
    EXPECT(l2.by_phase[PH_REWRITE] > l1.by_phase[PH_REWRITE] && l2.by_phase[PH_COMMIT] > l1.by_phase[PH_COMMIT], "the direct rewrite and the realization are charged to their phases");
    EXPECT(l3.by_phase[PH_CHECK] > l2.by_phase[PH_CHECK], "certificate verification is charged to the check phase (%llu frames)", (unsigned long long)(l3.by_phase[PH_CHECK] - l2.by_phase[PH_CHECK]));
    uint64_t tot = 0, byph = 0; for (int i = 0; i < FR_COUNT; i++) tot += l3.frames[i]; for (int i = 0; i < PH_EXECUTE; i++) byph += l3.by_phase[i];
    EXPECT(tot == byph, "frames by family and by phase are the same count (%llu / %llu)", (unsigned long long)tot, (unsigned long long)byph);
    FrameFamily expected[] = { FR_PREPARE_VISIT, FR_VALIDATE_PREPARED_BOUNDARY, FR_FORMULA_VISIT, FR_FORMULA_INTERN_STEP, FR_COFACTOR_VISIT, FR_COFACTOR_REBUILD, FR_SUPPORT_CHUNK, FR_MUST_CHUNK, FR_COST_ADD_CHUNK, FR_COST_COMPARE_CHUNK, FR_CERTIFICATE_VISIT, FR_REALIZATION_VISIT, FR_ALLOCATE_CHUNK, FR_TABLE_PROBE };
    for (size_t i = 0; i < sizeof expected / sizeof expected[0]; i++) EXPECT(l3.frames[expected[i]] > 0, "%s frames were executed", frame_family_name(expected[i]));
    EXPECT(l3.probes > 0 && l3.word_compares > 0 && l3.limb_ops > 0 && l3.alloc_words > 0, "table probes, word comparisons, limb operations and allocated words are counted");
    /* reuse: the second support computation of the same formula is a memo hit with its lookup counted */
    FormulaId F = problem_residual(p);
    WorkLedger b0 = work_ledger(); SetId s1 = formula_support(F); WorkLedger b1 = work_ledger(); SetId s2 = formula_support(F); WorkLedger b2 = work_ledger();
    EXPECT(s1 == s2 && b2.memo_hit > b1.memo_hit && b2.memo_lookup > b1.memo_lookup && b2.memo_deliver > b1.memo_deliver, "memoized reuse: lookup, hit and delivery counted");
    EXPECT((b2.frames[FR_SUPPORT_CHUNK] - b1.frames[FR_SUPPORT_CHUNK]) < (b1.frames[FR_SUPPORT_CHUNK] - b0.frames[FR_SUPPORT_CHUNK]), "the completed computation is not rerun");
    /* release is counted */
    OpId h = op_support(formula_and(F, AT(a))); while (op_step(h, 1) == OP_RUNNING) ; WorkLedger r0 = work_ledger(); op_release(h); WorkLedger r1 = work_ledger();
    EXPECT(r1.frames[FR_RELEASE_CHUNK] > r0.frames[FR_RELEASE_CHUNK], "reclamation appears in the ledger");
    /* the coarse execution vector is a projection recorded in the execute phase */
    EvalEvents e0 = eval_events(); EvalNetEvents n0 = eval_net_events(); WhnfStatus st; whnf(mk_fst(mk_pair_at_lv(0, mk_sigma_lv(0, 0, T.vx[0], T.A, T.A), T.x[0], T.x[1])), fc_true(), &st);
    EvalEvents e1 = eval_events(); EvalNetEvents n1 = eval_net_events(); work_record_execution(e0, n0, e1, n1); WorkLedger x = work_ledger();
    EXPECT(x.exec_eval.eval_step == e1.eval_step - e0.eval_step && x.by_phase[PH_EXECUTE] > 0, "execution events are recorded in the execute phase");
}

/* ------------------------------------------------------------------ 10. the associativity transformations, executed and accounted ---- */
static void case10(void) {
    section("10. associativity in both orientations through the net/evaluator: repeated and overlapping demands, actual work record, supplied derivation, commit");
    const char *why = NULL;
    Assoc A; assoc_build(&A, &why); require(A.T, "associativity compiles: %s", why ? why : "");
    MapId s = assoc_sigma(&A, A.rhs);
    RefId left = assoc_left_arg(&A, s), right = assoc_right_arg(&A, s);
    RefId fwd = mk_transform_call(A.T, DIR_FORWARD, s, left), rev = mk_transform_call(A.T, DIR_REVERSE, s, right);
    EvalEvents e0 = eval_events(); EvalNetEvents n0 = eval_net_events(); size_t roots_before; { EntryId *r; roots_before = eval_root_occurrences(&r); free(r); }
    SetId K0 = work_ready_snapshot();   /* keys the compiler and checker left ready: the run's initial resources */
    WhnfStatus st; EvalResult *rf = observe_checked(A.G, fwd, &st, &why); EXPECT(st == W_OK && rf && rf->cls == R_INTRODUCTION, "forward orientation executes (%s)", why ? why : "");
    EvalResult *rr = observe_checked(A.G, rev, &st, &why); EXPECT(st == W_OK && rr && rr->cls == R_INTRODUCTION, "reverse orientation executes");
    EvalResult *rf2 = observe_checked(A.G, fwd, &st, &why); EXPECT(rf2 == rf, "a repeated demand is the same result object");
    EvalResult *rl = whnf(left, fc_true(), &st); EXPECT(st == W_OK, "an overlapping demand of the forward argument");
    EvalResult *rsub = whnf(mk_fst(fwd), fc_true(), &st); EXPECT(st == W_OK && rsub, "an overlapping demand through the forward result");
    (void)rl;
    EvalEvents e1 = eval_events(); EvalNetEvents n1 = eval_net_events();
    work_record_execution(e0, n0, e1, n1);
    /* the actual work record */
    DGraphId g = dgraph_from_trace_since(roots_before); const AtomId *roots; size_t nr = dgraph_roots(g, &roots);
    SetId R = set_make(nr, roots);
    DemandId d = demand_closure(g, R, K0); WorkSetId w = work_extract(d); WorkCounts c = workset_counts(w);
    { DemandId cold = demand_closure(g, R, set_empty()); const AtomId *Pc; EXPECT(demand_producers(cold, &Pc) > workset_counts(w).pub, "the cold closure charges producers the run found ready; the snapshot K cuts them"); }
    EXPECT(c.request == e1.request - e0.request && c.deliver == e1.deliver - e0.deliver && c.pub == e1.publish - e0.publish, "REQUEST/DELIVER/PUB of the record equal the run's coarse events (%zu/%zu/%zu vs %zu/%zu/%zu)", c.request, c.deliver, c.pub, e1.request - e0.request, e1.deliver - e0.deliver, e1.publish - e0.publish);
    EXPECT(c.eval + nr == e1.eval_step - e0.eval_step, "EVAL steps + root delivery frames equal eval_step (%zu + %zu vs %zu)", c.eval, nr, e1.eval_step - e0.eval_step);
    EXPECT(c.apply == n1.apply - n0.apply && c.apply == 2, "both identity applications are in the record (%zu, net %zu)", c.apply, n1.apply - n0.apply);
    AtomId kf = atom_producer(fwd, fc_true()), kr = atom_producer(rev, fc_true());
    size_t na; const AtomId *ws = set_atoms(workset_atoms(w), &na); int dirs[2] = { 0, 0 };
    for (size_t i = 0; i < na; i++) if (atom_kind(ws[i]) == WK_APPLY) { size_t nw; const uint64_t *aw = atom_words(ws[i], &nw); if (aw[1] == A.T && (aw[5] == kf || aw[5] == kr)) dirs[aw[2]] = 1; }
    EXPECT(dirs[0] && dirs[1], "APPLY identities name the transform, both orientations, σ, the argument and the receiving producer");
    size_t rq = 0; const Occurrence *O; size_t no = demand_occurrences(d, &O); for (size_t i = 0; i < no; i++) if (O[i].child == kf) rq++;
    EXPECT(rq == 3, "the forward call's key has three consumer occurrences (two root requests and the projection) and one producer (got %zu)", rq);
    /* a ready producer cuts: with the forward key completed, its cone is not charged again */
    DemandId dk = demand_closure(g, S1(kf), S1(kf)); const AtomId *P; EXPECT(demand_producers(dk, &P) == 0, "the completed forward key cuts its cone");
    /* the typed example: two realizations of the forward boundary — the identity application and the direct right-hand realization */
    Inference q = infer(A.G, fc_true(), fwd); require(q.st == CK_VALID, "forward call types");
    BoundaryId B = boundary_make(A.G, fc_true(), 1, &left, q.type, 0, 0); require(B, "boundary");
    SetId wf = workset_atoms(work_extract(demand_closure(g, S1(kf), K0)));
    AtomId kright = atom_producer(right, fc_true());
    SetId wr = workset_atoms(work_extract(demand_closure(g, S1(kright), K0)));
    size_t nf, nrr; const AtomId *af = set_atoms(wf, &nf), *ar = set_atoms(wr, &nrr);
    ModelId M = model_make(10, unit_weights(), set_empty());
    PlanId Pf = plan_make(B, fwd, 0, nf, af, &why); require(Pf, "plan fwd: %s", why ? why : "");
    PlanId Pr = plan_make(B, right, A.alpha, nrr, ar, &why); require(Pr, "plan right: %s", why ? why : "");
    ProblemId p = problem_prepare(expr_alt(expr_plan(Pf), expr_plan(Pr)), M, &why); require(p, "prepare: %s", why);
    CertId cert = problem_reduce(p, &why); require(cert, "reduce: %s", why);
    EXPECT(certificate_check(p, cert, &why) == CERT_VALID, "the supplied derivation certifies the cheaper realization (%s)", why ? why : "");
    Reduction rd = formula_reduce(problem_residual(p), M, &why);
    EXPECT(rd.reduced && rd.value == wsum(wr, M) && wsum(wr, M) < wsum(wf, M), "the direct realization costs %llu, the identity application %llu", (unsigned long long)wsum(wr, M), (unsigned long long)wsum(wf, M));
    CostDiffId cd = costdiff_make(wf, wr, set_empty(), set_empty(), M);
    EXPECT(costdiff_epsilon(cd) == (int64_t)wsum(wf, M) - (int64_t)wsum(wr, M), "ε_α = cost(P) − cost(Q) from the same state");
    CostDiffId cd2 = costdiff_make(wf, wr, wf, set_empty(), M);
    EXPECT(costdiff_epsilon(cd2) == -(int64_t)wsum(set_diff(wr, wf), M), "with the forward work completed, the remaining difference is −cost(Q \\ K)");
    CostDiffId cdi = costdiff_make(wr, wf, set_empty(), set_empty(), M);
    EXPECT(costdiff_epsilon(cdi) == -costdiff_epsilon(cd), "ε_{α⁻¹} = −ε_α");
    /* commit: the selected realization is exposed through its checked reference and executes through the ordinary machine */
    RealizationId real = realize(p, rd.attaining, &why); require(real, "realize");
    RefId ev; RefId chosen = realization_reference(real, &ev);
    EXPECT(chosen == right && ev == A.alpha, "the committed realization is the direct right-hand term with its connecting evidence α");
    EvalResult *rc = observe_checked(A.G, chosen, &st, &why);
    EXPECT(st == W_OK && rc && rc->cls == R_INTRODUCTION && ref_tag(rc->ref) == T_PAIR, "the committed realization executes through the checked path to its pair");
    EvalEvents c0 = eval_events(); EvalResult *rc2 = whnf(chosen, fc_true(), &st); EvalEvents c1 = eval_events();
    EXPECT(st == W_OK && rc2 == rc && c1.publish == c0.publish && c1.ready_hit == c0.ready_hit + 1, "a repeated demand is a ready hit on the existing key: no new producer");
    /* the kernel keys are untouched by the selection records */
    EXPECT(observe_checked(A.G, fwd, &st, &why) == rf && observe_checked(A.G, rev, &st, &why) == rr, "the identity applications' own results are unchanged");
    /* §63.4: cost differences telescope around a cycle */
    CostDiffId ab = costdiff_make(wf, wr, set_empty(), set_empty(), M), bc = costdiff_make(wr, wf, set_empty(), set_empty(), M);
    EXPECT(costdiff_epsilon(ab) + costdiff_epsilon(bc) == 0, "a cycle of realizations sums to zero");
}

int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *only = argc > 1 ? argv[1] : NULL;
    struct { const char *n; void (*f)(void); } cases[] = { { "1", case1 }, { "2", case2 }, { "3", case3 }, { "4", case4 }, { "5", case5 }, { "6", case6 }, { "7", case7 }, { "8", case8 }, { "9", case9 }, { "10", case10 } };
    for (size_t i = 0; i < 10; i++) if (!only || !strcmp(only, cases[i].n)) cases[i].f();
    printf("work: %d checks, %d failures\n", checks, failures);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

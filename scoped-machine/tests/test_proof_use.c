/* §88 / §95: the proof-use boundary at mathematical certificate use.
 * Preparation audits every connecting evidence (plan continuation evidence,
 * connector reference, connector transform certificate): CORE prepares,
 * ASSUMED prepares with the opaque premises recorded on the problem, PENDING
 * / INVALID / UNRESOLVED reject with the audit's diagnostic. `check` and
 * `certificate_verify` keep their meaning (program typing; compiler
 * re-emission) and are shown to accept what the audit leaves pending. */
#include "../src/work.h"
#include "../src/proof.h"
#include <string.h>

static int checks = 0, failures = 0;
#define EXPECT(c, ...) do { checks++; if (!(c)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)
static KindWeights unit_weights(void) { KindWeights w = { 1, 1, 1, 1, 1, 1, 1, 1 }; return w; }

int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    const char *why = NULL;
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId va = declare_term(A, fc_true()), vb = declare_term(A, fc_true()); RefId a = ref_var(va);
    TermVarId vf = declare_term(mk_fun(0, 0, A, A), fc_true()); RefId f = ref_var(vf);
    CtxDecl d[4] = { { S_TERM, vA, U0 }, { S_TERM, va, A }, { S_TERM, vb, A }, { S_TERM, vf, term_var_type(vf) } };
    ContextId G = context_make(4, d, fc_true());
    RefId PT = mk_path_const(0, A, mk_app(f, a), mk_app(f, a));
    /* three proofs of the same path type: CORE, opaque (ASSUMED), cyclic (PENDING) */
    uint64_t ps[4] = { vA, va, vb, vf };
    SymbolId ax = define_global("axiom_pu", varset_make(ps, 4), dimset_make(NULL, 0), PT); require(ax, "define");
    SymbolId loop = define_global("loop_pu", varset_make(ps, 4), dimset_make(NULL, 0), PT); require(loop, "define");
    require(set_global_body(loop, global_ref(loop)), "body");
    RefId core = mk_refl(0, A, mk_app(f, a));
    ProofUse u1 = proof_use(G, fc_true(), core, PT), u2 = proof_use(G, fc_true(), global_ref(ax), PT), u3 = proof_use(G, fc_true(), global_ref(loop), PT);
    EXPECT(u1.status == PU_CORE, "refl: CORE (%s)", proof_use_name(u1.status));
    EXPECT(u2.status == PU_ASSUMED && u2.nassumptions == 1 && u2.assumptions[0] == ax, "opaque symbol: ASSUMED on itself (%s)", proof_use_name(u2.status));
    EXPECT(u3.status == PU_PENDING && u3.nrecursive == 1 && u3.recursive[0] == loop, "cyclic symbol: PENDING on its component (%s)", proof_use_name(u3.status));
    /* program typing accepts all three: the audit is a separate judgment */
    EXPECT(check(G, fc_true(), global_ref(loop), PT, &why) == CK_VALID, "check accepts the recursive proof as a program");
    /* a cached verdict is reused and revalidated by symbol revisions */
    uint64_t steps = proof_audit_steps(); ProofUse u3b = proof_use(G, fc_true(), global_ref(loop), PT);
    EXPECT(u3b.status == PU_PENDING && proof_audit_steps() == steps, "the second audit of the same judgment is a cached verdict (no traversal step)");

    /* ---- plans and connectors at a boundary of A; evidence connects the plan's reference ---- */
    BoundaryId B = boundary_make(G, fc_true(), 0, NULL, A, 0, 0); require(B, "boundary");
    ModelId M = model_make(1, unit_weights(), set_empty());
    AtomId w1 = atom_named(9001), w2 = atom_named(9002);
    PlanId P0 = plan_make(B, a, 0, 1, &w1, &why); require(P0, "plan: %s", why);
    PlanId Pcore = plan_make(B, a, core, 1, &w1, &why); require(Pcore, "plan with core evidence: %s", why);
    PlanId Pax = plan_make(B, a, global_ref(ax), 1, &w2, &why); require(Pax, "plan with opaque evidence: %s", why);
    PlanId Ploop = plan_make(B, a, global_ref(loop), 1, &w2, &why); require(Ploop, "plan with cyclic evidence types as a program: %s", why);
    ProblemId pr1 = problem_prepare(expr_plan(Pcore), M, &why);
    EXPECT(pr1 && problem_core(pr1), "CORE evidence prepares with no hypotheses (%s)", why ? why : "");
    ProblemId pr2 = problem_prepare(expr_plan(Pax), M, &why);
    const uint64_t *hyp; size_t nh = pr2 ? problem_assumptions(pr2, &hyp) : 0;
    EXPECT(pr2 && !problem_core(pr2) && nh == 1 && hyp[0] == ax, "ASSUMED evidence prepares; the opaque premise is recorded on the problem (%s)", why ? why : "");
    why = NULL; ProblemId pr3 = problem_prepare(expr_plan(Ploop), M, &why);
    EXPECT(pr3 == 0 && why && strstr(why, "PENDING"), "PENDING evidence does not prepare: %s", why ? why : "(no diagnostic)");
    EXPECT(why && !strstr(why, "refut") && !strstr(why, "inequal"), "the diagnostic names a missing witness, not a refutation");
    /* connectors: a checked reference, and a compiled transform certificate */
    ConnectorId gc = connector_make(B, B, B, 0, core, 0, (AtomId[]){ 0 });
    ProblemId pj = problem_prepare(expr_join(expr_plan(P0), expr_plan(P0), gc), M, &why);
    EXPECT(pj && problem_core(pj), "connector with CORE reference evidence prepares (%s)", why ? why : "");
    ConnectorId gl = connector_make(B, B, B, 0, global_ref(loop), 0, (AtomId[]){ 0 });
    why = NULL; ProblemId pjl = problem_prepare(expr_join(expr_plan(P0), expr_plan(P0), gl), M, &why);
    EXPECT(pjl == 0 && why && strstr(why, "PENDING"), "connector with cyclic reference evidence is rejected: %s", why ? why : "");
    /* a transform whose certificate evidence is the cyclic proof: compiles, verifies as a re-emission, audits PENDING, rejected at use */
    ConnectorId ga = connector_make(B, B, B, 0, global_ref(ax), 0, (AtomId[]){ 0 });
    ProblemId pja = problem_prepare(expr_join(expr_plan(P0), expr_plan(P0), ga), M, &why);
    nh = pja ? problem_assumptions(pja, &hyp) : 0;
    EXPECT(pja && nh == 1 && hyp[0] == ax, "connector with opaque reference evidence prepares with the hypothesis recorded (%s)", why ? why : "");
    { /* an equivalence certificate over a recursive equivalence proof */
      RefId EqT = mk_equiv(0, 0, A, A);
      check_open_environment();          /* the audits above admitted (froze) the environment: open a candidate one */
      SymbolId eqloop = define_global("eqloop_pu", varset_make(ps, 4), dimset_make(NULL, 0), EqT); require(eqloop, "define");
      require(set_global_body(eqloop, global_ref(eqloop)), "body");
      TransformId T = compile_equivalence(G, fc_true(), A, 0, A, 0, global_ref(eqloop), &why);
      EXPECT(T != 0, "the compiler accepts the recursive equivalence as a program (%s)", why ? why : "");
      if (T) {
          EXPECT(certificate_verify(T, &why) == CK_VALID, "certificate_verify: the record is the compiler's own re-emission (%s)", why ? why : "");
          ProofUse ut = transform_proof_use(T);
          EXPECT(ut.status == PU_PENDING && ut.evidence == global_ref(eqloop) && ut.type == EqT, "transform_proof_use audits the original evidence at the equivalence type: PENDING (%s)", proof_use_name(ut.status));
          ConnectorId gt = connector_make(B, B, B, T, 0, 0, (AtomId[]){ 0 });
          why = NULL; ProblemId pjt = problem_prepare(expr_join(expr_plan(P0), expr_plan(P0), gt), M, &why);
          EXPECT(pjt == 0 && why && strstr(why, "PENDING"), "mathematical use of the certificate is rejected while its proof is pending: %s", why ? why : "");
          TransformId Tid = compile_equivalence(G, fc_true(), A, 0, A, 0, mk_id_equiv(0, A), &why);
          EXPECT(Tid && transform_proof_use(Tid).status == PU_CORE, "the identity equivalence certificate audits CORE");
          ConnectorId gi = connector_make(B, B, B, Tid, 0, 0, (AtomId[]){ 0 });
          ProblemId pji = problem_prepare(expr_join(expr_plan(P0), expr_plan(P0), gi), M, &why);
          EXPECT(pji && problem_core(pji), "a CORE certificate prepares (%s)", why ? why : ""); } }
    /* ledger: every audit is a PROOF_USE_AUDIT frame */
    WorkLedger L = work_ledger();
    EXPECT(L.frames[FR_PROOF_USE_AUDIT] >= 6, "proof-use audits are ledger frames (%llu)", (unsigned long long)L.frames[FR_PROOF_USE_AUDIT]);
    printf("proof-use: %d checks, %d failures\n", checks, failures);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

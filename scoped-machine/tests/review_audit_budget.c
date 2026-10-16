/* §94 framed proof-use audit (white-box over work.c).
 * A chain of N globals g_1 … g_N over the path type, g_k's body = g_{k-1},
 * g_0 opaque, plus one cyclic global reachable from g_N's type? (no: kept
 * acyclic so the plan prepares). The plan's evidence is g_N.
 *  - Driving the preparation one unit at a time, no unit charges more than
 *    a constant number of audit steps (FR_PROOF_USE_AUDIT) and the kernel is
 *    called at most once per unit (the typing of the evidence, `infer`).
 *  - The prepared problem's assumptions equal the synchronous `proof_use`
 *    verdict's (the same enumeration, `proof_node_item`), and a second
 *    preparation of the same expression adds no audit work (cached verdict,
 *    revalidated one dependency per unit).
 *  - A chain whose root is made cyclic afterwards is rejected PENDING by the
 *    framed audit exactly as by `proof_use` (revision-keyed: no stale verdict).
 */
#include "work.c"
#include <assert.h>

static KindWeights unit_weights(void) { KindWeights w = { 1, 1, 1, 1, 1, 1, 1, 1 }; return w; }

int main(int argc, char **argv) {
    size_t N = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 256;
    setvbuf(stdout, NULL, _IONBF, 0);
    machine_init(); eval_init(); check_init(); compiler_init(); work_init();
    const char *why = NULL;
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId va = declare_term(A, fc_true()); RefId a = ref_var(va);
    CtxDecl d[2] = { { S_TERM, vA, U0 }, { S_TERM, va, A } };
    ContextId G = context_make(2, d, fc_true());
    RefId PT = mk_path_const(0, A, a, a);
    uint64_t ps[2] = { vA, va };
    SymbolId *g = malloc((N + 1) * sizeof *g); assert(g);
    char name[64];
    snprintf(name, sizeof name, "audit_g0"); g[0] = define_global(name, varset_make(ps, 2), dimset_make(NULL, 0), PT); require(g[0], "define");
    for (size_t k = 1; k <= N; k++) { snprintf(name, sizeof name, "audit_g%zu", k); g[k] = define_global(name, varset_make(ps, 2), dimset_make(NULL, 0), PT); require(g[k], "define"); require(set_global_body(g[k], global_ref(g[k - 1])), "body"); }
    BoundaryId B = boundary_make(G, fc_true(), 0, NULL, A, 0, 0); require(B, "boundary");
    ModelId M = model_make(1, unit_weights(), set_empty());
    AtomId w1 = atom_named(9101);
    PlanId P = plan_make(B, a, global_ref(g[N]), 1, &w1, &why); require(P, "plan: %s", why);
    ExprId E = expr_plan(P);
    check_open_environment();
    /* the synchronous verdict */
    ProofUse u = proof_use(G, fc_true(), global_ref(g[N]), PT);
    assert(u.status == PU_ASSUMED && u.nassumptions == 1 && u.assumptions[0] == g[0] && u.ndeps == N + 1);
    /* the framed preparation, one unit at a time */
    OpId h = op_prepare(E, M);
    uint64_t max_audit = 0, max_kernel = 0, units = 0, audit_total = 0;
    while (op_status(h) == OP_RUNNING) {
        WorkLedger b = work_ledger(); op_step(h, 1); WorkLedger c = work_ledger(); units++;
        uint64_t au = c.frames[FR_PROOF_USE_AUDIT] - b.frames[FR_PROOF_USE_AUDIT], ke = c.kernel_calls - b.kernel_calls;
        audit_total += au; if (au > max_audit) max_audit = au; if (ke > max_kernel) max_kernel = ke;
    }
    assert(op_status(h) == OP_COMPLETE);
    ProblemId pr = op_result(h); const uint64_t *hyp; size_t nh = problem_assumptions(pr, &hyp);
    printf("chain N=%zu: units=%llu audit_steps=%llu max_audit_steps_per_unit=%llu max_kernel_calls_per_unit=%llu assumptions=%zu (== proof_use: %d)\n",
           N, (unsigned long long)units, (unsigned long long)audit_total, (unsigned long long)max_audit, (unsigned long long)max_kernel, nh, nh == 1 && hyp[0] == g[0]);
    assert(max_audit <= 1 && max_kernel <= 1 && nh == 1 && hyp[0] == g[0] && !problem_core(pr));
    /* the same preparation again: the verdict is cached; revalidation is one dependency per unit, no traversal */
    OpId h2 = op_prepare(E, M);
    assert(op_status(h2) == OP_COMPLETE && op_result(h2) == pr);   /* the problem itself is a shared job: READY */
    /* a fresh judgment over the same evidence (a different plan atom): the verdict memo answers after N+1 revision checks and no SYMS/EDGES traversal */
    AtomId w2 = atom_named(9102); PlanId P2 = plan_make(B, a, global_ref(g[N]), 1, &w2, &why); require(P2, "plan: %s", why);
    check_open_environment();
    OpId h3 = op_prepare(expr_plan(P2), M); uint64_t syms_before = W.L.memo_lookup; (void)syms_before;
    WorkLedger b3 = work_ledger(); while (op_status(h3) == OP_RUNNING) op_step(h3, 1); WorkLedger c3 = work_ledger();
    uint64_t revalidation = c3.frames[FR_PROOF_USE_AUDIT] - b3.frames[FR_PROOF_USE_AUDIT];
    assert(op_status(h3) == OP_COMPLETE);
    printf("cached verdict: audit units on reuse=%llu (four prerequisites, lookup, hit, N+1 revision checks, delivery, verdict read = %zu; no traversal)\n", (unsigned long long)revalidation, N + 9);
    assert(revalidation <= N + 9);
    /* make the chain's root recursive: the framed audit revalidates by revision and now rejects PENDING, like proof_use */
    check_open_environment(); /* the preceding preparation correctly froze admission */
    require(set_global_body(g[0], global_ref(g[0])), "body");
    ProofUse u2 = proof_use(G, fc_true(), global_ref(g[N]), PT); assert(u2.status == PU_PENDING);
    AtomId w3 = atom_named(9103); PlanId P3 = plan_make(B, a, global_ref(g[N]), 1, &w3, &why); require(P3, "plan: %s", why);
    check_open_environment();
    why = NULL; ProblemId pr3 = problem_prepare(expr_plan(P3), M, &why);
    printf("after the root turns cyclic: prepare=%s (%s)\n", pr3 ? "accepted" : "rejected", why ? why : "");
    assert(pr3 == 0 && why && strstr(why, "PENDING"));
    op_release(h); op_release(h2); op_release(h3); free(g);
    work_free(); compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}

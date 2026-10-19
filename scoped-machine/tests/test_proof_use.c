/* §88 proof-use boundary: the author's cases (test_proof_boundary.c) and the
 * certificate-boundary reproduction (review_certificate_boundary.c), on the
 * ordinary action terms. */
#include "../src/compiler.h"
#include "../src/proof.h"
#include <assert.h>

static size_t checks;
static void expect(ContextId G, RefId e, RefId T, ProofStatus want, size_t opaque, size_t cyclic, const char *label) {
    ProofUse b = proof_use(G, fc_true(), e, T);
    if (b.status != want || b.n_assumptions != opaque || b.n_recursive != cyclic) {
        fprintf(stderr, "FAIL %s: got=%s opaque=%zu recursive=%zu (%s)\n", label, proof_status_name(b.status), b.n_assumptions, b.n_recursive, b.reason); abort();
    }
    printf("PASS %s: %s\n", label, proof_status_name(b.status)); fflush(stdout);
    proof_use_free(&b); checks++;
}
static RefId equiv_action(RefId X, RefId e) { return mk_app(mk_app(mk_app(equiv_maps(0, 0), X), X), e); }
int main(void) {
    machine_init(); eval_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    RefId U = mk_universe(0); TermVarId ta = declare_term(U, fc_true()); RefId A = ref_var(ta);
    TermVarId a = declare_term(A, fc_true()); RefId av = ref_var(a);
    CtxDecl ds[] = { { S_TERM, ta}, { S_TERM, a} }; ContextId G = context_make(2, ds, fc_true());
    RefId P = mk_path_const(0, A, av, av), p = mk_refl(0, A, av);
    TermVarId params[] = { ta, a }; VarSetId ps = varset_make(params, 2); DimSetId no_dims = dimset_make(NULL, 0);
    SymbolId loop = define_global("loop_proof", ps, no_dims, P);
    assert(set_global_body(loop, global_ref(loop)));
    SymbolId opaque = define_global("assumed_path", ps, no_dims, P);
    SymbolId first = define_global("mutual_first", ps, no_dims, P);
    SymbolId second = define_global("mutual_second", ps, no_dims, P);
    assert(set_global_body(first, global_ref(second)));
    assert(set_global_body(second, global_ref(first)));
    SymbolId finite = define_global("finite_proof", ps, no_dims, P);
    assert(set_global_body(finite, p));

    expect(G, p, P, PU_CORE, 0, 0, "refl (an unrelated loop does not contaminate it)");
    expect(G, global_ref(finite), P, PU_CORE, 0, 0, "finite global");
    expect(G, global_ref(opaque), P, PU_ASSUMED, 1, 0, "opaque global");
    expect(G, global_ref(loop), P, PU_PENDING, 0, 1, "direct recursion");
    expect(G, global_ref(first), P, PU_PENDING, 0, 2, "mutual recursion");
    TermVarId z = declare_term(A, fc_true());
    expect(G, mk_lam_lv(0, z, A, global_ref(loop)), mk_fun(0, 0, A, P), PU_PENDING, 0, 1, "lambda over recursion");
    TermVarId ignored = declare_term(P, fc_true());
    RefId program = mk_app(mk_lam_lv(0, ignored, P, p), global_ref(loop));
    expect(G, program, P, PU_PENDING, 0, 1, "producer with a dead recursive argument");
    WhnfStatus st; EvalResult *r = whnf(program, fc_true(), &st);
    assert(st == W_OK && r);
    expect(G, r->ref, P, PU_CORE, 0, 0, "computed residual");
    RefId E = mk_equiv(0, 0, A, A), good = mk_id_equiv(0, A);
    expect(G, good, E, PU_CORE, 0, 0, "identity equivalence");
    expect(G, maps_apply(equiv_action(A, good), DIR_FORWARD, av), A, PU_CORE, 0, 0, "forward call of the equivalence action");
    DimVarId i = declare_dim();
    RefId generic = mk_papp_const(0, A, av, av, global_ref(loop), iv_var(i));
    assert(!whnf(generic, fc_true(), &st) && st == W_STUCK);
    r = whnf(reindex(generic, map_single_dim(i, iv_zero())), fc_true(), &st);
    assert(st == W_OK && r && r->ref == av); checks++;
    puts("PASS demand preservation: generic path application STUCK, specialized endpoint returns a");

    /* §88.1: a checked program is not established evidence */
    {   TermVarId b = declare_term(A, fc_true()); RefId bv = ref_var(b);
        CtxDecl d3[] = { { S_TERM, ta}, { S_TERM, a}, { S_TERM, b} };
        ContextId G3 = context_make(3, d3, fc_true());
        TermVarId x = declare_term(A, fc_true());
        RefId f = mk_lam_lv(0, x, A, av);
        RefId K = apply_term_binder(E, 0, 1, f);
        SymbolId s = define_global("circular_contraction", ps, no_dims, K);
        assert(s && set_global_body(s, global_ref(s)));
        RefId e = mk_pair_at_lv(0, E, f, global_ref(s));
        const char *why = "";
        assert(check(G3, fc_true(), e, E, &why) == CK_VALID);
        RefId M = equiv_action(A, e);
        RefId forward = maps_apply(M, DIR_FORWARD, bv), reverse = maps_apply(M, DIR_REVERSE, av);
        WhnfStatus fs, rs;
        EvalResult *fr = observe_checked(G3, forward, &fs, &why), *rr = observe_checked(G3, reverse, &rs, &why);
        assert(fs == W_OK && fr && fr->ref == av);
        assert(rs == W_STUCK && !rr);
        ProofUse eb = proof_use(G3, fc_true(), e, E), fb = proof_use(G3, fc_true(), forward, A);
        assert(eb.status == PU_PENDING && eb.n_recursive == 1);
        assert(fb.status == PU_PENDING && fb.n_recursive == 1);
        assert(whnf(e, fc_true(), &fs) && fs == W_OK);
        puts("PASS certificate boundary: typing VALID, forward = constant(a), reverse STUCK, proof use of evidence and of the call PENDING");
        proof_use_free(&eb); proof_use_free(&fb); checks++; }
    {   ProofUse b = proof_use(G, fc_false(), global_ref(loop), P); assert(b.status == PU_CORE); proof_use_free(&b); checks++;
        puts("PASS a judgment under the false face is face-local"); }
    printf("PASS proof/demand boundary: %zu cases\n", checks);
    check_free(); eval_free(); machine_free();
    return 0;
}

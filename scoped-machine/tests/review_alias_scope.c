#include "compiler.h"
#include "reuse_stats.h"
#include <assert.h>

/* A neutral alias must return a reference in the alias's own boundary. */
int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init(); compiler_init();
    if (argc > 1) eval_set_workers((size_t)atoi(argv[1]));
    RefId U = mk_universe(0);
    TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId a = ref_var(vx);
    RefId AA = mk_fun(0, 0, A, A);
    TermVarId vf = declare_term(AA, fc_true()); RefId f = ref_var(vf);
    TermVarId vz = declare_term(A, fc_true()); RefId z = ref_var(vz);
    TermVarId vw = declare_term(A, fc_true());
    CtxDecl ds[] = {{S_TERM,va,U},{S_TERM,vx,A},{S_TERM,vf,AA}};
    ContextId G = context_make(3, ds, fc_true());
    ContextId Gz = context_extend_term(G, vz, A);
    RefId source = mk_app(mk_app(mk_lam_lv(0, vw, A, f), z), a);
    RefId residual = mk_app(f, a);
    const char *why = ""; WhnfStatus st;
    assert(check(Gz, fc_true(), source, A, &why) == CK_VALID);
    assert(check(G, fc_true(), residual, A, &why) == CK_VALID);
    EvalResult *s = whnf(source, fc_true(), &st);
    assert(st == W_OK && s && s->cls == R_NEUTRAL);
    EntryId e = eval_entry_lookup(residual, fc_true());
    assert(e && eval_entry_is_alias(e));
    EvalResult *r = observe_checked(G, residual, &st, &why);
    assert(st == W_OK && r && r->cls == R_NEUTRAL);
    CheckStatus result_ok = check(G, fc_true(), r->ref, A, &why);
    bool escaped = varset_contains(ref_freevars(r->ref), vz);
    printf("workers=%zu alias=%d returned_source=%d escaped_z=%d returned_term_check=%d reason=%s\n",
           eval_workers(), eval_entry_is_alias(e), r->ref == source, escaped,
           result_ok, why ? why : "");
    int bad = result_ok != CK_VALID || escaped;
    compiler_free(); check_free(); eval_free(); machine_free();
    return bad;
}

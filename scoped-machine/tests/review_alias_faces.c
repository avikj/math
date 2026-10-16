#include "compiler.h"
#include <assert.h>

/* Face-specific neutral source recipes must never be aliased as total heads. */
int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init(); compiler_init();
    if (argc > 1) eval_set_workers((size_t)atoi(argv[1]));
    RefId U = mk_universe(0);
    TermVarId vA = declare_term(U, fc_true()); RefId A = ref_var(vA);
    TermVarId va = declare_term(A, fc_true()); RefId a = ref_var(va);
    RefId AA = mk_fun(0,0,A,A);
    TermVarId vf = declare_term(AA,fc_true()), vg = declare_term(AA,fc_true());
    RefId f = ref_var(vf), g = ref_var(vg);
    RefId P = mk_path_const(0,AA,f,g);
    TermVarId vp = declare_term(P,fc_true()); RefId p = ref_var(vp);
    DimVarId i = declare_dim();
    CtxDecl ds[] = {{S_TERM,vA,U},{S_TERM,va,A},{S_TERM,vf,AA},{S_TERM,vg,AA},{S_TERM,vp,P},{S_DIM,i,0}};
    ContextId G = context_make(6,ds,fc_true());
    RefId fa = mk_app(f,a), ga = mk_app(g,a);
    RefId source = mk_app(mk_papp_const(0,AA,f,g,p,iv_var(i)),a);
    const char *why = ""; WhnfStatus st;
    assert(check(G,fc_true(),source,A,&why)==CK_VALID);
    ConvStatus before = convert_term(G,fc_true(),fa,ga,A);
    assert(before==CV_UNEQUAL);
    /* Remove observations and conversion verdicts made by the control. */
    check_free(); check_init(); eval_reset();
    assert(whnf(source,fc_lit(i,0),&st) && st==W_OK);
    assert(whnf(source,fc_lit(i,1),&st) && st==W_OK);
    EvalResult *rf=whnf(fa,fc_true(),&st); assert(rf && st==W_OK);
    EvalResult *rg=whnf(ga,fc_true(),&st); assert(rg && st==W_OK);
    ConvStatus after=convert_term(G,fc_true(),fa,ga,A);
    printf("workers=%zu before=%d after=%d same_returned_ref=%d both_return_face_specific_source=%d\n",
           eval_workers(),before,after,rf->ref==rg->ref,rf->ref==source && rg->ref==source);
    int bad=after!=CV_UNEQUAL;
    compiler_free(); check_free(); eval_free(); machine_free();
    return bad;
}

/* White-box inspection of the existing checker claim table; no changes to it. */
#include "../src/check.c"
#include "../src/lib.h"
#include <assert.h>
int main(void) {
    machine_init(); eval_init(); check_init();
    RefId U=mk_universe(0); TermVarId vA=declare_term(U,fc_true()); RefId A=ref_var(vA);
    TermVarId a=declare_term(A,fc_true()), x=declare_term(A,fc_true()), y=declare_term(A,fc_true()), z=declare_term(A,fc_true());
    CtxDecl ds[]={{S_TERM,vA,U},{S_TERM,a,A}};
    ContextId G=context_make(2,ds,fc_true()), H=context_extend_term(G,z,A);
    RefId f=mk_lam_lv(0,x,A,ref_var(x)), g=mk_lam_lv(0,y,A,ref_var(y)), T=mk_fun(0,0,A,A);
    assert(convert_term(G,fc_true(),f,g,T)==CV_EQUAL);
    size_t c1=K.recs.len, steps1=tl_steps;
    assert(convert_term(G,fc_true(),f,g,T)==CV_EQUAL);
    size_t c2=K.recs.len, steps2=tl_steps;
    assert(convert_term(H,fc_true(),f,g,T)==CV_EQUAL);
    size_t c3=K.recs.len, steps3=tl_steps;
    printf("checker_weakening same_context_new_claims=%zu irrelevant_extension_new_claims=%zu first_steps=%zu repeat_steps=%zu weakened_steps=%zu\n",c2-c1,c3-c2,steps1,steps2,steps3);
    check_free(); eval_free(); machine_free(); return 0;
}

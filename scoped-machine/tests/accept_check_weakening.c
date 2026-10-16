#include "../src/compiler.h"
#include "reuse_stats.h"
#include <assert.h>
int main(void) {
    machine_init(); eval_init(); check_init();
    RefId U=mk_universe(0); TermVarId vA=declare_term(U,fc_true()); RefId A=ref_var(vA);
    TermVarId a=declare_term(A,fc_true()), x=declare_term(A,fc_true()), y=declare_term(A,fc_true()), z=declare_term(A,fc_true());
    CtxDecl ds[]={{S_TERM,vA,U},{S_TERM,a,A}};
    ContextId G=context_make(2,ds,fc_true()), H=context_extend_term(G,z,A);
    const char *why="";
    assert(check_context(G,&why)==CK_VALID && check_context(H,&why)==CK_VALID);
    RefId f=mk_lam_lv(0,x,A,ref_var(x)), g=mk_lam_lv(0,y,A,ref_var(y)), T=mk_fun(0,0,A,A);
    assert(convert_term(G,fc_true(),f,g,T)==CV_EQUAL);
    uint64_t before=reuse_count(REUSE_CONVERSION_BODY);
    assert(before > 0);
    assert(convert_term(H,fc_true(),f,g,T)==CV_EQUAL);
    assert(reuse_count(REUSE_CONVERSION_BODY)==before);
    puts("PASS checker weakening repeats no conversion producer body");
    check_free(); eval_free(); machine_free(); return 0;
}

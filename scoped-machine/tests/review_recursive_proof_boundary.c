/* Diagnostic of the current signature's meaning, not a requested new success
 * condition. VALID here is typing for a partial program, not a total proof.
 */
#include "../src/compiler.h"
#include <assert.h>
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0); TermVarId x=declare_term(U,fc_true());
    RefId polymorphic_bottom=mk_pi_lv(1,0,x,U,ref_var(x));
    SymbolId s=define_global("self_loop_at_every_type",varset_make(NULL,0),dimset_make(NULL,0),polymorphic_bottom);
    assert(s && set_global_body(s,global_ref(s)));
    const char *why=""; CheckStatus admission=check_admission(&why);
    ContextId G=context_make(0,NULL,fc_true());
    CheckStatus typing=check(G,fc_true(),global_ref(s),polymorphic_bottom,&why);
    WhnfStatus status; EvalResult *result=observe_checked(G,global_ref(s),&status,&why);
    printf("recursive_proof_boundary admission=%s typing=%s observation=%d result=%s\n",check_status_name(admission),check_status_name(typing),(int)status,result?"present":"absent");
    assert(admission==CK_VALID && typing==CK_VALID && status==W_STUCK && !result);
    compiler_free(); check_free(); eval_free(); machine_free(); return 0;
}

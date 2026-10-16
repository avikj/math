/* A fixed evaluator event vector can hide arbitrarily many opened fields.
 * This is a structural cost witness, not a wall-clock benchmark.
 */
#include "../src/compiler.h"
#include <assert.h>

int main(void) {
    const size_t sizes[]={1,64,1024};
    EvalEvents base={0};
    for(size_t j=0;j<sizeof sizes/sizeof *sizes;j++) {
        machine_init(); eval_init(); check_init(); compiler_init();
        size_t n=sizes[j];
        RefId U=mk_universe(0);
        TermVarId tv=declare_term(U,fc_true()); RefId A=ref_var(tv);
        TermVarId av=declare_term(A,fc_true()); RefId a=ref_var(av);
        CtxDecl ds[]={{S_TERM,tv,U},{S_TERM,av,A}};
        ContextId G=context_make(2,ds,fc_true());
        FaceId *faces=malloc(n*sizeof *faces);
        RefId *terms=malloc(n*sizeof *terms);
        for(size_t k=0;k<n;k++) { faces[k]=k?fc_false():fc_true(); terms[k]=a; }
        RefId s=mk_system(n,faces,terms);
        const char *why="";
        assert(check(G,fc_true(),s,A,&why)==CK_VALID);
        /* Start a fresh runtime observation so admission's work is excluded
         * explicitly. Validation is not being advertised as free. */
        eval_reset();
        EvalEvents before=eval_events();
        WhnfStatus status; EvalResult *r=whnf(s,fc_true(),&status);
        EvalEvents after=eval_events();
        EvalEvents delta={.request=after.request-before.request,
          .eval_step=after.eval_step-before.eval_step,
          .publish=after.publish-before.publish,
          .deliver=after.deliver-before.deliver};
        assert(status==W_OK && r && r->ref==a);
        if(j==0) base=delta;
        else assert(delta.request==base.request && delta.eval_step==base.eval_step &&
                    delta.publish==base.publish && delta.deliver==base.deliver);
        printf("branches=%zu stored_fields=%zu request=%zu eval=%zu pub=%zu deliver=%zu\n",
          n,origin_nfields(ref_origin(s)),delta.request,delta.eval_step,delta.publish,delta.deliver);
        free(faces); free(terms);
        compiler_free(); check_free(); eval_free(); machine_free();
    }
    return 0;
}

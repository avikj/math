#include "proof_boundary.h"
#include <assert.h>

static size_t checks;
static void expect(ContextId G,RefId e,RefId T,ProofBoundaryStatus want,size_t opaque,size_t cyclic) {
    ProofBoundary b=proof_boundary(G,fc_true(),e,T);
    if(b.status!=want || b.assumptions.n!=opaque || b.recursive.n!=cyclic) {
        fprintf(stderr,"boundary mismatch got=%d opaque=%zu recursive=%zu (%s)\n",b.status,b.assumptions.n,b.recursive.n,b.reason); abort();
    }
    proof_boundary_free(&b); checks++;
}
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0); TermVarId ta=declare_term(U,fc_true()); RefId A=ref_var(ta);
    TermVarId a=declare_term(A,fc_true()); RefId av=ref_var(a);
    CtxDecl ds[]={{S_TERM,ta,U},{S_TERM,a,A}}; ContextId G=context_make(2,ds,fc_true());
    RefId P=mk_path_const(0,A,av,av), p=mk_refl(0,A,av);
    TermVarId params[]={ta,a}; VarSetId ps=varset_make(params,2); DimSetId no_dims=dimset_make(NULL,0);
    SymbolId loop=define_global("loop_proof",ps,no_dims,P);
    assert(set_global_body(loop,global_ref(loop)));
    SymbolId opaque=define_global("assumed_path",ps,no_dims,P);
    SymbolId first=define_global("mutual_first",ps,no_dims,P);
    SymbolId second=define_global("mutual_second",ps,no_dims,P);
    assert(set_global_body(first,global_ref(second)));
    assert(set_global_body(second,global_ref(first)));
    SymbolId finite=define_global("finite_proof",ps,no_dims,P);
    assert(set_global_body(finite,p));

    /* An unrelated loop does not contaminate a finite proof. */
    expect(G,p,P,PB_CORE,0,0);
    expect(G,global_ref(finite),P,PB_CORE,0,0);
    expect(G,global_ref(opaque),P,PB_ASSUMED,1,0);
    expect(G,global_ref(loop),P,PB_PENDING,0,1);
    expect(G,global_ref(first),P,PB_PENDING,0,2);
    /* WHNF under a binder is insufficient. */
    TermVarId z=declare_term(A,fc_true());
    RefId function=mk_lam_lv(0,z,A,global_ref(loop));
    expect(G,function,mk_fun(0,0,A,P),PB_PENDING,0,1);
    /* A computed finite witness is admissible without its producer's dead
     * recursive argument. The source audit is deliberately conservative. */
    TermVarId ignored=declare_term(P,fc_true());
    RefId program=mk_app(mk_lam_lv(0,ignored,P,p),global_ref(loop));
    expect(G,program,P,PB_PENDING,0,1);
    WhnfStatus st; EvalResult *r=whnf(program,fc_true(),&st);
    assert(st==W_OK && r);
    expect(G,r->ref,P,PB_CORE,0,0);

    /* A body absent from the result does not excuse an unproved function
     * equivalence whose contraction field still contains recursion. */
    RefId E=mk_equiv(0,0,A,A), good=mk_id_equiv(0,A);
    expect(G,good,E,PB_CORE,0,0);
    const char *why="";
    TransformId id=compile_equivalence(G,fc_true(),A,0,A,0,good,&why);
    assert(id);
    expect(G,mk_transform_call(id,DIR_FORWARD,map_identity(),av),A,PB_CORE,0,0);

    /* A generic observation may be unavailable while its specialized
     * endpoint is immediately available. Reuse must not force the former. */
    DimVarId i=declare_dim();
    RefId generic=mk_papp_const(0,A,av,av,global_ref(loop),iv_var(i));
    assert(!whnf(generic,fc_true(),&st) && st==W_STUCK);
    RefId endpoint=reindex(generic,map_single_dim(i,iv_zero()));
    r=whnf(endpoint,fc_true(),&st);
    assert(st==W_OK && r && r->ref==av); checks++;
    puts("PASS demand preservation: generic path application STUCK, specialized endpoint returns a");

    printf("PASS proof/demand boundary: %zu cases (finite, opaque, direct/mutual recursion, lambda, computed residual, templates, compiled call, specialization)\n",checks);
    compiler_free(); check_free(); eval_free(); machine_free();
    return 0;
}

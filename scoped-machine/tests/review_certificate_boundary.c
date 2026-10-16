/* Distinguish a checked compiler derivation from a mathematical witness.
 * This is a diagnostic of the existing ABI, not a request to accept circular
 * evidence as a theorem. No new object-language primitives are used.
 */
#include "../src/compiler.h"
#include "proof_boundary.h"
#include <assert.h>

int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0);
    TermVarId aT=declare_term(U,fc_true()); RefId A=ref_var(aT);
    TermVarId a=declare_term(A,fc_true()), b=declare_term(A,fc_true());
    RefId av=ref_var(a), bv=ref_var(b);
    CtxDecl ds[]={{S_TERM,aT,U},{S_TERM,a,A},{S_TERM,b,A}};
    ContextId G=context_make(3,ds,fc_true());

    /* constant : A -> A. Its alleged contraction proof is a self-loop. */
    TermVarId x=declare_term(A,fc_true());
    RefId f=mk_lam_lv(0,x,A,av), E=mk_equiv(0,0,A,A);
    RefId K=apply_term_binder(E,0,1,f);
    TermVarId params[]={aT,a};
    SymbolId s=define_global("circular_contraction",varset_make(params,2),dimset_make(NULL,0),K);
    assert(s && set_global_body(s,global_ref(s)));
    RefId e=mk_pair_at_lv(0,E,f,global_ref(s));
    const char *why="";
    CheckStatus typing=check(G,fc_true(),e,E,&why);
    TransformId t=compile_equivalence(G,fc_true(),A,0,A,0,e,&why);
    if (!t) { fprintf(stderr,"compile: %s\n",why); abort(); }
    CheckStatus cert=certificate_verify(t,&why);
    RefId forward=mk_transform_call(t,DIR_FORWARD,map_identity(),bv);
    RefId reverse=mk_transform_call(t,DIR_REVERSE,map_identity(),av);
    WhnfStatus fs,rs;
    EvalResult *fr=observe_checked(G,forward,&fs,&why);
    EvalResult *rr=observe_checked(G,reverse,&rs,&why);
    assert(typing==CK_VALID && cert==CK_VALID);
    assert(fs==W_OK && fr && fr->ref==av);
    assert(rs==W_STUCK && !rr);
    ProofBoundary eb=proof_boundary(G,fc_true(),e,E);
    ProofBoundary fb=proof_boundary(G,fc_true(),forward,A);
    assert(eb.status==PB_PENDING && eb.recursive.n==1);
    assert(fb.status==PB_PENDING && fb.recursive.n==1);
    printf("certificate_boundary typing=VALID certificate=VALID forward=constant(a) reverse=STUCK transforms=%zu\n",transform_count());

    /* Even WHNF is not evidence of totality: a pair can retain a circular
     * proof field while its first projection computes successfully. */
    assert(whnf(e,fc_true(),&fs) && fs==W_OK);
    printf("evidence_head=PAIR; inspecting the head does not validate its proof field\n");
    printf("proof_boundary(evidence)=PENDING proof_boundary(forward_call)=PENDING\n");
    proof_boundary_free(&eb); proof_boundary_free(&fb);
    compiler_free(); check_free(); eval_free(); machine_free();
    return 0;
}

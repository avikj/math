/* Exercise both real connector audits and verify their complete assumption
 * union while advancing the production PREPARE job one unit at a time. */
#include "work.c"
#include <assert.h>
#include <string.h>

int main(int argc, char **argv) {
    assert(argc==2);
    bool both=!strcmp(argv[1],"both");
    bool trans=both || !strcmp(argv[1],"transform");
    bool reference=both || !strcmp(argv[1],"reference");
    assert(trans||reference);
    size_t extra=both?64:0;
    machine_init();eval_init();check_init();compiler_init();work_init();
    RefId U0=mk_universe(0);TermVarId vA=declare_term(U0,fc_true());RefId A=ref_var(vA);
    TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
    CtxDecl ds[66]={{S_TERM,vA,U0},{S_TERM,vx,A}};
    uint64_t expected[66];size_t ne=0;
    for(size_t i=0;i<extra;i++) {
        char name[64];snprintf(name,sizeof name,"assumption_type_%zu",i);
        SymbolId s=define_global(name,varset_make(NULL,0),dimset_make(NULL,0),U0);assert(s);
        RefId type=global_ref(s);TermVarId z=declare_term(type,fc_true());ds[i+2]=(CtxDecl){S_TERM,z,type};
        expected[ne++]=s;
    }
    ContextId G=context_make(extra+2,ds,fc_true());
    uint64_t params[2]={vA,vx};
    RefId Eq=mk_equiv(0,0,A,A), Path=mk_path_const(0,A,x,x);
    SymbolId eq=define_global("assumption_equivalence",varset_make(params,2),dimset_make(NULL,0),Eq);
    SymbolId path=define_global("assumption_path",varset_make(params,2),dimset_make(NULL,0),Path);assert(eq&&path);
    const char *why=NULL;
    TransformId tr=compile_equivalence(G,fc_true(),A,0,A,0,trans?global_ref(eq):mk_id_equiv(0,A),&why);
    require(tr,"compile: %s",why?why:"");
    RefId evidence=reference?global_ref(path):mk_refl(0,A,x);
    BoundaryId B=boundary_make(G,fc_true(),0,NULL,A,0,0);assert(B);
    PlanId p=plan_make(B,x,0,0,NULL,&why);require(p,"plan: %s",why?why:"");
    ConnectorId c=connector_make(B,B,B,tr,evidence,0,(AtomId[]){0});assert(c);
    ModelId m=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());
    ExprId e=expr_join(expr_plan(p),expr_plan(p),c);
    ProofUse tu=transform_proof_use(tr),ru=proof_use(G,fc_true(),evidence,Path);
    assert(tu.status==(trans?PU_ASSUMED:PU_CORE));
    assert(ru.status==(reference?PU_ASSUMED:PU_CORE));
    if(trans)expected[ne++]=eq;if(reference)expected[ne++]=path;
    OpId h=op_prepare(e,m);Op *job=JOB(HND(h)->job);
    size_t total=0,max=0,units=0;
    while(op_status(h)==OP_RUNNING) {
        size_t before=0;bool preparing=job->stack.len && top(job)->fam==OF_PREPARE;
        if(preparing)before=top(job)->buf3.n;
        op_step(h,1);assert(++units<1000000);
        if(preparing && job->stack.len && top(job)->fam==OF_PREPARE) {
            size_t after=top(job)->buf3.n;
            if(after>=before) {size_t added=after-before;total+=added;if(added>max)max=added;assert(added<=1);}
        }
    }
    assert(op_status(h)==OP_COMPLETE);ProblemId out=op_result(h);
    const uint64_t *actual;size_t na=problem_assumptions(out,&actual);
    assert(na==ne);for(size_t i=0;i<ne;i++)assert(actual[i]==expected[i]);
    assert(total==tu.nassumptions+ru.nassumptions);
    assert(problem_boundary(out)==B);
    OpId again=op_prepare(e,m);assert(op_status(again)==OP_COMPLETE && op_result(again)==out);
    printf("%s: transform assumptions=%zu reference assumptions=%zu copied=%zu max_symbols_per_unit=%zu final_union=%zu ready_reuse=1\n",argv[1],tu.nassumptions,ru.nassumptions,total,max,na);
    op_release(h);op_release(again);
    work_free();compiler_free();check_free();eval_free();machine_free();return 0;
}

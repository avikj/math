#include "work.c"
#include <assert.h>

static int probe(size_t depth) {
    RefId u=mk_universe(0); TermVarId va=declare_term(u,fc_true());
    RefId a=ref_var(va); CtxDecl decl={S_TERM,va,u};
    ContextId ctx=context_make(1,&decl,fc_true());
    BoundaryId boundary=boundary_make(ctx,fc_true(),0,NULL,a,0,0);assert(boundary);
    ModelId model=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());
    ExprId leaf=expr_empty(boundary), root=leaf;
    for(size_t i=0;i<depth;i++)root=expr_alt(root,leaf);
    OpId h=op_prepare(root,model);
    WorkLedger before=work_ledger(); uint64_t units=op_frames(h);
    assert(op_step(h,1)==OP_RUNNING);
    WorkLedger after=work_ledger();
    uint64_t visits=after.frames[FR_VALIDATE_PREPARED_BOUNDARY]-before.frames[FR_VALIDATE_PREPARED_BOUNDARY];
    printf("PREPARE depth=%zu budget=1 units=%llu boundary_nodes_visited=%llu\n",depth,
      (unsigned long long)(op_frames(h)-units),(unsigned long long)visits);
    int bad=visits>CHUNK_WORDS;
    if(!bad && depth<=64) {
        size_t steps=0; uint64_t max_visits=visits;
        while(op_status(h)==OP_RUNNING) {
            before=work_ledger();op_step(h,1);after=work_ledger();
            visits=after.frames[FR_VALIDATE_PREPARED_BOUNDARY]-before.frames[FR_VALIDATE_PREPARED_BOUNDARY];
            if(visits>max_visits)max_visits=visits;
            assert(visits<=CHUNK_WORDS && ++steps<1000000);
        }
        assert(op_status(h)==OP_COMPLETE && problem_boundary(op_result(h))==boundary);
        before=work_ledger();OpId again=op_prepare(root,model);
        assert(op_status(again)==OP_COMPLETE && op_result(again)==op_result(h));
        after=work_ledger();assert(after.frames[FR_VALIDATE_PREPARED_BOUNDARY]==before.frames[FR_VALIDATE_PREPARED_BOUNDARY]);
        printf("completed correct boundary=1; max_boundary_steps_per_unit=%llu; ready reuse adds zero boundary work=1\n",(unsigned long long)max_visits);
        op_release(again);
    }
    op_release(h);return bad;
}
int main(int argc,char **argv) {
    assert(argc==2);machine_init();eval_init();check_init();compiler_init();work_init();
    int bad=probe((size_t)strtoull(argv[1],NULL,10));
    work_free();compiler_free();check_free();eval_free();machine_free();return bad;
}

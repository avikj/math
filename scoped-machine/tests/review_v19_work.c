#include "work.c"
#include <assert.h>
#include <string.h>
int main(int argc,char **argv){
 assert(argc==2);setvbuf(stdout,NULL,_IONBF,0);
 machine_init();eval_init();check_init();compiler_init();work_init();
 if(!strcmp(argv[1],"sync-reap")){
  arena_reap_all();ArenaStats before=arena_stats();
  AtomId a=atom_named(9111),b=atom_named(9112);SetId sa=set_make(1,&a),sb=set_make(1,&b);
  SetId out=set_union(sa,sb);size_t n;set_atoms(out,&n);assert(n==2);
  ArenaStats after=arena_stats();printf("synchronous set union: page releases=%llu\n",(unsigned long long)(after.releases-before.releases));
  assert(after.releases>before.releases);
 }else if(!strcmp(argv[1],"audit-sharing")){
  RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);
  TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
  CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};ContextId G=context_make(2,ds,fc_true());
  RefId PT=mk_path_const(0,A,x,x);uint64_t ps[]={va,vx};
  SymbolId ax=define_global("audit_share",varset_make(ps,2),dimset_make(NULL,0),PT);assert(ax);
  BoundaryId B=boundary_make(G,fc_true(),0,NULL,A,0,0);assert(B);
  ModelId M=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());const char *why=NULL;
  AtomId a=atom_named(9121),b=atom_named(9122);
  PlanId pa=plan_make(B,x,global_ref(ax),1,&a,&why),pb=plan_make(B,x,global_ref(ax),1,&b,&why);assert(pa&&pb);
  OpId ha=op_prepare(expr_plan(pa),M),hb=op_prepare(expr_plan(pb),M);
  uint64_t maxk=0,maxau=0;size_t units=0;
  while(op_status(ha)==OP_RUNNING||op_status(hb)==OP_RUNNING){
   for(size_t k=0;k<2;k++){
    OpId h=k?hb:ha;if(op_status(h)!=OP_RUNNING)continue;
    WorkLedger b=work_ledger();op_step(h,1);WorkLedger c=work_ledger();
    if(c.kernel_calls-b.kernel_calls>maxk)maxk=c.kernel_calls-b.kernel_calls;
    if(c.frames[FR_PROOF_USE_AUDIT]-b.frames[FR_PROOF_USE_AUDIT]>maxau)maxau=c.frames[FR_PROOF_USE_AUDIT]-b.frames[FR_PROOF_USE_AUDIT];
    assert(++units<1000000);
   }
  }
  assert(op_status(ha)==OP_COMPLETE&&op_status(hb)==OP_COMPLETE);
  size_t producers=0;for(size_t i=1;i<=W.tab.n;i++){Side*s=side(i);if(s->kind==K_JOB&&s->ptr&&((Op*)s->ptr)->family==OF_AUDIT)producers++;}
  const uint64_t *h;assert(problem_assumptions(op_result(ha),&h)==1&&h[0]==ax);
  assert(problem_assumptions(op_result(hb),&h)==1&&h[0]==ax);
  printf("interleaved preparations: audit producers=%zu max_kernel=%llu max_audit=%llu units=%zu\n",producers,(unsigned long long)maxk,(unsigned long long)maxau,units);
  assert(producers==1&&maxk<=1&&maxau<=1);op_release(ha);op_release(hb);
 }else assert(!"unknown mode");
 work_free();compiler_free();check_free();eval_free();machine_free();return 0;
}

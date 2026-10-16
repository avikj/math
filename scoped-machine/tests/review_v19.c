#include "work.h"
#include "proof.h"
#include "arena.h"
#include <assert.h>
#include <string.h>

static void init(void){machine_init();eval_init();check_init();compiler_init();work_init();}
static void done(void){work_free();compiler_free();check_free();eval_free();machine_free();}
int main(int argc,char **argv){
 assert(argc==2);setvbuf(stdout,NULL,_IONBF,0);
 if(!strcmp(argv[1],"arena-directory") || !strcmp(argv[1],"arena-empty")){
  arena_init();Paged p;paged_init(&p,sizeof(uint64_t));
  if(!strcmp(argv[1],"arena-empty")){
   paged_retire(&p);printf("empty retire: elem=%zu per=%zu\n",p.elem,p.per);
   assert(p.elem==sizeof(uint64_t)&&p.per==ARENA_PAGE);pw_push(&p,42);assert(pw_get(&p,0)==42);
  }else{
   for(size_t i=0;i<(size_t)ARENA_PAGE*PAGED_DIR+1;i++)pw_push(&p,i);
   printf("pages=%zu (second directory present=%d)\n",paged_pages(&p),!!p.dir2);
  }
  paged_retire(&p);size_t units=0;while(arena_reap())units++;
  ArenaStats st=arena_stats();printf("reap units=%zu words_out=%llu words_in=%llu missing=%llu\n",units,(unsigned long long)st.words_out,(unsigned long long)st.words_in,(unsigned long long)(st.words_out-st.words_in));
  assert(st.words_out==st.words_in);arena_free();return 0;
 }
 init();const char *why=NULL;
 RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);
 TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
 CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};ContextId G=context_make(2,ds,fc_true());
 uint64_t ps[]={va,vx};RefId PT=mk_path_const(0,A,x,x);
 RefId Eq=mk_equiv(0,0,A,A);
 SymbolId eq=define_global("review_eq",varset_make(ps,2),dimset_make(NULL,0),Eq);assert(eq);
 SymbolId ax=define_global("review_path",varset_make(ps,2),dimset_make(NULL,0),PT);assert(ax);
 TransformId tr=compile_equivalence(G,fc_true(),A,0,A,0,global_ref(eq),&why);require(tr,"compile %s",why?why:"");
 BoundaryId B=boundary_make(G,fc_true(),0,NULL,A,0,0);assert(B);
 ModelId M=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());
 if(!strcmp(argv[1],"audit-admission")){
  PlanId p=plan_make(B,x,0,0,NULL,&why);assert(p);
  ConnectorId c=connector_make(B,B,B,tr,0,0,(AtomId[]){0});assert(c);
  ExprId e=expr_join(expr_plan(p),expr_plan(p),c);
  check_open_environment();assert(set_global_body(eq,U));
  ProblemId pr=problem_prepare(e,M,&why);
  printf("after bad body: prepare=%llu core=%d reason=%s\n",(unsigned long long)pr,pr?problem_core(pr):-1,why?why:"");
  ProofUse oracle=transform_proof_use(tr);printf("oracle=%s\n",proof_use_name(oracle.status));
  assert(oracle.status==PU_INVALID);assert(pr==0);
 }else if(!strcmp(argv[1],"audit-marks")){
  RefId a1=global_ref(ax);TermVarId z=declare_term(PT,fc_true());
  RefId a2=mk_app(mk_lam_lv(0,z,PT,ref_var(z)),a1);
  AtomId w1=atom_named(9901),w2=atom_named(9902),w3=atom_named(9903);
  PlanId p1=plan_make(B,x,a1,1,&w1,&why),p2=plan_make(B,x,a2,1,&w2,&why);assert(p1&&p2);
  ProblemId both=problem_prepare(expr_alt(expr_plan(p1),expr_plan(p2)),M,&why);require(both,"both %s",why?why:"");
  const uint64_t *hyp;size_t nh=problem_assumptions(both,&hyp);printf("two audits: assumptions=%zu core=%d\n",nh,problem_core(both));assert(nh==1&&hyp[0]==ax);
  /* Whichever judgment was second must still retain ax on cached reuse. */
  PlanId pa=plan_make(B,x,a1,1,&w3,&why),pb=plan_make(B,x,a2,1,&w3,&why);assert(pa&&pb);
  ProblemId qa=problem_prepare(expr_plan(pa),M,&why),qb=problem_prepare(expr_plan(pb),M,&why);assert(qa&&qb);
  const uint64_t *ha,*hb;size_t na=problem_assumptions(qa,&ha),nb=problem_assumptions(qb,&hb);
  printf("separate reuse: assumptions=%zu/%zu core=%d/%d\n",na,nb,problem_core(qa),problem_core(qb));
  assert(na==1&&nb==1&&ha[0]==ax&&hb[0]==ax&&!problem_core(qa)&&!problem_core(qb));
 }else assert(!"unknown mode");done();return 0;
}

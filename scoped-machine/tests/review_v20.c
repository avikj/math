#include "work.c"
#include "fine.h"
#include <assert.h>
#include <string.h>
static size_t kernel_qsort_max;
void __real_qsort(void*,size_t,size_t,int(*)(const void*,const void*));
void __wrap_qsort(void*p,size_t n,size_t z,int(*cmp)(const void*,const void*)){
 if(kf_tl&&n>kernel_qsort_max)kernel_qsort_max=n;
 __real_qsort(p,n,z,cmp);
}
static void init(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void done(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
static uint64_t total(FineVector a, FineVector b) { uint64_t n=0; for(int k=0;k<FC_COUNT;k++) n+=b.v[k]-a.v[k]; return n; }
static OpId kernel(uint64_t kind,uint64_t a,uint64_t b,uint64_t c,uint64_t d) {
 pthread_mutex_lock(&W.mu); OpId h=op_new(OF_KERNEL,PH_CHECK,kfr(kind,a,b,c,d));pthread_mutex_unlock(&W.mu);return h;
}
static int starve(int released) {
 init(); RefId U=mk_universe(0); TermVarId va=declare_term(U,fc_true()); RefId A=ref_var(va);
 TermVarId vx=declare_term(A,fc_true()),vy=declare_term(A,fc_true()); RefId x=ref_var(vx),y=ref_var(vy);
 RefId f=ref_var(declare_term(mk_fun(0,0,A,A),fc_true())); RefId t=x;for(size_t j=0;j<8;j++)t=mk_app(f,t);
 AtomId a=atom_producer(t,fc_true()),b=atom_producer(mk_app(f,t),fc_true());
 SetId sa=set_make(1,&a),sb=set_make(1,&b);MapId m=map_single_term(vx,y);
 OpId h1=op_specialize_set(sa,m);size_t i=0;while(!W.kf_active&&op_status(h1)==OP_RUNNING&&i++<10000)op_step(h1,1);
 assert(W.kf_active);if(released)op_release(h1);OpId h2=op_specialize_set(sb,m);uint64_t owner=W.kf_owner;
 for(i=0;i<30000&&op_status(h2)==OP_RUNNING;i++)op_step(h2,1);
 int ok=op_status(h2)==OP_COMPLETE;
 printf("independent root: steps=%zu complete=%d foreign_done=%d same_owner=%d first_status=%d\n",i,ok,W.kf_active?kf_done(W.kf_active):-1,W.kf_owner==owner,op_status(h1));
 op_release(h1);op_release(h2);done();return ok?0:1;
}
static int evalbound(size_t n) {
 init();RefId U=mk_universe(0);FaceId *fs=malloc(n*sizeof *fs);RefId *ts=malloc(n*sizeof *ts);
 for(size_t i=0;i<n;i++){fs[i]=i?fc_false():fc_true();ts[i]=U;}
 RefId S=mk_system(n,fs,ts);TermVarId vx=declare_term(S,fc_true());RefId x=ref_var(vx);
 CtxDecl ds[]={{S_TERM,vx,S}};ContextId G=context_make(1,ds,fc_true());
 OpId h=kernel(KK_IS_TYPE,G,fc_true(),x,0);size_t units=0;uint64_t max=0,mfields=0;
 while(op_status(h)==OP_RUNNING&&units<5000000){FineVector a=fine_snapshot();op_step(h,1);FineVector b=fine_snapshot();uint64_t d=total(a,b);if(d>max)max=d;if(b.v[FC_FIELDS_OPENED]-a.v[FC_FIELDS_OPENED]>mfields)mfields=b.v[FC_FIELDS_OPENED]-a.v[FC_FIELDS_OPENED];units++;}
 printf("evaluator n=%zu status=%d units=%zu max_fine_per_unit=%llu max_fields_per_unit=%llu\n",n,op_status(h),units,(unsigned long long)max,(unsigned long long)mfields);
 int ok=op_status(h)==OP_COMPLETE&&max<=128;op_release(h);free(fs);free(ts);done();return ok?0:1;
}
static int retry(void) {
 init();RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
 CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};ContextId G=context_make(2,ds,fc_true());
 RefId t=mk_app(mk_lam_lv(0,vx,A,x),x);
 check_set_budget(1);OpId h1=kernel(KK_INFER,G,fc_true(),t,0);
 size_t i=0;while(op_status(h1)==OP_RUNNING&&i++<100000)op_step(h1,1);
 printf("retry first=%d diagnostic=%s\n",op_status(h1),op_diagnostic(h1));
 check_set_budget(100000);Inference oracle=infer(G,fc_true(),t);OpId h2=kernel(KK_INFER,G,fc_true(),t,0);
 i=0;while(op_status(h2)==OP_RUNNING&&i++<100000)op_step(h2,1);
 printf("retry oracle=%d second=%d diagnostic=%s\n",oracle.st,op_status(h2),op_diagnostic(h2));
 int ok=oracle.st==CK_VALID&&op_status(h2)==OP_COMPLETE;op_release(h1);op_release(h2);done();return ok?0:1;
}
static int lifecycle(void) {
 machine_init();eval_init();check_init();compiler_init();
 uint64_t leak[3];for(size_t i=0;i<3;i++){ArenaStats b=arena_stats();work_init();AtomId a=atom_named(500+i);SetId S=set_make(1,&a);SetId out=set_union(S,set_empty());assert(out==S);work_free();ArenaStats c=arena_stats();leak[i]=(c.words_out-b.words_out)-(c.words_in-b.words_in);printf("work lifecycle %zu unreleased_words=%llu\n",i,(unsigned long long)leak[i]);}
 compiler_free();check_free();eval_free();machine_free();return leak[2]==0?0:1;
}
static int prepare_retry(void) {
 init();RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
 CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};ContextId G=context_make(2,ds,fc_true());
 RefId PT=mk_path_const(0,A,x,x);uint64_t ps[]={va,vx};SymbolId ax=define_global("retry",varset_make(ps,2),dimset_make(NULL,0),PT);assert(ax);
 BoundaryId B=boundary_make(G,fc_true(),0,NULL,A,0,0);const char*why=NULL;AtomId a=atom_named(9919);PlanId P=plan_make(B,x,global_ref(ax),1,&a,&why);assert(P);
 ExprId E=expr_plan(P);ModelId M=model_make(1,(KindWeights){1,1,1,1,1,1,1,1},set_empty());
 check_open_environment();check_set_budget(1);OpId h1=op_prepare(E,M);size_t i=0;while(op_status(h1)==OP_RUNNING&&i++<1000000)op_step(h1,1);
 printf("prepare retry first=%d reason=%s\n",op_status(h1),op_diagnostic(h1));check_set_budget(100000);
 CheckStatus oracle=check(G,fc_true(),global_ref(ax),PT,&why);OpId h2=op_prepare(E,M);i=0;while(op_status(h2)==OP_RUNNING&&i++<1000000)op_step(h2,1);
 printf("prepare retry oracle=%d second=%d reason=%s\n",oracle,op_status(h2),op_diagnostic(h2));int ok=oracle==CK_VALID&&op_status(h2)==OP_COMPLETE;
 op_release(h1);op_release(h2);done();return ok?0:1;
}
static int map_sort(size_t n) {
 init();RefId U0=mk_universe(0),U1=mk_universe(1);MapBuilder b;mapb_init(&b);
 for(size_t i=0;i<n;i++)mapb_term(&b,declare_term(U1,fc_true()),U0);
 MapId sigma=mapb_finish(&b),tau=map_single_term(declare_term(U1,fc_true()),U0);
 OpId h=kernel(KK_COMPOSE,sigma,tau,0,0);size_t units=0;
 while(op_status(h)==OP_RUNNING&&units++<5000000)op_step(h,1);
 printf("map compose n=%zu kernel_qsort_max=%zu status=%d units=%zu\n",n,kernel_qsort_max,op_status(h),units);
 int ok=op_status(h)==OP_COMPLETE&&kernel_qsort_max==0;op_release(h);done();return ok?0:1;
}
static int fresh_retire(void){arena_init();ArenaStats b=arena_stats();size_t got=0;uint64_t*p=arena_alloc_zero(4096,&got);p[got-1]=123;arena_release(p,got);ArenaStats c=arena_stats();
 printf("fresh retirement: out=%llu in=%llu\n",(unsigned long long)(c.words_out-b.words_out),(unsigned long long)(c.words_in-b.words_in));return c.words_out-b.words_out==c.words_in-b.words_in?0:1;}
static int independent_cone(void) {
 init();RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);TermVarId vx=declare_term(A,fc_true()),vy=declare_term(A,fc_true());RefId x=ref_var(vx),y=ref_var(vy);
 RefId f=ref_var(declare_term(mk_fun(0,0,A,A),fc_true()));RefId t=x;for(size_t i=0;i<64;i++)t=mk_app(f,t);
 OpId h1=kernel(KK_REINDEX,t,map_single_term(vx,y),0,0);op_step(h1,1);assert(W.kf_active&&!kf_done(W.kf_active));KStack*first=W.kf_active;uint64_t before=first->steps;
 OpId h2=kernel(KK_REF_VALIDATE,U,0,0,0);op_step(h2,1);uint64_t advanced=first->steps-before;
 printf("independent cones: second root advanced first continuation by %llu transitions\n",(unsigned long long)advanced);
 op_release(h1);op_release(h2);done();return advanced==0?0:1;
}
int main(int argc,char**argv){setvbuf(stdout,NULL,_IONBF,0);assert(argc>=2);
 if(!strcmp(argv[1],"independent"))return starve(0);
 if(!strcmp(argv[1],"independent-release"))return starve(1);
 if(!strcmp(argv[1],"independent-cone"))return independent_cone();
 if(!strcmp(argv[1],"evaluator"))return evalbound(argc>2?strtoull(argv[2],NULL,10):64);
 if(!strcmp(argv[1],"retry"))return retry();
 if(!strcmp(argv[1],"prepare-retry"))return prepare_retry();
 if(!strcmp(argv[1],"lifecycle"))return lifecycle();
 if(!strcmp(argv[1],"map-sort"))return map_sort(argc>2?strtoull(argv[2],NULL,10):64);
 if(!strcmp(argv[1],"fresh-retire"))return fresh_retire();
 return 2;
}

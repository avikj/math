#include "check.h"
#include "lib.h"
#include "compiler.h"
#include "reuse_stats.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

typedef struct { RefId U,A,x;TermVarId a,xv;DimVarId i,j; } World;
static size_t workers;
static void init(World*w){machine_init();eval_init();check_init();compiler_init();if(workers)eval_set_workers(workers);w->U=mk_universe(0);w->a=declare_term(w->U,fc_true());w->A=ref_var(w->a);w->xv=declare_term(w->A,fc_true());w->x=ref_var(w->xv);w->i=declare_dim();w->j=declare_dim();}
static void done(void){compiler_free();check_free();eval_free();machine_free();}
static SymbolId sym(World*w,const char*name,RefId T,bool dim){uint64_t xs[]={w->a,w->xv},ds[]={w->i};return define_global(name,varset_make(xs,2),dimset_make(ds,dim?1:0),T);}
static bool has(const PrefixFact*f,SymbolId s){for(size_t k=0;f&&k+1<f->ngdeps;k+=2)if(f->gdeps[k]==s&&f->gdeps[k+1]==global_revision(s))return true;return false;}
static RefId at(RefId t,DimVarId i,IntervalId r){MapBuilder b;mapb_init(&b);mapb_dim(&b,i,r);return reindex(t,mapb_finish(&b));}
static int ready_prefix(void){
    World w;init(&w);SymbolId g=sym(&w,"opaque",w.A,false);assert(g);
    TermVarId z=declare_term(w.A,fc_true());RefId t=mk_app(mk_lam_lv(0,z,w.A,global_ref(g)),w.x);
    WhnfStatus st;EvalResult*r=whnf(t,fc_true(),&st);assert(st==W_OK&&r&&r->cls==R_NEUTRAL);
    EntryId old=eval_entry_lookup(t,fc_true());const PrefixFact*f=eval_entry_prefix(old);
    assert(f&&eval_prefix_valid(f)&&!has(f,g));
    assert(set_global_body(g,w.x));assert(!eval_entry_deps_valid(old));assert(eval_prefix_valid(f));
    uint64_t b=reuse_count(REUSE_BETA);r=whnf(t,fc_true(),&st);
    uint64_t added=reuse_count(REUSE_BETA)-b;bool ok=st==W_OK&&r&&r->ref==w.x;
    printf("ready-prefix: semantic_ok=%d valid_old_prefix=1 added_beta=%llu expected=0\n",ok,(unsigned long long)added);
    done();return ok&&added==0?0:1;
}
static int late_context(void){
    World w;init(&w);RefId Fun=mk_fun(0,0,w.A,w.A);TermVarId v=declare_term(w.A,fc_true());RefId id=mk_lam_lv(0,v,w.A,ref_var(v));
    SymbolId p=sym(&w,"pending_fun",mk_path_const(0,Fun,id,id),false);assert(p&&set_global_body(p,global_ref(p)));
    RefId pi=mk_papp_const(0,Fun,id,id,global_ref(p),iv_var(w.i));
    TermVarId z=declare_term(w.A,fc_true());RefId child=mk_app(mk_lam_lv(0,z,w.A,pi),w.x);
    WhnfStatus st;assert(!whnf(child,fc_true(),&st)&&st==W_STUCK);
    const PrefixFact*cf=eval_entry_prefix(eval_entry_lookup(child,fc_true()));assert(cf);
    RefId parent=mk_app(child,w.x);assert(!whnf(parent,fc_true(),&st)&&st==W_STUCK);
    const PrefixFact*f=eval_entry_prefix(eval_entry_lookup(parent,fc_true()));
    printf("late-context: child_fact=1 parent_fact=%d expected=1\n",f!=NULL);
    bool ok=f&&f->source==parent&&f->residual;
    done();return ok?0:1;
}
static int adapter_premise(void){
    World w;init(&w);SymbolId p=sym(&w,"pending",mk_path_const(0,w.A,w.x,w.x),false);assert(p&&set_global_body(p,global_ref(p)));
    RefId pi=mk_papp_const(0,w.A,w.x,w.x,global_ref(p),iv_var(w.i));TermVarId z=declare_term(w.A,fc_true());
    SymbolId F=sym(&w,"F",mk_fun(0,0,w.A,w.A),true);assert(F&&set_global_body(F,mk_lam_lv(0,z,w.A,pi)));
    RefId src=mk_app(global_ref(F),w.x);WhnfStatus st;assert(!whnf(src,fc_true(),&st)&&st==W_STUCK);
    const PrefixFact*f=eval_entry_prefix(eval_entry_lookup(src,fc_true()));assert(f&&has(f,F));
    RefId dst=at(src,w.i,iv_var(w.j));assert(!whnf(dst,fc_true(),&st)&&st==W_STUCK);
    EntryId e=eval_entry_lookup(dst,fc_true());assert(eval_entry_adapter_fact(e));
    const PrefixFact*g=eval_entry_prefix(e);assert(g);
    bool ok=true;size_t n=0;for(const PrefixFact*q=g;q;q=q->next){n++;if(!has(q,F))ok=false;}
    RefId endpoint=at(src,w.i,iv_zero());EvalResult*r=whnf(endpoint,fc_true(),&st);
    assert(st==W_OK&&r&&r->ref==w.x);const PVec*deps=NULL;
    size_t nd=eval_entry_gdeps(eval_entry_lookup(endpoint,fc_true()),&deps);bool final_has=false;
    for(size_t k=0;k<nd;k++)if(pv_get(deps,2*k)==F&&pv_get(deps,2*k+1)==global_revision(F))final_has=true;
    printf("adapter-premise: source_reads_F=1 derived_facts=%zu all_preserve_F=%d final_preserves_F=%d expected=1/1\n",n,ok,final_has);
    ok=ok&&final_has;
    done();return ok?0:1;
}
static int branch_prefix(void){
    World w;init(&w);SymbolId p=sym(&w,"pending_branch",mk_path_const(0,w.A,w.x,w.x),false);assert(p&&set_global_body(p,global_ref(p)));
    RefId pj=mk_papp_const(0,w.A,w.x,w.x,global_ref(p),iv_var(w.j));TermVarId z=declare_term(w.A,fc_true());
    RefId f=mk_lam_lv(0,z,w.A,pj);FaceId faces[]={fc_lit(w.i,0),fc_lit(w.i,1)};RefId terms[]={f,f};FaceId chi=fc_join(faces[0],faces[1]);
    RefId t=mk_app(mk_system(2,faces,terms),w.x);WhnfStatus st;
    assert(!whnf(t,chi,&st)&&st==W_STUCK);EntryId e=eval_entry_lookup(t,chi);assert(e&&eval_entry_state(e)==E_RUNNING);
    bool a=false,b=false,safe=true;for(const PrefixFact*q=eval_entry_prefix(e);q;q=q->next){if(q->face==faces[0])a=true;if(q->face==faces[1])b=true;if(q->face!=faces[0]&&q->face!=faces[1])safe=false;}
    RefId endpoint=at(t,w.j,iv_zero());bool reuse=true;
    for(size_t k=0;k<2;k++){uint64_t before=reuse_count(REUSE_BETA);EvalResult*r=whnf(endpoint,faces[k],&st);if(st!=W_OK||!r||r->ref!=w.x||reuse_count(REUSE_BETA)!=before)reuse=false;}
    printf("branch-prefix: branch0=%d branch1=%d guarded=%d both_faces_reused=%d expected=1/1/1/1 parent_pending=1\n",a,b,safe,reuse);
    done();return a&&b&&safe&&reuse?0:1;
}
static int comp_guard(void){
    World w;init(&w);DimVarId b=declare_dim();
    SymbolId p=sym(&w,"pending_type",mk_path_const(1,w.U,w.A,w.A),false);assert(p&&set_global_body(p,global_ref(p)));
    RefId pk=mk_papp_const(1,w.U,w.A,w.A,global_ref(p),iv_var(w.j));
    TermVarId z=declare_term(w.A,fc_true());RefId f=mk_lam_lv(0,z,w.A,pk);
    FaceId faces[]={fc_lit(w.i,0),fc_lit(w.i,1),fc_meet(fc_lit(w.i,0),fc_lit(b,0))};
    RefId terms[]={f,f,f};FaceId chi=fc_join(faces[0],faces[1]);
    RefId family=mk_app(mk_system(3,faces,terms),w.x);
    RefId cap=ref_var(declare_term(pk,fc_true()));RefId t=mk_comp_lv(0,b,family,fc_false(),cap,cap);
    DimOpen opened=resolve_dim_binder(t,0,0);WhnfStatus st;
    assert(!whnf(t,chi,&st)&&st==W_STUCK);EntryId e=eval_entry_lookup(t,chi);
    bool a=false,c=false,safe=true;size_t n=0;
    for(const PrefixFact*q=eval_entry_prefix(e);q;q=q->next){
        n++;if(q->face==faces[0])a=true;if(q->face==faces[1])c=true;
        if(fc_forall(opened.j,q->face)!=q->face)safe=false;
    }
    printf("comp-guard: facts=%zu outer_faces=%d/%d bound_dimension_absent=%d expected=1/1/1\n",n,a,c,safe);
    done();return a&&c&&safe?0:1;
}
typedef struct { pthread_barrier_t *start; RefId term; WhnfStatus status; EvalResult *result; } Race;
static void *race_request(void *ptr){Race*r=ptr;pthread_barrier_wait(r->start);r->result=whnf(r->term,fc_true(),&r->status);return NULL;}
static int subscriber_race(void){
    bool ok=true;
    for(size_t trial=0;trial<16;trial++){
        World w;init(&w);RefId Fun=mk_fun(0,0,w.A,w.A);TermVarId v=declare_term(w.A,fc_true());RefId id=mk_lam_lv(0,v,w.A,ref_var(v));
        SymbolId p=sym(&w,"race_pending",mk_path_const(0,Fun,id,id),false);assert(p&&set_global_body(p,global_ref(p)));
        RefId pi=mk_papp_const(0,Fun,id,id,global_ref(p),iv_var(w.i));TermVarId z=declare_term(w.A,fc_true());
        RefId child=mk_app(mk_lam_lv(0,z,w.A,pi),w.x),parent=mk_app(child,w.x);
        pthread_barrier_t start;assert(!pthread_barrier_init(&start,NULL,2));Race a={.start=&start,.term=child},b={.start=&start,.term=parent};pthread_t ta,tb;
        assert(!pthread_create(&ta,NULL,race_request,&a));assert(!pthread_create(&tb,NULL,race_request,&b));pthread_join(ta,NULL);pthread_join(tb,NULL);pthread_barrier_destroy(&start);
        size_t nc=eval_entry_prefix_count(eval_entry_lookup(child,fc_true())),np=eval_entry_prefix_count(eval_entry_lookup(parent,fc_true()));
        if(a.result||b.result||a.status!=W_STUCK||b.status!=W_STUCK||nc!=1||np!=1){ok=false;printf("race trial=%zu child=%zu parent=%zu statuses=%d/%d\n",trial,nc,np,a.status,b.status);}
        done();
    }
    printf("subscriber-race: 16 trials one child fact/one contextual fact=%d\n",ok);return ok?0:1;
}
int main(int argc,char**argv){setvbuf(stdout,NULL,_IONBF,0);assert(argc>=2);
    workers=argc>2?(size_t)strtoul(argv[2],NULL,10):0;
    if(!strcmp(argv[1],"ready-prefix"))return ready_prefix();
    if(!strcmp(argv[1],"late-context"))return late_context();
    if(!strcmp(argv[1],"adapter-premise"))return adapter_premise();
    if(!strcmp(argv[1],"branch-prefix"))return branch_prefix();
    if(!strcmp(argv[1],"comp-guard"))return comp_guard();
    if(!strcmp(argv[1],"subscriber-race"))return subscriber_race();
    return 2;
}

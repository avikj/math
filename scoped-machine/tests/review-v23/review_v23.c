#define _GNU_SOURCE
#include "work.c"
#include "canon.h"
#include "runtime.h"
#include "fine.h"
#include "kstack.h"
#include <assert.h>
#include <unistd.h>
#include <sys/wait.h>
#include <stdatomic.h>

/* Link with -Wl,--wrap=pthread_create. Count real native workers, including
 * detached ones; no /proc access or timing inference is required. */
static _Atomic size_t live_threads;
typedef struct { void *(*fn)(void *); void *arg; } ThreadStart;
int __real_pthread_create(pthread_t *,const pthread_attr_t *,void *(*)(void *),void *);
static void thread_done(void *p){(free)(p);atomic_fetch_sub(&live_threads,1);}
static void *count_thread(void *p){ThreadStart*s=p;void*r;pthread_cleanup_push(thread_done,p);r=s->fn(s->arg);pthread_cleanup_pop(1);return r;}
int __wrap_pthread_create(pthread_t*t,const pthread_attr_t*a,void*(*fn)(void*),void*arg){ThreadStart*s=(malloc)(sizeof *s);assert(s);*s=(ThreadStart){fn,arg};atomic_fetch_add(&live_threads,1);int e=__real_pthread_create(t,a,count_thread,s);if(e)thread_done(s);return e;}

static void init(void){machine_init();eval_init();check_init();compiler_init();work_init();}
static void done(void){work_free();compiler_free();check_free();eval_free();machine_free();}
static Graph *export_ref(RefId t){Canon*c=canon_new();EvalResult r={0};r.cls=R_INTRODUCTION;r.ref=t;canon_add_result(c,"root",&r);Graph*g=canon_export(c);canon_free(c);return g;}

static int canon_tail(void){
    init();uint64_t a[9]={1,0,0,0,0,0,0,0,1},b[9]={2,0,0,0,0,0,0,0,1};
    Nat na=nat_from_limbs(9,a),nb=nat_from_limbs(9,b);assert(na!=nb);
    RefId U=mk_universe(0);TermVarId x=declare_term(U,fc_true());
    /* Only the stored level annotation differs. Export must retain it even
     * for raw input that would later fail its typing boundary. */
    Graph*g=export_ref(mk_lam_lv(na,x,U,ref_var(x))),*h=export_ref(mk_lam_lv(nb,x,U,ref_var(x)));
    MatchReport r;bool eq=graph_match(g,h,&r);
    printf("canon-tail: distinct 155-digit annotations compare_equal=%d expected=0\n",eq);
    graph_free(g);graph_free(h);done();return eq?1:0;
}
static char *child_export(int shift,int mode){
    int fds[2];assert(!pipe(fds));pid_t pid=fork();assert(pid>=0);
    if(!pid){
        close(fds[0]);init();if(shift)nat_from_word(UINT64_C(1)<<63);
        Nat l=nat_from_limbs(2,(uint64_t[]){0,1});RefId t;
        if(!mode)t=mk_universe(l);
        else {RefId A=ref_var(declare_term(mk_universe(l),fc_true())),x=ref_var(declare_term(A,fc_true()));t=mode==1?mk_refl(l,A,x):rt_maps_type(l,l,A,A);}
        Canon*c=canon_new();EvalResult r={0};r.cls=R_INTRODUCTION;r.ref=t;canon_add_result(c,"root",&r);
        size_t n;const char*s=canon_finish(c,&n);size_t at=0;while(at<n){ssize_t k=write(fds[1],s+at,n-at);assert(k>0);at+=(size_t)k;}
        close(fds[1]);canon_free(c);done();_exit(0);
    }
    close(fds[1]);size_t n=0,cap=1024;char*s=(malloc)(cap);
    for(;;){if(n+512>=cap){cap*=2;s=(realloc)(s,cap);}ssize_t k=read(fds[0],s+n,cap-n-1);assert(k>=0);if(!k)break;n+=(size_t)k;}
    s[n]=0;close(fds[0]);int status;assert(waitpid(pid,&status,0)==pid&&WIFEXITED(status)&&WEXITSTATUS(status)==0);return s;
}
static int export_order(int mode){char*a=child_export(0,mode),*b=child_export(1,mode);bool eq=!strcmp(a,b);printf("export-order %s: same value after unrelated Nat allocation exports_equal=%d expected=1\n",mode==2?"runtime":mode?"template":"universe",eq);if(!eq&&mode!=2)printf("FIRST\n%sSECOND\n%s",a,b);(free)(a);(free)(b);return eq?0:1;}

static int long_name(void){
    init();char a[900],b[900];memset(a,'a',sizeof a);a[899]=0;memcpy(b,a,sizeof a);b[898]='b';
    SymbolId sa=define_global(a,varset_make(NULL,0),dimset_make(NULL,0),mk_universe(0));
    SymbolId sb=define_global(b,varset_make(NULL,0),dimset_make(NULL,0),mk_universe(0));
    Graph*g=export_ref(global_ref(sa)),*h=export_ref(global_ref(sb));MatchReport r;bool eq=graph_match(g,h,&r);
    printf("long-name: distinct names compare_equal=%d expected=0\n",eq);graph_free(g);graph_free(h);done();return eq?1:0;
}

static _Atomic bool slow_done;
static void finite_slow(KCont*k){for(size_t i=0;i<((size_t)1<<20)+17;i++)fine_bump(FC_NAT_LIMBS);slow_done=true;k->ok=true;k->out[0]=0;}
static int cleanup_long(void){
    init();pthread_mutex_lock(&W.mu);OpId h=op_new(OF_KERNEL,PH_CHECK,kfr(KK_SHAPE_OF,mk_universe(0),0,0,0));Op*o=JOB(HND(h)->job);Frame*f=top(o);
    KCont*k=kc_new(finite_slow,NULL,0);k->job=o->id;f->ph=1;f->acc=(uint64_t)(uintptr_t)k;pthread_mutex_unlock(&W.mu);
    op_step(h,1);assert(!kc_done(k));op_release(h);work_free();
    check_free();compiler_free();eval_free();machine_free();
    size_t live=atomic_load(&live_threads);
    printf("cleanup-long: finite call completed=%d; native workers retained after closed teardown=%zu expected=0\n",atomic_load(&slow_done),live);
    return live?1:0;
}
static int counter_wrap(void){
    /* Boundary injection avoids executing 2^64 instructions. This test is
     * deliberately tied to V23's word-counter ABI; an exact-counter ABI
     * should replace it with an exact seed/read helper, not a saturation. */
    __atomic_store_n(&fine_counters[FC_NAT_LIMBS],UINT64_MAX,__ATOMIC_RELAXED);
    fine_bump(FC_NAT_LIMBS);uint64_t n=fine_count(FC_NAT_LIMBS);
    printf("counter-wrap: after 2^64 increments the fine reading is %llu; zero is not the exact value\n",(unsigned long long)n);
    return n==0?1:0;
}
static RefId malformed_ref,malformed_type; static ScopeId malformed_scope; static ContextId malformed_context; static int small_stack_ok;
static void *validate_small(void *unused){
    (void)unused; const char *why=NULL;
    bool r=ref_validate(malformed_ref,&why),s=scope_validate(malformed_scope,&why);
    CheckStatus ck=check(malformed_context,fc_false(),malformed_ref,malformed_type,&why);
    printf("small-stack-validation: malformed ref valid=%d scope valid=%d check-under-false=%s segments=%zu\n",r,s,check_status_name(ck),kstack_segments());
    small_stack_ok=!r&&!s&&ck==CK_INVALID;return NULL;
}
static int small_stack_validation(void){
    init();RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());malformed_type=ref_var(va);
    TermVarId vx=declare_term(malformed_type,fc_true());RefId x=ref_var(vx);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,malformed_type}};malformed_context=context_make(2,ds,fc_true());
    LocalDecl d={S_DIM,0,LEVEL_NONE,fc_true()};
    malformed_scope=scope_intern(1,&d,(Val){VS_REF,ref_var(bound_id(1,0))},malformed_type,0,fc_false());
    malformed_ref=mk_fst(mk_hcomp(0,malformed_type,fc_false(),malformed_scope,x));
    pthread_attr_t a;assert(!pthread_attr_init(&a));assert(!pthread_attr_setstacksize(&a,(size_t)256<<10));pthread_t th;assert(!pthread_create(&th,&a,validate_small,NULL));assert(!pthread_join(th,NULL));pthread_attr_destroy(&a);done();return small_stack_ok?0:1;
}
static RefId deep_term,deep_type;static TermVarId deep_x;static int deep_ok;
static void *capture_small(void *unused){
    (void)unused;CaptureDecl d={S_TERM,deep_x,deep_type,0,fc_true()};
    ScopeId s=capture_scope(1,&d,(Val){VS_REF,deep_term},deep_type,0,fc_true());
    Val arg={VS_REF,ref_var(deep_x)};TypedPartial p=apply_scope(s,1,&arg);
    deep_ok=p.body.sort==VS_REF&&p.body.id==deep_term;
    printf("deep-capture: capture/apply restored the same reference=%d segments=%zu\n",deep_ok,kstack_segments());return NULL;
}
static int deep_capture(void){
    init();deep_type=ref_var(declare_term(mk_universe(0),fc_true()));deep_x=declare_term(deep_type,fc_true());
    RefId f=ref_var(declare_term(mk_fun(0,0,deep_type,deep_type),fc_true()));RefId wrapper=mk_app(f,ref_var(deep_x));deep_term=ref_var(deep_x);
    for(size_t i=0;i<4000;i++)deep_term=reindex(wrapper,map_single_term(deep_x,deep_term));
    pthread_attr_t a;assert(!pthread_attr_init(&a));assert(!pthread_attr_setstacksize(&a,(size_t)256<<10));pthread_t th;assert(!pthread_create(&th,&a,capture_small,NULL));assert(!pthread_join(th,NULL));pthread_attr_destroy(&a);done();return deep_ok?0:1;
}
int main(int argc,char**argv){setvbuf(stdout,NULL,_IONBF,0);assert(argc==2);
    if(!strcmp(argv[1],"canon-tail"))return canon_tail();
    if(!strcmp(argv[1],"export-universe"))return export_order(0);
    if(!strcmp(argv[1],"export-template"))return export_order(1);
    if(!strcmp(argv[1],"export-runtime"))return export_order(2);
    if(!strcmp(argv[1],"long-name"))return long_name();
    if(!strcmp(argv[1],"cleanup-long"))return cleanup_long();
    if(!strcmp(argv[1],"counter-wrap"))return counter_wrap();
    if(!strcmp(argv[1],"small-stack-validation"))return small_stack_validation();
    if(!strcmp(argv[1],"deep-capture"))return deep_capture();
    return 2;
}

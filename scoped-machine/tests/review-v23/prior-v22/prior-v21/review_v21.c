#include "work.c"
#include "fine.h"
#include <assert.h>
#include <string.h>

static void init(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void done(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
static OpId kernel(uint64_t kind,uint64_t a,uint64_t b,uint64_t c,uint64_t d) {
    pthread_mutex_lock(&W.mu); OpId h=op_new(OF_KERNEL,PH_CHECK,kfr(kind,a,b,c,d)); pthread_mutex_unlock(&W.mu); return h;
}
static void finish(OpId h) {
    size_t n=0; while(op_status(h)==OP_RUNNING && n++<2000000) op_step(h,1);
    assert(op_status(h)==OP_COMPLETE);
}
static int zero_interleave(bool different_order) {
    arena_init(); size_t na,nb;
    uint64_t *a=arena_alloc_zero(different_order?1024:512,&na);
    uint64_t *b=arena_alloc_zero(512,&nb);
    for(size_t i=0;i<na;i++) a[i]=0x12345678;
    for(size_t i=0;i<nb;i++) b[i]=0xabcdef01;
    arena_release(a,na); assert(arena_tend_zero());
    arena_release(b,nb);
    while(arena_tend_zero()) {}
    /* Both blocks are now in ready lists. Inspect every reused block;
       list order is deliberately immaterial. */
    size_t nc,nd; uint64_t*c=arena_alloc_zero(512,&nc);
    uint64_t*d=arena_alloc_zero(different_order?1024:512,&nd);
    size_t bad=0,first=(size_t)-1;
    for(size_t i=0;i<nc;i++) if(c[i]){bad++;if(first==(size_t)-1)first=i;}
    for(size_t i=0;i<nd;i++) if(d[i]){bad++;if(first==(size_t)-1)first=i;}
    printf("zero-%s: nonzero_words=%zu first_nonzero=%zu\n",different_order?"order":"head",bad,first);
    arena_release(c,nc);arena_release(d,nd);return bad?1:0;
}
static void one_tick(KCont*k) { fine_bump(FC_VALIDATE_STEPS); k->ok=true; }
static int capacity(void) {
    KCont *ks[257];
    for(size_t i=0;i<257;i++){ks[i]=kc_new(one_tick,NULL,0);kc_grant(ks[i],1);assert(!kc_done(ks[i]));}
    for(size_t i=0;i<257;i++)kc_free(ks[i]);kc_shutdown();
    puts("257 live continuations completed");return 0;
}
static int ledger(void) {
    init(); RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);
    RefId x=ref_var(declare_term(A,fc_true())),y=ref_var(declare_term(A,fc_true()));
    RefId f=ref_var(declare_term(mk_fun(0,0,A,A),fc_true()));
    RefId a=x,b=y;for(size_t i=0;i<8;i++){a=mk_app(f,a);b=mk_app(f,b);}
    OpId h1=kernel(KK_SHAPE_OF,a,0,0,0),h2=kernel(KK_SHAPE_OF,b,0,0,0);
    uint64_t actual0=reuse_count(REUSE_SHAPE_NODE),charged0=work_ledger().frames[FR_SHAPE_NODE];
    op_step(h1,1);assert(W.kc_active&&!kc_done(W.kc_active));
    finish(h2);finish(h1);
    uint64_t actual=reuse_count(REUSE_SHAPE_NODE)-actual0,charged=work_ledger().frames[FR_SHAPE_NODE]-charged0;
    printf("interleaved shape accounting: actual=%llu charged=%llu\n",(unsigned long long)actual,(unsigned long long)charged);
    op_release(h1);op_release(h2);done();return actual==charged?0:1;
}
static void observe(KCont*k) {
    WhnfStatus s; EvalResult*r=whnf(k->arg[0],fc_true(),&s);
    k->ok=s==W_OK&&r; k->out[0]=s;
}
static int wait_owner(void) {
    init();FaceId fs[16];RefId as[16],bs[16];
    for(size_t i=0;i<16;i++){fs[i]=i?fc_false():fc_true();as[i]=mk_universe(0);bs[i]=mk_universe(1);}
    RefId a=mk_system(16,fs,as),b=mk_system(16,fs,bs);
    uint64_t aa[]={a},bb[]={b};
    KCont *unrelated=kc_new(observe,aa,1),*owner=kc_new(observe,bb,1),*waiter=kc_new(observe,bb,1);
    for(size_t n=0;!unrelated->in_eval&&n<100000;n++)kc_grant(unrelated,1);
    assert(unrelated->in_eval&&!kc_done(unrelated));
    for(size_t n=0;!owner->in_eval&&n<100000;n++)kc_grant(owner,1);
    assert(owner->in_eval&&!kc_done(owner));
    for(size_t n=0;!waiter->blocked&&!kc_done(waiter)&&n<100000;n++)kc_grant(waiter,1);
    assert(waiter->blocked);
    bool correct=waiter->blocked_on==owner;
    printf("wait owner: actual_owner=%d unrelated_owner=%d\n",correct,waiter->blocked_on==unrelated);
    /* The actual producer alone can discharge this observation. */
    while(!kc_done(owner))kc_grant(owner,KC_UNBOUNDED);
    while(!kc_done(waiter))kc_grant(waiter,KC_UNBOUNDED);
    while(!kc_done(unrelated))kc_grant(unrelated,KC_UNBOUNDED);
    assert(owner->ok&&waiter->ok&&unrelated->ok);
    kc_free(waiter);kc_free(owner);kc_free(unrelated);done();return correct?0:1;
}
static void *zero_worker(void*arg) {
    size_t seed=(size_t)(uintptr_t)arg;
    for(size_t j=0;j<1000;j++){
        size_t n;uint64_t*p=arena_alloc_zero((j+seed)%2?512:1024,&n);
        for(size_t i=0;i<n;i++)assert(p[i]==0);
        for(size_t i=0;i<n;i++)p[i]=j+1;
        arena_release(p,n);for(size_t i=0;i<5;i++)arena_tend_zero();
    }
    return NULL;
}
static int zero_stress(void) {
    arena_init();pthread_t t[4];
    for(size_t i=0;i<4;i++)assert(pthread_create(&t[i],NULL,zero_worker,(void*)(uintptr_t)i)==0);
    for(size_t i=0;i<4;i++)assert(pthread_join(t[i],NULL)==0);
    while(arena_tend_zero()){}puts("zero-stress: 4000 allocations, every returned word zero");return 0;
}
static int cleanup_wait(bool drain) {
    init(); RefId U=mk_universe(0);TermVarId va=declare_term(U,fc_true());RefId A=ref_var(va);
    TermVarId vx=declare_term(A,fc_true());RefId x=ref_var(vx);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};ContextId G=context_make(2,ds,fc_true());
    RefId t=mk_refl(0,A,x),T=mk_path_const(0,A,x,x);
    OpId waiter=kernel(KK_CHECK,G,fc_true(),t,T);
    OpId owner=kernel(KK_INFER,G,fc_true(),t,0);
    /* Start the later allocated job first, until it owns a checker claim. */
    bool caught=false;
    for(size_t i=0;i<100000&&op_status(owner)==OP_RUNNING;i++){
        op_step(owner,1);
        if(fine_count(FC_CHECK_FRAMES)>1){caught=true;break;}
    }
    assert(caught&&op_status(owner)==OP_RUNNING);
    KCont*owner_k=W.kc_active;
    KCont*waiter_k=NULL;
    for(size_t i=0;i<100000&&op_status(waiter)==OP_RUNNING;i++){
        op_step(waiter,1);waiter_k=W.kc_active;
        if(waiter_k&&waiter_k!=owner_k&&waiter_k->blocked)break;
    }
    assert(waiter_k&&waiter_k->blocked&&waiter_k->blocked_on==owner_k);
    printf("cleanup-wait: waiter and owner suspended; starting teardown\n");
    if(drain){finish(owner);finish(waiter);puts("cleanup-drain: actual owner and waiter completed");}
    op_release(waiter);op_release(owner);done();puts("cleanup-wait: teardown returned");return 0;
}
int main(int argc,char**argv){setvbuf(stdout,NULL,_IONBF,0);assert(argc==2);
    if(!strcmp(argv[1],"zero-head"))return zero_interleave(false);
    if(!strcmp(argv[1],"zero-order"))return zero_interleave(true);
    if(!strcmp(argv[1],"capacity"))return capacity();
    if(!strcmp(argv[1],"ledger"))return ledger();
    if(!strcmp(argv[1],"wait-owner"))return wait_owner();
    if(!strcmp(argv[1],"zero-stress"))return zero_stress();
    if(!strcmp(argv[1],"cleanup-wait"))return cleanup_wait(false);
    if(!strcmp(argv[1],"cleanup-drain"))return cleanup_wait(true);
    return 2;
}

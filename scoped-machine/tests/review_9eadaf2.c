#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include "../src/compiler.h"
#include <string.h>
#include <pthread.h>
static pthread_barrier_t restart_gate;
static int restart_failed;
static void *retained_client(void *unused) {
    (void)unused;
    template_set_kappa(fc_false());
    pthread_barrier_wait(&restart_gate);
    pthread_barrier_wait(&restart_gate);
    RefId U=mk_universe(0); TermVarId va=declare_term(U,fc_true()); RefId A=ref_var(va);
    TermVarId vx=declare_term(A,fc_true()); RefId x=ref_var(vx);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}}; ContextId G=context_make(2,ds,fc_true());
    bool fresh=template_kappa()==fc_true();
    RefId t=mk_refl(0,A,x); const char *why="";
    CheckStatus s=check(G,fc_true(),t,mk_path_const(0,A,x,x),&why);
    printf("retained thread: fresh kappa=%d, reflexivity=%s (%s)\n",fresh,check_status_name(s),why?why:"");
    restart_failed=(!fresh)+(s!=CK_VALID); return NULL;
}
int main(int argc,char **argv) {
    setvbuf(stdout,NULL,_IONBF,0);
    const char *mode=argc>1?argv[1]:"scope-depth";
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0); TermVarId va=declare_term(U,fc_true()); RefId A=ref_var(va);
    TermVarId vx=declare_term(A,fc_true()); RefId x=ref_var(vx);
    DimVarId i=declare_dim(); CtxDecl ds[]={{S_DIM,i,0},{S_TERM,va,U},{S_TERM,vx,A}};
    ContextId G=context_make(3,ds,fc_true()); int failed=0;
    if (!strcmp(mode,"scope-depth") || !strcmp(mode,"scope-sort")) {
        ScopeId good=capture_dim1(i,x,A,0,fc_false());
        Inference q=infer(G,fc_true(),mk_hcomp(0,A,fc_false(),good,x));
        printf("well-scoped partial tube: %s\n",check_status_name(q.st));
        failed+=q.st!=CK_VALID;
        LocalDecl d={S_DIM,0,LEVEL_NONE,fc_true()};
        RefId bad=ref_var(bound_id(!strcmp(mode,"scope-depth")?1:0,0));
        ScopeId s=scope_intern(1,&d,(Val){VS_REF,bad},A,0,fc_false());
        q=infer(G,fc_true(),mk_hcomp(0,A,fc_false(),s,x));
        printf("malformed partial tube (%s): %s (%s)\n",mode,check_status_name(q.st),q.reason?q.reason:"");
        failed+=q.st!=CK_INVALID;
    } else if (!strcmp(mode,"nested-control")) {
        DimVarId j=declare_dim();
        RefId P=mk_path_const(0,A,x,x); TermVarId vp=declare_term(P,fc_true());
        G=context_extend_term(G,vp,P);
        RefId at=mk_papp_const(0,A,x,x,ref_var(vp),iv_var(i));
        ScopeId inner=capture_dim1(j,at,A,0,fc_false());
        RefId body=mk_hcomp(0,A,fc_false(),inner,x);
        ScopeId outer=capture_dim1(i,body,A,0,fc_true());
        Inference q=infer(G,fc_true(),mk_hcomp(0,A,fc_false(),outer,x));
        printf("valid outer binder used inside a nested scope: %s (%s)\n",check_status_name(q.st),q.reason?q.reason:"");
        failed+=q.st!=CK_VALID;
    } else if (!strcmp(mode,"kappa-thread")) {
        pthread_t th; pthread_barrier_init(&restart_gate,NULL,2);
        pthread_create(&th,NULL,retained_client,NULL); pthread_barrier_wait(&restart_gate);
        compiler_free(); check_free(); eval_free(); machine_free();
        machine_init(); eval_init(); check_init(); compiler_init(); (void)fc_true(); (void)fc_false();
        pthread_barrier_wait(&restart_gate); pthread_join(th,NULL); pthread_barrier_destroy(&restart_gate);
        failed+=restart_failed;
    } else if (!strcmp(mode,"kappa-restart") || !strcmp(mode,"kappa-alias")) {
        template_set_kappa(fc_false());
        compiler_free(); check_free(); eval_free(); machine_free();
        machine_init(); eval_init(); check_init(); compiler_init();
        U=mk_universe(0); va=declare_term(U,fc_true()); A=ref_var(va);
        vx=declare_term(A,fc_true()); x=ref_var(vx);
        CtxDecl fresh[]={{S_TERM,va,U},{S_TERM,vx,A}};
        G=context_make(2,fresh,fc_true());
        if (!strcmp(mode,"kappa-alias")) (void)fc_false();
        printf("fresh-machine default kappa is true: %d\n",template_kappa()==fc_true());
        RefId t=mk_refl(0,A,x);
        printf("fresh-machine default kappa is true: %d; new refl required face is true: %d\n",template_kappa()==fc_true(),ref_required(t)==fc_true());
        const char *why="";
        CheckStatus st=check(G,fc_true(),t,mk_path_const(0,A,x,x),&why);
        printf("fresh-machine refl: %s (%s)\n",check_status_name(st),why?why:"");
        failed+=template_kappa()!=fc_true(); failed+=st!=CK_VALID;
    } else return 2;
    printf("%s: %d failed expectations\n",mode,failed);
    compiler_free(); check_free(); eval_free(); machine_free(); return failed?1:0;
}

#define _POSIX_C_SOURCE 200809L
#include "../src/compiler.h"
#include "../src/net.h"
#include "assoc.h"
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
#undef W_OK /* unistd.h access() flag conflicts with eval.h's WhnfStatus */

typedef struct { ContextId G; RefId A,x; DiagramId d; pthread_barrier_t gate; } Race;
static void *diagram_reader(void *arg) {
    Race *r=arg; pthread_barrier_wait(&r->gate);
    for(size_t k=0;k<20000;k++) require(diagram_canonical(r->d)==r->x,"canonical diagram unchanged");
    return NULL;
}
static void *diagram_writer(void *arg) {
    Race *r=arg; pthread_barrier_wait(&r->gate);
    for(size_t k=0;k<3000;k++) {
        RefId fresh=ref_var(declare_term(r->A,fc_true()));
        ContextId Gx=context_extend_term(r->G,ref_var_id(fresh),r->A);
        diagram_declare(Gx,0,NULL,r->A,0,fresh);
    }
    return NULL;
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "guard";
    setvbuf(stdout, NULL, _IONBF, 0);
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U = mk_universe(0);
    TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    DimVarId i = declare_dim();
    CtxDecl ds[] = {{S_DIM,i,0},{S_TERM,va,U},{S_TERM,vx,A}};
    ContextId G = context_make(3, ds, fc_true());
    const char *why = "";
    int failed = 0;
    if (!strcmp(mode, "guard")) {
        TermVarId z = declare_term(A, fc_true());
        RefId P = mk_pi_lv(0,0,z,A,A);
        term_require_push(fc_lit(i,0));
        RefId body = mk_lam_lv(0,z,A,ref_var(z));
        term_require_pop();
        CheckStatus local = check(G,fc_true(),body,P,&why);
        printf("partial lambda checked at true: %s (%s)\n",check_status_name(local),why?why:"");
        CheckStatus guarded = check(G,fc_lit(i,0),body,P,&why);
        printf("partial lambda checked at its required face: %s\n",check_status_name(guarded));
        uint64_t ts[]={va}, dim[]={i};
        SymbolId f=define_global("partial_function",varset_make(ts,1),dimset_make(dim,1),P);
        require(set_global_body(f,body),"register body");
        CheckStatus admitted=check_admission(&why);
        printf("whole environment admission: %s (%s)\n",check_status_name(admitted),why?why:"");
        WhnfStatus st; EvalResult *r=observe_checked(G,global_ref(f),&st,&why);
        printf("checked observation: %d; result: ",st); print_result(r,stdout); printf("\n");
        failed=(local!=CK_INVALID)+(admitted!=CK_INVALID)+(guarded!=CK_VALID);
    } else if (!strcmp(mode,"false-scope")) {
        LocalDecl d={S_DIM,0,LEVEL_NONE,fc_true()};
        ScopeId s=scope_intern(1,&d,(Val){VS_REF,ref_var(bound_id(1,0))},A,0,fc_false());
        RefId bad=mk_hcomp(0,A,fc_false(),s,x);
        Inference q=infer(G,fc_false(),bad);
        printf("infer malformed scope under false: %s (%s)\n",check_status_name(q.st),q.reason?q.reason:"");
        CheckStatus ck=check(G,fc_false(),bad,A,&why);
        printf("check malformed scope under false: %s (%s)\n",check_status_name(ck),why?why:"");
        TermVarId y=declare_term(A,fc_true());
        CtxDecl target[]={{S_TERM,va,U},{S_TERM,y,A}};
        ContextId H=context_make(2,target,fc_true());
        CheckStatus mp=check_map(G,fc_false(),map_single_term(y,bad),H,fc_true(),&why);
        printf("map malformed scope under false: %s (%s)\n",check_status_name(mp),why?why:"");
        failed=(q.st!=CK_INVALID)+(ck!=CK_INVALID)+(mp!=CK_INVALID);
    } else if (!strcmp(mode,"candidate")) {
        uint64_t ts[]={va,vx};
        SymbolId f=define_global("candidate",varset_make(ts,2),dimset_make(NULL,0),A);
        Inference before=infer(G,fc_true(),global_ref(f));
        printf("opaque candidate before definition: %s\n",check_status_name(before.st));
        require(set_global_body(f,mk_universe(0)),"register invalid body while environment open");
        CheckStatus admitted=check_admission(&why);
        printf("admission after adding ill-typed body: %s (%s)\n",check_status_name(admitted),why?why:"");
        WhnfStatus st; EvalResult *r=observe_checked(G,global_ref(f),&st,&why);
        printf("checked observation: %d; result: ",st); print_result(r,stdout); printf("\n");
        failed=(before.st!=CK_VALID)+(admitted!=CK_INVALID)+(st!=W_INVALID);
    } else if (!strcmp(mode,"coe-scope")) {
        LocalDecl d={S_DIM,0,LEVEL_NONE,fc_true()};
        ScopeId s=scope_intern(1,&d,(Val){VS_REF,ref_var(bound_id(0,0))},U,1,fc_true());
        RefId bad=mk_coe(0,s,x);
        Inference q=infer(G,fc_true(),bad);
        printf("Coe with wrong-sort scope: %s (%s)\n",check_status_name(q.st),q.reason?q.reason:"");
        failed=q.st!=CK_INVALID;
    } else if (!strcmp(mode,"net-tview")) {
        RefId h=mk_hcomp_at(0,i,A,fc_true(),x,x);
        require(ref_is_tview(h),"HComp is a TVIEW");
        Inference q=infer(G,fc_true(),h);
        printf("HComp input: %s\n",check_status_name(q.st));
        Net n; net_init(&n); int8_t neg[]={-1};
        NodeId root=net_node(&n,A_ROOT,1,neg,(Payload){0});
        NodeId op=net_operation(&n,OP_APPLY_PARTIAL_DIM_BINDER,(Payload){.a=iv_one()});
        NodeId data=net_descriptor(&n,D_PARTIAL_DIM_BINDER,(Payload){.a=h,.b=0,.c=2,.d=1});
        net_connect(&n,op,1,root,0); net_connect(&n,op,0,data,0);
        net_run(&n);
        Payload out; NodeKind kind;
        bool got=net_root_read(&n,root,&kind,&out);
        printf("partial dimension binder applied: %d\n",got);
        failed=q.st!=CK_VALID || !got || kind!=D_PARTIAL || out.face!=fc_true() || out.ref!=x;
        net_free(&n);
    } else if (!strcmp(mode,"net-race")) {
        Net n; net_init(&n);
        int8_t neg[]={-1}, hp[]={1,-1}, dp[]={-1,1,1};
        enum { COUNT=6000 };
        NodeId *roots=calloc(2*COUNT,sizeof *roots);
        for(size_t k=0;k<COUNT;k++) {
            NodeId h=net_node(&n,A_HEAD,2,hp,(Payload){0});
            net_node_ptr(&n,h)->tag=T_FST;
            NodeId d=net_node(&n,A_DUP,3,dp,(Payload){0});
            NodeId op=net_operation(&n,OP_REINDEX_TERM,(Payload){.a=map_identity()});
            NodeId v=net_descriptor(&n,D_REF,(Payload){.ref=x});
            for(size_t j=0;j<2;j++) { roots[2*k+j]=net_node(&n,A_ROOT,1,neg,(Payload){0}); net_connect(&n,d,j+1,roots[2*k+j],0); }
            net_connect(&n,h,1,op,1);
            net_connect(&n,d,0,h,0); net_connect(&n,op,0,v,0);
        }
        net_set_workers(&n,4); net_run(&n);
        for(size_t k=0;k<2*COUNT;k++) {
            Endpoint h=net_peer(&n,roots[k],0); Endpoint v=net_peer(&n,h.node,1);
            Node *value=net_node_ptr(&n,v.node);
            failed+=value->kind!=D_REF || value->p.ref!=x;
        }
        printf("adjacent net pairs: rewrites=%zu, retries=%zu\n",n.rewrites,n.retries);
        failed+=n.rewrites!=3*COUNT;
        free(roots); net_free(&n);
    } else if (!strcmp(mode,"diagram-race")) {
        Race r={.G=G,.A=A,.x=x};
        r.d=diagram_declare(G,0,NULL,A,0,x); diagram_canonical(r.d);
        pthread_barrier_init(&r.gate,NULL,2);
        pthread_t a,b; pthread_create(&a,NULL,diagram_reader,&r); pthread_create(&b,NULL,diagram_writer,&r);
        pthread_join(a,NULL); pthread_join(b,NULL); pthread_barrier_destroy(&r.gate);
        printf("concurrent diagram registration and lookup complete\n");
    } else if (!strcmp(mode,"diagram-session")) {
        RefId path=mk_path_const(0,A,x,x);
        RefId wrong=mk_refl(0,U,x);
        DiagramId d=diagram_declare(G,0,NULL,path,0,wrong);
        CheckStatus before=diagram_validate(d,fc_true(),&why);
        printf("diagram before reset: %s (%s)\n",check_status_name(before),why?why:"");
        char *expected=strdup(why?why:"");
        check_open_environment(); why="";
        CheckStatus after=diagram_validate(d,fc_true(),&why);
        printf("diagram after reset: %s (%s)\n",check_status_name(after),why?why:"");
        failed=(before!=CK_INVALID)+(after!=CK_INVALID)+(!why || strcmp(expected,why)!=0);
        free(expected);
    } else if (!strcmp(mode,"positive")) {
        if(getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
        Assoc a; assoc_build(&a,&why);
        require(a.T,"associativity identity compiles");
        failed+=certificate_verify(a.T,&why)!=CK_VALID;
        MapId s=assoc_sigma(&a,a.rhs);
        RefId left=assoc_left_arg(&a,s), right=assoc_right_arg(&a,s);
        RefId calls[]={mk_transform_call(a.T,DIR_FORWARD,s,left),mk_transform_call(a.T,DIR_REVERSE,s,right)};
        for(size_t k=0;k<2;k++) {
            WhnfStatus st; EvalResult *r=observe_checked(a.G,calls[k],&st,&why);
            printf("checked identity orientation %zu: status=%d, class=%d, head=%s\n",k,st,r?(int)r->cls:-1,r?tag_name(ref_tag(r->ref)):"absent");
            failed+=st!=W_OK || !r || r->cls!=R_INTRODUCTION || ref_tag(r->ref)!=T_PAIR;
            EvalEvents before=eval_events(); EvalNetEvents n0=eval_net_events();
            EvalResult *again=observe_checked(a.G,calls[k],&st,&why);
            EvalEvents after=eval_events(); EvalNetEvents n1=eval_net_events();
            failed+=again!=r || st!=W_OK || before.publish!=after.publish || n0.apply!=n1.apply;
        }
    } else if (!strcmp(mode,"universe") || !strcmp(mode,"packed-level")) {
        /* Overflow is a host failure. Isolate that permitted rejection from
         * the test runner; silently accepting a wrapped level must fail. */
        pid_t child=fork(); require(child>=0,"fork");
        if(child==0) {
            Inference q;
            if(!strcmp(mode,"universe")) {
                ContextId empty=context_make(0,NULL,fc_true());
                q=infer(empty,fc_true(),mk_universe(UINT64_MAX));
                printf("infer U_UINT64_MAX: %s; type: ",check_status_name(q.st));
            } else {
                TermVarId z=declare_term(A,fc_true());
                RefId p=mk_pi_lv(UINT64_C(1)<<32,0,z,A,A);
                q=infer(G,fc_true(),p);
                printf("Pi with domain level 2^32: stored level=%llu, %s; type: ",(unsigned long long)levels_first(origin_levels(ref_origin(p))),check_status_name(q.st));
            }
            if(q.type) print_ref(q.type,stdout);
            printf("\n");
            _exit(q.st==CK_INVALID?0:1);
        }
        int status; require(waitpid(child,&status,0)==child,"waitpid");
        failed=!((WIFSIGNALED(status)&&WTERMSIG(status)==SIGABRT)||(WIFEXITED(status)&&WEXITSTATUS(status)==0));
    } else return 2;
    printf("%s: %d failed expectations\n",mode,failed);
    compiler_free(); check_free(); eval_free(); machine_free();
    return failed?1:0;
}

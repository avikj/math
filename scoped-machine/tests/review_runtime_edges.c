#define _GNU_SOURCE
#include "runtime.h"
#include "proof.h"
#include <assert.h>
#include <pthread.h>
#include <string.h>

static TermVarId v(RefId t) { return declare_term(t,fc_true()); }
static RefId a2(RefId f,RefId x,RefId y){return mk_app(mk_app(f,x),y);}
static int levels(void) {
    RefId U=mk_universe(2);TermVarId va=v(U);RefId A=ref_var(va);
    TermVarId vt=v(A);RefId t=ref_var(vt);
    TermVarId vx=v(A);RefId X=ref_var(vx),E=mk_path_const(2,A,t,X);TermVarId ve=v(E);
    RefId DT=mk_pi_lv(2,2,vx,A,mk_pi_lv(2,1,ve,E,mk_universe(0)));
    TermVarId vd=v(DT);RefId D=ref_var(vd);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vt,A},{S_TERM,vd,DT}};ContextId G=context_make(3,ds,fc_true());
    const char *why="";assert(check_context(G,&why)==CK_VALID);
    RefId S=mk_sigma_lv(2,2,vx,A,mk_sigma_lv(2,0,ve,E,a2(D,X,ref_var(ve))));
    RefId Z=a2(D,t,mk_refl(2,A,t));RefId M=rt_maps_type(2,0,S,Z);
    CheckStatus st=check(G,fc_true(),rt_singleton_maps(2,0,A,t,D),M,&why);
    printf("singleton a=2 r=0 expected=VALID observed=%s reason=%s\n",check_status_name(st),why);
    return st!=CK_VALID;
}
static int commute(void) {
    TermVarId va=v(mk_universe(0));RefId A=ref_var(va);
    TermVarId vx=v(A),vy=v(A);RefId x=ref_var(vx),y=ref_var(vy);
    RefId Px=mk_path_const(0,A,x,x),Py=mk_path_const(0,A,y,y);
    TermVarId vp=v(Px),vq=v(Py);RefId p=ref_var(vp),q=ref_var(vq);
    MapBuilder mb;mapb_init(&mb);mapb_term(&mb,vx,y);mapb_term(&mb,vp,q);MapId m=mapb_finish(&mb);
    RefId id=mk_id_fun(0,A);
    RefId ap0=rt_ap(0,0,A,A,id,x,x,p),ap1=rt_ap(0,0,A,A,id,y,y,q);
    TermVarId vb=v(A);RefId O=mk_lam_lv(0,vb,A,A);
    RefId r0=rt_reuse(0,0,A,O,x,x,p,x),r1=rt_reuse(0,0,A,O,y,y,q,y);
    TermVarId vz=v(A);RefId Ez=mk_path_const(0,A,x,ref_var(vz));TermVarId ve=v(Ez);
    RefId P=mk_lam_lv(0,vz,A,mk_lam_lv(0,ve,Ez,A));
    RefId j0=rt_J(0,0,A,x,P,x,x,p),j1=rt_J(0,0,A,y,reindex(P,m),y,y,q);
    CtxDecl ds[]={{S_TERM,va,mk_universe(0)},{S_TERM,vx,A},{S_TERM,vy,A},{S_TERM,vp,Px},{S_TERM,vq,Py}};
    ContextId ctx=context_make(5,ds,fc_true());const char *why;
    assert(check_context(ctx,&why)==CK_VALID);
    assert(check(ctx,fc_true(),ap0,Px,&why)==CK_VALID);
    assert(check(ctx,fc_true(),ap1,Py,&why)==CK_VALID);
    assert(check(ctx,fc_true(),r0,A,&why)==CK_VALID);
    assert(check(ctx,fc_true(),r1,A,&why)==CK_VALID);
    assert(check(ctx,fc_true(),j0,A,&why)==CK_VALID);
    assert(check(ctx,fc_true(),j1,A,&why)==CK_VALID);
    assert(convert_term(ctx,fc_true(),reindex(ap0,m),ap1,Py)==CV_EQUAL);
    assert(convert_term(ctx,fc_true(),reindex(r0,m),r1,A)==CV_EQUAL);
    assert(convert_term(ctx,fc_true(),reindex(j0,m),j1,A)==CV_EQUAL);
    puts("all six helper terms typecheck; all three substitution pairs convert equal");
    bool ok1=reindex(ap0,m)==ap1,ok2=reindex(r0,m)==r1,ok3=reindex(j0,m)==j1;
    printf("fixed-template substitution equality: ap=%d reuse=%d J=%d (expected all 1)\n",ok1,ok2,ok3);
    return !(ok1&&ok2&&ok3);
}
static int residual(void) {
    RefId U=mk_universe(0);TermVarId va=v(U);RefId AA=ref_var(va);TermVarId vt=v(AA);RefId t=ref_var(vt);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vt,AA}};ContextId ctx=context_make(2,ds,fc_true());
    TermVarId x1=v(AA),e1=v(mk_path_const(0,AA,t,ref_var(x1)));
    TermVarId x2=v(AA),e2=v(mk_path_const(0,AA,ref_var(x1),ref_var(x2)));
    DiagNode nodes[]={{1,x1,e1,AA,0,t},{2,x2,e2,AA,0,ref_var(x1)}};
    RefId Z=mk_path_const(0,AA,ref_var(x2),ref_var(x2));
    DiagramId d=residual_declare(ctx,2,nodes,Z,0);const char *why;
    assert(diagram_validate(d,fc_true(),&why)==CK_VALID);
    RefId ty,term=rt_diagram_export(d,&ty);
    CheckStatus st=check(ctx,fc_true(),term,ty,&why);
    printf("two-node dependent residual export expected=VALID observed=%s reason=%s\n",check_status_name(st),why);
    return st!=CK_VALID;
}
static pthread_barrier_t gate;
static RefId A,proof,type;static ContextId G;static bool audit;
static void *client(void *p) {
    pthread_barrier_wait(&gate);
    if(audit) { ProofUse r=proof_use(G,fc_true(),proof,type);assert(r.status==PU_CORE); }
    else { RefId r=rt_maps_id(0,A);assert(r); }
    return NULL;
}
static int cold(bool pu) {
    audit=pu;TermVarId va=v(mk_universe(0));A=ref_var(va);TermVarId vx=v(A);RefId x=ref_var(vx);
    CtxDecl ds[]={{S_TERM,va,mk_universe(0)},{S_TERM,vx,A}};G=context_make(2,ds,fc_true());
    proof=mk_refl(0,A,x);type=mk_path_const(0,A,x,x);const char *why;
    assert(check(G,fc_true(),proof,type,&why)==CK_VALID);
    pthread_t ts[8];pthread_barrier_init(&gate,NULL,8);
    for(int i=0;i<8;i++)assert(!pthread_create(ts+i,NULL,client,NULL));
    for(int i=0;i<8;i++)assert(!pthread_join(ts[i],NULL));
    pthread_barrier_destroy(&gate);puts("cold concurrent calls completed");return 0;
}
int main(int argc,char **argv) {
    assert(argc==2);machine_init();eval_init();check_init();compiler_init();check_set_budget(0);
    int bad=!strcmp(argv[1],"levels")?levels():!strcmp(argv[1],"commute")?commute():!strcmp(argv[1],"residual")?residual():cold(!strcmp(argv[1],"proof-cold"));
    compiler_free();check_free();eval_free();machine_free();return bad;
}

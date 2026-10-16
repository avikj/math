#include "../src/compiler.h"
#include <stdio.h>
int main(void) {
    setvbuf(stdout,NULL,_IONBF,0);
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0);
    TermVarId va=declare_term(U,fc_true()); RefId A=ref_var(va);
    TermVarId vx=declare_term(A,fc_true()); RefId x=ref_var(vx);
    CtxDecl ds[]={{S_TERM,va,U},{S_TERM,vx,A}};
    ContextId G=context_make(2,ds,fc_true());
    LocalDecl d={S_DIM,0,LEVEL_NONE,fc_true()};
    ScopeId s=scope_intern(1,&d,(Val){VS_REF,ref_var(bound_id(1,0))},A,0,fc_false());
    RefId bad=mk_hcomp(0,A,fc_false(),s,x);
    RefId wrapped=mk_fst(bad);
    const char *why="";
    bool direct=ref_validate(bad,&why);
    bool nested=ref_validate(wrapped,&why);
    Inference q=infer(G,fc_false(),wrapped);
    CheckStatus ck=check(G,fc_false(),wrapped,A,&why);
    TermVarId vy=declare_term(A,fc_true());
    CtxDecl hs[]={{S_TERM,va,U},{S_TERM,vy,A}};
    ContextId H=context_make(2,hs,fc_true());
    CheckStatus mp=check_map(G,fc_false(),map_single_term(vy,wrapped),H,fc_true(),&why);
    printf("direct valid=%d; nested valid=%d; infer=%s; check=%s; map=%s\n",direct,nested,check_status_name(q.st),check_status_name(ck),check_status_name(mp));
    int failed=direct || nested || q.st!=CK_INVALID || ck!=CK_INVALID || mp!=CK_INVALID;
    FaceId fs[]={fc_false(),fc_true()}; RefId ts[]={bad,x};
    RefId system=mk_system(2,fs,ts);
    CheckStatus sc=check(G,fc_true(),system,A,&why);
    printf("system with malformed scope in false branch at true: %s\n",check_status_name(sc));
    failed+=sc!=CK_INVALID;
    ScopeId outer=scope_intern(0,NULL,(Val){VS_REF,wrapped},A,0,fc_false());
    bool ov=scope_validate(outer,&why);
    printf("scope containing raw wrapper: valid=%d\n",ov); failed+=ov;
    ScopeId good=scope_intern(1,&d,(Val){VS_REF,x},A,0,fc_false());
    RefId ok=mk_hcomp(0,A,fc_false(),good,x);
    TermVarId z=declare_term(A,fc_true()); RefId S=mk_sigma_lv(0,0,z,A,A);
    RefId projected=mk_fst(mk_pair_at_lv(0,S,ok,x));
    bool pv=ref_validate(projected,&why);
    CheckStatus pc=check(G,fc_true(),projected,A,&why);
    printf("valid scope below raw pair/fst: valid=%d; check=%s\n",pv,check_status_name(pc));
    failed+=!pv || pc!=CK_VALID;
    compiler_free(); check_free(); eval_free(); machine_free();
    return failed;
}

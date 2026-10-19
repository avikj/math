#include "../src/compiler.h"
#include <assert.h>

static RefId pair(RefId S, RefId a, RefId b) { return mk_pair_at_lv(0,S,a,b); }
static RefId app2(RefId f, RefId x, RefId y) { return mk_app(mk_app(f,x),y); }
static void valid(ContextId G, RefId t, RefId T, const char *label) {
    const char *why=""; CheckStatus st=check(G,fc_true(),t,T,&why);
    if(st!=CK_VALID) { fprintf(stderr,"%s: %s %s\n",label,check_status_name(st),why); abort(); }
    printf("PASS %s\n",label);
}
int main(void) {
    machine_init(); check_init();
    RefId U=mk_universe(0); TermVarId vA=declare_term(U,fc_true()); RefId A=ref_var(vA);
    TermVarId vt=declare_term(A,fc_true()); RefId t=ref_var(vt);
    TermVarId vx=declare_term(A,fc_true()); RefId x=ref_var(vx), Ex=mk_path_const(0,A,t,x);
    TermVarId ve=declare_term(Ex,fc_true()); RefId e=ref_var(ve);
    RefId DT=mk_pi_lv(0,1,vx,A,mk_pi_lv(0,1,ve,Ex,U));
    TermVarId vD=declare_term(DT,fc_true()); RefId D=ref_var(vD), Dx=app2(D,x,e), refl=mk_refl(0,A,t);
    CtxDecl ds[]={{S_TERM,vA},{S_TERM,vt},{S_TERM,vD}};
    ContextId G=context_make(3,ds,fc_true());
    RefId S=mk_sigma_lv(0,0,vx,A,mk_sigma_lv(0,0,ve,Ex,Dx)), Z=app2(D,t,refl);
    ScopeId DS=capture_term2(vx,A,0,ve,Ex,0,Dx,U,1,fc_true());
    TermVarId vr=declare_term(S,fc_true()); RefId r=ref_var(vr);
    RefId rx=mk_fst(r), re=mk_fst(mk_snd(r)), rz=mk_snd(mk_snd(r));
    RefId downBody=mk_down(0,0,A,t,DS,rx,re,rz), down=mk_lam_lv(0,vr,S,downBody);
    TermVarId vz=declare_term(Z,fc_true()); RefId z=ref_var(vz);
    RefId inner=apply_term_binder(S,0,1,t);
    RefId upBody=pair(S,t,pair(inner,refl,z)), up=mk_lam_lv(0,vz,Z,upBody);
    valid(G,down,mk_fun(0,0,S,Z),"generic singleton down");
    valid(G,up,mk_fun(0,0,Z,S),"generic singleton up");
    DimVarId i=declare_dim(), j=declare_dim(), k=declare_dim();
    RefId xi=mk_papp_const(0,A,t,rx,re,iv_var(i));
    RefId ei=mk_plam(j,mk_papp_const(0,A,t,rx,re,iv_meet(iv_var(i),iv_var(j))));
    RefId xk=mk_papp_const(0,A,t,rx,re,iv_negate(iv_var(k)));
    RefId ek=mk_plam(j,mk_papp_const(0,A,t,rx,re,iv_meet(iv_negate(iv_var(k)),iv_var(j))));
    RefId Dk=app2(D,xk,ek), empty=mk_system(0,NULL,NULL);
    RefId zi=mk_fill_at(0,k,Dk,fc_false(),empty,rz,iv_negate(iv_var(i)));
    RefId inneri=apply_term_binder(S,0,1,xi);
    RefId hbody=mk_plam(i,pair(S,xi,pair(inneri,ei,zi)));
    RefId h=mk_lam_lv(0,vr,S,hbody);
    RefId HT=mk_pi_lv(0,0,vr,S,mk_path_const(0,S,mk_app(up,mk_app(down,r)),r));
    valid(G,h,HT,"generic dependent singleton up-down homotopy");
    RefId constantFill=mk_fill_at(0,k,Z,fc_false(),empty,z,iv_negate(iv_var(i)));
    RefId eps=mk_lam_lv(0,vz,Z,mk_plam(i,constantFill));
    RefId ET=mk_pi_lv(0,0,vz,Z,mk_path_const(0,Z,mk_app(down,mk_app(up,z)),z));
    valid(G,eps,ET,"generic dependent singleton down-up homotopy");
    check_free(); machine_free();
    return 0;
}

#include "../src/compiler.h"
#include <assert.h>

static RefId w_maps(RefId X, RefId Y) {
    RefId FT=mk_fun(0,0,X,Y), GT=mk_fun(0,0,Y,X);
    TermVarId f=declare_term(FT,fc_true()), g=declare_term(GT,fc_true());
    TermVarId x=declare_term(X,fc_true()), y=declare_term(Y,fc_true());
    RefId HT=mk_pi_lv(0,0,x,X,mk_path_const(0,X,mk_app(ref_var(g),mk_app(ref_var(f),ref_var(x))),ref_var(x)));
    RefId KT=mk_pi_lv(0,0,y,Y,mk_path_const(0,Y,mk_app(ref_var(f),mk_app(ref_var(g),ref_var(y))),ref_var(y)));
    TermVarId h=declare_term(HT,fc_true());
    return mk_sigma_lv(0,0,f,FT,mk_sigma_lv(0,0,g,GT,mk_sigma_lv(0,0,h,HT,KT)));
}
static RefId w_diagram_type(RefId B) {
    TermVarId c=declare_term(B,fc_true()), y=declare_term(B,fc_true());
    RefId RT=mk_pi_lv(0,1,y,B,mk_universe(0)); TermVarId R=declare_term(RT,fc_true());
    RefId M=mk_pi_lv(0,0,y,B,w_maps(mk_app(ref_var(R),ref_var(y)),mk_path_const(0,B,ref_var(c),ref_var(y))));
    return mk_sigma_lv(0,1,c,B,mk_sigma_lv(1,0,R,RT,M));
}
static RefId value(RefId d) { return mk_fst(d); }
static RefId realization(RefId d,RefId y) { return mk_app(mk_fst(mk_snd(d)),y); }
static RefId pair_maps(RefId d,RefId y) { return mk_app(mk_snd(mk_snd(d)),y); }
static RefId collapse(RefId d,RefId y) { return mk_fst(pair_maps(d,y)); }
static RefId expand(RefId d,RefId y) { return mk_fst(mk_snd(pair_maps(d,y))); }
static void verify(ContextId G,RefId t,RefId T,const char *name) {
    const char *why=""; CheckStatus s=check(G,fc_true(),t,T,&why);
    if(s!=CK_VALID) { fprintf(stderr,"%s: %s %s\n",name,check_status_name(s),why); abort(); }
    printf("PASS %s\n",name);
}
int main(void) {
    machine_init(); eval_init(); check_init();
    RefId U=mk_universe(0); TermVarId vB=declare_term(U,fc_true()); RefId B=ref_var(vB);
    CtxDecl decl={S_TERM,vB}; ContextId G=context_make(1,&decl,fc_true());
    RefId DT=w_diagram_type(B); uint64_t level=99; const char *why="";
    assert(check_is_type(G,fc_true(),DT,&level,&why)==CK_VALID && level==1);
    TermVarId l=declare_term(DT,fc_true()), r=declare_term(DT,fc_true()); RefId L=ref_var(l),R=ref_var(r);
    RefId PT=mk_path_const(0,B,value(L),value(R)); TermVarId p=declare_term(PT,fc_true()),y=declare_term(B,fc_true());
    RefId Y=ref_var(y), P=ref_var(p), RL=realization(L,Y), RR=realization(R,Y);
    TermVarId a=declare_term(RL,fc_true()),b=declare_term(RR,fc_true());
    RefId qp=mk_path_concat(0,B,value(R),value(L),Y,mk_path_rev(0,B,value(L),value(R),P),mk_app(collapse(L,Y),ref_var(a)));
    RefId qm=mk_path_concat(0,B,value(L),value(R),Y,P,mk_app(collapse(R,Y),ref_var(b)));
    RefId F=mk_lam_lv(0,a,RL,mk_app(expand(R,Y),qp)), FT=mk_pi_lv(0,0,a,RL,RR);
    RefId H=mk_lam_lv(0,b,RR,mk_app(expand(L,Y),qm)), HT=mk_pi_lv(0,0,b,RR,RL);
    TermVarId ids[]={y,p,r,l}; RefId types[]={B,PT,DT,DT}; uint64_t domain_levels[]={0,0,1,1}, codomain_levels[]={0,0,0,1};
    for(size_t k=0;k<4;k++) {
        F=mk_lam_lv(domain_levels[k],ids[k],types[k],F);
        H=mk_lam_lv(domain_levels[k],ids[k],types[k],H);
        FT=mk_pi_lv(domain_levels[k],codomain_levels[k],ids[k],types[k],FT);
        HT=mk_pi_lv(domain_levels[k],codomain_levels[k],ids[k],types[k],HT);
    }
    verify(G,F,FT,"fully parameterized forward identity action on diagram values");
    verify(G,H,HT,"fully parameterized reverse identity action on diagram values");
    { Inference I=infer(context_make(0,NULL,fc_true()),fc_true(),id_action(0,0,0));
      if(I.st!=CK_VALID) { fprintf(stderr,"production id_action: %s %s\n",check_status_name(I.st),I.reason?I.reason:""); abort(); }
      printf("PASS production id_action(0,0,0) with both inverse proofs is a closed typed term\n"); }
    check_free(); eval_free(); machine_free(); return 0;
}

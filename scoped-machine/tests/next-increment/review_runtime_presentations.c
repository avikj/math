/* Existing-core witness: runtime-computed presentations are ordinary data.
 * No diagram/transform is registered. All maps and inverse witnesses are terms.
 */
#include "../src/compiler.h"
#include <assert.h>

static RefId qinv(RefId X, RefId Y) {
    RefId F=mk_fun(0,0,X,Y), G=mk_fun(0,0,Y,X);
    TermVarId f=declare_term(F,fc_true()), g=declare_term(G,fc_true());
    TermVarId x=declare_term(X,fc_true()), y=declare_term(Y,fc_true());
    RefId H=mk_pi_lv(0,0,x,X,mk_path_const(0,X,mk_app(ref_var(g),mk_app(ref_var(f),ref_var(x))),ref_var(x)));
    RefId K=mk_pi_lv(0,0,y,Y,mk_path_const(0,Y,mk_app(ref_var(f),mk_app(ref_var(g),ref_var(y))),ref_var(y)));
    TermVarId h=declare_term(H,fc_true());
    return mk_sigma_lv(0,0,f,F,mk_sigma_lv(0,0,g,G,mk_sigma_lv(0,0,h,H,K)));
}
static RefId presentation(RefId Z) {
    RefId U=mk_universe(0); TermVarId R=declare_term(U,fc_true());
    return mk_sigma_lv(1,0,R,U,qinv(ref_var(R),Z));
}
static RefId tuple(RefId type, RefId a, RefId b, uint64_t level) {
    return mk_pair_at_lv(level,type,a,b);
}
static RefId identity_presentation(RefId A, RefId PT) {
    RefId id=mk_id_fun(0,A), Q=apply_term_binder(PT,0,1,A);
    RefId Qg=apply_term_binder(Q,0,1,id), Qh=apply_term_binder(Qg,0,1,id);
    TermVarId x=declare_term(A,fc_true());
    RefId h=mk_lam_lv(0,x,A,mk_refl(0,A,ref_var(x)));
    RefId q=tuple(Q,id,tuple(Qg,id,tuple(Qh,h,h,0),0),0);
    return tuple(PT,A,q,1);
}
static RefId ptype(RefId P) { return mk_fst(P); }
static RefId collapse(RefId P) { return mk_fst(mk_snd(P)); }
static RefId expand(RefId P) { return mk_fst(mk_snd(mk_snd(P))); }
static void valid(ContextId G, RefId t, RefId T) {
    const char *why=""; CheckStatus st=check(G,fc_true(),t,T,&why);
    if(st!=CK_VALID) { fprintf(stderr,"check: %s %s\n",check_status_name(st),why); abort(); }
}
int main(void) {
    machine_init(); eval_init(); check_init(); compiler_init();
    RefId U=mk_universe(0); TermVarId aT=declare_term(U,fc_true()); RefId A=ref_var(aT);
    TermVarId a=declare_term(A,fc_true()); RefId av=ref_var(a);
    CtxDecl ds[]={{S_TERM,aT,U},{S_TERM,a,A}}; ContextId G=context_make(2,ds,fc_true());
    RefId PT=presentation(A), P0=identity_presentation(A,PT);
    valid(G,P0,PT);
    TermVarId p=declare_term(PT,fc_true()), q=declare_term(PT,fc_true());
    RefId pv=ref_var(p), qv=ref_var(q); TermVarId r=declare_term(ptype(pv),fc_true());
    RefId body=mk_app(expand(qv),mk_app(collapse(pv),ref_var(r)));
    RefId action=mk_lam_lv(1,p,PT,mk_lam_lv(1,q,PT,mk_lam_lv(0,r,ptype(pv),body)));
    RefId actionT=mk_pi_lv(1,1,p,PT,mk_pi_lv(1,0,q,PT,mk_pi_lv(0,0,r,ptype(pv),ptype(qv))));
    valid(G,action,actionT);
    TermVarId z=declare_term(PT,fc_true()); RefId delay=mk_lam_lv(1,z,PT,ref_var(z));
    RefId P=mk_app(delay,P0), Q=mk_app(delay,mk_app(delay,P0));
    RefId call=mk_app(mk_app(mk_app(action,P),Q),av);
    assert(transform_count()==0);
    const char *why=""; WhnfStatus status; EvalResult *ans=observe_checked(G,call,&status,&why);
    assert(status==W_OK && ans && ans->ref==av && transform_count()==0);
    printf("PASS computed presentations: checked generic action, result is input, registered transforms=%zu\n",transform_count());
    compiler_free(); check_free(); eval_free(); machine_free();
    return 0;
}

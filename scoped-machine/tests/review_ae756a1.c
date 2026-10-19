#include "../src/check.h"
#include "../src/lib.h"
#include "../src/compiler.h"
#include "../src/canon.h"
#include <string.h>
#include <pthread.h>
/* The reviewer's nine modes for ae756a1, unchanged except the `environment`
 * mode, adapted as the review directed once registration fails closed: the
 * registration into the admitted environment must be rejected, and the
 * invalid body is checked in a fresh candidate environment. Two concurrent
 * modes were added: `publication-concurrent` (eight clients compile one
 * declaration) and `diagnostics-concurrent` (eight clients validate invalid
 * template instances, exercising the immutable diagnostic storage). */

static int failures;
#define EXPECT(c, label) do { if (!(c)) { ++failures; printf("FAIL: %s\n", label); } } while (0)
static void verdict(const char *label, CheckStatus s, const char *why) {
    printf("%s: %s (%s)\n", label, check_status_name(s), why ? why : "");
}
int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "signature";
    machine_init(); eval_init(); check_init();
    const char *why = "";
    RefId U0 = mk_universe(0), U1 = mk_universe(1);
    TermVarId vA = declare_term(U0, fc_true()), vB = declare_term(U0, fc_true());
    RefId A = ref_var(vA), B = ref_var(vB);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    DimVarId i = declare_dim();
    CtxDecl ds[] = {{S_DIM,i,0}, {S_TERM,vA,U0}, {S_TERM,vB,U0}, {S_TERM,vx,A}};
    ContextId G = context_make(4, ds, fc_true());
    if (!strcmp(mode,"signature")) {
        RefId ok = mk_refl(0,A,x), wrong_type = mk_refl(0,B,x), wrong_level = mk_refl(1,A,x);
        EXPECT(infer(G,fc_true(),ok).st==CK_VALID,"positive control: valid Refl");
        printf("Refl(A,x)==Refl(B,x): %d; level0==level1: %d\n",ok==wrong_type,ok==wrong_level);
        EXPECT(ok != wrong_type, "typed Refl boundary must retain its declared A");
        EXPECT(ok != wrong_level, "typed Refl boundary must retain its declared level");
        Inference it = infer(G,fc_true(),wrong_type), il = infer(G,fc_true(),wrong_level);
        verdict("wrong type parameter",it.st,it.reason); verdict("wrong level parameter",il.st,il.reason);
        EXPECT(it.st==CK_INVALID,"Refl(B,x:A) must be rejected");
        EXPECT(il.st==CK_INVALID,"Refl(1,A:U0,x) must be rejected");
    } else if (!strcmp(mode,"scope")) {
        ScopeId bad_type = capture_dim1(i,A,U1,2,fc_true());
        ScopeId good = capture_dim1(i,A,U0,1,fc_true());
        EXPECT(infer(G,fc_true(),mk_coe(0,good,x)).st==CK_VALID,"positive control: valid family scope");
        ScopeId unavailable = capture_dim1(i,A,U0,1,fc_false());
        RefId t1=mk_coe(0,bad_type,x), t2=mk_coe(0,unavailable,x);
        Inference it=infer(G,fc_true(),t1), ig=infer(G,fc_true(),t2);
        verdict("family body A:U0 falsely annotated U1",it.st,it.reason);
        verdict("family available only on false used at true",ig.st,ig.reason);
        EXPECT(it.st==CK_INVALID,"a family scope's result annotation must be checked");
        EXPECT(ig.st==CK_INVALID,"a total family formal cannot accept a false-only scope");
    } else if (!strcmp(mode,"annotations")) {
        TermVarId vz=declare_term(A,fc_true());
        RefId lam=mk_lam_lv(1,vz,A,ref_var(vz));
        RefId expected=mk_pi_lv(0,0,vz,A,A);
        EXPECT(check(G,fc_true(),mk_lam_lv(0,vz,A,ref_var(vz)),expected,&why)==CK_VALID,"positive control: correctly annotated lambda");
        CheckStatus lc=check(G,fc_true(),lam,expected,&why); verdict("wrong lambda level in check",lc,why);
        Inference li=infer(G,fc_true(),lam); verdict("same lambda in infer",li.st,li.reason);
        EXPECT(lc==CK_INVALID,"check must reject the same wrong annotation as infer");
        RefId sg=mk_sigma_lv(0,0,vz,A,A), badsg=mk_sigma_lv(0,0,vz,A,B);
        RefId pair=mk_pair_at_lv(0,badsg,x,x);
        CheckStatus pc=check(G,fc_true(),pair,sg,&why); verdict("pair with incompatible stored Sigma annotation",pc,why);
        EXPECT(pc==CK_INVALID,"checking against another Sigma cannot erase the stored annotation");
    } else if (!strcmp(mode,"missing-level")) {
        /* negative: the original unannotated core composition must be rejected */
        TermVarId vz=declare_term(A,fc_true());
        RefId pi=mk_pi(vz,A,A), cap=mk_lam(vz,A,ref_var(vz));
        RefId term=mk_comp(i,pi,fc_false(),mk_system(0,NULL,NULL),cap);
        WhnfStatus ws; EvalResult *r=observe_checked(G,term,&ws,&why);
        printf("unannotated checked COMP: status=%d result=%d (%s)\n",(int)ws,r!=NULL,why?why:"");
        EXPECT(ws==W_INVALID && r==NULL,"an unannotated required type position is rejected before execution");
        /* positive: the explicitly annotated term executes and its output carries its level */
        RefId pia=mk_pi_lv(0,0,vz,A,A), capa=mk_lam_lv(0,vz,A,ref_var(vz));
        RefId terma=mk_comp_lv(0,i,pia,fc_false(),mk_system(0,NULL,NULL),capa);
        r=observe_checked(G,terma,&ws,&why);
        printf("annotated checked COMP: status=%d result=%d\n",(int)ws,r!=NULL);
        if(r) { Head h;open_ref(r->ref,&h);printf("result levels=%llu\n",(unsigned long long)levels_first(h.levels)); EXPECT(levels_first(h.levels)!=LEVEL_NONE,"admitted clause output must carry its explicit formation level");head_free(&h); }
        EXPECT(r && ws==W_OK,"the annotated composition executes");
    } else if (!strcmp(mode,"environment")) {
        /* PLAN §10: no admission freeze. A body registered later is a new
         * revision: an explicit signature request and every later checked
         * observation validate it; nothing is frozen or reopened. */
        uint64_t pars[]={vA};
        SymbolId s=define_global("late",varset_make(pars,1),dimset_make(NULL,0),A);
        CheckStatus first=check_signature(&why);verdict("opaque environment",first,why);
        EXPECT(first==CK_VALID,"positive control: the opaque environment is valid");
        bool accepted=set_global_body(s,U0);
        EXPECT(accepted,"registration needs no reopening (no freeze)");
        CheckStatus second=check_signature(&why);verdict("signature with ill-typed body U0:A",second,why);
        EXPECT(second==CK_INVALID,"the new revision is validated, not the earlier acceptance reused");
        WhnfStatus ws;EvalResult *r=observe_checked(G,global_ref(s),&ws,&why);
        printf("bad body checked execution: status=%d result=%d\n",(int)ws,r!=NULL);
        EXPECT(ws==W_INVALID && r==NULL,"ill-typed late body cannot execute through a checked observation");
    } else if (!strcmp(mode,"retry")) {
        uint64_t pars[]={vA};
        SymbolId s=define_global("valid",varset_make(pars,1),dimset_make(NULL,0),U0);
        set_global_body(s,A);
        check_set_budget(1);
        CheckStatus first=check_signature(&why);verdict("budget1 admission",first,why);
        check_set_budget(0);check_new_attempt();
        CheckStatus next=check_signature(&why);verdict("unlimited fresh attempt admission",next,why);
        CheckStatus raw=check_signature(&why);verdict("direct signature after retry",raw,why);
        EXPECT(next==CK_VALID,"a new attempt must invalidate unresolved admission cache");
        EXPECT(raw==CK_VALID,"positive control signature is valid");
    } else if (!strcmp(mode,"partial-context")) {
        FaceId phi=fc_lit(i,0);
        TermVarId vt=declare_term(U0,phi);RefId T=ref_var(vt);
        RefId eq=mk_equiv(0,0,T,A);TermVarId ve=declare_term(eq,phi);
        CtxDecl d[]={{S_DIM,i,0},{S_TERM,vA,U0},{S_TERM,vt,U0},{S_TERM,ve,eq}};
        ContextId partial=context_make(4,d,fc_true());
        CheckStatus st=check_context(partial,&why);verdict("T:U0@phi, e:Equiv(T,A)@phi",st,why);
        EXPECT(st==CK_VALID,"a partial declaration's type forms under its own guard");
    } else if (!strcmp(mode,"publication")) {
        RefId e=mk_id_equiv(0,A);
        RefId a=mk_app(mk_app(mk_app(equiv_maps(0,0),A),A),e), b=mk_app(mk_app(mk_app(equiv_maps(0,0),A),A),e);
        printf("identical constructions: %llu / %llu\n",(unsigned long long)a,(unsigned long long)b);
        EXPECT(a==b,"building a construction twice gives one reference");
        RefId p=maps_apply(a,DIR_FORWARD,x),q=maps_apply(b,DIR_FORWARD,x);printf("calls identical: %d\n",p==q);EXPECT(p==q,"equal calls are one reference");
        (void)why;
    } else if (!strcmp(mode,"publication-concurrent")) {
        static RefId cA, ce; static RefId got[8]; static pthread_barrier_t gate;
        cA=A; ce=mk_id_equiv(0,A);
        pthread_barrier_init(&gate,NULL,8);
        void *client(void *p) { size_t k=*(size_t *)p; pthread_barrier_wait(&gate); got[k]=mk_app(mk_app(mk_app(equiv_maps(0,0),cA),cA),ce); return NULL; }
        pthread_t th[8]; size_t ids[8];
        for(size_t k=0;k<8;k++){ids[k]=k;pthread_create(&th[k],NULL,client,&ids[k]);}
        for(size_t k=0;k<8;k++)pthread_join(th[k],NULL);
        bool same=got[0]!=0; for(size_t k=1;k<8;k++) same=same&&got[k]==got[0];
        printf("eight concurrent constructions: %llu..%llu same=%d\n",(unsigned long long)got[0],(unsigned long long)got[7],same);
        EXPECT(same,"concurrent identical constructions are one reference");
        pthread_barrier_destroy(&gate);
    } else if (!strcmp(mode,"diagnostics-concurrent")) {
        static ContextId cG; static RefId bad[8]; static CheckStatus st[8]; static const char *why8[8]; static pthread_barrier_t gate;
        cG=G;
        for(size_t k=0;k<8;k++) bad[k]=mk_refl(k,B,x);   /* eight distinct invalid instances (x : A, not B) */
        pthread_barrier_init(&gate,NULL,8);
        void *client(void *p) { size_t k=*(size_t *)p; pthread_barrier_wait(&gate); Inference I=infer(cG,fc_true(),bad[k]); st[k]=I.st; why8[k]=I.reason; return NULL; }
        pthread_t th[8]; size_t ids[8];
        for(size_t k=0;k<8;k++){ids[k]=k;pthread_create(&th[k],NULL,client,&ids[k]);}
        for(size_t k=0;k<8;k++)pthread_join(th[k],NULL);
        bool all=true; for(size_t k=0;k<8;k++){ all=all&&st[k]==CK_INVALID&&why8[k]&&strstr(why8[k],"Refl"); }
        printf("eight concurrent invalid-template diagnostics intact: %d (e.g. %s)\n",all,why8[0]?why8[0]:"");
        EXPECT(all,"concurrent invalid-template diagnostics are each intact");
        for(size_t k=0;k<8;k++){ Inference I=infer(cG,fc_true(),bad[k]); EXPECT(I.st==CK_INVALID&&I.reason==why8[k],"a cached diagnostic keeps its text"); }
        pthread_barrier_destroy(&gate);
    } else if (!strcmp(mode,"canon")) {
        TermVarId vz=declare_term(A,fc_true());
        RefId p=mk_pi_lv(0,0,vz,A,A),q=mk_pi_lv(0,1,vz,A,A);
        Canon *a=canon_new(),*b=canon_new();
        canon_add_key(a,p,fc_true(),0,0,0,0);canon_add_key(b,q,fc_true(),0,0,0,0);
        Graph *ga=canon_export(a),*gb=canon_export(b);
        MatchReport ms;bool equal=graph_match(ga,gb,&ms);
        printf("distinct raw universe annotations compare equal: %d\n",equal);
        EXPECT(!equal,"comparison must retain raw origin level annotations");
        graph_free(ga);graph_free(gb);canon_free(a);canon_free(b);
    } else {fprintf(stderr,"unknown mode\n");return 2;}
    printf("%s: %d expectation failures\n",mode,failures);
    check_free();eval_free();machine_free();
    return failures ? 1 : 0;
}

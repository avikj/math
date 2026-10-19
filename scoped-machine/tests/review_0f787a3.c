#include "../src/check.h"
#include "../src/lib.h"
#include "../src/compiler.h"
#include <string.h>

static int failures;
#define EXPECT(c, label) do { if (!(c)) { ++failures; printf("FAIL: %s\n", label); } } while (0)
static void show(const char *label, Inference r) {
    printf("%s: %s (%s)\n", label, check_status_name(r.st), r.reason ? r.reason : "");
}
static RefId field(RefId t, size_t n) { Head h; open_ref(t,&h); RefId out=HF(&h, n).id; head_free(&h); return out; }
int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "scope-level";
    machine_init(); eval_init(); check_init();
    RefId U0=mk_universe(0);
    TermVarId va=declare_term(U0,fc_true()); RefId A=ref_var(va);
    TermVarId vx=declare_term(A,fc_true()); RefId x=ref_var(vx);
    DimVarId i=declare_dim();
    CtxDecl ds[]={{S_DIM,i,0},{S_TERM,va,U0},{S_TERM,vx,A}};
    ContextId G=context_make(3,ds,fc_true());
    if (!strcmp(mode,"scope-level")) {
        ScopeId good=capture_dim1(i,x,A,0,fc_true());
        ScopeId bad=capture_dim1(i,x,A,1,fc_true());
        Inference a=infer(G,fc_true(),mk_hcomp(0,A,fc_false(),good,x));
        Inference b=infer(G,fc_true(),mk_hcomp(0,A,fc_false(),bad,x));
        show("correct total tube, empty requested face",a);
        show("incorrect total tube level, empty requested face",b);
        EXPECT(a.st==CK_VALID,"correct tube is valid");
        EXPECT(b.st==CK_INVALID,"a total scope must validate its stated result level under its own guard even when this caller requests it only on false");
    } else if (!strcmp(mode,"binder-boundary")) {
        RefId ie=mk_id_equiv(0,A);
        RefId outer=field(ie,1);
        TermOpen oy=resolve_term_binder(outer,0,1);
        RefId contraction=field(oy.body,1);
        TermOpen ow=resolve_term_binder(contraction,0,1);
        DimOpen oi=resolve_dim_binder(ow.body,0,0);
        RefId snd_w=field(field(oi.body,0),3);
        EXPECT(ref_tag(snd_w)==T_SND,"located the IdEquiv template's projection from w");
        ContextId H=context_extend_term(G,oy.x,oy.type);
        ContextId Hw=context_extend_term(H,ow.x,ow.type);
        Inference good=infer(Hw,fc_true(),snd_w); show("projection at its declared local",good);
        TermVarId z=declare_term(A,fc_true());
        RefId wrongSigma=mk_sigma_lv(0,0,z,A,A);
        TermVarId q=declare_term(wrongSigma,fc_true());
        ContextId Hq=context_extend_term(H,q,wrongSigma);
        RefId bad=reindex(snd_w,map_single_term(ow.x,ref_var(q)));
        const char *why="";
        CheckStatus image=check(Hq,fc_true(),ref_var(q),ow.type,&why);
        printf("replacement at the binder's declared type: %s (%s)\n",check_status_name(image),why?why:"");
        Inference ib=infer(Hq,fc_true(),bad); show("projection after ill-typed local substitution",ib);
        EXPECT(good.st==CK_VALID && image==CK_INVALID,"valid original, invalid substitute for w");
        EXPECT(ib.st==CK_INVALID,"a retained constructor-local image is checked against its binder declaration after the child escapes the binder");
    } else if (!strcmp(mode,"machine-restart")) {
        const char *why="";
        EXPECT(check_signature(&why)==CK_VALID,"first empty environment admitted");
        check_free(); eval_free(); machine_free();
        machine_init(); eval_init(); check_init();
        SymbolId s=define_global("fresh",varset_make(NULL,0),dimset_make(NULL,0),mk_universe(0));
        printf("fresh machine accepts first declaration: %d\n",s!=0);
        EXPECT(s!=0,"machine_init starts a new open environment after machine_free");
    } else if (!strcmp(mode,"scope-locals")) {
        RefId U1=mk_universe(1);
        TermVarId z=declare_term(U0,fc_true());
        TermVarId unavailable=declare_term(U0,fc_false());
        RefId pi=mk_pi_lv(1,0,z,U0,ref_var(z));
        TermVarId capvar=declare_term(pi,fc_true()); RefId cap=ref_var(capvar);
        ContextId H=context_extend_term(G,capvar,pi);
        ScopeId D=capture_dim1(i,U0,U1,2,fc_true());
        ScopeId tube=capture_dim1(i,cap,pi,1,fc_false());
        CaptureDecl gooddecl[]={{S_DIM,i,0,LEVEL_NONE,fc_true()},{S_TERM,z,U0,1,fc_true()}};
        CaptureDecl baddecl[]={{S_DIM,i,0,LEVEL_NONE,fc_true()},{S_TERM,unavailable,U0,1,fc_false()}};
        ScopeId good=capture_scope(2,gooddecl,(Val){VS_REF,ref_var(z)},U0,1,fc_true());
        ScopeId bad=capture_scope(2,baddecl,(Val){VS_REF,ref_var(unavailable)},U0,1,fc_true());
        gooddecl[1].level=LEVEL_NONE;
        ScopeId missing=capture_scope(2,gooddecl,(Val){VS_REF,ref_var(z)},U0,1,fc_true());
        ScopeId candidates[]={good,bad,missing};
        for(size_t k=0;k<3;k++) {
            TVal args[]={{PS_LEVEL,1},{PS_LEVEL,0},{PS_SCOPE,D},{PS_SCOPE,candidates[k]},{PS_FACE,fc_false()},{PS_SCOPE,tube},{PS_REF,cap}};
            RefId term=template_call(TD_PICOMP,7,args).id;
            Inference r=infer(H,fc_true(),term);
            show(k==0?"correct PiComp codomain":k==1?"PiComp codomain uses a false-only local at true":"PiComp codomain local omits required level",r);
            EXPECT(r.st==(k==0?CK_VALID:CK_INVALID),"validate the supplied local telescope and body before signature comparison");
        }
    } else if (!strcmp(mode,"call-boundary")) {
        RefId U1=mk_universe(1);
        ScopeId good=capture_dim1(i,A,U0,1,fc_true());
        ScopeId bad_type=capture_dim1(i,A,U1,2,fc_true());
        ScopeId bad_guard=capture_dim1(i,A,U0,1,fc_false());
        RefId a=mk_line_equiv(0,good), b=mk_line_equiv(0,bad_type), c=mk_line_equiv(0,bad_guard);
        Inference ia=infer(G,fc_true(),a), ib=infer(G,fc_true(),b), ic=infer(G,fc_true(),c);
        printf("LineEquiv correct==wrong annotation: %d; correct==unavailable: %d\n",a==b,a==c);
        show("LineEquiv correct family",ia); show("LineEquiv false result annotation",ib); show("LineEquiv unavailable family",ic);
        EXPECT(ia.st==CK_VALID,"correct LineEquiv family passes");
        EXPECT(a!=b && a!=c,"typed caller boundary survives a root expression that calls another template");
        EXPECT(ib.st==CK_INVALID,"LineEquiv validates the original family annotation");
        EXPECT(ic.st==CK_INVALID,"LineEquiv validates the original family's availability");
    } else if (!strcmp(mode,"missing-level")) {
        TermVarId z=declare_term(A,fc_true());
        RefId pi=mk_pi(z,A,A), cap=mk_lam(z,A,ref_var(z));
        RefId t=mk_comp(i,pi,fc_false(),mk_system(0,NULL,NULL),cap);
        const char *why=""; WhnfStatus s; EvalResult *r=observe_checked(G,t,&s,&why);
        printf("unannotated checked comp: status=%d result=%d reason=%s\n",s,r!=NULL,why?why:"");
        EXPECT(s==W_INVALID && !r,"required levels are rejected when absent");
    } else { printf("unknown mode: %s\n",mode); failures++; }
    printf("%s: %d expectation failures\n",mode,failures);
    check_free(); eval_free(); machine_free();
    return failures?1:0;
}

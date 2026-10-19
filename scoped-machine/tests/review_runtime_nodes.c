/* §96 integration witness. Every constructor below emits an ordinary core
 * term; the resulting node function is closed and its tail is a runtime
 * argument. No DiagramId, TransformId, global axiom, or native rule is used.
 * The worker should register these recipes as fixed templates, not run this
 * test's host emitters on every object-language invocation. */
#include "../src/compiler.h"
#include <assert.h>
#include <stdlib.h>

typedef uint64_t Level;
typedef struct { RefId type, value; } Typed;
static Level max2(Level a, Level b) { return a>b?a:b; }
static RefId app2(RefId f,RefId x,RefId y) { return mk_app(mk_app(f,x),y); }
static RefId app4(RefId f,RefId a,RefId b,RefId c,RefId d) {
    return app2(app2(f,a,b),c,d);
}
static TermVarId var(RefId A) { return declare_term(A,fc_true()); }
static RefId pair(Level l,RefId S,RefId x,RefId y) {
    return mk_pair_at_lv(l,S,x,y);
}
static RefId tail(RefId S,RefId x) { return apply_term_binder(S,0,1,x); }
static RefId mf(RefId E) { return mk_fst(E); }
static RefId mg(RefId E) { return mk_fst(mk_snd(E)); }
static RefId mh(RefId E) { return mk_fst(mk_snd(mk_snd(E))); }
static RefId mk(RefId E) { return mk_snd(mk_snd(mk_snd(E))); }
static RefId dc(RefId Q) { return mk_fst(Q); }
static RefId dr(RefId Q,RefId y) { return mk_app(mk_fst(mk_snd(Q)),y); }
static RefId dm(RefId Q,RefId y) { return mk_app(mk_snd(mk_snd(Q)),y); }

static RefId w_maps_type(Level a,Level b,RefId A,RefId B) {
    Level m=max2(a,b);
    RefId F=mk_fun(a,b,A,B),G=mk_fun(b,a,B,A);
    TermVarId f=var(F),g=var(G),x=var(A),y=var(B);
    RefId H=mk_pi_lv(a,a,x,A,mk_path_const(a,A,
        mk_app(ref_var(g),mk_app(ref_var(f),ref_var(x))),ref_var(x)));
    RefId K=mk_pi_lv(b,b,y,B,mk_path_const(b,B,
        mk_app(ref_var(f),mk_app(ref_var(g),ref_var(y))),ref_var(y)));
    TermVarId h=var(H);
    return mk_sigma_lv(m,m,f,F,mk_sigma_lv(m,m,g,G,mk_sigma_lv(a,b,h,H,K)));
}
static RefId maps_pack(Level a,Level b,RefId A,RefId B,
                       RefId f,RefId g,RefId h,RefId k) {
    Level m=max2(a,b); RefId M=w_maps_type(a,b,A,B),M1=tail(M,f),M2=tail(M1,g);
    return pair(m,M,f,pair(m,M1,g,pair(m,M2,h,k)));
}
static RefId maps_id(Level a,RefId A) {
    TermVarId x=var(A); RefId id=mk_id_fun(a,A);
    RefId h=mk_lam_lv(a,x,A,mk_refl(a,A,ref_var(x)));
    return maps_pack(a,a,A,A,id,id,h,h);
}
static RefId ap(Level a,RefId A,RefId x,RefId y,RefId f,RefId p) {
    DimVarId i=declare_dim();
    return mk_plam(i,mk_app(f,mk_papp_const(a,A,x,y,p,iv_var(i))));
}
/* E:A<->B, F:B<->C. Both homotopies are retained as ordinary fields. */
static RefId maps_comp(Level a,Level b,Level c,RefId A,RefId B,RefId C,
                       RefId E,RefId F) {
    RefId f=mf(E),g=mg(E),h=mh(E),k=mk(E);
    RefId u=mf(F),v=mg(F),H=mh(F),K=mk(F);
    TermVarId x=var(A),z=var(C); RefId xv=ref_var(x),zv=ref_var(z);
    RefId fx=mk_app(f,xv),vz=mk_app(v,zv);
    RefId forward=mk_lam_lv(a,x,A,mk_app(u,fx));
    RefId reverse=mk_lam_lv(c,z,C,mk_app(g,vz));
    RefId vufx=mk_app(v,mk_app(u,fx)),gvufx=mk_app(g,vufx),gfx=mk_app(g,fx);
    RefId h0=ap(b,B,vufx,fx,g,mk_app(H,fx));
    RefId hh=mk_lam_lv(a,x,A,mk_path_concat(a,A,gvufx,gfx,xv,h0,mk_app(h,xv)));
    RefId fgvz=mk_app(f,mk_app(g,vz)),ufgvz=mk_app(u,fgvz),uvz=mk_app(u,vz);
    RefId k0=ap(b,B,fgvz,vz,u,mk_app(k,vz));
    RefId kk=mk_lam_lv(c,z,C,mk_path_concat(c,C,ufgvz,uvz,zv,k0,mk_app(K,zv)));
    return maps_pack(a,c,A,C,forward,reverse,hh,kk);
}
static RefId singleton(Level a,Level r,RefId A,RefId t,
                       TermVarId x,TermVarId e,RefId D) {
    Level s=max2(a,r); RefId Ex=mk_path_const(a,A,t,ref_var(x));
    RefId S=mk_sigma_lv(a,s,x,A,mk_sigma_lv(a,r,e,Ex,D));
    ScopeId DS=capture_term2(x,A,a,e,Ex,a,D,mk_universe(r),r+1,fc_true());
    RefId refl=mk_refl(a,A,t),Z;
    /* Substitute simultaneously, so images are not rewritten by the map. */
    MapBuilder images;mapb_init(&images);mapb_term(&images,x,t);mapb_term(&images,e,refl);
    Z=reindex(D,mapb_finish(&images));
    TermVarId w=var(S),z=var(Z); RefId wv=ref_var(w),zv=ref_var(z);
    RefId wx=mk_fst(wv),we=mk_fst(mk_snd(wv)),wz=mk_snd(mk_snd(wv));
    RefId down=mk_lam_lv(s,w,S,mk_down(r,a,A,t,DS,wx,we,wz));
    RefId up=mk_lam_lv(r,z,Z,pair(s,S,t,pair(s,tail(S,t),refl,zv)));
    DimVarId i=declare_dim(),j=declare_dim(),q=declare_dim();
    RefId xi=mk_papp_const(a,A,t,wx,we,iv_var(i));
    RefId ei=mk_plam(j,mk_papp_const(a,A,t,wx,we,iv_meet(iv_var(i),iv_var(j))));
    RefId xq=mk_papp_const(a,A,t,wx,we,iv_negate(iv_var(q)));
    RefId eq=mk_plam(j,mk_papp_const(a,A,t,wx,we,iv_meet(iv_negate(iv_var(q)),iv_var(j))));
    MapBuilder qi;mapb_init(&qi);mapb_term(&qi,x,xq);mapb_term(&qi,e,eq);
    RefId Dq=reindex(D,mapb_finish(&qi)),empty=mk_system(0,NULL,NULL);
    RefId zi=mk_fill_at(r,q,Dq,fc_false(),empty,wz,iv_negate(iv_var(i)));
    RefId h=mk_lam_lv(s,w,S,mk_plam(i,pair(s,S,xi,pair(s,tail(S,xi),ei,zi))));
    RefId k=mk_lam_lv(r,z,Z,mk_plam(i,
        mk_fill_at(r,q,Z,fc_false(),empty,zv,iv_negate(iv_var(i)))));
    return maps_pack(s,r,S,Z,down,up,h,k);
}
static RefId w_diagram_type(Level b,Level r,RefId B) {
    Level rl=max2(b,r+1),ml=max2(b,r);
    TermVarId c=var(B),y=var(B);
    RefId RT=mk_pi_lv(b,r+1,y,B,mk_universe(r)); TermVarId R=var(RT);
    RefId M=mk_pi_lv(b,ml,y,B,w_maps_type(r,b,mk_app(ref_var(R),ref_var(y)),
        mk_path_const(b,B,ref_var(c),ref_var(y))));
    return mk_sigma_lv(b,rl,c,B,mk_sigma_lv(rl,ml,R,RT,M));
}
static RefId diagram_pack(Level b,Level r,RefId B,RefId c,RefId R,RefId M) {
    Level dl=max2(b,r+1);RefId D=w_diagram_type(b,r,B);
    return pair(dl,D,c,pair(dl,tail(D,c),R,M));
}
static RefId zero(Level b,RefId B,RefId c) {
    TermVarId y=var(B); RefId P=mk_path_const(b,B,c,ref_var(y));
    return diagram_pack(b,b,B,c,mk_lam_lv(b,y,B,P),mk_lam_lv(b,y,B,maps_id(b,P)));
}
/* The emitter creates one closed term. Applying that term does all of the
 * diagram construction inside the object language, including its proofs. */
static Typed node_program(Level a,Level b,Level r) {
    Level s=max2(a,r),dl=max2(b,r+1),outl=max2(b,s+1);
    RefId UA=mk_universe(a),UB=mk_universe(b);
    TermVarId vB=var(UB),vA=var(UA);RefId B=ref_var(vB),A=ref_var(vA);
    TermVarId vt=var(A);RefId t=ref_var(vt);TermVarId x=var(A);
    RefId Ex=mk_path_const(a,A,t,ref_var(x));TermVarId e=var(Ex);
    RefId DT=w_diagram_type(b,r,B);
    RefId QT=mk_pi_lv(a,max2(a,dl),x,A,mk_pi_lv(a,dl,e,Ex,DT));
    Level ql=max2(a,dl);TermVarId q=var(QT);RefId Q=ref_var(q);
    RefId Q0=app2(Q,t,mk_refl(a,A,t)),c=dc(Q0);TermVarId y=var(B);RefId yv=ref_var(y);
    RefId D=dr(app2(Q,ref_var(x),ref_var(e)),yv);
    RefId S=mk_sigma_lv(a,s,x,A,mk_sigma_lv(a,r,e,Ex,D));
    RefId Z=dr(Q0,yv),P=mk_path_const(b,B,c,yv);
    RefId E=singleton(a,r,A,t,x,e,D),F=dm(Q0,yv);
    RefId R=mk_lam_lv(b,y,B,S);
    RefId M=mk_lam_lv(b,y,B,maps_comp(s,r,b,S,Z,P,E,F));
    RefId body=diagram_pack(b,s,B,c,R,M),type=w_diagram_type(b,s,B);
    body=mk_lam_lv(ql,q,QT,body);type=mk_pi_lv(ql,outl,q,QT,type);outl=max2(ql,outl);
    body=mk_lam_lv(a,vt,A,body);type=mk_pi_lv(a,outl,vt,A,type);outl=max2(a,outl);
    body=mk_lam_lv(a+1,vA,UA,body);type=mk_pi_lv(a+1,outl,vA,UA,type);outl=max2(a+1,outl);
    body=mk_lam_lv(b+1,vB,UB,body);type=mk_pi_lv(b+1,outl,vB,UB,type);
    return (Typed){type,body};
}
static void valid(ContextId G,RefId t,RefId T,const char *label) {
    const char *why="";CheckStatus st=check(G,fc_true(),t,T,&why);
    if(st!=CK_VALID){fprintf(stderr,"FAIL %s: %s: %s\n",label,check_status_name(st),why);abort();}
    printf("PASS %s\n",label);fflush(stdout);
}
static void equal(ContextId G,RefId a,RefId b,RefId T,const char *label) {
    ConvStatus st=convert_term(G,fc_true(),a,b,T);
    if(st!=CV_EQUAL){fprintf(stderr,"FAIL %s: %s\n",label,conv_status_name(st));abort();}
    printf("PASS %s\n",label);fflush(stdout);
}
int main(int argc,char **argv) {
    int workers=argc>1?atoi(argv[1]):0;
    machine_init();check_init();eval_set_workers(workers);
    check_set_budget(0);assert(eval_workers()==(size_t)workers);
    printf("actual_workers=%zu\n",eval_workers());fflush(stdout);
    ContextId empty=context_make(0,NULL,fc_true());
    if(argc>2 && !strcmp(argv[2],"levels")) {
        const Level levels[][3]={{1,0,0},{0,1,0},{0,0,1}};
        for(size_t j=0;j<3;++j) {
            Typed n=node_program(levels[j][0],levels[j][1],levels[j][2]);
            char label[100];snprintf(label,sizeof label,"closed node with exact levels a=%llu b=%llu r=%llu",
                (unsigned long long)levels[j][0],(unsigned long long)levels[j][1],(unsigned long long)levels[j][2]);
            valid(empty,n.value,n.type,label);
        }
        for(size_t j=0;j<3;++j) {
            Typed n=node_program(levels[j][0],levels[j][1],levels[j][2]);
            valid(empty,dg_node(levels[j][0],levels[j][1],levels[j][2]),n.type,"production node at the witnessed type");
        }
        check_free();machine_free();return 0;
    }
    Typed N=node_program(0,0,0);
    valid(empty,N.value,N.type,"closed nonempty node, arbitrary dependent runtime tail, all four fields");
    valid(empty,dg_node(0,0,0),N.type,"production node at the witnessed type");
    if(argc>2 && !strcmp(argv[2],"generic")) {
        check_free();machine_free();return 0;
    }
    RefId U=mk_universe(0);TermVarId vA=var(U);RefId A=ref_var(vA);
    TermVarId vt=var(A),vy=var(A);RefId t=ref_var(vt),y=ref_var(vy),P=mk_path_const(0,A,t,y);
    TermVarId vp=var(P);RefId p=ref_var(vp);
    CtxDecl ds[]={{S_TERM,vA},{S_TERM,vt},{S_TERM,vy},{S_TERM,vp}};
    ContextId G=context_make(4,ds,fc_true());
    TermVarId x=var(A);RefId Ex=mk_path_const(0,A,t,ref_var(x));TermVarId e=var(Ex);
    RefId QT=mk_pi_lv(0,1,x,A,mk_pi_lv(0,1,e,Ex,w_diagram_type(0,0,A)));
    RefId Q=mk_lam_lv(0,x,A,mk_lam_lv(0,e,Ex,zero(0,A,ref_var(x))));
    RefId computedQ=mk_app(mk_id_fun(1,QT),Q);
    RefId D=app4(dg_node(0,0,0),A,A,t,computedQ),DT=w_diagram_type(0,0,A);
    valid(G,D,DT,"runtime nonempty node with tail centre depending on bound x");
    equal(G,dc(D),t,A,"computed node centre");
    RefId S=dr(D,y),E=dm(D,y),f=mf(E),g=mg(E),h=mh(E),k=mk(E);
    valid(G,E,w_maps_type(0,0,S,P),"computed node collapse, expansion and both inverse proofs");
    RefId w=mk_app(g,p),fw=mk_app(f,w),gw=mk_app(g,fw);
    valid(G,w,S,"expansion of an arbitrary output path");
    valid(G,fw,P,"collapse of the expanded realization");
    RefId kp=mk_app(k,p),hw=mk_app(h,w);
    valid(G,kp,mk_path_const(0,P,fw,p),"runtime collapse-after-expansion proof");
    valid(G,hw,mk_path_const(0,S,gw,w),"runtime expansion-after-collapse proof");
    equal(G,mk_papp_const(0,P,fw,p,kp,iv_zero()),fw,P,"first proof source endpoint");
    equal(G,mk_papp_const(0,P,fw,p,kp,iv_one()),p,P,"first proof target endpoint");
    equal(G,mk_papp_const(0,S,gw,w,hw,iv_zero()),gw,S,"second proof source endpoint");
    equal(G,mk_papp_const(0,S,gw,w,hw,iv_one()),w,S,"second proof target endpoint");
    check_free();machine_free();return 0;
}

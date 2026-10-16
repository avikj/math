#include "assoc.h"
#include "../src/work.h"
#include <assert.h>

static void start(void) { machine_init(); eval_init(); check_init(); compiler_init(); work_init(); }
static void stop(void) { work_free(); compiler_free(); check_free(); eval_free(); machine_free(); }
static RefId observe(RefId t, FaceId f) {
    WhnfStatus st; EvalResult *r = whnf(t, f, &st);
    assert(st == W_OK && r); return r->ref;
}
typedef struct { RefId A, a; TermVarId x; ContextId G; } Base;
static Base base(void) {
    RefId U = mk_universe(0); TermVarId A = declare_term(U, fc_true());
    TermVarId a = declare_term(ref_var(A), fc_true());
    Base b = { ref_var(A), ref_var(a), declare_term(ref_var(A), fc_true()), 0 };
    CtxDecl ds[] = { {S_TERM, A, U}, {S_TERM, a, b.A} };
    b.G = context_make(2, ds, fc_true()); return b;
}
static void origin_case(void) {
    Base b = base(); RefId fn = mk_lam_lv(0, b.x, b.A, ref_var(b.x));
    TermVarId z = declare_term(b.A, fc_true());
    RefId abstract = mk_app(fn, ref_var(z));
    RefId via_map = reindex1(abstract, z, b.a), direct = mk_app(fn, b.a);
    Head h, g; open_ref(via_map, &h); open_ref(direct, &g);
    bool same = h.tag == g.tag && h.n == g.n;
    for (size_t k = 0; same && k < h.n; k++) same = h.f[k].id == g.f[k].id;
    head_free(&h); head_free(&g); assert(same);
    assert(observe(via_map, fc_true()) == b.a); EvalEvents e = eval_events();
    assert(observe(via_map, fc_true()) == b.a); EvalEvents hit = eval_events();
    assert(hit.launch == e.launch);
    assert(observe(direct, fc_true()) == b.a); EvalEvents end = eval_events();
    assert(convert_term(b.G, fc_true(), via_map, direct, b.A) == CV_EQUAL);
    printf("origin same_opened_head=%d same_ref=%d repeat_launches=%zu direct_launches=%zu direct_frames=%zu\n", same, via_map == direct, hit.launch-e.launch, end.launch-hit.launch, end.eval_step-hit.eval_step);
}
static void alpha_case(void) {
    Base b = base(); TermVarId y = declare_term(b.A, fc_true());
    RefId f = mk_lam_lv(0, b.x, b.A, ref_var(b.x));
    RefId g = mk_lam_lv(0, y, b.A, ref_var(y));
    RefId appf = mk_app(f, b.a), appg = mk_app(g, b.a);
    assert(observe(appf, fc_true()) == b.a); EvalEvents e = eval_events();
    assert(observe(appg, fc_true()) == b.a); EvalEvents end = eval_events();
    assert(convert_term(b.G, fc_true(), f, g, mk_fun(0,0,b.A,b.A)) == CV_EQUAL);
    printf("alpha same_ref=%d second_launches=%zu second_frames=%zu\n", f == g, end.launch-e.launch, end.eval_step-e.eval_step);
}
static void face_case(void) {
    Base b = base(); DimVarId i = declare_dim();
    RefId ptype = mk_path_const(0, b.A, b.a, b.a);
    TermVarId p = declare_term(ptype, fc_true());
    RefId pi = mk_papp_const(0, b.A, b.a, b.a, ref_var(p), iv_var(i));
    RefId k = mk_lam_lv(0,b.x,b.A,b.a), t = mk_app(k,pi);
    assert(observe(t,fc_true()) == b.a); EvalEvents e = eval_events();
    assert(observe(t,fc_lit(i,0)) == b.a); EvalEvents end = eval_events();
    printf("face term_mentions_i=%d argument_ever_evaluated=%d stronger_launches=%zu stronger_frames=%zu\n",dimset_contains(ref_support(t),i),eval_entry_lookup(pi,fc_true())!=0,end.launch-e.launch,end.eval_step-e.eval_step);
}
static void specialize_case(void) {
    Base b = base(); TermVarId z = declare_term(b.A,fc_true());
    RefId f = mk_lam_lv(0,b.x,b.A,ref_var(b.x));
    RefId t = mk_app(f,ref_var(z));
    assert(observe(t,fc_true()) == ref_var(z));
    assert(observe(b.a,fc_true()) == b.a); EvalEvents e = eval_events();
    RefId instance = reindex1(t,z,b.a);
    assert(observe(instance,fc_true()) == b.a); EvalEvents end = eval_events();
    printf("specialize generic_result_ready=1 image_ready=1 instance_launches=%zu instance_frames=%zu\n",end.launch-e.launch,end.eval_step-e.eval_step);
}
static void environment_case(void) {
    RefId U0 = mk_universe(0), U1 = mk_universe(1);
    TermVarId x = declare_term(U1,fc_true());
    RefId t = mk_app(mk_lam_lv(2,x,U1,ref_var(x)),U0);
    assert(observe(t,fc_true()) == U0); EvalEvents e = eval_events();
    SymbolId s = define_global("unrelated",varset_make(NULL,0),dimset_make(NULL,0),U0);
    assert(s); assert(observe(t,fc_true()) == U0); EvalEvents end = eval_events();
    printf("environment closed_term_globals=0 unrelated_registration=%llu repeat_launches=%zu repeat_frames=%zu\n",(unsigned long long)s,end.launch-e.launch,end.eval_step-e.eval_step);
}
static void identity_name_case(void) {
    const char *why = ""; Assoc a; assoc_build(&a,&why); assert(a.T);
    IdentityDecl d = { 987654321, a.G, fc_true(), a.X, 0, a.L, a.R, a.alpha };
    TransformId t2 = compile_identity(&d,&why); assert(t2);
    const CompiledTransform *x=transform_get(a.T), *y=transform_get(t2);
    bool bodies = x->forward_body==y->forward_body && x->reverse_body==y->reverse_body;
    assert(bodies);
    MapId s=assoc_sigma(&a,a.rhs); RefId arg=assoc_left_arg(&a,s);
    RefId c1=mk_transform_call(a.T,DIR_FORWARD,s,arg), c2=mk_transform_call(t2,DIR_FORWARD,s,arg);
    RefId r1=observe(c1,fc_true()); EvalEvents e=eval_events(); EvalNetEvents n=eval_net_events();
    RefId r2=observe(c2,fc_true()); EvalEvents end=eval_events(); EvalNetEvents ne=eval_net_events();
    assert(r1==r2);
    printf("identity_name same_bodies=%d same_record=%d same_call=%d second_apply=%zu second_launches=%zu second_frames=%zu\n",bodies,a.T==t2,c1==c2,ne.apply-n.apply,end.launch-e.launch,end.eval_step-e.eval_step);
}
static void work_case(void) {
    FormulaId f=formula_one();
    for(uint64_t i=1;i<=12;i++) f=formula_and(f,formula_atom(atom_named(i)));
    ModelId m=model_make(1,(KindWeights){.named=1},set_empty());
    OpId x=op_reduce(f,m);
    while(op_step(x,100)==OP_RUNNING){} assert(op_status(x)==OP_COMPLETE);
    uint64_t r1=op_result(x), n1=op_frames(x); op_release(x);
    OpId y=op_reduce(f,m);
    while(op_step(y,100)==OP_RUNNING){} assert(op_status(y)==OP_COMPLETE);
    uint64_t r2=op_result(y), n2=op_frames(y); op_release(y);
    printf("work_repeat same_result_record=%d first_frames=%llu second_frames=%llu\n",r1==r2,(unsigned long long)n1,(unsigned long long)n2);
}
int main(int argc,char **argv) {
    assert(argc==2); start();
    if(!strcmp(argv[1],"origin")) origin_case();
    else if(!strcmp(argv[1],"alpha")) alpha_case();
    else if(!strcmp(argv[1],"face")) face_case();
    else if(!strcmp(argv[1],"specialize")) specialize_case();
    else if(!strcmp(argv[1],"environment")) environment_case();
    else if(!strcmp(argv[1],"identity-name")) identity_name_case();
    else if(!strcmp(argv[1],"work")) work_case();
    else assert(0);
    stop(); return 0;
}

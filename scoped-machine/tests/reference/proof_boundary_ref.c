#include "proof_boundary.h"

/* Conservative finite stored-syntax traversal. Unlike the substitution
 * traversal, it includes fields behind views, inactive branches, binder
 * domains, scope declarations and result types. It may retain dependencies
 * which evaluation later removes. That yields PENDING, never a false proof.
 *
 * The current fixed template language has no literal reference/global opcode:
 * references come from its retained, declaration-closed environment. If that
 * language is extended, this argument must be revisited before accepting the
 * new opcode. No origin or scope is opened during this walk.
 */
typedef struct { WordMap seen; Words symbols; } Scan;
static bool enter(Scan *s,uint64_t kind,uint64_t id) {
    uint64_t key[]={kind,id}, found;
    if(wordmap_get(&s->seen,key,2,&found)) return false;
    wordmap_put(&s->seen,key,2,1); return true;
}
static void add(Words *w,uint64_t x) {
    for(size_t k=0;k<w->n;k++) if(w->w[k]==x) return;
    words_push(w,x);
}
static void scan_ref(Scan *s,RefId t);
static void scan_context(Scan *s,ContextId G) {
    for(size_t k=0;k<context_size(G);k++) {
        CtxDecl d=context_decl(G,k);
        if(d.sort==S_TERM) scan_ref(s,d.type);
    }
}
static void scan_scope(Scan *s,ScopeId S) {
    if(!enter(s,2,S)) return;
    for(size_t k=0;k<scope_arity(S);k++) {
        LocalDecl d=scope_local(S,k);
        if(d.type) scan_ref(s,d.type);
    }
    Val b=scope_body(S);
    if(b.sort==VS_REF) scan_ref(s,b.id);
    if(scope_type(S)) scan_ref(s,scope_type(S));
    /* Interval/face syntax has no global-reference constructor. */
}
static void scan_ref(Scan *s,RefId t) {
    if(!t || !enter(s,1,t)) return;
    if(ref_is_var(t)) {
        TermVarId x=ref_var_id(t);
        if(!is_bound_id(x)) scan_ref(s,term_var_type(x));
        return;
    }
    if(ref_is_tview(t)) {
        TEnvId E=tenv_of(t);
        for(size_t k=0;k<tenv_size(E);k++) {
            uint64_t slot; TVal v; tenv_entry(E,k,&slot,&v);
            if(v.sort==PS_REF) scan_ref(s,v.id);
            else if(v.sort==PS_SCOPE) scan_scope(s,v.id);
        }
        return;
    }
    OriginId o=ref_origin(t); MapId m=ref_map(t);
    Tag tag=origin_tag(o);
    if(tag==T_GLOBAL) add(&s->symbols,origin_payload(o));
    if(tag==T_TCALL) {
        const CompiledTransform *tr=transform_get(origin_payload(o)/2);
        require(tr,"proof boundary: invalid transform id");
        scan_context(s,tr->parameters);
        scan_ref(s,tr->domain); scan_ref(s,tr->codomain);
        scan_ref(s,tr->forward_body); scan_ref(s,tr->reverse_body);
    }
    for(size_t k=0;k<origin_nfields(o);k++) {
        Field f=origin_field(o,(FieldIndex)k);
        if(f.kind==F_REF) scan_ref(s,f.id);
    }
    for(size_t k=0;k<origin_nbinders(o);k++) {
        Binder b=origin_binder(o,(BinderSlot)k);
        if(b.sort==S_TERM) scan_ref(s,term_var_type(b.formal));
    }
    for(size_t k=0;k<map_n_terms(m);k++) {
        TermVarId x; RefId image; map_term_entry(m,k,&x,&image);
        scan_ref(s,image);
    }
    size_t n; const uint64_t *xs=varset_get(origin_ft(o),&n);
    for(size_t k=0;k<n;k++) scan_ref(s,term_var_type(xs[k]));
}
static void scan_init(Scan *s) { memset(s,0,sizeof *s); wordmap_init(&s->seen); words_init(&s->symbols); }
static void scan_free(Scan *s) { wordmap_free(&s->seen); words_free(&s->symbols); }

typedef struct { Words deps; bool seen; size_t index,low; bool onstack; } Vertex;
typedef struct { Vertex *v; size_t n,next; Words stack; ProofBoundary *out; } Graph;
static void discover(Graph *g,SymbolId s) {
    require(s && s<=g->n,"proof boundary: unknown global");
    Vertex *v=&g->v[s]; if(v->seen) return; v->seen=true;
    Scan walk; scan_init(&walk);
    scan_ref(&walk,global_type(s));
    RefId body=global_body(s);
    if(body) scan_ref(&walk,body); else add(&g->out->assumptions,s);
    size_t n; const uint64_t *params=varset_get(global_params(s),&n);
    for(size_t k=0;k<n;k++) scan_ref(&walk,term_var_type(params[k]));
    v->deps=walk.symbols; words_init(&walk.symbols); scan_free(&walk);
    for(size_t k=0;k<v->deps.n;k++) discover(g,v->deps.w[k]);
}
static void component(Graph *g,SymbolId s) {
    Vertex *v=&g->v[s]; v->index=v->low=++g->next;
    words_push(&g->stack,s); v->onstack=true;
    for(size_t k=0;k<v->deps.n;k++) {
        SymbolId d=v->deps.w[k]; Vertex *w=&g->v[d];
        if(!w->index) { component(g,d); if(w->low<v->low) v->low=w->low; }
        else if(w->onstack && w->index<v->low) v->low=w->index;
    }
    if(v->low==v->index) {
        Words members; words_init(&members); SymbolId d;
        do { d=g->stack.w[--g->stack.n]; g->v[d].onstack=false; words_push(&members,d); } while(d!=s);
        bool cyclic=members.n>1;
        for(size_t k=0;k<v->deps.n;k++) if(v->deps.w[k]==s) cyclic=true;
        if(cyclic) for(size_t k=0;k<members.n;k++) add(&g->out->recursive,members.w[k]);
        words_free(&members);
    }
}
void proof_boundary_free(ProofBoundary *r) { words_free(&r->assumptions); words_free(&r->recursive); }
ProofBoundary proof_boundary(ContextId G,FaceId face,RefId e,RefId T) {
    ProofBoundary out; memset(&out,0,sizeof out);
    words_init(&out.assumptions); words_init(&out.recursive); out.reason="";
    out.context=G; out.face=face; out.evidence=e; out.type=T;
    CheckStatus st=check_admission(&out.reason);
    out.environment=global_env_version(); /* admission has frozen this snapshot */
    if(st==CK_VALID) st=check_context(G,&out.reason);
    uint64_t level;
    if(st==CK_VALID) st=check_is_type(G,face,T,&level,&out.reason);
    if(st==CK_VALID) st=check(G,face,e,T,&out.reason);
    if(st!=CK_VALID) { out.status=st==CK_INVALID?PB_INVALID:PB_UNRESOLVED; return out; }
    /* False-face validity is local to that face, never a total theorem. */
    if(face==fc_false()) { out.status=PB_CORE; return out; }
    Scan roots; scan_init(&roots); scan_context(&roots,G); scan_ref(&roots,T); scan_ref(&roots,e);
    Graph graph; memset(&graph,0,sizeof graph); graph.n=global_count(); graph.out=&out;
    graph.v=calloc(graph.n+1,sizeof *graph.v); require(graph.v,"out of memory"); words_init(&graph.stack);
    for(size_t k=0;k<roots.symbols.n;k++) discover(&graph,roots.symbols.w[k]);
    for(SymbolId s=1;s<=graph.n;s++) if(graph.v[s].seen && !graph.v[s].index) component(&graph,s);
    out.status=out.recursive.n?PB_PENDING:out.assumptions.n?PB_ASSUMED:PB_CORE;
    out.reason=out.recursive.n?"recursive dependencies need a logical witness":out.assumptions.n?"relative to explicit opaque assumptions":"acyclic core proof relative to the occurrence context";
    for(SymbolId s=1;s<=graph.n;s++) words_free(&graph.v[s].deps);
    free(graph.v); words_free(&graph.stack); scan_free(&roots);
    return out;
}

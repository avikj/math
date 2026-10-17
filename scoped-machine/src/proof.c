/* proof.c — the proof-use boundary (§88). See proof.h. */
#include "proof.h"
#include "scope.h"
#include "fine.h"

/* symbol sets are interned sorted lists; node results are memoized per
 * reference / scope / symbol-at-revision; verdicts per judgment */
static struct {
    Interner sets;          /* sorted symbol lists */
    WordMap ref_memo;       /* (1, ref) → set id ; (2, scope) → set id ; (3, symbol, revision) → set id of its edges */
    WordMap verdicts;       /* (ctx, face, e, E) → verdict record id */
    Interner records;       /* verdict records: [status, nassump, assump..., nrec, rec..., ndeps, (sym,rev)...] */
    pthread_mutex_t mu;
    uint64_t steps;
    bool live;
} P;

/* §R5: initialized in the serial lifecycle (compiler_init), torn down at the quiescent boundary (compiler_free); public entries require it live */
void proof_init(void) { if (P.live) return; memset(&P, 0, sizeof P); interner_init(&P.sets); wordmap_init(&P.ref_memo); wordmap_init(&P.verdicts); interner_init(&P.records); pthread_mutex_init(&P.mu, NULL); P.live = true; }
void proof_free(void) { if (!P.live) return; interner_free(&P.sets); wordmap_free(&P.ref_memo); wordmap_free(&P.verdicts); interner_free(&P.records); pthread_mutex_destroy(&P.mu); P.live = false; }
uint64_t proof_audit_steps(void) { return __atomic_load_n(&P.steps, __ATOMIC_SEQ_CST); }
static void step(void) { __atomic_add_fetch(&P.steps, 1, __ATOMIC_RELAXED); fine_bump(FC_AUDIT_STEPS); }
const char *proof_use_name(ProofUseStatus s) { static const char *n[] = { "CORE", "ASSUMED", "PENDING", "INVALID", "UNRESOLVED" }; return n[s]; }

/* the interner and the word map are internally synchronized (§94): no outer P.mu section around them */
static uint64_t set_intern(uint64_t *w, size_t n) { n = sort_unique_u64(w, n); return interner_intern(&P.sets, w, n, NULL); }
static const uint64_t *set_get(uint64_t id, size_t *n) { return interner_get(&P.sets, id, n); }
static bool memo_get(uint64_t kind, uint64_t a, uint64_t b, uint64_t *out) { uint64_t k[3] = { kind, a, b }; bool h = wordmap_get(&P.ref_memo, k, 3, out); return h; }
static void memo_put(uint64_t kind, uint64_t a, uint64_t b, uint64_t v) { uint64_t k[3] = { kind, a, b }; wordmap_put(&P.ref_memo, k, 3, v); }

/* ---- the explicit owned traversal stack (§88.3) ----
 * A frame holds one node, its enumerated children (kind, id pairs) and the
 * symbols it contributes directly; children are processed one per step,
 * taking memoized results where present; a finished node's set is the
 * union of its own symbols and its children's sets. The traversal visits
 * stored syntax only: no evaluation, no scope opening, no global unfolding. */
typedef struct { uint64_t kind, id; Words children; Words syms; size_t next; bool expanded; } TFrame;

static void push_child(Words *c, uint64_t kind, uint64_t id) { if (id) { words_push(c, kind); words_push(c, id); } }
static void expand(TFrame *f) {
    f->expanded = true;
    if (f->kind == N_CTX) { ContextId G = f->id; for (size_t k = 0; k < context_size(G); k++) { CtxDecl d = context_decl(G, k); if (d.sort == S_TERM) push_child(&f->children, N_REF, d.type); } return; }
    if (f->kind == N_SCOPE) {
        ScopeId S = f->id;
        for (size_t k = 0; k < scope_arity(S); k++) { LocalDecl d = scope_local(S, k); if (d.type) push_child(&f->children, N_REF, d.type); }
        Val b = scope_body(S); if (b.sort == VS_REF) push_child(&f->children, N_REF, b.id);
        push_child(&f->children, N_REF, scope_type(S));
        return;   /* intervals and faces carry no reference constructor */
    }
    RefId t = f->id;
    if (ref_is_var(t)) { TermVarId x = ref_var_id(t); if (!is_bound_id(x)) push_child(&f->children, N_REF, term_var_type(x)); return; }
    if (ref_is_tview(t)) {
        TEnvId E = tenv_of(t);
        for (size_t k = 0; k < tenv_size(E); k++) { uint64_t slot; TVal v; tenv_entry(E, k, &slot, &v); if (v.sort == PS_REF) push_child(&f->children, N_REF, v.id); else if (v.sort == PS_SCOPE) push_child(&f->children, N_SCOPE, v.id); }
        return;   /* the fixed template interpreter has no literal-reference opcode: every reference comes from this environment */
    }
    OriginId o = ref_origin(t); MapId m = ref_map(t); Tag tag = origin_tag(o);
    if (tag == T_GLOBAL) words_push(&f->syms, origin_payload(o));
    if (tag == T_TCALL) {
        const CompiledTransform *tr = transform_get(origin_payload(o) / 2);
        require(tr, "proof audit: call of an unknown transform");
        push_child(&f->children, N_CTX, tr->parameters);
        push_child(&f->children, N_REF, tr->domain); push_child(&f->children, N_REF, tr->codomain);
        push_child(&f->children, N_REF, tr->forward_body); push_child(&f->children, N_REF, tr->reverse_body);
    }
    for (size_t k = 0; k < origin_nfields(o); k++) { Field fl = origin_field(o, (FieldIndex)k); if (fl.kind == F_REF) push_child(&f->children, N_REF, fl.id); }   /* every stored field, inactive branches included */
    for (size_t k = 0; k < origin_nbinders(o); k++) { Binder b = origin_binder(o, (BinderSlot)k); if (b.sort == S_TERM) push_child(&f->children, N_REF, term_var_type(b.formal)); }
    for (size_t k = 0; k < map_n_terms(m); k++) { TermVarId x; RefId im; map_term_entry(m, k, &x, &im); push_child(&f->children, N_REF, im); }
    size_t n; const uint64_t *xs = varset_get(origin_ft(o), &n);
    for (size_t k = 0; k < n; k++) push_child(&f->children, N_REF, term_var_type(xs[k]));
}
/* ---- §94: the stored-syntax items of a node, one per call (for the framed audit in work.c) ----
 * The same enumeration `expand` performs, addressed by (source, index):
 * `proof_node_item` is O(1) and returns false when source `src` has no item
 * `k` (the caller advances to the next source; PN_SOURCES sources). An item
 * is a child node (PN_CHILD), a directly contributed symbol (PN_SYMBOL) or
 * nothing (PN_NONE: a stored slot without a reference), so a traversal that
 * walks (src, k) in order visits exactly what the synchronous audit visits. */
bool proof_node_item(uint64_t kind, uint64_t id, unsigned src, size_t k, PNodeItem *out) {
    out->what = PN_NONE; out->kind = N_REF; out->id = 0;
    if (kind == N_CTX) {
        if (src != 0 || k >= context_size(id)) return false;
        CtxDecl d = context_decl(id, k); if (d.sort == S_TERM && d.type) { out->what = PN_CHILD; out->id = d.type; }
        return true;
    }
    if (kind == N_SCOPE) {
        ScopeId S = id;
        if (src == 0) { if (k >= scope_arity(S)) return false; LocalDecl d = scope_local(S, k); if (d.type) { out->what = PN_CHILD; out->id = d.type; } return true; }
        if (src == 1) { if (k) return false; Val b = scope_body(S); if (b.sort == VS_REF && b.id) { out->what = PN_CHILD; out->id = b.id; } return true; }
        if (src == 2) { if (k) return false; if (scope_type(S)) { out->what = PN_CHILD; out->id = scope_type(S); } return true; }
        return false;
    }
    RefId t = id;
    if (ref_is_var(t)) {
        if (src != 0 || k) return false;
        TermVarId x = ref_var_id(t); if (!is_bound_id(x) && term_var_type(x)) { out->what = PN_CHILD; out->id = term_var_type(x); }
        return true;
    }
    if (ref_is_tview(t)) {
        if (src != 0) return false;
        TEnvId E = tenv_of(t); if (k >= tenv_size(E)) return false;
        uint64_t slot; TVal v; tenv_entry(E, k, &slot, &v);
        if (v.sort == PS_REF && v.id) { out->what = PN_CHILD; out->id = v.id; }
        else if (v.sort == PS_SCOPE && v.id) { out->what = PN_CHILD; out->kind = N_SCOPE; out->id = v.id; }
        return true;
    }
    OriginId o = ref_origin(t); MapId m = ref_map(t); Tag tag = origin_tag(o);
    switch (src) {
    case 0: if (k) return false; if (tag == T_GLOBAL) { out->what = PN_SYMBOL; out->id = origin_payload(o); } return true;
    case 1: {
        if (tag != T_TCALL || k >= 5) return false;
        const CompiledTransform *tr = transform_get(origin_payload(o) / 2); require(tr, "proof audit: call of an unknown transform");
        uint64_t v = k == 0 ? tr->parameters : k == 1 ? tr->domain : k == 2 ? tr->codomain : k == 3 ? tr->forward_body : tr->reverse_body;
        if (v) { out->what = PN_CHILD; out->kind = k == 0 ? N_CTX : N_REF; out->id = v; }
        return true;
    }
    case 2: { if (k >= origin_nfields(o)) return false; Field fl = origin_field(o, (FieldIndex)k); if (fl.kind == F_REF && fl.id) { out->what = PN_CHILD; out->id = fl.id; } return true; }
    case 3: { if (k >= origin_nbinders(o)) return false; Binder b = origin_binder(o, (BinderSlot)k); if (b.sort == S_TERM && term_var_type(b.formal)) { out->what = PN_CHILD; out->id = term_var_type(b.formal); } return true; }
    case 4: { if (k >= map_n_terms(m)) return false; TermVarId x; RefId im; map_term_entry(m, k, &x, &im); if (im) { out->what = PN_CHILD; out->id = im; } return true; }
    case 5: { size_t n; const uint64_t *xs = varset_get(origin_ft(o), &n); if (k >= n) return false; if (term_var_type(xs[k])) { out->what = PN_CHILD; out->id = term_var_type(xs[k]); } return true; }
    default: return false;
    }
}

static bool node_memo(uint64_t kind, uint64_t id, uint64_t *set) { return kind == N_CTX ? false : memo_get(kind == N_REF ? 1 : 2, id, 0, set); }
/* the symbol set of a node, by the explicit stack; charged one step per
 * expansion and per child visit; memoized per reference and scope */
static uint64_t symbols_of(uint64_t kind, uint64_t id) {
    uint64_t have; if (node_memo(kind, id, &have)) return have;
    VEC(TFrame) st = {0};
    TFrame root; memset(&root, 0, sizeof root); root.kind = kind; root.id = id; words_init(&root.children); words_init(&root.syms); vec_push(&st, root);
    uint64_t result = 0;
    while (st.len) {
        TFrame *f = &st.data[st.len - 1];
        step();
        if (!f->expanded) { expand(f); continue; }
        if (f->next + 1 < f->children.n) {
            uint64_t ck = f->children.w[f->next], cid = f->children.w[f->next + 1]; f->next += 2;
            uint64_t cs;
            if (node_memo(ck, cid, &cs)) { size_t n; const uint64_t *w = set_get(cs, &n); words_append(&f->syms, w, n); continue; }
            /* a node already on the stack (shared syntax reached twice before completion) contributes nothing further: its symbols are counted where it completes */
            bool on = false; for (size_t i = 0; i < st.len; i++) if (st.data[i].kind == ck && st.data[i].id == cid) { on = true; break; }
            if (on) continue;
            TFrame c; memset(&c, 0, sizeof c); c.kind = ck; c.id = cid; words_init(&c.children); words_init(&c.syms); vec_push(&st, c);
            continue;
        }
        uint64_t s = set_intern(f->syms.w, f->syms.n);
        if (f->kind != N_CTX) memo_put(f->kind == N_REF ? 1 : 2, f->id, 0, s);
        words_free(&f->children); words_free(&f->syms);
        st.len--;
        if (st.len) { size_t n; const uint64_t *w = set_get(s, &n); words_append(&st.data[st.len - 1].syms, w, n); }
        else result = s;
    }
    vec_free(&st);
    return result;
}
size_t ref_symbols(RefId t, const uint64_t **out) { require(P.live, "proof-use audit before compiler_init"); uint64_t s = symbols_of(N_REF, t); size_t n; *out = set_get(s, &n); return n; }

/* the outgoing edges of a global: symbols in its declared type, parameter
 * declarations and body; memoized per (symbol, revision) */
static uint64_t global_edges(SymbolId s) {
    uint64_t rev = global_revision(s), have;
    if (memo_get(3, s, rev, &have)) return have;
    Words acc; words_init(&acc);
    size_t n; const uint64_t *w;
    w = set_get(symbols_of(N_REF, global_type(s)), &n); words_append(&acc, w, n);
    RefId body = global_body(s); if (body) { w = set_get(symbols_of(N_REF, body), &n); words_append(&acc, w, n); }
    const uint64_t *params = varset_get(global_params(s), &n);
    for (size_t k = 0; k < n; k++) { size_t m; const uint64_t *v = set_get(symbols_of(N_REF, term_var_type(params[k])), &m); words_append(&acc, v, m); }
    uint64_t id = set_intern(acc.w, acc.n); words_free(&acc);
    memo_put(3, s, rev, id);
    return id;
}

/* reached graph + Tarjan's components with an explicit stack */
typedef struct { uint64_t edges; size_t index, low; bool onstack, seen; } V;
typedef struct { SymbolId s; size_t k; } TF;
static void audit_graph(const uint64_t *roots, size_t nroots, Words *assumptions, Words *recursive, Words *deps) {
    size_t n = global_count();
    V *v = calloc(n + 1, sizeof *v); require(v, "out of memory");
    /* discovery (explicit worklist) */
    Words work; words_init(&work);
    for (size_t k = 0; k < nroots; k++) words_push(&work, roots[k]);
    while (work.n) {
        SymbolId s = work.w[--work.n];
        if (v[s].seen) continue;
        v[s].seen = true; step();
        words_push(deps, s); words_push(deps, global_revision(s));
        if (!global_body(s)) words_push(assumptions, s);
        v[s].edges = global_edges(s);
        size_t m; const uint64_t *e = set_get(v[s].edges, &m);
        for (size_t k = 0; k < m; k++) if (!v[e[k]].seen) words_push(&work, e[k]);
    }
    words_free(&work);
    /* components */
    size_t next = 0; Words stack; words_init(&stack); VEC(TF) call = {0};
    for (SymbolId r = 1; r <= n; r++) {
        if (!v[r].seen || v[r].index) continue;
        TF f0 = { r, 0 }; vec_push(&call, f0); v[r].index = v[r].low = ++next; words_push(&stack, r); v[r].onstack = true;
        while (call.len) {
            TF *f = &call.data[call.len - 1]; SymbolId s = f->s;
            size_t m; const uint64_t *e = set_get(v[s].edges, &m);
            step();
            if (f->k < m) {
                SymbolId d = e[f->k++];
                if (!v[d].index) { v[d].index = v[d].low = ++next; words_push(&stack, d); v[d].onstack = true; TF g = { d, 0 }; vec_push(&call, g); }
                else if (v[d].onstack && v[d].index < v[s].low) v[s].low = v[d].index;
                continue;
            }
            if (v[s].low == v[s].index) {
                Words members; words_init(&members); SymbolId d;
                do { d = stack.w[--stack.n]; v[d].onstack = false; words_push(&members, d); } while (d != s);
                bool cyclic = members.n > 1;
                for (size_t k = 0; k < m && !cyclic; k++) if (e[k] == s) cyclic = true;
                if (cyclic) words_append(recursive, members.w, members.n);
                words_free(&members);
            }
            call.len--;
            if (call.len) { SymbolId parent = call.data[call.len - 1].s; if (v[s].low < v[parent].low) v[parent].low = v[s].low; }
        }
    }
    vec_free(&call); words_free(&stack); free(v);
}

/* verdict records: [status, na, a..., nr, r..., nd, (s,rev)...] */
static ProofUse decode(uint64_t rec, ContextId G, FaceId face, RefId e, RefId E) {
    ProofUse out; memset(&out, 0, sizeof out);
    size_t n; const uint64_t *w = interner_get(&P.records, rec, &n);
    out.status = (ProofUseStatus)w[0]; out.context = G; out.face = face; out.evidence = e; out.type = E; out.session = check_session_id(); out.env = global_env_version();
    size_t i = 1; out.nassumptions = w[i++]; out.assumptions = w + i; i += out.nassumptions;
    out.nrecursive = w[i++]; out.recursive = w + i; i += out.nrecursive;
    out.ndeps = w[i++]; out.deps = w + i;
    out.reason = out.status == PU_PENDING ? "recursive dependencies need a logical witness" : out.status == PU_ASSUMED ? "relative to explicit opaque assumptions" : "acyclic core proof relative to the occurrence context";
    return out;
}
static bool deps_current(const uint64_t *d, size_t nd) { for (size_t k = 0; k < nd; k++) if (global_revision(d[2 * k]) != d[2 * k + 1]) return false; return true; }

ProofUse proof_use(ContextId G, FaceId face, RefId e, RefId E) {
    require(P.live, "proof-use audit before compiler_init");
    ProofUse out; memset(&out, 0, sizeof out);
    out.context = G; out.face = face; out.evidence = e; out.type = E; out.reason = "";
    CheckStatus st = check_admission(&out.reason);
    out.session = check_session_id(); out.env = global_env_version();
    if (st == CK_VALID) st = check_context(G, &out.reason);
    uint64_t level;
    if (st == CK_VALID) st = check_is_type(G, face, E, &level, &out.reason);
    if (st == CK_VALID) st = check(G, face, e, E, &out.reason);
    if (st != CK_VALID) { out.status = st == CK_INVALID ? PU_INVALID : PU_UNRESOLVED; return out; }
    if (fc_is_false(face)) { out.status = PU_CORE; out.reason = "vacuous: a judgment under the false face is local to that face"; return out; }
    /* a cached verdict for this judgment is reused while its recorded revisions are current (§79) */
    uint64_t key[4] = { G, face, e, E }, rec;
    pthread_mutex_lock(&P.mu); bool have = wordmap_get(&P.verdicts, key, 4, &rec); pthread_mutex_unlock(&P.mu);
    if (have) { ProofUse c = decode(rec, G, face, e, E); if (deps_current(c.deps, c.ndeps)) return c; }
    /* roots: the context declarations, the expected type, the evidence */
    Words roots; words_init(&roots);
    { size_t n; const uint64_t *w;
      w = set_get(symbols_of(N_CTX, G), &n); words_append(&roots, w, n);
      w = set_get(symbols_of(N_REF, E), &n); words_append(&roots, w, n);
      w = set_get(symbols_of(N_REF, e), &n); words_append(&roots, w, n); }
    roots.n = sort_unique_u64(roots.w, roots.n);
    Words assumptions, recursive, deps; words_init(&assumptions); words_init(&recursive); words_init(&deps);
    audit_graph(roots.w, roots.n, &assumptions, &recursive, &deps);
    assumptions.n = sort_unique_u64(assumptions.w, assumptions.n); recursive.n = sort_unique_u64(recursive.w, recursive.n);
    ProofUseStatus status = recursive.n ? PU_PENDING : assumptions.n ? PU_ASSUMED : PU_CORE;
    Words r; words_init(&r); words_push(&r, status);
    words_push(&r, assumptions.n); words_append(&r, assumptions.w, assumptions.n);
    words_push(&r, recursive.n); words_append(&r, recursive.w, recursive.n);
    words_push(&r, deps.n / 2); words_append(&r, deps.w, deps.n);
    rec = interner_intern(&P.records, r.w, r.n, NULL);   /* the interner is internally synchronized: hashing, comparison and the copy run outside P.mu */
    pthread_mutex_lock(&P.mu); wordmap_put(&P.verdicts, key, 4, rec); pthread_mutex_unlock(&P.mu);
    words_free(&r); words_free(&roots); words_free(&assumptions); words_free(&recursive); words_free(&deps);
    return decode(rec, G, face, e, E);
}

ProofUse transform_proof_use(TransformId id) {
    ContextId G; FaceId face; RefId e, E;
    ProofUse out; memset(&out, 0, sizeof out);
    if (!transform_evidence(id, &G, &face, &e, &E)) { out.status = PU_INVALID; out.reason = "unknown transform"; return out; }
    return proof_use(G, face, e, E);
}

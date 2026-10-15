#include "check.h"
#include "lib.h"

/* ------------------------------------------------------------------ */
/* state: memo tables and budget                                        */
static WordMap sym_memo; static bool sym_memo_init;

typedef struct { int state; ContextId ctx; FaceId req; RefId type; const char *reason; } OriginRec;  /* state: 0 none, 1 running, 2 valid, 3 invalid */

static struct {
    WordMap origin_idx;          /* OriginId → index+1 */
    VEC(OriginRec) origins; pthread_mutex_t mu;
    WordMap ctx_memo;            /* ContextId → 1 valid / 2 invalid */
    WordMap map_memo;            /* (Delta,psi,sigma,Gamma,chi) → 1 / 2 */
    WordMap conv_memo;           /* (mode,G,face,A,B,T) → 1 equal / 2 unequal / 3 running */
    size_t budget;
} K;

static __thread size_t tl_steps, tl_depth;
static const char *R_BUDGET = "budget exhausted";

void check_init(void) {
    memset(&K, 0, sizeof K);
    wordmap_init(&K.origin_idx); wordmap_init(&K.ctx_memo); wordmap_init(&K.map_memo); wordmap_init(&K.conv_memo);
    pthread_mutex_init(&K.mu, NULL);
}
void check_free(void) {
    if (sym_memo_init) { wordmap_free(&sym_memo); sym_memo_init = false; }
    wordmap_free(&K.origin_idx); wordmap_free(&K.ctx_memo); wordmap_free(&K.map_memo); wordmap_free(&K.conv_memo);
    vec_free(&K.origins); pthread_mutex_destroy(&K.mu);
    memset(&K, 0, sizeof K);
}
void check_set_budget(size_t steps) { K.budget = steps; }
const char *check_status_name(CheckStatus s) { return s == CK_VALID ? "VALID" : s == CK_INVALID ? "INVALID" : "UNRESOLVED"; }
const char *conv_status_name(ConvStatus s) { return s == CV_EQUAL ? "EQUAL" : s == CV_UNEQUAL ? "UNEQUAL" : "UNRESOLVED"; }

static bool budget_ok(void) { tl_steps++; return K.budget == 0 || tl_steps <= K.budget; }
#define ENTER() do { if (tl_depth++ == 0) tl_steps = 0; } while (0)
#define LEAVE() do { tl_depth--; } while (0)

/* ------------------------------------------------------------------ */
/* faces: clauses and clause substitution                               */

static size_t clauses_of(FaceId chi, FaceId **out) {
    Dnf d; fc_to_dnf(chi, &d);
    FaceId *cs = malloc((d.n ? d.n : 1) * sizeof(FaceId));
    for (size_t i = 0; i < d.n; i++) { Dnf one; dnf_init(&one); dnf_add_clause(&one, d.c[i].a, d.c[i].n); cs[i] = fc_from_dnf(&one); }
    size_t n = d.n;
    dnf_free(&d);
    *out = cs;
    return n;
}

/* the endpoints fixed by a single clause, as a dimension map */
static MapId clause_map(FaceId C) {
    Dnf d; fc_to_dnf(C, &d);
    MapBuilder b; mapb_init(&b);
    if (d.n == 1) for (size_t k = 0; k < d.c[0].n; k++) mapb_dim(&b, FC_LIT_DIM(d.c[0].a[k]), FC_LIT_EPS(d.c[0].a[k]) ? iv_one() : iv_zero());
    dnf_free(&d);
    return mapb_finish(&b);
}
static bool iv_equal_under(FaceId C, IntervalId r, IntervalId s) { MapId m = clause_map(C); return iv_reindex(r, m) == iv_reindex(s, m); }
static bool fc_equal_under(FaceId C, FaceId a, FaceId b) { return fc_meet(C, a) == fc_meet(C, b); }

static bool dims_declared(ContextId G, DimSetId S) {
    size_t n; const uint64_t *ds = dimset_get(S, &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_dim(G, ds[k])) return false;
    return true;
}
static DimSetId face_dims(FaceId f) { Words w; words_init(&w); fc_dims(f, &w); DimSetId s = dimset_make(w.w, w.n); words_free(&w); return s; }
static DimSetId iv_dimset(IntervalId r) { Words w; words_init(&w); iv_dims(r, &w); DimSetId s = dimset_make(w.w, w.n); words_free(&w); return s; }

/* ------------------------------------------------------------------ */
/* fresh comparison identities (distinct owner namespace)               */

/* keyed by the comparison request (both sides and the expected type head) */
static TermVarId conv_var(RefId l, RefId r, RefId head, uint64_t slot, RefId type) {
    KeyWord kw[5] = { { KW_CONST, 5000 }, { KW_REF, l }, { KW_REF, r }, { KW_REF, head }, { KW_CONST, slot } };
    return fresh_term_keyed(kw, 5, type);
}
static DimVarId conv_dim(RefId l, RefId r, uint64_t slot) {
    KeyWord kw[4] = { { KW_CONST, 5001 }, { KW_REF, l }, { KW_REF, r }, { KW_CONST, slot } };
    return fresh_dim_keyed(kw, 4);
}

/* ------------------------------------------------------------------ */
/* observation helpers                                                  */

static CheckStatus observe(FaceId C, RefId t, EvalResult **out, const char **reason) {
    WhnfStatus st;
    EvalResult *r = whnf(t, C, &st);
    if (st == W_OK) { *out = r; return CK_VALID; }
    *out = NULL;
    if (st == W_STUCK) { *reason = "unresolved: weak-head observation did not complete (cyclic or suspended demand)"; return CK_UNRESOLVED; }
    *reason = r && r->message ? r->message : "invalid observation";
    return CK_INVALID;
}

/* weak-head observe a type and require a given introduction tag */
static CheckStatus observe_head(FaceId C, RefId T, Tag want, RefId *head, const char **reason) {
    EvalResult *r;
    CheckStatus s = observe(C, T, &r, reason);
    if (s != CK_VALID) return s;
    if (r->cls != R_INTRODUCTION) { *reason = "expected a type former, found a neutral or system"; return CK_INVALID; }
    Head h; open_ref(r->ref, &h); Tag tag = h.tag; head_free(&h);
    if (tag != want) { *reason = "type former mismatch"; return CK_INVALID; }
    *head = r->ref;
    return CK_VALID;
}

static CheckStatus infer_clause(ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static CheckStatus check_clause(ContextId G, FaceId C, RefId t, RefId A, const char **reason);
static ConvStatus conv_type_clause(ContextId G, FaceId C, RefId A, RefId B);
static ConvStatus conv_term_clause(ContextId G, FaceId C, RefId t, RefId u, RefId A);

/* the universe level of a type under a clause */
static CheckStatus level_of(ContextId G, FaceId C, RefId A, uint64_t *lvl, const char **reason) {
    RefId T; CheckStatus s = infer_clause(G, C, A, &T, reason);
    if (s != CK_VALID) return s;
    RefId U;
    s = observe_head(C, T, T_UNIVERSE, &U, reason);
    if (s != CK_VALID) { if (s == CK_INVALID) *reason = "not a type: its type is not a universe"; return s; }
    Head h; open_ref(U, &h); *lvl = h.payload; head_free(&h);
    return CK_VALID;
}

/* ------------------------------------------------------------------ */
/* contexts                                                             */

ContextId origin_context(OriginId C) {
    size_t nd, nt;
    const uint64_t *ds = dimset_get(origin_fd(C), &nd);
    const uint64_t *xs = varset_get(origin_ft(C), &nt);
    CtxDecl *decls = malloc((nd + nt + 1) * sizeof(CtxDecl));
    size_t n = 0;
    for (size_t k = 0; k < nd; k++) { decls[n].sort = S_DIM; decls[n].id = ds[k]; decls[n].type = 0; n++; }
    /* term variables in dependency order: a variable follows the free
     * variables of its declared type */
    bool *placed = calloc(nt ? nt : 1, sizeof(bool));
    size_t done = 0;
    while (done < nt) {
        bool progress = false;
        for (size_t k = 0; k < nt; k++) {
            if (placed[k]) continue;
            size_t m; const uint64_t *fv = varset_get(ref_freevars(term_var_type(xs[k])), &m);
            bool ready = true;
            for (size_t q = 0; q < m && ready; q++) { bool found = false; for (size_t j = 0; j < nt; j++) if (xs[j] == fv[q] && placed[j]) found = true; if (!found) ready = false; }
            if (!ready) continue;
            decls[n].sort = S_TERM; decls[n].id = xs[k]; decls[n].type = term_var_type(xs[k]); n++;
            placed[k] = true; done++; progress = true;
        }
        require(progress, "cyclic declaration dependency in origin boundary");
    }
    free(placed);
    ContextId ctx = context_make(n, decls, origin_required(C));
    free(decls);
    return ctx;
}

CheckStatus check_context(ContextId G, const char **reason) {
    uint64_t key[1] = { G }, v;
    if (wordmap_get(&K.ctx_memo, key, 1, &v)) { if (v == 1) return CK_VALID; *reason = "context previously found invalid"; return CK_INVALID; }
    ENTER();
    CheckStatus st = CK_VALID;
    size_t n = context_size(G);
    FaceId assumption = context_assumption(G);
    /* 1. unique identities; the assumption uses declared dimensions */
    uint64_t *dims = malloc((n ? n : 1) * sizeof(uint64_t)); size_t nd = 0;
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(G, k);
        for (size_t j = 0; j < k; j++) { CtxDecl e = context_decl(G, j); if (e.sort == d.sort && e.id == d.id) { *reason = "duplicate declaration"; st = CK_INVALID; } }
        if (d.sort == S_DIM) dims[nd++] = d.id;
    }
    if (st == CK_VALID) {
        DimSetId all = dimset_make(dims, nd);
        size_t m; const uint64_t *fd = dimset_get(face_dims(assumption), &m);
        for (size_t q = 0; q < m; q++) if (!dimset_contains(all, fd[q])) { *reason = "assumption mentions an undeclared dimension"; st = CK_INVALID; }
    }
    /* 2. each term declaration's type and required face use only the prefix;
     * the type is a type under the assumption projected to the prefix dims */
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(G, k);
        if (d.sort != S_TERM) continue;
        CtxDecl *prefix = malloc((k ? k : 1) * sizeof(CtxDecl));
        uint64_t *pd = malloc((k ? k : 1) * sizeof(uint64_t)); size_t npd = 0;
        for (size_t j = 0; j < k; j++) { prefix[j] = context_decl(G, j); if (prefix[j].sort == S_DIM) pd[npd++] = prefix[j].id; }
        DimSetId pds = dimset_make(pd, npd);
        FaceId proj = fc_project(assumption, dimset_get(pds, &npd), npd);
        ContextId P = context_make(k, prefix, proj);
        free(prefix); free(pd);
        size_t m; const uint64_t *fv = varset_get(ref_freevars(d.type), &m);
        for (size_t q = 0; q < m && st == CK_VALID; q++) if (!context_declares_term(P, fv[q], NULL)) { *reason = "declaration type mentions a variable not declared earlier"; st = CK_INVALID; }
        if (st == CK_VALID && !dims_declared(P, ref_support(d.type))) { *reason = "declaration type mentions a dimension not declared earlier"; st = CK_INVALID; }
        if (st == CK_VALID && !dims_declared(P, face_dims(term_var_required(d.id)))) { *reason = "declaration's required face mentions a dimension not declared earlier"; st = CK_INVALID; }
        if (st == CK_VALID && d.type != term_var_type(d.id)) { *reason = "declared type differs from the variable's declaration"; st = CK_INVALID; }
        if (st == CK_VALID) {
            FaceId *cs; size_t nc = clauses_of(proj, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) { uint64_t l; st = level_of(P, cs[c], d.type, &l, reason); }
            free(cs);
        }
    }
    free(dims);
    if (st != CK_UNRESOLVED) wordmap_put(&K.ctx_memo, key, 1, st == CK_VALID ? 1 : 2);
    LEAVE();
    return st;
}

/* the judgment Γ;χ: the context carries χ as its assumption, so that
 * declaration types are validated under the same face they are used under */
static ContextId under(ContextId G, FaceId C) {
    if (context_assumption(G) == C) return G;
    size_t n = context_size(G);
    CtxDecl *ds = malloc((n ? n : 1) * sizeof(CtxDecl));
    for (size_t k = 0; k < n; k++) ds[k] = context_decl(G, k);
    ContextId out = context_make(n, ds, C);
    free(ds);
    return out;
}
static ContextId extend_term(ContextId G, TermVarId x, RefId type) { return context_extend_term(G, x, type); }
static ContextId extend_dim(ContextId G, DimVarId j) { return context_extend_dim(G, j); }

/* ------------------------------------------------------------------ */
/* typed maps and origins (substitution lemma)                          */

CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason) {
    Delta = under(Delta, psi); Gamma = under(Gamma, chi);
    uint64_t key[5] = { Delta, psi, sigma, Gamma, chi }, v;
    if (wordmap_get(&K.map_memo, key, 5, &v)) { if (v == 1) return CK_VALID; *reason = "map previously found invalid"; return CK_INVALID; }
    ENTER();
    CheckStatus st = check_context(Gamma, reason);
    if (st == CK_VALID) st = check_context(Delta, reason);
    size_t n = context_size(Gamma);
    for (size_t k = 0; k < n && st == CK_VALID; k++) {
        CtxDecl d = context_decl(Gamma, k);
        if (d.sort == S_DIM) {
            /* the dimension image is an interval over the source dimensions */
            if (!dims_declared(Delta, iv_dimset(map_dim_image(sigma, d.id)))) { *reason = "dimension image mentions an undeclared source dimension"; st = CK_INVALID; }
            continue;
        }
        /* term image against A[sigma] under the source face (vacuous on false) */
        RefId image = map_term_image(sigma, d.id);
        RefId Asub = reindex(d.type, sigma);
        FaceId *cs; size_t nc = clauses_of(psi, &cs);
        for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(Delta, cs[c], image, Asub, reason);
        free(cs);
        /* the target declaration's own required face obligation */
        if (st == CK_VALID && !fc_entails(psi, fc_reindex(term_var_required(d.id), sigma))) { *reason = "source face does not entail a target declaration's required face"; st = CK_INVALID; }
    }
    if (st == CK_VALID && !fc_entails(psi, fc_reindex(chi, sigma))) { *reason = "source face does not entail the substituted target assumption"; st = CK_INVALID; }
    if (st != CK_UNRESOLVED) wordmap_put(&K.map_memo, key, 5, st == CK_VALID ? 1 : 2);
    LEAVE();
    return st;
}

static CheckStatus infer_head(ContextId G, FaceId C, RefId t, RefId *type, const char **reason);
static CheckStatus validate_symbol(SymbolId s, const char **reason);

CheckStatus check_origin(OriginId C, ContextId *ctx_out, FaceId *req_out, RefId *type_out, const char **reason) {
    uint64_t key[1] = { C }, idx;
    pthread_mutex_lock(&K.mu);
    if (!wordmap_get(&K.origin_idx, key, 1, &idx)) {
        OriginRec rec; memset(&rec, 0, sizeof rec);
        vec_push(&K.origins, rec);
        idx = K.origins.len;
        wordmap_put(&K.origin_idx, key, 1, idx);
    }
    OriginRec snap = K.origins.data[idx - 1];
    int state = snap.state;
    if (state == 0) K.origins.data[idx - 1].state = 1;
    pthread_mutex_unlock(&K.mu);
    if (state == 2) { if (ctx_out) *ctx_out = snap.ctx; if (req_out) *req_out = snap.req; if (type_out) *type_out = snap.type; return CK_VALID; }
    if (state == 3) { *reason = snap.reason; return CK_INVALID; }
    if (state == 1) { *reason = "unresolved: origin validation is already in progress (cyclic dependency)"; return CK_UNRESOLVED; }
    ENTER();
    ContextId ctx = origin_context(C);
    FaceId req = origin_required(C);
    RefId type = 0;
    CheckStatus st = check_context(ctx, reason);
    if (st == CK_VALID) {
        RefId t = make_view(C, map_identity());
        /* a system's own required face is its coverage; the body is checked under it */
        FaceId *cs; size_t nc = clauses_of(req, &cs);
        RefId *types = malloc((nc ? nc : 1) * sizeof(RefId));
        for (size_t c = 0; c < nc && st == CK_VALID; c++) st = infer_head(ctx, cs[c], t, &types[c], reason);
        if (st == CK_VALID) {
            bool same = true;
            for (size_t c = 1; c < nc; c++) if (types[c] != types[0]) same = false;
            if (nc == 0) type = mk_system(0, NULL, NULL);            /* required face false: vacuous */
            else if (same) type = types[0];
            else type = mk_system(nc, cs, types);
        }
        free(types); free(cs);
    }
    pthread_mutex_lock(&K.mu);
    { OriginRec *r = &K.origins.data[idx - 1];
      if (st == CK_VALID) { r->state = 2; r->ctx = ctx; r->req = req; r->type = type; }
      else if (st == CK_INVALID) { r->state = 3; r->reason = *reason; }
      else r->state = 0; }                              /* unresolved: not a verdict */
    pthread_mutex_unlock(&K.mu);
    if (st == CK_VALID) { if (ctx_out) *ctx_out = ctx; if (req_out) *req_out = req; if (type_out) *type_out = type; }
    LEAVE();
    return st;
}

/* ------------------------------------------------------------------ */
/* inference                                                            */

static CheckStatus glue_data_ok(ContextId G, FaceId C, RefId A, FaceId alpha, RefId T, RefId e, uint64_t *lvl, const char **reason) {
    CheckStatus st = level_of(G, C, A, lvl, reason);
    if (st != CK_VALID) return st;
    if (!dims_declared(G, face_dims(alpha))) { *reason = "Glue face mentions an undeclared dimension"; return CK_INVALID; }
    FaceId Ca = fc_meet(C, alpha);
    if (fc_is_false(Ca)) return CK_VALID;              /* vacuous */
    FaceId *cs; size_t nc = clauses_of(Ca, &cs);
    for (size_t c = 0; c < nc && st == CK_VALID; c++) {
        uint64_t lT;
        st = level_of(G, cs[c], T, &lT, reason);
        if (st == CK_VALID && lT != *lvl) { *reason = "Glue fibre type is not in the base's universe"; st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, cs[c], e, mk_equiv(T, A), reason);
    }
    free(cs);
    return st;
}

static CheckStatus infer_head(ContextId G, FaceId C, RefId t, RefId *type, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    if (ref_is_var(t)) {
        TermVarId x = ref_var_id(t);
        RefId ty;
        if (!context_declares_term(G, x, &ty)) { *reason = "unbound variable"; return CK_INVALID; }
        if (!fc_entails(C, term_var_required(x))) { *reason = "variable used outside its required face"; return CK_INVALID; }
        *type = ty;
        return CK_VALID;
    }
    Head h; open_ref(t, &h);
    CheckStatus st = CK_VALID;
    switch (h.tag) {
    case T_UNIVERSE: *type = mk_universe(h.payload + 1); break;
    case T_PI: case T_SIGMA: {
        uint64_t i, j;
        st = level_of(G, C, h.f[0].id, &i, reason);
        if (st != CK_VALID) break;
        TermOpen o = resolve_term_binder(t, 0, 1);
        st = level_of(extend_term(G, o.x, o.type), C, o.body, &j, reason);
        if (st == CK_VALID) *type = mk_universe(i > j ? i : j);
        break;
    }
    case T_LAM: {
        uint64_t i;
        st = level_of(G, C, h.f[0].id, &i, reason);
        if (st != CK_VALID) break;
        TermOpen o = resolve_term_binder(t, 0, 1);
        RefId B;
        st = infer_clause(extend_term(G, o.x, o.type), C, o.body, &B, reason);
        if (st == CK_VALID) *type = mk_pi(o.x, o.type, B);
        break;
    }
    case T_APP: {
        RefId Tf, P;
        st = infer_clause(G, C, h.f[0].id, &Tf, reason);
        if (st != CK_VALID) break;
        st = observe_head(C, Tf, T_PI, &P, reason);
        if (st != CK_VALID) { if (st == CK_INVALID) *reason = "application of a non-function"; break; }
        Head hp; open_ref(P, &hp); RefId dom = hp.f[0].id; head_free(&hp);
        st = check_clause(G, C, h.f[1].id, dom, reason);
        if (st == CK_VALID) *type = apply_term_binder(P, 0, 1, h.f[1].id);
        break;
    }
    case T_PAIR: {
        RefId A, B;
        st = infer_clause(G, C, h.f[0].id, &A, reason);
        if (st == CK_VALID) st = infer_clause(G, C, h.f[1].id, &B, reason);
        if (st == CK_VALID) { TermVarId x = conv_var(t, t, A, 0, A); *type = mk_sigma(x, A, B); }
        break;
    }
    case T_FST: case T_SND: {
        RefId Tp, P;
        st = infer_clause(G, C, h.f[0].id, &Tp, reason);
        if (st != CK_VALID) break;
        st = observe_head(C, Tp, T_SIGMA, &P, reason);
        if (st != CK_VALID) { if (st == CK_INVALID) *reason = "projection of a non-pair"; break; }
        Head hp; open_ref(P, &hp); RefId dom = hp.f[0].id; head_free(&hp);
        *type = h.tag == T_FST ? dom : apply_term_binder(P, 0, 1, mk_fst(h.f[0].id));
        break;
    }
    case T_PATH: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        uint64_t l;
        st = level_of(extend_dim(G, o.j), C, o.body, &l, reason);
        if (st == CK_VALID) st = check_clause(G, C, h.f[1].id, reindex_dim(o.body, o.j, iv_zero()), reason);
        if (st == CK_VALID) st = check_clause(G, C, h.f[2].id, reindex_dim(o.body, o.j, iv_one()), reason);
        if (st == CK_VALID) *type = mk_universe(l);
        break;
    }
    case T_PLAM: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        RefId Bj;
        st = infer_clause(extend_dim(G, o.j), C, o.body, &Bj, reason);
        if (st == CK_VALID) *type = mk_path(o.j, Bj, reindex_dim(o.body, o.j, iv_zero()), reindex_dim(o.body, o.j, iv_one()));
        break;
    }
    case T_PAPP: {
        DimOpen o = resolve_dim_binder(t, 0, 0);
        uint64_t l;
        st = level_of(extend_dim(G, o.j), C, o.body, &l, reason);
        if (st == CK_VALID) st = check_clause(G, C, h.f[1].id, reindex_dim(o.body, o.j, iv_zero()), reason);
        if (st == CK_VALID) st = check_clause(G, C, h.f[2].id, reindex_dim(o.body, o.j, iv_one()), reason);
        if (st == CK_VALID && !dims_declared(G, iv_dimset(h.f[4].id))) { *reason = "path applied to an out-of-scope interval"; st = CK_INVALID; }
        if (st == CK_VALID) st = check_clause(G, C, h.f[3].id, mk_path(o.j, o.body, h.f[1].id, h.f[2].id), reason);
        if (st == CK_VALID) *type = reindex_dim(o.body, o.j, h.f[4].id);
        break;
    }
    case T_GLUE_TYPE: {
        uint64_t l;
        st = glue_data_ok(G, C, h.f[0].id, h.f[1].id, h.f[2].id, h.f[3].id, &l, reason);
        if (st == CK_VALID) *type = mk_universe(l);
        break;
    }
    case T_GLUE_INTRO: {
        uint64_t l;
        RefId A = h.f[0].id, T = h.f[2].id, e = h.f[3].id, tt = h.f[4].id, a = h.f[5].id; FaceId alpha = h.f[1].id;
        st = glue_data_ok(G, C, A, alpha, T, e, &l, reason);
        if (st == CK_VALID) st = check_clause(G, C, a, A, reason);
        FaceId Ca = fc_meet(C, alpha);
        if (st == CK_VALID && !fc_is_false(Ca)) {
            FaceId *cs; size_t nc = clauses_of(Ca, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                st = check_clause(G, cs[c], tt, T, reason);
                if (st != CK_VALID) break;
                ConvStatus cv = conv_term_clause(G, cs[c], mk_app(mk_fst(e), tt), a, A);
                if (cv == CV_UNEQUAL) { *reason = "glue: e.map(t) is not the base term on the Glue face"; st = CK_INVALID; }
                else if (cv == CV_UNRESOLVED) { *reason = "unresolved: glue map agreement"; st = CK_UNRESOLVED; }
            }
            free(cs);
        }
        if (st == CK_VALID) *type = mk_glue_type(A, alpha, T, e);
        break;
    }
    case T_UNGLUE: {
        uint64_t l;
        RefId A = h.f[0].id, T = h.f[2].id, e = h.f[3].id, v = h.f[4].id; FaceId alpha = h.f[1].id;
        st = glue_data_ok(G, C, A, alpha, T, e, &l, reason);
        if (st == CK_VALID) st = check_clause(G, C, v, mk_glue_type(A, alpha, T, e), reason);
        if (st == CK_VALID) *type = A;
        break;
    }
    case T_COMP: {
        DimOpen fam = resolve_dim_binder(t, 0, 0), tube = resolve_dim_binder(t, 0, 2);
        FaceId phi = h.f[1].id; RefId a0 = h.f[3].id;
        ContextId Gj = extend_dim(G, fam.j);
        uint64_t l;
        st = level_of(Gj, C, fam.body, &l, reason);
        if (st == CK_VALID && (!dims_declared(G, face_dims(phi)) || dimset_contains(face_dims(phi), fam.j))) { *reason = "composition face must be in scope and independent of the bound dimension"; st = CK_INVALID; }
        RefId A0 = reindex_dim(fam.body, fam.j, iv_zero());
        if (st == CK_VALID) st = check_clause(G, C, a0, A0, reason);
        FaceId Cp = fc_meet(C, phi);
        if (st == CK_VALID && !fc_is_false(Cp)) {
            FaceId *cs; size_t nc = clauses_of(Cp, &cs);
            for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                st = check_clause(Gj, cs[c], tube.body, fam.body, reason);
                if (st != CK_VALID) break;
                ConvStatus cv = conv_term_clause(G, cs[c], reindex_dim(tube.body, tube.j, iv_zero()), a0, A0);
                if (cv == CV_UNEQUAL) { *reason = "composition: tube at 0 disagrees with the cap"; st = CK_INVALID; }
                else if (cv == CV_UNRESOLVED) { *reason = "unresolved: cap/tube agreement"; st = CK_UNRESOLVED; }
            }
            free(cs);
        }
        if (st == CK_VALID) *type = reindex_dim(fam.body, fam.j, iv_one());
        break;
    }
    case T_SYSTEM: {
        size_t nb = h.n / 2;
        FaceId uni = fc_false();
        for (size_t k = 0; k < nb; k++) uni = fc_join(uni, h.f[2 * k].id);
        if (!fc_entails(C, uni)) { *reason = "system does not cover the face"; st = CK_INVALID; break; }
        RefId *types = calloc(nb ? nb : 1, sizeof(RefId));
        size_t sel = nb;
        for (size_t k = 0; k < nb && st == CK_VALID; k++) {
            FaceId Ck = fc_meet(C, h.f[2 * k].id);
            if (!dims_declared(G, face_dims(h.f[2 * k].id))) { *reason = "system guard mentions an undeclared dimension"; st = CK_INVALID; break; }
            if (fc_is_false(Ck)) continue;
            st = infer_clause(G, Ck, h.f[2 * k + 1].id, &types[k], reason);
            if (st == CK_VALID && sel == nb && fc_entails(C, h.f[2 * k].id)) sel = k;
        }
        /* overlaps: branches agree in their (convertible) types */
        for (size_t k = 0; k < nb && st == CK_VALID; k++)
            for (size_t l = k + 1; l < nb && st == CK_VALID; l++) {
                FaceId Ckl = fc_meet(C, fc_meet(h.f[2 * k].id, h.f[2 * l].id));
                if (fc_is_false(Ckl)) continue;
                FaceId *cs; size_t nc = clauses_of(Ckl, &cs);
                for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                    ConvStatus cv = conv_type_clause(G, cs[c], types[k], types[l]);
                    if (cv == CV_EQUAL) cv = conv_term_clause(G, cs[c], h.f[2 * k + 1].id, h.f[2 * l + 1].id, types[k]);
                    if (cv == CV_UNEQUAL) { *reason = "system branches disagree on an overlap"; st = CK_INVALID; }
                    else if (cv == CV_UNRESOLVED) { *reason = "unresolved: system overlap"; st = CK_UNRESOLVED; }
                }
                free(cs);
            }
        if (st == CK_VALID) { require(sel < nb, "a covered system has an entailed branch under a single clause"); *type = types[sel]; }
        free(types);
        break;
    }
    case T_GLOBAL: {
        SymbolId s = (SymbolId)h.payload;
        st = validate_symbol(s, reason);
        if (st != CK_VALID) break;
        ContextId Gs = origin_context(h.origin);
        st = check_map(G, C, h.map, Gs, fc_true(), reason);
        if (st == CK_VALID) *type = reindex(global_type(s), h.map);
        break;
    }
    }
    head_free(&h);
    return st;
}

/* inference of an arbitrary reference under a clause: variables directly,
 * views through the substitution lemma */
static CheckStatus infer_clause(ContextId G, FaceId C, RefId t, RefId *type, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    if (ref_is_var(t)) return infer_head(G, C, t, type, reason);
    if (origin_tag(ref_origin(t)) == T_GLOBAL) return infer_head(G, C, t, type, reason);
    OriginId O = ref_origin(t);
    ContextId Gc; FaceId req; RefId Ac;
    CheckStatus st = check_origin(O, &Gc, &req, &Ac, reason);
    if (st != CK_VALID) return st;
    st = check_map(G, C, ref_map(t), Gc, req, reason);
    if (st != CK_VALID) return st;
    *type = reindex(Ac, ref_map(t));
    return CK_VALID;
}

/* scope validity independent of the face: every free variable and dimension
 * is declared, and the face itself is in scope */
static CheckStatus scope_ok(ContextId G, FaceId chi, RefId t, const char **reason) {
    if (!dims_declared(G, face_dims(chi))) { *reason = "face mentions an undeclared dimension"; return CK_INVALID; }
    size_t n; const uint64_t *xs = varset_get(ref_freevars(t), &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_term(G, xs[k], NULL)) { *reason = "unbound variable"; return CK_INVALID; }
    if (!dims_declared(G, ref_support(t))) { *reason = "unbound dimension"; return CK_INVALID; }
    return CK_VALID;
}

Inference infer(ContextId G, FaceId chi, RefId t) {
    Inference out = { CK_VALID, 0, NULL };
    ENTER();
    out.st = scope_ok(G, chi, t, &out.reason);
    if (out.st != CK_VALID) { LEAVE(); return out; }
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    RefId *types = malloc((nc ? nc : 1) * sizeof(RefId));
    for (size_t c = 0; c < nc && out.st == CK_VALID; c++) out.st = infer_clause(G, cs[c], t, &types[c], &out.reason);
    if (out.st == CK_VALID) {
        if (nc == 0) out.type = mk_system(0, NULL, NULL);
        else { bool same = true; for (size_t c = 1; c < nc; c++) if (types[c] != types[0]) same = false; out.type = same ? types[0] : mk_system(nc, cs, types); }
    }
    free(types); free(cs);
    LEAVE();
    return out;
}

/* ------------------------------------------------------------------ */
/* checking against an expected type                                    */

static CheckStatus check_clause(ContextId G, FaceId C, RefId t, RefId A, const char **reason) {
    if (!budget_ok()) { *reason = R_BUDGET; return CK_UNRESOLVED; }
    G = under(G, C);
    Tag tag = 0;
    if (!ref_is_var(t)) tag = origin_tag(ref_origin(t));
    if (tag == T_LAM || tag == T_PAIR || tag == T_PLAM || tag == T_SYSTEM) {
        Head h; open_ref(t, &h);
        CheckStatus st = CK_VALID;
        RefId P;
        switch (tag) {
        case T_LAM: {
            st = observe_head(C, A, T_PI, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "lambda checked against a non-product type"; break; }
            Head hp; open_ref(P, &hp); RefId D = hp.f[0].id; head_free(&hp);
            ConvStatus cv = conv_type_clause(G, C, h.f[0].id, D);
            if (cv == CV_UNEQUAL) { *reason = "lambda domain differs from the expected domain"; st = CK_INVALID; break; }
            if (cv == CV_UNRESOLVED) { *reason = "unresolved: lambda domain conversion"; st = CK_UNRESOLVED; break; }
            { uint64_t l; st = level_of(G, C, h.f[0].id, &l, reason); if (st != CK_VALID) break; }   /* the annotation is a type */
            TermVarId x = conv_var(t, P, P, 0, D);
            st = check_clause(extend_term(G, x, D), C, apply_term_binder(t, 0, 1, ref_var(x)), apply_term_binder(P, 0, 1, ref_var(x)), reason);
            break;
        }
        case T_PAIR: {
            st = observe_head(C, A, T_SIGMA, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "pair checked against a non-sum type"; break; }
            Head hp; open_ref(P, &hp); RefId D = hp.f[0].id; head_free(&hp);
            st = check_clause(G, C, h.f[0].id, D, reason);
            if (st == CK_VALID) st = check_clause(G, C, h.f[1].id, apply_term_binder(P, 0, 1, h.f[0].id), reason);
            break;
        }
        case T_PLAM: {
            st = observe_head(C, A, T_PATH, &P, reason);
            if (st != CK_VALID) { if (st == CK_INVALID) *reason = "path lambda checked against a non-path type"; break; }
            Head hp; open_ref(P, &hp); RefId l = hp.f[1].id, r = hp.f[2].id; head_free(&hp);
            DimVarId j = conv_dim(t, P, 0);
            RefId body = apply_dim_binder(t, 0, 0, iv_var(j)), Bj = apply_dim_binder(P, 0, 0, iv_var(j));
            st = check_clause(extend_dim(G, j), C, body, Bj, reason);
            if (st != CK_VALID) break;
            ConvStatus c0 = conv_term_clause(G, C, apply_dim_binder(t, 0, 0, iv_zero()), l, apply_dim_binder(P, 0, 0, iv_zero()));
            ConvStatus c1 = c0 == CV_EQUAL ? conv_term_clause(G, C, apply_dim_binder(t, 0, 0, iv_one()), r, apply_dim_binder(P, 0, 0, iv_one())) : c0;
            if (c1 == CV_UNEQUAL) { *reason = "path lambda endpoints differ from the path type's endpoints"; st = CK_INVALID; }
            else if (c1 == CV_UNRESOLVED) { *reason = "unresolved: path endpoint conversion"; st = CK_UNRESOLVED; }
            break;
        }
        case T_SYSTEM: {
            size_t nb = h.n / 2;
            FaceId uni = fc_false();
            for (size_t k = 0; k < nb; k++) uni = fc_join(uni, h.f[2 * k].id);
            if (!fc_entails(C, uni)) { *reason = "system does not cover the face"; st = CK_INVALID; break; }
            for (size_t k = 0; k < nb && st == CK_VALID; k++) {
                FaceId Ck = fc_meet(C, h.f[2 * k].id);
                if (!dims_declared(G, face_dims(h.f[2 * k].id))) { *reason = "system guard mentions an undeclared dimension"; st = CK_INVALID; break; }
                if (fc_is_false(Ck)) continue;
                FaceId *cs; size_t nc = clauses_of(Ck, &cs);
                for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(G, cs[c], h.f[2 * k + 1].id, A, reason);
                free(cs);
            }
            for (size_t k = 0; k < nb && st == CK_VALID; k++)
                for (size_t l = k + 1; l < nb && st == CK_VALID; l++) {
                    FaceId Ckl = fc_meet(C, fc_meet(h.f[2 * k].id, h.f[2 * l].id));
                    if (fc_is_false(Ckl)) continue;
                    FaceId *cs; size_t nc = clauses_of(Ckl, &cs);
                    for (size_t c = 0; c < nc && st == CK_VALID; c++) {
                        ConvStatus cv = conv_term_clause(G, cs[c], h.f[2 * k + 1].id, h.f[2 * l + 1].id, A);
                        if (cv == CV_UNEQUAL) { *reason = "system branches disagree on an overlap"; st = CK_INVALID; }
                        else if (cv == CV_UNRESOLVED) { *reason = "unresolved: system overlap"; st = CK_UNRESOLVED; }
                    }
                    free(cs);
                }
            break;
        }
        default: break;
        }
        head_free(&h);
        return st;
    }
    RefId T;
    CheckStatus st = infer_clause(G, C, t, &T, reason);
    if (st != CK_VALID) return st;
    ConvStatus cv = conv_type_clause(G, C, T, A);
    if (cv == CV_EQUAL) return CK_VALID;
    if (cv == CV_UNEQUAL) {
        if (getenv("CK_DEBUG")) { fprintf(stderr, "UNEQUAL under "); fc_print(C, stderr); fprintf(stderr, "\n  term: "); print_ref_depth(t, stderr, 2); fprintf(stderr, "\n  inferred: "); print_ref_depth(T, stderr, 3); fprintf(stderr, "\n  expected: "); print_ref_depth(A, stderr, 3); fprintf(stderr, "\n"); }
        *reason = "inferred type is not convertible to the expected type"; return CK_INVALID;
    }
    *reason = "unresolved: type conversion";
    return CK_UNRESOLVED;
}

CheckStatus check(ContextId G, FaceId chi, RefId t, RefId A, const char **reason) {
    ENTER();
    CheckStatus st = scope_ok(G, chi, t, reason);
    if (st == CK_VALID) st = scope_ok(G, chi, A, reason);
    if (st != CK_VALID) { LEAVE(); return st; }
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    for (size_t c = 0; c < nc && st == CK_VALID; c++) st = check_clause(G, cs[c], t, A, reason);
    free(cs);
    LEAVE();
    return st;
}

/* ------------------------------------------------------------------ */
/* conversion                                                           */

static ConvStatus conv_memo_get(uint64_t mode, ContextId G, FaceId C, RefId a, RefId b, RefId T, uint64_t key[6], bool *found) {
    DimSetId S = dimset_union(ref_support(a), ref_support(b));
    if (T) S = dimset_union(S, ref_support(T));
    size_t n; const uint64_t *ds = dimset_get(S, &n);
    key[0] = mode; key[1] = under(G, fc_true()); key[2] = fc_project(C, ds, n); key[3] = a; key[4] = b; key[5] = T;
    uint64_t v;
    *found = wordmap_get(&K.conv_memo, key, 6, &v);
    if (!*found) return CV_UNRESOLVED;
    return v == 1 ? CV_EQUAL : v == 2 ? CV_UNEQUAL : CV_UNRESOLVED;   /* 3 = running: a cycle */
}
static void conv_memo_set(uint64_t key[6], ConvStatus s) { wordmap_put(&K.conv_memo, key, 6, s == CV_EQUAL ? 1 : s == CV_UNEQUAL ? 2 : 3); }
static void conv_memo_clear_running(uint64_t key[6]) { wordmap_put(&K.conv_memo, key, 6, 4); }   /* 4 = no verdict */

static ConvStatus and3(ConvStatus a, ConvStatus b) {
    if (a == CV_UNEQUAL || b == CV_UNEQUAL) return CV_UNEQUAL;
    if (a == CV_UNRESOLVED || b == CV_UNRESOLVED) return CV_UNRESOLVED;
    return CV_EQUAL;
}

static ConvStatus spine(ContextId G, FaceId C, RefId n1, RefId n2);

static ConvStatus observe_both(FaceId C, RefId a, RefId b, EvalResult **ra, EvalResult **rb) {
    const char *reason;
    if (observe(C, a, ra, &reason) != CK_VALID) return CV_UNRESOLVED;
    if (observe(C, b, rb, &reason) != CK_VALID) return CV_UNRESOLVED;
    return CV_EQUAL;
}

static ConvStatus conv_type_clause(ContextId G, FaceId C, RefId A, RefId B) {
    if (A == B) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    uint64_t key[6]; bool found;
    ConvStatus memo = conv_memo_get(1, G, C, A, B, 0, key, &found);
    if (found) { uint64_t v; wordmap_get(&K.conv_memo, key, 6, &v); if (v == 1 || v == 2) return memo; if (v == 3) return CV_UNRESOLVED; }
    conv_memo_set(key, CV_UNRESOLVED);          /* running */
    ConvStatus out = CV_UNRESOLVED;
    EvalResult *ra, *rb;
    if (observe_both(C, A, B, &ra, &rb) != CV_EQUAL) goto done;
    if (ra->ref == rb->ref) { out = CV_EQUAL; goto done; }
    if (ra->cls == R_SYSTEM || rb->cls == R_SYSTEM) { out = CV_UNRESOLVED; goto done; }
    if (ra->cls != rb->cls) { out = CV_UNEQUAL; goto done; }
    if (ra->cls == R_NEUTRAL) { out = spine(G, C, ra->ref, rb->ref); goto done; }
    {
        Head ha, hb; open_ref(ra->ref, &ha); open_ref(rb->ref, &hb);
        if (ha.tag != hb.tag) out = CV_UNEQUAL;
        else switch (ha.tag) {
        case T_UNIVERSE: out = ha.payload == hb.payload ? CV_EQUAL : CV_UNEQUAL; break;
        case T_PI: case T_SIGMA: {
            out = conv_type_clause(G, C, ha.f[0].id, hb.f[0].id);
            if (out != CV_EQUAL) break;
            TermVarId x = conv_var(ra->ref, rb->ref, ra->ref, 0, ha.f[0].id);
            out = conv_type_clause(extend_term(G, x, ha.f[0].id), C, apply_term_binder(ra->ref, 0, 1, ref_var(x)), apply_term_binder(rb->ref, 0, 1, ref_var(x)));
            break;
        }
        case T_PATH: {
            DimVarId j = conv_dim(ra->ref, rb->ref, 0);
            RefId Ba = apply_dim_binder(ra->ref, 0, 0, iv_var(j)), Bb = apply_dim_binder(rb->ref, 0, 0, iv_var(j));
            out = conv_type_clause(extend_dim(G, j), C, Ba, Bb);
            if (out == CV_EQUAL) out = conv_term_clause(G, C, ha.f[1].id, hb.f[1].id, reindex_dim(Ba, j, iv_zero()));
            if (out == CV_EQUAL) out = conv_term_clause(G, C, ha.f[2].id, hb.f[2].id, reindex_dim(Ba, j, iv_one()));
            break;
        }
        case T_GLUE_TYPE: {
            if (!fc_equal_under(C, ha.f[1].id, hb.f[1].id)) { out = CV_UNEQUAL; break; }
            out = conv_type_clause(G, C, ha.f[0].id, hb.f[0].id);
            FaceId Ca = fc_meet(C, ha.f[1].id);
            if (out == CV_EQUAL && !fc_is_false(Ca)) {
                FaceId *cs; size_t nc = clauses_of(Ca, &cs);
                for (size_t c = 0; c < nc && out == CV_EQUAL; c++) {
                    out = conv_type_clause(G, cs[c], ha.f[2].id, hb.f[2].id);
                    if (out == CV_EQUAL) out = conv_term_clause(G, cs[c], ha.f[3].id, hb.f[3].id, mk_equiv(ha.f[2].id, ha.f[0].id));
                }
                free(cs);
            }
            break;
        }
        default: out = CV_UNEQUAL; break;       /* an introduction that is not a type former */
        }
        head_free(&ha); head_free(&hb);
    }
done:
    if (out == CV_UNRESOLVED) conv_memo_clear_running(key); else conv_memo_set(key, out);
    return out;
}

static ConvStatus conv_term_clause(ContextId G, FaceId C, RefId t, RefId u, RefId A) {
    if (t == u) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    uint64_t key[6]; bool found;
    ConvStatus memo = conv_memo_get(2, G, C, t, u, A, key, &found);
    if (found) { uint64_t v; wordmap_get(&K.conv_memo, key, 6, &v); if (v == 1 || v == 2) return memo; if (v == 3) return CV_UNRESOLVED; }
    conv_memo_set(key, CV_UNRESOLVED);
    ConvStatus out = CV_UNRESOLVED;
    EvalResult *rA; const char *reason;
    if (observe(C, A, &rA, &reason) != CK_VALID) goto done;
    if (rA->cls == R_INTRODUCTION) {
        Head h; open_ref(rA->ref, &h);
        switch (h.tag) {
        case T_PI: {
            TermVarId x = conv_var(t, u, rA->ref, 0, h.f[0].id);
            RefId Bx = apply_term_binder(rA->ref, 0, 1, ref_var(x));
            out = conv_term_clause(extend_term(G, x, h.f[0].id), C, mk_app(t, ref_var(x)), mk_app(u, ref_var(x)), Bx);
            break;
        }
        case T_SIGMA: {
            out = conv_term_clause(G, C, mk_fst(t), mk_fst(u), h.f[0].id);
            if (out == CV_EQUAL) out = conv_term_clause(G, C, mk_snd(t), mk_snd(u), apply_term_binder(rA->ref, 0, 1, mk_fst(t)));
            break;
        }
        case T_PATH: {
            DimVarId j = conv_dim(t, u, 0);
            DimOpen o = resolve_dim_binder(rA->ref, 0, 0);
            RefId Bj = reindex_dim(o.body, o.j, iv_var(j));
            out = conv_term_clause(extend_dim(G, j), C, mk_papp(o.j, o.body, h.f[1].id, h.f[2].id, t, iv_var(j)), mk_papp(o.j, o.body, h.f[1].id, h.f[2].id, u, iv_var(j)), Bj);
            break;
        }
        case T_GLUE_TYPE: {
            /* non-collapsed Glue (C does not entail alpha): Glue eta */
            RefId Ab = h.f[0].id, T = h.f[2].id, e = h.f[3].id; FaceId alpha = h.f[1].id;
            out = conv_term_clause(G, C, mk_unglue(Ab, alpha, T, e, t), mk_unglue(Ab, alpha, T, e, u), Ab);
            FaceId Ca = fc_meet(C, alpha);
            if (out == CV_EQUAL && !fc_is_false(Ca)) {
                FaceId *cs; size_t nc = clauses_of(Ca, &cs);
                for (size_t c = 0; c < nc && out == CV_EQUAL; c++) out = conv_term_clause(G, cs[c], t, u, T);
                free(cs);
            }
            break;
        }
        case T_UNIVERSE: out = conv_type_clause(G, C, t, u); break;
        default: out = CV_UNEQUAL; break;
        }
        head_free(&h);
    } else if (rA->cls == R_NEUTRAL) {
        /* neutral expected type: observe the terms and compare their neutral structures */
        EvalResult *rt, *ru;
        if (observe_both(C, t, u, &rt, &ru) != CV_EQUAL) goto done;
        if (rt->ref == ru->ref) out = CV_EQUAL;
        else if (rt->cls == R_NEUTRAL && ru->cls == R_NEUTRAL) out = spine(G, C, rt->ref, ru->ref);
        else if (rt->cls == R_SYSTEM || ru->cls == R_SYSTEM) out = CV_UNRESOLVED;
        else out = CV_UNEQUAL;
    } else out = CV_UNRESOLVED;                 /* a system type under a single clause is not a covered type */
done:
    if (out == CV_UNRESOLVED) conv_memo_clear_running(key); else conv_memo_set(key, out);
    return out;
}

/* structural comparison of neutral spines; n1, n2 are neutral result references */
static ConvStatus spine(ContextId G, FaceId C, RefId n1, RefId n2) {
    if (n1 == n2) return CV_EQUAL;
    if (!budget_ok()) return CV_UNRESOLVED;
    G = under(G, C);
    if (ref_is_var(n1) || ref_is_var(n2)) return (ref_is_var(n1) && ref_is_var(n2) && ref_var_id(n1) == ref_var_id(n2)) ? CV_EQUAL : CV_UNEQUAL;
    Head a, b; open_ref(n1, &a); open_ref(n2, &b);
    ConvStatus out = CV_UNEQUAL;
    if (a.tag != b.tag) goto done;
    switch (a.tag) {
    case T_APP: {
        EvalResult *fa, *fb;
        if (observe_both(C, a.f[0].id, b.f[0].id, &fa, &fb) != CV_EQUAL) { out = CV_UNRESOLVED; break; }
        if (fa->cls != R_NEUTRAL || fb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, fa->ref, fb->ref);
        if (out != CV_EQUAL) break;
        RefId Tf, P; const char *reason;
        if (infer_clause(G, C, a.f[0].id, &Tf, &reason) != CK_VALID || observe_head(C, Tf, T_PI, &P, &reason) != CK_VALID) { out = CV_UNRESOLVED; break; }
        Head hp; open_ref(P, &hp); RefId dom = hp.f[0].id; head_free(&hp);
        out = conv_term_clause(G, C, a.f[1].id, b.f[1].id, dom);
        break;
    }
    case T_FST: case T_SND: {
        EvalResult *pa, *pb;
        if (observe_both(C, a.f[0].id, b.f[0].id, &pa, &pb) != CV_EQUAL || pa->cls != R_NEUTRAL || pb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, pa->ref, pb->ref);
        break;
    }
    case T_PAPP: {
        if (!iv_equal_under(C, a.f[4].id, b.f[4].id)) { out = CV_UNEQUAL; break; }
        EvalResult *pa, *pb;
        if (observe_both(C, a.f[3].id, b.f[3].id, &pa, &pb) != CV_EQUAL || pa->cls != R_NEUTRAL || pb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, pa->ref, pb->ref);
        break;
    }
    case T_UNGLUE: {
        if (!fc_equal_under(C, a.f[1].id, b.f[1].id)) { out = CV_UNEQUAL; break; }
        out = conv_type_clause(G, C, a.f[0].id, b.f[0].id);
        FaceId Ca = fc_meet(C, a.f[1].id);
        if (out == CV_EQUAL && !fc_is_false(Ca)) {
            FaceId *cs; size_t nc = clauses_of(Ca, &cs);
            for (size_t c = 0; c < nc && out == CV_EQUAL; c++) {
                out = conv_type_clause(G, cs[c], a.f[2].id, b.f[2].id);
                if (out == CV_EQUAL) out = conv_term_clause(G, cs[c], a.f[3].id, b.f[3].id, mk_equiv(a.f[2].id, a.f[0].id));
            }
            free(cs);
        }
        if (out != CV_EQUAL) break;
        EvalResult *va, *vb;
        if (observe_both(C, a.f[4].id, b.f[4].id, &va, &vb) != CV_EQUAL || va->cls != R_NEUTRAL || vb->cls != R_NEUTRAL) { out = CV_UNRESOLVED; break; }
        out = spine(G, C, va->ref, vb->ref);
        break;
    }
    case T_COMP: {
        if (!fc_equal_under(C, a.f[1].id, b.f[1].id)) { out = CV_UNEQUAL; break; }
        DimVarId j = conv_dim(n1, n2, 0);
        RefId A1 = apply_dim_binder(n1, 0, 0, iv_var(j)), A2 = apply_dim_binder(n2, 0, 0, iv_var(j));
        ContextId Gj = extend_dim(G, j);
        out = conv_type_clause(Gj, C, A1, A2);
        if (out == CV_EQUAL) out = conv_term_clause(G, C, a.f[3].id, b.f[3].id, reindex_dim(A1, j, iv_zero()));
        FaceId Cp = fc_meet(C, a.f[1].id);
        if (out == CV_EQUAL && !fc_is_false(Cp)) {
            RefId u1 = apply_dim_binder(n1, 0, 2, iv_var(j)), u2 = apply_dim_binder(n2, 0, 2, iv_var(j));
            FaceId *cs; size_t nc = clauses_of(Cp, &cs);
            for (size_t c = 0; c < nc && out == CV_EQUAL; c++) out = conv_term_clause(Gj, cs[c], u1, u2, A1);
            free(cs);
        }
        break;
    }
    case T_GLOBAL: {
        if (a.payload != b.payload) { out = CV_UNEQUAL; break; }
        ContextId Gs = origin_context(a.origin);
        out = CV_EQUAL;
        size_t n = context_size(Gs);
        for (size_t k = 0; k < n && out == CV_EQUAL; k++) {
            CtxDecl d = context_decl(Gs, k);
            if (d.sort == S_DIM) { if (!iv_equal_under(C, map_dim_image(a.map, d.id), map_dim_image(b.map, d.id))) out = CV_UNEQUAL; }
            else out = conv_term_clause(G, C, map_term_image(a.map, d.id), map_term_image(b.map, d.id), reindex(d.type, a.map));
        }
        break;
    }
    default: out = CV_UNEQUAL; break;
    }
done:
    head_free(&a); head_free(&b);
    return out;
}

ConvStatus convert_type(ContextId G, FaceId chi, RefId A, RefId B) {
    const char *why;
    if (scope_ok(G, chi, A, &why) != CK_VALID || scope_ok(G, chi, B, &why) != CK_VALID) return CV_UNRESOLVED;
    ENTER();
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    ConvStatus out = CV_EQUAL;
    for (size_t c = 0; c < nc; c++) { ConvStatus r = conv_type_clause(G, cs[c], A, B); out = and3(out, r); if (out == CV_UNEQUAL) break; }
    free(cs);
    LEAVE();
    return out;
}
ConvStatus convert_term(ContextId G, FaceId chi, RefId t, RefId u, RefId A) {
    const char *why;
    if (scope_ok(G, chi, t, &why) != CK_VALID || scope_ok(G, chi, u, &why) != CK_VALID || scope_ok(G, chi, A, &why) != CK_VALID) return CV_UNRESOLVED;
    ENTER();
    FaceId *cs; size_t nc = clauses_of(chi, &cs);
    ConvStatus out = CV_EQUAL;
    for (size_t c = 0; c < nc; c++) { ConvStatus r = conv_term_clause(G, cs[c], t, u, A); out = and3(out, r); if (out == CV_UNEQUAL) break; }
    free(cs);
    LEAVE();
    return out;
}

/* A declared symbol is validated once: its declared type is a type over its
 * parameters, and its registered body (if any) checks against that type.
 * While a symbol's own body is being validated, its recursive occurrences
 * use the declared type: the signature's declaration is the assumption the
 * body is checked under; this does not prove termination. */
static CheckStatus validate_symbol(SymbolId s, const char **reason) {
    if (!sym_memo_init) { wordmap_init(&sym_memo); sym_memo_init = true; }
    uint64_t key[1] = { s }, v;
    if (wordmap_get(&sym_memo, key, 1, &v) && v != 4) { if (v == 1 || v == 3) return CK_VALID; *reason = "symbol previously found invalid"; return CK_INVALID; }
    RefId type = global_type(s);
    if (!type) { *reason = "symbol without a declared type"; wordmap_put(&sym_memo, key, 1, 2); return CK_INVALID; }
    wordmap_put(&sym_memo, key, 1, 3);                 /* running: recursive uses see the declaration */
    OriginId o = ref_origin(global_ref(s));
    ContextId Gs = origin_context(o);
    CheckStatus st = check_context(Gs, reason);
    if (st == CK_VALID) { uint64_t l; st = level_of(Gs, fc_true(), type, &l, reason); }
    RefId body = global_body(s);
    if (st == CK_VALID && body) st = check(Gs, fc_true(), body, type, reason);
    if (st == CK_UNRESOLVED) { wordmap_put(&sym_memo, key, 1, 4); return st; }   /* 4: no verdict */
    wordmap_put(&sym_memo, key, 1, st == CK_VALID ? 1 : 2);
    return st;
}

EvalResult *observe_checked(ContextId G, RefId t, WhnfStatus *status, const char **reason) {
    CheckStatus st = check_context(G, reason);
    if (st == CK_VALID) { Inference I = infer(G, context_assumption(G), t); st = I.st; if (st != CK_VALID) *reason = I.reason; }
    if (st == CK_INVALID) { if (status) *status = W_INVALID; return NULL; }
    if (st == CK_UNRESOLVED) { if (status) *status = W_STUCK; return NULL; }
    return whnf(t, context_assumption(G), status);
}

CheckStatus check_signature(const char **reason) {
    size_t n = global_count();
    for (SymbolId s = 1; s <= n; s++) { CheckStatus st = validate_symbol(s, reason); if (st != CK_VALID) return st; }
    return CK_VALID;
}

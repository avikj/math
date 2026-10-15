#include "lib.h"

void lib_free(void) { templates_free(); }
size_t lib_template_count(void) { return interner_count(&M.tnodes); }

IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j) {
    IntervalId vj = iv_var(j);
    return iv_join(iv_meet(r, iv_negate(vj)), iv_meet(s, vj));
}

/* ------------------------------------------------------------------ */
/* capture adapters                                                      */

ScopeId capture_dim1(DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard) {
    CaptureDecl d[1] = { { S_DIM, j, 0, LEVEL_NONE, fc_true() } };
    Val b = { VS_REF, body };
    return capture_scope(1, d, b, type, level, guard);
}
ScopeId capture_dim1_face(DimVarId j, FaceId body) {
    CaptureDecl d[1] = { { S_DIM, j, 0, LEVEL_NONE, fc_true() } };
    Val b = { VS_FACE, body };
    return capture_scope(1, d, b, 0, LEVEL_NONE, fc_true());
}
ScopeId capture_dim2(DimVarId i, DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard) {
    CaptureDecl d[2] = { { S_DIM, i, 0, LEVEL_NONE, fc_true() }, { S_DIM, j, 0, LEVEL_NONE, fc_true() } };
    Val b = { VS_REF, body };
    return capture_scope(2, d, b, type, level, guard);
}
ScopeId capture_dim_term(DimVarId j, TermVarId x, RefId xtype, uint64_t xlevel, RefId body, RefId type, uint64_t level, FaceId guard) {
    CaptureDecl d[2] = { { S_DIM, j, 0, LEVEL_NONE, fc_true() }, { S_TERM, x, xtype, xlevel, term_var_required(x) } };
    Val b = { VS_REF, body };
    return capture_scope(2, d, b, type, level, guard);
}
ScopeId capture_term2(TermVarId x, RefId xtype, uint64_t xlevel, TermVarId e, RefId etype, uint64_t elevel, RefId body, RefId type, uint64_t level, FaceId guard) {
    CaptureDecl d[2] = { { S_TERM, x, xtype, xlevel, term_var_required(x) }, { S_TERM, e, etype, elevel, term_var_required(e) } };
    Val b = { VS_REF, body };
    return capture_scope(2, d, b, type, level, guard);
}

/* ------------------------------------------------------------------ */
/* §52 programs                                                          */

static TVal VL(uint64_t n) { TVal v = { PS_LEVEL, n }; return v; }
static TVal VR(RefId r) { TVal v = { PS_REF, r }; return v; }
static TVal VI(IntervalId r) { TVal v = { PS_INTERVAL, r }; return v; }
static TVal VF(FaceId f) { TVal v = { PS_FACE, f }; return v; }
static TVal VS(ScopeId s) { TVal v = { PS_SCOPE, s }; return v; }
#define CALLT(def, ...) ({ TVal _a[] = { __VA_ARGS__ }; template_call(def, sizeof _a / sizeof _a[0], _a).id; })

RefId mk_path_const(uint64_t l, RefId A, RefId lft, RefId r) { return CALLT(TD_PATHCONST, VL(l), VR(A), VR(lft), VR(r)); }
RefId mk_refl(uint64_t l, RefId A, RefId a) { return CALLT(TD_REFL, VL(l), VR(A), VR(a)); }
RefId mk_papp_const(uint64_t l, RefId A, RefId lft, RefId r, RefId p, IntervalId s) { return CALLT(TD_PAPPCONST, VL(l), VR(A), VR(lft), VR(r), VR(p), VI(s)); }
RefId mk_path_rev(uint64_t l, RefId A, RefId lft, RefId r, RefId p) { return CALLT(TD_REVERSE, VL(l), VR(A), VR(lft), VR(r), VR(p)); }
RefId mk_path_concat(uint64_t l, RefId A, RefId x, RefId y, RefId z, RefId p, RefId q) { return CALLT(TD_CONCAT, VL(l), VR(A), VR(x), VR(y), VR(z), VR(p), VR(q)); }
RefId mk_fun(uint64_t l, uint64_t m, RefId X, RefId Y) { return CALLT(TD_FUN, VL(l), VL(m), VR(X), VR(Y)); }
RefId mk_contr(uint64_t l, RefId X) { return CALLT(TD_CONTR, VL(l), VR(X)); }
RefId mk_fib(uint64_t l, uint64_t m, RefId X, RefId Y, RefId f, RefId y) { return CALLT(TD_FIB, VL(l), VL(m), VR(X), VR(Y), VR(f), VR(y)); }
RefId mk_equiv(uint64_t l, uint64_t m, RefId X, RefId Y) { return CALLT(TD_EQUIV, VL(l), VL(m), VR(X), VR(Y)); }
RefId mk_id_fun(uint64_t l, RefId X) { return CALLT(TD_IDFUN, VL(l), VR(X)); }
RefId mk_id_equiv(uint64_t l, RefId X) { return CALLT(TD_IDEQUIV, VL(l), VR(X)); }
RefId equiv_map(uint64_t l, uint64_t m, RefId X, RefId Y, RefId e) { return CALLT(TD_EQUIVMAP, VL(l), VL(m), VR(X), VR(Y), VR(e)); }
RefId equiv_contr(uint64_t l, uint64_t m, RefId X, RefId Y, RefId e, RefId y) { return CALLT(TD_EQUIVCONTR, VL(l), VL(m), VR(X), VR(Y), VR(e), VR(y)); }
RefId mk_fill(uint64_t l, ScopeId A, FaceId phi, ScopeId u, RefId cap, IntervalId r) { return CALLT(TD_FILL, VL(l), VS(A), VF(phi), VS(u), VR(cap), VI(r)); }
RefId mk_hcomp(uint64_t l, RefId X, FaceId phi, ScopeId u, RefId cap) { return CALLT(TD_HCOMP, VL(l), VR(X), VF(phi), VS(u), VR(cap)); }
RefId mk_coe(uint64_t l, ScopeId A, RefId cap) { return CALLT(TD_COE, VL(l), VS(A), VR(cap)); }
RefId mk_extend_contr(uint64_t l, RefId X, RefId c, RefId k, FaceId theta, RefId v) { return CALLT(TD_EXTENDCONTR, VL(l), VR(X), VR(c), VR(k), VF(theta), VR(v)); }
RefId mk_line_equiv(uint64_t l, ScopeId X) { return CALLT(TD_LINEEQUIV, VL(l), VS(X)); }
RefId mk_ua(uint64_t l, RefId X, RefId Y, RefId e) { return CALLT(TD_UA, VL(l), VR(X), VR(Y), VR(e)); }
RefId mk_down(uint64_t l, uint64_t lA, RefId A, RefId t, ScopeId D, RefId x, RefId e, RefId z) { return CALLT(TD_DOWN, VL(l), VL(lA), VR(A), VR(t), VS(D), VR(x), VR(e), VR(z)); }

RefId mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap) {
    return mk_coe(l, capture_dim1(i, A_i, mk_universe(l), level_succ(l), template_kappa()), cap);
}
RefId mk_fill_at(uint64_t l, DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId cap, IntervalId r) {
    ScopeId A = capture_dim1(i, A_i, mk_universe(l), level_succ(l), template_kappa());
    ScopeId u = capture_dim1(i, u_i, A_i, l, fc_meet(template_kappa(), phi));
    return mk_fill(l, A, phi, u, cap, r);
}
RefId mk_hcomp_at(uint64_t l, DimVarId j, RefId X, FaceId phi, RefId u_j, RefId cap) {
    ScopeId u = capture_dim1(j, u_j, X, l, fc_meet(template_kappa(), phi));
    return mk_hcomp(l, X, phi, u, cap);
}

/* ------------------------------------------------------------------ */
/* §54: capture the retained components of an exposed head and select the one fixed clause */

/* §59.1: a family without its required level annotation is not admitted
 * core syntax; no clause is instantiated for it (the evaluator reports the
 * demand as invalid) and no scope is manufactured without its declared type */
static RefId U_of(uint64_t l) { return mk_universe(l); }
RefId comp_clause(DimVarId j, RefId fam, FaceId phi, RefId tube_j, RefId cap, FaceId eta) {
    FaceId saved = template_kappa();
    template_set_kappa(eta);
    Head h; open_ref(fam, &h);
    RefId out = 0;
    if ((h.tag == T_PI || h.tag == T_SIGMA || h.tag == T_PATH || h.tag == T_GLUE_TYPE) && (h.levels == LEVELS_NONE || levels_first(h.levels) == LEVEL_NONE || ((h.tag == T_PI || h.tag == T_SIGMA) && levels_second(h.levels) == LEVEL_NONE))) {
        head_free(&h); template_set_kappa(saved); return 0;
    }
    FaceId tube_guard = fc_meet(eta, phi);
    switch (h.tag) {
    case T_PI: case T_SIGMA: {
        uint64_t m = levels_first(h.levels), n = levels_second(h.levels);
        RefId domain = h.f[0].id;
        TermOpen o = resolve_term_binder(fam, 0, 1);                  /* resolved once: (x, D_j, codomain) */
        ScopeId D = capture_dim1(j, domain, U_of(m), level_succ(m), eta);
        ScopeId E = capture_dim_term(j, o.x, o.type, m, o.body, U_of(n), level_succ(n), eta);
        ScopeId u = capture_dim1(j, tube_j, fam, level_max(m, n), tube_guard);
        TVal a[7] = { VL(m), VL(n), VS(D), VS(E), VF(phi), VS(u), VR(cap) };
        out = template_call(h.tag == T_PI ? TD_PICOMP : TD_SIGMACOMP, 7, a).id;
        break;
    }
    case T_PATH: {
        uint64_t n = levels_first(h.levels);
        DimOpen Bk = resolve_dim_binder(fam, 0, 0);                   /* (k, B(j,k)) */
        ScopeId B = capture_dim2(j, Bk.j, Bk.body, U_of(n), level_succ(n), eta);
        ScopeId left = capture_dim1(j, h.f[1].id, reindex_dim(Bk.body, Bk.j, iv_zero()), n, eta);
        ScopeId right = capture_dim1(j, h.f[2].id, reindex_dim(Bk.body, Bk.j, iv_one()), n, eta);
        ScopeId u = capture_dim1(j, tube_j, fam, n, tube_guard);
        TVal a[7] = { VL(n), VS(B), VS(left), VS(right), VF(phi), VS(u), VR(cap) };
        out = template_call(TD_PATHCOMP, 7, a).id;
        break;
    }
    case T_GLUE_TYPE: {
        uint64_t n = levels_first(h.levels);
        RefId A_j = h.f[0].id, T_j = h.f[2].id, e_j = h.f[3].id; FaceId alpha_j = h.f[1].id;
        ScopeId A = capture_dim1(j, A_j, U_of(n), level_succ(n), eta);
        ScopeId alpha = capture_dim1_face(j, alpha_j);
        ScopeId T = capture_dim1(j, T_j, U_of(n), level_succ(n), fc_meet(eta, alpha_j));
        ScopeId e = capture_dim1(j, e_j, mk_equiv(n, n, T_j, A_j), n, fc_meet(eta, alpha_j));
        ScopeId u = capture_dim1(j, tube_j, fam, n, tube_guard);
        TVal a[8] = { VL(n), VS(A), VS(alpha), VS(T), VS(e), VF(phi), VS(u), VR(cap) };
        out = template_call(TD_GLUECOMP, 8, a).id;
        break;
    }
    case T_UNIVERSE: {
        uint64_t l = h.payload;
        ScopeId types = capture_dim1(j, tube_j, fam, level_succ(l), tube_guard);
        TVal a[4] = { VL(l), VF(phi), VS(types), VR(cap) };
        out = template_call(TD_UNIVERSECOMP, 4, a).id;
        break;
    }
    default: break;
    }
    head_free(&h);
    template_set_kappa(saved);
    return out;
}

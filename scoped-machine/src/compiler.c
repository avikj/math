/* compiler.c — identities as ordinary values (compiler.h). The emitters of
 * Maps, the singleton, Diagram, zero and node follow the §96 witness. */
#include "compiler.h"

/* the telescope of a closed construction; its binders are keyed by
 * (construction, levels, ordinal), so building it again shares its open
 * intermediate terms as well as its reference */
typedef struct { uint64_t k[5], n; size_t m; TermVarId x[8]; RefId A[8]; uint64_t l[8]; } Tele;
static TermVarId var(Tele *T, RefId A) {
    KeyWord k[7] = { { KW_CONST, 8100 }, { KW_CONST, T->k[0] }, { KW_CONST, T->k[1] }, { KW_CONST, T->k[2] }, { KW_CONST, T->k[3] }, { KW_CONST, T->k[4] }, { KW_CONST, T->n++ } };
    return fresh_term_keyed(k, 7, A);
}
static DimVarId dim(Tele *T) {
    KeyWord k[7] = { { KW_CONST, 8101 }, { KW_CONST, T->k[0] }, { KW_CONST, T->k[1] }, { KW_CONST, T->k[2] }, { KW_CONST, T->k[3] }, { KW_CONST, T->k[4] }, { KW_CONST, T->n++ } };
    return fresh_dim_keyed(k, 7);
}
static RefId P(Tele *T, RefId A, uint64_t l) { TermVarId x = var(T, A); T->x[T->m] = x; T->A[T->m] = A; T->l[T->m] = l; T->m++; return ref_var(x); }
static RefId close(const Tele *T, RefId body) { for (size_t q = T->m; q-- > 0; ) body = mk_lam_lv(T->l[q], T->x[q], T->A[q], body); return body; }

static RefId U(uint64_t l) { return mk_universe(l); }
static RefId app2(RefId f, RefId x, RefId y) { return mk_app(mk_app(f, x), y); }
static RefId app3(RefId f, RefId x, RefId y, RefId z) { return mk_app(app2(f, x, y), z); }
static RefId tail(RefId S, RefId x) { return apply_term_binder(S, 0, 1, x); }
static RefId pair(uint64_t l, RefId S, RefId x, RefId y) { return mk_pair_at_lv(l, S, x, y); }
static RefId path(uint64_t l, RefId A, RefId x, RefId y) { return mk_path_const(l, A, x, y); }
static RefId papp(uint64_t l, RefId A, RefId x, RefId y, RefId p, IntervalId s) { return mk_papp_const(l, A, x, y, p, s); }
static RefId cat(uint64_t l, RefId A, RefId x, RefId y, RefId z, RefId p, RefId q) { return mk_path_concat(l, A, x, y, z, p, q); }
static RefId rev(uint64_t l, RefId A, RefId x, RefId y, RefId p) { return mk_path_rev(l, A, x, y, p); }
static RefId refl(uint64_t l, RefId A, RefId a) { return mk_refl(l, A, a); }

RefId maps_c(RefId M) { return mk_fst(M); }
RefId maps_d(RefId M) { return mk_fst(mk_snd(M)); }
RefId maps_h(RefId M) { return mk_fst(mk_snd(mk_snd(M))); }
RefId maps_k(RefId M) { return mk_snd(mk_snd(mk_snd(M))); }
RefId res_T(RefId R) { return mk_fst(R); }
RefId res_X(RefId R) { return mk_fst(mk_snd(R)); }
RefId res_M(RefId R) { return mk_snd(mk_snd(R)); }
RefId dg_C(RefId D) { return mk_fst(D); }
RefId dg_R(RefId D, RefId y) { return mk_app(mk_fst(mk_snd(D)), y); }
RefId dg_M(RefId D, RefId y) { return mk_app(mk_snd(mk_snd(D)), y); }
RefId maps_apply(RefId M, int dir, RefId a) { return mk_app(dir ? maps_d(M) : maps_c(M), a); }

#define APPN(f, ...) appn((f), sizeof((RefId[]){ __VA_ARGS__ }) / sizeof(RefId), (RefId[]){ __VA_ARGS__ })
static RefId appn(RefId f, size_t n, const RefId *a) { for (size_t q = 0; q < n; q++) f = mk_app(f, a[q]); return f; }

/* Every construction below is one closed term (keyed binders: rebuilding
 * gives the same reference), and every use of one inside another is an
 * application, so its typing is one judgment shared by all uses. */

/* ---------------- Maps (§83.1) ---------------- */
static RefId maps_sigma(Tele *T, uint64_t a, uint64_t b, RefId A, RefId B) {
    uint64_t m = level_max(a, b);
    RefId F = mk_fun(a, b, A, B), G = mk_fun(b, a, B, A);
    TermVarId f = var(T, F), g = var(T, G), x = var(T, A), y = var(T, B);
    RefId H = mk_pi_lv(a, a, x, A, path(a, A, mk_app(ref_var(g), mk_app(ref_var(f), ref_var(x))), ref_var(x)));
    RefId K = mk_pi_lv(b, b, y, B, path(b, B, mk_app(ref_var(f), mk_app(ref_var(g), ref_var(y))), ref_var(y)));
    TermVarId h = var(T, H);
    return mk_sigma_lv(m, m, f, F, mk_sigma_lv(m, m, g, G, mk_sigma_lv(a, b, h, H, K)));
}
static RefId Maps(uint64_t a, uint64_t b) {
    Tele T_ = { { 40, a, b, 0, 0 } }, *T = &T_;
    RefId X = P(T, U(a), level_succ(a)), Y = P(T, U(b), level_succ(b));
    RefId out = close(T, maps_sigma(T, a, b, X, Y));
    return out;
}
RefId maps_type(uint64_t a, uint64_t b, RefId X, RefId Y) { return app2(Maps(a, b), X, Y); }
static RefId Pack(uint64_t a, uint64_t b) {
    Tele T_ = { { 41, a, b, 0, 0 } }, *T = &T_;
    uint64_t m = level_max(a, b);
    RefId X = P(T, U(a), level_succ(a)), Y = P(T, U(b), level_succ(b));
    RefId f = P(T, mk_fun(a, b, X, Y), m), g = P(T, mk_fun(b, a, Y, X), m);
    TermVarId x = var(T, X), y = var(T, Y);
    RefId h = P(T, mk_pi_lv(a, a, x, X, path(a, X, mk_app(g, mk_app(f, ref_var(x))), ref_var(x))), a);
    RefId k = P(T, mk_pi_lv(b, b, y, Y, path(b, Y, mk_app(f, mk_app(g, ref_var(y))), ref_var(y))), b);
    RefId M = maps_sigma(T, a, b, X, Y), M1 = tail(M, f), M2 = tail(M1, g);
    RefId out = close(T, pair(m, M, f, pair(m, M1, g, pair(m, M2, h, k))));
    return out;
}
static RefId maps_pack(uint64_t a, uint64_t b, RefId A, RefId B, RefId f, RefId g, RefId h, RefId k) { return APPN(Pack(a, b), A, B, f, g, h, k); }
static RefId ap(Tele *T, uint64_t a, RefId A, RefId x, RefId y, RefId f, RefId p) {
    DimVarId i = dim(T);
    return mk_plam(i, mk_app(f, papp(a, A, x, y, p, iv_var(i))));
}
static RefId Id(uint64_t a) {
    Tele T_ = { { 42, a, 0, 0, 0 } }, *T = &T_;
    RefId X = P(T, U(a), level_succ(a));
    TermVarId x = var(T, X); RefId id = mk_id_fun(a, X), h = mk_lam_lv(a, x, X, refl(a, X, ref_var(x)));
    RefId out = close(T, maps_pack(a, a, X, X, id, id, h, h));
    return out;
}
static RefId maps_id(uint64_t a, RefId A) { return mk_app(Id(a), A); }
/* E : A ↔ B, F : B ↔ C */
static RefId Comp(uint64_t a, uint64_t b, uint64_t c) {
    Tele T_ = { { 43, a, b, c, 0 } }, *T = &T_;
    RefId A = P(T, U(a), level_succ(a)), B = P(T, U(b), level_succ(b)), C = P(T, U(c), level_succ(c));
    RefId E = P(T, maps_type(a, b, A, B), level_max(a, b)), F = P(T, maps_type(b, c, B, C), level_max(b, c));
    RefId f = maps_c(E), g = maps_d(E), h = maps_h(E), k = maps_k(E);
    RefId u = maps_c(F), v = maps_d(F), H = maps_h(F), K = maps_k(F);
    TermVarId x = var(T, A), z = var(T, C); RefId xv = ref_var(x), zv = ref_var(z);
    RefId fx = mk_app(f, xv), vz = mk_app(v, zv);
    RefId forward = mk_lam_lv(a, x, A, mk_app(u, fx));
    RefId reverse = mk_lam_lv(c, z, C, mk_app(g, vz));
    RefId vufx = mk_app(v, mk_app(u, fx)), gvufx = mk_app(g, vufx), gfx = mk_app(g, fx);
    RefId hh = mk_lam_lv(a, x, A, cat(a, A, gvufx, gfx, xv, ap(T, b, B, vufx, fx, g, mk_app(H, fx)), mk_app(h, xv)));
    RefId fgvz = mk_app(f, mk_app(g, vz)), ufgvz = mk_app(u, fgvz), uvz = mk_app(u, vz);
    RefId kk = mk_lam_lv(c, z, C, cat(c, C, ufgvz, uvz, zv, ap(T, b, B, fgvz, vz, u, mk_app(k, vz)), mk_app(K, zv)));
    RefId out = close(T, maps_pack(a, c, A, C, forward, reverse, hh, kk));
    return out;
}
static RefId maps_comp(uint64_t a, uint64_t b, uint64_t c, RefId A, RefId B, RefId C, RefId E, RefId F) { return APPN(Comp(a, b, c), A, B, C, E, F); }
static RefId Inv(uint64_t a, uint64_t b) {
    Tele T_ = { { 44, a, b, 0, 0 } }, *T = &T_;
    RefId A = P(T, U(a), level_succ(a)), B = P(T, U(b), level_succ(b)), E = P(T, maps_type(a, b, A, B), level_max(a, b));
    RefId out = close(T, maps_pack(b, a, B, A, maps_d(E), maps_c(E), maps_k(E), maps_h(E)));
    return out;
}
static RefId maps_inv(uint64_t a, uint64_t b, RefId A, RefId B, RefId E) { return APPN(Inv(a, b), A, B, E); }

/* ---------------- the dependent singleton (§83.2) ---------------- */
/* λ A t D. Maps(Σ x. Σ (e : t = x). D x e, D t refl) */
static RefId Sing(uint64_t a, uint64_t r) {
    Tele T_ = { { 45, a, r, 0, 0 } }, *T = &T_;
    uint64_t s = level_max(a, r);
    RefId A = P(T, U(a), level_succ(a)), t = P(T, A, a);
    TermVarId x0 = var(T, A); RefId Ex0 = path(a, A, t, ref_var(x0)); TermVarId e0 = var(T, Ex0);
    RefId Df = P(T, mk_pi_lv(a, level_max(a, level_succ(r)), x0, A, mk_pi_lv(a, level_succ(r), e0, Ex0, U(r))), level_max(a, level_succ(r)));
    TermVarId x = var(T, A); RefId Ex = path(a, A, t, ref_var(x)); TermVarId e = var(T, Ex);
    RefId D = app2(Df, ref_var(x), ref_var(e));
    RefId S = mk_sigma_lv(a, s, x, A, mk_sigma_lv(a, r, e, Ex, D));
    ScopeId DS = capture_term2(x, A, a, e, Ex, a, D, U(r), level_succ(r), fc_true());
    RefId rf = refl(a, A, t), Z = app2(Df, t, rf);
    TermVarId w = var(T, S), z = var(T, Z); RefId wv = ref_var(w), zv = ref_var(z);
    RefId wx = mk_fst(wv), we = mk_fst(mk_snd(wv)), wz = mk_snd(mk_snd(wv));
    RefId down = mk_lam_lv(s, w, S, mk_down(r, a, A, t, DS, wx, we, wz));
    RefId up = mk_lam_lv(r, z, Z, pair(s, S, t, pair(s, tail(S, t), rf, zv)));
    DimVarId i = dim(T), j = dim(T), q = dim(T);
    RefId xi = papp(a, A, t, wx, we, iv_var(i));
    RefId ei = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_var(i), iv_var(j))));
    RefId xq = papp(a, A, t, wx, we, iv_negate(iv_var(q)));
    RefId eq = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_negate(iv_var(q)), iv_var(j))));
    RefId Dq = app2(Df, xq, eq), empty = mk_system(0, NULL, NULL);
    RefId zi = mk_fill_at(r, q, Dq, fc_false(), empty, wz, iv_negate(iv_var(i)));
    RefId h = mk_lam_lv(s, w, S, mk_plam(i, pair(s, S, xi, pair(s, tail(S, xi), ei, zi))));
    RefId k = mk_lam_lv(r, z, Z, mk_plam(i, mk_fill_at(r, q, Z, fc_false(), empty, zv, iv_negate(iv_var(i)))));
    RefId out = close(T, maps_pack(s, r, S, Z, down, up, h, k));
    return out;
}

/* ---------------- presentations and diagrams (§83.3, §96.2) ---------------- */
RefId res_type(uint64_t z, uint64_t r) {
    Tele T_ = { { 46, z, r, 0, 0 } }, *T = &T_;
    TermVarId vT = var(T, U(z)), X = var(T, U(r));
    RefId out = mk_sigma_lv(level_succ(z), level_max(level_succ(r), z), vT, U(z), mk_sigma_lv(level_succ(r), level_max(r, z), X, U(r), maps_type(r, z, ref_var(X), ref_var(vT))));
    return out;
}
static RefId RPack(uint64_t z, uint64_t r) {
    Tele T_ = { { 47, z, r, 0, 0 } }, *T = &T_;
    RefId Tz = P(T, U(z), level_succ(z)), X = P(T, U(r), level_succ(r)), M = P(T, maps_type(r, z, X, Tz), level_max(r, z));
    RefId RT = res_type(z, r);
    RefId out = close(T, pair(level_max(level_succ(z), level_succ(r)), RT, Tz, pair(level_max(level_succ(r), z), tail(RT, Tz), X, M)));
    return out;
}
static RefId res_pack(uint64_t z, uint64_t r, RefId T, RefId X, RefId M) { return APPN(RPack(z, r), T, X, M); }
static RefId diagram_sigma(Tele *T, uint64_t b, uint64_t r, RefId B) {
    uint64_t rl = level_max(b, level_succ(r)), ml = level_max(b, r);
    TermVarId c = var(T, B), y = var(T, B);
    RefId RT = mk_pi_lv(b, level_succ(r), y, B, U(r)); TermVarId R = var(T, RT);
    RefId M = mk_pi_lv(b, ml, y, B, maps_type(r, b, mk_app(ref_var(R), ref_var(y)), path(b, B, ref_var(c), ref_var(y))));
    return mk_sigma_lv(b, rl, c, B, mk_sigma_lv(rl, ml, R, RT, M));
}
static RefId DT(uint64_t b, uint64_t r) {
    Tele T_ = { { 48, b, r, 0, 0 } }, *T = &T_;
    RefId B = P(T, U(b), level_succ(b));
    RefId out = close(T, diagram_sigma(T, b, r, B));
    return out;
}
RefId diagram_type(uint64_t b, uint64_t r, RefId B) { return mk_app(DT(b, r), B); }
static RefId DPack(uint64_t b, uint64_t r) {
    Tele T_ = { { 49, b, r, 0, 0 } }, *T = &T_;
    uint64_t dl = level_max(b, level_succ(r)), ml = level_max(b, r);
    RefId B = P(T, U(b), level_succ(b)), c = P(T, B, b);
    TermVarId y0 = var(T, B); RefId R = P(T, mk_pi_lv(b, level_succ(r), y0, B, U(r)), dl);
    TermVarId y1 = var(T, B);
    RefId M = P(T, mk_pi_lv(b, ml, y1, B, maps_type(r, b, mk_app(R, ref_var(y1)), path(b, B, c, ref_var(y1)))), ml);
    RefId D = diagram_sigma(T, b, r, B);
    RefId out = close(T, pair(dl, D, c, pair(dl, tail(D, c), R, M)));
    return out;
}
static RefId dg_pack(uint64_t b, uint64_t r, RefId B, RefId c, RefId R, RefId M) { return APPN(DPack(b, r), B, c, R, M); }

RefId res_zero(uint64_t z) {
    Tele T_ = { { 1, z, 0, 0, 0 } }, *T = &T_;
    RefId Tz = P(T, U(z), level_succ(z));
    RefId out = close(T, res_pack(z, z, Tz, Tz, maps_id(z, Tz)));
    return out;
}
RefId res_node(uint64_t a, uint64_t z, uint64_t r) {
    Tele T_ = { { 2, a, z, r, 0 } }, *T = &T_;
    uint64_t s = level_max(a, r), tl = level_max(level_succ(z), level_succ(r));
    RefId A = P(T, U(a), level_succ(a)), t = P(T, A, a);
    TermVarId qx = var(T, A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(T, qEx);
    RefId Q = P(T, mk_pi_lv(a, level_max(a, tl), qx, A, mk_pi_lv(a, tl, qe, qEx, res_type(z, r))), level_max(a, tl));
    RefId Q0 = app2(Q, t, refl(a, A, t));
    TermVarId x = var(T, A); RefId Ex = path(a, A, t, ref_var(x)); TermVarId e = var(T, Ex);
    RefId D = res_X(app2(Q, ref_var(x), ref_var(e)));
    RefId Df = mk_lam_lv(a, x, A, mk_lam_lv(a, e, Ex, D));
    TermVarId x2 = var(T, A); RefId Ex2 = path(a, A, t, ref_var(x2)); TermVarId e2 = var(T, Ex2);
    RefId S = mk_sigma_lv(a, s, x2, A, mk_sigma_lv(a, r, e2, Ex2, res_X(app2(Q, ref_var(x2), ref_var(e2)))));
    RefId E = APPN(Sing(a, r), A, t, Df);
    RefId out = close(T, res_pack(z, s, res_T(Q0), S, maps_comp(s, r, z, S, res_X(Q0), res_T(Q0), E, res_M(Q0))));
    return out;
}
RefId dg_zero(uint64_t b) {
    Tele T_ = { { 3, b, 0, 0, 0 } }, *T = &T_;
    RefId B = P(T, U(b), level_succ(b)), c = P(T, B, b);
    TermVarId y = var(T, B); RefId Py = path(b, B, c, ref_var(y));
    RefId out = close(T, dg_pack(b, b, B, c, mk_lam_lv(b, y, B, Py), mk_lam_lv(b, y, B, maps_id(b, Py))));
    return out;
}
/* the diagram node is the presentation node at each y, its terminal C = y */
RefId dg_node(uint64_t a, uint64_t b, uint64_t r) {
    Tele T_ = { { 4, a, b, r, 0 } }, *T = &T_;
    uint64_t s = level_max(a, r), dl = level_max(b, level_succ(r));
    RefId B = P(T, U(b), level_succ(b)), A = P(T, U(a), level_succ(a)), t = P(T, A, a);
    TermVarId qx = var(T, A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(T, qEx);
    RefId Q = P(T, mk_pi_lv(a, level_max(a, dl), qx, A, mk_pi_lv(a, dl, qe, qEx, diagram_type(b, r, B))), level_max(a, dl));
    TermVarId y = var(T, B); RefId yv = ref_var(y);
    TermVarId x = var(T, A); RefId Ex = path(a, A, t, ref_var(x)); TermVarId e = var(T, Ex);
    RefId Qxe = app2(Q, ref_var(x), ref_var(e));
    RefId tl = mk_lam_lv(a, x, A, mk_lam_lv(a, e, Ex, res_pack(b, r, path(b, B, dg_C(Qxe), yv), dg_R(Qxe, yv), dg_M(Qxe, yv))));
    RefId N = app3(res_node(a, b, r), A, t, tl);
    RefId out = close(T, dg_pack(b, s, B, dg_C(app2(Q, t, refl(a, A, t))), mk_lam_lv(b, y, B, res_X(N)), mk_lam_lv(b, y, B, res_M(N))));
    return out;
}

/* ---------------- path induction, K words and the groupoid laws (§83.4) ---------------- */
/* J(T, P, d, b, p) = coe^i P(p@i, ⟨j⟩ p@(i∧j)) d */
static RefId J(Tele *T, uint64_t l, RefId A, RefId a, RefId Pm, RefId d, RefId b, RefId p) {
    DimVarId i = dim(T), j = dim(T);
    RefId ej = mk_plam(j, papp(l, A, a, b, p, iv_meet(iv_var(i), iv_var(j))));
    return mk_coe_at(l, i, app2(Pm, papp(l, A, a, b, p, iv_var(i)), ej), d);
}
typedef RefId (*Motive)(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *cx);
static RefId motive(Tele *T, uint64_t l, RefId A, RefId a, Motive m, const void *cx) {
    TermVarId x = var(T, A); RefId Ax = path(l, A, a, ref_var(x)); TermVarId e = var(T, Ax);
    return mk_lam_lv(l, x, A, mk_lam_lv(l, e, Ax, m(T, l, A, a, ref_var(x), ref_var(e), cx)));
}
typedef struct Word { char op; const struct Word *a, *b; } Word;
static const Word WR = { 'R', NULL, NULL };
static RefId wt(uint64_t l, RefId A, RefId a, const Word *w) {
    if (w->op == 'R') return refl(l, A, a);
    if (w->op == 'V') return rev(l, A, a, a, wt(l, A, a, w->a));
    return cat(l, A, a, a, a, wt(l, A, a, w->a), wt(l, A, a, w->b));
}
/* K(T, w) : w = refl */
static RefId K(Tele *T, uint64_t l, RefId A, RefId a, const Word *w) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a);
    if (w->op == 'R') return refl(l, Paa, ra);
    DimVarId k = dim(T);
    RefId Kv = K(T, l, A, a, w->a), tv = wt(l, A, a, w->a);
    if (w->op == 'V') return mk_plam(k, rev(l, A, a, a, papp(l, Paa, tv, ra, Kv, iv_var(k))));
    RefId Kw = K(T, l, A, a, w->b), tw = wt(l, A, a, w->b);
    RefId mid = mk_plam(k, cat(l, A, a, a, a, papp(l, Paa, tv, ra, Kv, iv_var(k)), papp(l, Paa, tw, ra, Kw, iv_var(k))));
    DimVarId k2 = dim(T), i = dim(T), j = dim(T);      /* K(T, refl·refl)@k@i = fill^j A [(i=0)↦a, (i=1)↦a] a (¬k) */
    RefId Kc = mk_plam(k2, mk_plam(i, mk_fill_at(l, j, A, fc_join(fc_lit(i, 0), fc_lit(i, 1)), a, a, iv_negate(iv_var(k2)))));
    return cat(l, Paa, wt(l, A, a, w), cat(l, A, a, a, a, ra, ra), ra, mid, Kc);
}
static RefId Keq(Tele *T, uint64_t l, RefId A, RefId a, const Word *u, const Word *v) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a), tv = wt(l, A, a, v);
    return cat(l, Paa, wt(l, A, a, u), ra, tv, K(T, l, A, a, u), rev(l, Paa, tv, ra, K(T, l, A, a, v)));
}
static RefId m_lunit(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, x), cat(l, A, a, a, x, refl(l, A, a), e), e); }
static RefId m_rinv(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, a), cat(l, A, a, x, a, e, rev(l, A, a, x, e)), refl(l, A, a)); }
static RefId m_linv(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, x, x), cat(l, A, x, a, x, rev(l, A, a, x, e), e), refl(l, A, x)); }
static RefId m_runinv(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, x), cat(l, A, a, x, x, e, rev(l, A, x, x, refl(l, A, x))), e); }
static RefId m_assoc3(Tele *T, uint64_t l, RefId A, RefId a, RefId z, RefId e3, const void *c) {
    RefId ra = refl(l, A, a);
    return path(l, path(l, A, a, z), cat(l, A, a, a, z, cat(l, A, a, a, a, ra, ra), e3), cat(l, A, a, a, z, ra, cat(l, A, a, a, z, ra, e3)));
}
static RefId m_assoc2(Tele *T, uint64_t l, RefId A, RefId a, RefId y, RefId e2, const void *c) {
    RefId ra = refl(l, A, a); TermVarId d = var(T, A); RefId dv = ref_var(d), Pyd = path(l, A, y, dv); TermVarId r = var(T, Pyd); RefId rv = ref_var(r);
    return mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, Pyd, path(l, path(l, A, a, dv), cat(l, A, a, y, dv, cat(l, A, a, a, y, ra, e2), rv), cat(l, A, a, a, dv, ra, cat(l, A, a, y, dv, e2, rv)))));
}
static RefId m_assoc1(Tele *T, uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) {
    TermVarId cc = var(T, A); RefId cv = ref_var(cc), Pxc = path(l, A, x, cv); TermVarId q = var(T, Pxc); RefId qv = ref_var(q);
    TermVarId d = var(T, A); RefId dv = ref_var(d), Pcd = path(l, A, cv, dv); TermVarId r = var(T, Pcd); RefId rv = ref_var(r);
    RefId Ty = path(l, path(l, A, a, dv), cat(l, A, a, cv, dv, cat(l, A, a, x, cv, e, qv), rv), cat(l, A, a, x, dv, e, cat(l, A, x, cv, dv, qv, rv)));
    return mk_pi_lv(l, l, cc, A, mk_pi_lv(l, l, q, Pxc, mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, Pcd, Ty))));
}
/* a one-path law λ A a b p. J(T, motive, K(T, u)·K(T, v)⁻¹, b, p) */
static RefId law1(uint64_t kind, uint64_t l, Motive m, const Word *u, const Word *v) {
    Tele T_ = { { kind, l, 0, 0, 0 } }, *T = &T_;
    RefId A = P(T, U(l), level_succ(l)), a = P(T, A, l), b = P(T, A, l), p = P(T, path(l, A, a, b), l);
    RefId out = close(T, J(T, l, A, a, motive(T, l, A, a, m, NULL), Keq(T, l, A, a, u, v), b, p));
    return out;
}
static const Word WRR = { 'C', &WR, &WR }, WV = { 'V', &WR, NULL }, WRV = { 'C', &WR, &WV }, WVR = { 'C', &WV, &WR };
static RefId lunit(uint64_t l) { return law1(10, l, m_lunit, &WRR, &WR); }
static RefId rinv(uint64_t l) { return law1(11, l, m_rinv, &WRV, &WR); }
static RefId linv(uint64_t l) { return law1(12, l, m_linv, &WVR, &WR); }
static RefId runinv(uint64_t l) { return law1(13, l, m_runinv, &WRV, &WR); }
/* induction on p, then q, then r; later data under Π */
static RefId assoc(uint64_t l) {
    Tele T_ = { { 14, l, 0, 0, 0 } }, *T = &T_;
    RefId A = P(T, U(l), level_succ(l)), a = P(T, A, l), b = P(T, A, l), c = P(T, A, l), d = P(T, A, l);
    RefId p = P(T, path(l, A, a, b), l), q = P(T, path(l, A, b, c), l), r = P(T, path(l, A, c, d), l);
    static const Word u = { 'C', &WRR, &WR }, v = { 'C', &WR, &WRR };
    TermVarId d2 = var(T, A); RefId P2d = path(l, A, a, ref_var(d2)); TermVarId r2 = var(T, P2d);
    RefId D2 = mk_lam_lv(l, d2, A, mk_lam_lv(l, r2, P2d, J(T, l, A, a, motive(T, l, A, a, m_assoc3, NULL), Keq(T, l, A, a, &u, &v), ref_var(d2), ref_var(r2))));
    TermVarId c1 = var(T, A); RefId Pc = path(l, A, a, ref_var(c1)); TermVarId q1 = var(T, Pc);
    TermVarId d1 = var(T, A); RefId Pd = path(l, A, ref_var(c1), ref_var(d1)); TermVarId r1 = var(T, Pd);
    RefId inner = app2(J(T, l, A, a, motive(T, l, A, a, m_assoc2, NULL), D2, ref_var(c1), ref_var(q1)), ref_var(d1), ref_var(r1));
    RefId D1 = mk_lam_lv(l, c1, A, mk_lam_lv(l, q1, Pc, mk_lam_lv(l, d1, A, mk_lam_lv(l, r1, Pd, inner))));
    RefId out = close(T, app2(app2(J(T, l, A, a, motive(T, l, A, a, m_assoc1, NULL), D1, b, p), c, q), d, r));
    return out;
}
/* the middle maps of p : a = c at y: f q = p⁻¹·q, g s = p·s, with
 * h q = assoc(p,p⁻¹,q)⁻¹ · ap(T, _·q)(rinv p) · lunit q and symmetrically k */
static RefId mid(uint64_t l) {
    Tele T_ = { { 15, l, 0, 0, 0 } }, *T = &T_;
    RefId B = P(T, U(l), level_succ(l)), a = P(T, B, l), c = P(T, B, l), p = P(T, path(l, B, a, c), l), y = P(T, B, l);
    RefId As = assoc(l), Lu = lunit(l);
    RefId Pay = path(l, B, a, y), Pcy = path(l, B, c, y), pinv = rev(l, B, a, c, p);
    RefId side[2];
    for (int dir = 0; dir < 2; dir++) {
        /* dir 0: q : a = y, the round trip p·(p⁻¹·q) ; dir 1: s : c = y, p⁻¹·(p·s) */
        RefId o = dir ? c : a, m = dir ? a : c, po = dir ? pinv : p, pm = dir ? p : pinv, Po = dir ? Pcy : Pay;
        TermVarId vq = var(T, Po); RefId q = ref_var(vq);
        RefId X0 = cat(l, B, o, m, y, po, cat(l, B, m, o, y, pm, q));
        RefId pp = cat(l, B, o, m, o, po, pm), X1 = cat(l, B, o, o, y, pp, q), X2 = cat(l, B, o, o, y, refl(l, B, o), q);
        RefId Poo = path(l, B, o, o); TermVarId vv = var(T, Poo);
        RefId s1 = rev(l, Po, X1, X0, APPN(As, B, o, m, o, y, po, pm, q));
        RefId s2 = ap(T, l, Poo, pp, refl(l, B, o), mk_lam_lv(l, vv, Poo, cat(l, B, o, o, y, ref_var(vv), q)), dir ? APPN(linv(l), B, a, c, p) : APPN(rinv(l), B, a, c, p));
        side[dir] = mk_lam_lv(l, vq, Po, cat(l, Po, X0, X1, q, s1, cat(l, Po, X1, X2, q, s2, APPN(Lu, B, o, y, q))));
    }
    TermVarId fq = var(T, Pay), gs = var(T, Pcy);
    RefId f = mk_lam_lv(l, fq, Pay, cat(l, B, c, a, y, pinv, ref_var(fq))), g = mk_lam_lv(l, gs, Pcy, cat(l, B, a, c, y, p, ref_var(gs)));
    RefId out = close(T, maps_pack(l, l, Pay, Pcy, f, g, side[0], side[1]));
    return out;
}

/* ---------------- actions ---------------- */
/* comp(comp(M_L, E), M_R⁻¹) : Maps(X_L, X_R) for E : Maps(T_L, T_R) */
RefId res_action(uint64_t zl, uint64_t rl, uint64_t zr, uint64_t rr) {
    Tele T_ = { { 20, zl, rl, zr, rr } }, *T = &T_;
    RefId L = P(T, res_type(zl, rl), level_max(level_succ(zl), level_succ(rl))), R = P(T, res_type(zr, rr), level_max(level_succ(zr), level_succ(rr)));
    RefId TL = res_T(L), TR = res_T(R), XL = res_X(L), XR = res_X(R);
    RefId E = P(T, maps_type(zl, zr, TL, TR), level_max(zl, zr));
    RefId C1 = maps_comp(rl, zl, zr, XL, TL, TR, res_M(L), E);
    RefId out = close(T, maps_comp(rl, zr, rr, XL, TR, XR, C1, maps_inv(rr, zr, XR, TR, res_M(R))));
    return out;
}
/* F = d_R(p⁻¹·c_L r), G = d_L(p·c_R s): the action of p on the presentations of C_L = y, C_R = y */
RefId id_action(uint64_t b, uint64_t rl, uint64_t rr) {
    Tele T_ = { { 21, b, rl, rr, 0 } }, *T = &T_;
    RefId B = P(T, U(b), level_succ(b));
    RefId L = P(T, diagram_type(b, rl, B), level_max(b, level_succ(rl))), R = P(T, diagram_type(b, rr, B), level_max(b, level_succ(rr)));
    RefId p = P(T, path(b, B, dg_C(L), dg_C(R)), b), y = P(T, B, b);
    RefId PL = res_pack(b, rl, path(b, B, dg_C(L), y), dg_R(L, y), dg_M(L, y));
    RefId PR = res_pack(b, rr, path(b, B, dg_C(R), y), dg_R(R, y), dg_M(R, y));
    RefId out = close(T, APPN(res_action(b, rl, b, rr), PL, PR, APPN(mid(b), B, dg_C(L), dg_C(R), p, y)));
    return out;
}

/* ---------------- the other schemas (§83.5) ---------------- */
RefId equiv_maps(uint64_t l, uint64_t m) {
    Tele T_ = { { 30, l, m, 0, 0 } }, *T = &T_;
    uint64_t n = level_max(l, m);
    RefId X = P(T, U(l), level_succ(l)), Y = P(T, U(m), level_succ(m)), e = P(T, mk_equiv(l, m, X, Y), n);
    RefId c = equiv_map(l, m, X, Y, e);
    TermVarId y1 = var(T, Y), y2 = var(T, Y), x = var(T, X);
    RefId d = mk_lam_lv(m, y1, Y, mk_fst(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y1)))));
    RefId k = mk_lam_lv(m, y2, Y, mk_snd(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y2)))));
    RefId y0 = mk_app(c, ref_var(x)), Fib = mk_fib(l, m, X, Y, c, y0), w = pair(n, Fib, ref_var(x), refl(m, Y, y0));
    RefId ctr = equiv_contr(l, m, X, Y, e, y0);
    DimVarId i = dim(T);
    RefId h = mk_lam_lv(l, x, X, mk_plam(i, mk_fst(papp(n, Fib, mk_fst(ctr), w, mk_app(mk_snd(ctr), w), iv_var(i)))));
    RefId out = close(T, maps_pack(l, m, X, Y, c, d, h, k));
    return out;
}
typedef struct { uint64_t b; RefId B, C, D, Cut; } CutCx;
/* P(z', v') = Π(u' : C = z'). (D, u'·v'⁻¹, refl D) = (z', u', v') in Cut */
static RefId m_cut(Tele *T, uint64_t l, RefId A, RefId a, RefId z, RefId v, const void *cxp) {
    const CutCx *c = cxp; RefId Cz = path(l, A, c->C, z); TermVarId u = var(T, Cz); RefId uv = ref_var(u);
    RefId gf = pair(l, c->Cut, c->D, pair(l, tail(c->Cut, c->D), cat(l, A, c->C, z, c->D, uv, rev(l, A, c->D, z, v)), refl(l, A, c->D)));
    return mk_pi_lv(l, l, u, Cz, path(l, c->Cut, gf, pair(l, c->Cut, z, pair(l, tail(c->Cut, z), uv, v))));
}
RefId cut_maps(uint64_t b) {
    Tele T_ = { { 31, b, 0, 0, 0 } }, *T = &T_;
    RefId B = P(T, U(b), level_succ(b)), C = P(T, B, b), D = P(T, B, b);
    TermVarId z = var(T, B); RefId Cz = path(b, B, C, ref_var(z)), Dz = path(b, B, D, ref_var(z)); TermVarId u = var(T, Cz);
    RefId Cut = mk_sigma_lv(b, b, z, B, mk_sigma_lv(b, b, u, Cz, Dz)), PCD = path(b, B, C, D);
    TermVarId w = var(T, Cut); RefId wv = ref_var(w), zw = mk_fst(wv), uw = mk_fst(mk_snd(wv)), vw = mk_snd(mk_snd(wv));
    RefId f = mk_lam_lv(b, w, Cut, cat(b, B, C, zw, D, uw, rev(b, B, D, zw, vw)));
    TermVarId hv = var(T, PCD);
    RefId g = mk_lam_lv(b, hv, PCD, pair(b, Cut, D, pair(b, tail(Cut, D), ref_var(hv), refl(b, B, D))));
    RefId Ri = runinv(b);                                          /* h·refl⁻¹ = h */
    TermVarId hk = var(T, PCD);
    RefId k = mk_lam_lv(b, hk, PCD, APPN(Ri, B, C, D, ref_var(hk)));
    CutCx cx = { b, B, C, D, Cut };
    TermVarId ub = var(T, PCD); DimVarId i = dim(T);
    RefId X0 = cat(b, B, C, D, D, ref_var(ub), rev(b, B, D, D, refl(b, B, D)));
    RefId base = mk_lam_lv(b, ub, PCD, mk_plam(i, pair(b, Cut, D, pair(b, tail(Cut, D), papp(b, PCD, X0, ref_var(ub), APPN(Ri, B, C, D, ref_var(ub)), iv_var(i)), refl(b, B, D)))));
    TermVarId w2 = var(T, Cut); RefId w2v = ref_var(w2);
    RefId h = mk_lam_lv(b, w2, Cut, mk_app(J(T, b, B, D, motive(T, b, B, D, m_cut, &cx), base, mk_fst(w2v), mk_snd(mk_snd(w2v))), mk_fst(mk_snd(w2v))));
    RefId out = close(T, maps_pack(b, b, Cut, PCD, f, g, h, k));
    return out;
}
RefId fibre_maps(uint64_t b, uint64_t r) {
    Tele T_ = { { 32, b, r, 0, 0 } }, *T = &T_;
    uint64_t s = level_max(b, r);
    RefId B = P(T, U(b), level_succ(b));
    TermVarId x0 = var(T, B); RefId R = P(T, mk_pi_lv(b, level_succ(r), x0, B, U(r)), level_max(b, level_succ(r)));
    TermVarId x1 = var(T, B); RefId k = P(T, mk_pi_lv(b, r, x1, B, mk_contr(r, mk_app(R, ref_var(x1)))), s);
    TermVarId xs = var(T, B); RefId S = mk_sigma_lv(b, r, xs, B, mk_app(R, ref_var(xs)));
    TermVarId w = var(T, S), xb = var(T, B), w2 = var(T, S), xk = var(T, B);
    RefId f = mk_lam_lv(s, w, S, mk_fst(ref_var(w)));
    RefId g = mk_lam_lv(b, xb, B, pair(s, S, ref_var(xb), mk_fst(mk_app(k, ref_var(xb)))));
    RefId b2 = mk_fst(ref_var(w2)), r2 = mk_snd(ref_var(w2)), kb = mk_app(k, b2);
    DimVarId i = dim(T);
    RefId h = mk_lam_lv(s, w2, S, mk_plam(i, pair(s, S, b2, papp(r, mk_app(R, b2), mk_fst(kb), r2, mk_app(mk_snd(kb), r2), iv_var(i)))));
    RefId out = close(T, maps_pack(s, b, S, B, f, g, h, mk_lam_lv(b, xk, B, refl(b, B, ref_var(xk)))));
    return out;
}

/* ---------------- source declarations: the right fold ---------------- */
static RefId fold(size_t n, const DiagNode *nd, RefId B, uint64_t lB, RefId o, uint64_t *r) {
    RefId D = B ? app2(dg_zero(lB), B, o) : mk_app(res_zero(lB), o);
    uint64_t lv = lB;
    for (size_t k = n; k-- > 0; ) {
        RefId Pk = path(nd[k].level, nd[k].A, nd[k].t, ref_var(nd[k].x));
        RefId Q = mk_lam_lv(nd[k].level, nd[k].x, nd[k].A, mk_lam_lv(nd[k].level, nd[k].e, Pk, D));
        D = B ? APPN(dg_node(nd[k].level, lB, lv), B, nd[k].A, nd[k].t, Q) : APPN(res_node(nd[k].level, lB, lv), nd[k].A, nd[k].t, Q);
        lv = level_max(nd[k].level, lv);
    }
    *r = lv;
    return D;
}
RefId diagram_fold(size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o, uint64_t *r) { return fold(n, nodes, B, lB, o, r); }
RefId residual_fold(size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ, uint64_t *r) { return fold(n, nodes, 0, lZ, Z, r); }

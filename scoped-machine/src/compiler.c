/* compiler.c — identities as ordinary values (compiler.h). The emitters of
 * Maps, the singleton, Diagram, zero and node follow the §96 witness. */
#include "compiler.h"

/* binders of one construction are keyed by (construction, levels, ordinal),
 * so building it again yields the same reference */
typedef struct { uint64_t k[5], n; bool on; } Keying;
static __thread Keying KY;
static Keying enter(uint64_t kind, uint64_t a, uint64_t b, uint64_t c, uint64_t d) { Keying s = KY; KY = (Keying){ { kind, a, b, c, d }, 0, true }; return s; }
static void leave(Keying s) { KY = s; }
static TermVarId var(RefId A) {
    if (!KY.on) return declare_term(A, fc_true());
    KeyWord k[7] = { { KW_CONST, 8100 }, { KW_CONST, KY.k[0] }, { KW_CONST, KY.k[1] }, { KW_CONST, KY.k[2] }, { KW_CONST, KY.k[3] }, { KW_CONST, KY.k[4] }, { KW_CONST, KY.n++ } };
    return fresh_term_keyed(k, 7, A);
}
static DimVarId dim(void) {
    if (!KY.on) return declare_dim();
    KeyWord k[7] = { { KW_CONST, 8101 }, { KW_CONST, KY.k[0] }, { KW_CONST, KY.k[1] }, { KW_CONST, KY.k[2] }, { KW_CONST, KY.k[3] }, { KW_CONST, KY.k[4] }, { KW_CONST, KY.n++ } };
    return fresh_dim_keyed(k, 7);
}
/* the telescope of a closed construction */
typedef struct { size_t n; TermVarId x[8]; RefId A[8]; uint64_t l[8]; } Tele;
static RefId P(Tele *T, RefId A, uint64_t l) { TermVarId x = var(A); T->x[T->n] = x; T->A[T->n] = A; T->l[T->n] = l; T->n++; return ref_var(x); }
static RefId close(const Tele *T, RefId body) { for (size_t q = T->n; q-- > 0; ) body = mk_lam_lv(T->l[q], T->x[q], T->A[q], body); return body; }

static uint64_t mx(uint64_t a, uint64_t b) { return a > b ? a : b; }
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

/* ---------------- Maps (§83.1) ---------------- */
RefId maps_type(uint64_t a, uint64_t b, RefId A, RefId B) {
    uint64_t m = mx(a, b);
    RefId F = mk_fun(a, b, A, B), G = mk_fun(b, a, B, A);
    TermVarId f = var(F), g = var(G), x = var(A), y = var(B);
    RefId H = mk_pi_lv(a, a, x, A, path(a, A, mk_app(ref_var(g), mk_app(ref_var(f), ref_var(x))), ref_var(x)));
    RefId K = mk_pi_lv(b, b, y, B, path(b, B, mk_app(ref_var(f), mk_app(ref_var(g), ref_var(y))), ref_var(y)));
    TermVarId h = var(H);
    return mk_sigma_lv(m, m, f, F, mk_sigma_lv(m, m, g, G, mk_sigma_lv(a, b, h, H, K)));
}
static RefId maps_pack(uint64_t a, uint64_t b, RefId A, RefId B, RefId f, RefId g, RefId h, RefId k) {
    uint64_t m = mx(a, b); RefId M = maps_type(a, b, A, B), M1 = tail(M, f), M2 = tail(M1, g);
    return pair(m, M, f, pair(m, M1, g, pair(m, M2, h, k)));
}
static RefId maps_id(uint64_t a, RefId A) {
    TermVarId x = var(A); RefId id = mk_id_fun(a, A);
    RefId h = mk_lam_lv(a, x, A, refl(a, A, ref_var(x)));
    return maps_pack(a, a, A, A, id, id, h, h);
}
static RefId ap(uint64_t a, RefId A, RefId x, RefId y, RefId f, RefId p) {
    DimVarId i = dim();
    return mk_plam(i, mk_app(f, papp(a, A, x, y, p, iv_var(i))));
}
/* E : A ↔ B, F : B ↔ C */
static RefId maps_comp(uint64_t a, uint64_t b, uint64_t c, RefId A, RefId B, RefId C, RefId E, RefId F) {
    RefId f = maps_c(E), g = maps_d(E), h = maps_h(E), k = maps_k(E);
    RefId u = maps_c(F), v = maps_d(F), H = maps_h(F), K = maps_k(F);
    TermVarId x = var(A), z = var(C); RefId xv = ref_var(x), zv = ref_var(z);
    RefId fx = mk_app(f, xv), vz = mk_app(v, zv);
    RefId forward = mk_lam_lv(a, x, A, mk_app(u, fx));
    RefId reverse = mk_lam_lv(c, z, C, mk_app(g, vz));
    RefId vufx = mk_app(v, mk_app(u, fx)), gvufx = mk_app(g, vufx), gfx = mk_app(g, fx);
    RefId hh = mk_lam_lv(a, x, A, cat(a, A, gvufx, gfx, xv, ap(b, B, vufx, fx, g, mk_app(H, fx)), mk_app(h, xv)));
    RefId fgvz = mk_app(f, mk_app(g, vz)), ufgvz = mk_app(u, fgvz), uvz = mk_app(u, vz);
    RefId kk = mk_lam_lv(c, z, C, cat(c, C, ufgvz, uvz, zv, ap(b, B, fgvz, vz, u, mk_app(k, vz)), mk_app(K, zv)));
    return maps_pack(a, c, A, C, forward, reverse, hh, kk);
}
static RefId maps_inv(uint64_t a, uint64_t b, RefId A, RefId B, RefId E) { return maps_pack(b, a, B, A, maps_d(E), maps_c(E), maps_k(E), maps_h(E)); }

/* ---------------- the dependent singleton (§83.2); D open in x, e ---------------- */
static RefId singleton(uint64_t a, uint64_t r, RefId A, RefId t, TermVarId x, TermVarId e, RefId D, RefId *S_out, RefId *Z_out) {
    uint64_t s = mx(a, r); RefId Ex = path(a, A, t, ref_var(x));
    RefId S = mk_sigma_lv(a, s, x, A, mk_sigma_lv(a, r, e, Ex, D));
    ScopeId DS = capture_term2(x, A, a, e, Ex, a, D, U(r), r + 1, fc_true());
    RefId rf = refl(a, A, t);
    MapBuilder mz; mapb_init(&mz); mapb_term(&mz, x, t); mapb_term(&mz, e, rf);
    RefId Z = reindex(D, mapb_finish(&mz));
    TermVarId w = var(S), z = var(Z); RefId wv = ref_var(w), zv = ref_var(z);
    RefId wx = mk_fst(wv), we = mk_fst(mk_snd(wv)), wz = mk_snd(mk_snd(wv));
    RefId down = mk_lam_lv(s, w, S, mk_down(r, a, A, t, DS, wx, we, wz));
    RefId up = mk_lam_lv(r, z, Z, pair(s, S, t, pair(s, tail(S, t), rf, zv)));
    DimVarId i = dim(), j = dim(), q = dim();
    RefId xi = papp(a, A, t, wx, we, iv_var(i));
    RefId ei = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_var(i), iv_var(j))));
    RefId xq = papp(a, A, t, wx, we, iv_negate(iv_var(q)));
    RefId eq = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_negate(iv_var(q)), iv_var(j))));
    MapBuilder mq; mapb_init(&mq); mapb_term(&mq, x, xq); mapb_term(&mq, e, eq);
    RefId Dq = reindex(D, mapb_finish(&mq)), empty = mk_system(0, NULL, NULL);
    RefId zi = mk_fill_at(r, q, Dq, fc_false(), empty, wz, iv_negate(iv_var(i)));
    RefId h = mk_lam_lv(s, w, S, mk_plam(i, pair(s, S, xi, pair(s, tail(S, xi), ei, zi))));
    RefId k = mk_lam_lv(r, z, Z, mk_plam(i, mk_fill_at(r, q, Z, fc_false(), empty, zv, iv_negate(iv_var(i)))));
    *S_out = S; *Z_out = Z;
    return maps_pack(s, r, S, Z, down, up, h, k);
}

/* ---------------- presentations and diagrams (§83.3, §96.2) ---------------- */
RefId res_type(uint64_t z, uint64_t r) {
    TermVarId T = var(U(z)), X = var(U(r));
    return mk_sigma_lv(z + 1, mx(r + 1, z), T, U(z), mk_sigma_lv(r + 1, mx(r, z), X, U(r), maps_type(r, z, ref_var(X), ref_var(T))));
}
static RefId res_pack(uint64_t z, uint64_t r, RefId T, RefId X, RefId M) {
    RefId RT = res_type(z, r);
    return pair(mx(z + 1, r + 1), RT, T, pair(mx(r + 1, z), tail(RT, T), X, M));
}
RefId diagram_type(uint64_t b, uint64_t r, RefId B) {
    uint64_t rl = mx(b, r + 1), ml = mx(b, r);
    TermVarId c = var(B), y = var(B);
    RefId RT = mk_pi_lv(b, r + 1, y, B, U(r)); TermVarId R = var(RT);
    RefId M = mk_pi_lv(b, ml, y, B, maps_type(r, b, mk_app(ref_var(R), ref_var(y)), path(b, B, ref_var(c), ref_var(y))));
    return mk_sigma_lv(b, rl, c, B, mk_sigma_lv(rl, ml, R, RT, M));
}
static RefId dg_pack(uint64_t b, uint64_t r, RefId B, RefId c, RefId R, RefId M) {
    uint64_t dl = mx(b, r + 1); RefId D = diagram_type(b, r, B);
    return pair(dl, D, c, pair(dl, tail(D, c), R, M));
}

RefId res_zero(uint64_t z) {
    Keying s = enter(1, z, 0, 0, 0); Tele T = { 0 };
    RefId Tz = P(&T, U(z), z + 1);
    RefId out = close(&T, res_pack(z, z, Tz, Tz, maps_id(z, Tz)));
    leave(s); return out;
}
RefId res_node(uint64_t a, uint64_t z, uint64_t r) {
    Keying sv = enter(2, a, z, r, 0); Tele T = { 0 };
    uint64_t s = mx(a, r), tl = mx(z + 1, r + 1);
    RefId A = P(&T, U(a), a + 1), t = P(&T, A, a);
    TermVarId qx = var(A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(qEx);
    RefId Q = P(&T, mk_pi_lv(a, mx(a, tl), qx, A, mk_pi_lv(a, tl, qe, qEx, res_type(z, r))), mx(a, tl));
    RefId Q0 = app2(Q, t, refl(a, A, t));
    TermVarId x = var(A); TermVarId e = var(path(a, A, t, ref_var(x)));
    RefId S, Z0, E = singleton(a, r, A, t, x, e, res_X(app2(Q, ref_var(x), ref_var(e))), &S, &Z0);
    RefId out = close(&T, res_pack(z, s, res_T(Q0), S, maps_comp(s, r, z, S, Z0, res_T(Q0), E, res_M(Q0))));
    leave(sv); return out;
}
RefId dg_zero(uint64_t b) {
    Keying sv = enter(3, b, 0, 0, 0); Tele T = { 0 };
    RefId B = P(&T, U(b), b + 1), c = P(&T, B, b);
    TermVarId y = var(B); RefId Py = path(b, B, c, ref_var(y));
    RefId out = close(&T, dg_pack(b, b, B, c, mk_lam_lv(b, y, B, Py), mk_lam_lv(b, y, B, maps_id(b, Py))));
    leave(sv); return out;
}
/* the diagram node is the presentation node at each y, its terminal C = y */
RefId dg_node(uint64_t a, uint64_t b, uint64_t r) {
    Keying sv = enter(4, a, b, r, 0); Tele T = { 0 };
    uint64_t s = mx(a, r), dl = mx(b, r + 1);
    RefId B = P(&T, U(b), b + 1), A = P(&T, U(a), a + 1), t = P(&T, A, a);
    TermVarId qx = var(A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(qEx);
    RefId Q = P(&T, mk_pi_lv(a, mx(a, dl), qx, A, mk_pi_lv(a, dl, qe, qEx, diagram_type(b, r, B))), mx(a, dl));
    TermVarId y = var(B); RefId yv = ref_var(y);
    TermVarId x = var(A); RefId Ex = path(a, A, t, ref_var(x)); TermVarId e = var(Ex);
    RefId Qxe = app2(Q, ref_var(x), ref_var(e));
    RefId tl = mk_lam_lv(a, x, A, mk_lam_lv(a, e, Ex, res_pack(b, r, path(b, B, dg_C(Qxe), yv), dg_R(Qxe, yv), dg_M(Qxe, yv))));
    RefId N = app3(res_node(a, b, r), A, t, tl);
    RefId out = close(&T, dg_pack(b, s, B, dg_C(app2(Q, t, refl(a, A, t))), mk_lam_lv(b, y, B, res_X(N)), mk_lam_lv(b, y, B, res_M(N))));
    leave(sv); return out;
}

/* ---------------- path induction, K words and the groupoid laws (§83.4) ---------------- */
/* J(P, d, b, p) = coe^i P(p@i, ⟨j⟩ p@(i∧j)) d */
static RefId J(uint64_t l, RefId A, RefId a, RefId Pm, RefId d, RefId b, RefId p) {
    DimVarId i = dim(), j = dim();
    RefId ej = mk_plam(j, papp(l, A, a, b, p, iv_meet(iv_var(i), iv_var(j))));
    return mk_coe_at(l, i, app2(Pm, papp(l, A, a, b, p, iv_var(i)), ej), d);
}
typedef RefId (*Motive)(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *cx);
static RefId motive(uint64_t l, RefId A, RefId a, Motive m, const void *cx) {
    TermVarId x = var(A); RefId Ax = path(l, A, a, ref_var(x)); TermVarId e = var(Ax);
    return mk_lam_lv(l, x, A, mk_lam_lv(l, e, Ax, m(l, A, a, ref_var(x), ref_var(e), cx)));
}
typedef struct Word { char op; const struct Word *a, *b; } Word;
static const Word WR = { 'R', NULL, NULL };
static RefId wt(uint64_t l, RefId A, RefId a, const Word *w) {
    if (w->op == 'R') return refl(l, A, a);
    if (w->op == 'V') return rev(l, A, a, a, wt(l, A, a, w->a));
    return cat(l, A, a, a, a, wt(l, A, a, w->a), wt(l, A, a, w->b));
}
/* K(w) : w = refl */
static RefId K(uint64_t l, RefId A, RefId a, const Word *w) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a);
    if (w->op == 'R') return refl(l, Paa, ra);
    DimVarId k = dim();
    RefId Kv = K(l, A, a, w->a), tv = wt(l, A, a, w->a);
    if (w->op == 'V') return mk_plam(k, rev(l, A, a, a, papp(l, Paa, tv, ra, Kv, iv_var(k))));
    RefId Kw = K(l, A, a, w->b), tw = wt(l, A, a, w->b);
    RefId mid = mk_plam(k, cat(l, A, a, a, a, papp(l, Paa, tv, ra, Kv, iv_var(k)), papp(l, Paa, tw, ra, Kw, iv_var(k))));
    DimVarId k2 = dim(), i = dim(), j = dim();      /* K(refl·refl)@k@i = fill^j A [(i=0)↦a, (i=1)↦a] a (¬k) */
    RefId Kc = mk_plam(k2, mk_plam(i, mk_fill_at(l, j, A, fc_join(fc_lit(i, 0), fc_lit(i, 1)), a, a, iv_negate(iv_var(k2)))));
    return cat(l, Paa, wt(l, A, a, w), cat(l, A, a, a, a, ra, ra), ra, mid, Kc);
}
static RefId Keq(uint64_t l, RefId A, RefId a, const Word *u, const Word *v) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a), tv = wt(l, A, a, v);
    return cat(l, Paa, wt(l, A, a, u), ra, tv, K(l, A, a, u), rev(l, Paa, tv, ra, K(l, A, a, v)));
}
static RefId m_lunit(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, x), cat(l, A, a, a, x, refl(l, A, a), e), e); }
static RefId m_rinv(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, a), cat(l, A, a, x, a, e, rev(l, A, a, x, e)), refl(l, A, a)); }
static RefId m_linv(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, x, x), cat(l, A, x, a, x, rev(l, A, a, x, e), e), refl(l, A, x)); }
static RefId m_runinv(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) { return path(l, path(l, A, a, x), cat(l, A, a, x, x, e, rev(l, A, x, x, refl(l, A, x))), e); }
static RefId m_assoc3(uint64_t l, RefId A, RefId a, RefId z, RefId e3, const void *c) {
    RefId ra = refl(l, A, a);
    return path(l, path(l, A, a, z), cat(l, A, a, a, z, cat(l, A, a, a, a, ra, ra), e3), cat(l, A, a, a, z, ra, cat(l, A, a, a, z, ra, e3)));
}
static RefId m_assoc2(uint64_t l, RefId A, RefId a, RefId y, RefId e2, const void *c) {
    RefId ra = refl(l, A, a); TermVarId d = var(A); RefId dv = ref_var(d), Pyd = path(l, A, y, dv); TermVarId r = var(Pyd); RefId rv = ref_var(r);
    return mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, Pyd, path(l, path(l, A, a, dv), cat(l, A, a, y, dv, cat(l, A, a, a, y, ra, e2), rv), cat(l, A, a, a, dv, ra, cat(l, A, a, y, dv, e2, rv)))));
}
static RefId m_assoc1(uint64_t l, RefId A, RefId a, RefId x, RefId e, const void *c) {
    TermVarId cc = var(A); RefId cv = ref_var(cc), Pxc = path(l, A, x, cv); TermVarId q = var(Pxc); RefId qv = ref_var(q);
    TermVarId d = var(A); RefId dv = ref_var(d), Pcd = path(l, A, cv, dv); TermVarId r = var(Pcd); RefId rv = ref_var(r);
    RefId T = path(l, path(l, A, a, dv), cat(l, A, a, cv, dv, cat(l, A, a, x, cv, e, qv), rv), cat(l, A, a, x, dv, e, cat(l, A, x, cv, dv, qv, rv)));
    return mk_pi_lv(l, l, cc, A, mk_pi_lv(l, l, q, Pxc, mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, Pcd, T))));
}
/* a one-path law λ A a b p. J(motive, K(u)·K(v)⁻¹, b, p) */
static RefId law1(uint64_t kind, uint64_t l, Motive m, const Word *u, const Word *v) {
    Keying sv = enter(kind, l, 0, 0, 0); Tele T = { 0 };
    RefId A = P(&T, U(l), l + 1), a = P(&T, A, l), b = P(&T, A, l), p = P(&T, path(l, A, a, b), l);
    RefId out = close(&T, J(l, A, a, motive(l, A, a, m, NULL), Keq(l, A, a, u, v), b, p));
    leave(sv); return out;
}
static const Word WRR = { 'C', &WR, &WR }, WV = { 'V', &WR, NULL }, WRV = { 'C', &WR, &WV }, WVR = { 'C', &WV, &WR };
static RefId lunit(uint64_t l) { return law1(10, l, m_lunit, &WRR, &WR); }
static RefId rinv(uint64_t l) { return law1(11, l, m_rinv, &WRV, &WR); }
static RefId linv(uint64_t l) { return law1(12, l, m_linv, &WVR, &WR); }
static RefId runinv(uint64_t l) { return law1(13, l, m_runinv, &WRV, &WR); }
/* induction on p, then q, then r; later data under Π */
static RefId assoc(uint64_t l) {
    Keying sv = enter(14, l, 0, 0, 0); Tele T = { 0 };
    RefId A = P(&T, U(l), l + 1), a = P(&T, A, l), b = P(&T, A, l), c = P(&T, A, l), d = P(&T, A, l);
    RefId p = P(&T, path(l, A, a, b), l), q = P(&T, path(l, A, b, c), l), r = P(&T, path(l, A, c, d), l);
    static const Word u = { 'C', &WRR, &WR }, v = { 'C', &WR, &WRR };
    TermVarId d2 = var(A); RefId P2d = path(l, A, a, ref_var(d2)); TermVarId r2 = var(P2d);
    RefId D2 = mk_lam_lv(l, d2, A, mk_lam_lv(l, r2, P2d, J(l, A, a, motive(l, A, a, m_assoc3, NULL), Keq(l, A, a, &u, &v), ref_var(d2), ref_var(r2))));
    TermVarId c1 = var(A); RefId Pc = path(l, A, a, ref_var(c1)); TermVarId q1 = var(Pc);
    TermVarId d1 = var(A); RefId Pd = path(l, A, ref_var(c1), ref_var(d1)); TermVarId r1 = var(Pd);
    RefId inner = app2(J(l, A, a, motive(l, A, a, m_assoc2, NULL), D2, ref_var(c1), ref_var(q1)), ref_var(d1), ref_var(r1));
    RefId D1 = mk_lam_lv(l, c1, A, mk_lam_lv(l, q1, Pc, mk_lam_lv(l, d1, A, mk_lam_lv(l, r1, Pd, inner))));
    RefId out = close(&T, app2(app2(J(l, A, a, motive(l, A, a, m_assoc1, NULL), D1, b, p), c, q), d, r));
    leave(sv); return out;
}
#define APPN(f, ...) appn((f), sizeof((RefId[]){ __VA_ARGS__ }) / sizeof(RefId), (RefId[]){ __VA_ARGS__ })
static RefId appn(RefId f, size_t n, const RefId *a) { for (size_t q = 0; q < n; q++) f = mk_app(f, a[q]); return f; }

/* the middle maps of p : a = c at y: f q = p⁻¹·q, g s = p·s, with
 * h q = assoc(p,p⁻¹,q)⁻¹ · ap(_·q)(rinv p) · lunit q and symmetrically k */
static RefId mid(uint64_t l) {
    Keying sv = enter(15, l, 0, 0, 0); Tele T = { 0 };
    RefId B = P(&T, U(l), l + 1), a = P(&T, B, l), c = P(&T, B, l), p = P(&T, path(l, B, a, c), l), y = P(&T, B, l);
    RefId As = assoc(l), Lu = lunit(l);
    RefId Pay = path(l, B, a, y), Pcy = path(l, B, c, y), pinv = rev(l, B, a, c, p);
    RefId side[2];
    for (int dir = 0; dir < 2; dir++) {
        /* dir 0: q : a = y, the round trip p·(p⁻¹·q) ; dir 1: s : c = y, p⁻¹·(p·s) */
        RefId o = dir ? c : a, m = dir ? a : c, po = dir ? pinv : p, pm = dir ? p : pinv, Po = dir ? Pcy : Pay;
        TermVarId vq = var(Po); RefId q = ref_var(vq);
        RefId X0 = cat(l, B, o, m, y, po, cat(l, B, m, o, y, pm, q));
        RefId pp = cat(l, B, o, m, o, po, pm), X1 = cat(l, B, o, o, y, pp, q), X2 = cat(l, B, o, o, y, refl(l, B, o), q);
        RefId Poo = path(l, B, o, o); TermVarId vv = var(Poo);
        RefId s1 = rev(l, Po, X1, X0, APPN(As, B, o, m, o, y, po, pm, q));
        RefId s2 = ap(l, Poo, pp, refl(l, B, o), mk_lam_lv(l, vv, Poo, cat(l, B, o, o, y, ref_var(vv), q)), dir ? APPN(linv(l), B, a, c, p) : APPN(rinv(l), B, a, c, p));
        side[dir] = mk_lam_lv(l, vq, Po, cat(l, Po, X0, X1, q, s1, cat(l, Po, X1, X2, q, s2, APPN(Lu, B, o, y, q))));
    }
    TermVarId fq = var(Pay), gs = var(Pcy);
    RefId f = mk_lam_lv(l, fq, Pay, cat(l, B, c, a, y, pinv, ref_var(fq))), g = mk_lam_lv(l, gs, Pcy, cat(l, B, a, c, y, p, ref_var(gs)));
    RefId out = close(&T, maps_pack(l, l, Pay, Pcy, f, g, side[0], side[1]));
    leave(sv); return out;
}

/* ---------------- actions ---------------- */
/* comp(comp(M_L, E), M_R⁻¹) : Maps(X_L, X_R) for E : Maps(T_L, T_R) */
RefId res_action(uint64_t zl, uint64_t rl, uint64_t zr, uint64_t rr) {
    Keying sv = enter(20, zl, rl, zr, rr); Tele T = { 0 };
    RefId L = P(&T, res_type(zl, rl), mx(zl + 1, rl + 1)), R = P(&T, res_type(zr, rr), mx(zr + 1, rr + 1));
    RefId TL = res_T(L), TR = res_T(R), XL = res_X(L), XR = res_X(R);
    RefId E = P(&T, maps_type(zl, zr, TL, TR), mx(zl, zr));
    RefId C1 = maps_comp(rl, zl, zr, XL, TL, TR, res_M(L), E);
    RefId out = close(&T, maps_comp(rl, zr, rr, XL, TR, XR, C1, maps_inv(rr, zr, XR, TR, res_M(R))));
    leave(sv); return out;
}
/* F = d_R(p⁻¹·c_L r), G = d_L(p·c_R s): the action of p on the presentations of C_L = y, C_R = y */
RefId id_action(uint64_t b, uint64_t rl, uint64_t rr) {
    Keying sv = enter(21, b, rl, rr, 0); Tele T = { 0 };
    RefId B = P(&T, U(b), b + 1);
    RefId L = P(&T, diagram_type(b, rl, B), mx(b, rl + 1)), R = P(&T, diagram_type(b, rr, B), mx(b, rr + 1));
    RefId p = P(&T, path(b, B, dg_C(L), dg_C(R)), b), y = P(&T, B, b);
    RefId PL = res_pack(b, rl, path(b, B, dg_C(L), y), dg_R(L, y), dg_M(L, y));
    RefId PR = res_pack(b, rr, path(b, B, dg_C(R), y), dg_R(R, y), dg_M(R, y));
    RefId out = close(&T, APPN(res_action(b, rl, b, rr), PL, PR, APPN(mid(b), B, dg_C(L), dg_C(R), p, y)));
    leave(sv); return out;
}

/* ---------------- the other schemas (§83.5) ---------------- */
RefId equiv_maps(uint64_t l, uint64_t m) {
    Keying sv = enter(30, l, m, 0, 0); Tele T = { 0 };
    uint64_t n = mx(l, m);
    RefId X = P(&T, U(l), l + 1), Y = P(&T, U(m), m + 1), e = P(&T, mk_equiv(l, m, X, Y), n);
    RefId c = equiv_map(l, m, X, Y, e);
    TermVarId y1 = var(Y), y2 = var(Y), x = var(X);
    RefId d = mk_lam_lv(m, y1, Y, mk_fst(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y1)))));
    RefId k = mk_lam_lv(m, y2, Y, mk_snd(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y2)))));
    RefId y0 = mk_app(c, ref_var(x)), Fib = mk_fib(l, m, X, Y, c, y0), w = pair(n, Fib, ref_var(x), refl(m, Y, y0));
    RefId ctr = equiv_contr(l, m, X, Y, e, y0);
    DimVarId i = dim();
    RefId h = mk_lam_lv(l, x, X, mk_plam(i, mk_fst(papp(n, Fib, mk_fst(ctr), w, mk_app(mk_snd(ctr), w), iv_var(i)))));
    RefId out = close(&T, maps_pack(l, m, X, Y, c, d, h, k));
    leave(sv); return out;
}
typedef struct { uint64_t b; RefId B, C, D, Cut; } CutCx;
/* P(z', v') = Π(u' : C = z'). (D, u'·v'⁻¹, refl D) = (z', u', v') in Cut */
static RefId m_cut(uint64_t l, RefId A, RefId a, RefId z, RefId v, const void *cxp) {
    const CutCx *c = cxp; RefId Cz = path(l, A, c->C, z); TermVarId u = var(Cz); RefId uv = ref_var(u);
    RefId gf = pair(l, c->Cut, c->D, pair(l, tail(c->Cut, c->D), cat(l, A, c->C, z, c->D, uv, rev(l, A, c->D, z, v)), refl(l, A, c->D)));
    return mk_pi_lv(l, l, u, Cz, path(l, c->Cut, gf, pair(l, c->Cut, z, pair(l, tail(c->Cut, z), uv, v))));
}
RefId cut_maps(uint64_t b) {
    Keying sv = enter(31, b, 0, 0, 0); Tele T = { 0 };
    RefId B = P(&T, U(b), b + 1), C = P(&T, B, b), D = P(&T, B, b);
    TermVarId z = var(B); RefId Cz = path(b, B, C, ref_var(z)), Dz = path(b, B, D, ref_var(z)); TermVarId u = var(Cz);
    RefId Cut = mk_sigma_lv(b, b, z, B, mk_sigma_lv(b, b, u, Cz, Dz)), PCD = path(b, B, C, D);
    TermVarId w = var(Cut); RefId wv = ref_var(w), zw = mk_fst(wv), uw = mk_fst(mk_snd(wv)), vw = mk_snd(mk_snd(wv));
    RefId f = mk_lam_lv(b, w, Cut, cat(b, B, C, zw, D, uw, rev(b, B, D, zw, vw)));
    TermVarId hv = var(PCD);
    RefId g = mk_lam_lv(b, hv, PCD, pair(b, Cut, D, pair(b, tail(Cut, D), ref_var(hv), refl(b, B, D))));
    RefId Ri = runinv(b);                                          /* h·refl⁻¹ = h */
    TermVarId hk = var(PCD);
    RefId k = mk_lam_lv(b, hk, PCD, APPN(Ri, B, C, D, ref_var(hk)));
    CutCx cx = { b, B, C, D, Cut };
    TermVarId ub = var(PCD); DimVarId i = dim();
    RefId X0 = cat(b, B, C, D, D, ref_var(ub), rev(b, B, D, D, refl(b, B, D)));
    RefId base = mk_lam_lv(b, ub, PCD, mk_plam(i, pair(b, Cut, D, pair(b, tail(Cut, D), papp(b, PCD, X0, ref_var(ub), APPN(Ri, B, C, D, ref_var(ub)), iv_var(i)), refl(b, B, D)))));
    TermVarId w2 = var(Cut); RefId w2v = ref_var(w2);
    RefId h = mk_lam_lv(b, w2, Cut, mk_app(J(b, B, D, motive(b, B, D, m_cut, &cx), base, mk_fst(w2v), mk_snd(mk_snd(w2v))), mk_fst(mk_snd(w2v))));
    RefId out = close(&T, maps_pack(b, b, Cut, PCD, f, g, h, k));
    leave(sv); return out;
}
RefId fibre_maps(uint64_t b, uint64_t r) {
    Keying sv = enter(32, b, r, 0, 0); Tele T = { 0 };
    uint64_t s = mx(b, r);
    RefId B = P(&T, U(b), b + 1);
    TermVarId x0 = var(B); RefId R = P(&T, mk_pi_lv(b, r + 1, x0, B, U(r)), mx(b, r + 1));
    TermVarId x1 = var(B); RefId k = P(&T, mk_pi_lv(b, r, x1, B, mk_contr(r, mk_app(R, ref_var(x1)))), s);
    TermVarId xs = var(B); RefId S = mk_sigma_lv(b, r, xs, B, mk_app(R, ref_var(xs)));
    TermVarId w = var(S), xb = var(B), w2 = var(S), xk = var(B);
    RefId f = mk_lam_lv(s, w, S, mk_fst(ref_var(w)));
    RefId g = mk_lam_lv(b, xb, B, pair(s, S, ref_var(xb), mk_fst(mk_app(k, ref_var(xb)))));
    RefId b2 = mk_fst(ref_var(w2)), r2 = mk_snd(ref_var(w2)), kb = mk_app(k, b2);
    DimVarId i = dim();
    RefId h = mk_lam_lv(s, w2, S, mk_plam(i, pair(s, S, b2, papp(r, mk_app(R, b2), mk_fst(kb), r2, mk_app(mk_snd(kb), r2), iv_var(i)))));
    RefId out = close(&T, maps_pack(s, b, S, B, f, g, h, mk_lam_lv(b, xk, B, refl(b, B, ref_var(xk)))));
    leave(sv); return out;
}

/* ---------------- source declarations: the right fold ---------------- */
static RefId fold(size_t n, const DiagNode *nd, RefId B, uint64_t lB, RefId o, uint64_t *r) {
    RefId D = B ? app2(dg_zero(lB), B, o) : mk_app(res_zero(lB), o);
    uint64_t lv = lB;
    for (size_t k = n; k-- > 0; ) {
        RefId Pk = path(nd[k].level, nd[k].A, nd[k].t, ref_var(nd[k].x));
        RefId Q = mk_lam_lv(nd[k].level, nd[k].x, nd[k].A, mk_lam_lv(nd[k].level, nd[k].e, Pk, D));
        D = B ? APPN(dg_node(nd[k].level, lB, lv), B, nd[k].A, nd[k].t, Q) : APPN(res_node(nd[k].level, lB, lv), nd[k].A, nd[k].t, Q);
        lv = mx(nd[k].level, lv);
    }
    *r = lv;
    return D;
}
RefId diagram_fold(size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o, uint64_t *r) { return fold(n, nodes, B, lB, o, r); }
RefId residual_fold(size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ, uint64_t *r) { return fold(n, nodes, 0, lZ, Z, r); }

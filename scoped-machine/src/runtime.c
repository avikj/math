/* runtime.c — the ordinary diagram values and actions (runtime.h).
 *
 * Emitters are host functions building ordinary terms with the existing
 * constructors; each recipe runs its emitters once per exact level tuple
 * (per machine lifetime) over keyed formals and keeps the open body and the
 * closed function. The emitters of Maps, the singleton, Diagram, zero and
 * node are those of the §96 witness (tests/review_runtime_nodes.c), so the
 * production node function is the witnessed term.
 */
#include "runtime.h"

static uint64_t mx(uint64_t a, uint64_t b) { return a > b ? a : b; }
static TermVarId var(RefId A) { return declare_term(A, fc_true()); }
static RefId app2(RefId f, RefId x, RefId y) { return mk_app(mk_app(f, x), y); }
static RefId tail(RefId S, RefId x) { return apply_term_binder(S, 0, 1, x); }
static RefId pair(uint64_t l, RefId S, RefId x, RefId y) { return mk_pair_at_lv(l, S, x, y); }
static RefId path(uint64_t l, RefId A, RefId x, RefId y) { return mk_path_const(l, A, x, y); }
static RefId papp(uint64_t l, RefId A, RefId x, RefId y, RefId p, IntervalId s) { return mk_papp_const(l, A, x, y, p, s); }
static RefId cat(uint64_t l, RefId A, RefId x, RefId y, RefId z, RefId p, RefId q) { return mk_path_concat(l, A, x, y, z, p, q); }
static RefId rev(uint64_t l, RefId A, RefId x, RefId y, RefId p) { return mk_path_rev(l, A, x, y, p); }
static RefId refl(uint64_t l, RefId A, RefId a) { return mk_refl(l, A, a); }

/* ---------------- projections ---------------- */
RefId rt_c(RefId M) { return mk_fst(M); }
RefId rt_d(RefId M) { return mk_fst(mk_snd(M)); }
RefId rt_h(RefId M) { return mk_fst(mk_snd(mk_snd(M))); }
RefId rt_k(RefId M) { return mk_snd(mk_snd(mk_snd(M))); }
RefId rt_dg_C(RefId D) { return mk_fst(D); }
RefId rt_dg_R(RefId D, RefId y) { return mk_app(mk_fst(mk_snd(D)), y); }
RefId rt_dg_M(RefId D, RefId y) { return mk_app(mk_snd(mk_snd(D)), y); }
RefId rt_res_Z(RefId P) { return mk_fst(P); }
RefId rt_res_X(RefId P) { return mk_fst(mk_snd(P)); }
RefId rt_res_M(RefId P) { return mk_snd(mk_snd(P)); }

/* ---------------- emitters (§83.1–§83.3, §96) ---------------- */
static RefId e_maps_type(uint64_t a, uint64_t b, RefId A, RefId B) {
    uint64_t m = mx(a, b);
    RefId F = mk_fun(a, b, A, B), G = mk_fun(b, a, B, A);
    TermVarId f = var(F), g = var(G), x = var(A), y = var(B);
    RefId H = mk_pi_lv(a, a, x, A, path(a, A, mk_app(ref_var(g), mk_app(ref_var(f), ref_var(x))), ref_var(x)));
    RefId K = mk_pi_lv(b, b, y, B, path(b, B, mk_app(ref_var(f), mk_app(ref_var(g), ref_var(y))), ref_var(y)));
    TermVarId h = var(H);
    return mk_sigma_lv(m, m, f, F, mk_sigma_lv(m, m, g, G, mk_sigma_lv(a, b, h, H, K)));
}
static RefId e_maps_pack(uint64_t a, uint64_t b, RefId A, RefId B, RefId f, RefId g, RefId h, RefId k) {
    uint64_t m = mx(a, b); RefId M = e_maps_type(a, b, A, B), M1 = tail(M, f), M2 = tail(M1, g);
    return pair(m, M, f, pair(m, M1, g, pair(m, M2, h, k)));
}
static RefId e_maps_id(uint64_t a, RefId A) {
    TermVarId x = var(A); RefId id = mk_id_fun(a, A);
    RefId h = mk_lam_lv(a, x, A, refl(a, A, ref_var(x)));
    return e_maps_pack(a, a, A, A, id, id, h, h);
}
static RefId e_ap(uint64_t a, RefId A, RefId x, RefId y, RefId f, RefId p) {
    DimVarId i = declare_dim();
    return mk_plam(i, mk_app(f, papp(a, A, x, y, p, iv_var(i))));
}
/* E : A ↔ B, F : B ↔ C; both homotopies retained as ordinary fields */
static RefId e_maps_comp(uint64_t a, uint64_t b, uint64_t c, RefId A, RefId B, RefId C, RefId E, RefId F) {
    RefId f = rt_c(E), g = rt_d(E), h = rt_h(E), k = rt_k(E);
    RefId u = rt_c(F), v = rt_d(F), H = rt_h(F), K = rt_k(F);
    TermVarId x = var(A), z = var(C); RefId xv = ref_var(x), zv = ref_var(z);
    RefId fx = mk_app(f, xv), vz = mk_app(v, zv);
    RefId forward = mk_lam_lv(a, x, A, mk_app(u, fx));
    RefId reverse = mk_lam_lv(c, z, C, mk_app(g, vz));
    RefId vufx = mk_app(v, mk_app(u, fx)), gvufx = mk_app(g, vufx), gfx = mk_app(g, fx);
    RefId h0 = e_ap(b, B, vufx, fx, g, mk_app(H, fx));
    RefId hh = mk_lam_lv(a, x, A, cat(a, A, gvufx, gfx, xv, h0, mk_app(h, xv)));
    RefId fgvz = mk_app(f, mk_app(g, vz)), ufgvz = mk_app(u, fgvz), uvz = mk_app(u, vz);
    RefId k0 = e_ap(b, B, fgvz, vz, u, mk_app(k, vz));
    RefId kk = mk_lam_lv(c, z, C, cat(c, C, ufgvz, uvz, zv, k0, mk_app(K, zv)));
    return e_maps_pack(a, c, A, C, forward, reverse, hh, kk);
}
/* §83.2: D open in x, e; returns Maps(S_D, Z) and S_D, Z */
static RefId e_singleton(uint64_t a, uint64_t r, RefId A, RefId t, TermVarId x, TermVarId e, RefId D, RefId *S_out, RefId *Z_out) {
    uint64_t s = mx(a, r); RefId Ex = path(a, A, t, ref_var(x));
    RefId S = mk_sigma_lv(a, s, x, A, mk_sigma_lv(a, r, e, Ex, D));
    ScopeId DS = capture_term2(x, A, a, e, Ex, a, D, mk_universe(r), r + 1, fc_true());
    RefId rf = refl(a, A, t), Z;
    /* simultaneous substitution: images are not rewritten by the map */
    MapBuilder images; mapb_init(&images); mapb_term(&images, x, t); mapb_term(&images, e, rf);
    Z = reindex(D, mapb_finish(&images));
    TermVarId w = var(S), z = var(Z); RefId wv = ref_var(w), zv = ref_var(z);
    RefId wx = mk_fst(wv), we = mk_fst(mk_snd(wv)), wz = mk_snd(mk_snd(wv));
    RefId down = mk_lam_lv(s, w, S, mk_down(r, a, A, t, DS, wx, we, wz));
    RefId up = mk_lam_lv(r, z, Z, pair(s, S, t, pair(s, tail(S, t), rf, zv)));
    DimVarId i = declare_dim(), j = declare_dim(), q = declare_dim();
    RefId xi = papp(a, A, t, wx, we, iv_var(i));
    RefId ei = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_var(i), iv_var(j))));
    RefId xq = papp(a, A, t, wx, we, iv_negate(iv_var(q)));
    RefId eq = mk_plam(j, papp(a, A, t, wx, we, iv_meet(iv_negate(iv_var(q)), iv_var(j))));
    MapBuilder qi; mapb_init(&qi); mapb_term(&qi, x, xq); mapb_term(&qi, e, eq);
    RefId Dq = reindex(D, mapb_finish(&qi)), empty = mk_system(0, NULL, NULL);
    RefId zi = mk_fill_at(r, q, Dq, fc_false(), empty, wz, iv_negate(iv_var(i)));
    RefId h = mk_lam_lv(s, w, S, mk_plam(i, pair(s, S, xi, pair(s, tail(S, xi), ei, zi))));
    RefId k = mk_lam_lv(r, z, Z, mk_plam(i, mk_fill_at(r, q, Z, fc_false(), empty, zv, iv_negate(iv_var(i)))));
    if (S_out) *S_out = S;
    if (Z_out) *Z_out = Z;
    return e_maps_pack(s, r, S, Z, down, up, h, k);
}
static RefId e_diagram_type(uint64_t b, uint64_t r, RefId B) {
    uint64_t rl = mx(b, r + 1), ml = mx(b, r);
    TermVarId c = var(B), y = var(B);
    RefId RT = mk_pi_lv(b, r + 1, y, B, mk_universe(r)); TermVarId R = var(RT);
    RefId M = mk_pi_lv(b, ml, y, B, e_maps_type(r, b, mk_app(ref_var(R), ref_var(y)), path(b, B, ref_var(c), ref_var(y))));
    return mk_sigma_lv(b, rl, c, B, mk_sigma_lv(rl, ml, R, RT, M));
}
static RefId e_diagram_pack(uint64_t b, uint64_t r, RefId B, RefId c, RefId R, RefId M) {
    uint64_t dl = mx(b, r + 1); RefId D = e_diagram_type(b, r, B);
    return pair(dl, D, c, pair(dl, tail(D, c), R, M));
}
static RefId e_zero(uint64_t b, RefId B, RefId c) {
    TermVarId y = var(B); RefId P = path(b, B, c, ref_var(y));
    return e_diagram_pack(b, b, B, c, mk_lam_lv(b, y, B, P), mk_lam_lv(b, y, B, e_maps_id(b, P)));
}
static RefId e_res_type(uint64_t z, uint64_t r) {
    TermVarId Z = var(mk_universe(z)), X = var(mk_universe(r));
    return mk_sigma_lv(z + 1, mx(r + 1, z), Z, mk_universe(z), mk_sigma_lv(r + 1, mx(r, z), X, mk_universe(r), e_maps_type(r, z, ref_var(X), ref_var(Z))));
}
static RefId e_res_pack(uint64_t z, uint64_t r, RefId Z, RefId X, RefId M) {
    RefId T = e_res_type(z, r);
    return pair(mx(z + 1, r + 1), T, Z, pair(mx(r + 1, z), tail(T, Z), X, M));
}

/* ---------------- path induction and the K words (§83.4) ---------------- */
/* J(P, d, b, p) = coe^i P(p@i, ⟨j⟩ p@(i∧j)) d, P : (x:A) → (a = x) → U_m */
static RefId e_J(uint64_t l, uint64_t m, RefId A, RefId a, RefId P, RefId d, RefId b, RefId p) {
    DimVarId i = declare_dim(), j = declare_dim();
    RefId pi = papp(l, A, a, b, p, iv_var(i));
    RefId ej = mk_plam(j, papp(l, A, a, b, p, iv_meet(iv_var(i), iv_var(j))));
    return mk_coe_at(m, i, app2(P, pi, ej), d);
}
/* a motive λ(x:A) λ(e : a = x). T, with T : U_m built by the callback */
typedef RefId (*MotiveBody)(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx);
static RefId e_motive(uint64_t l, RefId A, RefId a, MotiveBody body, void *cx) {
    TermVarId x = var(A); RefId Ax = path(l, A, a, ref_var(x));
    TermVarId e = var(Ax);
    return mk_lam_lv(l, x, A, mk_lam_lv(l, e, Ax, body(l, A, a, ref_var(x), ref_var(e), cx)));
}
/* words over refl at a: R, V(w), C(v, w) */
typedef struct Word { char op; const struct Word *a, *b; } Word;
static const Word W_R = { 'R', NULL, NULL };
static RefId w_term(uint64_t l, RefId A, RefId a, const Word *w) {
    if (w->op == 'R') return refl(l, A, a);
    if (w->op == 'V') return rev(l, A, a, a, w_term(l, A, a, w->a));
    return cat(l, A, a, a, a, w_term(l, A, a, w->a), w_term(l, A, a, w->b));
}
/* K(w) : Path_{a = a}(w, refl a) */
static RefId w_K(uint64_t l, RefId A, RefId a, const Word *w) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a);
    if (w->op == 'R') return refl(l, Paa, ra);
    DimVarId k = declare_dim();
    if (w->op == 'V') {
        RefId Kv = w_K(l, A, a, w->a);
        return mk_plam(k, rev(l, A, a, a, papp(l, Paa, w_term(l, A, a, w->a), ra, Kv, iv_var(k))));
    }
    RefId Kv = w_K(l, A, a, w->a), Kw = w_K(l, A, a, w->b);
    RefId tv = w_term(l, A, a, w->a), tw = w_term(l, A, a, w->b);
    RefId mid = mk_plam(k, cat(l, A, a, a, a, papp(l, Paa, tv, ra, Kv, iv_var(k)), papp(l, Paa, tw, ra, Kw, iv_var(k))));
    /* K(refl·refl)@k@i = fill^j A [(i=0) ↦ a, (i=1) ↦ a] a (¬k) */
    DimVarId k2 = declare_dim(), i = declare_dim(), j = declare_dim();
    RefId Kc = mk_plam(k2, mk_plam(i, mk_fill_at(l, j, A, fc_join(fc_lit(i, 0), fc_lit(i, 1)), a, a, iv_negate(iv_var(k2)))));
    RefId rr = cat(l, A, a, a, a, ra, ra);
    return cat(l, Paa, w_term(l, A, a, w), rr, ra, mid, Kc);
}
/* the equality of two base words: K(u)·K(v)⁻¹ */
static RefId w_eq(uint64_t l, RefId A, RefId a, const Word *u, const Word *v) {
    RefId Paa = path(l, A, a, a), ra = refl(l, A, a), tu = w_term(l, A, a, u), tv = w_term(l, A, a, v);
    return cat(l, Paa, tu, ra, tv, w_K(l, A, a, u), rev(l, Paa, tv, ra, w_K(l, A, a, v)));
}

/* ---------------- recipes ---------------- */
static struct {
    pthread_mutex_t mu; pthread_once_t once;
    uint64_t gen; bool live;
    WordMap idx; VEC(Recipe *) all;
} RT = { .once = PTHREAD_ONCE_INIT };
static void rt_once(void) {
    pthread_mutexattr_t at; pthread_mutexattr_init(&at); pthread_mutexattr_settype(&at, PTHREAD_MUTEX_RECURSIVE);
    pthread_mutex_init(&RT.mu, &at); pthread_mutexattr_destroy(&at);
}
static void rt_clear_locked(void) {
    if (!RT.live) return;
    for (size_t k = 0; k < RT.all.len; k++) free(RT.all.data[k]);
    vec_free(&RT.all); wordmap_free(&RT.idx);
    RT.live = false;
}
void rt_free(void) { pthread_once(&RT.once, rt_once); pthread_mutex_lock(&RT.mu); rt_clear_locked(); pthread_mutex_unlock(&RT.mu); }

static TermVarId formal(Recipe *R, RefId type, uint64_t level) {
    require(R->n < RT_MAXF, "recipe arity");
    KeyWord k[7] = { { KW_CONST, 8100 }, { KW_CONST, R->kind }, { KW_CONST, R->lv[0] }, { KW_CONST, R->lv[1] }, { KW_CONST, R->lv[2] }, { KW_CONST, R->lv[3] }, { KW_CONST, R->n } };
    TermVarId x = fresh_term_keyed(k, 7, type);
    R->formal[R->n] = x; R->ftype[R->n] = type; R->flevel[R->n] = level; R->n++;
    return x;
}
#define F(T, L) ref_var(formal(R, (T), (L)))
#define U(l) mk_universe(l)
static const Recipe *rec(RecipeKind k, uint64_t a, uint64_t b, uint64_t c, uint64_t d) { return rt_recipe(k, a, b, c, d); }
static RefId apply(const Recipe *r, size_t n, const RefId *args) { require(n == r->n, "recipe application arity"); return rt_apply(r, args); }
#define APPLY(r, ...) apply((r), sizeof((RefId[]){ __VA_ARGS__ }) / sizeof(RefId), (RefId[]){ __VA_ARGS__ })

/* motive bodies of the groupoid laws */
static RefId mb_lunit(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) { (void)cx; return path(l, path(l, A, a, x), cat(l, A, a, a, x, refl(l, A, a), e), e); }
static RefId mb_runit(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) { (void)cx; return path(l, path(l, A, a, x), cat(l, A, a, x, x, e, refl(l, A, x)), e); }
static RefId mb_rinv(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) { (void)cx; return path(l, path(l, A, a, a), cat(l, A, a, x, a, e, rev(l, A, a, x, e)), refl(l, A, a)); }
static RefId mb_linv(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) { (void)cx; return path(l, path(l, A, x, x), cat(l, A, x, a, x, rev(l, A, a, x, e), e), refl(l, A, x)); }
/* assoc: P3(z, e3) = ((refl·refl)·e3 = refl·(refl·e3)) */
static RefId mb_assoc3(uint64_t l, RefId A, RefId a, RefId z, RefId e3, void *cx) {
    (void)cx; RefId ra = refl(l, A, a);
    return path(l, path(l, A, a, z), cat(l, A, a, a, z, cat(l, A, a, a, a, ra, ra), e3), cat(l, A, a, a, z, ra, cat(l, A, a, a, z, ra, e3)));
}
/* P2(y, e2) = Π(d:A) Π(r : y = d). ((refl·e2)·r = refl·(e2·r)) */
static RefId mb_assoc2(uint64_t l, RefId A, RefId a, RefId y, RefId e2, void *cx) {
    (void)cx; RefId ra = refl(l, A, a);
    TermVarId d = var(A); RefId dv = ref_var(d); TermVarId r = var(path(l, A, y, dv)); RefId rv = ref_var(r);
    RefId T = path(l, path(l, A, a, dv), cat(l, A, a, y, dv, cat(l, A, a, a, y, ra, e2), rv), cat(l, A, a, a, dv, ra, cat(l, A, a, y, dv, e2, rv)));
    return mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, path(l, A, y, dv), T));
}
/* P1(x, e) = Π(c:A) Π(q : x = c) Π(d:A) Π(r : c = d). ((e·q)·r = e·(q·r)) */
static RefId mb_assoc1(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) {
    (void)cx;
    TermVarId c = var(A); RefId cv = ref_var(c); TermVarId q = var(path(l, A, x, cv)); RefId qv = ref_var(q);
    TermVarId d = var(A); RefId dv = ref_var(d); TermVarId r = var(path(l, A, cv, dv)); RefId rv = ref_var(r);
    RefId T = path(l, path(l, A, a, dv), cat(l, A, a, cv, dv, cat(l, A, a, x, cv, e, qv), rv), cat(l, A, a, x, dv, e, cat(l, A, x, cv, dv, qv, rv)));
    return mk_pi_lv(l, l, c, A, mk_pi_lv(l, l, q, path(l, A, x, cv), mk_pi_lv(l, l, d, A, mk_pi_lv(l, l, r, path(l, A, cv, dv), T))));
}
/* a one-path law Π(A) Π(a b) Π(p : a = b). P(b, p), by J on p at the base K(u)·K(v)⁻¹ */
static void law1(Recipe *R, MotiveBody mb, const Word *u, const Word *v) {
    uint64_t l = R->lv[0];
    RefId A = F(U(l), l + 1), a = F(A, l), b = F(A, l), p = F(path(l, A, a, b), l);
    RefId P = e_motive(l, A, a, mb, NULL);
    R->body = e_J(l, l, A, a, P, w_eq(l, A, a, u, v), b, p);
    R->body_type = mb(l, A, a, b, p, NULL); R->body_level = l;
}

/* CUT_TO_PATH round trips */
typedef struct { uint64_t b; RefId B, C, D, Cut, Pk; } CutCx;
/* k-motive P(x, e) = (e·refl_x⁻¹ = e) at base point C */
static RefId mb_cutk(uint64_t l, RefId A, RefId a, RefId x, RefId e, void *cx) {
    (void)cx; return path(l, path(l, A, a, x), cat(l, A, a, x, x, e, rev(l, A, x, x, refl(l, A, x))), e);
}
/* k(h) = J(P_k, K(refl·refl⁻¹)·K(refl)⁻¹, D, h) : h·refl_D⁻¹ = h */
static RefId cut_k(const CutCx *c, RefId h) {
    Word u = { 'C', &W_R, &(Word){ 'V', &W_R, NULL } };
    return e_J(c->b, c->b, c->B, c->C, c->Pk, w_eq(c->b, c->B, c->C, &u, &W_R), c->D, h);
}
/* h-motive at base point D: P(z', v') = Π(u' : C = z'). (D, u'·v'⁻¹, refl D) = (z', u', v') in Cut */
static RefId mb_cuth(uint64_t l, RefId A, RefId a, RefId z, RefId v, void *cxp) {
    const CutCx *c = cxp; (void)a;
    RefId Cz = path(l, A, c->C, z);
    TermVarId u = var(Cz); RefId uv = ref_var(u);
    RefId gf = pair(l, c->Cut, c->D, pair(l, tail(c->Cut, c->D), cat(l, A, c->C, z, c->D, uv, rev(l, A, c->D, z, v)), refl(l, A, c->D)));
    RefId wz = pair(l, c->Cut, z, pair(l, tail(c->Cut, z), uv, v));
    return mk_pi_lv(l, l, u, Cz, path(l, c->Cut, gf, wz));
}

static void build(Recipe *R) {
    uint64_t *lv = R->lv;
    switch (R->kind) {
    case RK_MAPS_TYPE: {
        uint64_t a = lv[0], b = lv[1];
        RefId X = F(U(a), a + 1), Y = F(U(b), b + 1);
        R->body = e_maps_type(a, b, X, Y); R->body_type = U(mx(a, b)); R->body_level = mx(a, b) + 1; break; }
    case RK_MAPS_ID: {
        uint64_t a = lv[0]; RefId X = F(U(a), a + 1);
        R->body = e_maps_id(a, X); R->body_type = e_maps_type(a, a, X, X); R->body_level = a; break; }
    case RK_MAPS_COMP: {
        uint64_t a = lv[0], b = lv[1], c = lv[2];
        RefId X = F(U(a), a + 1), Y = F(U(b), b + 1), Z = F(U(c), c + 1);
        RefId E = F(e_maps_type(a, b, X, Y), mx(a, b)), Fm = F(e_maps_type(b, c, Y, Z), mx(b, c));
        R->body = e_maps_comp(a, b, c, X, Y, Z, E, Fm); R->body_type = e_maps_type(a, c, X, Z); R->body_level = mx(a, c); break; }
    case RK_MAPS_INV: {
        uint64_t a = lv[0], b = lv[1];
        RefId X = F(U(a), a + 1), Y = F(U(b), b + 1), E = F(e_maps_type(a, b, X, Y), mx(a, b));
        R->body = e_maps_pack(b, a, Y, X, rt_d(E), rt_c(E), rt_k(E), rt_h(E)); R->body_type = e_maps_type(b, a, Y, X); R->body_level = mx(a, b); break; }
    case RK_SINGLETON: {
        uint64_t a = lv[0], r = lv[1], s = mx(a, r);
        RefId A = F(U(a), a + 1), t = F(A, a);
        TermVarId x0 = var(A); RefId Ex0 = path(a, A, t, ref_var(x0)); TermVarId e0 = var(Ex0);
        RefId DT = mk_pi_lv(a, mx(a, r + 1), x0, A, mk_pi_lv(a, r + 1, e0, Ex0, U(r)));
        RefId D = F(DT, mx(a, r + 1));
        TermVarId x = var(A); TermVarId e = var(path(a, A, t, ref_var(x)));
        RefId S, Z;
        R->body = e_singleton(a, r, A, t, x, e, app2(D, ref_var(x), ref_var(e)), &S, &Z);
        R->body_type = e_maps_type(s, r, S, Z); R->body_level = s; break; }
    case RK_DIAGRAM_TYPE: {
        uint64_t b = lv[0], r = lv[1]; RefId B = F(U(b), b + 1);
        R->body = e_diagram_type(b, r, B); R->body_type = U(mx(b, r + 1)); R->body_level = mx(b, r + 1) + 1; break; }
    case RK_ZERO: {
        uint64_t b = lv[0]; RefId B = F(U(b), b + 1), c = F(B, b);
        R->body = e_zero(b, B, c); R->body_type = e_diagram_type(b, b, B); R->body_level = mx(b, b + 1); break; }
    case RK_NODE: {
        /* §96.2: node_{a,b,r} B A t Q */
        uint64_t a = lv[0], b = lv[1], r = lv[2], s = mx(a, r), dl = mx(b, r + 1);
        RefId B = F(U(b), b + 1), A = F(U(a), a + 1), t = F(A, a);
        TermVarId qx = var(A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(qEx);
        RefId DT = e_diagram_type(b, r, B);
        RefId QT = mk_pi_lv(a, mx(a, dl), qx, A, mk_pi_lv(a, dl, qe, qEx, DT));
        RefId Q = F(QT, mx(a, dl));
        RefId Q0 = app2(Q, t, refl(a, A, t)), c = rt_dg_C(Q0);
        TermVarId x = var(A); RefId Ex = path(a, A, t, ref_var(x)); TermVarId e = var(Ex);
        TermVarId y = var(B); RefId yv = ref_var(y);
        RefId D = rt_dg_R(app2(Q, ref_var(x), ref_var(e)), yv);
        RefId S, Z, P = path(b, B, c, yv);
        RefId E = e_singleton(a, r, A, t, x, e, D, &S, &Z), Fm = rt_dg_M(Q0, yv);
        RefId Rf = mk_lam_lv(b, y, B, S);
        RefId M = mk_lam_lv(b, y, B, e_maps_comp(s, r, b, S, Z, P, E, Fm));
        R->body = e_diagram_pack(b, s, B, c, Rf, M); R->body_type = e_diagram_type(b, s, B); R->body_level = mx(b, s + 1); break; }
    case RK_LUNIT: law1(R, mb_lunit, &(Word){ 'C', &W_R, &W_R }, &W_R); break;
    case RK_RUNIT: law1(R, mb_runit, &(Word){ 'C', &W_R, &W_R }, &W_R); break;
    case RK_RINV: law1(R, mb_rinv, &(Word){ 'C', &W_R, &(Word){ 'V', &W_R, NULL } }, &W_R); break;
    case RK_LINV: law1(R, mb_linv, &(Word){ 'C', &(Word){ 'V', &W_R, NULL }, &W_R }, &W_R); break;
    case RK_ASSOC: {
        /* path induction on p, then q, then r (left to right), later data under Π */
        uint64_t l = lv[0];
        RefId A = F(U(l), l + 1), a = F(A, l), b = F(A, l), c = F(A, l), d = F(A, l);
        RefId p = F(path(l, A, a, b), l), q = F(path(l, A, b, c), l), r = F(path(l, A, c, d), l);
        Word RR = { 'C', &W_R, &W_R };
        Word u = { 'C', &RR, &W_R }, v = { 'C', &W_R, &RR };
        RefId P3 = e_motive(l, A, a, mb_assoc3, NULL), P2 = e_motive(l, A, a, mb_assoc2, NULL), P1 = e_motive(l, A, a, mb_assoc1, NULL);
        /* d2 = λd'' r''. J(P3, K(u)·K(v)⁻¹, d'', r'') */
        TermVarId d2 = var(A); TermVarId r2 = var(path(l, A, a, ref_var(d2)));
        RefId D2 = mk_lam_lv(l, d2, A, mk_lam_lv(l, r2, path(l, A, a, ref_var(d2)), e_J(l, l, A, a, P3, w_eq(l, A, a, &u, &v), ref_var(d2), ref_var(r2))));
        /* d1 = λc' q' d' r'. J(P2, d2, c', q') d' r' */
        TermVarId c1 = var(A); TermVarId q1 = var(path(l, A, a, ref_var(c1)));
        TermVarId d1 = var(A); TermVarId r1 = var(path(l, A, ref_var(c1), ref_var(d1)));
        RefId inner = app2(e_J(l, l, A, a, P2, D2, ref_var(c1), ref_var(q1)), ref_var(d1), ref_var(r1));
        RefId D1 = mk_lam_lv(l, c1, A, mk_lam_lv(l, q1, path(l, A, a, ref_var(c1)), mk_lam_lv(l, d1, A, mk_lam_lv(l, r1, path(l, A, ref_var(c1), ref_var(d1)), inner))));
        R->body = app2(app2(e_J(l, l, A, a, P1, D1, b, p), c, q), d, r);
        R->body_type = path(l, path(l, A, a, d), cat(l, A, a, c, d, cat(l, A, a, b, c, p, q), r), cat(l, A, a, b, d, p, cat(l, A, b, c, d, q, r)));
        R->body_level = l; break; }
    case RK_MID: {
        /* §83.4: f(q) = p⁻¹·q, g(s) = p·s with both inverse paths */
        uint64_t l = lv[0];
        RefId B = F(U(l), l + 1), a = F(B, l), c = F(B, l), p = F(path(l, B, a, c), l), y = F(B, l);
        const Recipe *As = rec(RK_ASSOC, l, 0, 0, 0), *Ri = rec(RK_RINV, l, 0, 0, 0), *Li = rec(RK_LINV, l, 0, 0, 0), *Lu = rec(RK_LUNIT, l, 0, 0, 0);
        RefId Pay = path(l, B, a, y), Pcy = path(l, B, c, y), Paa = path(l, B, a, a), Pcc = path(l, B, c, c);
        RefId pinv = rev(l, B, a, c, p);
        TermVarId vq = var(Pay), vs = var(Pcy); RefId qv = ref_var(vq), sv = ref_var(vs);
        RefId f = mk_lam_lv(l, vq, Pay, cat(l, B, c, a, y, pinv, qv));
        RefId g = mk_lam_lv(l, vs, Pcy, cat(l, B, a, c, y, p, sv));
        /* h(q) = assoc(p,p⁻¹,q)⁻¹ · ap(λv.v·q)(rinv p) · lunit(q) */
        {   RefId X0 = cat(l, B, a, c, y, p, cat(l, B, c, a, y, pinv, qv));
            RefId pp = cat(l, B, a, c, a, p, pinv);
            RefId X1 = cat(l, B, a, a, y, pp, qv), X2 = cat(l, B, a, a, y, refl(l, B, a), qv);
            RefId s1 = rev(l, Pay, X1, X0, APPLY(As, B, a, c, a, y, p, pinv, qv));
            TermVarId vv = var(Paa);
            RefId s2 = e_ap(l, Paa, pp, refl(l, B, a), mk_lam_lv(l, vv, Paa, cat(l, B, a, a, y, ref_var(vv), qv)), APPLY(Ri, B, a, c, p));
            RefId s3 = APPLY(Lu, B, a, y, qv);
            RefId hq = cat(l, Pay, X0, X1, qv, s1, cat(l, Pay, X1, X2, qv, s2, s3));
            TermVarId vq2 = var(Pay);
            MapBuilder mb; mapb_init(&mb); mapb_term(&mb, vq, ref_var(vq2));
            RefId h = mk_lam_lv(l, vq2, Pay, reindex(hq, mapb_finish(&mb)));
            /* k(s) = assoc(p⁻¹,p,s)⁻¹ · ap(λv.v·s)(linv p) · lunit(s) */
            RefId Y0 = cat(l, B, c, a, y, pinv, cat(l, B, a, c, y, p, sv));
            RefId ip = cat(l, B, c, a, c, pinv, p);
            RefId Y1 = cat(l, B, c, c, y, ip, sv), Y2 = cat(l, B, c, c, y, refl(l, B, c), sv);
            RefId t1 = rev(l, Pcy, Y1, Y0, APPLY(As, B, c, a, c, y, pinv, p, sv));
            TermVarId vw = var(Pcc);
            RefId t2 = e_ap(l, Pcc, ip, refl(l, B, c), mk_lam_lv(l, vw, Pcc, cat(l, B, c, c, y, ref_var(vw), sv)), APPLY(Li, B, a, c, p));
            RefId t3 = APPLY(Lu, B, c, y, sv);
            RefId ks = cat(l, Pcy, Y0, Y1, sv, t1, cat(l, Pcy, Y1, Y2, sv, t2, t3));
            TermVarId vs2 = var(Pcy);
            MapBuilder mk; mapb_init(&mk); mapb_term(&mk, vs, ref_var(vs2));
            RefId k = mk_lam_lv(l, vs2, Pcy, reindex(ks, mapb_finish(&mk)));
            R->body = e_maps_pack(l, l, Pay, Pcy, f, g, h, k); }
        R->body_type = e_maps_type(l, l, Pay, Pcy); R->body_level = l; break; }
    case RK_ACTION: {
        /* §83.4: comp(comp(M_L(y), mid(p, y)), M_R(y)⁻¹) : Maps(R_L y, R_R y) */
        uint64_t b = lv[0], rl = lv[1], rr = lv[2];
        RefId B = F(U(b), b + 1);
        RefId L = F(e_diagram_type(b, rl, B), mx(b, rl + 1)), Rd = F(e_diagram_type(b, rr, B), mx(b, rr + 1));
        RefId CL = rt_dg_C(L), CR = rt_dg_C(Rd);
        RefId p = F(path(b, B, CL, CR), b), y = F(B, b);
        RefId RLy = rt_dg_R(L, y), RRy = rt_dg_R(Rd, y), PL = path(b, B, CL, y), PR = path(b, B, CR, y);
        RefId MID = APPLY(rec(RK_MID, b, 0, 0, 0), B, CL, CR, p, y);
        RefId MRi = APPLY(rec(RK_MAPS_INV, rr, b, 0, 0), RRy, PR, rt_dg_M(Rd, y));
        RefId C1 = APPLY(rec(RK_MAPS_COMP, rl, b, b, 0), RLy, PL, PR, rt_dg_M(L, y), MID);
        R->body = APPLY(rec(RK_MAPS_COMP, rl, b, rr, 0), RLy, PR, RRy, C1, MRi);
        R->body_type = e_maps_type(rl, rr, RLy, RRy); R->body_level = mx(rl, rr); break; }
    case RK_EQUIV_MAPS: {
        /* §83.5: c = fst e; d y = centre's point; k y = centre's path; h x = ap(fst)(contraction at (x, refl)) */
        uint64_t l = lv[0], m = lv[1], n = mx(l, m);
        RefId X = F(U(l), l + 1), Y = F(U(m), m + 1), e = F(mk_equiv(l, m, X, Y), n);
        RefId c = equiv_map(l, m, X, Y, e);
        TermVarId y1 = var(Y), y2 = var(Y), x = var(X);
        RefId d = mk_lam_lv(m, y1, Y, mk_fst(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y1)))));
        RefId k = mk_lam_lv(m, y2, Y, mk_snd(mk_fst(equiv_contr(l, m, X, Y, e, ref_var(y2)))));
        RefId y0 = mk_app(c, ref_var(x)), Fib = mk_fib(l, m, X, Y, c, y0);
        RefId w = pair(n, Fib, ref_var(x), refl(m, Y, y0));
        RefId ctr = equiv_contr(l, m, X, Y, e, y0), centre = mk_fst(ctr);
        RefId P = mk_app(mk_snd(ctr), w);
        DimVarId i = declare_dim();
        RefId h = mk_lam_lv(l, x, X, mk_plam(i, mk_fst(papp(n, Fib, centre, w, P, iv_var(i)))));
        R->body = e_maps_pack(l, m, X, Y, c, d, h, k); R->body_type = e_maps_type(l, m, X, Y); R->body_level = n; break; }
    case RK_CUT_MAPS: {
        /* §44 / §83.5: (z,u,v) ↦ u·v⁻¹ ; h ↦ (D, h, refl D); the path-space
         * round trip by J on h, the cut round trip by J on v (u under Π) */
        uint64_t b = lv[0];
        RefId B = F(U(b), b + 1), C = F(B, b), D = F(B, b);
        TermVarId z = var(B); RefId Cz = path(b, B, C, ref_var(z)), Dz = path(b, B, D, ref_var(z));
        TermVarId u = var(Cz);
        RefId Cut = mk_sigma_lv(b, b, z, B, mk_sigma_lv(b, b, u, Cz, Dz)), PCD = path(b, B, C, D);
        TermVarId w = var(Cut); RefId wv = ref_var(w);
        RefId zw = mk_fst(wv), uw = mk_fst(mk_snd(wv)), vw = mk_snd(mk_snd(wv));
        RefId f = mk_lam_lv(b, w, Cut, cat(b, B, C, zw, D, uw, rev(b, B, D, zw, vw)));
        TermVarId hv = var(PCD);
        RefId g = mk_lam_lv(b, hv, PCD, pair(b, Cut, D, pair(b, tail(Cut, D), ref_var(hv), refl(b, B, D))));
        CutCx cx = { b, B, C, D, Cut, 0 };
        cx.Pk = e_motive(b, B, C, mb_cutk, NULL);
        TermVarId hk = var(PCD);
        RefId k = mk_lam_lv(b, hk, PCD, cut_k(&cx, ref_var(hk)));
        RefId Ph = e_motive(b, B, D, mb_cuth, &cx);
        TermVarId ub = var(PCD); DimVarId i = declare_dim();
        RefId X0 = cat(b, B, C, D, D, ref_var(ub), rev(b, B, D, D, refl(b, B, D)));
        RefId base = mk_lam_lv(b, ub, PCD, mk_plam(i, pair(b, Cut, D, pair(b, tail(Cut, D), papp(b, PCD, X0, ref_var(ub), cut_k(&cx, ref_var(ub)), iv_var(i)), refl(b, B, D)))));
        TermVarId w2 = var(Cut); RefId w2v = ref_var(w2);
        RefId h = mk_lam_lv(b, w2, Cut, mk_app(e_J(b, b, B, D, Ph, base, mk_fst(w2v), mk_snd(mk_snd(w2v))), mk_fst(mk_snd(w2v))));
        R->body = e_maps_pack(b, b, Cut, PCD, f, g, h, k); R->body_type = e_maps_type(b, b, Cut, PCD); R->body_level = b; break; }
    case RK_FIBRE_MAPS: {
        /* §83.5 COLLAPSE_FIBRE: fst and b ↦ (b, centre); h(b,r) = ⟨i⟩(b, contraction(r)@i), k = refl */
        uint64_t b = lv[0], r = lv[1], s = mx(b, r);
        RefId B = F(U(b), b + 1);
        TermVarId x0 = var(B); RefId Rt = mk_pi_lv(b, r + 1, x0, B, U(r));
        RefId Rf = F(Rt, mx(b, r + 1));
        TermVarId x1 = var(B); RefId Kt = mk_pi_lv(b, r, x1, B, mk_contr(r, mk_app(Rf, ref_var(x1))));
        RefId k = F(Kt, s);
        TermVarId xs = var(B); RefId S = mk_sigma_lv(b, r, xs, B, mk_app(Rf, ref_var(xs)));
        TermVarId w = var(S), xb = var(B), w2 = var(S), xk = var(B);
        RefId f = mk_lam_lv(s, w, S, mk_fst(ref_var(w)));
        RefId g = mk_lam_lv(b, xb, B, pair(s, S, ref_var(xb), mk_fst(mk_app(k, ref_var(xb)))));
        RefId b2 = mk_fst(ref_var(w2)), r2 = mk_snd(ref_var(w2)), kb = mk_app(k, b2);
        DimVarId i = declare_dim();
        RefId h = mk_lam_lv(s, w2, S, mk_plam(i, pair(s, S, b2, papp(r, mk_app(Rf, b2), mk_fst(kb), r2, mk_app(mk_snd(kb), r2), iv_var(i)))));
        RefId kk = mk_lam_lv(b, xk, B, refl(b, B, ref_var(xk)));
        R->body = e_maps_pack(s, b, S, B, f, g, h, kk); R->body_type = e_maps_type(s, b, S, B); R->body_level = s; break; }
    case RK_RES_TYPE: {
        uint64_t z = lv[0], r = lv[1];
        R->body = e_res_type(z, r); R->body_type = U(mx(z + 1, r + 1)); R->body_level = mx(z + 1, r + 1) + 1; break; }
    case RK_RES_ZERO: {
        uint64_t z = lv[0]; RefId Z = F(U(z), z + 1);
        R->body = e_res_pack(z, z, Z, Z, e_maps_id(z, Z)); R->body_type = e_res_type(z, z); R->body_level = z + 1; break; }
    case RK_RES_NODE: {
        /* §83.3 residual extension: Res_{z,r} tails, terminal family retained */
        uint64_t a = lv[0], z = lv[1], r = lv[2], s = mx(a, r), tl = mx(z + 1, r + 1);
        RefId A = F(U(a), a + 1), t = F(A, a);
        TermVarId qx = var(A); RefId qEx = path(a, A, t, ref_var(qx)); TermVarId qe = var(qEx);
        RefId QT = mk_pi_lv(a, mx(a, tl), qx, A, mk_pi_lv(a, tl, qe, qEx, e_res_type(z, r)));
        RefId Q = F(QT, mx(a, tl));
        RefId Q0 = app2(Q, t, refl(a, A, t));
        TermVarId x = var(A); TermVarId e = var(path(a, A, t, ref_var(x)));
        RefId S, Z0;
        RefId E = e_singleton(a, r, A, t, x, e, rt_res_X(app2(Q, ref_var(x), ref_var(e))), &S, &Z0);
        RefId Zc = rt_res_Z(Q0);
        R->body = e_res_pack(z, s, Zc, S, e_maps_comp(s, r, z, S, Z0, Zc, E, rt_res_M(Q0)));
        R->body_type = e_res_type(z, s); R->body_level = mx(z + 1, s + 1); break; }
    case RK_RES_ACTION: {
        /* comp(comp(M_L, maps(e)), M_R⁻¹) : Maps(X_L, X_R), e : Equiv(Z_L, Z_R) */
        uint64_t zl = lv[0], rl = lv[1], zr = lv[2], rr = lv[3];
        RefId L = F(e_res_type(zl, rl), mx(zl + 1, rl + 1)), Rr = F(e_res_type(zr, rr), mx(zr + 1, rr + 1));
        RefId ZL = rt_res_Z(L), ZR = rt_res_Z(Rr), XL = rt_res_X(L), XR = rt_res_X(Rr);
        RefId e = F(mk_equiv(zl, zr, ZL, ZR), mx(zl, zr));
        RefId EM = APPLY(rec(RK_EQUIV_MAPS, zl, zr, 0, 0), ZL, ZR, e);
        RefId MRi = APPLY(rec(RK_MAPS_INV, rr, zr, 0, 0), XR, ZR, rt_res_M(Rr));
        RefId C1 = APPLY(rec(RK_MAPS_COMP, rl, zl, zr, 0), XL, ZL, ZR, rt_res_M(L), EM);
        R->body = APPLY(rec(RK_MAPS_COMP, rl, zr, rr, 0), XL, ZR, XR, C1, MRi);
        R->body_type = e_maps_type(rl, rr, XL, XR); R->body_level = mx(rl, rr); break; }
    default: die("unknown recipe kind");
    }
}

/* the closed function: λ formals. body : Π formals. body_type */
static void close_recipe(Recipe *R) {
    RefId v = R->body, T = R->body_type; uint64_t l = R->body_level;
    for (size_t q = R->n; q-- > 0; ) {
        v = mk_lam_lv(R->flevel[q], R->formal[q], R->ftype[q], v);
        T = mk_pi_lv(R->flevel[q], l, R->formal[q], R->ftype[q], T);
        l = mx(R->flevel[q], l);
    }
    R->value = v; R->type = T; R->level = l;
    CtxDecl ds[RT_MAXF];
    for (size_t q = 0; q < R->n; q++) { ds[q].sort = S_TERM; ds[q].id = R->formal[q]; ds[q].type = R->ftype[q]; }
    R->telescope = context_make(R->n, ds, fc_true());
}

const Recipe *rt_recipe(RecipeKind kind, uint64_t l0, uint64_t l1, uint64_t l2, uint64_t l3) {
    pthread_once(&RT.once, rt_once);
    pthread_mutex_lock(&RT.mu);
    uint64_t g = machine_generation();
    if (RT.live && RT.gen != g) rt_clear_locked();
    if (!RT.live) { wordmap_init(&RT.idx); RT.all.len = 0; RT.all.cap = 0; RT.all.data = NULL; RT.gen = g; RT.live = true; }
    uint64_t key[5] = { kind, l0, l1, l2, l3 }, have;
    if (wordmap_get(&RT.idx, key, 5, &have)) { pthread_mutex_unlock(&RT.mu); return (const Recipe *)(uintptr_t)have; }
    Recipe *R = calloc(1, sizeof *R); require(R, "out of memory");
    R->kind = kind; R->lv[0] = l0; R->lv[1] = l1; R->lv[2] = l2; R->lv[3] = l3;
    build(R);                 /* under the (recursive) table lock: one build per tuple */
    close_recipe(R);
    vec_push(&RT.all, R);
    wordmap_put(&RT.idx, key, 5, (uint64_t)(uintptr_t)R);
    pthread_mutex_unlock(&RT.mu);
    return R;
}

static MapId formals_map(const Recipe *r, const RefId *args) {
    MapBuilder b; mapb_init(&b);
    for (size_t q = 0; q < r->n; q++) mapb_term(&b, r->formal[q], args[q]);
    return mapb_finish(&b);
}
MapId rt_args(const Recipe *r, const RefId *args) { return formals_map(r, args); }
RefId rt_inst(const Recipe *r, const RefId *args) { return r->n ? reindex(r->body, formals_map(r, args)) : r->body; }
RefId rt_inst_type(const Recipe *r, const RefId *args) { return r->n ? reindex(r->body_type, formals_map(r, args)) : r->body_type; }
RefId rt_apply(const Recipe *r, const RefId *args) { RefId v = r->value; for (size_t q = 0; q < r->n; q++) v = mk_app(v, args[q]); return v; }

RefId rt_maps_type(uint64_t a, uint64_t b, RefId X, RefId Y) { RefId args[2] = { X, Y }; return rt_inst(rt_recipe(RK_MAPS_TYPE, a, b, 0, 0), args); }
RefId rt_diagram_type(uint64_t b, uint64_t r, RefId B) { return rt_inst(rt_recipe(RK_DIAGRAM_TYPE, b, r, 0, 0), &B); }
RefId rt_res_type(uint64_t z, uint64_t r) { return rt_recipe(RK_RES_TYPE, z, r, 0, 0)->body; }

/* runtime.c — §§83–84: presentations, diagram values, the generic identity
 * action and the groupoid witnesses as fixed core templates. See runtime.h. */
#include "runtime.h"

/* ------------------------------------------------------------------ */
/* keyed formals and the template memo                                   */

enum { RT_MAPS_TYPE = 1, RT_MAPS_ID, RT_MAPS_COMPOSE, RT_MAPS_INV, RT_PRES_TYPE, RT_PRES_CONST,
       RT_SING_TYPE, RT_SING_MAPS, RT_SING, RT_DIAG_TYPE, RT_DIAG_ZERO, RT_DIAG_EXTEND,
       RT_ACTION_F, RT_ACTION_G, RT_ACTION_FUN_F, RT_ACTION_FUN_G, RT_MIDDLE, RT_ACTION_MAPS,
       RT_J, RT_LUNIT, RT_RINV, RT_LINV, RT_ASSOC, RT_AP, RT_REUSE, RT_NODE_FUN, RT_KBASE };

static struct { WordMap memo; pthread_mutex_t mu; size_t count; bool live; } RT;
static void rt_init(void) { if (RT.live) return; wordmap_init(&RT.memo); pthread_mutex_init(&RT.mu, NULL); RT.count = 0; RT.live = true; }
void rt_free(void) { if (!RT.live) return; wordmap_free(&RT.memo); pthread_mutex_destroy(&RT.mu); RT.live = false; }
size_t rt_template_count(void) { return RT.count; }

/* a keyed formal of one template: (construction, levels, slot) */
typedef struct { uint64_t cons, a, b, c; } Key;
static TermVarId tv(Key k, uint64_t slot, RefId type) {
    KeyWord w[6] = { { KW_CONST, 9000 }, { KW_CONST, k.cons }, { KW_CONST, k.a }, { KW_CONST, k.b }, { KW_CONST, k.c }, { KW_CONST, slot } };
    return fresh_term_keyed(w, 6, type);
}
static DimVarId dv(Key k, uint64_t slot) {
    KeyWord w[6] = { { KW_CONST, 9001 }, { KW_CONST, k.cons }, { KW_CONST, k.a }, { KW_CONST, k.b }, { KW_CONST, k.c }, { KW_CONST, slot } };
    return fresh_dim_keyed(w, 6);
}
static bool memo_get(Key k, RefId *out) { uint64_t w[4] = { k.cons, k.a, k.b, k.c }; pthread_mutex_lock(&RT.mu); bool h = wordmap_get(&RT.memo, w, 4, out); pthread_mutex_unlock(&RT.mu); return h; }
static void memo_put(Key k, RefId t) { uint64_t w[4] = { k.cons, k.a, k.b, k.c }; pthread_mutex_lock(&RT.mu); uint64_t have; if (!wordmap_get(&RT.memo, w, 4, &have)) { wordmap_put(&RT.memo, w, 4, t); RT.count++; } pthread_mutex_unlock(&RT.mu); }

/* instantiate a template at images of its formals (simultaneous) */
static RefId inst(RefId tpl, size_t n, const TermVarId *xs, const RefId *imgs) {
    MapBuilder b; mapb_init(&b);
    for (size_t k = 0; k < n; k++) mapb_term(&b, xs[k], imgs[k]);
    return reindex(tpl, mapb_finish(&b));
}
#define LMAX level_max
static RefId app2(RefId f, RefId x, RefId y) { return mk_app(mk_app(f, x), y); }
static RefId P1(RefId m) { return mk_fst(m); }
static RefId P2(RefId m) { return mk_fst(mk_snd(m)); }
static RefId P3(RefId m) { return mk_fst(mk_snd(mk_snd(m))); }
static RefId P4(RefId m) { return mk_snd(mk_snd(mk_snd(m))); }
RefId rt_maps_c(RefId m) { return P1(m); }
RefId rt_maps_d(RefId m) { return P2(m); }
RefId rt_maps_h(RefId m) { return P3(m); }
RefId rt_maps_k(RefId m) { return P4(m); }
RefId rt_pres_X(RefId P) { return mk_fst(P); }
RefId rt_pres_maps(RefId P) { return mk_snd(P); }
RefId rt_diagram_value(RefId d) { return mk_fst(d); }
RefId rt_diagram_family(RefId d, RefId y) { return mk_app(mk_fst(mk_snd(d)), y); }
RefId rt_diagram_maps(RefId d, RefId y) { return mk_app(mk_snd(mk_snd(d)), y); }

/* ------------------------------------------------------------------ */
/* §83.1 maps                                                            */

/* Maps_{a,b}(X,Z) built directly over keyed bound formals (slots 10..) */
static RefId maps_type_direct(Key k, uint64_t a, uint64_t b, RefId X, RefId Z) {
    RefId FT = mk_fun(a, b, X, Z), GT = mk_fun(b, a, Z, X);
    TermVarId f = tv(k, 10, FT), g = tv(k, 11, GT), x = tv(k, 12, X), z = tv(k, 13, Z);
    RefId HT = mk_pi_lv(a, a, x, X, mk_path_const(a, X, mk_app(ref_var(g), mk_app(ref_var(f), ref_var(x))), ref_var(x)));
    RefId KT = mk_pi_lv(b, b, z, Z, mk_path_const(b, Z, mk_app(ref_var(f), mk_app(ref_var(g), ref_var(z))), ref_var(z)));
    TermVarId h = tv(k, 14, HT);
    uint64_t ab = LMAX(a, b);
    return mk_sigma_lv(ab, ab, f, FT, mk_sigma_lv(ab, ab, g, GT, mk_sigma_lv(a, b, h, HT, KT)));
}
/* the Maps value (c,(d,(h,k))) at its type */
static RefId maps_value(uint64_t a, uint64_t b, RefId MT, RefId c, RefId d, RefId h, RefId kk) {
    uint64_t ab = LMAX(a, b);
    RefId M1 = apply_term_binder(MT, 0, 1, c), M2 = apply_term_binder(M1, 0, 1, d);
    return mk_pair_at_lv(ab, MT, c, mk_pair_at_lv(ab, M1, d, mk_pair_at_lv(ab, M2, h, kk)));
}
RefId rt_maps_type(uint64_t a, uint64_t b, RefId X, RefId Z) {
    rt_init(); Key k = { RT_MAPS_TYPE, a, b, 0 }; RefId t;
    TermVarId vX = tv(k, 0, mk_universe(a)), vZ = tv(k, 1, mk_universe(b));
    if (!memo_get(k, &t)) { t = maps_type_direct(k, a, b, ref_var(vX), ref_var(vZ)); memo_put(k, t); }
    TermVarId xs[2] = { vX, vZ }; RefId im[2] = { X, Z }; return inst(t, 2, xs, im);
}
RefId rt_maps_id(uint64_t a, RefId X) {
    rt_init(); Key k = { RT_MAPS_ID, a, 0, 0 }; RefId t;
    TermVarId vX = tv(k, 0, mk_universe(a));
    if (!memo_get(k, &t)) {
        RefId Xv = ref_var(vX), MT = rt_maps_type(a, a, Xv, Xv), id = mk_id_fun(a, Xv);
        TermVarId x = tv(k, 10, Xv);
        RefId h = mk_lam_lv(a, x, Xv, mk_refl(a, Xv, ref_var(x)));
        t = maps_value(a, a, MT, id, id, h, h); memo_put(k, t);
    }
    return inst(t, 1, &vX, &X);
}
RefId rt_ap(uint64_t l, uint64_t m, RefId A, RefId Bt, RefId f, RefId x, RefId y, RefId p) {
    rt_init(); Key k = { RT_AP, l, m, 0 };
    (void)Bt; DimVarId i = dv(k, 0);
    return mk_plam(i, mk_app(f, mk_papp_const(l, A, x, y, p, iv_var(i))));
}
RefId rt_maps_compose(uint64_t a, uint64_t b, uint64_t c, RefId X, RefId Y, RefId Z, RefId E, RefId F) {
    rt_init(); Key k = { RT_MAPS_COMPOSE, a, b, c }; RefId t;
    TermVarId vX = tv(k, 0, mk_universe(a)), vY = tv(k, 1, mk_universe(b)), vZ = tv(k, 2, mk_universe(c));
    RefId Xv = ref_var(vX), Yv = ref_var(vY), Zv = ref_var(vZ);
    TermVarId vE = tv(k, 3, rt_maps_type(a, b, Xv, Yv)), vF = tv(k, 4, rt_maps_type(b, c, Yv, Zv));
    if (!memo_get(k, &t)) {
        RefId Ev = ref_var(vE), Fv = ref_var(vF);
        RefId f = P1(Ev), g = P2(Ev), h = P3(Ev), kk = P4(Ev), u = P1(Fv), v = P2(Fv), H = P3(Fv), K = P4(Fv);
        TermVarId x = tv(k, 10, Xv), z = tv(k, 11, Zv); RefId xv = ref_var(x), zv = ref_var(z);
        RefId fx = mk_app(f, xv), ufx = mk_app(u, fx), vufx = mk_app(v, ufx);
        RefId vz = mk_app(v, zv), gvz = mk_app(g, vz), fgvz = mk_app(f, gvz);
        RefId cf = mk_lam_lv(a, x, Xv, ufx);
        RefId cg = mk_lam_lv(c, z, Zv, gvz);
        /* h'(x) = ap(g)(H(f x)) · h(x) : g(v(u(f x))) = x */
        RefId apg = rt_ap(b, a, Yv, Xv, g, vufx, fx, mk_app(H, fx));
        RefId ch = mk_lam_lv(a, x, Xv, mk_path_concat(a, Xv, mk_app(g, vufx), mk_app(g, fx), xv, apg, mk_app(h, xv)));
        /* k'(z) = ap(u)(k(v z)) · K(z) : u(f(g(v z))) = z */
        RefId apu = rt_ap(b, c, Yv, Zv, u, fgvz, vz, mk_app(kk, vz));
        RefId ck = mk_lam_lv(c, z, Zv, mk_path_concat(c, Zv, mk_app(u, fgvz), mk_app(u, vz), zv, apu, mk_app(K, zv)));
        t = maps_value(a, c, rt_maps_type(a, c, Xv, Zv), cf, cg, ch, ck); memo_put(k, t);
    }
    TermVarId xs[5] = { vX, vY, vZ, vE, vF }; RefId im[5] = { X, Y, Z, E, F }; return inst(t, 5, xs, im);
}
RefId rt_maps_inverse(uint64_t a, uint64_t b, RefId X, RefId Z, RefId E) {
    rt_init(); Key k = { RT_MAPS_INV, a, b, 0 }; RefId t;
    TermVarId vX = tv(k, 0, mk_universe(a)), vZ = tv(k, 1, mk_universe(b));
    RefId Xv = ref_var(vX), Zv = ref_var(vZ);
    TermVarId vE = tv(k, 2, rt_maps_type(a, b, Xv, Zv));
    if (!memo_get(k, &t)) { RefId Ev = ref_var(vE); t = maps_value(b, a, rt_maps_type(b, a, Zv, Xv), P2(Ev), P1(Ev), P4(Ev), P3(Ev)); memo_put(k, t); }
    TermVarId xs[3] = { vX, vZ, vE }; RefId im[3] = { X, Z, E }; return inst(t, 3, xs, im);
}
RefId rt_pres_type(uint64_t a, uint64_t b, RefId Z) {
    rt_init(); Key k = { RT_PRES_TYPE, a, b, 0 }; RefId t;
    TermVarId vZ = tv(k, 0, mk_universe(b));
    if (!memo_get(k, &t)) { TermVarId X = tv(k, 10, mk_universe(a)); t = mk_sigma_lv(level_succ(a), LMAX(a, b), X, mk_universe(a), rt_maps_type(a, b, ref_var(X), ref_var(vZ))); memo_put(k, t); }
    return inst(t, 1, &vZ, &Z);
}
static RefId pres_value(uint64_t a, uint64_t b, RefId PT, RefId X, RefId maps) { return mk_pair_at_lv(LMAX(level_succ(a), b), PT, X, maps); }
RefId rt_pres_const(uint64_t a, RefId Z) {
    rt_init(); Key k = { RT_PRES_CONST, a, 0, 0 }; RefId t;
    TermVarId vZ = tv(k, 0, mk_universe(a));
    if (!memo_get(k, &t)) { RefId Zv = ref_var(vZ); t = pres_value(a, a, rt_pres_type(a, a, Zv), Zv, rt_maps_id(a, Zv)); memo_put(k, t); }
    return inst(t, 1, &vZ, &Z);
}

/* ------------------------------------------------------------------ */
/* §83.2 the dependent singleton                                         */

typedef struct { TermVarId vA, vt, vD; RefId A, t, D, DT, Ex; TermVarId vx, ve; } SingFormals;
static SingFormals sing_formals(Key k, uint64_t a, uint64_t r) {
    SingFormals s; s.vA = tv(k, 0, mk_universe(a)); s.A = ref_var(s.vA);
    s.vt = tv(k, 1, s.A); s.t = ref_var(s.vt);
    s.vx = tv(k, 10, s.A); s.Ex = mk_path_const(a, s.A, s.t, ref_var(s.vx)); s.ve = tv(k, 11, s.Ex);
    s.DT = mk_pi_lv(a, level_succ(r), s.vx, s.A, mk_pi_lv(a, level_succ(r), s.ve, s.Ex, mk_universe(r)));
    s.vD = tv(k, 2, s.DT); s.D = ref_var(s.vD);
    return s;
}
static RefId sing_S(const SingFormals *s, uint64_t a, uint64_t r) {
    RefId Dx = app2(s->D, ref_var(s->vx), ref_var(s->ve));
    return mk_sigma_lv(a, LMAX(a, r), s->vx, s->A, mk_sigma_lv(a, r, s->ve, s->Ex, Dx));
}
RefId rt_singleton_type(uint64_t a, uint64_t r, RefId A, RefId t, RefId D) {
    rt_init(); Key k = { RT_SING_TYPE, a, r, 0 }; RefId tp; SingFormals s = sing_formals(k, a, r);
    if (!memo_get(k, &tp)) { tp = sing_S(&s, a, r); memo_put(k, tp); }
    TermVarId xs[3] = { s.vA, s.vt, s.vD }; RefId im[3] = { A, t, D }; return inst(tp, 3, xs, im);
}
static RefId sing_maps_build(Key k, uint64_t a, uint64_t r, const SingFormals *s) {
    uint64_t lS = LMAX(a, r);
    RefId A = s->A, t = s->t, D = s->D, refl = mk_refl(a, A, t);
    RefId S = sing_S(s, a, r), Z = app2(D, t, refl);
    RefId Dx = app2(D, ref_var(s->vx), ref_var(s->ve));
    ScopeId DS = capture_term2(s->vx, A, a, s->ve, s->Ex, a, Dx, mk_universe(r), level_succ(r), fc_true());
    TermVarId vr = tv(k, 12, S); RefId rr = ref_var(vr);
    RefId rx = mk_fst(rr), re = mk_fst(mk_snd(rr)), rz = mk_snd(mk_snd(rr));
    RefId down = mk_lam_lv(lS, vr, S, mk_down(r, a, A, t, DS, rx, re, rz));
    TermVarId vz = tv(k, 13, Z); RefId z = ref_var(vz);
    RefId inner = apply_term_binder(S, 0, 1, t);
    RefId up = mk_lam_lv(r, vz, Z, mk_pair_at_lv(lS, S, t, mk_pair_at_lv(lS, inner, refl, z)));
    DimVarId i = dv(k, 0), j = dv(k, 1), kk = dv(k, 2);
    RefId xi = mk_papp_const(a, A, t, rx, re, iv_var(i));
    RefId ei = mk_plam(j, mk_papp_const(a, A, t, rx, re, iv_meet(iv_var(i), iv_var(j))));
    RefId xk = mk_papp_const(a, A, t, rx, re, iv_negate(iv_var(kk)));
    RefId ek = mk_plam(j, mk_papp_const(a, A, t, rx, re, iv_meet(iv_negate(iv_var(kk)), iv_var(j))));
    RefId Dk = app2(D, xk, ek), empty = mk_system(0, NULL, NULL);
    RefId zi = mk_fill_at(r, kk, Dk, fc_false(), empty, rz, iv_negate(iv_var(i)));
    RefId inneri = apply_term_binder(S, 0, 1, xi);
    RefId h = mk_lam_lv(lS, vr, S, mk_plam(i, mk_pair_at_lv(lS, S, xi, mk_pair_at_lv(lS, inneri, ei, zi))));
    RefId kz = mk_lam_lv(r, vz, Z, mk_plam(i, mk_fill_at(r, kk, Z, fc_false(), empty, z, iv_negate(iv_var(i)))));
    return maps_value(lS, r, rt_maps_type(lS, r, S, Z), down, up, h, kz);
}
RefId rt_singleton_maps(uint64_t a, uint64_t r, RefId A, RefId t, RefId D) {
    rt_init(); Key k = { RT_SING_MAPS, a, r, 0 }; RefId tp; SingFormals s = sing_formals(k, a, r);
    if (!memo_get(k, &tp)) { tp = sing_maps_build(k, a, r, &s); memo_put(k, tp); }
    TermVarId xs[3] = { s.vA, s.vt, s.vD }; RefId im[3] = { A, t, D }; return inst(tp, 3, xs, im);
}
RefId rt_singleton(uint64_t a, uint64_t r, RefId A, RefId t, RefId D) {
    rt_init(); Key k = { RT_SING, a, r, 0 }; RefId tp; SingFormals s = sing_formals(k, a, r);
    if (!memo_get(k, &tp)) {
        uint64_t lS = LMAX(a, r); RefId Z = app2(s.D, s.t, mk_refl(a, s.A, s.t));
        tp = pres_value(lS, r, rt_pres_type(lS, r, Z), rt_singleton_type(a, r, s.A, s.t, s.D), rt_singleton_maps(a, r, s.A, s.t, s.D)); memo_put(k, tp);
    }
    TermVarId xs[3] = { s.vA, s.vt, s.vD }; RefId im[3] = { A, t, D }; return inst(tp, 3, xs, im);
}

/* ------------------------------------------------------------------ */
/* §83.3 diagram values                                                  */

static uint64_t diag_level(uint64_t b, uint64_t r) { return LMAX(b, level_succ(r)); }
RefId rt_diagram_type(uint64_t b, uint64_t r, RefId B) {
    rt_init(); Key k = { RT_DIAG_TYPE, b, r, 0 }; RefId t;
    TermVarId vB = tv(k, 0, mk_universe(b));
    if (!memo_get(k, &t)) {
        RefId Bv = ref_var(vB);
        TermVarId c = tv(k, 10, Bv), y = tv(k, 11, Bv);
        RefId RT_ = mk_pi_lv(b, level_succ(r), y, Bv, mk_universe(r)); TermVarId R = tv(k, 12, RT_);
        RefId M = mk_pi_lv(b, LMAX(r, b), y, Bv, rt_maps_type(r, b, mk_app(ref_var(R), ref_var(y)), mk_path_const(b, Bv, ref_var(c), ref_var(y))));
        t = mk_sigma_lv(b, diag_level(b, r), c, Bv, mk_sigma_lv(LMAX(b, level_succ(r)), LMAX(r, b), R, RT_, M)); memo_put(k, t);
    }
    return inst(t, 1, &vB, &B);
}
static RefId diag_value(uint64_t b, uint64_t r, RefId DT, RefId C, RefId R, RefId maps) {
    uint64_t l = diag_level(b, r); RefId D1 = apply_term_binder(DT, 0, 1, C);
    return mk_pair_at_lv(l, DT, C, mk_pair_at_lv(l, D1, R, maps));
}
RefId rt_diagram_zero(uint64_t b, RefId B, RefId C) {
    rt_init(); Key k = { RT_DIAG_ZERO, b, 0, 0 }; RefId t;
    TermVarId vB = tv(k, 0, mk_universe(b)); RefId Bv = ref_var(vB); TermVarId vC = tv(k, 1, Bv);
    if (!memo_get(k, &t)) {
        RefId Cv = ref_var(vC); TermVarId y = tv(k, 10, Bv); RefId Py = mk_path_const(b, Bv, Cv, ref_var(y));
        RefId R = mk_lam_lv(b, y, Bv, Py);
        RefId maps = mk_lam_lv(b, y, Bv, rt_maps_id(b, Py));
        t = diag_value(b, b, rt_diagram_type(b, b, Bv), Cv, R, maps); memo_put(k, t);
    }
    TermVarId xs[2] = { vB, vC }; RefId im[2] = { B, C }; return inst(t, 2, xs, im);
}
RefId rt_diagram_extend(uint64_t a, uint64_t b, uint64_t r, RefId A, RefId t, RefId Q, RefId B) {
    rt_init(); Key k = { RT_DIAG_EXTEND, a, b, r }; RefId tp;
    TermVarId vB = tv(k, 0, mk_universe(b)), vA = tv(k, 1, mk_universe(a)); RefId Bv = ref_var(vB), Av = ref_var(vA);
    TermVarId vt = tv(k, 2, Av); RefId tv_ = ref_var(vt);
    TermVarId vx = tv(k, 10, Av); RefId Ex = mk_path_const(a, Av, tv_, ref_var(vx)); TermVarId ve = tv(k, 11, Ex);
    RefId DT = rt_diagram_type(b, r, Bv); uint64_t lDT = diag_level(b, r);
    RefId QT = mk_pi_lv(a, LMAX(a, lDT), vx, Av, mk_pi_lv(a, lDT, ve, Ex, DT));
    TermVarId vQ = tv(k, 3, QT);
    if (!memo_get(k, &tp)) {
        RefId Qv = ref_var(vQ), refl = mk_refl(a, Av, tv_), centre = app2(Qv, tv_, refl), C0 = mk_fst(centre);
        uint64_t r2 = LMAX(a, r);
        TermVarId y = tv(k, 12, Bv); RefId yv = ref_var(y);
        RefId Qxe = app2(Qv, ref_var(vx), ref_var(ve));
        RefId Rqy = rt_diagram_family(Qxe, yv);                                  /* R_{Q x e}(y) : U_r */
        RefId Sy = mk_sigma_lv(a, r2, vx, Av, mk_sigma_lv(a, r, ve, Ex, Rqy));
        RefId Rp = mk_lam_lv(b, y, Bv, Sy);                                      /* R' : B → U_{r'} */
        RefId Dy = mk_lam_lv(a, vx, Av, mk_lam_lv(a, ve, Ex, Rqy));              /* D_y : (x:A) → (t=x) → U_r */
        RefId sing = rt_singleton_maps(a, r, Av, tv_, Dy);                       /* Maps(S_{D_y}, R_centre y) */
        RefId Y = rt_diagram_family(centre, yv), Z = mk_path_const(b, Bv, C0, yv);
        RefId tail = rt_diagram_maps(centre, yv);                                /* Maps(R_centre y, Path(C0,y)) */
        RefId maps = mk_lam_lv(b, y, Bv, rt_maps_compose(r2, r, b, rt_singleton_type(a, r, Av, tv_, Dy), Y, Z, sing, tail));
        tp = diag_value(b, r2, rt_diagram_type(b, r2, Bv), C0, Rp, maps); memo_put(k, tp);
    }
    TermVarId xs[4] = { vB, vA, vt, vQ }; RefId im[4] = { B, A, t, Q }; return inst(tp, 4, xs, im);
}

RefId rt_node_fun(uint64_t a, uint64_t b, uint64_t r, RefId *type) {
    rt_init(); Key k = { RT_NODE_FUN, a, b, r }; RefId t;
    uint64_t s = LMAX(a, r), lDT = diag_level(b, r), outl = diag_level(b, s);
    RefId UA = mk_universe(a), UB = mk_universe(b);
    TermVarId vB = tv(k, 0, UB), vA = tv(k, 1, UA); RefId Bv = ref_var(vB), Av = ref_var(vA);
    TermVarId vt = tv(k, 2, Av); RefId tv_ = ref_var(vt);
    TermVarId vx = tv(k, 10, Av); RefId Ex = mk_path_const(a, Av, tv_, ref_var(vx)); TermVarId ve = tv(k, 11, Ex);
    RefId DT = rt_diagram_type(b, r, Bv);
    RefId QT = mk_pi_lv(a, LMAX(a, lDT), vx, Av, mk_pi_lv(a, lDT, ve, Ex, DT)); uint64_t ql = LMAX(a, lDT);
    TermVarId vQ = tv(k, 3, QT);
    if (!memo_get(k, &t)) {
        RefId body = rt_diagram_extend(a, b, r, Av, tv_, ref_var(vQ), Bv);
        body = mk_lam_lv(ql, vQ, QT, body); body = mk_lam_lv(a, vt, Av, body);
        body = mk_lam_lv(level_succ(a), vA, UA, body); body = mk_lam_lv(level_succ(b), vB, UB, body);
        t = body; memo_put(k, t);
    }
    if (type) {
        RefId T = mk_pi_lv(ql, outl, vQ, QT, rt_diagram_type(b, s, Bv)); uint64_t l = LMAX(ql, outl);
        T = mk_pi_lv(a, l, vt, Av, T); l = LMAX(a, l);
        T = mk_pi_lv(level_succ(a), l, vA, UA, T); l = LMAX(level_succ(a), l);
        T = mk_pi_lv(level_succ(b), l, vB, UB, T);
        *type = T;
    }
    return t;
}

/* ------------------------------------------------------------------ */
/* §83.4 the generic action                                              */

typedef struct { TermVarId vB, vL, vR, vp, vy, va; RefId B, L, R, p, y, PT, DL, DR, RL, RR; } ActFormals;
static ActFormals act_formals(Key k, uint64_t b, uint64_t rl, uint64_t rr, int dir) {
    ActFormals f; f.vB = tv(k, 0, mk_universe(b)); f.B = ref_var(f.vB);
    f.DL = rt_diagram_type(b, rl, f.B); f.DR = rt_diagram_type(b, rr, f.B);
    f.vL = tv(k, 1, f.DL); f.vR = tv(k, 2, f.DR); f.L = ref_var(f.vL); f.R = ref_var(f.vR);
    f.PT = mk_path_const(b, f.B, rt_diagram_value(f.L), rt_diagram_value(f.R)); f.vp = tv(k, 3, f.PT); f.p = ref_var(f.vp);
    f.vy = tv(k, 4, f.B); f.y = ref_var(f.vy);
    f.RL = rt_diagram_family(f.L, f.y); f.RR = rt_diagram_family(f.R, f.y);
    f.va = tv(k, 5, dir ? f.RR : f.RL);
    return f;
}
static RefId act_body(uint64_t b, const ActFormals *f, int dir) {
    RefId CL = rt_diagram_value(f->L), CR = rt_diagram_value(f->R), arg = ref_var(f->va);
    if (!dir) { RefId q = mk_path_concat(b, f->B, CR, CL, f->y, mk_path_rev(b, f->B, CL, CR, f->p), mk_app(rt_maps_c(rt_diagram_maps(f->L, f->y)), arg));
                return mk_app(rt_maps_d(rt_diagram_maps(f->R, f->y)), q); }
    RefId q = mk_path_concat(b, f->B, CL, CR, f->y, f->p, mk_app(rt_maps_c(rt_diagram_maps(f->R, f->y)), arg));
    return mk_app(rt_maps_d(rt_diagram_maps(f->L, f->y)), q);
}
RefId rt_action(int dir, uint64_t b, uint64_t rl, uint64_t rr, RefId B, RefId L, RefId R, RefId p, RefId y, RefId arg) {
    rt_init(); Key k = { dir ? RT_ACTION_G : RT_ACTION_F, b, rl, rr }; RefId t; ActFormals f = act_formals(k, b, rl, rr, dir);
    if (!memo_get(k, &t)) { t = act_body(b, &f, dir); memo_put(k, t); }
    TermVarId xs[6] = { f.vB, f.vL, f.vR, f.vp, f.vy, f.va }; RefId im[6] = { B, L, R, p, y, arg }; return inst(t, 6, xs, im);
}
RefId rt_action_fun(int dir, uint64_t b, uint64_t rl, uint64_t rr, RefId B, RefId *type) {
    rt_init(); Key k = { dir ? RT_ACTION_FUN_G : RT_ACTION_FUN_F, b, rl, rr }; RefId t; ActFormals f = act_formals(k, b, rl, rr, dir);
    uint64_t lDL = diag_level(b, rl), lDR = diag_level(b, rr), lin = dir ? rr : rl, lout = dir ? rl : rr;
    RefId in = dir ? f.RR : f.RL, out = dir ? f.RL : f.RR;
    RefId T = mk_pi_lv(lin, lout, f.va, in, out);
    T = mk_pi_lv(b, LMAX(lin, lout), f.vy, f.B, T);
    T = mk_pi_lv(b, LMAX(b, LMAX(lin, lout)), f.vp, f.PT, T);
    uint64_t l3 = LMAX(b, LMAX(lin, lout));
    T = mk_pi_lv(lDR, l3, f.vR, f.DR, T);
    T = mk_pi_lv(lDL, LMAX(lDR, l3), f.vL, f.DL, T);
    if (!memo_get(k, &t)) {
        RefId body = act_body(b, &f, dir);
        body = mk_lam_lv(lin, f.va, in, body); body = mk_lam_lv(b, f.vy, f.B, body); body = mk_lam_lv(b, f.vp, f.PT, body);
        body = mk_lam_lv(lDR, f.vR, f.DR, body); body = mk_lam_lv(lDL, f.vL, f.DL, body);
        t = body; memo_put(k, t);
    }
    if (type) *type = inst(T, 1, &f.vB, &B);
    return inst(t, 1, &f.vB, &B);
}

/* ------------------------------------------------------------------ */
/* §83.4 path induction and the groupoid laws                            */

RefId rt_J(uint64_t l, uint64_t lp, RefId A, RefId a, RefId P, RefId d, RefId b, RefId p) {
    rt_init(); Key k = { RT_J, l, lp, 0 }; DimVarId i = dv(k, 0), j = dv(k, 1);
    RefId pi = mk_papp_const(l, A, a, b, p, iv_var(i));
    RefId pij = mk_plam(j, mk_papp_const(l, A, a, b, p, iv_meet(iv_var(i), iv_var(j))));
    return mk_coe_at(lp, i, app2(P, pi, pij), d);
}
/* words at a point and K(w) : w = refl (§83.4) */
typedef enum { W_REFL = 1, W_INV, W_CAT } WordTag;
typedef struct Word { WordTag tag; const struct Word *l, *r; } Word;
typedef struct { uint64_t l; RefId A, a, LoopT, refl; Key k; } KCtx;
static RefId word_term(const KCtx *c, const Word *w) {
    switch (w->tag) {
    case W_REFL: return c->refl;
    case W_INV: return mk_path_rev(c->l, c->A, c->a, c->a, word_term(c, w->l));
    default: return mk_path_concat(c->l, c->A, c->a, c->a, c->a, word_term(c, w->l), word_term(c, w->r));
    }
}
/* K(refl·refl) = ⟨k⟩⟨i⟩ fill^j_A [(i=0)↦a,(i=1)↦a] a (¬k) */
static RefId k_base(const KCtx *c) {
    DimVarId i = dv(c->k, 2), j = dv(c->k, 3), kk = dv(c->k, 4);
    FaceId faces[2] = { fc_lit(i, 0), fc_lit(i, 1) }; RefId terms[2] = { c->a, c->a };
    RefId sys = mk_system(2, faces, terms);
    RefId fill = mk_fill_at(c->l, j, c->A, fc_join(faces[0], faces[1]), sys, c->a, iv_negate(iv_var(kk)));
    return mk_plam(kk, mk_plam(i, fill));
}
static RefId K_of(const KCtx *c, const Word *w) {
    uint64_t l = c->l; RefId LT = c->LoopT, refl = c->refl;
    switch (w->tag) {
    case W_REFL: return mk_refl(l, LT, refl);
    case W_INV: {   /* ap(inverse)(K(v)) : v⁻¹ = refl⁻¹, then refl⁻¹ ≡ refl by the definition of inverse */
        RefId v = word_term(c, w->l), Kv = K_of(c, w->l);
        TermVarId u = tv(c->k, 20, LT);
        RefId invf = mk_lam_lv(l, u, LT, mk_path_rev(l, c->A, c->a, c->a, ref_var(u)));
        return rt_ap(l, l, LT, LT, invf, v, refl, Kv);
    }
    default: {   /* ⟨k⟩(K(v)@k)·(K(w)@k) : v·w = refl·refl, then K(refl·refl) */
        RefId v = word_term(c, w->l), ww = word_term(c, w->r), Kv = K_of(c, w->l), Kw = K_of(c, w->r);
        DimVarId kk = dv(c->k, 5);
        RefId vk = mk_papp_const(l, LT, v, refl, Kv, iv_var(kk)), wk = mk_papp_const(l, LT, ww, refl, Kw, iv_var(kk));
        RefId first = mk_plam(kk, mk_path_concat(l, c->A, c->a, c->a, c->a, vk, wk));
        RefId rr = mk_path_concat(l, c->A, c->a, c->a, c->a, refl, refl);
        return mk_path_concat(l, LT, word_term(c, w), rr, refl, first, k_base(c));
    }
    }
}
static KCtx kctx(Key k, uint64_t l, RefId A, RefId a) { KCtx c; c.l = l; c.A = A; c.a = a; c.refl = mk_refl(l, A, a); c.LoopT = mk_path_const(l, A, a, a); c.k = k; return c; }
/* the equality of two base words u = v: K(u) · K(v)⁻¹ */
static RefId words_equal(const KCtx *c, const Word *u, const Word *v) {
    RefId tu = word_term(c, u), tvv = word_term(c, v);
    return mk_path_concat(c->l, c->LoopT, tu, c->refl, tvv, K_of(c, u), mk_path_rev(c->l, c->LoopT, tvv, c->refl, K_of(c, v)));
}
static const Word W_R = { W_REFL, NULL, NULL };
static const Word W_RR = { W_CAT, &W_R, &W_R };          /* refl·refl */
static const Word W_RI = { W_INV, &W_R, NULL };          /* refl⁻¹ */
static const Word W_R_RI = { W_CAT, &W_R, &W_RI };       /* refl·refl⁻¹ */
static const Word W_RI_R = { W_CAT, &W_RI, &W_R };       /* refl⁻¹·refl */
static const Word W_RR_R = { W_CAT, &W_RR, &W_R };       /* (refl·refl)·refl */
static const Word W_R_RR = { W_CAT, &W_R, &W_RR };       /* refl·(refl·refl) */

/* each law is one template over A : U_l, a : A and its path formals,
 * generated once per level and instantiated by substitution */
typedef struct { TermVarId vA, va; RefId A, a; } LawFormals;
static LawFormals law_formals(Key k, uint64_t l) { LawFormals f; f.vA = tv(k, 0, mk_universe(l)); f.A = ref_var(f.vA); f.va = tv(k, 1, f.A); f.a = ref_var(f.va); return f; }
static RefId PathT(uint64_t l, RefId A, RefId x, RefId y) { return mk_path_const(l, A, x, y); }

RefId rt_lunit(uint64_t l, RefId A, RefId a, RefId b, RefId q) {
    rt_init(); Key k = { RT_LUNIT, l, 0, 0 }; RefId t; LawFormals f = law_formals(k, l);
    TermVarId vb = tv(k, 2, f.A); RefId bv = ref_var(vb); TermVarId vq = tv(k, 3, PathT(l, f.A, f.a, bv));
    if (!memo_get(k, &t)) {
        KCtx c = kctx(k, l, f.A, f.a); RefId qv = ref_var(vq);
        /* motive P(b,q) = Path(refl·q, q) */
        TermVarId mb = tv(k, 10, f.A); RefId mbv = ref_var(mb); TermVarId mq = tv(k, 11, PathT(l, f.A, f.a, mbv)); RefId mqv = ref_var(mq);
        RefId Pb = PathT(l, PathT(l, f.A, f.a, mbv), mk_path_concat(l, f.A, f.a, f.a, mbv, c.refl, mqv), mqv);
        RefId P = mk_lam_lv(l, mb, f.A, mk_lam_lv(l, mq, PathT(l, f.A, f.a, mbv), Pb));
        t = rt_J(l, l, f.A, f.a, P, k_base(&c), bv, qv); memo_put(k, t);
    }
    TermVarId xs[4] = { f.vA, f.va, vb, vq }; RefId im[4] = { A, a, b, q }; return inst(t, 4, xs, im);
}
static RefId inv_law(Key k, uint64_t l, RefId A, RefId a, RefId b, RefId p, bool right) {
    RefId t; LawFormals f = law_formals(k, l);
    TermVarId vb = tv(k, 2, f.A); RefId bv = ref_var(vb); TermVarId vp = tv(k, 3, PathT(l, f.A, f.a, bv));
    if (!memo_get(k, &t)) {
        KCtx c = kctx(k, l, f.A, f.a); RefId pv = ref_var(vp);
        TermVarId mb = tv(k, 10, f.A); RefId mbv = ref_var(mb); TermVarId mp = tv(k, 11, PathT(l, f.A, f.a, mbv)); RefId mpv = ref_var(mp);
        RefId inv = mk_path_rev(l, f.A, f.a, mbv, mpv);
        RefId word = right ? mk_path_concat(l, f.A, f.a, mbv, f.a, mpv, inv) : mk_path_concat(l, f.A, mbv, f.a, mbv, inv, mpv);
        RefId at = right ? f.a : mbv;
        RefId Pb = PathT(l, PathT(l, f.A, at, at), word, mk_refl(l, f.A, at));
        RefId P = mk_lam_lv(l, mb, f.A, mk_lam_lv(l, mp, PathT(l, f.A, f.a, mbv), Pb));
        t = rt_J(l, l, f.A, f.a, P, K_of(&c, right ? &W_R_RI : &W_RI_R), bv, pv); memo_put(k, t);
    }
    TermVarId xs[4] = { f.vA, f.va, vb, vp }; RefId im[4] = { A, a, b, p }; return inst(t, 4, xs, im);
}
RefId rt_rinv(uint64_t l, RefId A, RefId a, RefId b, RefId p) { rt_init(); Key k = { RT_RINV, l, 0, 0 }; return inv_law(k, l, A, a, b, p, true); }
RefId rt_linv(uint64_t l, RefId A, RefId a, RefId b, RefId p) { rt_init(); Key k = { RT_LINV, l, 0, 0 }; return inv_law(k, l, A, a, b, p, false); }

RefId rt_assoc(uint64_t l, RefId A, RefId a, RefId b, RefId c, RefId d, RefId p, RefId q, RefId r) {
    rt_init(); Key k = { RT_ASSOC, l, 0, 0 }; RefId t; LawFormals f = law_formals(k, l);
    TermVarId vb = tv(k, 2, f.A), vc = tv(k, 3, f.A), vd = tv(k, 4, f.A); RefId bv = ref_var(vb), cv = ref_var(vc), dvv = ref_var(vd);
    TermVarId vp = tv(k, 5, PathT(l, f.A, f.a, bv)), vq = tv(k, 6, PathT(l, f.A, bv, cv)), vr = tv(k, 7, PathT(l, f.A, cv, dvv));
    if (!memo_get(k, &t)) {
        KCtx kc = kctx(k, l, f.A, f.a); RefId pv = ref_var(vp), qv = ref_var(vq), rv = ref_var(vr), A_ = f.A, a_ = f.a;
        /* innermost: induction on r with p = q = refl: motive P3(d,r) = Path((refl·refl)·r, refl·(refl·r)) */
        TermVarId m3d = tv(k, 10, A_); RefId m3dv = ref_var(m3d); TermVarId m3r = tv(k, 11, PathT(l, A_, a_, m3dv)); RefId m3rv = ref_var(m3r);
        RefId rr = mk_path_concat(l, A_, a_, a_, a_, kc.refl, kc.refl);
        RefId lhs3 = mk_path_concat(l, A_, a_, a_, m3dv, rr, m3rv), rhs3 = mk_path_concat(l, A_, a_, a_, m3dv, kc.refl, mk_path_concat(l, A_, a_, a_, m3dv, kc.refl, m3rv));
        RefId P3 = mk_lam_lv(l, m3d, A_, mk_lam_lv(l, m3r, PathT(l, A_, a_, m3dv), PathT(l, PathT(l, A_, a_, m3dv), lhs3, rhs3)));
        RefId base3 = words_equal(&kc, &W_RR_R, &W_R_RR);
        /* middle: induction on q with p = refl: motive P2(c,q) = Π(d:A).Π(r:c=d). Path((refl·q)·r, refl·(q·r)) */
        TermVarId m2c = tv(k, 12, A_); RefId m2cv = ref_var(m2c); TermVarId m2q = tv(k, 13, PathT(l, A_, a_, m2cv)); RefId m2qv = ref_var(m2q);
        TermVarId m2d = tv(k, 14, A_); RefId m2dv = ref_var(m2d); TermVarId m2r = tv(k, 15, PathT(l, A_, m2cv, m2dv)); RefId m2rv = ref_var(m2r);
        RefId lhs2 = mk_path_concat(l, A_, a_, m2cv, m2dv, mk_path_concat(l, A_, a_, a_, m2cv, kc.refl, m2qv), m2rv);
        RefId rhs2 = mk_path_concat(l, A_, a_, a_, m2dv, kc.refl, mk_path_concat(l, A_, a_, m2cv, m2dv, m2qv, m2rv));
        RefId body2 = mk_pi_lv(l, l, m2d, A_, mk_pi_lv(l, l, m2r, PathT(l, A_, m2cv, m2dv), PathT(l, PathT(l, A_, a_, m2dv), lhs2, rhs2)));
        RefId P2_ = mk_lam_lv(l, m2c, A_, mk_lam_lv(l, m2q, PathT(l, A_, a_, m2cv), body2));
        /* base of the middle induction: λd r. J(P3, base3, d, r) */
        TermVarId b2d = tv(k, 16, A_); RefId b2dv = ref_var(b2d); TermVarId b2r = tv(k, 17, PathT(l, A_, a_, b2dv));
        RefId base2 = mk_lam_lv(l, b2d, A_, mk_lam_lv(l, b2r, PathT(l, A_, a_, b2dv), rt_J(l, l, A_, a_, P3, base3, b2dv, ref_var(b2r))));
        /* outer: induction on p: motive P1(b,p) = Π(c:A).Π(q:b=c).Π(d:A).Π(r:c=d). Path((p·q)·r, p·(q·r)) */
        TermVarId m1b = tv(k, 18, A_); RefId m1bv = ref_var(m1b); TermVarId m1p = tv(k, 19, PathT(l, A_, a_, m1bv)); RefId m1pv = ref_var(m1p);
        TermVarId m1c = tv(k, 20, A_); RefId m1cv = ref_var(m1c); TermVarId m1q = tv(k, 21, PathT(l, A_, m1bv, m1cv)); RefId m1qv = ref_var(m1q);
        TermVarId m1d = tv(k, 22, A_); RefId m1dv = ref_var(m1d); TermVarId m1r = tv(k, 23, PathT(l, A_, m1cv, m1dv)); RefId m1rv = ref_var(m1r);
        RefId lhs1 = mk_path_concat(l, A_, a_, m1cv, m1dv, mk_path_concat(l, A_, a_, m1bv, m1cv, m1pv, m1qv), m1rv);
        RefId rhs1 = mk_path_concat(l, A_, a_, m1bv, m1dv, m1pv, mk_path_concat(l, A_, m1bv, m1cv, m1dv, m1qv, m1rv));
        RefId body1 = mk_pi_lv(l, l, m1c, A_, mk_pi_lv(l, l, m1q, PathT(l, A_, m1bv, m1cv), mk_pi_lv(l, l, m1d, A_, mk_pi_lv(l, l, m1r, PathT(l, A_, m1cv, m1dv), PathT(l, PathT(l, A_, a_, m1dv), lhs1, rhs1)))));
        RefId P1_ = mk_lam_lv(l, m1b, A_, mk_lam_lv(l, m1p, PathT(l, A_, a_, m1bv), body1));
        /* base of the outer induction: λc q. J(P2, base2, c, q) */
        TermVarId b1c = tv(k, 24, A_); RefId b1cv = ref_var(b1c); TermVarId b1q = tv(k, 25, PathT(l, A_, a_, b1cv));
        RefId base1 = mk_lam_lv(l, b1c, A_, mk_lam_lv(l, b1q, PathT(l, A_, a_, b1cv), rt_J(l, l, A_, a_, P2_, base2, b1cv, ref_var(b1q))));
        RefId J1 = rt_J(l, l, A_, a_, P1_, base1, bv, pv);
        t = app2(app2(J1, cv, qv), dvv, rv); memo_put(k, t);
    }
    TermVarId xs[8] = { f.vA, f.va, vb, vc, vd, vp, vq, vr }; RefId im[8] = { A, a, b, c, d, p, q, r }; return inst(t, 8, xs, im);
}

/* the middle maps of the action at y with both inverse witnesses */
RefId rt_action_middle(uint64_t b, RefId B, RefId CL, RefId CR, RefId p, RefId y) {
    rt_init(); Key k = { RT_MIDDLE, b, 0, 0 }; RefId t;
    TermVarId vB = tv(k, 0, mk_universe(b)); RefId Bv = ref_var(vB);
    TermVarId vCL = tv(k, 1, Bv), vCR = tv(k, 2, Bv), vy = tv(k, 3, Bv); RefId CLv = ref_var(vCL), CRv = ref_var(vCR), yv = ref_var(vy);
    TermVarId vp = tv(k, 4, PathT(b, Bv, CLv, CRv)); RefId pv = ref_var(vp);
    if (!memo_get(k, &t)) {
        RefId QL = PathT(b, Bv, CLv, yv), QR = PathT(b, Bv, CRv, yv), pinv = mk_path_rev(b, Bv, CLv, CRv, pv);
        TermVarId q = tv(k, 10, QL), s = tv(k, 11, QR); RefId qv = ref_var(q), sv = ref_var(s);
        RefId fq = mk_path_concat(b, Bv, CRv, CLv, yv, pinv, qv);         /* p⁻¹·q : CR = y */
        RefId gs = mk_path_concat(b, Bv, CLv, CRv, yv, pv, sv);           /* p·s : CL = y */
        RefId f = mk_lam_lv(b, q, QL, fq), g = mk_lam_lv(b, s, QR, gs);
        /* h(q) : p·(p⁻¹·q) = q  =  assoc(p,p⁻¹,q)⁻¹ · ap(λv.v·q)(rinv p) · lunit(q) */
        RefId LL = PathT(b, Bv, CLv, CLv), reflL = mk_refl(b, Bv, CLv);
        RefId pp = mk_path_concat(b, Bv, CLv, CRv, CLv, pv, pinv);                 /* p·p⁻¹ : CL = CL */
        RefId gfq = mk_path_concat(b, Bv, CLv, CRv, yv, pv, fq);                   /* p·(p⁻¹·q) */
        RefId ppq = mk_path_concat(b, Bv, CLv, CLv, yv, pp, qv);                    /* (p·p⁻¹)·q */
        RefId rq = mk_path_concat(b, Bv, CLv, CLv, yv, reflL, qv);                  /* refl·q */
        RefId as1 = mk_path_rev(b, QL, ppq, gfq, rt_assoc(b, Bv, CLv, CRv, CLv, yv, pv, pinv, qv));
        TermVarId vv = tv(k, 12, LL);
        RefId catq = mk_lam_lv(b, vv, LL, mk_path_concat(b, Bv, CLv, CLv, yv, ref_var(vv), qv));
        RefId ap1 = rt_ap(b, b, LL, QL, catq, pp, reflL, rt_rinv(b, Bv, CLv, CRv, pv));
        RefId h = mk_lam_lv(b, q, QL, mk_path_concat(b, QL, gfq, ppq, qv, as1, mk_path_concat(b, QL, ppq, rq, qv, ap1, rt_lunit(b, Bv, CLv, yv, qv))));
        /* k(s) : p⁻¹·(p·s) = s  =  assoc(p⁻¹,p,s)⁻¹ · ap(λv.v·s)(linv p) · lunit(s) */
        RefId RR_ = PathT(b, Bv, CRv, CRv), reflR = mk_refl(b, Bv, CRv);
        RefId ipp = mk_path_concat(b, Bv, CRv, CLv, CRv, pinv, pv);               /* p⁻¹·p : CR = CR */
        RefId fgs = mk_path_concat(b, Bv, CRv, CLv, yv, pinv, gs);                 /* p⁻¹·(p·s) */
        RefId ipps = mk_path_concat(b, Bv, CRv, CRv, yv, ipp, sv);                  /* (p⁻¹·p)·s */
        RefId rs = mk_path_concat(b, Bv, CRv, CRv, yv, reflR, sv);
        RefId as2 = mk_path_rev(b, QR, ipps, fgs, rt_assoc(b, Bv, CRv, CLv, CRv, yv, pinv, pv, sv));
        TermVarId vw = tv(k, 13, RR_);
        RefId cats = mk_lam_lv(b, vw, RR_, mk_path_concat(b, Bv, CRv, CRv, yv, ref_var(vw), sv));
        RefId ap2 = rt_ap(b, b, RR_, QR, cats, ipp, reflR, rt_linv(b, Bv, CLv, CRv, pv));
        RefId kk = mk_lam_lv(b, s, QR, mk_path_concat(b, QR, fgs, ipps, sv, as2, mk_path_concat(b, QR, ipps, rs, sv, ap2, rt_lunit(b, Bv, CRv, yv, sv))));
        t = maps_value(b, b, rt_maps_type(b, b, QL, QR), f, g, h, kk); memo_put(k, t);
    }
    TermVarId xs[5] = { vB, vCL, vCR, vy, vp }; RefId im[5] = { B, CL, CR, y, p }; return inst(t, 5, xs, im);
}
RefId rt_action_maps(uint64_t b, uint64_t rl, uint64_t rr, RefId B, RefId L, RefId R, RefId p, RefId y) {
    rt_init(); Key k = { RT_ACTION_MAPS, b, rl, rr }; RefId t; ActFormals f = act_formals(k, b, rl, rr, 0);
    if (!memo_get(k, &t)) {
        RefId CL = rt_diagram_value(f.L), CR = rt_diagram_value(f.R), QL = PathT(b, f.B, CL, f.y), QR = PathT(b, f.B, CR, f.y);
        RefId mid = rt_action_middle(b, f.B, CL, CR, f.p, f.y);
        RefId left = rt_maps_compose(rl, b, b, f.RL, QL, QR, rt_diagram_maps(f.L, f.y), mid);
        RefId invR = rt_maps_inverse(rr, b, f.RR, QR, rt_diagram_maps(f.R, f.y));
        t = rt_maps_compose(rl, b, rr, f.RL, QR, f.RR, left, invR); memo_put(k, t);
    }
    TermVarId xs[5] = { f.vB, f.vL, f.vR, f.vp, f.vy }; RefId im[5] = { B, L, R, p, y }; return inst(t, 5, xs, im);
}

/* ------------------------------------------------------------------ */
/* §84                                                                   */

RefId rt_reuse(uint64_t lb, uint64_t lo, RefId B, RefId O, RefId x, RefId y, RefId p, RefId a) {
    rt_init(); Key k = { RT_REUSE, lb, lo, 0 }; DimVarId i = dv(k, 0);
    return mk_coe_at(lo, i, mk_app(O, mk_papp_const(lb, B, x, y, p, iv_var(i))), a);
}

/* the host diagram as the right fold of extensions ending in zero (ordinary
 * diagrams) or of singleton presentations ending in the constant presentation
 * (residual descriptions); memoized per diagram id */
static RefId export_fold(size_t k, size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o, bool residual, uint64_t *level) {
    if (k == n) { *level = lB; return residual ? rt_pres_const(lB, o) : rt_diagram_zero(lB, B, o); }
    uint64_t inner; RefId tail = export_fold(k + 1, n, nodes, B, lB, o, residual, &inner);
    const DiagNode *nd = &nodes[k];
    RefId Pk = mk_path_const(nd->level, nd->A, nd->t, ref_var(nd->x));
    *level = level_max(nd->level, inner);
    if (!residual) {
        RefId Q = mk_lam_lv(nd->level, nd->x, nd->A, mk_lam_lv(nd->level, nd->e, Pk, tail));
        return rt_diagram_extend(nd->level, lB, inner, nd->A, nd->t, Q, B);
    }
    /* residual: Pres_{inner,lB}(Z) under (x,e); the singleton over D(x,e) = X_tail, composed with the tail's maps at the centre */
    RefId D = mk_lam_lv(nd->level, nd->x, nd->A, mk_lam_lv(nd->level, nd->e, Pk, rt_pres_X(tail)));
    RefId refl = mk_refl(nd->level, nd->A, nd->t);
    MapBuilder mb; mapb_init(&mb); mapb_term(&mb, nd->x, nd->t); mapb_term(&mb, nd->e, refl); MapId nu = mapb_finish(&mb);
    RefId centre = reindex(tail, nu), Zc = reindex(o, nu);
    RefId S = rt_singleton_type(nd->level, inner, nd->A, nd->t, D), Y = rt_pres_X(centre);
    RefId maps = rt_maps_compose(*level, inner, lB, S, Y, Zc, rt_singleton_maps(nd->level, inner, nd->A, nd->t, D), rt_pres_maps(centre));
    return pres_value(*level, lB, rt_pres_type(*level, lB, Zc), S, maps);
}
RefId rt_diagram_export(DiagramId d, RefId *type) {
    rt_init(); Key k = { RT_KBASE + 1, d, 0, 0 }; RefId t;
    size_t n; const DiagNode *nodes; RefId B, o; uint64_t lB; bool residual;
    n = diagram_nodes(d, &nodes); o = diagram_output(d, &B, &lB, &residual);
    if (!memo_get(k, &t)) { uint64_t level; t = export_fold(0, n, nodes, B, lB, o, residual, &level); memo_put(k, t); }
    if (type) {
        uint64_t lv = lB; for (size_t i = n; i-- > 0; ) lv = level_max(nodes[i].level, lv);
        *type = residual ? rt_pres_type(lv, lB, diagram_canonical(d)) : rt_diagram_type(lB, lv, B);
    }
    return t;
}

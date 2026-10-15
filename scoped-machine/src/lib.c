#include "lib.h"

/* ====================================================================
 * Fixed templates (§9, §14).
 *
 * Every derived definition is compiled once into a fixed origin over formal
 * parameters, and an invocation is a view of that origin: `reindex(body, σ)`
 * with σ sending the formals to the arguments. Because reindexing composes,
 * specializing an invocation and invoking at the specialized arguments give
 * the same reference (reindex(T(a), τ) = T(a[τ]) when τ acts on the
 * arguments that are formals).
 *
 * Parameters come in three kinds:
 *   - term formals: term-sorted arguments used at the template's own
 *     dimension points (values, paths, functions, caps, tubes used in place).
 *     A tube is declared partial on its guard, so it contributes no
 *     requirement to the view beyond its guard.
 *   - interval formals: interval arguments (a path application point, the
 *     fill parameter r). They are dimension formals whose images are
 *     intervals.
 *   - shape data: type and family arguments, faces, and families that the
 *     body must re-scope (u_i at i ↦ r∧j). A family is passed as a reference
 *     with its scope map and becomes part of the origin: a term variable
 *     cannot stand for a family that is specialized along a dimension (its
 *     occurrences would lose the specialization), so these are the template's
 *     index rather than its formals. The free dimensions of shape data are
 *     canonicalized to template dimension formals (in increasing order of the
 *     actual identities), so an invocation whose shape differs by an
 *     order-preserving renaming of dimensions shares the template, and
 *     dimension substitutions commute with invocation at the template
 *     interface (formal ↦ interval).
 *
 * Generated names are keyed by (definition, role, slot[, shape]) only, so
 * provenance compares up to renaming and never depends on which arguments
 * an invocation happens to pass.
 * ==================================================================== */

enum {
    N_FILL = 1, N_PATHC, N_REFL, N_PAPPC, N_REV, N_CONCAT, N_FUN, N_CONTR,
    N_FIB, N_EQUIV, N_IDFUN, N_IDEQ, N_EXT, N_LINEEQ, N_UA,
    N_CPI, N_CSG, N_CPA, N_CU, N_CG
};
enum { ROLE_DIM = 1, ROLE_IV, ROLE_INT, ROLE_TERM, ROLE_BOUND };

#define TM_MAX 8
#define TM_DIMS (4 * TM_MAX)

typedef struct {
    RefId body;
    TermVarId formal[TM_MAX];
    DimVarId ivformal[TM_MAX];
} TmEntry;

static struct { WordMap idx; VEC(TmEntry) entries; pthread_mutex_t mu; bool init; } TT;

static void tt_init(void) {
    static pthread_mutex_t once = PTHREAD_MUTEX_INITIALIZER;
    pthread_mutex_lock(&once);
    if (!TT.init) { wordmap_init(&TT.idx); pthread_mutex_init(&TT.mu, NULL); TT.init = true; }
    pthread_mutex_unlock(&once);
}
void lib_free(void) {
    if (!TT.init) return;
    wordmap_free(&TT.idx); vec_free(&TT.entries); pthread_mutex_destroy(&TT.mu);
    memset(&TT, 0, sizeof TT);
}
size_t lib_template_count(void) {
    if (!TT.init) return 0;
    pthread_mutex_lock(&TT.mu); size_t n = TT.entries.len; pthread_mutex_unlock(&TT.mu);
    return n;
}

typedef struct {
    uint64_t def;
    RefId uref[TM_MAX]; size_t nref; RefId sref[TM_MAX];      /* shape references: actual, canonical */
    FaceId uface[TM_MAX]; size_t nface; FaceId sface[TM_MAX];
    uint64_t consts[TM_MAX]; size_t nconst;
    DimVarId udim[TM_MAX]; size_t nudim;                      /* explicitly registered dimensions */
    uint64_t actual[TM_DIMS]; DimVarId formal[TM_DIMS]; size_t nd;
    MapId canon;                                              /* actual ↦ formal */
    KeyWord key[TM_DIMS]; size_t nkey;
    bool hit; TmEntry e;
    MapBuilder inst;
} Tm;

static void tm_begin(Tm *t, uint64_t def) { memset(t, 0, sizeof *t); t->def = def; tt_init(); }
static void tm_use_ref(Tm *t, RefId r) { require(t->nref < TM_MAX, "template shape too large"); t->uref[t->nref++] = r; }
static void tm_use_face(Tm *t, FaceId f) { require(t->nface < TM_MAX, "template shape too large"); t->uface[t->nface++] = f; }
static void tm_use_dim(Tm *t, DimVarId i) { require(t->nudim < TM_MAX, "template shape too large"); t->udim[t->nudim++] = i; }

static DimVarId named_dim(uint64_t def, uint64_t role, uint64_t slot) {
    KeyWord k[4] = { { KW_CONST, 7000 }, { KW_CONST, def }, { KW_CONST, role }, { KW_CONST, slot } };
    return fresh_dim_keyed(k, 4);
}

static void key_words(const Tm *t, uint64_t *w, size_t *wn) {
    size_t n = 0;
    for (size_t k = 0; k < t->nkey; k++) { w[n++] = t->key[k].kind; w[n++] = t->key[k].v; }
    *wn = n;
}

/* collect the dimensions of the shape, assign canonical formals, canonicalize
 * the shape, build the key and look the template up */
static void tm_seal(Tm *t) {
    Words d; words_init(&d);
    for (size_t k = 0; k < t->nref; k++) { size_t n; const uint64_t *ds = dimset_get(ref_support(t->uref[k]), &n); words_append(&d, ds, n); }
    for (size_t k = 0; k < t->nface; k++) fc_dims(t->uface[k], &d);
    for (size_t k = 0; k < t->nudim; k++) words_push(&d, t->udim[k]);
    d.n = sort_unique_u64(d.w, d.n);
    /* a dimension that occurs in the declared type or required face of a
     * free variable of the shape is pinned: declarations are not renamed,
     * so it stays actual and is part of the index as it is */
    DimSetId pinned = dimset_make(NULL, 0);
    for (size_t k = 0; k < t->nref; k++) {
        size_t n; const uint64_t *xs = varset_get(ref_freevars(t->uref[k]), &n);
        for (size_t q = 0; q < n; q++) pinned = dimset_union(pinned, ref_support(ref_var((TermVarId)xs[q])));
    }
    MapBuilder b; mapb_init(&b);
    size_t nd = 0;
    for (size_t k = 0; k < d.n; k++) {
        if (dimset_contains(pinned, d.w[k])) continue;
        require(nd < TM_DIMS, "template shape mentions too many dimensions");
        t->actual[nd] = d.w[k];
        t->formal[nd] = named_dim(t->def, ROLE_DIM, nd);
        mapb_dim(&b, (DimVarId)d.w[k], iv_var(t->formal[nd]));
        nd++;
    }
    t->nd = nd;
    words_free(&d);
    t->canon = mapb_finish(&b);
    size_t n = 0;
    t->key[n++] = (KeyWord){ KW_CONST, t->def };
    for (size_t k = 0; k < t->nconst; k++) t->key[n++] = (KeyWord){ KW_CONST, t->consts[k] };
    for (size_t k = 0; k < t->nref; k++) { t->sref[k] = reindex(t->uref[k], t->canon); t->key[n++] = (KeyWord){ KW_REF, t->sref[k] }; }
    for (size_t k = 0; k < t->nface; k++) { t->sface[k] = fc_reindex(t->uface[k], t->canon); t->key[n++] = (KeyWord){ KW_FACE, t->sface[k] }; }
    t->nkey = n;
    uint64_t w[2 * TM_DIMS]; size_t wn; key_words(t, w, &wn);
    uint64_t v;
    pthread_mutex_lock(&TT.mu);
    if (wordmap_get(&TT.idx, w, wn, &v)) { t->hit = true; t->e = TT.entries.data[v - 1]; }
    pthread_mutex_unlock(&TT.mu);
    mapb_init(&t->inst);
}

/* the template's name for an actual dimension of the shape (itself when pinned) */
static DimVarId tm_dim_formal(Tm *t, DimVarId i) {
    for (size_t k = 0; k < t->nd; k++) if (t->actual[k] == i) return t->formal[k];
    return i;
}

static TermVarId keyed_formal(Tm *t, uint64_t role, uint64_t slot, RefId type, FaceId required) {
    KeyWord k[TM_DIMS + 4];
    k[0] = (KeyWord){ KW_CONST, 7001 }; k[1] = (KeyWord){ KW_CONST, role }; k[2] = (KeyWord){ KW_CONST, slot };
    memcpy(k + 3, t->key, t->nkey * sizeof(KeyWord));
    return fresh_term_keyed_req(k, t->nkey + 3, type, required);
}
/* a term formal of the template (an argument) */
static TermVarId tm_formal(Tm *t, size_t slot, RefId type, FaceId required) {
    require(slot < TM_MAX, "template slot");
    TermVarId x = keyed_formal(t, ROLE_TERM, slot, type, required);
    t->e.formal[slot] = x;
    return x;
}
/* a variable bound inside the body */
static TermVarId bound_formal(Tm *t, uint64_t slot, RefId type) { return keyed_formal(t, ROLE_BOUND, slot, type, fc_true()); }
static DimVarId tm_ivformal(Tm *t, size_t slot) {
    require(slot < TM_MAX, "template slot");
    DimVarId i = named_dim(t->def, ROLE_IV, slot);
    t->e.ivformal[slot] = i;
    return i;
}
/* an internal dimension of the body (a binder name, or a parameter that the
 * body substitutes away before it is complete) */
static DimVarId tm_internal(Tm *t, size_t slot) { return named_dim(t->def, ROLE_INT, slot); }

static void tm_store(Tm *t, RefId body) {
    t->e.body = body;
    uint64_t w[2 * TM_DIMS]; size_t wn; key_words(t, w, &wn);
    pthread_mutex_lock(&TT.mu);
    uint64_t v;
    if (!wordmap_get(&TT.idx, w, wn, &v)) { vec_push(&TT.entries, t->e); wordmap_put(&TT.idx, w, wn, TT.entries.len); }
    else t->e = TT.entries.data[v - 1];           /* a concurrent builder won: identical records */
    pthread_mutex_unlock(&TT.mu);
}
static void tm_arg(Tm *t, size_t slot, RefId image) { mapb_term(&t->inst, t->e.formal[slot], image); }
static void tm_ivarg(Tm *t, size_t slot, IntervalId r) { mapb_dim(&t->inst, t->e.ivformal[slot], r); }
static RefId tm_finish(Tm *t) {
    for (size_t k = 0; k < t->nd; k++) mapb_dim(&t->inst, t->formal[k], iv_var((DimVarId)t->actual[k]));
    return reindex(t->e.body, mapb_finish(&t->inst));
}

IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j) {
    IntervalId vj = iv_var(j);
    return iv_join(iv_meet(r, iv_negate(vj)), iv_meet(s, vj));
}

static RefId empty_system(void) { return mk_system(0, NULL, NULL); }

/* ---- filling and transport ---- */

RefId mk_fill(DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId a0, IntervalId r) {
    /* fill^i A_i [phi ↦ u_i] a0 (r) = comp^j A_{r∧j} [phi ↦ u_{r∧j}, (r=0) ↦ a0] a0
     * shape: i, A_i, phi, u_i (the tube is re-scoped); formal: a0; interval: r */
    Tm t; tm_begin(&t, N_FILL);
    tm_use_dim(&t, i); tm_use_ref(&t, A_i); tm_use_face(&t, phi); tm_use_ref(&t, u_i);
    tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId A = t.sref[0], u = t.sref[1]; FaceId ph = t.sface[0];
        TermVarId cap = tm_formal(&t, 0, reindex_dim(A, fi, iv_zero()), fc_true());
        DimVarId rho = tm_ivformal(&t, 0), j = tm_internal(&t, 0);
        IntervalId rj = iv_meet(iv_var(rho), iv_var(j));
        FaceId r0 = fc_endpoint(iv_var(rho), 0);
        FaceId faces[2] = { ph, r0 };
        RefId terms[2] = { reindex_dim(u, fi, rj), ref_var(cap) };
        tm_store(&t, mk_comp(j, reindex_dim(A, fi, rj), fc_join(ph, r0), mk_system(2, faces, terms), ref_var(cap)));
    }
    tm_arg(&t, 0, a0); tm_ivarg(&t, 0, r);
    return tm_finish(&t);
}

RefId mk_hcomp(DimVarId j, RefId X, FaceId phi, RefId u_j, RefId cap) { return mk_comp(j, X, phi, u_j, cap); }
RefId mk_coe(DimVarId i, RefId A_i, RefId a0) { return mk_comp(i, A_i, fc_false(), empty_system(), a0); }

/* ---- paths ---- */

RefId mk_path_const(RefId A, RefId l, RefId r) {
    Tm t; tm_begin(&t, N_PATHC); tm_use_ref(&t, A); tm_seal(&t);
    if (!t.hit) {
        RefId Af = t.sref[0];
        TermVarId xl = tm_formal(&t, 0, Af, fc_true()), xr = tm_formal(&t, 1, Af, fc_true());
        tm_store(&t, mk_path(tm_internal(&t, 0), Af, ref_var(xl), ref_var(xr)));
    }
    tm_arg(&t, 0, l); tm_arg(&t, 1, r);
    return tm_finish(&t);
}

RefId mk_refl(RefId A, RefId a) {
    Tm t; tm_begin(&t, N_REFL); tm_use_ref(&t, A); tm_seal(&t);
    if (!t.hit) {
        TermVarId v = tm_formal(&t, 0, t.sref[0], fc_true());
        tm_store(&t, mk_plam(tm_internal(&t, 0), ref_var(v)));
    }
    tm_arg(&t, 0, a);
    return tm_finish(&t);
}

RefId mk_papp_const(RefId A, RefId l, RefId r, RefId p, IntervalId s) {
    Tm t; tm_begin(&t, N_PAPPC); tm_use_ref(&t, A); tm_seal(&t);
    if (!t.hit) {
        RefId Af = t.sref[0];
        TermVarId xl = tm_formal(&t, 0, Af, fc_true()), xr = tm_formal(&t, 1, Af, fc_true());
        TermVarId xp = tm_formal(&t, 2, mk_path_const(Af, ref_var(xl), ref_var(xr)), fc_true());
        DimVarId sv = tm_ivformal(&t, 0);
        tm_store(&t, mk_papp(tm_internal(&t, 0), Af, ref_var(xl), ref_var(xr), ref_var(xp), iv_var(sv)));
    }
    tm_arg(&t, 0, l); tm_arg(&t, 1, r); tm_arg(&t, 2, p); tm_ivarg(&t, 0, s);
    return tm_finish(&t);
}

RefId mk_path_rev(RefId A, RefId l, RefId r, RefId p) {
    Tm t; tm_begin(&t, N_REV); tm_use_ref(&t, A); tm_seal(&t);
    if (!t.hit) {
        RefId Af = t.sref[0];
        TermVarId xl = tm_formal(&t, 0, Af, fc_true()), xr = tm_formal(&t, 1, Af, fc_true());
        TermVarId xp = tm_formal(&t, 2, mk_path_const(Af, ref_var(xl), ref_var(xr)), fc_true());
        DimVarId i = tm_internal(&t, 0);
        tm_store(&t, mk_plam(i, mk_papp_const(Af, ref_var(xl), ref_var(xr), ref_var(xp), iv_negate(iv_var(i)))));
    }
    tm_arg(&t, 0, l); tm_arg(&t, 1, r); tm_arg(&t, 2, p);
    return tm_finish(&t);
}

RefId mk_path_concat(RefId A, RefId x, RefId y, RefId z, RefId p, RefId q) {
    /* p·q = ⟨i⟩ hcomp^j_A [(i=0) ↦ x, (i=1) ↦ q(j)] p(i) */
    Tm t; tm_begin(&t, N_CONCAT); tm_use_ref(&t, A); tm_seal(&t);
    if (!t.hit) {
        RefId Af = t.sref[0];
        TermVarId vx = tm_formal(&t, 0, Af, fc_true()), vy = tm_formal(&t, 1, Af, fc_true()), vz = tm_formal(&t, 2, Af, fc_true());
        TermVarId vp = tm_formal(&t, 3, mk_path_const(Af, ref_var(vx), ref_var(vy)), fc_true());
        TermVarId vq = tm_formal(&t, 4, mk_path_const(Af, ref_var(vy), ref_var(vz)), fc_true());
        DimVarId i = tm_internal(&t, 0), j = tm_internal(&t, 1);
        FaceId faces[2] = { fc_lit(i, 0), fc_lit(i, 1) };
        RefId terms[2] = { ref_var(vx), mk_papp_const(Af, ref_var(vy), ref_var(vz), ref_var(vq), iv_var(j)) };
        RefId body = mk_hcomp(j, Af, fc_join(faces[0], faces[1]), mk_system(2, faces, terms),
                              mk_papp_const(Af, ref_var(vx), ref_var(vy), ref_var(vp), iv_var(i)));
        tm_store(&t, mk_plam(i, body));
    }
    tm_arg(&t, 0, x); tm_arg(&t, 1, y); tm_arg(&t, 2, z); tm_arg(&t, 3, p); tm_arg(&t, 4, q);
    return tm_finish(&t);
}

/* ---- equivalence data (§15) ---- */

RefId mk_fun(RefId X, RefId Y) {
    Tm t; tm_begin(&t, N_FUN); tm_use_ref(&t, X); tm_use_ref(&t, Y); tm_seal(&t);
    if (!t.hit) { TermVarId x = bound_formal(&t, 0, t.sref[0]); tm_store(&t, mk_pi(x, t.sref[0], t.sref[1])); }
    return tm_finish(&t);
}

RefId mk_contr(RefId X) {
    Tm t; tm_begin(&t, N_CONTR); tm_use_ref(&t, X); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0];
        TermVarId c = bound_formal(&t, 0, Xf), x = bound_formal(&t, 1, Xf);
        tm_store(&t, mk_sigma(c, Xf, mk_pi(x, Xf, mk_path_const(Xf, ref_var(c), ref_var(x)))));
    }
    return tm_finish(&t);
}

RefId mk_fib(RefId X, RefId Y, RefId f, RefId y) {
    Tm t; tm_begin(&t, N_FIB); tm_use_ref(&t, X); tm_use_ref(&t, Y); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0], Yf = t.sref[1];
        TermVarId vf = tm_formal(&t, 0, mk_fun(Xf, Yf), fc_true()), vy = tm_formal(&t, 1, Yf, fc_true());
        TermVarId x = bound_formal(&t, 0, Xf);
        tm_store(&t, mk_sigma(x, Xf, mk_path_const(Yf, mk_app(ref_var(vf), ref_var(x)), ref_var(vy))));
    }
    tm_arg(&t, 0, f); tm_arg(&t, 1, y);
    return tm_finish(&t);
}

RefId mk_equiv(RefId X, RefId Y) {
    Tm t; tm_begin(&t, N_EQUIV); tm_use_ref(&t, X); tm_use_ref(&t, Y); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0], Yf = t.sref[1];
        RefId XY = mk_fun(Xf, Yf);
        TermVarId f = bound_formal(&t, 0, XY), y = bound_formal(&t, 1, Yf);
        tm_store(&t, mk_sigma(f, XY, mk_pi(y, Yf, mk_contr(mk_fib(Xf, Yf, ref_var(f), ref_var(y))))));
    }
    return tm_finish(&t);
}

RefId mk_id_fun(RefId X) {
    Tm t; tm_begin(&t, N_IDFUN); tm_use_ref(&t, X); tm_seal(&t);
    if (!t.hit) { TermVarId x = bound_formal(&t, 0, t.sref[0]); tm_store(&t, mk_lam(x, t.sref[0], ref_var(x))); }
    return tm_finish(&t);
}

RefId mk_id_equiv(RefId X) {
    /* (id, λy. ((y, refl), λw. ⟨i⟩ (p(¬i), ⟨j⟩ p(¬i ∨ j))))  with (x,p) = w */
    Tm t; tm_begin(&t, N_IDEQ); tm_use_ref(&t, X); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0];
        RefId idf = mk_id_fun(Xf);
        TermVarId y = bound_formal(&t, 0, Xf);
        RefId fib = mk_fib(Xf, Xf, idf, ref_var(y));
        TermVarId w = bound_formal(&t, 1, fib);
        RefId xw = mk_fst(ref_var(w)), p = mk_snd(ref_var(w));
        RefId idx = mk_app(idf, xw);                 /* f x, as the fibre type states it */
        DimVarId i = tm_internal(&t, 0), j = tm_internal(&t, 1);
        IntervalId ni = iv_negate(iv_var(i));
        RefId first = mk_papp_const(Xf, idx, ref_var(y), p, ni);
        RefId second = mk_plam(j, mk_papp_const(Xf, idx, ref_var(y), p, iv_join(ni, iv_var(j))));
        RefId contraction = mk_lam(w, fib, mk_plam(i, mk_pair_at(fib, first, second)));
        RefId centre = mk_pair_at(fib, ref_var(y), mk_refl(Xf, ref_var(y)));
        tm_store(&t, mk_pair_at(mk_equiv(Xf, Xf), idf, mk_lam(y, Xf, mk_pair_at(mk_contr(fib), centre, contraction))));
    }
    return tm_finish(&t);
}

RefId equiv_map(RefId e) { return mk_fst(e); }
RefId equiv_contr(RefId e, RefId y) { return mk_app(mk_snd(e), y); }

RefId mk_extend_contr(RefId X, RefId c, RefId k, FaceId theta, RefId v) {
    /* hcomp^j_X [theta ↦ k(v)@j] c ; v is only used under theta */
    Tm t; tm_begin(&t, N_EXT); tm_use_ref(&t, X); tm_use_face(&t, theta); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0]; FaceId th = t.sface[0];
        TermVarId vc = tm_formal(&t, 0, Xf, fc_true());
        TermVarId x = bound_formal(&t, 0, Xf);
        TermVarId vk = tm_formal(&t, 1, mk_pi(x, Xf, mk_path_const(Xf, ref_var(vc), ref_var(x))), fc_true());
        TermVarId vv = tm_formal(&t, 2, Xf, th);
        DimVarId j = tm_internal(&t, 0);
        RefId tube = mk_papp_const(Xf, ref_var(vc), ref_var(vv), mk_app(ref_var(vk), ref_var(vv)), iv_var(j));
        tm_store(&t, mk_hcomp(j, Xf, th, tube, ref_var(vc)));
    }
    tm_arg(&t, 0, c); tm_arg(&t, 1, k); tm_arg(&t, 2, v);
    return tm_finish(&t);
}

RefId mk_line_equiv(DimVarId j, RefId X_j) {
    Tm t; tm_begin(&t, N_LINEEQ); tm_use_dim(&t, j); tm_use_ref(&t, X_j); tm_seal(&t);
    if (!t.hit) {
        DimVarId fj = tm_dim_formal(&t, j);
        RefId Xf = t.sref[0], X0 = reindex_dim(Xf, fj, iv_zero());
        tm_store(&t, mk_coe(fj, mk_equiv(X0, Xf), mk_id_equiv(X0)));
    }
    return tm_finish(&t);
}

RefId mk_ua(RefId X, RefId Y, RefId e) {
    Tm t; tm_begin(&t, N_UA); tm_use_ref(&t, X); tm_use_ref(&t, Y); tm_seal(&t);
    if (!t.hit) {
        RefId Xf = t.sref[0], Yf = t.sref[1];
        TermVarId ve = tm_formal(&t, 0, mk_equiv(Xf, Yf), fc_true());
        DimVarId i = tm_internal(&t, 0);
        FaceId faces[2] = { fc_lit(i, 0), fc_lit(i, 1) };
        RefId Ts[2] = { Xf, Yf };
        RefId es[2] = { ref_var(ve), mk_id_equiv(Yf) };
        tm_store(&t, mk_plam(i, mk_glue_type(Yf, fc_join(faces[0], faces[1]), mk_system(2, faces, Ts), mk_system(2, faces, es))));
    }
    tm_arg(&t, 0, e);
    return tm_finish(&t);
}

/* ---- structural composition clauses (§14, §16, §17) ----
 * shape: the opened dimension i, the exposed family head and the tube face
 * (and the tube where the clause re-scopes it); formals: the cap, and the
 * tube where the clause uses it in place. */

RefId comp_clause_pi(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Tm t; tm_begin(&t, N_CPI); tm_use_dim(&t, i); tm_use_ref(&t, fam); tm_use_face(&t, phi); tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId F = t.sref[0]; FaceId ph = t.sface[0];
        Head h; open_ref(F, &h);
        require(h.tag == T_PI, "pi clause on a non-pi head");
        RefId D_i = h.f[0].id;
        head_free(&h);
        RefId D_1 = reindex_dim(D_i, fi, iv_one());
        TermVarId u = tm_formal(&t, 0, F, ph);
        TermVarId f0 = tm_formal(&t, 1, reindex_dim(F, fi, iv_zero()), fc_true());
        TermVarId x1 = bound_formal(&t, 0, D_1);
        DimVarId rho = tm_internal(&t, 0), jj = tm_internal(&t, 1);
        /* shared backward filler v(r) = fill^j D_{¬j} [] x1 (¬r), built once with r = rho */
        RefId D_negj = reindex_dim(D_i, fi, iv_negate(iv_var(jj)));
        RefId V = mk_fill(jj, D_negj, fc_false(), empty_system(), ref_var(x1), iv_negate(iv_var(rho)));
        RefId v_i = reindex_dim(V, rho, iv_var(fi));
        RefId v_0 = reindex_dim(V, rho, iv_zero());
        RefId E_i = apply_term_binder(F, 0, 1, v_i);          /* E_i(v(i)), i free */
        RefId body = mk_comp(fi, E_i, ph, mk_app(ref_var(u), v_i), mk_app(ref_var(f0), v_0));
        tm_store(&t, mk_lam(x1, D_1, body));
    }
    tm_arg(&t, 0, u_i); tm_arg(&t, 1, cap);
    return tm_finish(&t);
}

RefId comp_clause_sigma(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    /* the tube's first component is re-scoped inside the filler: shape */
    Tm t; tm_begin(&t, N_CSG); tm_use_dim(&t, i); tm_use_ref(&t, fam); tm_use_face(&t, phi); tm_use_ref(&t, u_i); tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId F = t.sref[0], u = t.sref[1]; FaceId ph = t.sface[0];
        Head h; open_ref(F, &h);
        require(h.tag == T_SIGMA, "sigma clause on a non-sigma head");
        RefId D_i = h.f[0].id;
        head_free(&h);
        TermVarId z0 = tm_formal(&t, 0, reindex_dim(F, fi, iv_zero()), fc_true());
        DimVarId rho = tm_internal(&t, 0);
        RefId A = mk_fill(fi, D_i, ph, mk_fst(u), mk_fst(ref_var(z0)), iv_var(rho));   /* a(rho), one reference */
        RefId a_i = reindex_dim(A, rho, iv_var(fi));
        RefId a_1 = reindex_dim(A, rho, iv_one());
        RefId E_i = apply_term_binder(F, 0, 1, a_i);
        RefId b_1 = mk_comp(fi, E_i, ph, mk_snd(u), mk_snd(ref_var(z0)));
        tm_store(&t, mk_pair_at(reindex_dim(F, fi, iv_one()), a_1, b_1));
    }
    tm_arg(&t, 0, cap);
    return tm_finish(&t);
}

RefId comp_clause_path(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    Tm t; tm_begin(&t, N_CPA); tm_use_dim(&t, i); tm_use_ref(&t, fam); tm_use_face(&t, phi); tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId F = t.sref[0]; FaceId ph = t.sface[0];
        Head h; open_ref(F, &h);
        require(h.tag == T_PATH, "path clause on a non-path head");
        RefId l_i = h.f[1].id, r_i = h.f[2].id;
        head_free(&h);
        TermVarId u = tm_formal(&t, 0, F, ph);
        TermVarId p0 = tm_formal(&t, 1, reindex_dim(F, fi, iv_zero()), fc_true());
        DimOpen B = resolve_dim_binder(F, 0, 0);               /* B(i, k), formal k = B.j */
        DimVarId j = tm_internal(&t, 0);
        RefId B_ij = reindex_dim(B.body, B.j, iv_var(j));
        RefId u_at_j = mk_papp(B.j, B.body, l_i, r_i, ref_var(u), iv_var(j));
        /* the cap lives at i = 0 */
        RefId B0 = reindex_dim(B.body, fi, iv_zero());
        RefId cap_at_j = mk_papp(B.j, B0, reindex_dim(l_i, fi, iv_zero()), reindex_dim(r_i, fi, iv_zero()), ref_var(p0), iv_var(j));
        FaceId faces[3] = { ph, fc_lit(j, 0), fc_lit(j, 1) };
        RefId terms[3] = { u_at_j, l_i, r_i };
        FaceId face = fc_join(ph, fc_join(faces[1], faces[2]));
        RefId body = mk_comp(fi, B_ij, face, mk_system(3, faces, terms), cap_at_j);
        tm_store(&t, mk_plam(j, body));
    }
    tm_arg(&t, 0, u_i); tm_arg(&t, 1, cap);
    return tm_finish(&t);
}

RefId comp_clause_universe(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap) {
    /* comp^i U [phi ↦ U_i] A_0 → Glue [phi ↦ (U_1, LineEquiv(j ↦ U_{¬j}))] A_0 ; the
     * moving type U_i is re-scoped: shape. The cap is a term of U_ℓ. */
    Tm t; tm_begin(&t, N_CU); tm_use_dim(&t, i); tm_use_ref(&t, fam); tm_use_face(&t, phi); tm_use_ref(&t, u_i); tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId F = t.sref[0], u = t.sref[1]; FaceId ph = t.sface[0];
        Head h; open_ref(F, &h);
        require(h.tag == T_UNIVERSE, "universe clause on a non-universe head");
        head_free(&h);
        TermVarId A0 = tm_formal(&t, 0, F, fc_true());
        RefId U_1 = reindex_dim(u, fi, iv_one());
        DimVarId j = tm_internal(&t, 0);
        RefId X_j = reindex_dim(u, fi, iv_negate(iv_var(j)));
        tm_store(&t, mk_glue_type(ref_var(A0), ph, U_1, mk_line_equiv(j, X_j)));
    }
    tm_arg(&t, 0, cap);
    return tm_finish(&t);
}

RefId comp_clause_glue(DimVarId i, RefId fam, FaceId psi, RefId u_i, RefId u_0) {
    Tm t; tm_begin(&t, N_CG); tm_use_dim(&t, i); tm_use_ref(&t, fam); tm_use_face(&t, psi); tm_use_ref(&t, u_i); tm_seal(&t);
    if (!t.hit) {
        DimVarId fi = tm_dim_formal(&t, i);
        RefId F = t.sref[0], u = t.sref[1]; FaceId ps = t.sface[0];
        Head h; open_ref(F, &h);
        require(h.tag == T_GLUE_TYPE, "glue clause on a non-glue head");
        RefId A_i = h.f[0].id; FaceId alpha_i = h.f[1].id; RefId T_i = h.f[2].id, e_i = h.f[3].id;
        head_free(&h);
        IntervalId zero = iv_zero(), one = iv_one();
        RefId A_0 = reindex_dim(A_i, fi, zero), T_0 = reindex_dim(T_i, fi, zero), e_0 = reindex_dim(e_i, fi, zero);
        FaceId alpha_0 = fc_reindex(alpha_i, map_single_dim(fi, zero));
        RefId A_1 = reindex_dim(A_i, fi, one), T_1 = reindex_dim(T_i, fi, one), e_1 = reindex_dim(e_i, fi, one);
        FaceId alpha_1 = fc_reindex(alpha_i, map_single_dim(fi, one));
        RefId u_1 = reindex_dim(u, fi, one);
        TermVarId g0 = tm_formal(&t, 0, reindex_dim(F, fi, zero), fc_true());
        RefId cap = ref_var(g0);

        /* base filler */
        RefId a0 = mk_unglue(A_0, alpha_0, T_0, e_0, cap);
        RefId ungl_i = mk_unglue(A_i, alpha_i, T_i, e_i, u);
        DimVarId rho = tm_internal(&t, 0);
        RefId Afill = mk_fill(fi, A_i, ps, ungl_i, a0, iv_var(rho));
        RefId a_i = reindex_dim(Afill, rho, iv_var(fi));
        RefId a1 = reindex_dim(Afill, rho, one);

        /* on delta = ∀i alpha_i the fibre line is available: the constructions
         * below are declared partial on delta (§2 required_face annotation) */
        FaceId delta = fc_forall(fi, alpha_i);
        RefId f_i = equiv_map(e_i), f_1 = equiv_map(e_1);      /* partial on alpha_i / alpha_1 by their own data */
        term_require_push(delta);
        RefId Tfill = mk_fill(fi, T_i, ps, u, cap, iv_var(rho));
        RefId t_i = reindex_dim(Tfill, rho, iv_var(fi));
        RefId t1p = reindex_dim(Tfill, rho, one);
        DimVarId q = tm_internal(&t, 1);
        FaceId wf[3] = { ps, fc_lit(q, 0), fc_lit(q, 1) };
        RefId wt[3] = { a_i, mk_app(f_i, t_i), a_i };
        RefId omega_q = mk_comp(fi, A_i, fc_join(ps, fc_join(wf[1], wf[2])), mk_system(3, wf, wt), a0);
        RefId omega = mk_plam(q, omega_q);                      /* f_1(t1') = a1 */
        term_require_pop();

        /* under alpha_1: extend [delta ↦ (t1', omega), psi ↦ (u_1, refl)] in fib(f_1, a1) */
        term_require_push(alpha_1);
        RefId fibT = mk_fib(T_1, A_1, f_1, a1);
        FaceId pf[2] = { delta, ps };
        RefId pt[2] = { mk_pair_at(fibT, t1p, omega), mk_pair_at(fibT, u_1, mk_refl(A_1, a1)) };
        RefId P = mk_system(2, pf, pt);
        RefId C = equiv_contr(e_1, a1);
        RefId ext = mk_extend_contr(fibT, mk_fst(C), mk_snd(C), fc_join(delta, ps), P);
        RefId t1 = mk_fst(ext), p = mk_snd(ext);                /* p : f_1(t1) = a1 */
        term_require_pop();

        /* repair the base endpoint */
        DimVarId q2 = tm_internal(&t, 2);
        FaceId rf[2] = { alpha_1, ps };
        RefId rt[2] = { mk_papp_const(A_1, mk_app(f_1, t1), a1, p, iv_negate(iv_var(q2))), a1 };
        RefId a1p = mk_hcomp(q2, A_1, fc_join(alpha_1, ps), mk_system(2, rf, rt), a1);
        tm_store(&t, mk_glue_intro(A_1, alpha_1, T_1, e_1, t1, a1p));
    }
    tm_arg(&t, 0, u_0);
    return tm_finish(&t);
}

/* Acceptance checks (§23) and law checks for the scope / face / evaluator
 * layers. Run under ASan+UBSan via `make test`. */
#include "../src/eval.h"
#include "../src/template.h"
#include "../src/eval.h"

static int n_pass = 0, n_fail = 0;
#define CHECK(cond, ...) do { if (cond) { n_pass++; } else { n_fail++; printf("  FAIL (%s:%d): ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)
#define SECTION(name) printf("== %s\n", name)

static RefId U0;
static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }
static RefId var(RefId type) { return ref_var(tv(type)); }
static RefId fun(RefId X, RefId Y) { return mk_pi(tv(X), X, Y); }
static RefId path_const(RefId A, RefId a, RefId b) { return mk_path(declare_dim(), A, a, b); }
static RefId papp_const(RefId A, RefId a, RefId b, RefId p, IntervalId s) { return mk_papp(declare_dim(), A, a, b, p, s); }

static Tag head_tag(EvalResult r) {
    Head h; open_ref(r.ref, &h); Tag t = h.is_var ? 0 : h.tag; head_free(&h); return t;
}

/* ---------------------------------------------------------------- */
/* the number of whnf keys formed so far */
static size_t whnf_keys(void) { size_t c = 0, n = eval_entry_count(); for (EntryId e = 1; e <= n; e++) if (eval_entry_live(e) && eval_entry_family(e) == F_WHNF) c++; return c; }
static void test_intervals_faces(void) {
    SECTION("§3–4 canonical intervals and faces");
    DimVarId i = declare_dim(), j = declare_dim();
    IntervalId vi = iv_var(i), vj = iv_var(j);
    CHECK(iv_meet(vi, vi) == vi, "i ∧ i is the same canonical interval as i");
    CHECK(iv_join(vi, vi) == vi, "i ∨ i = i");
    IntervalId ini = iv_meet(vi, iv_negate(vi));
    CHECK(!iv_is_zero(ini), "i ∧ ¬i is retained (not Boolean)");
    CHECK(!iv_is_one(iv_join(vi, iv_negate(vi))), "i ∨ ¬i ≠ 1");
    { size_t n; const uint64_t *w = interner_get(&M.keys, ini, &n); CHECK(n == 3 && w[2] == DNF_SEP, "i ∧ ¬i is one clause of two atoms"); }
    CHECK(iv_negate(iv_zero()) == iv_one() && iv_negate(iv_one()) == iv_zero(), "¬0 = 1, ¬1 = 0");
    CHECK(iv_negate(iv_negate(iv_meet(vi, vj))) == iv_meet(vi, vj), "double negation (De Morgan) is identity");
    CHECK(iv_negate(iv_meet(vi, vj)) == iv_join(iv_negate(vi), iv_negate(vj)), "¬(i∧j) = ¬i ∨ ¬j");
    CHECK(iv_meet(iv_join(vi, vj), vi) == vi, "absorption (i∨j)∧i = i");

    CHECK(fc_is_false(fc_meet(fc_lit(i, 0), fc_lit(i, 1))), "(i=0) ∧ (i=1) = false");
    CHECK(!fc_is_true(fc_join(fc_lit(i, 0), fc_lit(i, 1))), "(i=0) ∨ (i=1) is not true");
    CHECK(fc_endpoint(iv_negate(vi), 0) == fc_lit(i, 1), "(¬i = 0) = (i = 1)");
    CHECK(fc_endpoint(iv_negate(vi), 1) == fc_lit(i, 0), "(¬i = 1) = (i = 0)");
    CHECK(fc_endpoint(iv_zero(), 0) == fc_true() && fc_endpoint(iv_zero(), 1) == fc_false(), "(0=0)=true, (0=1)=false");
    CHECK(fc_endpoint(iv_one(), 1) == fc_true() && fc_endpoint(iv_one(), 0) == fc_false(), "(1=1)=true, (1=0)=false");
    CHECK(fc_endpoint(iv_meet(vi, vj), 1) == fc_meet(fc_lit(i, 1), fc_lit(j, 1)), "(i∧j = 1) = (i=1)∧(j=1)");
    CHECK(fc_endpoint(iv_meet(vi, vj), 0) == fc_join(fc_lit(i, 0), fc_lit(j, 0)), "(i∧j = 0) = (i=0)∨(j=0)");
    CHECK(fc_endpoint(ini, 1) == fc_false(), "(i∧¬i = 1) = false");
    CHECK(fc_endpoint(ini, 0) == fc_join(fc_lit(i, 0), fc_lit(i, 1)), "(i∧¬i = 0) = (i=0)∨(i=1), not true");

    FaceId both = fc_meet(fc_lit(i, 0), fc_lit(j, 0));
    uint64_t Sj[1] = { j };
    CHECK(fc_project(both, set_make(Sj, 1)) == fc_lit(j, 0), "π_{j}((i=0)∧(j=0)) = (j=0)");
    CHECK(fc_forall(i, both) == fc_false(), "∀i((i=0)∧(j=0)) = false");
    CHECK(fc_forall(i, fc_join(fc_lit(i, 0), fc_lit(j, 0))) == fc_lit(j, 0), "∀i((i=0)∨(j=0)) = (j=0)");
    CHECK(fc_project(fc_false(), set_make(NULL, 0)) == fc_false(), "π_∅(false) = false");
    CHECK(fc_project(both, set_make(NULL, 0)) == fc_true(), "π_∅ of a consistent face = true");
    CHECK(fc_entails(fc_false(), fc_lit(i, 0)) && fc_entails(fc_lit(i, 0), fc_true()), "false ⇒ φ, φ ⇒ true");
    CHECK(fc_entails(both, fc_lit(i, 0)) && !fc_entails(fc_lit(i, 0), both), "clause containment entailment");

    /* substitution of a face through an interval map */
    MapId m = map_single_dim(i, iv_meet(vj, iv_negate(vj)));
    CHECK(fc_reindex(fc_lit(i, 1), m) == fc_false(), "(i=1)[i ↦ j∧¬j] = false");
    CHECK(fc_reindex(fc_lit(i, 0), m) == fc_join(fc_lit(j, 0), fc_lit(j, 1)), "(i=0)[i ↦ j∧¬j] = (j=0)∨(j=1)");
    /* interval substitution is single-lookup: [i ↦ j, j ↦ ¬i] */
    MapBuilder b; mapb_init(&b); mapb_dim(&b, i, vj); mapb_dim(&b, j, iv_negate(vi));
    MapId sw = mapb_finish(&b);
    CHECK(iv_reindex(iv_meet(vi, vj), sw) == iv_meet(vj, iv_negate(vi)), "simultaneous interval substitution");
}

/* exhaustive law check over all canonical faces on two dimensions */
static void test_face_laws(void) {
    SECTION("§5 projection / quantification laws, exhaustive on 2 dimensions");
    DimVarId i = declare_dim(), j = declare_dim();
    uint64_t lits[4] = { FC_LIT(i, 0), FC_LIT(i, 1), FC_LIT(j, 0), FC_LIT(j, 1) };
    /* consistent clauses = subsets of literals with no contradictory pair */
    uint64_t clauses[16]; size_t nc = 0;
    for (unsigned mask = 0; mask < 16; mask++) {
        if ((mask & 3) == 3 || (mask & 12) == 12) continue;
        clauses[nc++] = mask;
    }
    CHECK(nc == 9, "9 consistent clauses");
    FaceId *faces = malloc(1024 * sizeof(FaceId)); size_t nf = 0;
    for (unsigned sub = 0; sub < (1u << nc); sub++) {
        FaceId f = fc_false();
        for (size_t c = 0; c < nc; c++) if (sub & (1u << c)) {
            FaceId cl = fc_true();
            for (int l = 0; l < 4; l++) if (clauses[c] & (1u << l)) cl = fc_meet(cl, fc_lit(FC_LIT_DIM(lits[l]), FC_LIT_EPS(lits[l])));
            f = fc_join(f, cl);
        }
        bool seen = false;
        for (size_t k = 0; k < nf; k++) if (faces[k] == f) { seen = true; break; }
        if (!seen) faces[nf++] = f;
    }
    CHECK(nf == 48, "48 canonical faces on two dimensions (got %zu)", nf);
    uint64_t Ss[4][2] = { {0, 0}, {i, 0}, {j, 0}, {i < j ? i : j, i < j ? j : i} };
    size_t Sn[4] = { 0, 1, 1, 2 };
    size_t comparisons = 0; bool ok = true;
    for (int s = 0; s < 4; s++) {
        for (size_t a = 0; a < nf; a++) {
            FaceId chi = faces[a];
            FaceId pr = fc_project(chi, set_make(Ss[s], Sn[s]));
            /* chi ⇒ π_S chi ; idempotence */
            if (!fc_entails(chi, pr)) ok = false;
            if (fc_project(pr, set_make(Ss[s], Sn[s])) != pr) ok = false;
            for (size_t bb = 0; bb < nf; bb++) {
                FaceId phi = faces[bb];
                size_t dn; const uint64_t *dw = set_get(family_call(F_DIMS, phi, 0), &dn);
                bool inS = true;
                for (size_t k = 0; k < dn; k++) {
                    bool found = false;
                    for (size_t q = 0; q < Sn[s]; q++) if (Ss[s][q] == dw[k]) found = true;
                    if (!found) inS = false;
                }
                if (!inS) continue;
                comparisons++;
                if (fc_entails(chi, phi) != fc_entails(pr, phi)) ok = false;
            }
        }
    }
    CHECK(ok, "χ ⇒ φ ⟺ π_S χ ⇒ φ for FV(φ) ⊆ S, and χ ⇒ π_S χ, π_S π_S = π_S");
    /* ∀i φ: largest i-independent face entailing φ */
    bool okq = true; size_t qcomp = 0;
    for (size_t a = 0; a < nf; a++) {
        FaceId phi = faces[a], all = fc_forall(i, phi);
        if (!fc_entails(all, phi)) okq = false;
        if (set_contains(family_call(F_DIMS, all, 0), i)) okq = false;
        for (size_t bb = 0; bb < nf; bb++) {
            FaceId psi = faces[bb];
            bool indep = !set_contains(family_call(F_DIMS, psi, 0), i);
            if (!indep) continue;
            qcomp++;
            if (fc_entails(psi, phi) && !fc_entails(psi, all)) okq = false;
        }
    }
    CHECK(okq, "∀i φ ⇒ φ, is i-free, and is the largest such");
    printf("  %zu projection comparisons, %zu quantifier comparisons\n", comparisons, qcomp);
    free(faces);
}

/* ---------------------------------------------------------------- */
static void test_substitution(void) {
    SECTION("§6–7 simultaneous substitution, boundary restriction, support");
    RefId A = var(U0);
    TermVarId x = tv(A), y = tv(A), z = tv(A);
    MapBuilder b; mapb_init(&b); mapb_term(&b, x, ref_var(y)); mapb_term(&b, y, ref_var(z));
    MapId m = mapb_finish(&b);
    CHECK(reindex(ref_var(x), m) == ref_var(y), "x[x→y, y→z] = y");
    CHECK(reindex(reindex(ref_var(x), map_single_term(x, ref_var(y))), map_single_term(y, ref_var(z))) == ref_var(z), "(x[x→y])[y→z] = z");
    MapId c = compose(map_single_term(x, ref_var(y)), map_single_term(y, ref_var(z)));
    CHECK(reindex(ref_var(x), c) == ref_var(z) && reindex(ref_var(y), c) == ref_var(z), "compose(σ,τ) = σ;τ, including keys only in τ");
    CHECK(map_is_identity(map_identity()) && reindex(ref_var(x), map_identity()) == ref_var(x), "identity map");

    /* R = (y, y); x absent from its typed boundary */
    RefId R = mk_pair(ref_var(y), ref_var(y));
    RefId a = var(A), bb = var(A);
    CHECK(reindex1(R, x, a) == reindex1(R, x, bb) && reindex1(R, x, a) == R, "R[x→a] and R[x→b] intern to the same RefId when x ∉ boundary");
    RefId Rx = mk_pair(ref_var(x), ref_var(y));
    CHECK(reindex1(Rx, x, a) != reindex1(Rx, x, bb), "but differ when x is in the boundary");
    CHECK(reindex1(reindex1(Rx, x, a), x, bb) == reindex1(Rx, x, a), "second substitution is a separate operation");

    /* typed boundary through declaration types: w : P(x) depends on x */
    RefId Pfam = var(fun(A, U0));
    TermVarId w = tv(mk_app(Pfam, ref_var(x)));
    RefId W = ref_var(w);
    CHECK(set_contains(ref_freevars(W), x), "boundary of VAR(w) includes x through w's declaration type");
    RefId Wsub = reindex1(mk_fst(mk_pair(W, W)), x, a);
    { bool has_a = false; TEnvId E = ref_tenv(Wsub); for (size_t q = 0; q < subst_size(E); q++) { uint64_t sl; TVal v; subst_get(E, q, &sl, &v); if (v.sort == PS_REF && v.id == a) has_a = true; }
      CHECK(Wsub != mk_fst(mk_pair(W, W)) && has_a, "x is in the complete typed boundary through w's declaration type, so its image is retained"); }
    RefId Wsub2 = reindex1(mk_fst(mk_pair(ref_var(y), ref_var(y))), x, a);
    CHECK(Wsub2 == mk_fst(mk_pair(ref_var(y), ref_var(y))), "a variable whose type is independent of x drops the x entry");

    /* instantiated support: image of x introduces dimension j */
    DimVarId j = declare_dim();
    RefId pth = var(path_const(A, a, bb));
    RefId at_j = papp_const(A, a, bb, pth, iv_var(j));   /* depends on j */
    RefId T = mk_pair(ref_var(x), ref_var(y));
    CHECK(!set_contains(ref_support(T), j), "origin has no j");
    RefId Tj = reindex1(T, x, at_j);
    CHECK(set_contains(ref_support(Tj), j), "instantiated support includes j introduced by the image of x");
    /* support through a declaration type depending on a dimension */
    TermVarId v = tv(mk_app(Pfam, at_j));
    CHECK(set_contains(ref_support(ref_var(v)), j), "support of VAR(v) includes dimensions of v's declaration type");
}

/* ---------------------------------------------------------------- */
static void test_binders(void) {
    SECTION("§8–9 binders and opening");
    RefId A = var(U0);
    TermVarId x = tv(A);
    RefId id = mk_lam_lv(0, x, A, ref_var(x));
    RefId a = var(A);
    CHECK(apply_term_binder(id, 0, 1, a) == a, "apply λx.x to a gives a");
    TermOpen o1 = resolve_term_binder(id, 0, 1), o2 = resolve_term_binder(id, 0, 1);
    CHECK(o1.x == o2.x && o1.x != x, "reopening the same owner/slot gives the same fresh binder identity");
    CHECK(o1.body == ref_var(o1.x) && o1.type == A, "opened body is VAR(x_new) at domain type");
    /* capture: substitute into the body a term mentioning the original formal */
    RefId K = mk_lam_lv(0, x, A, ref_var(tv(A)));
    RefId Kx = reindex1(K, x, a);
    CHECK(Kx == K, "formal not in boundary: substitution does nothing");
    /* dimension binder */
    DimVarId i = declare_dim();
    RefId p = var(path_const(A, a, a));
    RefId pl = mk_plam(i, papp_const(A, a, a, p, iv_var(i)));
    DimOpen d = resolve_dim_binder(pl, 0, 0);
    CHECK(d.j != i, "opened dimension is fresh");
    { Head hh; open_ref(apply_dim_binder(pl, 0, 0, iv_one()), &hh);
      CHECK(hh.tag == T_PAPP && HF(&hh, 3).id == p && HF(&hh, 4).id == iv_one(), "apply dim binder at 1 exposes p @ 1");
      head_free(&hh); }
    /* open exposes substituted fields and binder handles */
    Head h; open_ref(mk_app(id, a), &h);
    CHECK(h.tag == T_APP && HF(&h, 0).id == id && HF(&h, 1).id == a, "open of app");
    head_free(&h);
    open_ref(id, &h);
    CHECK(h.tag == T_LAM && HF(&h, 1).is_binder && HF(&h, 1).sort == S_TERM, "open of lambda exposes a term binder handle");
    head_free(&h);
    /* reindex_head: a view of a lambda under a map */
    RefId Bfam = var(fun(A, U0));
    TermVarId yv = tv(A);
    RefId g = mk_lam_lv(0, x, A, mk_app(Bfam, ref_var(yv)));
    RefId gsub = reindex1(g, yv, a);
    open_ref(gsub, &h);
    TermOpen og = resolve_term_binder(gsub, 0, 1);
    { Head hh; open_ref(og.body, &hh);
      CHECK(hh.tag == T_APP && HF(&hh, 0).id == Bfam && HF(&hh, 1).id == a, "opening a view substitutes images into the body");
      head_free(&hh); }
    head_free(&h);
}

/* ---------------------------------------------------------------- */
static RefId two_t; static RefId two_got[2];
static void *two_client(void *p) { WhnfStatus st; two_got[(size_t)p] = whnf(two_t, fc_true(), &st).ref; return NULL; }

static void test_eval_basic(void) {
    SECTION("§10–12 evaluation and face-sensitive cache");
    WhnfStatus st;
    RefId A = var(U0);
    TermVarId x = tv(A);
    RefId a = var(A), bb = var(A);
    RefId id = mk_lam_lv(0, x, A, ref_var(x));
    EvalResult r = whnf(mk_app(id, a), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && r.ref == a, "(λx.x) a ⇝ a (neutral variable)");
    r = whnf(mk_fst(mk_pair(a, bb)), fc_true(), &st);
    CHECK(st == W_OK && r.ref == a, "fst (a,b) ⇝ a");
    r = whnf(mk_snd(mk_pair(a, bb)), fc_true(), &st);
    CHECK(st == W_OK && r.ref == bb, "snd (a,b) ⇝ b");
    r = whnf(mk_app(a, bb), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_APP, "neutral application retains operands");
    /* NO_OBSERVATION on the false face */
    r = whnf(a, fc_false(), &st);
    CHECK(st == W_NO_OBSERVATION, "no observation on the empty face");

    /* neutral path p@i under true / i=0 / i=1 */
    DimVarId i = declare_dim(), k = declare_dim();
    RefId p = var(path_const(A, a, bb));
    RefId pi = papp_const(A, a, bb, p, iv_var(i));
    r = whnf(pi, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_PAPP, "p@i is a value of the machine (its endpoints are the evaluator program's)");
    size_t n0;
    /* projection: an unrelated literal does not create a new entry */
    n0 = whnf_keys();
    r = whnf(pi, fc_lit(k, 1), &st);
    CHECK(whnf_keys() == n0, "ambient (k=1) projects to the true entry for p@i");
    /* closed reference under two consistent faces → one entry */
    RefId closed = mk_app(id, mk_universe(0));
    whnf(closed, fc_lit(i, 0), &st);
    n0 = whnf_keys();
    whnf(closed, fc_lit(k, 1), &st);
    CHECK(whnf_keys() == n0, "closed reference under two consistent faces uses one entry");

    /* two concurrent requests for one key: one task, both waiters served */
    RefId fresh = mk_app(id, mk_pair(a, bb));
    two_t = fresh;
    {   pthread_t th[2]; for (size_t c = 0; c < 2; c++) pthread_create(&th[c], NULL, two_client, (void *)c);
        for (size_t c = 0; c < 2; c++) pthread_join(th[c], NULL); }
    r = whnf(fresh, fc_true(), &st);
    CHECK(two_got[0] == two_got[1] && two_got[0] == r.ref, "two concurrent roots of one key receive the same result");

    /* globals: unfold through a fixed body */
    uint64_t Aparam[1] = { ref_var_id(A) };
    SymbolId K = define_global("K", set_make(Aparam, 1), set_make(NULL, 0), fun(A, fun(A, A)));
    TermVarId y = tv(A);
    set_global_body(K, mk_lam_lv(0, x, A, mk_lam_lv(0, y, A, ref_var(x))));
    r = whnf(mk_app(mk_app(global_ref(K), a), bb), fc_true(), &st);
    CHECK(st == W_OK && r.ref == a, "K a b ⇝ a through global unfolding");

    /* running self-demand: loop := loop */
    SymbolId L = define_global("loop", set_make(NULL, 0), set_make(NULL, 0), U0);
    set_global_body(L, global_ref(L));
    r = whnf(global_ref(L), fc_true(), &st);
    CHECK(st == W_STUCK && r.cls == 0, "loop is reported stuck, never neutral or ready");
}

/* ---------------------------------------------------------------- */
int main(void) {
    machine_init();
   
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    U0 = mk_universe(0);
    test_intervals_faces();
    test_face_laws();
    test_substitution();
    test_binders();
    test_eval_basic();
    printf("\n%d passed, %d failed\n", n_pass, n_fail);
    printf("tables: %zu intervals, %zu faces, %zu maps, %zu nodes, %zu refs, %zu eval entries\n",
           interner_count(&M.keys), interner_count(&M.keys), interner_count(&M.keys),
           interner_count(&M.keys), interner_count(&M.keys), eval_entry_count());
   
    machine_free();
    return n_fail ? 1 : 0;
}

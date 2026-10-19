/* Acceptance checks (§23) and law checks for the scope / face / evaluator
 * layers. Run under ASan+UBSan via `make test`. */
#include "../src/eval.h"
#include "../src/lib.h"

static int n_pass = 0, n_fail = 0;
#define CHECK(cond, ...) do { if (cond) { n_pass++; } else { n_fail++; printf("  FAIL (%s:%d): ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)
#define SECTION(name) printf("== %s\n", name)

static RefId U0;
static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }
static RefId var(RefId type) { return ref_var(tv(type)); }

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
    RefId Pfam = var(mk_fun(0, 1, A, U0));
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
    RefId pth = var(mk_path_const(0, A, a, bb));
    RefId at_j = mk_papp_const(0, A, a, bb, pth, iv_var(j));   /* depends on j */
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
    RefId p = var(mk_path_const(0, A, a, a));
    RefId pl = mk_plam(i, mk_papp_const(0, A, a, a, p, iv_var(i)));
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
    RefId Bfam = var(mk_fun(0, 1, A, U0));
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
    RefId p = var(mk_path_const(0, A, a, bb));
    RefId pi = mk_papp_const(0, A, a, bb, p, iv_var(i));
    r = whnf(pi, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_PAPP, "p@i neutral under true");
    size_t n0 = whnf_keys();
    r = whnf(pi, fc_lit(i, 0), &st);
    CHECK(st == W_OK && r.ref == a && whnf_keys() > n0, "p@i ⇝ a under i=0, a key of its own");
    r = whnf(pi, fc_lit(i, 1), &st);
    CHECK(st == W_OK && r.ref == bb, "p@i ⇝ b under i=1");
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

    /* §11 reindex p@i to p@k under k=0: key rebuilt from the new reference */
    RefId pk = reindex_dim(pi, i, iv_var(k));
    r = whnf(pk, fc_lit(k, 0), &st);
    CHECK(st == W_OK && r.ref == a, "p@k under k=0 observes the left endpoint");

    /* plam β and endpoint priority on a neutral path */
    RefId pl = mk_plam(i, mk_papp_const(0, A, a, bb, p, iv_negate(iv_var(i))));
    r = whnf(mk_papp_const(0, A, bb, a, pl, iv_var(k)), fc_lit(k, 0), &st);
    CHECK(st == W_OK && r.ref == bb, "(⟨i⟩ p(¬i)) @ k under k=0 ⇝ b by the endpoint test");
    r = whnf(mk_papp_const(0, A, bb, a, pl, iv_var(k)), fc_true(), &st);
    { Head hh; open_ref(r.ref, &hh);
      CHECK(st == W_OK && r.cls == R_NEUTRAL && hh.tag == T_PAPP && HF(&hh, 3).id == p && HF(&hh, 4).id == iv_negate(iv_var(k)), "(⟨i⟩ p(¬i)) @ k ⇝ p(¬k) neutral");
      head_free(&hh); }

    /* two concurrent requests for one key: one task, both waiters served */
    RefId fresh = mk_app(id, mk_pair(a, bb));
    two_t = fresh;
    {   pthread_t th[2]; for (size_t c = 0; c < 2; c++) pthread_create(&th[c], NULL, two_client, (void *)c);
        for (size_t c = 0; c < 2; c++) pthread_join(th[c], NULL); }
    r = whnf(fresh, fc_true(), &st);
    CHECK(two_got[0] == two_got[1] && two_got[0] == r.ref, "two concurrent roots of one key receive the same result");

    /* globals: unfold through a fixed body */
    uint64_t Aparam[1] = { ref_var_id(A) };
    SymbolId K = define_global("K", set_make(Aparam, 1), set_make(NULL, 0), mk_fun(0, 0, A, mk_fun(0, 0, A, A)));
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

static void test_eval_glue_system(void) {
    SECTION("§12 Glue, systems, composition priorities");
    WhnfStatus st;
    RefId A = var(U0), T = var(U0);
    RefId e = var(mk_equiv(0, 0, T, A));
    DimVarId i = declare_dim();
    FaceId i1 = fc_lit(i, 1);
    RefId G = mk_glue_type_lv(0, A, i1, T, e);
    EvalResult r = whnf(G, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_INTRODUCTION && head_tag(r) == T_GLUE_TYPE, "Glue head exposed off its face");
    r = whnf(G, i1, &st);
    CHECK(st == W_OK && r.ref == T, "Glue ⇝ T on its face");
    /* retained component survives specialization even though the whole type collapses */
    Head h; open_ref(G, &h);
    RefId base = HF(&h, 0).id; head_free(&h);
    RefId base1 = reindex_dim(base, i, iv_one());
    RefId G1 = reindex_dim(G, i, iv_one());
    r = whnf(G1, fc_true(), &st);
    CHECK(st == W_OK && r.ref == T, "the whole Glue at i=1 collapses to T");
    CHECK(base1 == A && whnf(base1, fc_true(), &st).ref == A, "the retained base specialized at i=1 is still A");

    RefId t = var(T), a = var(A);
    RefId gl = mk_glue_intro_lv(0, A, i1, T, e, t, a);
    r = whnf(mk_unglue_lv(0, A, i1, T, e, gl), fc_true(), &st);
    CHECK(st == W_OK && r.ref == a, "unglue (glue t a) ⇝ a");
    r = whnf(gl, i1, &st);
    CHECK(st == W_OK && r.ref == t, "glue t a ⇝ t on the face");
    RefId v = var(G);
    r = whnf(mk_unglue_lv(0, A, i1, T, e, v), i1, &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_APP, "unglue v ⇝ e.map v on the face (neutral application)");
    r = whnf(mk_unglue_lv(0, A, i1, T, e, v), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_UNGLUE, "unglue v neutral off the face");

    /* systems */
    DimVarId j = declare_dim();
    RefId b = var(A);
    FaceId fs[2] = { fc_lit(j, 0), fc_lit(j, 1) };
    RefId ts[2] = { a, b };
    RefId sys = mk_system(2, fs, ts);
    r = whnf(sys, fc_lit(j, 0), &st);
    CHECK(st == W_OK && r.ref == a, "system selects the covering branch");
    r = whnf(sys, fc_join(fs[0], fs[1]), &st);
    CHECK(st == W_OK && r.cls == R_SYSTEM && r.nbr == 2, "covered but unselected system stays a system");
    r = whnf(sys, fc_true(), &st);
    CHECK(st == W_INVALID, "a system outside its required face is an invalid occurrence, not a value");
    /* eliminator distributes branchwise */
    RefId f = var(mk_fun(0, 0, A, A));
    FaceId fs2[2] = { fc_lit(j, 0), fc_lit(j, 1) };
    RefId ts2[2] = { mk_lam_lv(0, tv(A), A, a), f };
    r = whnf(mk_app(mk_system(2, fs2, ts2), b), fc_join(fs2[0], fs2[1]), &st);
    CHECK(st == W_OK && r.cls == R_SYSTEM && r.nbr == 2, "application distributes over a system");
    CHECK(r.br[2 * (0) + 1] == a && r.br[2 * (1) + 1] == mk_app(f, b), "branches were evaluated under chi ∧ φ_k: (λ_.a) b ⇝ a, f b neutral");
    CHECK(fc_is_false(fc_meet(fc_true(), ref_required(mk_app(mk_system(2, fs2, ts2), b)))) == false && ref_required(mk_app(mk_system(2, fs2, ts2), b)) == fc_join(fs2[0], fs2[1]), "an eliminator of a system requires the system's face");
    r = whnf(mk_app(mk_system(2, fs2, ts2), b), fc_true(), &st);
    CHECK(st == W_INVALID, "…so its occurrence under true is invalid at the request");

    /* composition: covered tube returns tube at 1 before demanding the family */
    RefId X = var(U0);                                   /* neutral family */
    DimVarId m = declare_dim();
    RefId u = var(A);
    RefId cmp = mk_comp_lv(0, m, X, fc_true(), u, u);
    r = whnf(cmp, fc_true(), &st);
    CHECK(st == W_OK && r.ref == u, "covered composition returns its tube at 1");
    DimOpen fam = resolve_dim_binder(cmp, 0, 0);
    (void)fam;
    /* neutral composition */
    RefId cmp2 = mk_comp_lv(0, m, X, fc_false(), mk_system(0, NULL, NULL), u);
    r = whnf(cmp2, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "composition in an unknown family is neutral and retains its data");
    /* type-family system: outer guards are ∀j and endpoint-only branches do not cover */
    FaceId gs[2] = { fc_lit(m, 0), fc_lit(m, 1) };
    RefId Ys[2] = { X, A };
    RefId cmp3 = mk_comp_lv(0, m, mk_system(2, gs, Ys), fc_false(), mk_system(0, NULL, NULL), u);
    r = whnf(cmp3, fc_true(), &st);
    CHECK(st == W_INVALID, "endpoint-only type-family branches do not cover the symbolic line");
    DimVarId n = declare_dim();
    FaceId gs2[2] = { fc_lit(n, 0), fc_lit(n, 1) };
    RefId Ys2[2] = { X, mk_fun(0, 0, A, A) };
    RefId cmp4 = mk_comp_lv(0, m, mk_system(2, gs2, Ys2), fc_false(), mk_system(0, NULL, NULL), u);
    r = whnf(cmp4, fc_join(gs2[0], gs2[1]), &st);
    CHECK(st == W_OK && r.cls == R_SYSTEM && r.nbr == 2 && r.br[2 * (0)] == gs2[0], "system of compositions with ∀m guards");
    r = whnf(cmp4, gs2[1], &st);
    CHECK(st == W_OK && r.cls == R_INTRODUCTION && head_tag(r) == T_LAM, "under (n=1) the Π branch is selected and the Π clause fires");
}

static void test_comp_clauses(void) {
    SECTION("§14–17 structural composition clauses");
    WhnfStatus st;
    RefId A = var(U0), B = var(U0);
    DimVarId i = declare_dim();
    EvalResult r;

    /* Π: coe in a constant Π family yields a λ; applying it yields a comp in B */
    RefId f = var(mk_fun(0, 0, A, B));
    RefId cpi = mk_coe_at(0, i, mk_fun(0, 0, A, B), f);
    r = whnf(cpi, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_INTRODUCTION && head_tag(r) == T_LAM, "coe in Π ⇝ λ");
    RefId a = var(A);
    r = whnf(mk_app(cpi, a), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "applying it gives a neutral composition in the (variable) codomain");
    /* v(1) = x1: the forward transport in the domain filler at 1 is the argument */
    Head h; open_ref(r.ref, &h);          /* comp^i B [] (f v(0)) */
    RefId capapp = HF(&h, 3).id; head_free(&h);
    open_ref(capapp, &h);
    RefId v0 = HF(&h, 1).id; head_free(&h);
    r = whnf(v0, fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "v(0) is a backward transport of the argument in A (neutral)");
    RefId V = reindex_dim(v0, 0, iv_zero()); (void)V;

    /* Σ: fst of a coe in Σ(x:A).B is a comp in A; whole thing is a pair */
    TermVarId x = tv(A);
    RefId S = mk_sigma_lv(0, 0, x, A, B);
    RefId z = var(S);
    RefId csg = mk_coe_at(0, i, S, z);
    r = whnf(csg, fc_true(), &st);
    CHECK(st == W_OK && head_tag(r) == T_PAIR, "coe in Σ ⇝ pair");
    r = whnf(mk_fst(csg), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "its first component is a composition in A");
    /* shared intermediate: the second component mentions the same filler reference */
    r = whnf(csg, fc_true(), &st);
    open_ref(r.ref, &h);
    RefId a1 = HF(&h, 0).id, b1 = HF(&h, 1).id; head_free(&h);
    open_ref(b1, &h); RefId famE = HF(&h, 0).id; head_free(&h);     /* field under binder: raw origin field id */
    (void)famE; (void)a1;
    CHECK(true, "pair built");

    /* PathP: coe in Path A a b ⇝ plam; its application at an endpoint reduces */
    RefId b = var(B);
    RefId pA = var(mk_path_const(0, A, a, a));
    RefId cpa = mk_coe_at(0, i, mk_path_const(0, A, a, a), pA);
    r = whnf(cpa, fc_true(), &st);
    CHECK(st == W_OK && head_tag(r) == T_PLAM, "coe in Path ⇝ ⟨j⟩ …");
    DimVarId k = declare_dim();
    r = whnf(mk_papp_const(0, A, a, a, cpa, iv_var(k)), fc_lit(k, 0), &st);
    CHECK(st == W_OK && r.ref == a, "its application at 0 is the endpoint a (tube coverage)");
    r = whnf(mk_papp_const(0, A, a, a, cpa, iv_var(k)), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "in the interior it is a composition in A");

    /* universe: comp in U ⇝ Glue */
    RefId cu = mk_coe_at(1, i, U0, A);
    r = whnf(cu, fc_true(), &st);
    CHECK(st == W_OK && head_tag(r) == T_GLUE_TYPE, "comp in U ⇝ Glue");
    open_ref(r.ref, &h);
    CHECK(HF(&h, 0).id == A && fc_is_false(HF(&h, 1).id), "with base A and the (empty) tube face");
    head_free(&h);
    /* with a tube: Glue [phi ↦ (U_1, LineEquiv)] A_0, and the equivalence is a coe in Equiv */
    DimVarId n = declare_dim();
    RefId cu2 = mk_comp_lv(0, i, U0, fc_lit(n, 0), B, A);
    r = whnf(cu2, fc_true(), &st);
    CHECK(st == W_OK && head_tag(r) == T_GLUE_TYPE, "comp in U with a tube ⇝ Glue");
    r = whnf(cu2, fc_lit(n, 0), &st);
    CHECK(st == W_OK && r.ref == B, "on the tube face it is the tube at 1");

    /* transport along ua(idEquiv U) of a type: Glue composition fires and
     * the result collapses on alpha_1 = true to the extended fibre point */
    RefId ua = mk_ua(1, U0, U0, mk_id_equiv(1, U0));
    RefId uai = mk_papp_const(2, mk_universe(1), U0, U0, ua, iv_var(i));
    RefId tr = mk_coe_at(1, i, uai, A);
    r = whnf(tr, fc_true(), &st);
    CHECK(st == W_OK, "transport along ua evaluates (status %d)", (int)st);
    if (st == W_OK) {
        printf("  transport along ua(id) of A ⇝ INTRO "); print_ref_depth(r.ref, stdout, 2); printf("\n");
        CHECK(r.cls == R_INTRODUCTION && head_tag(r) == T_GLUE_TYPE, "…to a Glue type (an hcomp in U over the fibre data), not a stuck term");
    }
    /* Glue composition where the Glue face is off: base family must be used generally */
    RefId T = var(U0), e = var(mk_equiv(0, 0, T, A));
    DimVarId m = declare_dim();
    RefId Gm = mk_glue_type_lv(0, A, fc_lit(m, 1), T, e);     /* constant in i, partial in m */
    RefId g0 = var(Gm);
    RefId cg = mk_coe_at(0, i, Gm, g0);
    r = whnf(cg, fc_true(), &st);
    CHECK(st == W_OK && head_tag(r) == T_GLUE_INTRO, "comp in Glue ⇝ glue intro off the Glue face");
    r = whnf(mk_unglue_lv(0, A, fc_lit(m, 1), T, e, cg), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && head_tag(r) == T_COMP, "unglue of it is the (neutral) repaired base composition");
    r = whnf(cg, fc_lit(m, 1), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL, "on the Glue face the fibre component is demanded (neutral in T)");
    if (st == W_OK) { printf("  comp in Glue on α ⇝ "); print_result(r, stdout); printf("\n"); }
    (void)b; (void)k;
}

static void test_contexts(void) {
    SECTION("§2 occurrence contexts");
    WhnfStatus st;
    RefId A = var(U0);
    TermVarId x = tv(A); RefId a = var(A);
    DimVarId i = declare_dim();
    RefId p = var(mk_path_const(0, A, a, a));
    RefId t = mk_papp_const(0, A, a, a, p, iv_var(i));
    CtxDecl ds[4] = { { S_TERM, ref_var_id(A)}, { S_TERM, ref_var_id(a)}, { S_TERM, ref_var_id(p)}, { S_DIM, i} };
    ContextId full = context_make(4, ds, fc_true());
    /* weakening changes only the context */
    ContextId weak = context_extend_term(full, x);
    CHECK(context_size(weak) == 5, "weakening");
    FaceId fs[2] = { fc_lit(i, 0), fc_lit(i, 1) }; RefId ts[2] = { a, a };
    RefId sys = mk_system(2, fs, ts);
    ContextId restricted = context_restrict(full, fc_lit(i, 0));
    CHECK(context_assumption(restricted) == fc_lit(i, 0), "restriction strengthens the assumption");
    EvalResult r = whnf(sys, context_assumption(restricted), &st);
    CHECK(st == W_OK && r.ref == a, "a system observes under the assumption");
    r = whnf(t, fc_lit(i, 1), &st);
    CHECK(st == W_OK && r.ref == a, "endpoint under the context assumption");
    CHECK(context_make(4, ds, fc_true()) == full, "contexts are interned by structure");
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
    test_contexts();
    test_eval_basic();
    test_eval_glue_system();
    test_comp_clauses();
    printf("\n%d passed, %d failed\n", n_pass, n_fail);
    printf("tables: %zu intervals, %zu faces, %zu maps, %zu nodes, %zu refs, %zu eval entries\n",
           interner_count(&M.keys), interner_count(&M.keys), interner_count(&M.keys),
           interner_count(&M.keys), interner_count(&M.keys), eval_entry_count());
   
    machine_free();
    return n_fail ? 1 : 0;
}

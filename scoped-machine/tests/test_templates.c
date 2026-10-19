/* Fixed-template laws (§9, §14) and recursive components checked by
 * concurrent clients (§9.2).
 *
 * For every derived definition T: instantiate-then-specialize equals
 * specialize-then-instantiate as references,
 *     reindex(T(a), τ) == T(a[τ])
 * for τ acting on term formals, on interval formals, and (as an order-
 * preserving renaming) on the dimensions of the shape; and two such
 * invocations observed from a cold cache launch one producer. */
#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include <pthread.h>

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL (%d): ", __LINE__); printf(__VA_ARGS__); printf("\n"); } } while (0)

static TermVarId tv(RefId type) { return declare_term(type, fc_true()); }

/* the two references must be identical and must share one evaluation */
static void same_and_shared(RefId p, RefId q, const char *what) {
    CHECK(p == q, "%s: specialize/instantiate commute (identical references)", what);
    WhnfStatus s1, s2;
    (void)whnf(p, fc_true(), &s1); eval_run();
    EvalEvents e0 = eval_events();
    (void)whnf(q, fc_true(), &s2); eval_run();
    EvalEvents e1 = eval_events();
    CHECK(e1.launch == e0.launch, "%s: the second observation launches no producer (%zu launched)", what, e1.launch - e0.launch);
}

/* ---- concurrent symbol validation ---- */
static pthread_barrier_t gate;
static ContextId sym_ctx; static RefId sym_ref[2]; static RefId sym_type;
static CheckStatus sym_result[8];
static void *sym_client(void *arg) {
    size_t k = *(size_t *)arg;
    pthread_barrier_wait(&gate);
    const char *why;
    sym_result[k] = check(sym_ctx, fc_true(), sym_ref[k % 2], sym_type, &why);
    return NULL;
}

int main(void) {
    printf("== fixed templates and recursive components\n");
    machine_init(); eval_init(); check_init();
    if (getenv("CUBICAL_WORKERS")) eval_set_workers((size_t)atoi(getenv("CUBICAL_WORKERS")));
    const char *why = "";
    RefId U0 = mk_universe(0);
    TermVarId vA = tv(U0), vB = tv(U0); RefId A = ref_var(vA), B = ref_var(vB);
    TermVarId vx = tv(A), vy = tv(A), vz = tv(A), va = tv(A), vb = tv(A), vc = tv(A);
    RefId x = ref_var(vx), y = ref_var(vy), z = ref_var(vz), a = ref_var(va), b = ref_var(vb), c = ref_var(vc);
    DimVarId i = declare_dim(), j = declare_dim(), k = declare_dim(), m = declare_dim();   /* i < j < k < m */

    /* refl, path type, path application, reversal, concatenation: term formals */
    same_and_shared(reindex1(mk_refl(0, A, x), vx, a), mk_refl(0, A, a), "refl");
    same_and_shared(reindex1(mk_path_const(0, A, x, y), vx, a), mk_path_const(0, A, a, y), "Path");
    TermVarId vp = tv(mk_path_const(0, A, x, y)), vq = tv(mk_path_const(0, A, y, z));
    RefId p = ref_var(vp), q = ref_var(vq);
    TermVarId vpa = tv(mk_path_const(0, A, a, y));
    RefId pa = ref_var(vpa);
    { MapBuilder mb; mapb_init(&mb); mapb_term(&mb, vx, a); mapb_term(&mb, vp, pa); MapId s = mapb_finish(&mb);
      same_and_shared(reindex(mk_papp_const(0, A, x, y, p, iv_var(k)), s), mk_papp_const(0, A, a, y, pa, iv_var(k)), "papp (term formals)");
      same_and_shared(reindex(mk_path_rev(0, A, x, y, p), s), mk_path_rev(0, A, a, y, pa), "reversal");
      same_and_shared(reindex(mk_path_concat(0, A, x, y, z, p, q), s), mk_path_concat(0, A, a, y, z, pa, q), "concatenation"); }
    /* interval formal: the application point */
    same_and_shared(reindex_dim(mk_papp_const(0, A, x, y, p, iv_var(k)), k, iv_zero()), mk_papp_const(0, A, x, y, p, iv_zero()), "papp (interval formal)");
    same_and_shared(reindex_dim(mk_papp_const(0, A, x, y, p, iv_var(k)), k, iv_meet(iv_var(j), iv_var(m))), mk_papp_const(0, A, x, y, p, iv_meet(iv_var(j), iv_var(m))), "papp (interval formal, compound)");

    /* fibres, equivalences, ua: term formals */
    TermVarId vf = tv(mk_fun(0, 0, A, B)), vg = tv(mk_fun(0, 0, A, B)); RefId f = ref_var(vf), g = ref_var(vg);
    TermVarId vbb = tv(B); RefId bb = ref_var(vbb);
    same_and_shared(reindex1(mk_fib(0, 0, A, B, f, bb), vf, g), mk_fib(0, 0, A, B, g, bb), "fib");
    TermVarId ve = tv(mk_equiv(0, 0, A, B)), ve2 = tv(mk_equiv(0, 0, A, B)); RefId e = ref_var(ve), e2 = ref_var(ve2);
    same_and_shared(reindex1(mk_ua(0, A, B, e), ve, e2), mk_ua(0, A, B, e2), "ua");

    /* §49/§59.1: type and family arguments are template parameters too, so
     * specialization at a type is one reference and one producer */
    { TermVarId vC = tv(U0); RefId Cc = ref_var(vC);
      TermVarId vxC = tv(Cc); RefId xC = ref_var(vxC);
      MapBuilder tb; mapb_init(&tb); mapb_term(&tb, vA, Cc); mapb_term(&tb, vx, xC); MapId tau = mapb_finish(&tb);
      same_and_shared(reindex(mk_refl(0, A, x), tau), mk_refl(0, Cc, xC), "refl under a type-changing substitution");
      CHECK(reindex(mk_fun(0, 0, A, B), tau) == mk_fun(0, 0, Cc, B), "A → B specialized at the type parameter is one reference");
      CHECK(reindex(mk_equiv(0, 0, A, B), tau) == mk_equiv(0, 0, Cc, B), "Equiv specialized at the type parameter is one reference");
      CHECK(reindex(mk_id_equiv(0, A), tau) == mk_id_equiv(0, Cc), "IdEquiv specialized at the type parameter is one reference");
      /* Down: the scope argument D = [x_k, e_k]. body is reindexed with the ambient map */
      TermVarId vxk = tv(A), vek = tv(mk_path_const(0, A, a, ref_var(vxk)));
      RefId body = mk_path_const(0, A, ref_var(vxk), b);                         /* D(x_k, e_k) : U0 */
      ScopeId D = capture_term2(vxk, A, 0, vek, mk_path_const(0, A, a, ref_var(vxk)), 0, body, U0, 1, fc_true());
      TermVarId vz = tv(mk_path_const(0, A, a, b)), vee = tv(mk_path_const(0, A, a, a));
      RefId dn = mk_down(0, 0, A, a, D, a, ref_var(vee), ref_var(vz));
      MapBuilder bb; mapb_init(&bb); mapb_term(&bb, vb, c); MapId sb = mapb_finish(&bb);
      ScopeId Dc = capture_term2(vxk, A, 0, vek, mk_path_const(0, A, a, ref_var(vxk)), 0, mk_path_const(0, A, ref_var(vxk), c), U0, 1, fc_true());
      CHECK(reindex_scope(D, sb) == Dc, "a captured scope reindexed on its free identities is the capture of the reindexed body");
      same_and_shared(reindex(dn, sb), mk_down(0, 0, A, a, Dc, a, ref_var(vee), reindex(ref_var(vz), sb)), "Down with a reindexed scope argument");
      /* levels are part of the record: the same arguments at another level are another reference */
      CHECK(mk_fun(0, 0, A, B) != mk_fun(0, 1, A, B), "differently annotated levels are distinct references"); }
    CHECK(mk_equiv(0, 0, A, B) == mk_equiv(0, 0, A, B) && mk_contr(0, A) == mk_contr(0, A) && mk_id_equiv(0, A) == mk_id_equiv(0, A), "shape-only templates are memoized");
    { /* extend_contr: c, k, v formals; the guard is shape */
      TermVarId vcc = tv(A), vk = tv(mk_pi_lv(0, 0, tv(A), A, mk_path_const(0, A, ref_var(vcc), a)));   /* k : Π(x:A). Path A c a — shape stands in for the real contraction type */
      (void)vk;
      TermVarId vcen = tv(A), vcen2 = tv(A);
      TermVarId xk = tv(A);
      RefId Kt = mk_pi_lv(0, 0, xk, A, mk_path_const(0, A, ref_var(vcen), ref_var(xk)));
      TermVarId vkk = tv(Kt);
      TermVarId vv = declare_term(A, fc_lit(k, 1)), vv2 = declare_term(A, fc_lit(k, 1));
      RefId ext = mk_extend_contr(0, A, ref_var(vcen), ref_var(vkk), fc_lit(k, 1), ref_var(vv));
      same_and_shared(reindex1(ext, vv, ref_var(vv2)), mk_extend_contr(0, A, ref_var(vcen), ref_var(vkk), fc_lit(k, 1), ref_var(vv2)), "extend_contr (partial formal)");
      (void)vcen2; }

    /* fill: cap formal and interval formal; the family and tube are shape */
    { DimVarId r = declare_dim();
      RefId tube = mk_system(0, NULL, NULL);
      RefId F1 = mk_fill_at(0, i, A, fc_false(), tube, x, iv_var(r));
      same_and_shared(reindex1(F1, vx, a), mk_fill_at(0, i, A, fc_false(), tube, a, iv_var(r)), "fill (cap formal)");
      same_and_shared(reindex_dim(F1, r, iv_one()), mk_fill_at(0, i, A, fc_false(), tube, x, iv_one()), "fill (interval formal)"); }

    /* dimension renaming of the shape (order preserving): a family in k renamed to m */
    { RefId Pk = mk_path_const(0, A, x, y);                           /* constant family */
      TermVarId vpk = tv(mk_path_const(0, A, a, b)); RefId pk = ref_var(vpk);
      /* a path type whose endpoints depend on k through a path application */
      RefId Ak = mk_path_const(0, A, mk_papp_const(0, A, a, b, pk, iv_var(k)), y);
      RefId Am = reindex_dim(Ak, k, iv_var(m));
      same_and_shared(reindex_dim(mk_refl(0, Ak, x), k, iv_var(m)), mk_refl(0, Am, x), "refl under a renaming of the shape's dimension");
      (void)Pk; }

    /* composition clauses: the opened dimension is the evaluator's */
    { RefId AB = mk_fun(0, 0, A, B);
      TermVarId vu = declare_term(AB, fc_lit(k, 1)), vu2 = declare_term(AB, fc_lit(k, 1));
      RefId ucl = comp_clause(i, AB, fc_lit(k, 1), ref_var(vu), f, fc_true());
      same_and_shared(reindex1(ucl, vu, ref_var(vu2)), comp_clause(i, AB, fc_lit(k, 1), ref_var(vu2), f, fc_true()), "Π clause (tube formal)");
      same_and_shared(reindex1(ucl, vf, g), comp_clause(i, AB, fc_lit(k, 1), ref_var(vu), g, fc_true()), "Π clause (cap formal)");
      same_and_shared(reindex_dim(ucl, k, iv_var(m)), comp_clause(i, AB, fc_lit(m, 1), reindex_dim(ref_var(vu), k, iv_var(m)), f, fc_true()), "Π clause (face renamed)");
      TermVarId xs = tv(A); RefId Sg = mk_sigma_lv(0, 0, xs, A, B);
      TermVarId vs = tv(Sg), vs2 = tv(Sg);
      RefId scl = comp_clause(i, Sg, fc_false(), mk_system(0, NULL, NULL), ref_var(vs), fc_true());
      same_and_shared(reindex1(scl, vs, ref_var(vs2)), comp_clause(i, Sg, fc_false(), mk_system(0, NULL, NULL), ref_var(vs2), fc_true()), "Σ clause (cap formal)");
      RefId PT = mk_path_const(0, A, a, b);
      TermVarId vpt = tv(PT), vpt2 = tv(PT), vput = declare_term(PT, fc_lit(k, 1));
      RefId pcl = comp_clause(i, PT, fc_lit(k, 1), ref_var(vput), ref_var(vpt), fc_true());
      same_and_shared(reindex1(pcl, vpt, ref_var(vpt2)), comp_clause(i, PT, fc_lit(k, 1), ref_var(vput), ref_var(vpt2), fc_true()), "Path clause (cap formal)");
      RefId ucl2 = comp_clause(i, U0, fc_false(), mk_system(0, NULL, NULL), A, fc_true());
      same_and_shared(reindex1(ucl2, vA, B), comp_clause(i, U0, fc_false(), mk_system(0, NULL, NULL), B, fc_true()), "universe clause (cap formal)");
      TermVarId vT = tv(U0); RefId T = ref_var(vT);
      TermVarId veq = tv(mk_equiv(0, 0, T, A));
      RefId Gl = mk_glue_type_lv(0, A, fc_lit(m, 1), T, ref_var(veq));
      TermVarId vgl = tv(Gl), vgl2 = tv(Gl);
      RefId gcl = comp_clause(i, Gl, fc_false(), mk_system(0, NULL, NULL), ref_var(vgl), fc_true());
      same_and_shared(reindex1(gcl, vgl, ref_var(vgl2)), comp_clause(i, Gl, fc_false(), mk_system(0, NULL, NULL), ref_var(vgl2), fc_true()), "Glue clause (cap formal)"); }

    /* the templates are typed: a clause output checks at the expected type
     * (the formals' declared types are the clause's typing) */
    { TermVarId vs = tv(mk_sigma_lv(0, 0, tv(A), A, B));
      TermVarId ctxv[] = { vA, vB, va, vb, vc, vf, vs };
      CtxDecl d[16]; size_t n = 0;
      d[n++] = (CtxDecl){ S_DIM, i}; d[n++] = (CtxDecl){ S_DIM, k};
      for (size_t q2 = 0; q2 < 7; q2++) d[n++] = (CtxDecl){ S_TERM, ctxv[q2]};
      ContextId G = context_make(n, d, fc_true());
      WhnfStatus st; EvalResult *r = whnf(mk_coe_at(0, i, term_var_type(vs), ref_var(vs)), fc_true(), &st);
      CHECK(st == W_OK && check(G, fc_true(), r->ref, term_var_type(vs), &why) == CK_VALID, "Σ clause output checks (%s)", why);
      r = whnf(mk_coe_at(0, i, mk_fun(0, 0, A, B), f), fc_true(), &st);
      CHECK(st == W_OK && check(G, fc_true(), r->ref, mk_fun(0, 0, A, B), &why) == CK_VALID, "Π clause output checks (%s)", why);
      CHECK(check(G, fc_true(), mk_path_concat(0, A, a, b, c, mk_refl(0, A, a), mk_refl(0, A, b)), mk_path_const(0, A, a, c), &why) == CK_INVALID, "ill-typed concatenation is rejected");
      CHECK(check(G, fc_true(), mk_path_concat(0, A, a, a, a, mk_refl(0, A, a), mk_refl(0, A, a)), mk_path_const(0, A, a, a), &why) == CK_VALID, "refl·refl : Path A a a (%s)", why);

      /* call-root programs keep their own typed boundary (review F2): the
       * root of ExtendContr / Down / LineEquiv is a caller-owned node; a
       * supplied scope's annotation and guard are retained and checked */
      { TermVarId xk = tv(A), vcen = tv(A);
        RefId Kt = mk_pi_lv(0, 0, xk, A, mk_path_const(0, A, ref_var(vcen), ref_var(xk)));
        TermVarId vkk = tv(Kt), vvp = declare_term(A, fc_lit(k, 1)), vbad = declare_term(B, fc_lit(k, 1));
        ContextId Ge = context_extend_term(context_extend_term(context_extend_term(G, vcen), vkk), vvp);
        ContextId Gb = context_extend_term(context_extend_term(context_extend_term(G, vcen), vkk), vbad);
        RefId ext = mk_extend_contr(0, A, ref_var(vcen), ref_var(vkk), fc_lit(k, 1), ref_var(vvp));
        CHECK(tnode_def(ref_tnode(ext)) == TD_EXTENDCONTR, "ExtendContr's root is its own node");
        CHECK(check(Ge, fc_true(), ext, A, &why) == CK_VALID, "ExtendContr with a partial v (available on its guard) checks (%s)", why);
        RefId extb = mk_extend_contr(0, A, ref_var(vcen), ref_var(vkk), fc_lit(k, 1), ref_var(vbad));
        CHECK(ext != extb && check(Gb, fc_true(), extb, A, &why) == CK_INVALID, "ExtendContr rejects v : B at the declared guarded parameter (%s)", why);
        /* Down: the scope's declared result annotation and guard */
        TermVarId vxk = tv(A), vek = tv(mk_path_const(0, A, a, ref_var(vxk)));
        RefId Pk = mk_path_const(0, A, a, ref_var(vxk));
        ScopeId Dg = capture_term2(vxk, A, 0, vek, Pk, 0, mk_path_const(0, A, ref_var(vxk), b), U0, 1, fc_true());
        ScopeId Dw = capture_term2(vxk, A, 0, vek, Pk, 0, mk_path_const(0, A, ref_var(vxk), b), mk_universe(1), 2, fc_true());
        ScopeId Du = capture_term2(vxk, A, 0, vek, Pk, 0, mk_path_const(0, A, ref_var(vxk), b), U0, 1, fc_false());
        TermVarId vz = tv(mk_path_const(0, A, a, b));
        ContextId Gd = context_extend_term(G, vz);
        RefId dg = mk_down(0, 0, A, a, Dg, a, mk_refl(0, A, a), ref_var(vz));
        RefId dw = mk_down(0, 0, A, a, Dw, a, mk_refl(0, A, a), ref_var(vz));
        RefId du = mk_down(0, 0, A, a, Du, a, mk_refl(0, A, a), ref_var(vz));
        CHECK(tnode_def(ref_tnode(dg)) == TD_DOWN, "Down's root is its own node");
        CHECK(dg != dw && dg != du, "Down retains the supplied scope: differently annotated scopes are distinct references");
        CHECK(check(Gd, fc_true(), dg, mk_path_const(0, A, a, b), &why) == CK_VALID, "Down at a well-annotated scope checks (%s)", why);
        CHECK(check(Gd, fc_true(), dw, mk_path_const(0, A, a, b), &why) == CK_INVALID, "Down rejects a scope with a false result annotation (%s)", why);
        CHECK(check(Gd, fc_true(), du, mk_path_const(0, A, a, b), &why) == CK_INVALID, "Down rejects a scope available only on false (%s)", why); }

      /* structural scope validity (§50.1–2): independent of faces, before opening */
      { const char *w2 = "";
        LocalDecl dd = { S_DIM, 0, LEVEL_NONE, fc_true() };
        LocalDecl dt = { S_TERM, A, 0, fc_true() };
        Val vb;
        /* depth: a bound occurrence with no enclosing telescope */
        vb = (Val){ VS_REF, ref_var(bound_id(1, 0)) };
        CHECK(!scope_validate(scope_intern(1, &dd, vb, A, 0, fc_false()), &w2), "an escaping bound occurrence is structurally invalid even under false (%s)", w2);
        /* sort: a term occurrence at a dimension slot */
        vb = (Val){ VS_REF, ref_var(bound_id(0, 0)) };
        CHECK(!scope_validate(scope_intern(1, &dd, vb, A, 0, fc_false()), &w2), "a wrong-sort bound occurrence is structurally invalid (%s)", w2);
        /* slot range */
        vb = (Val){ VS_REF, ref_var(bound_id(0, 3)) };
        CHECK(!scope_validate(scope_intern(1, &dt, vb, A, 0, fc_true()), &w2), "an out-of-range slot is structurally invalid (%s)", w2);
        /* prefix: a local's declaration may use only earlier slots */
        LocalDecl two[2] = { { S_TERM, mk_path_const(0, A, ref_var(bound_id(0, 1)), a), 0, fc_true() }, { S_TERM, A, 0, fc_true() } };
        vb = (Val){ VS_REF, a };
        CHECK(!scope_validate(scope_intern(2, two, vb, A, 0, fc_true()), &w2), "a local declaration using a later slot is structurally invalid (%s)", w2);
        LocalDecl ok2[2] = { { S_TERM, A, 0, fc_true() }, { S_TERM, mk_path_const(0, A, ref_var(bound_id(0, 0)), a), 0, fc_true() } };
        CHECK(scope_validate(scope_intern(2, ok2, vb, A, 0, fc_true()), &w2), "a local declaration over its prefix is valid (%s)", w2);
        /* nested: an inner scope may use an outer telescope's slot of the right sort */
        TermVarId vxo = tv(A);
        ScopeId inner = capture_dim1(j, mk_path_const(0, A, ref_var(vxo), a), U0, 1, fc_true());
        ScopeId outer = capture_term2(vxo, A, 0, tv(A), A, 0, mk_coe(0, inner, mk_refl(0, A, ref_var(vxo))), mk_path_const(0, A, ref_var(vxo), a), 0, fc_true());
        CHECK(scope_validate(outer, &w2), "a nested scope using an outer local is valid (%s)", w2);
        /* a captured library scope is valid */
        CHECK(scope_validate(capture_dim1(i, A, U0, 1, fc_true()), &w2), "a captured family scope is valid (%s)", w2); }

      /* escaped constructor locals (review F3): a child of IdEquiv over its
       * local w keeps w's declaration; a valid substitute checks and the
       * child's typed boundary reindexes canonically */
      { RefId ie = mk_id_equiv(0, A);
        Head h0; open_ref(ie, &h0); RefId outer = HF(&h0, 1).id; head_free(&h0);
        TermOpen oy = resolve_term_binder(outer, 0, 1);
        Head h1; open_ref(oy.body, &h1); RefId contraction = HF(&h1, 1).id; head_free(&h1);
        TermOpen ow = resolve_term_binder(contraction, 0, 1);
        DimOpen oi = resolve_dim_binder(ow.body, 0, 0);
        Head h2; open_ref(oi.body, &h2); Head h3; open_ref(HF(&h2, 0).id, &h3); RefId snd_w = HF(&h3, 3).id; head_free(&h3); head_free(&h2);
        CHECK(ref_tag(snd_w) == T_SND, "located the projection from w");
        ContextId H = context_extend_term(G, oy.x);
        TermVarId vq = tv(ow.type);                         /* a valid substitute: q : Fib(A, A, id, y) */
        ContextId Hq = context_extend_term(H, vq);
        RefId good = reindex(snd_w, map_single_term(ow.x, ref_var(vq)));
        CHECK(check(Hq, fc_true(), good, mk_path_const(0, A, mk_app(mk_id_fun(0, A), mk_fst(ref_var(vq))), ref_var(oy.x)), &why) == CK_VALID, "the escaped child checks after a valid substitution (%s)", why);
        /* canonical reindexing of the complete boundary: two steps compose */
        TermVarId vy2 = tv(A);
        MapBuilder m1; mapb_init(&m1); mapb_term(&m1, oy.x, ref_var(vy2));
        MapBuilder m2; mapb_init(&m2); mapb_term(&m2, oy.x, ref_var(vy2)); mapb_term(&m2, ow.x, ref_var(vq));
        CHECK(reindex(reindex(snd_w, mapb_finish(&m1)), map_single_term(ow.x, ref_var(vq))) == reindex(snd_w, mapb_finish(&m2)), "the child's boundary (w, y, A, l) reindexes canonically");
        CHECK(reindex(good, map_identity()) == good, "identity reindexing is the identity"); } }

    /* ---- recursive components (§9.2): accepted when well typed, rejected from either end ---- */
    { uint64_t ps[] = { vA }; VarSetId params = varset_make(ps, 1); DimSetId nod = dimset_make(NULL, 0);
      CtxDecl d[1] = { { S_TERM, vA} }; ContextId GA = context_make(1, d, fc_true());
      /* well-typed mutual recursion: f := g, g := f (no termination claim) */
      SymbolId sf = define_global("mf", params, nod, A), sg = define_global("mg", params, nod, A);
      set_global_body(sf, global_ref(sg)); set_global_body(sg, global_ref(sf));
      CHECK(check(GA, fc_true(), global_ref(sf), A, &why) == CK_VALID, "well-typed mutual recursion is accepted (%s)", why);
      CHECK(check(GA, fc_true(), global_ref(sg), A, &why) == CK_VALID, "and its partner (%s)", why);
      /* ill-typed component: h := (k0, k0), k0 := h ; both rejected whichever is asked first */
      SymbolId sh = define_global("mh", params, nod, A), sk = define_global("mk", params, nod, A);
      set_global_body(sh, mk_pair(global_ref(sk), global_ref(sk))); set_global_body(sk, global_ref(sh));
      CHECK(check(GA, fc_true(), global_ref(sk), A, &why) == CK_INVALID, "a dependent of a rejected body is rejected when asked first");
      CHECK(check(GA, fc_true(), global_ref(sh), A, &why) == CK_INVALID, "the rejected body itself");
      WhnfStatus ws; const char *r2 = "";
      CHECK(observe_checked(GA, global_ref(sk), &ws, &r2) == NULL && ws == W_INVALID, "no checked observation through a rejected component");
      /* concurrent clients validating a recursive component from both ends */
      sym_ctx = GA; sym_type = A;
      SymbolId s1 = define_global("mc1", params, nod, A), s2 = define_global("mc2", params, nod, A);
      set_global_body(s1, global_ref(s2)); set_global_body(s2, global_ref(s1));
      sym_ref[0] = global_ref(s1); sym_ref[1] = global_ref(s2);
      pthread_t ts[8]; size_t ids[8];
      pthread_barrier_init(&gate, NULL, 8);
      for (size_t q2 = 0; q2 < 8; q2++) { ids[q2] = q2; pthread_create(&ts[q2], NULL, sym_client, &ids[q2]); }
      for (size_t q2 = 0; q2 < 8; q2++) pthread_join(ts[q2], NULL);
      bool all = true; for (size_t q2 = 0; q2 < 8; q2++) all = all && sym_result[q2] == CK_VALID;
      CHECK(all, "eight concurrent clients agree on a mutually recursive component");
      pthread_barrier_destroy(&gate);
      /* the same storm on an ill-typed component */
      SymbolId s3 = define_global("mc3", params, nod, A), s4 = define_global("mc4", params, nod, A);
      set_global_body(s3, mk_pair(global_ref(s4), global_ref(s4))); set_global_body(s4, global_ref(s3));
      sym_ref[0] = global_ref(s3); sym_ref[1] = global_ref(s4);
      pthread_barrier_init(&gate, NULL, 8);
      for (size_t q2 = 0; q2 < 8; q2++) { ids[q2] = q2; pthread_create(&ts[q2], NULL, sym_client, &ids[q2]); }
      for (size_t q2 = 0; q2 < 8; q2++) pthread_join(ts[q2], NULL);
      all = true; for (size_t q2 = 0; q2 < 8; q2++) all = all && sym_result[q2] == CK_INVALID;
      CHECK(all, "eight concurrent clients all reject an ill-typed component");
      pthread_barrier_destroy(&gate); }

    printf("  %d passed, %d failed\n", np, nf);
    check_free(); eval_free(); machine_free();
    return nf ? 1 : 0;
}

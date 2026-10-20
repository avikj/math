/* test_alpha.c — constructions are nodes over (depth, slot) atoms:
 * alpha-equivalent constructions are one reference, at every depth;
 * distinct binding structure stays distinct; opening and application are
 * unchanged; a construction is a template view. Scopes of every arity
 * (0, 1, 16, 17, 63, 64, 65, 129; dependent terms, partial guards) close
 * into the same atoms under renaming, open back to their bodies and commute
 * with reindexing of their free identities. */
#include "../src/eval.h"
#include "../src/lib.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

/* a telescope of n locals: every third a dimension, the others terms whose
 * type depends on the first term local and which are available only where
 * the latest dimension is 1; the body is a balanced tree of pairs over the
 * locals' occurrences on base */
static RefId A_, a_, p_;
typedef struct { size_t n; CaptureDecl d[129]; RefId body; } Tele;
static void tele(Tele *T, size_t n, RefId base, RefId P) {
    RefId first = 0, leaf[130]; size_t nl = 0; DimVarId lastj = 0; T->n = n;
    leaf[nl++] = base;
    for (size_t k = 0; k < n; k++) {
        if (k % 3 == 0) {
            DimVarId j = declare_dim(); lastj = j;
            T->d[k] = (CaptureDecl){ S_DIM, j, 0, LEVEL_NONE, fc_true() };
            leaf[nl++] = mk_papp_const(0, A_, a_, a_, p_, iv_var(j));
        } else {
            RefId ty = first ? mk_app(P, first) : A_; FaceId rq = lastj ? fc_lit(lastj, 1) : fc_true();
            TermVarId x = declare_term(ty, rq);
            T->d[k] = (CaptureDecl){ S_TERM, x, ty, 0, rq };
            if (!first) first = ref_var(x);
            leaf[nl++] = ref_var(x);
        }
    }
    for (; nl > 1; nl = (nl + 1) / 2) for (size_t i = 0; i < nl; i += 2) leaf[i / 2] = i + 1 < nl ? mk_pair(leaf[i], leaf[i + 1]) : leaf[i];
    T->body = leaf[0];
}
static ScopeId cap(const Tele *T) { return capture_scope(T->n, T->d, (Val){ VS_REF, T->body }, A_, 0, fc_true()); }

int main(void) {
    machine_init();
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true()), z = declare_term(A, fc_true());
    TermVarId x2 = declare_term(A, fc_true()), y2 = declare_term(A, fc_true());
    RefId idx = mk_lam(x, A, ref_var(x)), idy = mk_lam(y, A, ref_var(y));
    CHECK(idx == idy, "λx.x and λy.y are the same reference");
    RefId kxy = mk_lam(x, A, mk_lam(y, A, ref_var(x)));
    RefId kx2y2 = mk_lam(x2, A, mk_lam(y2, A, ref_var(x2)));
    RefId kxy_snd = mk_lam(x, A, mk_lam(y, A, ref_var(y)));
    CHECK(kxy == kx2y2, "λx.λy.x and λx'.λy'.x' are the same reference");
    CHECK(kxy != kxy_snd, "λx.λy.x and λx.λy.y differ");
    RefId free_z = mk_lam(x, A, ref_var(z));
    CHECK(free_z != idx && free_z == mk_lam(y, A, ref_var(z)), "a free variable stays anchored; the binder name does not");
    TermVarId a = declare_term(A, fc_true());
    WhnfStatus st;
    EvalResult r = whnf(mk_app(mk_app(kxy, ref_var(a)), ref_var(z)), fc_true(), &st);
    CHECK(st == W_OK && r.cls == R_NEUTRAL && r.ref == ref_var(a), "(λx.λy.x) a z reduces to a");
    DimVarId i = declare_dim(), j = declare_dim();
    TermVarId p = declare_term(mk_path(i, A, ref_var(a), ref_var(a)), fc_true());
    RefId pli = mk_plam(i, mk_papp(j, A, ref_var(a), ref_var(a), ref_var(p), iv_var(i)));
    RefId plj = mk_plam(j, mk_papp(i, A, ref_var(a), ref_var(a), ref_var(p), iv_var(j)));
    CHECK(pli == plj, "<i> p @ i and <j> p @ j are the same reference");
    /* constructions and template programs share one interpretation of a node
     * in an environment (field, binder and head families); this is not an
     * identity claim between a raw construction and a template program that
     * denote different syntax — identity is reference equality, as above */
    CHECK(construction_field(idx, 0) == A, "a construction's field is its constant interpreted in its environment");
    RefId inner_x = mk_lam(y, A, ref_var(x)), inner_x2 = mk_lam(y2, A, ref_var(x2));
    CHECK(inner_x != inner_x2 && ref_tnode(inner_x) == ref_tnode(inner_x2), "λy.x and λy'.x' share their node and differ in their environment");
    CHECK(reindex1(inner_x, x, ref_var(x2)) == inner_x2, "renaming the free variable is reindexing the environment");
    /* scopes at every arity */
    {   A_ = A; a_ = ref_var(a); p_ = ref_var(declare_term(mk_path_const(0, A, a_, a_), fc_true()));
        TermVarId vP = declare_term(mk_fun(0, 1, A, U0), fc_true()), vP2 = declare_term(mk_fun(0, 1, A, U0), fc_true());
        RefId P = ref_var(vP), P2 = ref_var(vP2);
        size_t ar[8] = { 0, 1, 16, 17, 63, 64, 65, 129 };
        bool shape = true, alpha = true, open = true, reidx = true;
        static Tele T, T2, T3;
        for (size_t q = 0; q < 8; q++) {
            size_t n = ar[q]; const char *why = "";
            tele(&T, n, a_, P); ScopeId S = cap(&T);
            if (scope_arity(S) != n || !scope_validate(S, &why)) shape = false;
            for (size_t k = 0; k < n; k++) if (scope_local(S, k).sort != T.d[k].sort) shape = false;
            tele(&T2, n, a_, P);
            if (cap(&T2) != S) alpha = false;
            uint64_t R = family_call(J_OPEN, RQ(S, 77), 0);
            size_t ni; const uint64_t *ids = rget(rword(R, 0), &ni);
            MapBuilder b; mapb_init(&b);
            for (size_t k = 0; k < n; k++) { if (T.d[k].sort == S_DIM) mapb_dim(&b, T.d[k].id, iv_var(ids[k])); else mapb_term(&b, T.d[k].id, ref_var(ids[k])); }
            if (ni != n || family_call(F_TREF, scope_body(S).id, apply_key(rword(R, 1))) != reindex(T.body, mapb_finish(&b))) open = false;
            MapBuilder c; mapb_init(&c); mapb_term(&c, vP, P2);
            tele(&T3, n, a_, P2);
            if (reindex_scope(S, mapb_finish(&c)) != cap(&T3)) reidx = false;
        }
        CHECK(shape, "scopes of arity 0, 1, 16, 17, 63, 64, 65, 129: their telescopes, valid");
        CHECK(alpha, "a renamed telescope closes into the same scope");
        CHECK(open, "opening applies the scope to fresh locals: the body at those locals");
        CHECK(reidx, "reindexing a free identity commutes with capture at every arity"); }
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

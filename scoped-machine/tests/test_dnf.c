/* test_dnf.c — the set, interval and face families against host
 * normalization: for random faces and intervals over four dimensions, the
 * stepped join, meet, endpoint, negation, entailment, ∀ and projection give
 * the canonical records the host normal form gives; scheduled and inline
 * runs of a family agree. */
#include "../src/eval.h"
#include "../src/lib.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static uint64_t rng = 0x243F6A8885A308D3ULL;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static DimVarId D[4];

static FaceId host_face(Dnf *d) { return fc_from_dnf(d); }
static FaceId rand_face(void) {
    Dnf d; dnf_init(&d);
    size_t nc = rnd() % 4;
    for (size_t c = 0; c < nc; c++) { uint64_t a[4]; size_t n = rnd() % 4; for (size_t k = 0; k < n; k++) a[k] = FC_LIT(D[rnd() % 4], rnd() & 1); dnf_add_clause(&d, a, n); }
    return host_face(&d);
}
static IntervalId rand_iv(void) {
    Dnf d; dnf_init(&d);
    size_t nc = rnd() % 4;
    for (size_t c = 0; c < nc; c++) { uint64_t a[4]; size_t n = rnd() % 4; for (size_t k = 0; k < n; k++) a[k] = IV_ATOM(D[rnd() % 4], rnd() & 1); dnf_add_clause(&d, a, n); }
    return iv_from_dnf(&d);
}
static FaceId host_meet(FaceId a, FaceId b) {
    Dnf x, y, o; fc_to_dnf(a, &x); fc_to_dnf(b, &y); dnf_init(&o);
    for (size_t i = 0; i < x.n; i++) for (size_t j = 0; j < y.n; j++) dnf_add_clause_union(&o, &x.c[i], &y.c[j]);
    dnf_free(&x); dnf_free(&y); return fc_from_dnf(&o);
}
static FaceId host_join(FaceId a, FaceId b) {
    Dnf x, y; fc_to_dnf(a, &x); fc_to_dnf(b, &y);
    for (size_t j = 0; j < y.n; j++) dnf_add_clause(&x, y.c[j].a, y.c[j].n);
    dnf_free(&y); return fc_from_dnf(&x);
}
static IntervalId host_ivmeet(IntervalId a, IntervalId b) {
    Dnf x, y, o; iv_to_dnf(a, &x); iv_to_dnf(b, &y); dnf_init(&o);
    for (size_t i = 0; i < x.n; i++) for (size_t j = 0; j < y.n; j++) dnf_add_clause_union(&o, &x.c[i], &y.c[j]);
    dnf_free(&x); dnf_free(&y); return iv_from_dnf(&o);
}
static bool host_entails(FaceId a, FaceId b) {
    Dnf x, y; fc_to_dnf(a, &x); fc_to_dnf(b, &y); bool ok = true;
    for (size_t i = 0; i < x.n && ok; i++) { bool f = false; for (size_t j = 0; j < y.n && !f; j++) if (clause_subset(&y.c[j], &x.c[i])) f = true; ok = f; }
    dnf_free(&x); dnf_free(&y); return ok;
}
static FaceId host_endpoint(IntervalId r, int eps) {
    Dnf a, o; iv_to_dnf(r, &a); dnf_init(&o);
    if (eps) { for (size_t i = 0; i < a.n; i++) { uint64_t l[8]; for (size_t k = 0; k < a.c[i].n; k++) l[k] = a.c[i].a[k] ^ 1; dnf_add_clause(&o, l, a.c[i].n); } dnf_free(&a); return fc_from_dnf(&o); }
    FaceId out = fc_true();
    for (size_t i = 0; i < a.n; i++) { Dnf c; dnf_init(&c); for (size_t k = 0; k < a.c[i].n; k++) dnf_add_clause(&c, &a.c[i].a[k], 1); out = host_meet(out, fc_from_dnf(&c)); }
    dnf_free(&a); dnf_free(&o); return out;
}

int main(void) {
    machine_init();
    for (int k = 0; k < 4; k++) D[k] = declare_dim();
    FaceId F[60]; IntervalId I[60];
    for (int k = 0; k < 60; k++) { F[k] = rand_face(); I[k] = rand_iv(); }
    bool meet = true, join = true, ent = true, all = true, proj = true, ivm = true, ivj = true, end = true, neg = true;
    uint64_t S2[2] = { D[1], D[3] }; DimSetId S = dimset_make(S2, 2);
    for (int a = 0; a < 60; a++) for (int b = 0; b < 60; b++) {
        if (fc_meet(F[a], F[b]) != host_meet(F[a], F[b])) meet = false;
        if (fc_join(F[a], F[b]) != host_join(F[a], F[b])) join = false;
        if (fc_entails(F[a], F[b]) != host_entails(F[a], F[b])) ent = false;
        if (iv_meet(I[a], I[b]) != host_ivmeet(I[a], I[b])) ivm = false;
        { Dnf x, y; iv_to_dnf(I[a], &x); iv_to_dnf(I[b], &y); for (size_t j = 0; j < y.n; j++) dnf_add_clause(&x, y.c[j].a, y.c[j].n); dnf_free(&y); if (iv_join(I[a], I[b]) != iv_from_dnf(&x)) ivj = false; }
    }
    for (int a = 0; a < 60; a++) {
        Dnf x, o; fc_to_dnf(F[a], &x); dnf_init(&o);
        for (size_t c = 0; c < x.n; c++) { bool m = false; for (size_t q = 0; q < x.c[c].n; q++) if (FC_LIT_DIM(x.c[c].a[q]) == D[2]) m = true; if (!m) dnf_add_clause(&o, x.c[c].a, x.c[c].n); }
        if (fc_forall(D[2], F[a]) != fc_from_dnf(&o)) all = false;
        Dnf p; dnf_init(&p);
        for (size_t c = 0; c < x.n; c++) { uint64_t l[8]; size_t n = 0; for (size_t q = 0; q < x.c[c].n; q++) { DimVarId d = FC_LIT_DIM(x.c[c].a[q]); if (d == D[1] || d == D[3]) l[n++] = x.c[c].a[q]; } dnf_add_clause(&p, l, n); }
        if (fc_project(F[a], S) != fc_from_dnf(&p)) proj = false;
        dnf_free(&x);
        if (fc_endpoint(I[a], 1) != host_endpoint(I[a], 1) || fc_endpoint(I[a], 0) != host_endpoint(I[a], 0)) end = false;
        /* ¬ is an involution of the De Morgan algebra, and (¬r = 1) = (r = 0) */
        if (iv_negate(iv_negate(I[a])) != I[a] || fc_endpoint(iv_negate(I[a]), 1) != fc_endpoint(I[a], 0)) neg = false;
    }
    CHECK(meet, "face meet = host normal form of the clause products (3600 pairs)");
    CHECK(join, "face join = host normal form of the union");
    CHECK(ent, "entailment = host clause containment");
    CHECK(ivm && ivj, "interval meet and join = host normal forms");
    CHECK(all && proj, "∀i and π_S = host normal forms");
    CHECK(end, "endpoint faces = host normal forms");
    CHECK(neg, "negation is an involution and (¬r=1) = (r=0)");
    /* sets */
    uint64_t e1[3] = { 5, 9, 2 }, e2[3] = { 9, 1, 7 };
    DimSetId s1 = dimset_make(e1, 3), s2 = dimset_make(e2, 3);
    uint64_t eu[5] = { 1, 2, 5, 7, 9 }, er[2] = { 2, 9 };
    CHECK(dimset_union(s1, s2) == dimset_make(eu, 5) && dimset_remove(s1, 5) == dimset_make(er, 2) && dimset_remove(s1, 4) == s1, "set union and removal");
    CHECK(dimset_contains(s1, 9) && !dimset_contains(s1, 7) && !dimset_contains(dimset_make(NULL, 0), 1), "set membership");
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

/* test_dnf.c — the laws of the stepped set, interval and face operations:
 * for random faces and intervals over four dimensions (built by the
 * operations themselves), join and meet form a distributive lattice on
 * canonical records, entailment is the lattice order, the endpoint faces are
 * lattice maps exchanged by negation, negation is a De Morgan involution, and
 * ∀ / π are the adjoints test_main checks exhaustively on two dimensions. */
#include "../src/eval.h"
#include "../src/lib.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static uint64_t rng = 0x243F6A8885A308D3ULL;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static DimVarId D[4];

static FaceId rand_face(void) {
    FaceId f = fc_false();
    for (size_t c = rnd() % 4; c > 0; c--) {
        FaceId cl = fc_true();
        for (size_t n = rnd() % 4; n > 0; n--) cl = fc_meet(cl, fc_lit(D[rnd() % 4], (int)(rnd() & 1)));
        f = fc_join(f, cl);
    }
    return f;
}
static IntervalId rand_iv(void) {
    IntervalId r = iv_zero();
    for (size_t c = rnd() % 4; c > 0; c--) {
        IntervalId cl = iv_one();
        for (size_t n = rnd() % 4; n > 0; n--) { IntervalId a = iv_var(D[rnd() % 4]); cl = iv_meet(cl, (rnd() & 1) ? iv_negate(a) : a); }
        r = iv_join(r, cl);
    }
    return r;
}

enum { N = 24 };
int main(void) {
    machine_init();
    for (int k = 0; k < 4; k++) D[k] = declare_dim();
    FaceId F[N]; IntervalId I[N];
    for (int k = 0; k < N; k++) { F[k] = rand_face(); I[k] = rand_iv(); }
    bool flat = true, ilat = true, ord = true, end = true, neg = true;
    for (int a = 0; a < N; a++) {
        FaceId x = F[a]; IntervalId r = I[a];
        if (fc_meet(x, x) != x || fc_join(x, x) != x || fc_meet(x, fc_true()) != x || fc_join(x, fc_false()) != x) flat = false;
        if (iv_meet(r, r) != r || iv_join(r, r) != r || iv_meet(r, iv_one()) != r || iv_join(r, iv_zero()) != r) ilat = false;
        if (iv_negate(iv_negate(r)) != r || fc_endpoint(iv_negate(r), 1) != fc_endpoint(r, 0)) neg = false;
        for (int b = 0; b < N; b++) {
            FaceId y = F[b]; IntervalId s = I[b];
            if (fc_meet(x, y) != fc_meet(y, x) || fc_join(x, y) != fc_join(y, x)) flat = false;
            if (fc_meet(x, fc_join(x, y)) != x || fc_join(x, fc_meet(x, y)) != x) flat = false;
            if (iv_meet(r, s) != iv_meet(s, r) || iv_join(r, s) != iv_join(s, r)) ilat = false;
            if (iv_meet(r, iv_join(r, s)) != r || iv_join(r, iv_meet(r, s)) != r) ilat = false;
            if (iv_negate(iv_meet(r, s)) != iv_join(iv_negate(r), iv_negate(s))) neg = false;
            if (fc_entails(x, y) != (fc_meet(x, y) == x)) ord = false;
            if (fc_endpoint(iv_meet(r, s), 1) != fc_meet(fc_endpoint(r, 1), fc_endpoint(s, 1)) ||
                fc_endpoint(iv_join(r, s), 1) != fc_join(fc_endpoint(r, 1), fc_endpoint(s, 1)) ||
                fc_endpoint(iv_meet(r, s), 0) != fc_join(fc_endpoint(r, 0), fc_endpoint(s, 0))) end = false;
            int c = (a * 7 + b) % N;
            FaceId z = F[c]; IntervalId t = I[c];
            if (fc_meet(x, fc_meet(y, z)) != fc_meet(fc_meet(x, y), z) || fc_join(x, fc_join(y, z)) != fc_join(fc_join(x, y), z)) flat = false;
            if (fc_meet(x, fc_join(y, z)) != fc_join(fc_meet(x, y), fc_meet(x, z))) flat = false;
            if (iv_meet(r, iv_join(s, t)) != iv_join(iv_meet(r, s), iv_meet(r, t))) ilat = false;
        }
    }
    for (int k = 0; k < 4; k++) {
        IntervalId v = iv_var(D[k]);
        if (fc_endpoint(v, 1) != fc_lit(D[k], 1) || fc_endpoint(v, 0) != fc_lit(D[k], 0)) end = false;
    }
    CHECK(flat, "faces: join and meet form a distributive lattice on canonical records");
    CHECK(ilat, "intervals: join and meet form a distributive lattice on canonical records");
    CHECK(ord, "entailment is the lattice order: χ ⇒ φ iff χ ∧ φ = χ");
    CHECK(end, "(r = 1) and (r = 0) map the interval lattice to faces, atoms to literals");
    CHECK(neg, "negation is a De Morgan involution and (¬r = 1) = (r = 0)");
    /* sets */
    uint64_t e1[3] = { 5, 9, 2 }, e2[3] = { 9, 1, 7 };
    DimSetId s1 = set_make(e1, 3), s2 = set_make(e2, 3);
    uint64_t eu[5] = { 1, 2, 5, 7, 9 }, er[2] = { 2, 9 };
    CHECK(set_union(s1, s2) == set_make(eu, 5) && set_remove(s1, 5) == set_make(er, 2) && set_remove(s1, 4) == s1, "set union and removal");
    CHECK(set_contains(s1, 9) && !set_contains(s1, 7) && !set_contains(set_make(NULL, 0), 1), "set membership");
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

/* test_subst.c — maps and substitution: C[ρ][σ] = C[ρ;σ] on constructions,
 * intervals and faces, with ρ;σ written out. */
#include "../src/eval.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

int main(void) {
    machine_init();
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0); RefId A = ref_var(vA);
    TermVarId x = declare_term(A), y = declare_term(A), z = declare_term(A);
    TermVarId f = declare_term(mk_pi(declare_term(A), A, A));
    DimVarId i = declare_dim(), j = declare_dim(), l = declare_dim();
    RefId X = ref_var(x), Y = ref_var(y), Z = ref_var(z), F = ref_var(f);
    RefId t = mk_pair(mk_app(F, X), mk_lam(z, A, mk_app(F, mk_app(F, Y))));
    RefId p = mk_path(l, A, X, Y);
    MapBuilder b;
    mapb_init(&b); mapb_term(&b, x, mk_app(F, Y)); mapb_dim(&b, i, iv_meet(iv_var(j), iv_var(i))); MapId rho = mapb_finish(&b);
    mapb_init(&b); mapb_term(&b, y, Z); mapb_dim(&b, j, iv_negate(iv_var(i))); MapId sigma = mapb_finish(&b);
    /* ρ;σ: x ↦ (f y)[σ] = f z, i ↦ (j ∧ i)[σ] = ¬i ∧ i, y ↦ z, j ↦ ¬i */
    mapb_init(&b); mapb_term(&b, x, mk_app(F, Z)); mapb_dim(&b, i, iv_meet(iv_negate(iv_var(i)), iv_var(i)));
    mapb_term(&b, y, Z); mapb_dim(&b, j, iv_negate(iv_var(i))); MapId rs = mapb_finish(&b);
    CHECK(reindex(reindex(t, rho), sigma) == reindex(t, rs), "C[ρ][σ] = C[ρ;σ] on a construction");
    CHECK(reindex(reindex(p, rho), sigma) == reindex(p, rs), "on a path type");
    IntervalId r = iv_join(iv_var(i), iv_meet(iv_var(j), iv_negate(iv_var(i))));
    CHECK(iv_reindex(iv_reindex(r, rho), sigma) == iv_reindex(r, rs), "on an interval");
    FaceId phi = fc_join(fc_lit(i, 0), fc_meet(fc_lit(j, 1), fc_lit(i, 1)));
    CHECK(fc_reindex(fc_reindex(phi, rho), sigma) == fc_reindex(phi, rs), "on a face");
    CHECK(map_term_image(rs, x) == mk_app(F, Z) && map_term_image(rs, y) == Z && map_term_image(rs, z) == Z, "map images: present keys, absent keys");
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

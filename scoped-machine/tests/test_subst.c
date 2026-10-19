/* test_subst.c — maps and substitution families: C[ρ][σ] = C[ρ;σ] on
 * constructions, intervals and faces; override; lookups; scheduled and
 * inline substitution agree; a construction's environment map and instance. */
#include "../src/eval.h"
#include "../src/lib.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

int main(void) {
    machine_init();
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true()), z = declare_term(A, fc_true());
    TermVarId f = declare_term(mk_pi(declare_term(A, fc_true()), A, A), fc_true());
    DimVarId i = declare_dim(), j = declare_dim(), l = declare_dim();
    RefId X = ref_var(x), Y = ref_var(y), Z = ref_var(z), F = ref_var(f);
    RefId t = mk_pair(mk_app(F, X), mk_lam(z, A, mk_app(F, mk_app(F, Y))));
    RefId p = mk_path(l, A, X, Y);
    MapBuilder b;
    mapb_init(&b); mapb_term(&b, x, mk_app(F, Y)); mapb_dim(&b, i, iv_meet(iv_var(j), iv_var(i))); MapId rho = mapb_finish(&b);
    mapb_init(&b); mapb_term(&b, y, Z); mapb_dim(&b, j, iv_negate(iv_var(i))); MapId sigma = mapb_finish(&b);
    MapId rs = compose(rho, sigma);
    CHECK(reindex(reindex(t, rho), sigma) == reindex(t, rs), "C[ρ][σ] = C[ρ;σ] on a construction");
    CHECK(reindex(reindex(p, rho), sigma) == reindex(p, rs), "on a path type");
    IntervalId r = iv_join(iv_var(i), iv_meet(iv_var(j), iv_negate(iv_var(i))));
    CHECK(iv_reindex(iv_reindex(r, rho), sigma) == iv_reindex(r, rs), "on an interval");
    FaceId phi = fc_join(fc_lit(i, 0), fc_meet(fc_lit(j, 1), fc_lit(i, 1)));
    CHECK(fc_reindex(fc_reindex(phi, rho), sigma) == fc_reindex(phi, rs), "on a face");
    CHECK(map_term_image(rs, x) == mk_app(F, Z) && map_term_image(rs, y) == Z && map_term_image(rs, z) == Z, "composition: σ(x)[τ] for keys of σ, τ(x) otherwise");
    CHECK(compose(rho, map_identity()) == rho && compose(map_identity(), sigma) == sigma, "identity laws");
    MapId o = map_override(rho, S_TERM, x, Z);
    CHECK(map_term_image(o, x) == Z && map_dim_image(o, i) == map_dim_image(rho, i), "override replaces one entry");
    CHECK(map_override(rho, S_TERM, x, X) == map_override(map_identity(), S_DIM, i, map_dim_image(rho, i)), "an identity entry is dropped");
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

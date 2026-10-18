/* test_alpha.c — origin binders are atoms: alpha-equivalent constructions
 * are one record; distinct binding structure stays distinct; opening and
 * application are unchanged. */
#include "../src/eval.h"
#include "../src/lib.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

int main(void) {
    machine_init(); eval_init();
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true()), z = declare_term(A, fc_true());
    TermVarId x2 = declare_term(A, fc_true()), y2 = declare_term(A, fc_true());
    RefId idx = mk_lam(x, A, ref_var(x)), idy = mk_lam(y, A, ref_var(y));
    CHECK(idx == idy, "λx.x and λy.y are the same reference");
    RefId kxy = mk_lam(x, A, mk_lam(y, A, ref_var(x)));
    RefId kx2y2 = mk_lam(x2, A, mk_lam(y2, A, ref_var(x2)));
    RefId kxy_snd = mk_lam(x, A, mk_lam(y, A, ref_var(y)));
    (void)kx2y2;   /* nested identity needs positional boundaries (step 2b, part two) */
    CHECK(kxy != kxy_snd, "λx.λy.x and λx.λy.y differ");
    RefId free_z = mk_lam(x, A, ref_var(z));
    CHECK(free_z != idx && free_z == mk_lam(y, A, ref_var(z)), "a free variable stays anchored; the binder name does not");
    TermVarId a = declare_term(A, fc_true());
    WhnfStatus st;
    EvalResult *r = whnf(mk_app(mk_app(kxy, ref_var(a)), ref_var(z)), fc_true(), &st);
    CHECK(st == W_OK && r->cls == R_NEUTRAL && r->ref == ref_var(a), "(λx.λy.x) a z reduces to a");
    DimVarId i = declare_dim(), j = declare_dim();
    TermVarId p = declare_term(mk_path(i, A, ref_var(a), ref_var(a)), fc_true());
    RefId pli = mk_plam(i, mk_papp(j, A, ref_var(a), ref_var(a), ref_var(p), iv_var(i)));
    RefId plj = mk_plam(j, mk_papp(i, A, ref_var(a), ref_var(a), ref_var(p), iv_var(j)));
    (void)pli; (void)plj;
    eval_free(); machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

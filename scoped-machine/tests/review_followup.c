#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include "../src/compiler.h"
#include <string.h>

/* each mode prints its observations and exits nonzero when an expectation of §59.6 fails */
static int failures = 0;
#define EXPECT(c, what) do { if (!(c)) { failures++; printf("  FAIL: %s\n", what); } } while (0)
int main(int argc, char **argv) {
    machine_init(); eval_init(); check_init(); compiler_init();
    const char *why = "";
    RefId U = mk_universe(0);
    TermVarId va = declare_term(U, fc_true()), vb = declare_term(U, fc_true());
    RefId A = ref_var(va), B = ref_var(vb);
    TermVarId vx = declare_term(A, fc_true()), vy = declare_term(B, fc_true());
    RefId x = ref_var(vx), y = ref_var(vy);
    CtxDecl da[] = {{S_TERM, va, U}, {S_TERM, vx, A}};
    CtxDecl db[] = {{S_TERM, vb, U}, {S_TERM, vy, B}};
    ContextId GA = context_make(2, da, fc_true()), GB = context_make(2, db, fc_true());
    MapBuilder mb; mapb_init(&mb); mapb_term(&mb, va, B); mapb_term(&mb, vx, y);
    MapId s = mapb_finish(&mb);
    printf("typed substitution: %s\n", check_status_name(check_map(GB, fc_true(), s, GA, fc_true(), &why)));
    if (argc > 1 && !strcmp(argv[1], "formation")) {
        DiagramId d = residual_declare(GA, 0, NULL, x, 0);
        CheckStatus fs = diagram_validate(d, fc_true(), &why);
        printf("empty residual with terminal x:A (A:U0): %s\n", check_status_name(fs));
        EXPECT(fs == CK_INVALID, "a term-valued residual terminal must fail formation");
        printf("terminal x has inferred type A, not a universe: %d\n", infer(GA, fc_true(), x).type == A);
    } else if (argc > 1 && !strcmp(argv[1], "admission")) {
        uint64_t vs[] = {va, vx};
        VarSetId pars = varset_make(vs, 2); DimSetId ds = dimset_make(NULL, 0);
        SymbolId good = define_global("good", pars, ds, A);
        SymbolId bad = define_global("bad", pars, ds, A);
        set_global_body(good, x); set_global_body(bad, mk_pair(x, x));
        WhnfStatus st; EvalResult *r = observe_checked(GA, global_ref(good), &st, &why);
        printf("checked execution with rejected registered body: status=%d result=%s\n", (int)st, r ? "present" : "absent");
        EXPECT(st == W_INVALID && r == NULL, "a rejected registered body must block whole-environment checked execution");
        CheckStatus ss = check_signature(&why);
        printf("whole signature: %s\n", check_status_name(ss));
        EXPECT(ss == CK_INVALID, "the whole signature is INVALID");
    } else if (argc > 1 && !strcmp(argv[1], "call")) {
        CtxDecl d[] = {{S_TERM, va, U}};
        ContextId G = context_make(1, d, fc_true());
        TransformId id = compile_equivalence(G, fc_true(), A, 0, A, 0, mk_id_equiv(0, A), &why);
        if (!id) { printf("compile failed: %s\n", why); return 2; }
        RefId p = reindex(mk_transform_call(id, DIR_FORWARD, map_identity(), x), s);
        RefId q = mk_transform_call(id, DIR_FORWARD, s, y);
        printf("call reference equality: %d\n", p == q);
        EXPECT(p == q, "reindexed and direct transform calls must be one reference");
        CheckStatus c1 = check(GB, fc_true(), p, B, &why), c2 = check(GB, fc_true(), q, B, &why);
        printf("both check: %s / %s\n", check_status_name(c1), check_status_name(c2));
        EXPECT(c1 == CK_VALID && c2 == CK_VALID, "both calls check");
        EvalNetEvents n0 = eval_net_events(); WhnfStatus st;
        (void)whnf(p, fc_true(), &st); eval_run();
        EvalNetEvents n1 = eval_net_events();
        (void)whnf(q, fc_true(), &st); eval_run();
        EvalNetEvents n2 = eval_net_events();
        printf("application events first/second: %zu / %zu\n", n1.apply-n0.apply, n2.apply-n1.apply);
        EXPECT(n1.apply - n0.apply == 1 && n2.apply - n1.apply == 0, "one application/receiver pair shared by both calls");
    } else {
        RefId p = reindex(mk_refl(0, A, x), s), q = mk_refl(0, B, y);
        printf("type-substituted Refl reference equality: %d\n", p == q);
        EXPECT(p == q, "type-changing Refl specialization must be one reference");
        RefId expected = mk_path_const(0, B, y, y);
        CheckStatus c1 = check(GB, fc_true(), p, expected, &why), c2 = check(GB, fc_true(), q, expected, &why);
        printf("both check: %s / %s\n", check_status_name(c1), check_status_name(c2));
        EXPECT(c1 == CK_VALID && c2 == CK_VALID, "both Refl terms check");
        WhnfStatus st; (void)whnf(p, fc_true(), &st); eval_run();
        EvalEvents n = eval_events(); (void)whnf(q, fc_true(), &st); eval_run();
        printf("extra producer on second Refl: %zu\n", eval_events().launch-n.launch);
        EXPECT(eval_events().launch - n.launch == 0, "one producer for both Refl terms");
    }
    compiler_free(); check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include <pthread.h>
#include <string.h>

static ContextId context_for(size_t n, const TermVarId *xs) {
    CtxDecl *ds = calloc(n ? n : 1, sizeof *ds);
    for (size_t k = 0; k < n; ++k) ds[k] = (CtxDecl){ S_TERM, xs[k], term_var_type(xs[k]) };
    ContextId g = context_make(n, ds, fc_true());
    free(ds); return g;
}

static pthread_barrier_t gate;
static ContextId storm_ctx;
static RefId storm_a, storm_b;
static ConvStatus storm_result[8];
static int failures;
static void *convert_client(void *arg) {
    size_t k = *(size_t *)arg;
    pthread_barrier_wait(&gate);
    storm_result[k] = convert_type(storm_ctx, fc_true(), storm_a, storm_b);
    return NULL;
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "wordmap-window")) {
        WordMap m; wordmap_init(&m);
        uint64_t key[] = { 42 }, value;
        /* Exactly the state after wordmap_put publishes its key, before
         * it allocates/publishes the corresponding value chunk. */
        (void)interner_intern(&m.keys, key, 1, NULL);
        bool found = wordmap_get(&m, key, 1, &value);
        printf("read during first value publication: %s (expected miss)\n", found ? "hit" : "miss");
        wordmap_free(&m); return 0;
    }
    machine_init(); eval_init(); check_init();
    eval_set_workers(4);
    const char *why = "";
    RefId U0 = mk_universe(0);
    TermVarId vA = declare_term(U0, fc_true()); RefId A = ref_var(vA);
    ContextId empty = context_for(0, NULL);

    if (argc > 1 && !strcmp(argv[1], "recursive")) {
        ContextId g = context_for(1, &vA);
        uint64_t ps[] = { vA };
        VarSetId params = varset_make(ps, 1);
        DimSetId dims = dimset_make(NULL, 0);
        SymbolId bad = define_global("bad", params, dims, A);
        SymbolId dependent = define_global("dependent", params, dims, A);
        RefId bad_ref = global_ref(bad), dependent_ref = global_ref(dependent);
        TermVarId x = declare_term(A, fc_true());
        RefId xx = ref_var(x);
        RefId pairer = mk_lam(x, A, mk_pair(xx, xx));
        set_global_body(bad, mk_app(pairer, dependent_ref));
        set_global_body(dependent, bad_ref);
        Inference first = infer(g, fc_true(), bad_ref);
        failures += first.st != CK_INVALID;
        printf("infer bad:A := (lambda x:A. (x,x)) dependent: %s (expected INVALID)\n", check_status_name(first.st));
        Inference second = infer(g, fc_true(), dependent_ref);
        failures += second.st != CK_INVALID;
        printf("infer dependent:A := bad after rejected bad body: %s (expected INVALID)\n", check_status_name(second.st));
        WhnfStatus ws;
        EvalResult *r = observe_checked(g, dependent_ref, &ws, &why);
        failures += ws != W_INVALID;
        printf("checked observation of dependent: status=%d, result=", (int)ws);
        print_result(r, stdout); putchar('\n');
        printf("whole signature: %s (expected INVALID)\n", check_status_name(check_signature(&why)));
    } else if (argc > 1 && !strcmp(argv[1], "concurrent")) {
        storm_ctx = context_for(1, &vA);
        storm_a = A; storm_b = A;
        /* Finite, well-typed, alpha-equivalent products. Distinct formal
         * identities force a real conversion instead of a pointer hit. */
        for (int k = 0; k < 50; ++k) {
            TermVarId x = declare_term(A, fc_true());
            TermVarId y = declare_term(A, fc_true());
            storm_a = mk_pi(x, A, storm_a);
            storm_b = mk_pi(y, A, storm_b);
        }
        CheckStatus c = check_context(storm_ctx, &why);
        printf("prechecked context: %s\n", check_status_name(c));
        pthread_t ts[8]; size_t ids[8];
        pthread_barrier_init(&gate, NULL, 8);
        for (size_t k = 0; k < 8; ++k) { ids[k] = k; pthread_create(&ts[k], NULL, convert_client, &ids[k]); }
        for (size_t k = 0; k < 8; ++k) pthread_join(ts[k], NULL);
        for (size_t k = 0; k < 8; ++k) {
            printf("concurrent conversion %zu: %s (expected EQUAL)\n", k, conv_status_name(storm_result[k]));
            failures += storm_result[k] != CV_EQUAL;
        }
        printf("serial retry: %s (expected EQUAL)\n", conv_status_name(convert_type(storm_ctx, fc_true(), storm_a, storm_b)));
        pthread_barrier_destroy(&gate);
    } else {
        TermVarId vx = declare_term(U0, fc_true());
        TermVarId vy = declare_term(U0, fc_true());
        ContextId target = context_for(1, &vx);
        MapId map = map_single_term(vx, ref_var(vy));
        CheckStatus s = check_map(empty, fc_false(), map, target, fc_true(), &why);
        failures += s != CK_INVALID;
        printf("false-face map with undeclared image y: %s (expected INVALID)\n", check_status_name(s));

        TermVarId z = declare_term(U0, fc_true());
        RefId beta_A = mk_app(mk_lam(z, U0, ref_var(z)), A);
        TermVarId va = declare_term(A, fc_true());
        ContextId prefix = context_for(1, &vA);
        printf("A versus (lambda Z:U0. Z) A: %s (expected EQUAL)\n", conv_status_name(convert_type(prefix, fc_true(), A, beta_A)));
        CtxDecl compatible[] = { {S_TERM, vA, U0}, {S_TERM, va, beta_A} };
        ContextId gc = context_make(2, compatible, fc_true());
        s = check_context(gc, &why);
        failures += s != CK_VALID;
        printf("context with beta-equivalent declaration: %s (expected VALID); %s\n", check_status_name(s), why);

        RefId AA = mk_fun(0, 0, A, A);
        TermVarId vf = declare_term(AA, fc_true());
        TermVarId vz = declare_term(AA, fc_true());
        RefId f = ref_var(vf), a = ref_var(va);
        RefId identity = mk_lam(vz, AA, ref_var(vz));
        TermVarId xs[] = { vA, va, vf };
        ContextId g = context_for(3, xs);
        printf("neutral ((lambda f. f) f) a versus f a: %s (expected EQUAL)\n",
               conv_status_name(convert_term(g, fc_true(), mk_app(mk_app(identity, f), a), mk_app(f, a), A)));

        TermVarId vxA = declare_term(A, fc_true());
        RefId before_substitution = reindex1(mk_refl(0, A, ref_var(vxA)), vxA, a);
        RefId after_substitution = mk_refl(0, A, a);
        failures += before_substitution != after_substitution;
        printf("fixed-template refl: reindex(mk_refl(0, A,x),x->a) == mk_refl(0, A,a): %s (expected identical references)\n",
               before_substitution == after_substitution ? "identical" : "distinct");
        EvalEvents ev0 = eval_events(); WhnfStatus ws;
        (void)whnf(before_substitution, fc_true(), &ws);
        (void)whnf(after_substitution, fc_true(), &ws);
        eval_run();
        EvalEvents ev1 = eval_events();
        failures += ev1.launch - ev0.launch != 1;
        printf("fixed-template refl observations: %zu new producer launches (expected 1)\n", ev1.launch - ev0.launch);
        printf("same refl terms remain mathematically convertible: %s\n",
               conv_status_name(convert_term(g, fc_true(), before_substitution, after_substitution, mk_path_const(0, A, a, a))));
    }
    check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

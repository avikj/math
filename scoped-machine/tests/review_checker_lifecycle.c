#define _POSIX_C_SOURCE 200809L
#include "../src/check.h"
#include "../src/lib.h"
#include <pthread.h>

static pthread_barrier_t gate;
static ContextId G;
static RefId left, right;
static ConvStatus result[8];
static void *client(void *p) {
    size_t k = *(size_t *)p;
    pthread_barrier_wait(&gate);
    result[k] = convert_type(G, fc_true(), left, right);
    return NULL;
}
int main(void) {
    machine_init(); eval_init(); check_init();
    const char *why = "";
    RefId U = mk_universe(0);
    TermVarId a = declare_term(U, fc_true()); RefId A = ref_var(a);
    CtxDecl ds[] = {{S_TERM, a, U}};
    G = context_make(1, ds, fc_true());
    require(check_context(G, &why) == CK_VALID, "initial context");
    /* Same process and main thread; a fresh checker session has no claims. */
    check_free(); check_init();
    left = right = A;
    for (int k = 0; k < 50; k++) {
        TermVarId x = declare_term(A, fc_true()), y = declare_term(A, fc_true());
        left = mk_pi_lv(0, 0, x, A, left); right = mk_pi_lv(0, 0, y, A, right);
    }
    pthread_t threads[7]; size_t ids[8];
    pthread_barrier_init(&gate, NULL, 8);
    for (size_t k = 0; k < 7; k++) { ids[k] = k; pthread_create(&threads[k], NULL, client, &ids[k]); }
    ids[7] = 7; client(&ids[7]);
    for (size_t k = 0; k < 7; k++) pthread_join(threads[k], NULL);
    int failures = 0;
    for (size_t k = 0; k < 8; k++) { printf("fresh-session client %zu: %s\n", k, conv_status_name(result[k])); failures += result[k] != CV_EQUAL; }
    pthread_barrier_destroy(&gate);
    check_free(); eval_free(); machine_free();
    return failures ? 1 : 0;
}

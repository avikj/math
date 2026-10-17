/* BOUNDS-COMPLETION §6/§7: nesting independent of the native stack. Deep
 * structural terms are shaped, validated, evaluated and checked on a thread
 * whose native stack is deliberately small (256 KiB); the kernel's recursive
 * procedures continue on added stack segments (kstack.h).
 * Run: test_deep N */
#include "check.h"
#include "lib.h"
#include "shape.h"
#include "kstack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

static size_t N; static int ok;
static void *body(void *unused) {
    (void)unused;
    RefId U = mk_universe(0); TermVarId va = declare_term(U, fc_true()); RefId A = ref_var(va);
    TermVarId vx = declare_term(A, fc_true()); RefId x = ref_var(vx);
    RefId AA = mk_fun(0, 0, A, A); TermVarId vf = declare_term(AA, fc_true()); RefId f = ref_var(vf);
    RefId t = x; for (size_t i = 0; i < N; i++) t = mk_app(f, t);
    CtxDecl ds[] = { { S_TERM, va, U }, { S_TERM, vx, A }, { S_TERM, vf, AA } }; ContextId G = context_make(3, ds, fc_true());
    const char *why = NULL;
    ShapeId s = shape_of(t);
    bool valid = ref_validate(t, &why);
    WhnfStatus ws; EvalResult *r = whnf(t, fc_true(), &ws);
    CheckStatus cs = check(G, fc_true(), t, A, &why);
    printf("depth %zu on a 256 KiB thread: shape=%d validate=%d whnf=%d check=%s segments=%zu\n", N, s != 0, valid, ws == W_OK && r != NULL, cs == CK_VALID ? "VALID" : "not valid", kstack_segments());
    ok = s && valid && ws == W_OK && r && cs == CK_VALID && kstack_segments() > 0;
    return NULL;
}
int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
    N = argc > 1 ? strtoull(argv[1], NULL, 10) : 20000;
    machine_init(); eval_init(); check_init();
    pthread_attr_t a; pthread_attr_init(&a); pthread_attr_setstacksize(&a, (size_t)256 << 10);
    pthread_t t; assert(pthread_create(&t, &a, body, NULL) == 0); pthread_join(t, NULL);
    check_free(); eval_free(); machine_free();
    return ok ? 0 : 1;
}

/* examples/embed.c — the machine from a host program: load the library, check and define, run. */
#include <stdio.h>
#include <string.h>
#include "cubical.h"

int main(void) {
    cub_init(0);
    FILE *quiet = fopen("/dev/null", "w");
    cub_output(quiet);
    const char *libs[] = { "lib/prelude.ctt", "lib/code.ctt", "lib/check.ctt", "lib/std.ctt" };
    for (int i = 0; i < 4; i++) if (cub_load_file(libs[i]) != 0) { printf("load %s: %s\n", libs[i], cub_error()); return 1; }

    /* a checked definition from the host */
    cub_verdict v = cub_define("twice", "(Pi n Nat Nat)", "(lam n (plus n n))");
    printf("define twice: %s\n", v.ok == 1 ? "ok" : "rejected");
    /* a rejected term comes back with its reason */
    cub_verdict w = cub_check("(Pi n Nat Bool)", "(lam n (plus n n))");
    printf("check: %s\n%s", w.ok == 1 ? "ok" : "rejected", w.reason ? w.reason : "");
    cub_free(w.reason);
    /* run */
    char *r = cub_eval("(twice (suc (suc zero)))");
    printf("(twice 2) = %s\n", r);
    cub_free(r);
    /* an error in the program is returned, not fatal */
    char *e = cub_eval("(undefined-name zero)");
    printf("error: %s\n", e ? "none" : cub_error());
    /* text loaded as a program */
    int f = cub_load_string("(checked thrice (Pi n Nat Nat) (lam n (plus n (twice n))))");
    char *t = cub_eval("(thrice (suc zero))");
    printf("thrice: %d failed, (thrice 1) = %s\n", f, t);
    cub_free(t);
    return 0;
}

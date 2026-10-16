#include "eval.h"
#include <assert.h>

/* Link with -Wl,--wrap=eval_init. Earlier standalone author witnesses set
 * CUBICAL_WORKERS without installing a pool; this makes the setting real. */
void __real_eval_init(void);
void __wrap_eval_init(void) {
    __real_eval_init();
    const char *v=getenv("REVIEW_WORKERS");
    size_t n=v?(size_t)strtoul(v,NULL,10):0;
    eval_set_workers(n);
    assert(eval_workers()==n);
    printf("review actual_workers=%zu\n",eval_workers());
}

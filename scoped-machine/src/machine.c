#include "state.h"
#include "eval.h"

Machine M;

void machine_init(void) {
    memset(&M, 0, sizeof M);
    interner_init(&M.keys);
    chunked_init(&M.defs, sizeof(Def));
    eval_init();                       /* one lifetime: the evaluator's memo is over these tables */
}

void machine_free(void) {
    eval_free();
    interner_free(&M.keys);
    chunked_free(&M.defs);
    memset(&M, 0, sizeof M);
}

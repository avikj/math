#include "state.h"
#include "lib.h"
#include "eval.h"

Machine M;

void machine_init(void) {
    memset(&M, 0, sizeof M);
    interner_init(&M.intervals);
    interner_init(&M.faces);
    interner_init(&M.dimsets);
    interner_init(&M.varsets);
    interner_init(&M.maps);
    interner_init(&M.refs);
    interner_init(&M.nominal);
    interner_init(&M.contexts);
    interner_init(&M.scopes); interner_init(&M.exprs); interner_init(&M.tnodes); interner_init(&M.tdefs); interner_init(&M.keys);
    chunked_init(&M.defs, sizeof(Def));
    eval_init();                       /* one lifetime: the evaluator's memo is over these tables */
    templates_init();                  /* the fixed library programs, as records of these tables */
}

void machine_free(void) {
    eval_free();
    lib_free();
    interner_free(&M.intervals);
    interner_free(&M.faces);
    interner_free(&M.dimsets);
    interner_free(&M.varsets);
    interner_free(&M.maps);
    interner_free(&M.refs);
    interner_free(&M.nominal);
    interner_free(&M.contexts);
    interner_free(&M.scopes); interner_free(&M.exprs); interner_free(&M.tnodes); interner_free(&M.tdefs); interner_free(&M.keys);
    chunked_free(&M.defs);
    memset(&M, 0, sizeof M);
}

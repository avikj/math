#include "state.h"

Machine M;

void machine_init(void) {
    memset(&M, 0, sizeof M);
    interner_init(&M.intervals);
    interner_init(&M.faces);
    interner_init(&M.dimsets);
    interner_init(&M.varsets);
    interner_init(&M.maps);
    interner_init(&M.origins);
    interner_init(&M.refs);
    interner_init(&M.nominal);
    wordmap_init(&M.reindex_memo);
    wordmap_init(&M.compose_memo);
}

void machine_free(void) {
    interner_free(&M.intervals);
    interner_free(&M.faces);
    interner_free(&M.dimsets);
    interner_free(&M.varsets);
    interner_free(&M.maps);
    interner_free(&M.origins);
    interner_free(&M.refs);
    interner_free(&M.nominal);
    wordmap_free(&M.reindex_memo);
    wordmap_free(&M.compose_memo);
    free(M.origin_side);
    free(M.ref_side);
    free(M.term_decl);
    free(M.defs);
    free(M.nominal_val);
    free(M.term_prov);
    free(M.dim_prov);
    memset(&M, 0, sizeof M);
}

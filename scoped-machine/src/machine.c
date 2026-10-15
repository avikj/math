#include "state.h"
#include "lib.h"

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
    interner_init(&M.contexts);
    interner_init(&M.scopes); interner_init(&M.exprs); interner_init(&M.tnodes); interner_init(&M.tenvs); interner_init(&M.tdefs); interner_init(&M.keys);
    wordmap_init(&M.trav_memo); wordmap_init(&M.interp_memo);
    chunked_init(&M.scope_side, sizeof(ScopeSide)); chunked_init(&M.tnode_side, sizeof(TNodeSide));
    wordmap_init(&M.reindex_memo);
    wordmap_init(&M.compose_memo);
    chunked_init(&M.origin_side, sizeof(OriginSide));
    chunked_init(&M.ref_side, sizeof(RefSide));
    chunked_init(&M.term_decl, sizeof(TermDecl));
    chunked_init(&M.dim_prov, sizeof(uint64_t));
    chunked_init(&M.nominal_val, sizeof(uint64_t));
    chunked_init(&M.defs, sizeof(Def));
    pthread_mutexattr_t a; pthread_mutexattr_init(&a);
    pthread_mutexattr_settype(&a, PTHREAD_MUTEX_RECURSIVE);
    pthread_mutex_init(&M.term_mu, &a);
    pthread_mutexattr_destroy(&a);
}

void machine_free(void) {
    lib_free();
    interner_free(&M.intervals);
    interner_free(&M.faces);
    interner_free(&M.dimsets);
    interner_free(&M.varsets);
    interner_free(&M.maps);
    interner_free(&M.origins);
    interner_free(&M.refs);
    interner_free(&M.nominal);
    interner_free(&M.contexts);
    interner_free(&M.scopes); interner_free(&M.exprs); interner_free(&M.tnodes); interner_free(&M.tenvs); interner_free(&M.tdefs); interner_free(&M.keys);
    wordmap_free(&M.trav_memo); wordmap_free(&M.interp_memo);
    chunked_free(&M.scope_side); chunked_free(&M.tnode_side);
    wordmap_free(&M.reindex_memo);
    wordmap_free(&M.compose_memo);
    chunked_free(&M.origin_side);
    chunked_free(&M.ref_side);
    chunked_free(&M.term_decl);
    chunked_free(&M.dim_prov);
    chunked_free(&M.nominal_val);
    chunked_free(&M.defs);
    pthread_mutex_destroy(&M.term_mu);
    memset(&M, 0, sizeof M);
}

#include "state.h"
#include "lib.h"

Machine M;
/* the machine lifetime generation: thread-local construction state that
 * caches machine handles (the template source face κ) is qualified by it */
static uint64_t machine_gen_ctr;
uint64_t machine_generation(void) { return __atomic_load_n(&machine_gen_ctr, __ATOMIC_ACQUIRE); }

void machine_init(void) {
    memset(&M, 0, sizeof M);
    __atomic_add_fetch(&machine_gen_ctr, 1, __ATOMIC_ACQ_REL);
    interner_init(&M.intervals);
    interner_init(&M.faces);
    interner_init(&M.dimsets);
    interner_init(&M.varsets);
    interner_init(&M.maps);
    interner_init(&M.refs);
    interner_init(&M.nominal);
    interner_init(&M.contexts);
    interner_init(&M.scopes); interner_init(&M.exprs); interner_init(&M.tnodes); interner_init(&M.tdefs); interner_init(&M.keys);
    chunked_init(&M.scope_side, sizeof(ScopeSide)); chunked_init(&M.tnode_side, sizeof(TNodeSide));
    chunked_init(&M.ref_side, sizeof(RefSide));
    chunked_init(&M.term_decl, sizeof(TermDecl));
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
    interner_free(&M.refs);
    interner_free(&M.nominal);
    interner_free(&M.contexts);
    interner_free(&M.scopes); interner_free(&M.exprs); interner_free(&M.tnodes); interner_free(&M.tdefs); interner_free(&M.keys);
    chunked_free(&M.scope_side); chunked_free(&M.tnode_side);
    chunked_free(&M.ref_side);
    chunked_free(&M.term_decl);
    chunked_free(&M.nominal_val);
    chunked_free(&M.defs);
    pthread_mutex_destroy(&M.term_mu);
    memset(&M, 0, sizeof M);
}

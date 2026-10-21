/* scope.h — scoped traversal (§50).
 *
 * Bound occurrences inside construction records are (depth, slot) atoms in
 * the variable / dimension id space (term.h `bound_id`); depth 0 is the
 * immediately enclosing binder. CLOSE turns concrete identities into those
 * atoms; APPLY substitutes values for depth-0 atoms and lowers deeper ones;
 * RE (a map) touches free identities only. */
#ifndef CUBICAL_SCOPE_H
#define CUBICAL_SCOPE_H

#include "term.h"

/* ---- scoped traversal (scopefam.c) ----
 * A traversal key [kind, depth, context]. The binders are construction
 * nodes; their locals are (depth, slot) atoms. CLOSE (context:
 * the record identity ↦ slot) closes identities into atoms of the key's
 * depth; APPLY (context: an environment slot ↦ value) replaces those atoms
 * and lowers deeper ones; LOWER removes one empty level (∀); RE (context: a
 * map) substitutes free identities and carries no depth. */
enum { TR_CLOSE = 1, TR_APPLY, TR_RE, TR_LOWER };
uint64_t trav_key(unsigned kind, unsigned depth, uint64_t ctx);
uint64_t re_key(uint64_t map);      /* RE at a map */
uint64_t close_key(uint64_t ctx);   /* CLOSE at depth 0 */
uint64_t apply_key(uint64_t env);   /* APPLY at depth 0 */
void scope_families_init(void);
#endif

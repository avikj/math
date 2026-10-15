/* canon.h — exact canonical form of the reachable record graph modulo a
 * consistent renaming of generated identities (§25, §31 comparison).
 *
 * The records reachable from the registered roots (results and cache keys)
 * are exported as a labelled graph: references, nominal (provenance)
 * records, faces, intervals, clauses, literals, map entries and input names.
 * Generated names are identified by their provenance record, input names
 * by their declaration index among input names, global symbols by name.
 * Ordered children (fields, binders, typed key items) keep their order;
 * unordered collections (map entries, DNF clauses, literals) are compared
 * as sets. Node classes are computed by exact partition refinement
 * (signature = own label, ordered child classes, multiset of unordered
 * child classes; classes renumbered by sorted signature each round until
 * stable), so the class of a node depends only on the graph up to
 * isomorphism — no hashing is involved. The dump then numbers nodes by one
 * DFS from the roots with unordered children in class order, so aliasing is
 * preserved (one record ↔ one number) and two runs of the same initial
 * configuration produce identical text exactly when their result graphs
 * are equal up to renaming.
 */
#ifndef CUBICAL_CANON_H
#define CUBICAL_CANON_H

#include "eval.h"
#include "match.h"

typedef struct Canon Canon;

Canon *canon_new(void);
void canon_free(Canon *c);
/* roots, in a fixed order chosen by the caller */
void canon_add_result(Canon *c, const char *label, const EvalResult *r);   /* r may be NULL (pending) */
/* a cache key with its per-key event counts; keys are emitted after the
 * results, ordered canonically */
void canon_add_key(Canon *c, RefId ref, FaceId face, size_t req, size_t del, size_t pub, int state);
/* export the labelled graph (machine-independent; survives machine_free).
 * Results are ordered roots, keys are set roots. The caller owns it. */
Graph *canon_export(Canon *c);
/* diagnostic text dump (refinement-ordered DFS numbering); returns the text (owned by c) */
const char *canon_finish(Canon *c, size_t *len);

#endif

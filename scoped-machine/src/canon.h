/* canon.h — canonical form of the reachable record graph modulo a consistent
 * renaming of generated identities.
 *
 * Generated names (binder variables, keyed fresh names) are identified by
 * their provenance record; input names by their declaration index among
 * input names; global symbols by name. A renaming-invariant hash orders
 * unordered collections (map entries, DNF clauses), and a DFS from the roots
 * numbers records in that order, so the textual dump of two runs of the same
 * initial configuration coincides exactly when the result graphs are equal
 * up to renaming, with aliasing preserved (one record ↔ one number).
 */
#ifndef CUBICAL_CANON_H
#define CUBICAL_CANON_H

#include "eval.h"

typedef struct Canon Canon;

Canon *canon_new(void);
void canon_free(Canon *c);
/* renaming-invariant hashes */
uint64_t canon_hash_ref(Canon *c, RefId t);
uint64_t canon_hash_face(Canon *c, FaceId f);
uint64_t canon_hash_interval(Canon *c, IntervalId r);
/* append the canonical dump of everything reachable from t (new records
 * only) to the text buffer, and return the record number of t */
size_t canon_dump_ref(Canon *c, RefId t);
void canon_dump_face_text(Canon *c, FaceId f);        /* appends inline text */
void canon_dump_result(Canon *c, const EvalResult *r); /* appends a line */
void canon_text(Canon *c, const char *s);             /* append raw text */
const char *canon_buffer(Canon *c, size_t *len);

#endif

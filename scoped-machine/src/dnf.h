/* dnf.h — canonical antichain normal forms shared by intervals (§3) and
 * faces (§4).
 *
 * A clause is a sorted set of atoms (u64). A DNF is a list of clauses.
 * Canonical form: every clause sorted without repeats; no repeated clause;
 * no clause strictly containing another clause; clauses in a fixed total
 * order (length, then lexicographic).
 *
 * Word encoding of a canonical DNF: [nclauses, len_1, atoms..., len_2, ...].
 */
#ifndef CUBICAL_DNF_H
#define CUBICAL_DNF_H

#include "common.h"

typedef struct {
    uint64_t *a;
    size_t n, cap;
} Clause;

typedef struct {
    Clause *c;
    size_t n, cap;
} Dnf;

void dnf_init(Dnf *d);
void dnf_free(Dnf *d);
/* append a clause (copied; atoms are sorted/deduplicated on normalize) */
void dnf_add_clause(Dnf *d, const uint64_t *atoms, size_t n);
/* union of two clauses, appended */
void dnf_add_clause_union(Dnf *d, const Clause *x, const Clause *y);
/* normalize in place. If contradiction(c) is non-NULL, clauses for which it
 * returns true are discarded BEFORE absorption (face rule). */
void dnf_normalize(Dnf *d, bool (*contradiction)(const Clause *));
/* decode from words / encode to words */
void dnf_decode(Dnf *d, const uint64_t *w, size_t n);
void dnf_encode(const Dnf *d, Words *out);
/* clause containment: every atom of small is in big (both sorted) */
bool clause_subset(const Clause *small, const Clause *big);

#endif

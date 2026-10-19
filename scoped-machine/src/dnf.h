/* dnf.h — canonical antichain normal forms shared by intervals (§3) and
 * faces (§4).
 *
 * A clause is a sorted set of atoms (u64). Canonical form: every clause
 * sorted without repeats; no repeated clause; no clause strictly containing
 * another clause; clauses in a fixed total order (length, then
 * lexicographic). Normal forms are produced only by the stepped operations
 * (dnfam.c); the host forms the constants 0, 1 and the single atoms.
 *
 * Word encoding of a canonical DNF: each clause's atoms followed by DNF_SEP,
 * clauses in canonical order (false = no words, true = [DNF_SEP]). A clause
 * is read by walking to its separator; every operation scans clauses in
 * order, so no position is reached through an unrelated one.
 */
#ifndef CUBICAL_DNF_H
#define CUBICAL_DNF_H

#include "common.h"
#define DNF_SEP UINT64_MAX

/* print a canonical record: clauses joined by `or`, atoms by `and`, the
 * empty record as `zero`, the empty clause as `one` */
void dnf_print(const uint64_t *w, size_t n, FILE *f, const char *zero, const char *one, void (*atom)(uint64_t a, FILE *f));

#endif

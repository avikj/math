/* pins.h — the definition revisions an observation is bound to.
 *
 * A revision of a global symbol is (symbol, body), body 0 for the opaque
 * declaration; a body is written once, so a symbol has at most two. A pin
 * set maps each symbol an observation may reach to the revision it reads:
 * the total substitution record [(symbol, PS_REF, body)*, 0] (equal sets are
 * one id), read and extended by the one stepped lookup and set, listed in
 * symbol order by subst_size / subst_get.
 *
 * The pin set of a request is the closure of the symbols its roots name
 * (globals.of) through the declarations and the bodies of the revisions
 * read: a checked observation validates exactly those revisions and
 * evaluates under them;
 * an unchecked observation reads the current revisions once, at its start.
 * The closure is keyed by the definition environment's snapshot (§79.2).
 */
#ifndef CUBICAL_PINS_H
#define CUBICAL_PINS_H

#include "eval.h"

typedef uint64_t PinSet;
PinSet pins_empty(void);

/* the closure family: key (roots, snapshot), roots the record [kind, id]*
 * (kind 0 a reference, 1 a scope), snapshot the current env_snapshot() */
uint64_t env_snapshot(void);
/* outside jobs: the closure of refs at the current revisions */
PinSet pins_current(size_t n, const RefId *refs);
void pins_families_init(void);

#endif

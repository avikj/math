/* pins.h — the definition revisions an observation is bound to.
 *
 * A revision of a global symbol is (symbol, body), body 0 for the opaque
 * declaration; a body is written once, so a symbol has at most two. A pin
 * set maps each symbol an observation may reach to the revision it reads: a
 * canonical hash trie of small interned records (equal sets are one id), so
 * insertion and lookup are bounded (one small intern or read per level).
 *
 * The pin set of a request is the closure of the symbols its roots name
 * (globals.of) through the declarations and the bodies of the revisions
 * read: a checked observation validates exactly those revisions and
 * evaluates under them;
 * an unchecked observation reads the current revisions once, at its start.
 * No environment-wide snapshot, no version in any key.
 */
#ifndef CUBICAL_PINS_H
#define CUBICAL_PINS_H

#include "eval.h"

typedef uint64_t PinSet;
PinSet pins_empty(void);
PinSet pins_insert(PinSet P, SymbolId s, RefId body);       /* bounded */
bool pins_lookup(PinSet P, SymbolId s, RefId *body);        /* bounded */
size_t pins_symbols(PinSet P, SymbolId *out, size_t max);   /* in-order listing (diagnostics, validation) */

/* the closure at the current revisions, as a stepped subroutine over the
 * roots in buf: pairs (kind, id), kind 0 a reference, 1 a scope */
Cont *pins_closure_sub(const Cont *caller, WordBuf *roots);
/* outside jobs */
PinSet pins_current(size_t n, const RefId *refs);
void pins_families_init(void);

#endif

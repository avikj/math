/* state.h — the machine's immutable record tables.
 *
 * Everything the evaluator observes is an interned immutable record of the
 * one record table. There is one definition environment per machine.
 */
#ifndef CUBICAL_STATE_H
#define CUBICAL_STATE_H

#include "common.h"
#include "intern.h"

typedef struct { VarSetId params; DimSetId dims; const char *name; RefId type; /* declared type over the parameters (0 = undeclared) */
                 uint64_t body; /* 0 until supplied; then its body */ bool opaque; } Def;

typedef struct {
    Interner keys;        /* every record: intervals, faces, sets, substitutions, references,
                           * variables, contexts, scopes, template expressions and nodes, keys */

    /* side data, non-moving; an element is written before its id is
     * published and never changes afterwards */
    Chunked defs;         /* Def per SymbolId-1 */
    size_t n_fresh, n_defs;   /* host declaration serials; symbol ids (atomic) */
} Machine;

extern Machine M;

/* a small record of the key store and its words */
static inline uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
static inline const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }
static inline uint64_t rword(uint64_t id, size_t i) { size_t n; return interner_get(&M.keys, id, &n)[i]; }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })

void machine_init(void);
void machine_free(void);

#endif

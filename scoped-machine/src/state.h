/* state.h — the machine's immutable record tables.
 *
 * Everything the evaluator observes is an interned immutable record held in
 * one of these tables. There is one definition environment per machine.
 */
#ifndef CUBICAL_STATE_H
#define CUBICAL_STATE_H

#include "common.h"
#include "intern.h"

typedef struct { RefId body; VarSetId params; DimSetId dims; const char *name; RefId type; /* declared type over the parameters (0 = undeclared) */ } Def;

typedef struct {
    Interner intervals;   /* IntervalId  → canonical interval DNF words */
    Interner faces;       /* FaceId      → canonical face DNF words */
    Interner dimsets;     /* DimSetId    → sorted DimVarId list */
    Interner varsets;     /* VarSetId    → sorted TermVarId list */
    Interner maps;        /* MapId       → raw map record */
    Interner refs;        /* RefId       → reference record */
    Interner nominal;     /* variables: their nominal records (key, sort, type, required) */
    Interner contexts;    /* ContextId   → occurrence context record */
    Interner scopes;      /* ScopeId     → scope record (§50) */
    Interner exprs;       /* template expression DAG nodes (§51) */
    Interner tnodes;      /* template constructor nodes */
    Interner tdefs;       /* template definitions (signature + root) */
    Interner keys;        /* interned word tuples used as memo keys */

    /* side data, non-moving; an element is written before its id is
     * published and never changes afterwards */
    Chunked defs;         /* Def per SymbolId-1 */
    size_t n_fresh, n_defs;   /* host declaration serials; symbol ids (atomic) */
    uint64_t env_gen;     /* the definition environment's snapshot: bumped by each declaration and body (host only, never during a computation) */
} Machine;

extern Machine M;

/* a small record of the key store and its words */
static inline uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
static inline const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })

void machine_init(void);
void machine_free(void);

#endif

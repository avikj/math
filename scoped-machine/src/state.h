/* state.h — the machine's immutable record tables.
 *
 * Everything the evaluator observes is an interned immutable record held in
 * one of these tables. There is one definition environment per machine.
 */
#ifndef CUBICAL_STATE_H
#define CUBICAL_STATE_H

#include "common.h"
#include "intern.h"

typedef struct { DimSetId support; VarSetId freevars; FaceId required; uint32_t published; } RefSide;   /* published: release-stored after the side data; a reference found by content is complete only when set */
typedef struct { RefId type; FaceId required; } TermDecl;   /* type: release-stored after required; nonzero once declared */
typedef struct { RefId body; VarSetId params; DimSetId dims; const char *name; RefId type; /* declared type over the parameters (0 = undeclared) */ uint64_t ctx; /* the parameter context */ } Def;
typedef struct { DimSetId support; VarSetId freevars; } ScopeSide;
typedef struct { uint64_t free_slots; /* interned word list */ } TNodeSide;

typedef struct {
    Interner intervals;   /* IntervalId  → canonical interval DNF words */
    Interner faces;       /* FaceId      → canonical face DNF words */
    Interner dimsets;     /* DimSetId    → sorted DimVarId list */
    Interner varsets;     /* VarSetId    → sorted TermVarId list */
    Interner maps;        /* MapId       → raw map record */
    Interner refs;        /* RefId       → reference record */
    Interner nominal;     /* binder identities (owner,slot,sort) and keyed fresh names */
    Interner contexts;    /* ContextId   → occurrence context record */
    Interner scopes;      /* ScopeId     → scope record (§50) */
    Interner exprs;       /* template expression DAG nodes (§51) */
    Interner tnodes;      /* template constructor nodes */
    Interner tdefs;       /* template definitions (signature + root) */
    Interner keys;        /* interned word tuples used as memo keys */
    Chunked scope_side;   /* ScopeSide per ScopeId-1 */
    Chunked tnode_side;   /* TNodeSide per node-1: computed free-slot sets */

    /* side data, non-moving; an element is written before its id is
     * published and never changes afterwards */
    Chunked ref_side;     /* RefSide per RefId-1 */
    Chunked term_decl;    /* TermDecl per TermVarId-1 (frozen once made) */
    Chunked nominal_val;  /* uint64_t minted name per nominal id-1 */
    Chunked defs;         /* Def per SymbolId-1 */
    size_t n_term_vars, n_dim_vars, n_defs;   /* allocation counters (atomic) */
} Machine;

extern Machine M;

void machine_init(void);
void machine_free(void);

#endif

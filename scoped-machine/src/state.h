/* state.h — the machine's immutable record tables.
 *
 * Everything the evaluator observes is an interned immutable record held in
 * one of these tables. There is one definition environment per machine.
 */
#ifndef CUBICAL_STATE_H
#define CUBICAL_STATE_H

#include "common.h"
#include "intern.h"

typedef struct { VarSetId ft; DimSetId fd; FaceId required; } OriginSide;
typedef struct { DimSetId support; VarSetId freevars; FaceId required; } RefSide;
typedef struct { RefId type; FaceId required; uint64_t prov; } TermDecl;
typedef struct { RefId body; VarSetId params; DimSetId dims; const char *name; } Def;

typedef struct {
    Interner intervals;   /* IntervalId  → canonical interval DNF words */
    Interner faces;       /* FaceId      → canonical face DNF words */
    Interner dimsets;     /* DimSetId    → sorted DimVarId list */
    Interner varsets;     /* VarSetId    → sorted TermVarId list */
    Interner maps;        /* MapId       → raw map record */
    Interner origins;     /* OriginId    → origin record */
    Interner refs;        /* RefId       → reference record */
    Interner nominal;     /* binder identities (owner,slot,sort) and keyed fresh names */
    Interner contexts;    /* ContextId   → occurrence context record */
    WordMap reindex_memo; /* (RefId, MapId) → RefId */
    WordMap compose_memo; /* (MapId, MapId) → MapId */

    /* side data, non-moving; an element is written before its id is
     * published and never changes afterwards */
    Chunked origin_side;  /* OriginSide per OriginId-1 */
    Chunked ref_side;     /* RefSide per RefId-1 */
    Chunked term_decl;    /* TermDecl per TermVarId-1 (frozen once made) */
    Chunked dim_prov;     /* uint64_t provenance per DimVarId-1 */
    Chunked nominal_val;  /* uint64_t minted name per nominal id-1 */
    Chunked defs;         /* Def per SymbolId-1 */
    size_t n_term_vars, n_dim_vars, n_defs;   /* under term_mu */

    /* one recursive mutex serializes creation in the term layer (origins,
     * references, declarations, nominal minting, definitions); reads of
     * published records and side data are lock-free */
    pthread_mutex_t term_mu;
} Machine;

extern Machine M;

void machine_init(void);
void machine_free(void);

#endif

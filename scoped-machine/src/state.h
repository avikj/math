/* state.h — the machine's immutable record tables.
 *
 * Everything the evaluator observes is an interned immutable record held in
 * one of these tables. There is one definition environment per machine.
 */
#ifndef CUBICAL_STATE_H
#define CUBICAL_STATE_H

#include "common.h"
#include "intern.h"

typedef struct {
    Interner intervals;   /* IntervalId  → canonical interval DNF words */
    Interner faces;       /* FaceId      → canonical face DNF words */
    Interner dimsets;     /* DimSetId    → sorted DimVarId list */
    Interner varsets;     /* VarSetId    → sorted TermVarId list */
    Interner maps;        /* MapId       → raw map record */
    Interner origins;     /* OriginId    → origin record */
    Interner refs;        /* RefId       → reference record */
    Interner nominal;     /* binder identities (owner,slot,sort) and keyed fresh names */
    WordMap reindex_memo; /* (RefId, MapId) → RefId */
    WordMap compose_memo; /* (MapId, MapId) → MapId */

    /* side data of origins, indexed by OriginId-1 */
    struct { VarSetId ft; DimSetId fd; FaceId required; } *origin_side;
    size_t origin_side_cap;
    /* side data of references, indexed by RefId-1 */
    struct { DimSetId support; VarSetId freevars; FaceId required; } *ref_side;
    size_t ref_side_cap;

    /* term variable declarations, indexed by TermVarId-1 (frozen once made) */
    struct { RefId type; FaceId required; } *term_decl;
    size_t n_term_vars, term_decl_cap;
    uint64_t n_dim_vars;

    /* global definitions, indexed by SymbolId-1 */
    struct { RefId body; VarSetId params; DimSetId dims; const char *name; } *defs;
    size_t n_defs, defs_cap;

    /* nominal payloads: for TERM binder identities, the minted TermVarId; for
     * DIM identities the minted DimVarId; indexed by nominal id-1 */
    uint64_t *nominal_val;
    size_t nominal_cap;
    /* provenance: the nominal id that minted a generated name (0 = input name
     * declared directly by the client); indexed by TermVarId-1 / DimVarId-1 */
    uint64_t *term_prov; size_t term_prov_cap;
    uint64_t *dim_prov; size_t dim_prov_cap;
} Machine;

extern Machine M;

void machine_init(void);
void machine_free(void);

#endif

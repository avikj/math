/* lib.h — the fixed library (§14–§18, §52–§54) through the template layer.
 *
 * Every helper is one fixed template program over typed parameters with
 * explicit universe levels (§59.1); an invocation is a TVIEW of the
 * program's root node, so specialization and invocation commute as an
 * identity of references for every parameter, type and family arguments
 * included. Nothing here evaluates. The composition clauses are instantiated
 * by `comp_clause` from the captured components of an exposed family head
 * (§54). */
#ifndef CUBICAL_LIB_H
#define CUBICAL_LIB_H

#include "template.h"

void lib_free(void);

/* ---- capture adapters (§54): abstract concrete identities into scopes ---- */
ScopeId capture_dim1(DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard);                 /* [j]. body */

/* ---- §52 programs; l, m are the exact universe levels of the type arguments ---- */
RefId mk_path_const(uint64_t l, RefId A, RefId lft, RefId r);
RefId mk_papp_const(uint64_t l, RefId A, RefId lft, RefId r, RefId p, IntervalId s);
RefId mk_coe(uint64_t l, ScopeId A, RefId cap);
RefId mk_fun(uint64_t l, uint64_t m, RefId X, RefId Y);
RefId mk_equiv(uint64_t l, uint64_t m, RefId X, RefId Y);
RefId mk_id_equiv(uint64_t l, RefId X);
RefId mk_ua(uint64_t l, RefId X, RefId Y, RefId e);

/* conveniences over a concrete dimension (capture then invoke) */
RefId mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap);

void lib_families_init(void);       /* comp.clause (registered by eval_init) */

#endif

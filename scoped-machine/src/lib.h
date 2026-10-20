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
ScopeId capture_term2(TermVarId x, RefId xtype, uint64_t xlevel, TermVarId e, RefId etype, uint64_t elevel, RefId body, RefId type, uint64_t level, FaceId guard);   /* [x, e]. body */

/* ---- §52 programs; l, m are the exact universe levels of the type arguments ---- */
RefId mk_path_const(uint64_t l, RefId A, RefId lft, RefId r);
RefId mk_refl(uint64_t l, RefId A, RefId a);
RefId mk_papp_const(uint64_t l, RefId A, RefId lft, RefId r, RefId p, IntervalId s);
RefId mk_path_rev(uint64_t l, RefId A, RefId lft, RefId r, RefId p);
RefId mk_path_concat(uint64_t l, RefId A, RefId x, RefId y, RefId z, RefId p, RefId q);
RefId mk_fun(uint64_t l, uint64_t m, RefId X, RefId Y);
RefId mk_contr(uint64_t l, RefId X);
RefId mk_fib(uint64_t l, uint64_t m, RefId X, RefId Y, RefId f, RefId y);
RefId mk_equiv(uint64_t l, uint64_t m, RefId X, RefId Y);
RefId mk_id_fun(uint64_t l, RefId X);
RefId mk_id_equiv(uint64_t l, RefId X);
RefId equiv_map(uint64_t l, uint64_t m, RefId X, RefId Y, RefId e);          /* fst e : X → Y */
RefId equiv_contr(uint64_t l, uint64_t m, RefId X, RefId Y, RefId e, RefId y);/* (snd e) y : Contr(fib) */
RefId mk_fill(uint64_t l, ScopeId A, FaceId phi, ScopeId u, RefId cap, IntervalId r);   /* A : [i]U_l, u : [i]A<i> on phi */
RefId mk_coe(uint64_t l, ScopeId A, RefId cap);
RefId mk_extend_contr(uint64_t l, RefId X, RefId c, RefId k, FaceId theta, RefId v);
RefId mk_ua(uint64_t l, RefId X, RefId Y, RefId e);
/* Down(l, lA, A, t, D, x, e, z) with D : [x:A, e:Path_A(t,x)] U_l (§54) */
RefId mk_down(uint64_t l, uint64_t lA, RefId A, RefId t, ScopeId D, RefId x, RefId e, RefId z);

/* conveniences over a concrete dimension (capture then invoke) */
RefId mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap);
RefId mk_fill_at(uint64_t l, DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId cap, IntervalId r);

/* ---- §53/§54: the structural composition clause for an exposed head ----
 * fam is the family head opened at the evaluator's dimension j (an
 * introduction of tag Π/Σ/PathP/Glue/U), tube_j the tube at j, phi its
 * face, cap the cap. Returns the clause instance, or 0 for a tag without a
 * clause. */
RefId comp_clause(DimVarId j, RefId fam, FaceId phi, RefId tube_j, RefId cap);
void lib_families_init(void);       /* comp.clause (registered by eval_init) */

#endif

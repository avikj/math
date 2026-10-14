/* lib.h — derived definitions over the core signature (§14–18).
 *
 * These construct references; they never evaluate. Every helper is a
 * definition in the object language built from the core constructors; the
 * composition clauses are invoked by the evaluator once a family head has
 * been exposed at a symbolic dimension.
 */
#ifndef CUBICAL_LIB_H
#define CUBICAL_LIB_H

#include "term.h"

/* interval lines */
IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j);  /* (r∧¬j)∨(s∧j) */

/* fill^i A_i [phi ↦ u_i] a0 (r) */
RefId mk_fill(DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId a0, IntervalId r);
/* hcomp^j_X [phi ↦ u_j] cap */
RefId mk_hcomp(DimVarId j, RefId X, FaceId phi, RefId u_j, RefId cap);
/* transport 0→1 along i ↦ A_i (empty tube) */
RefId mk_coe(DimVarId i, RefId A_i, RefId a0);
RefId mk_refl(RefId A, RefId a);                      /* ⟨_⟩ a : Path A a a */
RefId mk_path_const(RefId A, RefId l, RefId r);       /* Path A l r */
RefId mk_papp_const(RefId A, RefId l, RefId r, RefId p, IntervalId s);
RefId mk_path_rev(RefId A, RefId l, RefId r, RefId p);/* ⟨i⟩ p(¬i) */
RefId mk_path_concat(RefId A, RefId x, RefId y, RefId z, RefId p, RefId q);

/* equivalence data (§15) */
RefId mk_contr(RefId X);                              /* Σ(c:X).Π(x:X).Path X c x */
RefId mk_fib(RefId X, RefId Y, RefId f, RefId y);     /* Σ(x:X).Path Y (f x) y */
RefId mk_fun(RefId X, RefId Y);                       /* non-dependent Π */
RefId mk_equiv(RefId X, RefId Y);
RefId mk_id_fun(RefId X);
RefId mk_id_equiv(RefId X);
RefId equiv_map(RefId e);                             /* fst e */
RefId equiv_contr(RefId e, RefId y);                  /* (snd e) y : Contr(fib) */
/* ExtendContr(c,k; theta, v) = hcomp^j_X [theta ↦ k(v)@j] c */
RefId mk_extend_contr(RefId X, RefId c, RefId k, FaceId theta, RefId v);
RefId mk_line_equiv(DimVarId j, RefId X_j);           /* coe in Equiv(X_0, X_j) of IdEquiv(X_0) */
RefId mk_ua(RefId X, RefId Y, RefId e);               /* ⟨i⟩ Glue [(i=0)↦(X,e),(i=1)↦(Y,id)] Y */

/* structural composition clauses: the family has been exposed at dimension
 * i with head reference `fam` (an INTRODUCTION of the indicated tag). The
 * tube u_i and face phi are those of the composition opened at the same i. */
RefId comp_clause_pi(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap);
RefId comp_clause_sigma(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap);
RefId comp_clause_path(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap);
RefId comp_clause_glue(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap);
RefId comp_clause_universe(DimVarId i, RefId fam, FaceId phi, RefId u_i, RefId cap);

#endif

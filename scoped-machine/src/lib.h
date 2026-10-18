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
size_t lib_template_count(void);

/* interval line (r∧¬j)∨(s∧j): canonical interval syntax, no reference */
IntervalId iv_line(IntervalId r, IntervalId s, DimVarId j);

/* ---- capture adapters (§54): abstract concrete identities into scopes ---- */
ScopeId capture_dim1(DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard);                 /* [j]. body */
ScopeId capture_dim1_face(DimVarId j, FaceId body);                                                       /* [j]. face (total syntax) */
ScopeId capture_dim2(DimVarId i, DimVarId j, RefId body, RefId type, uint64_t level, FaceId guard);     /* [i, j]. body */
ScopeId capture_dim_term(DimVarId j, TermVarId x, RefId xtype, uint64_t xlevel, RefId body, RefId type, uint64_t level, FaceId guard);   /* [j, x:xtype]. body */
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
RefId mk_hcomp(uint64_t l, RefId X, FaceId phi, ScopeId u, RefId cap);                  /* u : [j]X on phi */
RefId mk_coe(uint64_t l, ScopeId A, RefId cap);
RefId mk_extend_contr(uint64_t l, RefId X, RefId c, RefId k, FaceId theta, RefId v);
RefId mk_line_equiv(uint64_t l, ScopeId X);
RefId mk_ua(uint64_t l, RefId X, RefId Y, RefId e);
/* Down(l, lA, A, t, D, x, e, z) with D : [x:A, e:Path_A(t,x)] U_l (§54) */
RefId mk_down(uint64_t l, uint64_t lA, RefId A, RefId t, ScopeId D, RefId x, RefId e, RefId z);

/* conveniences over a concrete dimension (capture then invoke) */
RefId mk_coe_at(uint64_t l, DimVarId i, RefId A_i, RefId cap);
RefId mk_fill_at(uint64_t l, DimVarId i, RefId A_i, FaceId phi, RefId u_i, RefId cap, IntervalId r);
RefId mk_hcomp_at(uint64_t l, DimVarId j, RefId X, FaceId phi, RefId u_j, RefId cap);

/* ---- §53/§54: the structural composition clause for an exposed head ----
 * fam is the family head opened at the evaluator's dimension j (an
 * introduction of tag Π/Σ/PathP/Glue/U), tube_j the tube at j, phi its
 * face, cap the cap; eta is the producer entry's face (the clause's source
 * annotation κ). Returns the clause instance, or 0 for a tag without a
 * clause. */
RefId comp_clause(DimVarId j, RefId fam, FaceId phi, RefId tube_j, RefId cap, FaceId eta);

/* frame families (kframe.h) */
#define capture_dim1_PARAMS(X) X(DimVarId, j) X(RefId, body) X(RefId, type) X(uint64_t, level) X(FaceId, guard)
#define capture_dim1_face_PARAMS(X) X(DimVarId, j) X(FaceId, body)
#define capture_dim2_PARAMS(X) X(DimVarId, i) X(DimVarId, j) X(RefId, body) X(RefId, type) X(uint64_t, level) X(FaceId, guard)
#define capture_dim_term_PARAMS(X) X(DimVarId, j) X(TermVarId, x) X(RefId, xtype) X(uint64_t, xlevel) X(RefId, body) X(RefId, type) X(uint64_t, level) X(FaceId, guard)
#define capture_term2_PARAMS(X) X(TermVarId, x) X(RefId, xtype) X(uint64_t, xlevel) X(TermVarId, e) X(RefId, etype) X(uint64_t, elevel) X(RefId, body) X(RefId, type) X(uint64_t, level) X(FaceId, guard)
KF_PROTO(capture_dim1, ScopeId, capture_dim1_PARAMS);
KF_PROTO(capture_dim1_face, ScopeId, capture_dim1_face_PARAMS);
KF_PROTO(capture_dim2, ScopeId, capture_dim2_PARAMS);
KF_PROTO(capture_dim_term, ScopeId, capture_dim_term_PARAMS);
KF_PROTO(capture_term2, ScopeId, capture_term2_PARAMS);
#define mk_path_const_PARAMS(X) X(uint64_t, l) X(RefId, A) X(RefId, lft) X(RefId, r)
KF_PROTO(mk_path_const, RefId, mk_path_const_PARAMS);
#define mk_refl_PARAMS(X) X(uint64_t, l) X(RefId, A) X(RefId, a)
KF_PROTO(mk_refl, RefId, mk_refl_PARAMS);
#define mk_papp_const_PARAMS(X) X(uint64_t, l) X(RefId, A) X(RefId, lft) X(RefId, r) X(RefId, p) X(IntervalId, s)
KF_PROTO(mk_papp_const, RefId, mk_papp_const_PARAMS);
#define mk_path_rev_PARAMS(X) X(uint64_t, l) X(RefId, A) X(RefId, lft) X(RefId, r) X(RefId, p)
KF_PROTO(mk_path_rev, RefId, mk_path_rev_PARAMS);
#define mk_path_concat_PARAMS(X) X(uint64_t, l) X(RefId, A) X(RefId, x) X(RefId, y) X(RefId, z) X(RefId, p) X(RefId, q)
KF_PROTO(mk_path_concat, RefId, mk_path_concat_PARAMS);
#define mk_fun_PARAMS(X) X(uint64_t, l) X(uint64_t, m) X(RefId, X_) X(RefId, Y)
KF_PROTO(mk_fun, RefId, mk_fun_PARAMS);
#define mk_contr_PARAMS(X) X(uint64_t, l) X(RefId, X_)
KF_PROTO(mk_contr, RefId, mk_contr_PARAMS);
#define mk_fib_PARAMS(X) X(uint64_t, l) X(uint64_t, m) X(RefId, X_) X(RefId, Y) X(RefId, f) X(RefId, y)
KF_PROTO(mk_fib, RefId, mk_fib_PARAMS);
#define mk_equiv_PARAMS(X) X(uint64_t, l) X(uint64_t, m) X(RefId, X_) X(RefId, Y)
KF_PROTO(mk_equiv, RefId, mk_equiv_PARAMS);
#define mk_id_fun_PARAMS(X) X(uint64_t, l) X(RefId, X_)
KF_PROTO(mk_id_fun, RefId, mk_id_fun_PARAMS);
#define mk_id_equiv_PARAMS(X) X(uint64_t, l) X(RefId, X_)
KF_PROTO(mk_id_equiv, RefId, mk_id_equiv_PARAMS);
#define equiv_map_PARAMS(X) X(uint64_t, l) X(uint64_t, m) X(RefId, X_) X(RefId, Y) X(RefId, e)
KF_PROTO(equiv_map, RefId, equiv_map_PARAMS);
#define equiv_contr_PARAMS(X) X(uint64_t, l) X(uint64_t, m) X(RefId, X_) X(RefId, Y) X(RefId, e) X(RefId, y)
KF_PROTO(equiv_contr, RefId, equiv_contr_PARAMS);
#define mk_fill_PARAMS(X) X(uint64_t, l) X(ScopeId, A) X(FaceId, phi) X(ScopeId, u) X(RefId, cap) X(IntervalId, r)
KF_PROTO(mk_fill, RefId, mk_fill_PARAMS);
#define mk_hcomp_PARAMS(X) X(uint64_t, l) X(RefId, X_) X(FaceId, phi) X(ScopeId, u) X(RefId, cap)
KF_PROTO(mk_hcomp, RefId, mk_hcomp_PARAMS);
#define mk_coe_PARAMS(X) X(uint64_t, l) X(ScopeId, A) X(RefId, cap)
KF_PROTO(mk_coe, RefId, mk_coe_PARAMS);
#define mk_extend_contr_PARAMS(X) X(uint64_t, l) X(RefId, X_) X(RefId, c) X(RefId, k) X(FaceId, theta) X(RefId, v)
KF_PROTO(mk_extend_contr, RefId, mk_extend_contr_PARAMS);
#define mk_line_equiv_PARAMS(X) X(uint64_t, l) X(ScopeId, X_)
KF_PROTO(mk_line_equiv, RefId, mk_line_equiv_PARAMS);
#define mk_ua_PARAMS(X) X(uint64_t, l) X(RefId, X_) X(RefId, Y) X(RefId, e)
KF_PROTO(mk_ua, RefId, mk_ua_PARAMS);
#define mk_down_PARAMS(X) X(uint64_t, l) X(uint64_t, lA) X(RefId, A) X(RefId, t) X(ScopeId, D) X(RefId, x) X(RefId, e) X(RefId, z)
KF_PROTO(mk_down, RefId, mk_down_PARAMS);
#define mk_coe_at_PARAMS(X) X(uint64_t, l) X(DimVarId, i) X(RefId, A_i) X(RefId, cap)
#define mk_fill_at_PARAMS(X) X(uint64_t, l) X(DimVarId, i) X(RefId, A_i) X(FaceId, phi) X(RefId, u_i) X(RefId, cap) X(IntervalId, rr)
#define mk_hcomp_at_PARAMS(X) X(uint64_t, l) X(DimVarId, j) X(RefId, X_) X(FaceId, phi) X(RefId, u_j) X(RefId, cap)
#define comp_clause_PARAMS(X) X(DimVarId, j) X(RefId, fam) X(FaceId, phi) X(RefId, tube_j) X(RefId, cap) X(FaceId, eta)
KF_PROTO(mk_coe_at, RefId, mk_coe_at_PARAMS);
KF_PROTO(mk_fill_at, RefId, mk_fill_at_PARAMS);
KF_PROTO(mk_hcomp_at, RefId, mk_hcomp_at_PARAMS);
KF_PROTO(comp_clause, RefId, comp_clause_PARAMS);

#endif

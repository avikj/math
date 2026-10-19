/* chain.h — the additive reading of the cubical presentation
 * (CUBICAL-STOKES-ADDENDUM §§1–5, §10).
 *
 * Exact signed integers, finitely supported modules over named units, cube
 * cells, sparse chains, cochains and chain maps are interned immutable
 * records; every operation is a family over them, one term or one face per
 * step.
 *
 *   z     [sign, limb_0 .. limb_{k-1}]        top limb nonzero; zero is [0]
 *   m     [(unit, z)*]                         sorted by unit, z ≠ 0
 *   gen   (kind, id)                           G_CUBE view, G_PROD product,
 *                                              G_PORT, G_HEAD, G_OCC
 *   view  [root scope, m, parameter map, n, image_1 .. image_n]
 *         image_r ∈ D(c_1..c_m) is the root's r-th dimension local
 *   prod  [kind_x, id_x, kind_y, id_y]
 *   chain [degree, (kind, id, z)*]             sorted by (kind, id), z ≠ 0
 *   cochain [CO_TABLE, degree, (kind, id, m)*]  |  [CO_COB, cochain]
 *   chain map [degree, (kind, id, chain)*]
 *
 * The coordinates c_k are canonical dimension atoms (keyed by k). A face
 * substitutes c_i ↦ ε and renumbers c_{k>i} ↦ c_{k−1} simultaneously in the
 * images, so both deletion orders of a codimension-two face are one view.
 */
#ifndef CUBICAL_CHAIN_H
#define CUBICAL_CHAIN_H

#include "eval.h"
#include "scope.h"

typedef enum { G_CUBE = 1, G_PROD, G_PORT, G_HEAD, G_OCC, G_TWIST } GenKind;   /* G_TWIST [view, unit]: a cell carrying a unit coefficient */
enum { CO_TABLE = 1, CO_COB };

/* exact signed integers and module elements (small records, host helpers) */
uint64_t z_from_i64(int64_t v);
uint64_t z_from_limbs(int negative, size_t n, const uint64_t *limbs);
uint64_t z_add(uint64_t a, uint64_t b);
uint64_t z_neg(uint64_t a);
uint64_t z_mul(uint64_t a, uint64_t b);
bool z_is_zero(uint64_t a);
bool z_to_i64(uint64_t a, int64_t *out);
uint64_t m_zero(void);
uint64_t m_unit(uint64_t unit, uint64_t z);
uint64_t m_add(uint64_t a, uint64_t b);
uint64_t m_scale(uint64_t z, uint64_t m);

/* cells */
DimVarId cube_coord(size_t k);                      /* c_k, k ≥ 1 */
uint64_t cube_view(ScopeId root, MapId params);     /* the root's identity view: image_r = c_r */
uint64_t cube_subst(uint64_t view, MapId sigma);        /* the parameter map composed with σ */
uint64_t cube_product(GenKind kx, uint64_t x, GenKind ky, uint64_t y);
size_t gen_degree(GenKind kind, uint64_t id);

/* the operations (families; synchronous drivers outside jobs) */
uint64_t cube_face(GenKind kind, uint64_t id, size_t i, int eps, GenKind *out_kind);   /* 1 ≤ i ≤ degree */
uint64_t cube_reindex(uint64_t view, size_t m2, const IntervalId *images);            /* c_k ↦ images[k-1] over c_1..c_m2 */
uint64_t chain_of(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *zs);
uint64_t chain_add(uint64_t c1, uint64_t c2);
uint64_t chain_scale(uint64_t c, uint64_t z);
uint64_t chain_boundary(uint64_t c);
uint64_t cochain_table(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *ms);
uint64_t cochain_cob(uint64_t a);
uint64_t chain_pair(uint64_t a, uint64_t c);       /* <a, c> ∈ the coefficient module */
uint64_t chain_map(uint64_t F, uint64_t c);        /* Σ m_x F(x) */
uint64_t chain_map_table(size_t degree, size_t n, const GenKind *kinds, const uint64_t *ids, const uint64_t *images);

/* local coefficients (ADDENDUM §6): a transport for each dimension local of
 * a root — a permutation of units, [(unit, image)*] — admitted as flat only
 * with a square witness naming every pair r < s, each pair commuting; 0 when
 * the witness is absent or invalid. The twisted boundary of [x, u] carries
 * the upper i-face's coefficient through the transport of the root local
 * that coordinate c_i is the image of. */
uint64_t perm_of(size_t n, const uint64_t *from, const uint64_t *to);
uint64_t local_system(ScopeId root, size_t nperm, const uint64_t *perms, size_t npairs, const uint64_t *pairs);
uint64_t twist_gen(uint64_t view, uint64_t unit);
uint64_t chain_tboundary(uint64_t c, uint64_t sys);
uint64_t cochain_cob_local(uint64_t a, uint64_t sys);   /* c ↦ <a, ∂_sys c> */
/* relative chains (ADDENDUM §8): c modulo the interface generators listed in I (a chain) */
uint64_t chain_relative(uint64_t c, uint64_t I);
void chain_families_init(void);

#endif

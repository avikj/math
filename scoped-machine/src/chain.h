/* chain.h — the additive reading of the cubical presentation
 * (CUBICAL-STOKES-ADDENDUM §§1–10).
 *
 * The source is the typed cubical construction: a presented n-cell is a
 * checked scope with n dimension locals (a root) and its cube view is the
 * root with a canonical simultaneous dimension map (one image in D(J) per
 * root coordinate, J the view's own coordinates c_1..c_m) and a parameter
 * map. FACE and CUBE_REINDEX compose the simultaneous maps: two restrictions
 * compose into one map, so the two computations of a corner use the same
 * coordinate assignment and the same interned cell. Chains, cochains, maps
 * and their pairings are readings over these references: immutable interned
 * descriptors (cells, exact module elements, sparse chains) and resumable
 * operations that run one bounded unit per job on the evaluator scheduler
 * (eval_job), charged to FC_CHAIN_STEPS.
 *
 * Cells come in the kinds the addendum names:
 *   VIEW      a cube view of a checked root (faces by substitution);
 *   PRESENTED an execution / comparison cell with its 2m declared faces; its
 *             admission checks every cubical face identity
 *             d_i^ε d_j^η = d_(j−1)^η d_i^ε (i<j) on the declared faces;
 *   DECLARED  a generator with a declared boundary chain (the resource
 *             incidence complex: produced − consumed); admission checks
 *             that the declared boundary is a cycle;
 *   PRODUCT   x×y with the product orientation (coordinates of x first);
 *             a product of two views is a view of the product root.
 * Coefficients are exact elements of finitely supported modules over named
 * units (integers: unit 0; tuples: units 0..k−1), signed exact naturals with
 * no word bound. Zero coefficients disappear from the chain reading; the
 * cells and every retained witness stay. */
#ifndef CUBICAL_CHAIN_H
#define CUBICAL_CHAIN_H
#include "scope.h"
#include "check.h"
#include "nat.h"

typedef uint64_t CellId;    /* 0: none */
typedef uint64_t ChainId;   /* an interned sparse chain (degree, terms sorted by cell) */
typedef uint64_t ModId;     /* an interned module element */
typedef struct { int sign; Nat mag; } Zx;   /* signed exact integer; sign ∈ {−1,0,1}, sign 0 iff mag 0 */

void chain_init(void);
void chain_free(void);

/* ---- exact integers and modules ---- */
Zx zx_i64(int64_t v);
Zx zx_nat(int sign, Nat mag);
Zx zx_add(Zx a, Zx b);
Zx zx_neg(Zx a);
Zx zx_mul(Zx a, Zx b);
bool zx_eq(Zx a, Zx b);
bool zx_is_zero(Zx a);
size_t zx_decimal(Zx a, char *buf, size_t cap);
Nat nat_mul_exact(Nat a, Nat b);              /* schoolbook, one FC_NAT_LIMBS transition per limb product */
ModId mod_zero(void);
ModId mod_unit(uint64_t unit, Zx c);          /* c·[unit] */
ModId mod_int(Zx c);                          /* c·[0] */
ModId mod_add(ModId a, ModId b);
ModId mod_scale(Zx c, ModId a);
ModId mod_neg(ModId a);
bool mod_is_zero(ModId a);
Zx mod_coef(ModId a, uint64_t unit);
size_t mod_nterms(ModId a);
void mod_term(ModId a, size_t k, uint64_t *unit, Zx *c);
bool mod_scalar(ModId a, Zx *c);              /* an element supported on unit 0 only */
size_t mod_print(ModId a, char *buf, size_t cap);

/* ---- coordinates and cells ---- */
DimVarId cube_coord(size_t k);                /* canonical coordinate c_k (k ≥ 1); no maximum */
enum { CK_VIEW = 1, CK_PRESENTED, CK_DECLARED, CK_PRODUCT };
/* a checked presented n-cell: the root's locals are n dimensions, its body in A under κ ∧ guard */
CheckStatus cell_admit_root(ContextId G, FaceId kappa, ScopeId root, const char **why);
CellId cell_view(ScopeId root, MapId params, size_t m, const IntervalId *images);   /* images over c_1..c_m */
CellId cell_root(ScopeId root, MapId params);                                         /* the identity view: degree n */
CellId cell_presented(uint64_t ns, uint64_t tag, size_t m, const CellId *faces, const char **why);   /* faces[2(i−1)+ε]; 0 when an identity fails */
CellId cell_declared(uint64_t ns, uint64_t tag, size_t m, ChainId boundary, const char **why);       /* 0 when ∂boundary ≠ 0 */
CellId cell_product(CellId x, CellId y);
int cell_kind(CellId x);
size_t cell_degree(CellId x);
uint64_t cell_tag(CellId x, uint64_t *ns);
bool cell_cubical(CellId x);                  /* faces defined: VIEW, PRESENTED, PRODUCT of cubical cells */
CellId cell_face(CellId x, size_t i, int eps);                                /* FACE(C,i,ε), 1 ≤ i ≤ m */
CellId cell_reindex(CellId x, size_t m2, const IntervalId *sigma);            /* CUBE_REINDEX: c_k ↦ sigma[k−1] ∈ D(c_1..c_m2) */
void cube_map_compose(size_t m, const IntervalId *sigma, size_t m2, const IntervalId *tau, IntervalId *out);   /* (σ∘τ)_k = σ_k[τ] */
CellId cell_param(CellId x, MapId tau);       /* base change of the parameters: params ; tau */
bool cell_view_parts(CellId x, ScopeId *root, MapId *params, size_t *n, const IntervalId **images);
RefId cell_body(CellId x);                    /* the view's body at its images (apply_scope; no evaluation) */
bool cell_degenerate(CellId x, size_t *coord);   /* a witness: a coordinate no image uses */
CellId cell_base_edge(CellId x, size_t i);    /* the edge of x along coordinate i at the all-zero vertex */
CellId cell_base_square(CellId x, size_t i, size_t j);   /* the 2-face in coordinates i < j at the all-zero vertex */

/* ---- chains (shared sparse terms of CellRef × coefficient) ---- */
ChainId chain_zero(size_t degree);
ChainId chain_gen(CellId x, ModId c);
ChainId chain_genz(CellId x, int64_t c);
ChainId chain_from(size_t degree, size_t n, const CellId *cells, const ModId *coefs);   /* combined, zeros dropped */
size_t chain_degree(ChainId c);
size_t chain_nterms(ChainId c);
void chain_term(ChainId c, size_t k, CellId *x, ModId *coef);
ModId chain_coef(ChainId c, CellId x);
bool chain_is_zero(ChainId c);
ChainId chain_add(ChainId a, ChainId b);
ChainId chain_scale(Zx s, ChainId a);
ChainId chain_sub(ChainId a, ChainId b);
ChainId chain_product(ChainId a, ChainId b);  /* bilinear; scalar coefficients multiply */
ChainId chain_normalize(ChainId c);           /* the normalized reading C/D: degenerate generators dropped (the source is unchanged) */
size_t chain_print(ChainId c, char *buf, size_t cap);

/* ---- local coefficient systems (§6) ----
 * T(edge, m, inverse): transport of m along a 1-cell (from its 0-end to its
 * 1-end; inverse back). units: the coefficient signature (basis units).
 * square(ctx, s): the supplied square-coherence witness for a 2-cell s
 * (NULL: absent). Admission on a cell checks, on every base square, that the
 * witness is supplied and that T(right)∘T(bottom) = T(top)∘T(left) on every
 * basis unit; without it the cell carries no flat interpretation. */
typedef ModId (*ChTransport)(void *ctx, CellId edge, ModId m, bool inverse);
typedef bool (*ChSquare)(void *ctx, CellId square);
typedef struct LocalSystem LocalSystem;
LocalSystem *localsys_new(ChTransport T, ChSquare square, void *ctx, size_t nunits, const uint64_t *units);
bool localsys_admit(LocalSystem *ls, CellId x, const char **why);
void localsys_free(LocalSystem *ls);

/* ---- cochains and chain maps ---- */
typedef int (*ChAct)(void *ctx, CellId x, ModId *out);   /* 0: value; 1: still being computed (the request suspends) */
typedef struct Cochain Cochain;
Cochain *cochain_gen(size_t degree, uint64_t signature, ChAct act, void *ctx);
Cochain *cochain_cob(Cochain *a, LocalSystem *ls);       /* COB(a): c ↦ PAIR(a, BOUNDARY(c)); with ls, the twisted differential */
size_t cochain_degree(const Cochain *a);
typedef ChainId (*ChMapAct)(void *ctx, CellId x);
typedef struct ChainMapT ChainMapT;
ChainMapT *chainmap_new(ChMapAct act, void *ctx, int degree_shift);
bool chainmap_admit(ChainMapT *F, CellId x, const char **why);   /* the boundary witness F∂x = ∂Fx on a generator (memoized) */
Cochain *cochain_pull(Cochain *a, ChainMapT *F);         /* f*a = a∘F */

/* ---- operations: one bounded unit per step, run as evaluator jobs ---- */
typedef struct ChOp ChOp;
enum { CH_RUNNING = 0, CH_DONE, CH_PENDING };
ChOp *op_boundary(ChainId c, LocalSystem *ls);           /* BOUNDARY: result ChainId */
ChOp *op_pair(Cochain *a, ChainId c);                    /* PAIR: result ModId */
ChOp *op_map_chain(ChainMapT *F, ChainId c);             /* MAP_CHAIN: result ChainId */
ChOp *op_law_d2(CellId x);                               /* the d²=0 law instantiated at x: result 1 when every pair cancels */
int chop_step(ChOp *o);
uint64_t chop_result(const ChOp *o);
size_t chop_units(const ChOp *o);
void chop_free(ChOp *o);
uint64_t ch_run(ChOp *o);                                /* through eval_job, one unit per job; frees o */
#define CH_TAG 0x4C00                                     /* EvalTaskInfo.tag of chain jobs */

/* convenience (each is one ch_run) */
ChainId chain_boundary(ChainId c, LocalSystem *ls);
ModId chain_pair(Cochain *a, ChainId c);
ChainId chain_map(ChainMapT *F, ChainId c);
/* READ_DEFECT(a,h): PAIR(a, BOUNDARY(h)) and PAIR(COB(a), h); *agree reports the Stokes equation */
ModId read_defect(Cochain *a, ChainId h, bool *agree);

/* ---- the shared law witness ---- */
typedef struct { size_t degree; uint64_t pairs; uint64_t instances; } LawD2;
LawD2 law_d2_record(size_t n);                           /* the shared record of degree n (4·C(n,2) cancelling pairs) */

/* ---- cycles, boundaries, relative chains, gluing, images ---- */
bool chain_is_cycle(ChainId z);
typedef struct { ChainId z, h; } BoundaryWitness;        /* a boundary comes with its higher chain */
bool boundary_witness(ChainId z, ChainId h, BoundaryWitness *out, const char **why);
typedef bool (*ChIn)(void *ctx, CellId x);
typedef struct { ChainId chain, relative, absolute_boundary, relative_boundary; } RelativeView;
RelativeView relative_view(ChainId c, ChIn in_A, void *ctx);   /* C(X)/C(A): representative off A; the absolute boundary retained */
ChainId chain_glue(ChainId h1, ChainId h2, ChainId j, const char **why);   /* [H1 ∪_J H2] = H1 + H2 − J; J must occur in both */
typedef CellId (*ChCellMap)(void *ctx, CellId x);
ChainId chain_pushforward(ChainId c, ChCellMap f, void *ctx);  /* additive multiplicities */
size_t chain_support_image(ChainId c, ChCellMap f, void *ctx, CellId **out);   /* Boolean direct image, deduplicated */

/* ---- realization (§10 PUBLISH_REALIZATION) ---- */
typedef bool (*ChOccurred)(void *ctx, CellId x);         /* an already accepted occurrence */
typedef struct { CellId typed; ChainId image, operational_boundary; size_t nlinks; } Realization;
bool publish_realization(CellId typed, ChainMapT *F, ChainId operational_boundary, ChOccurred occurred, void *ctx, Realization *out, const char **why);

typedef struct { uint64_t cells, chains, mods, ops, units, memo_hits, law_pairs; } ChainStats;
ChainStats chain_stats(void);
#endif

/* compiler.h — identity-to-agent compiler (§39–§48).
 *
 * Checked diagram declarations, generated realization maps (singleton
 * contraction and expansion), identity / equivalence / residual / cut /
 * contractible-fibre transforms with structural certificates, the
 * TRANSFORM_CALL instruction and its exact application wiring.
 *
 * Everything the compiler emits is annotated core syntax built with the
 * existing constructors and the fixed library templates (§40); nothing here
 * evaluates. Generated formal identities are anchored in the owning
 * diagram / template identity, a compilation role and a slot, so a
 * recompilation produces identical references (the certificate check).
 */
#ifndef CUBICAL_COMPILER_H
#define CUBICAL_COMPILER_H

#include "check.h"
#include "lib.h"

typedef uint64_t DiagramId;
typedef uint64_t TransformId;

/* one node of a finite construction diagram: value variable x : A (A : U_level),
 * witness variable e : Path_A(t, x), defining term t : A (§59.1: every type
 * position carries its universe level) */
typedef struct { uint64_t node_id; TermVarId x, e; RefId A; uint64_t level; RefId t; } DiagNode;

/* ---- diagrams (§39) ---- */
/* an ordinary diagram with output type B : U_lB and output term o */
DiagramId diagram_declare(ContextId params, size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o);
/* a residual description (§44): the telescope ends in the terminal type Z : U_lZ */
DiagramId residual_declare(ContextId params, size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ);
/* typed telescope check under the required face */
CheckStatus diagram_validate(DiagramId d, FaceId required, const char **reason);
TermVarId diagram_output_param(DiagramId d);       /* the diagram's own y : B (0 for a residual) */
RefId diagram_realization(DiagramId d);            /* Real(C, Γ, y_d) = R_0 */
MapId diagram_canonical_subst(DiagramId d);        /* ν */
RefId diagram_canonical(DiagramId d);              /* C = o[ν] (a residual: Z[ν]) */
/* the emitted maps (§41), cached per diagram and role:
 *   collapse: formal r : R_0            ↦ Path_B(C, y_d)  (residual: Z[ν])
 *   expand:   formal q : Path_B(C, y_d) ↦ R_0 */
RefId diagram_collapse(DiagramId d, TermVarId *r_slot);
RefId diagram_expand(DiagramId d, TermVarId *q_slot);

/* ---- declarations and compiled records (§39, §42) ---- */
typedef enum { EV_IDENTITY = 1, EV_EQUIVALENCE, EV_RESIDUAL_EQUIVALENCE, EV_CUT, EV_CONTRACTIBLE_FIBRE } EvidenceKind;

typedef struct {
    uint64_t id;              /* stable source identity */
    ContextId parameters;     /* Γ */
    FaceId required_face;     /* φ */
    RefId result_type;        /* B */
    uint64_t result_level;    /* B : U_result_level */
    DiagramId left, right;
    RefId evidence;           /* p : Path_B(C_left, C_right) */
} IdentityDecl;

typedef struct {
    TransformId id;
    ContextId parameters;     /* identity: Γ, y */
    FaceId required_face;
    RefId domain, codomain;
    uint64_t domain_level, codomain_level;   /* TypeAt levels (§59.1) */
    RefId generic_call[2];    /* §59.3: the fixed call origin per orientation, over the parameters and the argument slot */
    TermVarId forward_argument_slot, reverse_argument_slot;
    RefId forward_body, reverse_body;
    EvidenceKind evidence_kind;
    uint64_t certificate;
    uint64_t identity_template;   /* GraphPairTemplate id, identity declarations only */
} CompiledTransform;

/* the generic proof-parameterized template of an ordered diagram pair (§42, §45) */
typedef struct {
    uint64_t id; DiagramId left, right;
    ContextId parameters;     /* Γ, y */
    TermVarId y, P, r_left, r_right;
    RefId domain, codomain, forward, reverse;   /* free in P */
} GraphPairTemplate;

/* each returns the published transform id, or 0 with *reason */
TransformId compile_identity(const IdentityDecl *d, const char **reason);
TransformId compile_equivalence(ContextId params, FaceId req, RefId X, uint64_t lX, RefId Y, uint64_t lY, RefId e, const char **reason);
TransformId compile_residual_equivalence(ContextId params, FaceId req, DiagramId L, DiagramId R, RefId e, const char **reason);
TransformId compile_cut(ContextId params, FaceId req, RefId B, uint64_t lB, RefId C, RefId D, const char **reason);
TransformId compile_contractible_fibre(ContextId params, FaceId req, RefId B, uint64_t lB, RefId R, RefId k, const char **reason);

const CompiledTransform *transform_get(TransformId id);      /* NULL when unknown */
const GraphPairTemplate *graph_pair_get(uint64_t id);
size_t transform_count(void);
/* reconstruct the derivation the certificate records and compare it exactly
 * with the registered record (§39) */
CheckStatus certificate_verify(TransformId id, const char **reason);

/* ---- invocation (§43, §59.3) ---- */
/* TRANSFORM_CALL(id, dir, σ, a) = reindex(generic_call[id,dir], σ + slot ↦ a):
 * one fixed call origin per transform and orientation */
RefId mk_transform_call(TransformId id, int dir, MapId sigma, RefId a);
void compiler_families_init(void);   /* tcall.decode (registered by eval_init) */
bool compiler_decode_call(const Head *h, uint64_t *id, int *dir, MapId *sigma, RefId *a);
/* the fixed template body and its argument slot for an orientation */
bool compiler_template(uint64_t id, int dir, RefId *body, TermVarId *slot);
/* an external application pair: APPLY_TRANSFORM(id,dir,σ) -- REF(a), result to b */
enum { DIR_FORWARD = 0, DIR_REVERSE = 1 };

void compiler_init(void);
void compiler_free(void);

#endif

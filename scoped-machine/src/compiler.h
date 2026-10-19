/* compiler.h — the identity compiler as an input adapter (PLAN §9.3, HANDOFF §84.1).
 *
 * A source diagram declaration (§39) is exported as an ordinary Diagram
 * value (runtime.h) by the right fold of the node constructor ending in
 * zero; a residual description as a residual presentation. An identity,
 * equivalence, residual equivalence, cut or contractible-fibre declaration
 * is validated with diagnostics and exported as an Action: an ordinary
 * Maps(domain, codomain) value — the generic action of §83.4 (or the §83.5
 * schema maps) instantiated at the declaration's data. Invocation is the
 * ordinary application of the forward or reverse field. There is no
 * transform registry, no call instruction and no certificate: execution and
 * checking see only ordinary terms. Exports are memoized by their complete
 * structural key (no environment version).
 */
#ifndef CUBICAL_COMPILER_H
#define CUBICAL_COMPILER_H

#include "check.h"
#include "lib.h"
#include "runtime.h"
#include "proof.h"

typedef uint64_t DiagramId;

/* one node of a finite construction diagram: value variable x : A (A : U_level),
 * witness variable e : Path_A(t, x), defining term t : A */
typedef struct { uint64_t node_id; TermVarId x, e; RefId A; uint64_t level; RefId t; } DiagNode;

/* ---- diagrams (§39) and their exported values ---- */
DiagramId diagram_declare(ContextId params, size_t n, const DiagNode *nodes, RefId B, uint64_t lB, RefId o);
DiagramId residual_declare(ContextId params, size_t n, const DiagNode *nodes, RefId Z, uint64_t lZ);
/* the declaration checks (diagnostics); they are the signature checks of the fold */
CheckStatus diagram_validate(DiagramId d, FaceId required, const char **reason);
RefId diagram_value(DiagramId d);              /* Diagram_{lB, r}(B) (residual: Res_{lZ, r}) over the parameters */
RefId diagram_value_type(DiagramId d);
uint64_t diagram_level(DiagramId d);           /* r: the realization level */
TermVarId diagram_output_param(DiagramId d);   /* y : B (0 for a residual) */
RefId diagram_realization(DiagramId d);        /* R(y) (residual: X) */
RefId diagram_canonical(DiagramId d);          /* o[ν] (residual: Z[ν]); fst of the value converts to it */
/* the value's maps at y, applied to keyed slots:
 *   collapse: r : R(y) ↦ c(r) : Path_B(C, y)   (residual: X → Z)
 *   expand:   q : Path_B(C, y) ↦ d(q) : R(y) */
RefId diagram_collapse(DiagramId d, TermVarId *r_slot);
RefId diagram_expand(DiagramId d, TermVarId *q_slot);

/* ---- declarations and their actions ---- */
typedef enum { EV_IDENTITY = 1, EV_EQUIVALENCE, EV_RESIDUAL_EQUIVALENCE, EV_CUT, EV_CONTRACTIBLE_FIBRE } EvidenceKind;

typedef struct {
    uint64_t id;              /* source identity (provenance only) */
    ContextId parameters;     /* Γ */
    FaceId required_face;     /* φ */
    RefId result_type;        /* B */
    uint64_t result_level;    /* B : U_result_level */
    DiagramId left, right;
    RefId evidence;           /* p : Path_B(C_left, C_right) */
} IdentityDecl;

typedef struct {
    EvidenceKind kind;
    ContextId parameters;     /* Γ (identity: Γ, y) */
    FaceId required_face;
    TermVarId y;              /* identity: the output point; 0 otherwise */
    RefId domain, codomain;
    uint64_t domain_level, codomain_level;
    RefId maps;               /* : Maps(domain, codomain), an ordinary value over the parameters:
                                 the recipe's open body at the declaration's data */
    RefId applied;            /* the closed recipe applied to the same data (β-equal to maps);
                                 its typing evaluates nothing, so it carries the judgment */
    RefId evidence, evidence_type;   /* the declaration's evidence (0 for a cut) */
} Action;

/* each validates and fills *out; CK_VALID on success, otherwise *reason */
CheckStatus compile_identity(const IdentityDecl *d, Action *out, const char **reason);
CheckStatus compile_equivalence(ContextId params, FaceId req, RefId X, uint64_t lX, RefId Y, uint64_t lY, RefId e, Action *out, const char **reason);
CheckStatus compile_residual_equivalence(ContextId params, FaceId req, DiagramId L, DiagramId R, RefId e, Action *out, const char **reason);
CheckStatus compile_cut(ContextId params, FaceId req, RefId B, uint64_t lB, RefId C, RefId D, Action *out, const char **reason);
CheckStatus compile_contractible_fibre(ContextId params, FaceId req, RefId B, uint64_t lB, RefId R, RefId k, Action *out, const char **reason);

enum { DIR_FORWARD = 0, DIR_REVERSE = 1 };
/* the forward (c) or reverse (d) map of the action as a function value */
RefId action_function(const Action *a, int dir);
/* app(action_function(a, dir)[σ], arg): σ maps the parameters into the target */
RefId action_call(const Action *a, int dir, MapId sigma, RefId arg);

/* §88.5: mathematical use of an action is the proof-use judgment of its
 * complete value (the applied recipe: the generic construction and every
 * datum, the evidence included) at Maps(domain, codomain) */
ProofUse action_proof_use(const Action *a);

void compiler_init(void);
void compiler_free(void);

#endif

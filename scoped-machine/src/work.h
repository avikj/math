/* work.h — identity-execution accounting and cost refinement (§§60–71 as
 * disposed by §73).
 *
 * Records over the accepted machine: work identities (producer keys,
 * consumer occurrences, primitive work occurrences, identity applications),
 * demand closure with ready-key cuts (§60), the finite resource algebra
 * (§61), typed specialization with Boolean direct image (§62), contextual
 * cost differences (§63), supplied geodesic certificates (§64), typed plan
 * boundaries / realizations / connectors / expressions / cost models (§66,
 * §67), the shared positive formula DAG with constructor simplifications,
 * stable atom order and syntactic restriction (§68.1), realization
 * reconstruction from a supplied support (§68.3), verification of supplied
 * lower-bound proof DAGs and upper witnesses (§69.1, §69.4), Must-factoring,
 * disjoint-support decomposition, the displayed shared-choice equality and
 * scoped selection schemas (§70), and the bounded continuation-frame engine
 * with the fine work ledger (§65, §71).
 *
 * Nothing here searches: there is no cofactor solver, no frontier, no
 * incumbent. Every operation is an explicit request over existing checked
 * records, runs as bounded frames of an operation handle, and is counted.
 * No operation changes the recipe of an ordinary evaluation key; a
 * realization is exposed through its existing checked reference.
 */
#ifndef CUBICAL_WORK_H
#define CUBICAL_WORK_H

#include "xcount.h"
#include "compiler.h"

typedef uint64_t AtomId, SetId, FormulaId, ExprId, BoundaryId, PlanId, ConnectorId, ModelId, ProblemId,
    RealizationId, ProofId, CertId, FamilyId, SchemaId, GeoId, DGraphId, DemandId, WorkSetId, CostDiffId, AtomMapId, OpId;

/* ---- costs: exact naturals and a distinct INFINITY (§68.2, §69.1; BOUNDS-COMPLETION §2) ----
 * A finite cost is a Nat (nat.h: immediate below 2^63, else a canonical limb
 * record); COST_INF is the reserved non-Nat word. There is no finite ceiling.
 * Equality is word equality; order is cost_cmp (never C `<` on handles). */
#include "nat.h"
typedef uint64_t Cost;
#define COST_INF UINT64_MAX
static inline bool cost_finite(Cost c) { return c != COST_INF; }
static inline int cost_cmp(Cost a, Cost b) { if (a == b) return 0; if (a == COST_INF) return 1; if (b == COST_INF) return -1; return nat_compare(a, b); }
static inline Cost cost_sum(Cost a, Cost b) { return a == COST_INF || b == COST_INF ? COST_INF : nat_add(a, b); }   /* INFINITY absorbs */

/* ---- work identities (§60.1, §62.1) ---- */
typedef enum {
    WK_PRODUCER = 1,   /* (ref, projected face, env version): an evaluator key */
    WK_REQUEST,        /* (owner producer or 0, slot, requested producer): one consumer occurrence's REQUEST */
    WK_DELIVER,        /* the same occurrence's DELIVER */
    WK_PUB,            /* (producer): its publication */
    WK_EVAL,           /* (producer, ordinal): one of its frame steps */
    WK_APPLY,          /* (transform, dir, σ, argument, receiving producer, ordinal): one identity application (§73.3) */
    WK_SLOT,           /* (index): a scoped selection schema parameter (§70.4) */
    WK_NAMED           /* (name words): a host control atom named by the caller (algebra tests, §67.2) */
} AtomKind;
AtomId atom_producer(RefId t, FaceId chi);                      /* interned key at the current environment */
AtomId atom_request(AtomId owner, uint64_t slot, AtomId child);
AtomId atom_deliver(AtomId owner, uint64_t slot, AtomId child);
AtomId atom_pub(AtomId producer);
AtomId atom_eval(AtomId producer, uint64_t ordinal);
AtomId atom_apply(uint64_t transform, int dir, MapId sigma, RefId arg, AtomId receiver, uint64_t ordinal);
AtomId atom_slot(uint64_t index);
AtomId atom_named(uint64_t name);
AtomKind atom_kind(AtomId a);
const uint64_t *atom_words(AtomId a, size_t *n);                 /* [kind, operands...] */

/* ---- finite atom sets (sorted, interned) ---- */
SetId set_make(size_t n, const AtomId *atoms);                   /* sorts and deduplicates (counted) */
size_t set_size(SetId s);
const AtomId *set_atoms(SetId s, size_t *n);
bool set_has(SetId s, AtomId a);
SetId set_empty(void);

/* ---- the positive formula DAG (§67.2, §68.1) ---- */
typedef enum { FM_ZERO = 1, FM_ONE, FM_ATOM, FM_AND, FM_OR } FormulaTag;
FormulaId formula_zero(void);
FormulaId formula_one(void);
FormulaTag formula_tag(FormulaId f);
AtomId formula_atom_of(FormulaId f);
FormulaId formula_left(FormulaId f);
FormulaId formula_right(FormulaId f);
/* synchronous constructors (each runs its framed operation to completion) */
FormulaId formula_atom(AtomId a);
FormulaId formula_and(FormulaId l, FormulaId r);
FormulaId formula_or(FormulaId l, FormulaId r);
FormulaId formula_restrict(FormulaId f, AtomId e, int bit);      /* syntactic cofactor */
FormulaId formula_subst(FormulaId f, SetId m, int bit);          /* F[M := bit] */
SetId formula_support(FormulaId f);
SetId formula_must(FormulaId f);                                 /* 0 for ZERO (Must is defined on nonzero formulas) */

/* ---- typed plan records (§66, §67.1) ---- */
/* A boundary: admitted environment/session, context and face, input
 * references, result type and level, retained continuation evidence. */
BoundaryId boundary_make(ContextId ctx, FaceId face, size_t ninputs, const RefId *inputs, RefId type, uint64_t level, RefId continuation);
/* A checked realization at a boundary: r : type under (ctx, face) is
 * checked at creation; evidence connects r to the requested observation
 * (0 when r is the requested reference itself); work is its finite work set. */
PlanId plan_make(BoundaryId b, RefId r, RefId evidence, size_t nwork, const AtomId *work, const char **why);   /* work: ordered (anchors the atom order, §68.1) */
RefId plan_reference(PlanId p);
RefId plan_evidence(PlanId p);
SetId plan_work(PlanId p);
BoundaryId plan_boundary(PlanId p);
/* A connector: certified compatible composition left × right → result,
 * with its own work set and connecting evidence (a compiled transform or a
 * checked reference). work = 0 (no set supplied) and absent evidence are
 * both rejected at preparation. */
ConnectorId connector_make(BoundaryId left, BoundaryId right, BoundaryId result, TransformId transform, RefId evidence, size_t nwork, const AtomId *work);   /* work == NULL: no work set supplied (rejected at preparation) */
/* prepared expression nodes */
ExprId expr_empty(BoundaryId b);
ExprId expr_plan(PlanId p);
ExprId expr_alt(ExprId e, ExprId f);
ExprId expr_join(ExprId e, ExprId f, ConnectorId g);
typedef enum { EX_EMPTY = 1, EX_PLAN, EX_ALT, EX_JOIN } ExprTag;
ExprTag expr_tag(ExprId e);
BoundaryId expr_boundary(ExprId e);                               /* 0 when not well-formed */
/* specialization of a plan's typed records along σ (§62, §68.4): reindexes
 * the realization, evidence and boundary, re-checks the realization, and
 * specializes its work set by Boolean direct image */
PlanId plan_specialize(PlanId p, MapId sigma, ContextId target, FaceId target_face, const char **why);   /* σ : (target, target_face) → the plan's boundary is checked first */

/* ---- cost models (§66) ---- */
typedef struct { Cost producer, request, deliver, pub, eval, apply, slot, named; } KindWeights;
/* a model: weights per atom kind, overrides per atom, the admitted
 * completed-work set K, and an identity word naming the model */
ModelId model_make(uint64_t name, KindWeights w, SetId completed);
ModelId model_with_weight(ModelId m, AtomId a, Cost w);           /* a new model (different identity) with one override */
ModelId model_with_completed(ModelId m, SetId completed);
Cost model_weight(ModelId m, AtomId a);
SetId model_completed(ModelId m);
Cost cost_add(Cost a, Cost b, bool *overflow);                   /* checked; INF absorbs */

/* ---- demand graphs and closure (§60) ---- */
/* a producer graph: nodes (producer atom, steps, ordered occurrences) */
DGraphId dgraph_new(void);
void dgraph_add_producer(DGraphId g, AtomId producer, uint64_t steps);
void dgraph_add_occurrence(DGraphId g, AtomId owner, AtomId child);   /* slot = ordinal among the owner's occurrences */
void dgraph_add_apply(DGraphId g, AtomId receiver, uint64_t transform, int dir, MapId sigma, RefId arg);
void dgraph_mark_alias(DGraphId g, AtomId producer);                  /* an alias publication (§76.3): no PUB, no steps */
void dgraph_add_root(DGraphId g, AtomId root);                        /* a root consumer occurrence (owner 0) */
/* the graph of the actual run so far: every evaluator entry is a producer
 * with its recorded occurrences and frame steps; root/external requests are
 * root occurrences; identity applications come from the net trace */
DGraphId dgraph_from_trace(void);
/* the same with root occurrences restricted to those requested at or after
 * index first_root of the evaluator's root list (a run's own roots) */
DGraphId dgraph_from_trace_since(size_t first_root);
size_t dgraph_roots(DGraphId g, const AtomId **out);
/* the quiescent initial snapshot K of a run: every key READY now (§60.2) */
SetId work_ready_snapshot(void);
/* demand closure D_P(R, K): producers that execute, and every consumer
 * occurrence (root occurrences and Use_P of each demanded producer) */
typedef struct { AtomId owner; uint64_t slot; AtomId child; } Occurrence;
DemandId demand_closure(DGraphId g, SetId roots, SetId ready);
size_t demand_producers(DemandId d, const AtomId **out);
size_t demand_occurrences(DemandId d, const Occurrence **out);
/* complete work extraction (§60.3): REQUEST+DELIVER per occurrence, PUB +
 * EVAL steps per demanded producer, identity applications received by a
 * demanded producer */
WorkSetId work_extract(DemandId d);
SetId workset_atoms(WorkSetId w);
typedef struct { size_t request, deliver, pub, eval, apply; } WorkCounts;
WorkCounts workset_counts(WorkSetId w);

/* ---- specialization and the Boolean direct image (§62) ---- */
SetId set_specialize(SetId s, MapId sigma, const char **why);    /* s_!(A); 0 with *why when a specialized occurrence is invalid */
FormulaId formula_specialize(FormulaId f, MapId sigma, const char **why);
SetId set_union(SetId a, SetId b);
SetId set_inter(SetId a, SetId b);
SetId set_diff(SetId a, SetId b);
bool set_subset(SetId a, SetId b);
bool set_disjoint(SetId a, SetId b);
Cost set_weight(SetId s, ModelId m, bool *overflow);

/* ---- the finite resource algebra (§61) ---- */
FamilyId family_make(size_t n, const SetId *sets);               /* N: duplicates and strict supersets removed */
size_t family_sets(FamilyId f, const SetId **out);
FamilyId family_plus(FamilyId a, FamilyId b);                     /* ⊕ */
FamilyId family_times(FamilyId a, FamilyId b);                    /* ⊗ */
FamilyId family_zero(void);                                       /* 0 = empty family */
FamilyId family_one(void);                                        /* 1 = {∅} */
FamilyId formula_antichain(FormulaId f);                          /* the semantic normal form of F (counted expansion) */
bool family_dominates(FamilyId a, FamilyId b);                    /* ∀B∈b ∃A∈a: A ⊆ B (§61.3) */
Cost family_residual(FamilyId a, SetId k, ModelId m);             /* f_A(K) */
FamilyId family_specialize(FamilyId a, MapId sigma, const char **why);

/* ---- contextual cost differences (§63) ---- */
/* ε = cost(A\K) − cost(B\K) for the two supplied supports from the same
 * completed context K, and the overlap-masked difference against the
 * continuation support C; both source sets, K, C, the model and the
 * environment snapshot are retained in the record */
CostDiffId costdiff_make(SetId a, SetId b, SetId k, SetId c, ModelId m);
int64_t costdiff_epsilon(CostDiffId d);                            /* compatibility: INT64_MIN when not representable in int64_t (use the exact readers) */
int64_t costdiff_masked(CostDiffId d);
NatDiff costdiff_epsilon_exact(CostDiffId d);                      /* exact signed difference: sign and Nat magnitude */
NatDiff costdiff_masked_exact(CostDiffId d);
bool costdiff_current(CostDiffId d);                               /* its environment/session snapshot is the current one */

/* ---- prepared problems (§67, §68.1) ---- */
/* validates the expression (boundaries, connectors, witnesses), fixes the
 * atom order by first occurrence in the ordered traversal, builds F and
 * F_K = F[e := 1 for e ∈ K]. 0 with *why when invalid. */
ProblemId problem_prepare(ExprId e, ModelId m, const char **why);
FormulaId problem_formula(ProblemId p);                            /* F */
FormulaId problem_residual(ProblemId p);                           /* F_K */
size_t problem_order(ProblemId p, const AtomId **out);             /* atoms in their anchored order */
BoundaryId problem_boundary(ProblemId p);
ModelId problem_model(ProblemId p);
ExprId problem_expr(ProblemId p);
bool problem_current(ProblemId p);                                 /* session and environment unchanged since preparation */
/* §88.4: the proof-use boundary at preparation. Every connecting evidence
 * (a plan's continuation evidence, a connector's transform certificate or
 * checked reference) is audited by proof_use (proof.h). CORE and ASSUMED
 * uses prepare; the opaque symbols every ASSUMED use depends on are recorded
 * in the problem as its explicit hypotheses. PENDING, INVALID and UNRESOLVED
 * uses reject preparation with the audit's diagnostic: a pending audit is
 * never treated as a refutation, only as a missing mathematical witness. */
size_t problem_assumptions(ProblemId p, const uint64_t **out);     /* sorted opaque symbols the problem's evidence uses depend on */
bool problem_core(ProblemId p);                                    /* every evidence use audited CORE (no hypotheses) */

/* ---- realization reconstruction from a supplied support (§68.3) ---- */
RealizationId realize(ProblemId p, SetId support, const char **why);   /* 0 with *why when S ∪ K does not satisfy the expression */
size_t realization_plans(RealizationId r, const PlanId **out);
size_t realization_connectors(RealizationId r, const ConnectorId **out);
SetId realization_work(RealizationId r);                           /* W(p) ⊆ S ∪ K */
Cost realization_cost(RealizationId r);                            /* residual cost Σ_{W(p)\K} w */
RefId realization_reference(RealizationId r, RefId *evidence);     /* the checked reference of its first plan; executes through the ordinary machine */

/* ---- lower-bound proofs and certificates (§69.1, §69.4, §70) ---- */
typedef enum { PR_TRIVIAL = 1, PR_FALSE, PR_MANDATORY, PR_SPLIT, PR_FACTOR, PR_DISJOINT_AND, PR_OR_BOUND, PR_WEAKEN, PR_EQUAL } ProofRule;
typedef enum { EQ_SHARED_OR = 1 } EqualityRule;                  /* (X∨Y)∧(X∨Z) = X∨(Y∧Z), §70.3 */
/* constructors record the claimed value; the checker recomputes it */
ProofId proof_trivial(FormulaId f);
ProofId proof_false(void);
ProofId proof_mandatory(FormulaId f, SetId m, ModelId model);
ProofId proof_split(FormulaId f, AtomId e, ProofId p0, ProofId p1, ModelId model);
ProofId proof_factor(FormulaId f, SetId m, ProofId p, ModelId model);
ProofId proof_disjoint_and(FormulaId f, FormulaId g, ProofId p, ProofId q);
ProofId proof_or_bound(FormulaId f, FormulaId g, ProofId p, ProofId q);
ProofId proof_weaken(ProofId p, Cost k);
ProofId proof_equal(FormulaId f, FormulaId g, ProofId p, EqualityRule rule);
/* a raw proof node with caller-supplied fields (for corrupted-certificate tests) */
ProofId proof_raw(ProofRule rule, FormulaId f, uint64_t aux, ProofId c1, ProofId c2, Cost value);
FormulaId proof_formula(ProofId p);
Cost proof_value(ProofId p);
/* a certificate: the prepared problem, a lower proof, an optional upper
 * witness (a realization) and the claimed bounds */
CertId certificate_make(ProblemId p, ProofId lower, RealizationId upper, Cost l, Cost u);
typedef enum { CERT_VALID = 1, CERT_INVALID, CERT_UNRESOLVED } CertStatus;
CertStatus certificate_check(ProblemId p, CertId c, const char **why);   /* synchronous; see op_check_certificate for bounded steps */
CertId certificate_problem_of(CertId c);

/* ---- the directly solvable fragment (§70) ---- */
/* Must-factoring, disjoint decomposition, the shared-choice equality and
 * OR bounds, bottom-up; each rule fires only when its checked premise holds.
 * A formula none of them reduces is retained unreduced (no enumeration). */
typedef struct { bool reduced; Cost value; ProofId lower; SetId attaining; FormulaId formula; } Reduction;
Reduction formula_reduce(FormulaId f, ModelId m, const char **why);
/* the same on a prepared problem's residual formula; when reduced, returns a
 * certificate whose upper witness is the realization reconstructed from the
 * attaining support (0 and *why when unreduced or when the support does not realize) */
CertId problem_reduce(ProblemId p, const char **why);

/* ---- scoped selection schemas (§70.4) ---- */
/* a schema: a formula over slot atoms, its proof over slot atoms and its
 * attaining slot set; instantiation substitutes actual atoms (possibly
 * identifying slots), rebuilds the proof and checks it against the prepared
 * problem, which re-establishes every guard (Must, disjointness, weights) */
SchemaId schema_make(size_t nslots, FormulaId formula, ProofId lower, SetId attaining);
AtomMapId atom_map_make(size_t n, const AtomId *from, const AtomId *to);
CertId schema_instantiate(SchemaId s, AtomMapId map, ProblemId p, const char **why);
FormulaId formula_map_atoms(FormulaId f, AtomMapId map);

/* ---- supplied geodesic certificates (§64.3) ---- */
GeoId geo_new(size_t nstates);
void geo_terminal(GeoId g, uint64_t state);
uint64_t geo_edge(GeoId g, uint64_t from, uint64_t to, Cost c);   /* returns the edge index */
void geo_value(GeoId g, uint64_t state, Cost v);
void geo_policy(GeoId g, uint64_t state, uint64_t edge);
void geo_rank(GeoId g, uint64_t state, uint64_t rank);             /* secondary well-founded rank (zero-cost steps) */
CertStatus geo_check(GeoId g, uint64_t root, Cost *value, const char **why);

/* ---- operation handles and bounded frames (§71, §73.3) ---- */
typedef enum { OP_RUNNING = 1, OP_COMPLETE, OP_RESOURCE_LIMIT, OP_INVALID } OpStatus;
typedef enum {
    FR_PREPARE_VISIT = 0, FR_VALIDATE_PREPARED_BOUNDARY, FR_FORMULA_VISIT, FR_FORMULA_INTERN_STEP, FR_COFACTOR_VISIT, FR_COFACTOR_REBUILD,
    FR_SUPPORT_CHUNK, FR_MUST_CHUNK, FR_COST_ADD_CHUNK, FR_COST_COMPARE_CHUNK, FR_CERTIFICATE_VISIT, FR_REALIZATION_VISIT,
    FR_ALLOCATE_CHUNK, FR_RELEASE_CHUNK, FR_TABLE_PROBE, FR_DEMAND_VISIT, FR_SPECIALIZE_VISIT, FR_FAMILY_CHUNK, FR_GEODESIC_VISIT,
    FR_PRODUCER_LOOKUP, FR_ALIAS_DELIVERY, FR_SHAPE_NODE, FR_DEPENDENCY_CHECK, FR_RECEIPT,   /* §81.1 */
    FR_PROOF_USE_AUDIT,            /* §88: one frame per audited evidence use at preparation */
    FR_SCHEDULE_STEP, FR_CYCLE_CHECK,   /* §94.2(3): one cone-path hop / one cycle-check hop per unit */
    FR_KERNEL_TRANSITION, FR_COUNT      /* §94: one fine step of a kernel frame stack (kframe.h) */
} FrameFamily;
typedef enum { PH_PREPARE = 0, PH_REWRITE, PH_CHECK, PH_COMMIT, PH_EXECUTE, PH_COUNT } Phase;
const char *frame_family_name(FrameFamily f);
/* constructors of framed operations (not started) */
OpId op_formula_and(FormulaId l, FormulaId r);
OpId op_formula_or(FormulaId l, FormulaId r);
OpId op_restrict(FormulaId f, AtomId e, int bit);
OpId op_support(FormulaId f);
OpId op_must(FormulaId f);
OpId op_set_weight(SetId s, ModelId m);
OpId op_demand(DGraphId g, SetId roots, SetId ready);
OpId op_extract(DemandId d);
OpId op_specialize_set(SetId s, MapId sigma);
OpId op_prepare(ExprId e, ModelId m);
OpId op_realize(ProblemId p, SetId support);
OpId op_check_certificate(ProblemId p, CertId c);
OpId op_reduce(FormulaId f, ModelId m);
OpId op_antichain(FormulaId f);
OpId op_geo_check(GeoId g, uint64_t root);
OpId op_proof_audit(ContextId G, FaceId phi, RefId e, RefId E);   /* EFFECT-AUTHORITY §3: the framed audit of e : E in Γ;φ */
int op_audit_verdict(OpId h, size_t *nassume, const uint64_t **assume);   /* -1 running, else a ProofUseStatus (proof.h); assumptions: the reached opaque symbols */
OpStatus op_step(OpId h, size_t budget);                            /* advances at most budget counted frames */
OpStatus op_status(OpId h);
uint64_t op_result(OpId h);
const char *op_diagnostic(OpId h);
uint64_t op_frames(OpId h);                                          /* frames this operation has executed */
void op_release(OpId h);                                             /* RELEASE_CHUNK frames, counted */

/* ---- the fine ledger (§65.1, §71.2) ---- */
typedef struct {
    uint64_t frames[FR_COUNT];        /* bounded frame steps by family */
    uint64_t by_phase[PH_COUNT];      /* the same steps by phase */
    uint64_t probes, word_compares, limb_ops, alloc_words, release_words;   /* components of the steps above */
    uint64_t memo_lookup, memo_hit, memo_deliver;
    uint64_t kernel_calls;            /* calls into the term/face/checker layers (reindex, validation, checking): charged as calls, their traversal is the kernel's own */
    EvalEvents exec_eval; EvalNetEvents exec_net;   /* the execute phase: the coarse event vector as a projection (§65.1) */
} WorkLedger;
WorkLedger work_ledger(void);        /* V23 R5: checked word projections of the exact ledger (fatal when a reading exceeds a word) */
/* V23 R5: the authoritative exact ledger (xcount.h): every family, phase and component count */
typedef struct {
    XSnap frames[FR_COUNT], by_phase[PH_COUNT];
    XSnap probes, word_compares, limb_ops, alloc_words, release_words, memo_lookup, memo_hit, memo_deliver, kernel_calls;
} WorkLedgerExact;
WorkLedgerExact work_ledger_exact(void);   /* the late contributions of closed scopes are folded into the readings work_ledger reports; this is the engine's own exact part */
void work_ledger_reset(void);
void work_set_phase(Phase p);
Phase work_phase(void);
uint64_t work_total_frames(void);
/* record the execution phase: the event deltas of an actual run */
void work_record_execution(EvalEvents before, EvalNetEvents nbefore, EvalEvents after, EvalNetEvents nafter);

void work_init(void);
void work_free(void);

#endif

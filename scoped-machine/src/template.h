/* template.h — fixed template programs and TVIEW references (§49, §51–§54).
 *
 * A template definition is a finite acyclic expression DAG over ordered
 * parameters (reference, interval, face, scope, universe level) whose
 * constructor occurrences are fixed nodes. TVIEW(node, environment) is the
 * third reference form: opening it interprets the node's finite field
 * recipes with the environment; reindexing it reindexes the environment and
 * executes no field program. Every constructor node's declared required face
 * is the `under` faces in force at the node; an instance's required face is
 * that strengthened by its images' requirements. */
#ifndef CUBICAL_TEMPLATE_H
#define CUBICAL_TEMPLATE_H

#include "scope.h"

typedef uint64_t ExprId, TDefId, TNodeId, TEnvId;

/* ---- definitions (registered once; the library of §52–§54 and Down) ---- */
typedef enum {
    TD_PATHCONST = 1, TD_REFL, TD_PAPPCONST, TD_REVERSE, TD_CONCAT, TD_FUN, TD_CONTR, TD_FIB, TD_EQUIV,
    TD_IDFUN, TD_EQUIVMAP, TD_EQUIVCONTR, TD_IDEQUIV, TD_FILL, TD_HCOMP, TD_COE, TD_EXTENDCONTR, TD_LINEEQUIV, TD_UA,
    TD_PICOMP, TD_SIGMACOMP, TD_PATHCOMP, TD_GLUECOMP, TD_UNIVERSECOMP, TD_DOWN, TD_COUNT
} TDefKind;
void templates_init(void);                      /* registers the library (idempotent per machine) */
void templates_free(void);

/* invoke a definition's root program: args in the definition's parameter
 * order (without κ, which is ⊤) */
TVal template_call(TDefKind def, size_t nargs, const TVal *args);

/* ---- TVIEW references ---- */
Tag tnode_tag(TNodeId Q);
TDefId tnode_def(TNodeId Q); uint64_t tnode_index(TNodeId Q);
size_t tnode_nfields(TNodeId Q); size_t tnode_nbinders(TNodeId Q);
/* the field kind / binder slot of a template node's field */
FieldKind tnode_field_kind(TNodeId Q, size_t k); BinderSlot tnode_field_slot(TNodeId Q, size_t k); Sort tnode_binder_sort(TNodeId Q, BinderSlot s);

/* checking support: the parameter signature of a definition, instantiated
 * by an environment. For a reference parameter the declared type; for a
 * scope parameter the expected telescope / result type / guard opened at
 * fresh locals keyed by `key`. */
typedef struct { PSort sort; size_t slot; uint64_t level; RefId type; FaceId guard; ScopeId sig; } ParamSig;
/* the retained parameter slots of t's node with their instantiated declared
 * types (reference parameters) or contextual signatures (scope parameters:
 * a scope whose locals are the expected telescope, whose body is the
 * expected result type, whose level and guard are the expected ones) */

/* ---- constructions (the one construction representation) ----
 * Every non-variable reference is TVIEW(node, environment). A construction
 * built by the term layer is a node whose field programs are constants
 * closed over (depth, slot) atoms: parameter k (the construction's typed free
 * boundary, dimensions first, then term variables in id order) is
 * bound_id(0, k), and the local of its binder bound_id(0, np). Its
 * environment gives every parameter's image (APPLY). Alpha-equivalent constructions
 * are therefore one node, and a construction is a template view.
 * Record: [0, np, tag, payload_e, levels_e, nf, (kind, slot, CONST)*, nb,
 *          (sort, domain_field, s)*, required_e, declared_e, (sort, type_e, guard_e)*np] */
ExprId expr_const(PSort sort, uint64_t id);
ExprId expr_level(uint64_t n);
bool tnode_is_construction(TNodeId Q);
uint64_t tnode_const_payload(TNodeId Q);
uint64_t tnode_const_field(TNodeId Q, size_t k);                    /* closed constant of field k */
bool tview_is_construction(RefId t);
void template_families_init(void);
void template_call_env(TDefKind def, size_t nargs, const TVal *args, WordBuf *er, ExprId *root);   /* the environment record into er (to be interned by intern_sub) */
ExprId tnode_head_expr(TNodeId Q, int levels);
ExprId tnode_field_expr(TNodeId Q, size_t k);
bool expr_is_level(ExprId e); uint64_t expr_level_value(ExprId e);   /* a closed level/payload expression */
void tnode_template_binder(TNodeId Q, BinderSlot slot, FieldIndex field, uint64_t *env_slot, ExprId *body_e);                     /* a template node's payload / levels recipe (0 = none) */

#endif

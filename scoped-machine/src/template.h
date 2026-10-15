/* template.h — fixed template programs and TVIEW references (§49, §51–§54).
 *
 * A template definition is a finite acyclic expression DAG over ordered
 * parameters (reference, interval, face, scope, universe level) whose
 * constructor occurrences are fixed nodes. TVIEW(node, environment) is the
 * third reference form: opening it interprets the node's finite field
 * recipes with the environment; reindexing it reindexes the environment and
 * executes no field program. Parameter slot 0 of every definition is the
 * source typing face κ (§51.4); every constructor node's declared required
 * face is κ strengthened by the `under` faces in force at the node. */
#ifndef CUBICAL_TEMPLATE_H
#define CUBICAL_TEMPLATE_H

#include "scope.h"

typedef uint64_t ExprId, TDefId, TNodeId, TEnvId;
typedef enum { PS_REF = 1, PS_INTERVAL, PS_FACE, PS_SCOPE, PS_LEVEL } PSort;
typedef struct { PSort sort; uint64_t id; } TVal;   /* RefId / IntervalId / FaceId / ScopeId / level */

/* ---- definitions (registered once; the library of §52–§54 and Down) ---- */
typedef enum {
    TD_PATHCONST = 1, TD_REFL, TD_PAPPCONST, TD_REVERSE, TD_CONCAT, TD_FUN, TD_CONTR, TD_FIB, TD_EQUIV,
    TD_IDFUN, TD_EQUIVMAP, TD_EQUIVCONTR, TD_IDEQUIV, TD_FILL, TD_HCOMP, TD_COE, TD_EXTENDCONTR, TD_LINEEQUIV, TD_UA,
    TD_PICOMP, TD_SIGMACOMP, TD_PATHCOMP, TD_GLUECOMP, TD_UNIVERSECOMP, TD_DOWN, TD_COUNT
} TDefKind;
void templates_init(void);                      /* registers the library (idempotent per machine) */
void templates_free(void);

/* invoke a definition's root program: args in the definition's parameter
 * order (without κ; the current κ is taken from template_kappa) */
TVal template_call(TDefKind def, size_t nargs, const TVal *args);
/* the source typing face κ for constructions made on this thread (default ⊤) */
void template_set_kappa(FaceId kappa);
FaceId template_kappa(void);

/* ---- TVIEW references ---- */
RefId make_template_view(TNodeId Q, size_t n, const TVal *slots, const uint64_t *slot_index);   /* values by slot */
TNodeId tnode_of(RefId t);
TEnvId tenv_of(RefId t);
size_t tenv_size(TEnvId E);
TEnvId tenv_make(size_t n, const uint64_t *slots, const TVal *vals);   /* intern an environment (slot order as given) */
TEnvId tenv_reindex(TEnvId E, MapId sigma);                            /* componentwise (§55) */
RefId tenv_instantiate(TNodeId Q, TEnvId E);                           /* INSTANTIATE_TEMPLATE(Q) with TEMPLATE_ENV(E) */
void tenv_entry(TEnvId E, size_t k, uint64_t *slot, TVal *v);
Tag tnode_tag(TNodeId Q);
TDefId tnode_def(TNodeId Q); uint64_t tnode_index(TNodeId Q);
const char *tdef_name(TDefId d);
size_t tnode_nfields(TNodeId Q); size_t tnode_nbinders(TNodeId Q);
/* the field kind / binder slot of a template node's field */
FieldKind tnode_field_kind(TNodeId Q, size_t k); BinderSlot tnode_field_slot(TNodeId Q, size_t k); Sort tnode_binder_sort(TNodeId Q, BinderSlot s);
RefId tview_traverse(RefId t, const Trav *tv, unsigned depth);

/* checking support: the parameter signature of a definition, instantiated
 * by an environment. For a reference parameter the declared type; for a
 * scope parameter the expected telescope / result type / guard opened at
 * fresh locals keyed by `key`. */
typedef struct { PSort sort; size_t slot; uint64_t level; RefId type; FaceId guard; ScopeId sig; } ParamSig;
/* the retained parameter slots of t's node with their instantiated declared
 * types (reference parameters) or contextual signatures (scope parameters:
 * a scope whose locals are the expected telescope, whose body is the
 * expected result type, whose level and guard are the expected ones) */
size_t tnode_signature(RefId t, ParamSig *out, size_t max);
/* the program's declared result type instantiated by t's environment, when
 * t is the root node of its definition */
bool tnode_result(RefId t, RefId *type, uint64_t *level);

#endif

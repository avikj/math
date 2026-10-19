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

/* ---- constructions (the one construction representation) ----
 * Every non-variable reference is TVIEW(node, environment). A construction
 * built by the term layer is a node whose field programs are constants
 * closed over positional atoms: parameter k (the construction's typed free
 * boundary, dimensions first, then term variables in dependency order) is
 * obound_id(k), and the local of binder s is obound_id(np + s). Its
 * environment gives every parameter's image. Alpha-equivalent constructions
 * are therefore one node, and a construction is a template view.
 * Record: [0, np, tag, payload_e, levels_e, nf, (kind, slot, CONST)*, nb,
 *          (sort, domain_field, s)*, required_e, declared_e, (sort, type_e, guard_e)*np] */
ExprId expr_const(PSort sort, uint64_t id);
ExprId expr_level(uint64_t n);
TNodeId tnode_construction_intern(const uint64_t *words, size_t n);
RefId tnode_construction_view(TNodeId Q, const TVal *vals);        /* vals: the np parameter images */
bool tnode_is_construction(TNodeId Q);
size_t tnode_nparams(TNodeId Q);
void tnode_param(TNodeId Q, size_t k, PSort *sort, RefId *closed_type, FaceId *closed_guard);
uint64_t tnode_const_field(TNodeId Q, size_t k);                    /* closed constant of field k */
FaceId tnode_const_required(TNodeId Q);
FaceId tnode_const_declared(TNodeId Q);                              /* 0 = no annotation */
uint64_t tnode_const_payload(TNodeId Q);
uint64_t tnode_const_levels(TNodeId Q);
bool tview_is_construction(RefId t);
MapId cons_envmap(TEnvId E);                                         /* a construction environment as a substitution of its atoms (subst.c) */
MapId tview_env_map(RefId t);                                        /* atoms ↦ images */
FaceId tview_declared_required(RefId t);                             /* 0 = no annotation */
MapId tview_lifted_map(RefId owner, BinderSlot slot, uint64_t *fresh);
/* generic instance of a construction node: parameters at fresh names keyed
 * by (node, slot), declared at the instantiated closed types; decls has
 * tnode_nparams(Q) entries. *req receives the node's required face there. */
RefId tnode_generic(TNodeId Q, CtxDecl *decls, FaceId *req);
MapId tview_generic_map(RefId t);                                    /* generic names ↦ t's images */
void template_families_init(void);
void template_call_env(TDefKind def, size_t nargs, const TVal *args, FaceId kappa, WordBuf *er, ExprId *root);   /* the environment record into er (to be interned by intern_sub) */
ExprId tnode_head_expr(TNodeId Q, int levels);
ExprId tnode_field_expr(TNodeId Q, size_t k);
FieldIndex tnode_binder_domain(TNodeId Q, BinderSlot s);
bool expr_is_level(ExprId e); uint64_t expr_level_value(ExprId e);   /* a closed level/payload expression */
size_t tnode_binder_local(TNodeId Q, BinderSlot s);        /* the binder's local position (atom np+local) */
void tnode_template_binder(TNodeId Q, BinderSlot slot, FieldIndex field, uint64_t *env_slot, ExprId *body_e);                     /* a template node's payload / levels recipe (0 = none) */
void construct_bind_template_families(void);                                   /* interpretation families (registered by eval_init) */

#endif

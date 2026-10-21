/* template.h — construction nodes and TVIEW references (§49).
 *
 * TVIEW(node, environment) is the reference form of every construction:
 * opening it applies the environment to the node's closed fields;
 * reindexing it reindexes the environment. */
#ifndef CUBICAL_TEMPLATE_H
#define CUBICAL_TEMPLATE_H

#include "scope.h"

typedef uint64_t ExprId, TDefId, TNodeId, TEnvId;

/* ---- TVIEW references ---- */
Tag tnode_tag(TNodeId Q);
TDefId tnode_def(TNodeId Q);
size_t tnode_nfields(TNodeId Q);
/* the field kind / binder slot of a template node's field */
FieldKind tnode_field_kind(TNodeId Q, size_t k); BinderSlot tnode_field_slot(TNodeId Q, size_t k); Sort tnode_binder_sort(TNodeId Q, BinderSlot s);

/* ---- constructions (the one construction representation) ----
 * Every non-variable reference is TVIEW(node, environment). A construction
 * built by the term layer is a node whose field programs are constants
 * closed over (depth, slot) atoms: parameter k (the construction's typed free
 * boundary, dimensions first, then term variables in id order) is
 * bound_id(0, k), and the local of its binder bound_id(0, np). Its
 * environment gives every parameter's image (APPLY). Alpha-equivalent constructions
 * are therefore one node, and a construction is a template view.
 * Record: [0, np, tag, payload_e, levels_e, nf, (kind, slot, CONST)*, nb,
 *          (sort, domain_field, s)*, (sort, type_e)*np] */
ExprId expr_const(PSort sort, uint64_t id);
ExprId expr_level(uint64_t n);
void template_families_init(void);
ExprId tnode_head_expr(TNodeId Q, int levels);
ExprId tnode_field_expr(TNodeId Q, size_t k);
bool expr_is_level(ExprId e); uint64_t expr_level_value(ExprId e);   /* a closed level/payload expression */
void tnode_template_binder(TNodeId Q, BinderSlot slot, FieldIndex field, uint64_t *env_slot, ExprId *body_e);                     /* a template node's payload / levels recipe (0 = none) */

#endif

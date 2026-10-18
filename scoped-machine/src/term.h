/* term.h — simultaneous substitutions, origins, references, instantiated
 * support, binders and opening (§2, §6–9).
 *
 *   reference      = VIEW(origin, substitution) | VAR(x)
 *   specialization = reindex(reference, substitution)
 *
 * Nothing in this file evaluates. reindex traverses finite image records,
 * never the body of an origin.
 */
#ifndef CUBICAL_TERM_H
#define CUBICAL_TERM_H

#include "state.h"
#include "interval.h"
#include "face.h"

typedef enum {
    T_UNIVERSE = 1, T_PI, T_SIGMA, T_LAM, T_APP, T_PAIR, T_FST, T_SND,
    T_PATH, T_PLAM, T_PAPP, T_GLUE_TYPE, T_GLUE_INTRO, T_UNGLUE, T_COMP,
    T_SYSTEM, T_GLOBAL,
    T_TCALL            /* §43 TRANSFORM_CALL: an internal instruction origin, not an object-language datatype */
} Tag;

typedef enum { F_REF = 1, F_INTERVAL, F_FACE } FieldKind;
typedef enum { S_TERM = 1, S_DIM } Sort;

typedef struct {
    FieldKind kind;
    BinderSlot slot;      /* NO_SLOT when not under a binder */
    uint64_t id;          /* RefId / IntervalId / FaceId */
} Field;

typedef struct {
    Sort sort;
    uint64_t formal;      /* TermVarId or DimVarId bound in the origin */
    FieldIndex domain_field; /* term binders: field holding the domain type */
} Binder;

/* ---- universe levels (§59.1): explicit formation annotations ----
 * An origin record carries an interned pair of exact levels (nat.h); LEVEL_NONE marks an
 * annotation the source did not supply (the checker then infers it; the
 * fixed templates always supply theirs). */
#define LEVEL_NONE  UINT64_MAX              /* absent (the reserved non-Nat word) */
#define LEVELS_NONE UINT64_MAX              /* both absent; otherwise an interned pair handle */
uint64_t levels_pack(uint64_t m, uint64_t n);
uint64_t levels_first(uint64_t lv);
uint64_t levels_second(uint64_t lv);
uint64_t level_max(uint64_t a, uint64_t b);      /* LEVEL_NONE absorbs */
uint64_t level_succ(uint64_t a);
uint64_t origin_levels(OriginId c);
/* set the levels for the next annotated construction on this thread (the
 * template layer uses it around its constructor nodes) */
void term_levels_push(uint64_t m, uint64_t n);
void term_levels_pop(void);

/* ---- bound local occurrences (§50) ----
 * A local of a scope telescope is an interned (depth, slot) atom tagged in the
 * variable / dimension id space with the top bit set; it has no declaration
 * record and no free support. */
#define BOUND_BIT (1ULL << 61)           /* below the atom shift of the interval/face encodings */
uint64_t bound_id(size_t depth, size_t slot);
static inline bool is_bound_id(uint64_t id) { return (id & BOUND_BIT) != 0; }
size_t bound_depth(uint64_t id);
size_t bound_slot(uint64_t id);

const char *tag_name(Tag t);

/* ---- declarations ---- */
TermVarId declare_term(RefId type, FaceId required);
DimVarId declare_dim(void);
RefId term_var_type(TermVarId x);
FaceId term_var_required(TermVarId x);

/* ---- raw maps ---- */
typedef struct { Words t; Words d; } MapBuilder;   /* (key,image) pairs */
/* inside a frame step: room for nt term and nd dimension entries, so the entries that follow do not grow the builder */
#define KF_MAPB_RESERVE(b, nt, nd) do { KF_CALL(words_reserve, NULL, &(b)->t, 2 * (size_t)(nt)); KF_CALL(words_reserve, NULL, &(b)->d, 2 * (size_t)(nd)); } while (0)
void mapb_init(MapBuilder *b);
void mapb_term(MapBuilder *b, TermVarId x, RefId image);
void mapb_dim(MapBuilder *b, DimVarId i, IntervalId image);
MapId mapb_finish(MapBuilder *b);  /* sorts, rejects duplicate keys, drops identity entries, interns */
MapId map_identity(void);
bool map_is_identity(MapId m);
RefId map_term_image(MapId m, TermVarId x);          /* VAR(x) when absent */
IntervalId map_dim_image(MapId m, DimVarId i);       /* i when absent */
/* iterate entries */
size_t map_n_terms(MapId m); size_t map_n_dims(MapId m);
void map_term_entry(MapId m, size_t k, TermVarId *x, RefId *img);
void map_dim_entry(MapId m, size_t k, DimVarId *i, IntervalId *img);
MapId map_single_term(TermVarId x, RefId a);
MapId map_single_dim(DimVarId i, IntervalId r);
IntervalId iv_reindex(IntervalId r, MapId m);
FaceId fc_reindex(FaceId phi, MapId m);
MapId compose(MapId sigma, MapId tau);   /* apply sigma then tau */

/* ---- origins ---- */
/* Declared required face (§2 `required_face` annotation): origins created
 * while a scope is pushed carry the scope's face as part of their record;
 * their required face is the structural one strengthened by it. Library
 * clauses use it for constructions that are only typed on a guard. */
void term_require_push(FaceId phi);
void term_require_pop(void);
FaceId origin_declared_required(OriginId c);
OriginId origin_make(Tag tag, uint64_t payload, const Field *fields, size_t nfields,
                     const Binder *binders, size_t nbinders);
Tag origin_tag(OriginId c);
uint64_t origin_payload(OriginId c);
size_t origin_nfields(OriginId c);
Field origin_field(OriginId c, FieldIndex k);
size_t origin_nbinders(OriginId c);
Binder origin_binder(OriginId c, BinderSlot s);
VarSetId origin_ft(OriginId c);
DimSetId origin_fd(OriginId c);
FaceId origin_required(OriginId c);

/* ---- references ---- */
RefId ref_var(TermVarId x);
bool ref_is_var(RefId t);
/* TVIEW(template_node, environment) references (§49): the third reference
 * form; their operations live in the template layer */
bool ref_is_tview(RefId t);
Tag ref_tag(RefId t);                 /* the head tag of a non-variable reference (VIEW origin or TVIEW node) */
uint64_t ref_tnode(RefId t);
uint64_t ref_tenv(RefId t);
#define ref_intern_tview_PARAMS(X) X(uint64_t, node) X(uint64_t, env) X(DimSetId, support) X(VarSetId, fv) X(FaceId, required)
KF_PROTO(ref_intern_tview, RefId, ref_intern_tview_PARAMS);
RefId ref_intern_tview(uint64_t node, uint64_t env, DimSetId support, VarSetId fv, FaceId required);

TermVarId ref_var_id(RefId t);
OriginId ref_origin(RefId t);
MapId ref_map(RefId t);
DimSetId ref_support(RefId t);
VarSetId ref_freevars(RefId t);
FaceId ref_required(RefId t);
RefId make_view(OriginId c, MapId sigma);
RefId reindex(RefId t, MapId sigma);
RefId reindex1(RefId t, TermVarId x, RefId a);
RefId reindex_dim(RefId t, DimVarId i, IntervalId r);

/* ---- binders ---- */
TermVarId binder_term_var(RefId owner, BinderSlot slot, RefId type);
DimVarId binder_dim_var(RefId owner, BinderSlot slot);
/* Keyed fresh names for library definitions: deterministic per key. A key is
 * a typed tuple so that provenance can be compared up to renaming. */
typedef enum { KW_CONST = 0, KW_REF, KW_FACE, KW_INTERVAL, KW_DIM, KW_VAR, KW_NAT } KeyKind;
typedef struct { KeyKind kind; uint64_t v; } KeyWord;
#define nominal_var_PARAMS(X) X(const KeyWord *, key) X(size_t, n) X(uint64_t, prefix) X(Sort, sort) X(RefId, type) X(FaceId, req) X(bool, check)
#define binder_var_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(Sort, sort) X(RefId, type)
KF_PROTO(nominal_var, uint64_t, nominal_var_PARAMS);   /* a keyed variable (prefix: a leading constant key word, 0 = none); check: a reuse must agree on type and face */
KF_PROTO(binder_var, uint64_t, binder_var_PARAMS);     /* the variable of the binder (owner, slot) */
uint64_t nominal_var(const KeyWord *key, size_t n, uint64_t prefix, Sort sort, RefId type, FaceId req, bool check);
TermVarId fresh_term_keyed(const KeyWord *key, size_t n, RefId type);
TermVarId fresh_term_keyed_req(const KeyWord *key, size_t n, RefId type, FaceId required);   /* a partial formal */
DimVarId fresh_dim_keyed(const KeyWord *key, size_t n);
/* provenance of a generated name: nominal id (0 for an input name) */
uint64_t term_var_provenance(TermVarId x);
uint64_t dim_var_provenance(DimVarId i);
/* a nominal record: typed key words (kind,value pairs) */
const uint64_t *nominal_key(uint64_t nid, size_t *npairs);

/* the lifted map of section 8 for a binder of `owner`: sigma without the
 * formal's entry, then formal ↦ fresh. *fresh receives the minted name. */
MapId lifted_map(RefId owner, BinderSlot slot, uint64_t *fresh);

typedef struct TermOpen { TermVarId x; RefId type; RefId body; } TermOpen;
typedef struct DimOpen { DimVarId j; RefId body; } DimOpen;
TermOpen resolve_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field);
DimOpen resolve_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field);
RefId apply_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field, RefId a);
RefId apply_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field, IntervalId r);

/* ---- opening ---- */
typedef struct {
    FieldKind kind;
    bool is_binder;       /* field lives under a binder: use (owner, slot, index) */
    Sort sort;            /* binder sort when is_binder */
    BinderSlot slot;
    FieldIndex index;
    uint64_t id;          /* substituted RefId / IntervalId / FaceId when !is_binder */
} HField;

typedef struct Head {
    bool is_var;
    TermVarId var;
    Tag tag;
    uint64_t payload;
    uint64_t levels;      /* packed formation levels (§59.1) */
    RefId owner;
    OriginId origin;      /* raw views */
    MapId map;
    size_t n;
    HField *f;
} Head;

void open_ref(RefId t, Head *h);
void head_free(Head *h);
/* TVIEW operations (template.c) */
RefId tview_reindex(RefId t, MapId sigma);
Tag tnode_tag(uint64_t Q);           /* template.c */
void tview_open(RefId t, Head *h);
TermOpen tview_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field);
DimOpen tview_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field);

/* ---- occurrence contexts (§2) ----
 * A context is an ordered list of declarations DIM(i) or TERM(x, type) with
 * a face assumption. It is interned by structure and is not part of RefId.
 * An occurrence (reference, context) is valid when the context declares
 * every free dimension and every free term variable of the reference with
 * its declared type, and its assumption entails the reference's required
 * face. This is the structural check; `occurrence_validate` compares declared
 * types by identity, and the typed check with conversion is `src/check.c`
 * (§33 item 3, `observe_checked`). */
typedef struct { Sort sort; uint64_t id; RefId type; } CtxDecl;
ContextId context_make(size_t n, const CtxDecl *decls, FaceId assumption);
ContextId context_extend_term(ContextId ctx, TermVarId x, RefId type);
ContextId context_extend_dim(ContextId ctx, DimVarId i);
ContextId context_restrict(ContextId ctx, FaceId phi);     /* strengthen the assumption */
FaceId context_assumption(ContextId ctx);
size_t context_size(ContextId ctx);
CtxDecl context_decl(ContextId ctx, size_t k);
bool context_declares_term(ContextId ctx, TermVarId x, RefId *type_out);
bool context_declares_dim(ContextId ctx, DimVarId i);
typedef enum { OCC_VALID = 0, OCC_UNDECLARED_TERM, OCC_UNDECLARED_DIM, OCC_TYPE_MISMATCH, OCC_FACE_NOT_ENTAILED } OccStatus;
OccStatus occurrence_validate(RefId t, ContextId ctx, uint64_t *culprit);

/* ---- globals ---- */
/* a declared symbol: parameters (term variables with their declared types),
 * free dimensions, and its declared type over them; a symbol without a body
 * is an opaque constant of the signature */
SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type);
RefId global_type(SymbolId s);
RefId global_body(SymbolId s);          /* 0 when opaque */
VarSetId global_params(SymbolId s);
DimSetId global_dims(SymbolId s);
const char *global_name(SymbolId s);
size_t global_count(void);
bool set_global_body(SymbolId s, RefId body);   /* false: the environment is frozen (admitted); open a new one first */
RefId global_ref(SymbolId s);          /* VIEW(GLOBAL(s), identity) */
uint64_t global_env_version(void);     /* changes with every declaration / body registration */
uint64_t global_revision(SymbolId s);  /* §79.1: the symbol's declaration/body slot revision (1 opaque; 2 once a body is set) */
/* §78.4: the recorded instantiation edges of a reference: pairs (source, map)
 * such that dest = reindex(source, map) was constructed; n pairs */
#define instantiation_edges_PARAMS(X) X(RefId, dest) X(const uint64_t **, pairs)
KF_PROTO(instantiation_edges, size_t, instantiation_edges_PARAMS);
size_t instantiation_edges(RefId dest, const uint64_t **pairs);
extern void (*term_edge_hook)(RefId dest, RefId src, MapId sigma);   /* called after a new instantiation edge is recorded (no term lock held) */
void env_control_init(void); void env_freeze(void); void env_unfreeze(void); bool env_is_frozen(void);   /* §57 R1: define_global returns 0 and set_global_body false while frozen */
RefId unfold_global(RefId t);          /* reindex(definition body, map) */

/* ---- constructors (identity views of fresh origins) ---- */
RefId mk_universe(uint64_t level);
RefId mk_pi(TermVarId x, RefId A, RefId B);
RefId mk_sigma(TermVarId x, RefId A, RefId B);
RefId mk_lam(TermVarId x, RefId A, RefId body);
RefId mk_pi_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B);     /* A : U_m, B : U_n */
RefId mk_sigma_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B);
RefId mk_lam_lv(uint64_t m, TermVarId x, RefId A, RefId body);
RefId mk_app(RefId f, RefId a);
RefId mk_pair(RefId a, RefId b);
RefId mk_pair_at(RefId S, RefId a, RefId b);        /* PAIR with its Σ type annotation (field 2) */
RefId mk_fst(RefId p);
RefId mk_snd(RefId p);
RefId mk_path(DimVarId j, RefId B_j, RefId l, RefId r);
RefId mk_plam(DimVarId j, RefId body);
RefId mk_papp(DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s);
RefId mk_glue_type(RefId A, FaceId alpha, RefId T, RefId e);
RefId mk_glue_intro(RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a);
RefId mk_unglue(RefId A, FaceId alpha, RefId T, RefId e, RefId v);
RefId mk_comp(DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap);
/* annotated forms (§59.1): n is the family's / type's universe level */
RefId mk_comp_lv(uint64_t n, DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap);
RefId mk_path_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r);
RefId mk_papp_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s);
RefId mk_glue_type_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e);
RefId mk_glue_intro_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a);
RefId mk_unglue_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId v);
RefId mk_pair_at_lv(uint64_t l, RefId S, RefId a, RefId b);
RefId mk_system(size_t n, const FaceId *faces, const RefId *terms);
/* TRANSFORM_CALL(id, dir, σ, a) with checked instantiated type annotations:
 * payload = 2·id + dir; fields = the images of the template's parameters in
 * parameter-context order (F_REF / F_INTERVAL), then a, then the input and
 * output type annotations; required face = required_face[σ]. Reindexing a
 * view of it composes σ with the map and reindexes a and the annotations. */
RefId mk_tcall(uint64_t id, int dir, size_t nparams, const Field *params, RefId a, RefId in_type, RefId out_type, FaceId required);

/* ---- printing (presentation only) ---- */
void print_ref(RefId t, FILE *f);
void print_ref_depth(RefId t, FILE *f, int depth);


/* ---- frame families (kframe.h): the same procedures as resumable frames ---- */
#define mapb_finish_PARAMS(X) X(MapBuilder *, b)
KF_PROTO(mapb_finish, MapId, mapb_finish_PARAMS);
KF_PROTO(map_identity, MapId, KF_NOPARAMS);
#define map_term_image_PARAMS(X) X(MapId, m) X(TermVarId, x)
KF_PROTO(map_term_image, RefId, map_term_image_PARAMS);
#define map_dim_image_PARAMS(X) X(MapId, m) X(DimVarId, i)
KF_PROTO(map_dim_image, IntervalId, map_dim_image_PARAMS);
#define map_single_term_PARAMS(X) X(TermVarId, x) X(RefId, a)
KF_PROTO(map_single_term, MapId, map_single_term_PARAMS);
#define map_single_dim_PARAMS(X) X(DimVarId, i) X(IntervalId, r0)
KF_PROTO(map_single_dim, MapId, map_single_dim_PARAMS);
#define iv_reindex_PARAMS(X) X(IntervalId, r) X(MapId, m)
KF_PROTO(iv_reindex, IntervalId, iv_reindex_PARAMS);
#define fc_reindex_PARAMS(X) X(FaceId, phi) X(MapId, m)
KF_PROTO(fc_reindex, FaceId, fc_reindex_PARAMS);
#define compose_PARAMS(X) X(MapId, sigma) X(MapId, tau)
KF_PROTO(compose, MapId, compose_PARAMS);
#define term_require_push_PARAMS(X) X(FaceId, phi)
KF_PROTO(term_require_push, void, term_require_push_PARAMS);
#define levels_pack_PARAMS(X) X(uint64_t, m) X(uint64_t, n)
KF_PROTO(levels_pack, uint64_t, levels_pack_PARAMS);
#define level_max_PARAMS(X) X(uint64_t, a) X(uint64_t, b)
KF_PROTO(level_max, uint64_t, level_max_PARAMS);
#define level_succ_PARAMS(X) X(uint64_t, a)
KF_PROTO(level_succ, uint64_t, level_succ_PARAMS);
#define origin_make_PARAMS(X) X(Tag, tag) X(uint64_t, payload) X(const Field *, fields) X(size_t, nf) X(const Binder *, binders) X(size_t, nb)
KF_PROTO(origin_make, OriginId, origin_make_PARAMS);
#define bound_id_PARAMS(X) X(size_t, depth) X(size_t, slot)
KF_PROTO(bound_id, uint64_t, bound_id_PARAMS);
#define ref_var_PARAMS(X) X(TermVarId, x)
KF_PROTO(ref_var, RefId, ref_var_PARAMS);
#define make_view_PARAMS(X) X(OriginId, c) X(MapId, sigma)
KF_PROTO(make_view, RefId, make_view_PARAMS);
#define reindex_PARAMS(X) X(RefId, t) X(MapId, sigma)
KF_PROTO(reindex, RefId, reindex_PARAMS);
#define reindex1_PARAMS(X) X(RefId, t) X(TermVarId, x) X(RefId, a)
KF_PROTO(reindex1, RefId, reindex1_PARAMS);
#define reindex_dim_PARAMS(X) X(RefId, t) X(DimVarId, i) X(IntervalId, r)
KF_PROTO(reindex_dim, RefId, reindex_dim_PARAMS);
#define fresh_term_keyed_PARAMS(X) X(const KeyWord *, key) X(size_t, n) X(RefId, type)
KF_PROTO(fresh_term_keyed, TermVarId, fresh_term_keyed_PARAMS);
#define lifted_map_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(uint64_t *, fresh)
KF_PROTO(lifted_map, MapId, lifted_map_PARAMS);
#define resolve_term_binder_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(FieldIndex, body_field)
KF_PROTO(resolve_term_binder, TermOpen, resolve_term_binder_PARAMS);
#define resolve_dim_binder_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(FieldIndex, body_field)
KF_PROTO(resolve_dim_binder, DimOpen, resolve_dim_binder_PARAMS);
#define apply_term_binder_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(FieldIndex, body_field) X(RefId, a)
KF_PROTO(apply_term_binder, RefId, apply_term_binder_PARAMS);
#define apply_dim_binder_PARAMS(X) X(RefId, owner) X(BinderSlot, slot) X(FieldIndex, body_field) X(IntervalId, iv)
KF_PROTO(apply_dim_binder, RefId, apply_dim_binder_PARAMS);
#define open_ref_PARAMS(X) X(RefId, t) X(Head *, h)
KF_PROTO(open_ref, void, open_ref_PARAMS);
#define context_make_PARAMS(X) X(size_t, n) X(const CtxDecl *, decls) X(FaceId, assumption)
KF_PROTO(context_make, ContextId, context_make_PARAMS);
#define context_extend_term_PARAMS(X) X(ContextId, c) X(TermVarId, x) X(RefId, type)
KF_PROTO(context_extend_term, ContextId, context_extend_term_PARAMS);
#define context_extend_dim_PARAMS(X) X(ContextId, c) X(DimVarId, i)
KF_PROTO(context_extend_dim, ContextId, context_extend_dim_PARAMS);
#define context_restrict_PARAMS(X) X(ContextId, c) X(FaceId, phi)
KF_PROTO(context_restrict, ContextId, context_restrict_PARAMS);
#define global_ref_PARAMS(X) X(SymbolId, s)
KF_PROTO(global_ref, RefId, global_ref_PARAMS);
#define unfold_global_PARAMS(X) X(RefId, t)
KF_PROTO(unfold_global, RefId, unfold_global_PARAMS);
#define mk_universe_PARAMS(X) X(uint64_t, level)
KF_PROTO(mk_universe, RefId, mk_universe_PARAMS);
#define mk_pi_PARAMS(X) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_pi, RefId, mk_pi_PARAMS);
#define mk_sigma_PARAMS(X) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_sigma, RefId, mk_sigma_PARAMS);
#define mk_lam_PARAMS(X) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_lam, RefId, mk_lam_PARAMS);
#define mk_pi_lv_PARAMS(X) X(uint64_t, m) X(uint64_t, n) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_pi_lv, RefId, mk_pi_lv_PARAMS);
#define mk_sigma_lv_PARAMS(X) X(uint64_t, m) X(uint64_t, n) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_sigma_lv, RefId, mk_sigma_lv_PARAMS);
#define mk_lam_lv_PARAMS(X) X(uint64_t, m) X(TermVarId, x) X(RefId, A) X(RefId, B)
KF_PROTO(mk_lam_lv, RefId, mk_lam_lv_PARAMS);
#define term_levels_push_PARAMS(X) X(uint64_t, m) X(uint64_t, n)
KF_PROTO(term_levels_push, void, term_levels_push_PARAMS);
#define mk_app_PARAMS(X) X(RefId, fn) X(RefId, a)
KF_PROTO(mk_app, RefId, mk_app_PARAMS);
#define mk_pair_PARAMS(X) X(RefId, a) X(RefId, b0)
KF_PROTO(mk_pair, RefId, mk_pair_PARAMS);
#define mk_pair_at_PARAMS(X) X(RefId, S) X(RefId, a) X(RefId, b0)
KF_PROTO(mk_pair_at, RefId, mk_pair_at_PARAMS);
#define mk_fst_PARAMS(X) X(RefId, p)
KF_PROTO(mk_fst, RefId, mk_fst_PARAMS);
#define mk_snd_PARAMS(X) X(RefId, p)
KF_PROTO(mk_snd, RefId, mk_snd_PARAMS);
#define mk_path_PARAMS(X) X(DimVarId, j) X(RefId, B_j) X(RefId, l) X(RefId, r0)
KF_PROTO(mk_path, RefId, mk_path_PARAMS);
#define mk_plam_PARAMS(X) X(DimVarId, j) X(RefId, body)
KF_PROTO(mk_plam, RefId, mk_plam_PARAMS);
#define mk_papp_PARAMS(X) X(DimVarId, j) X(RefId, B_j) X(RefId, l) X(RefId, r0) X(RefId, p) X(IntervalId, s)
KF_PROTO(mk_papp, RefId, mk_papp_PARAMS);
#define mk_glue_type_PARAMS(X) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e)
KF_PROTO(mk_glue_type, RefId, mk_glue_type_PARAMS);
#define mk_glue_intro_PARAMS(X) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e) X(RefId, t) X(RefId, a)
KF_PROTO(mk_glue_intro, RefId, mk_glue_intro_PARAMS);
#define mk_unglue_PARAMS(X) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e) X(RefId, v)
KF_PROTO(mk_unglue, RefId, mk_unglue_PARAMS);
#define mk_comp_PARAMS(X) X(DimVarId, j) X(RefId, A_j) X(FaceId, phi) X(RefId, u_j) X(RefId, cap)
KF_PROTO(mk_comp, RefId, mk_comp_PARAMS);
#define mk_comp_lv_PARAMS(X) X(uint64_t, n) X(DimVarId, j) X(RefId, A_j) X(FaceId, phi) X(RefId, u_j) X(RefId, cap)
KF_PROTO(mk_comp_lv, RefId, mk_comp_lv_PARAMS);
#define mk_path_lv_PARAMS(X) X(uint64_t, n) X(DimVarId, j) X(RefId, B_j) X(RefId, l) X(RefId, r0)
KF_PROTO(mk_path_lv, RefId, mk_path_lv_PARAMS);
#define mk_papp_lv_PARAMS(X) X(uint64_t, n) X(DimVarId, j) X(RefId, B_j) X(RefId, l) X(RefId, r0) X(RefId, p) X(IntervalId, s)
KF_PROTO(mk_papp_lv, RefId, mk_papp_lv_PARAMS);
#define mk_glue_type_lv_PARAMS(X) X(uint64_t, n) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e)
KF_PROTO(mk_glue_type_lv, RefId, mk_glue_type_lv_PARAMS);
#define mk_glue_intro_lv_PARAMS(X) X(uint64_t, n) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e) X(RefId, t) X(RefId, a)
KF_PROTO(mk_glue_intro_lv, RefId, mk_glue_intro_lv_PARAMS);
#define mk_unglue_lv_PARAMS(X) X(uint64_t, n) X(RefId, A) X(FaceId, alpha) X(RefId, T) X(RefId, e) X(RefId, v)
KF_PROTO(mk_unglue_lv, RefId, mk_unglue_lv_PARAMS);
#define mk_pair_at_lv_PARAMS(X) X(uint64_t, n) X(RefId, S) X(RefId, a) X(RefId, b0)
KF_PROTO(mk_pair_at_lv, RefId, mk_pair_at_lv_PARAMS);
#define mk_tcall_PARAMS(X) X(uint64_t, id) X(int, dir) X(size_t, nparams) X(const Field *, params) X(RefId, a) X(RefId, in_type) X(RefId, out_type) X(FaceId, required)
KF_PROTO(mk_tcall, RefId, mk_tcall_PARAMS);
#define mk_system_PARAMS(X) X(size_t, n) X(const FaceId *, faces) X(const RefId *, terms)
KF_PROTO(mk_system, RefId, mk_system_PARAMS);

#endif

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
    T_SYSTEM, T_GLOBAL
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

const char *tag_name(Tag t);

/* ---- declarations ---- */
TermVarId declare_term(RefId type, FaceId required);
DimVarId declare_dim(void);
RefId term_var_type(TermVarId x);
FaceId term_var_required(TermVarId x);

/* ---- raw maps ---- */
typedef struct { Words t; Words d; } MapBuilder;   /* (key,image) pairs */
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
typedef enum { KW_CONST = 0, KW_REF, KW_FACE, KW_INTERVAL, KW_DIM, KW_VAR } KeyKind;
typedef struct { KeyKind kind; uint64_t v; } KeyWord;
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

typedef struct { TermVarId x; RefId type; RefId body; } TermOpen;
typedef struct { DimVarId j; RefId body; } DimOpen;
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

typedef struct {
    bool is_var;
    TermVarId var;
    Tag tag;
    uint64_t payload;
    RefId owner;
    OriginId origin;
    MapId map;
    size_t n;
    HField *f;
} Head;

void open_ref(RefId t, Head *h);
void head_free(Head *h);

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
void set_global_body(SymbolId s, RefId body);
RefId global_ref(SymbolId s);          /* VIEW(GLOBAL(s), identity) */
RefId unfold_global(RefId t);          /* reindex(definition body, map) */

/* ---- constructors (identity views of fresh origins) ---- */
RefId mk_universe(uint64_t level);
RefId mk_pi(TermVarId x, RefId A, RefId B);
RefId mk_sigma(TermVarId x, RefId A, RefId B);
RefId mk_lam(TermVarId x, RefId A, RefId body);
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
RefId mk_system(size_t n, const FaceId *faces, const RefId *terms);

/* ---- printing (presentation only) ---- */
void print_ref(RefId t, FILE *f);
void print_ref_depth(RefId t, FILE *f, int depth);

#endif

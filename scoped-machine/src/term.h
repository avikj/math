/* term.h — simultaneous substitutions, constructions, references, instantiated
 * support, binders and opening (§2, §6–9).
 *
 *   reference      = TVIEW(node, environment) | VAR(x)
 *   specialization = reindex(reference, substitution)
 *
 * A construction is a node whose fields are constants closed over positional
 * atoms (template.h); a template program's node interprets field recipes.
 * Nothing in this file evaluates. reindex traverses finite environments,
 * never a node's fields.
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
    uint64_t formal;      /* TermVarId or DimVarId bound by the construction (closed into its atom) */
    FieldIndex domain_field; /* term binders: field holding the domain type */
} Binder;

/* ---- universe levels (§59.1): explicit formation annotations ----
 * A construction record carries a packed pair of levels; LEVEL_NONE marks an
 * annotation the source did not supply (the checker then infers it; the
 * fixed templates always supply theirs). */
#define LEVEL_NONE  0xffffffffULL
#define LEVELS_NONE 0xffffffffffffffffULL
uint64_t levels_pack(uint64_t m, uint64_t n);
uint64_t levels_first(uint64_t lv);
uint64_t levels_second(uint64_t lv);
uint64_t level_max(uint64_t a, uint64_t b);      /* LEVEL_NONE absorbs */
uint64_t level_succ(uint64_t a);

/* ---- bound local occurrences (§50) ----
 * A local of a scope telescope is a (depth, slot) atom encoded in the
 * variable / dimension id space with the top bit set; it has no declaration
 * record and no free support. */
#define BOUND_BIT (1ULL << 61)           /* below the atom shift of the interval/face encodings */
static inline uint64_t bound_id(uint32_t depth, uint32_t slot) { return BOUND_BIT | ((uint64_t)depth << 32) | slot; }
static inline bool is_bound_id(uint64_t id) { return (id & BOUND_BIT) != 0; }
static inline uint32_t bound_depth(uint64_t id) { return (uint32_t)((id & ~BOUND_BIT) >> 32) & 0x1fffffffu; }
static inline uint32_t bound_slot(uint64_t id) { return (uint32_t)(id & 0xffffffffULL); }

/* ---- construction atoms ----
 * Inside a construction node's field constants, parameter k is the atom
 * obound_id(k) and the local of binder s is obound_id(np + s). The atoms of a
 * node are interpreted only against that node's environment (they never
 * occur in a construction's free boundary), so atoms of different nodes never
 * meet in one map. Like scope locals, an atom has no declaration. */
#define OBOUND_BIT (1ULL << 60)
static inline uint64_t obound_id(uint32_t slot) { return OBOUND_BIT | slot; }
static inline bool is_obound_id(uint64_t id) { return (id & OBOUND_BIT) != 0 && (id & BOUND_BIT) == 0; }
static inline bool is_local_atom(uint64_t id) { return is_bound_id(id) || is_obound_id(id); }

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
MapId map_override(MapId sigma, Sort sort, uint64_t key, uint64_t image);   /* sigma without key's entry, then key ↦ image */

/* ---- constructions ---- */
/* the construction (tag, payload, fields, binders) over its typed free
 * boundary, instantiated at the boundary itself */
RefId construct(Tag tag, uint64_t payload, const Field *fields, size_t nfields,
                const Binder *binders, size_t nbinders);
/* the construction families (construct.c) */
RefId construct_request(const uint64_t *req, size_t n);
uint64_t construction_field(RefId t, size_t k);
RefId construction_binder(RefId t, Sort sort, BinderSlot slot, FieldIndex field, uint64_t image);
RefId ref_var_family(TermVarId x);
RefId ref_var_publish(TermVarId x, DimSetId support, VarSetId fv, FaceId req);

/* ---- references ---- */
RefId ref_var(TermVarId x);
bool ref_is_var(RefId t);
/* TVIEW(node, environment) references (§49): every non-variable reference;
 * their operations live in the template layer */
Tag ref_tag(RefId t);                 /* the head tag of a non-variable reference */
uint64_t ref_tnode(RefId t);
uint64_t ref_tenv(RefId t);
RefId ref_intern_tview(uint64_t node, uint64_t env, DimSetId support, VarSetId fv, FaceId required);

TermVarId ref_var_id(RefId t);
DimSetId ref_support(RefId t);
VarSetId ref_freevars(RefId t);
FaceId ref_required(RefId t);
RefId reindex(RefId t, MapId sigma);
RefId reindex1(RefId t, TermVarId x, RefId a);
RefId reindex_dim(RefId t, DimVarId i, IntervalId r);

/* ---- binders ---- */
RefId ref_lookup(const uint64_t *w, size_t n);   /* a complete reference by content, or 0 */
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
/* a nominal record: typed key words (kind,value pairs) */

/* the lifted map of section 8 for a binder of a construction `owner`: its
 * environment map, then the binder's atom ↦ fresh. *fresh receives the
 * minted name. */

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
    uint64_t tnode, tenv; /* the node and its environment */
    size_t n;
} Head;

/* Opening exposes the head's tag, payload and levels; a field is computed
 * only when it is read (head_field), so opening does work independent of
 * the number of fields. */
void open_ref(RefId t, Head *h);
HField head_field(const Head *h, size_t k);
#define HF(h, k) head_field((h), (k))
void head_free(Head *h);
/* TVIEW operations (template.c) */
Tag tnode_tag(uint64_t Q);           /* template.c */
void tview_open(RefId t, Head *h);
TermOpen tview_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field);
DimOpen tview_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field);

/* ---- occurrence contexts (§2) ----
 * A context is an ordered list of declarations DIM(i) or TERM(x, type) with
 * a face assumption, interned by structure; it is not part of RefId. Its
 * validity and the scope of an occurrence in it are judgments (judge.ctx,
 * judge.scope). */
typedef struct { Sort sort; uint64_t id; } CtxDecl;
ContextId context_make(size_t n, const CtxDecl *decls, FaceId assumption);
ContextId context_extend_term(ContextId ctx, TermVarId x);
ContextId context_extend_dim(ContextId ctx, DimVarId i);
ContextId context_restrict(ContextId ctx, FaceId phi);     /* strengthen the assumption */
FaceId context_assumption(ContextId ctx);
size_t context_size(ContextId ctx);
CtxDecl context_decl(ContextId ctx, size_t k);

/* ---- globals ---- */
/* a declared symbol: parameters (term variables with their declared types),
 * free dimensions, and its declared type over them; a symbol without a body
 * is an opaque constant of the signature */
SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type);
RefId global_type(SymbolId s);
RefId global_body(SymbolId s);          /* 0 when opaque */
VarSetId global_params(SymbolId s);
DimSetId global_dims(SymbolId s);
size_t global_count(void);
bool set_global_body(SymbolId s, RefId body);   /* false: the environment is frozen (admitted); open a new one first */
RefId global_ref(SymbolId s);          /* the GLOBAL(s) construction at the definition's own parameters */
MapId global_args(RefId t);            /* a global reference's images of the definition's parameters */
ContextId global_context_flat(SymbolId s);   /* the parameter context of a global (fixed at declaration) */
ContextId boundary_context(VarSetId ft, DimSetId fd, FaceId req);          /* reindex(definition body, global_args) */

/* ---- constructors (constructions at their own boundary) ---- */
RefId mk_universe(uint64_t level);
RefId mk_pi(TermVarId x, RefId A, RefId B);
RefId mk_lam(TermVarId x, RefId A, RefId body);
RefId mk_pi_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B);     /* A : U_m, B : U_n */
RefId mk_sigma_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B);
RefId mk_lam_lv(uint64_t m, TermVarId x, RefId A, RefId body);
RefId mk_app(RefId f, RefId a);
RefId mk_pair(RefId a, RefId b);
RefId mk_fst(RefId p);
RefId mk_snd(RefId p);
RefId mk_path(DimVarId j, RefId B_j, RefId l, RefId r);
RefId mk_plam(DimVarId j, RefId body);
RefId mk_papp(DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s);
/* annotated forms (§59.1): n is the family's / type's universe level */
RefId mk_comp_lv(uint64_t n, DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap);
RefId mk_glue_type_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e);
RefId mk_glue_intro_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a);
RefId mk_unglue_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId v);
RefId mk_pair_at_lv(uint64_t l, RefId S, RefId a, RefId b);
RefId mk_system(size_t n, const FaceId *faces, const RefId *terms);
/* ---- printing (presentation only) ---- */
void print_ref(RefId t, FILE *f);
void print_ref_depth(RefId t, FILE *f, int depth);

#endif

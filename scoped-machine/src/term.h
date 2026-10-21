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
    T_SYSTEM, T_GLOBAL,
    /* code: the records the machine runs, as values of the language (code.c) */
    T_CODE, T_QUOTE, T_QIV, T_QFC,
    T_CMATCH, T_CINST, T_CEQ, T_CENT, T_CFCEND, T_CUNFOLD,
    T_CSET, T_CLEVELS, T_CSETLV, T_QLV, T_CLSUCC, T_CLMAX, T_COP, T_CSYSCONS, T_CVAR, T_CSUBST
} Tag;
#define T_LAST T_CSUBST
/* the operations of T_COP (its payload) on interval and face codes */
enum { COP_IVNEG = 1, COP_IVAND, COP_IVOR, COP_FCAND, COP_FCOR, COP_FORALL };
#define FORMER_SYS0 255   /* the former an empty system matches */

typedef enum { F_REF = 1, F_INTERVAL, F_FACE } FieldKind;
typedef enum { S_TERM = 1, S_DIM } Sort;


/* ---- universe levels (§59.1): explicit formation annotations ----
 * A level is an exact natural: a value below 2^63 is the word itself, a
 * larger one LEVEL_BIG | z with z its canonical exact-integer record
 * (chain.h), so equal levels are equal words. LEVEL_NONE marks an annotation
 * the source did not supply (the checker then infers it; the fixed templates
 * always supply theirs). A construction record carries the interned pair of
 * its two optional levels; LEVELS_NONE is the pair of two absent levels. */
#define LEVEL_NONE  UINT64_MAX
#define LEVELS_NONE UINT64_MAX
#define LEVEL_BIG   ((uint64_t)1 << 63)
uint64_t levels_pack(uint64_t m, uint64_t n);
uint64_t levels_first(uint64_t lv);
uint64_t levels_second(uint64_t lv);
/* successor and maximum (LEVEL_NONE absorbs): the _now forms answer in one
 * bounded step unless the operands need limb arithmetic, which is the
 * family level.succ / level.max, one limb per step; inside a step use
 * FR_LSUCC / FR_LMAX, outside one the host forms drive the family */
bool level_succ_now(uint64_t a, uint64_t *out);
bool level_max_now(uint64_t a, uint64_t b, uint64_t *out);
void level_print(uint64_t l, FILE *f);
uint64_t level_succ(uint64_t a);
void level_families_init(void);   /* level.c */
void code_families_init(void);    /* code.c */
#define FR_LSUCC(k, dst, a) if (!level_succ_now((a), &(dst))) FR_AWAIT(k, dst, F_LSUCC, (a), 0)
#define FR_LMAX(k, dst, a, b) if (!level_max_now((a), (b), &(dst))) FR_AWAIT(k, dst, F_LMAX, (a), (b))

/* ---- bound local occurrences (§50) ----
 * A local of a scope telescope is a (depth, slot) atom encoded in the
 * variable / dimension id space with the top bit set; it has no declaration
 * record and no free support. */
#define BOUND_BIT (1ULL << 61)           /* below the atom shift of the interval/face encodings */
static inline uint64_t bound_id(uint32_t depth, uint32_t slot) { return BOUND_BIT | ((uint64_t)depth << 32) | slot; }
static inline bool is_bound_id(uint64_t id) { return (id & BOUND_BIT) != 0; }
static inline uint32_t bound_depth(uint64_t id) { return (uint32_t)((id & ~BOUND_BIT) >> 32) & 0x1fffffffu; }
static inline uint32_t bound_slot(uint64_t id) { return (uint32_t)(id & 0xffffffffULL); }
/* A construction node is a binder like a scope: its field constants are
 * closed over (depth, slot) atoms — parameter k is bound_id(0, k), the local
 * of its binder bound_id(0, np) — and its environment applies them (APPLY). */

const char *tag_name(Tag t);

/* ---- declarations ---- */
TermVarId declare_term(RefId type, FaceId required);
DimVarId declare_dim(void);
RefId term_var_type(TermVarId x);
FaceId term_var_required(TermVarId x);

/* ---- substitution records (subst.c) ----
 * [(key, sort, value)*] sorted by key, an environment followed by its
 * definition word. A map's keys are variables, dimensions and atoms, its
 * absent keys their own images (identity entries are never stored); an
 * environment's keys are a node's slots. */
typedef enum { PS_REF = 1, PS_INTERVAL, PS_FACE, PS_SCOPE, PS_LEVEL } PSort;
typedef struct { PSort sort; uint64_t id; } TVal;   /* RefId / IntervalId / FaceId / ScopeId / level */
size_t subst_size(uint64_t rec);
void subst_get(uint64_t rec, size_t k, uint64_t *key, TVal *v);
uint64_t subst_value(uint64_t rec, size_t k);   /* the value of entry k */
uint64_t subst_entry(uint64_t key, uint64_t sort, uint64_t value);   /* the set family's entry operand */
bool subst_identity(uint64_t sort, uint64_t key, uint64_t value);
uint64_t env_empty(uint64_t def);
typedef struct { Words w; } MapBuilder;            /* (key, sort, image) triples */
void mapb_init(MapBuilder *b);
void mapb_term(MapBuilder *b, TermVarId x, RefId image);
void mapb_dim(MapBuilder *b, DimVarId i, IntervalId image);
MapId mapb_finish(MapBuilder *b);  /* sorts, rejects conflicting keys, drops identity entries, interns */
MapId map_identity(void);
bool map_is_identity(MapId m);
MapId map_single_term(TermVarId x, RefId a);
MapId map_single_dim(DimVarId i, IntervalId r);
RefId map_term_image(MapId m, TermVarId x);          /* VAR(x) when absent */
IntervalId map_dim_image(MapId m, DimVarId i);       /* i when absent */
IntervalId iv_reindex(IntervalId r, MapId m);
FaceId fc_reindex(FaceId phi, MapId m);
MapId compose(MapId sigma, MapId tau);   /* apply sigma then tau */
MapId map_override(MapId sigma, Sort sort, uint64_t key, uint64_t image);   /* sigma with key ↦ image */

/* ---- constructions (construct.c) ----
 * The constructor schema: per tag, its fields' kinds, the binder each sits
 * under, its binder's sort (a term binder's domain is field 0), its partial
 * (guarded) positions, its role and, for an eliminator, its scrutinee field.
 * A system's fields alternate face and reference. Every builder of a
 * construction — host, stepped, template — reads it. */
typedef enum { ROLE_OTHER = 0, ROLE_INTRO, ROLE_ELIM } TagRole;
typedef struct { uint8_t nf, bsort, role, scrut; uint8_t kind[6], under[6], partial[6]; } TagSchema;
const TagSchema *tag_schema(Tag tag);
FieldKind schema_kind(Tag tag, size_t k);
BinderSlot schema_slot(Tag tag, size_t k);
/* the request record [tag, payload, levels, declared, ft, fd, nf, (kind,
 * slot, id)*, nb, (sort, formal, domain)*] (ft = fd = 0: the boundary is
 * the fields'), written into a word buffer: its header, then one entry (a
 * field or binder triple) per write; the whole record of a fixed-shape tag
 * at operands ids[0..n) with binder formal `formal`; a system's header and
 * branches. construct_buf constructs a written record (host). */
enum { CREQ_MAX = 7 + 3 * 6 + 1 + 3 };
size_t creq_fixed(uint64_t *w, Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal);   /* into w[CREQ_MAX] */
void creq_begin(WordBuf *w, Tag tag, uint64_t payload, uint64_t levels, VarSetId ft, DimSetId fd, size_t nf);
void creq_entry(WordBuf *w, uint64_t a, uint64_t b, uint64_t c);
void creq_tag(WordBuf *w, Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal);
void creq_system_begin(WordBuf *w, size_t n);
void creq_system_branch(WordBuf *w, FaceId f, RefId t);   /* after the last branch: wordbuf_push(w, 0) */
RefId construct_buf(WordBuf *w);
RefId mk_tag(Tag tag, uint64_t payload, uint64_t levels, size_t n, const uint64_t *ids, uint64_t formal);
#define MK(tag, payload, levels, formal, ...) mk_tag((tag), (payload), (levels), sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ }, (formal))
uint64_t construction_field(RefId t, size_t k);
RefId construction_binder(RefId t, Sort sort, BinderSlot slot, FieldIndex field, uint64_t image);
uint64_t binder_req(Sort sort, BinderSlot slot, FieldIndex field, uint64_t image);   /* the binder family's operand */
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
TermVarId binder_term_var(RefId owner, BinderSlot slot, RefId type);
DimVarId binder_dim_var(RefId owner, BinderSlot slot);
/* Keyed fresh names for library definitions: deterministic per key. A key is
 * a typed tuple so that provenance can be compared up to renaming. */
typedef enum { KW_CONST = 0, KW_REF, KW_FACE, KW_INTERVAL, KW_DIM, KW_VAR } KeyKind;
typedef struct { KeyKind kind; uint64_t v; } KeyWord;
TermVarId fresh_term_keyed_req(const KeyWord *key, size_t n, RefId type, FaceId required);   /* a partial formal */
DimVarId fresh_dim_keyed(const KeyWord *key, size_t n);
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


/* ---- globals ---- */
/* a declared symbol: parameters (term variables with their declared types),
 * free dimensions, and its declared type over them. Its body, which may
 * mention the symbol itself, is set once and before the symbol's first
 * observation: that observation seals it, so every evaluation sees one body.
 * A symbol sealed without a body is an opaque constant. */
SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type);
VarSetId global_params(SymbolId s);
DimSetId global_dims(SymbolId s);
bool set_global_body(SymbolId s, RefId body);   /* once, before the first observation */
RefId global_body_sealed(SymbolId s);            /* the body (0: none), sealing the symbol */
RefId global_ref(SymbolId s);          /* the GLOBAL(s) construction at the definition's own parameters */

/* ---- constructors (constructions at their own boundary) ---- */
RefId mk_universe(uint64_t level);
RefId mk_pi(TermVarId x, RefId A, RefId B);
RefId mk_sigma_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B);
RefId mk_lam(TermVarId x, RefId A, RefId body);
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
RefId mk_system(size_t n, const FaceId *faces, const RefId *terms);
/* ---- printing (presentation only) ---- */
void print_ref(RefId t, FILE *f);
void print_ref_depth(RefId t, FILE *f, int depth);

#endif

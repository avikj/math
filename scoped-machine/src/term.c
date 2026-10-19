#include "term.h"
#include "template.h"

const char *tag_name(Tag t) {
    switch (t) {
    case T_UNIVERSE: return "U"; case T_PI: return "Π"; case T_SIGMA: return "Σ";
    case T_LAM: return "λ"; case T_APP: return "app"; case T_PAIR: return "pair";
    case T_FST: return "fst"; case T_SND: return "snd"; case T_PATH: return "PathP";
    case T_PLAM: return "plam"; case T_PAPP: return "papp"; case T_GLUE_TYPE: return "Glue";
    case T_GLUE_INTRO: return "glue"; case T_UNGLUE: return "unglue"; case T_COMP: return "comp";
    case T_SYSTEM: return "system"; case T_GLOBAL: return "global"; case T_TCALL: return "tcall";
    }
    return "?";
}

#define RSIDE(id) ((RefSide *)chunked_at(&M.ref_side, (id) - 1))
#define TDECL(x) ((TermDecl *)chunked_at(&M.term_decl, (x) - 1))
#define DPROV(i) ((uint64_t *)chunked_at(&M.dim_prov, (i) - 1))
#define NVAL(id) ((uint64_t *)chunked_at(&M.nominal_val, (id) - 1))
#define DEF(s) ((Def *)chunked_at(&M.defs, (s) - 1))
static void term_lock(void) { pthread_mutex_lock(&M.term_mu); }
static void term_unlock(void) { pthread_mutex_unlock(&M.term_mu); }

/* ================= declarations ================= */

TermVarId declare_term(RefId type, FaceId required) {
    term_lock();
    TermVarId x = (TermVarId)(M.n_term_vars + 1);
    TermDecl *d = TDECL(x);
    d->type = type; d->required = required; d->prov = 0;
    __atomic_store_n(&M.n_term_vars, M.n_term_vars + 1, __ATOMIC_RELEASE);
    term_unlock();
    return x;
}
DimVarId declare_dim(void) {
    term_lock();
    DimVarId i = (DimVarId)(M.n_dim_vars + 1);
    *DPROV(i) = 0;
    __atomic_store_n(&M.n_dim_vars, M.n_dim_vars + 1, __ATOMIC_RELEASE);
    term_unlock();
    return i;
}
static size_t n_terms_now(void) { return __atomic_load_n(&M.n_term_vars, __ATOMIC_ACQUIRE); }
RefId term_var_type(TermVarId x) { require(x >= 1 && x <= n_terms_now(), "undeclared term variable"); return TDECL(x)->type; }
FaceId term_var_required(TermVarId x) { require(x >= 1 && x <= n_terms_now(), "undeclared term variable"); return TDECL(x)->required; }

/* ================= raw maps ================= */
/* record: [(x,ref)*, (i,intv)*, nt] — keys sorted within each section, no
 * identity entries; the count is the last word, so a map is written in one
 * pass and both sections are reached in constant time. The operations on
 * maps (image lookup, override, composition) are families (subst.c). */

void mapb_init(MapBuilder *b) { words_init(&b->t); words_init(&b->d); }
void mapb_term(MapBuilder *b, TermVarId x, RefId image) { words_push(&b->t, x); words_push(&b->t, image); }
void mapb_dim(MapBuilder *b, DimVarId i, IntervalId image) { words_push(&b->d, i); words_push(&b->d, image); }

static int cmp_pair(const void *a, const void *b) {
    const uint64_t *x = a, *y = b;
    return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0;
}

MapId mapb_finish(MapBuilder *b) {
    size_t nt = b->t.n / 2, nd = b->d.n / 2;
    if (nt > 1) qsort(b->t.w, nt, 2 * sizeof(uint64_t), cmp_pair);
    if (nd > 1) qsort(b->d.w, nd, 2 * sizeof(uint64_t), cmp_pair);
    Words w; words_init(&w);
    size_t kept = 0;
    for (size_t k = 0; k < nt; k++) {
        uint64_t x = b->t.w[2 * k], img = b->t.w[2 * k + 1];
        if (k > 0 && b->t.w[2 * (k - 1)] == x) {
            require(b->t.w[2 * (k - 1) + 1] == img, "duplicate term key in map");
            continue;
        }
        if (img == ref_var(x)) continue;   /* identity entry */
        words_push(&w, x); words_push(&w, img); kept++;
    }
    for (size_t k = 0; k < nd; k++) {
        uint64_t i = b->d.w[2 * k], img = b->d.w[2 * k + 1];
        if (k > 0 && b->d.w[2 * (k - 1)] == i) {
            require(b->d.w[2 * (k - 1) + 1] == img, "duplicate dimension key in map");
            continue;
        }
        if (img == iv_var(i)) continue;
        words_push(&w, i); words_push(&w, img);
    }
    words_push(&w, kept);
    MapId id = interner_intern(&M.maps, w.w, w.n, NULL);
    words_free(&w);
    words_free(&b->t); words_free(&b->d);
    return id;
}

MapId map_identity(void) { MapBuilder b; mapb_init(&b); return mapb_finish(&b); }
bool map_is_identity(MapId m) { size_t n; (void)interner_get(&M.maps, m, &n); return n == 1; }
size_t map_n_terms(MapId m) { size_t n; const uint64_t *w = interner_get(&M.maps, m, &n); return (size_t)w[n - 1]; }
size_t map_n_dims(MapId m) { size_t n; const uint64_t *w = interner_get(&M.maps, m, &n); return (n - 1 - 2 * (size_t)w[n - 1]) / 2; }
void map_term_entry(MapId m, size_t k, TermVarId *x, RefId *img) {
    size_t n; const uint64_t *w = interner_get(&M.maps, m, &n);
    require(k < w[n - 1], "map entry out of range");
    *x = w[2 * k]; *img = w[2 * k + 1];
}
void map_dim_entry(MapId m, size_t k, DimVarId *i, IntervalId *img) {
    size_t n; const uint64_t *w = interner_get(&M.maps, m, &n);
    size_t nt = (size_t)w[n - 1];
    require(k < (n - 1 - 2 * nt) / 2, "map entry out of range");
    *i = w[2 * nt + 2 * k]; *img = w[2 * nt + 2 * k + 1];
}
MapId map_single_term(TermVarId x, RefId a) { MapBuilder b; mapb_init(&b); mapb_term(&b, x, a); return mapb_finish(&b); }
MapId map_single_dim(DimVarId i, IntervalId r) { MapBuilder b; mapb_init(&b); mapb_dim(&b, i, r); return mapb_finish(&b); }

/* ================= constructions ================= */
/* A construction is a node of the one constructor-program representation
 * (template.h): its fields are constants closed over positional atoms —
 * parameter k of its typed free boundary is obound_id(k), the local of
 * binder s is obound_id(np + s) — and its reference is TVIEW(node, images).
 * Alpha-equivalent constructions are one node; a construction and a
 * template view are one reference form. */

static __thread FaceId tl_req_scope[16]; static __thread size_t tl_req_depth;
static __thread uint64_t tl_levels = LEVELS_NONE;   /* formation levels of the origin being built (§59.1) */
void term_require_push(FaceId phi) {
    require(tl_req_depth < 16, "required-face scope too deep");
    FaceId f = tl_req_depth ? fc_meet(tl_req_scope[tl_req_depth - 1], phi) : phi;
    tl_req_scope[tl_req_depth++] = f;
}
void term_require_pop(void) { require(tl_req_depth > 0, "required-face scope underflow"); tl_req_depth--; }
static FaceId current_declared_required(void) { return tl_req_depth ? tl_req_scope[tl_req_depth - 1] : 0; }
/* §51.2 / §59.1: a level is a number below LEVEL_NONE or the sentinel itself;
 * anything else is a host failure, never a wrapped level */
static void level_check(uint64_t l) { require(l <= LEVEL_NONE, "universe level out of the representable range"); }
uint64_t levels_pack(uint64_t m, uint64_t n) { level_check(m); level_check(n); return m | (n << 32); }
uint64_t levels_first(uint64_t lv) { return lv & 0xffffffffULL; }
uint64_t levels_second(uint64_t lv) { return lv >> 32; }
uint64_t level_max(uint64_t a, uint64_t b) { if (a == LEVEL_NONE || b == LEVEL_NONE) return LEVEL_NONE; return a > b ? a : b; }
uint64_t level_succ(uint64_t a) { if (a == LEVEL_NONE) return LEVEL_NONE; require(a < LEVEL_NONE - 1, "universe level overflow"); return a + 1; }


/* the request record of a construction (construct.c):
 * [tag, payload, levels, declared, ft, fd, nf, (kind, slot, id)*, nb, (sort, formal, domain)*];
 * ft = fd = 0: the boundary is the fields' */
static RefId construction_request(Tag tag, uint64_t payload, const Field *fields, size_t nf,
                                  const Binder *binders, size_t nb, VarSetId ft, DimSetId fd) {
    Words w; words_init(&w);
    words_push(&w, tag); words_push(&w, payload); words_push(&w, tl_levels); words_push(&w, current_declared_required());
    words_push(&w, ft); words_push(&w, fd); words_push(&w, nf);
    for (size_t q = 0; q < nf; q++) { words_push(&w, fields[q].kind); words_push(&w, fields[q].slot); words_push(&w, fields[q].id); }
    words_push(&w, nb);
    for (size_t s = 0; s < nb; s++) { words_push(&w, binders[s].sort); words_push(&w, binders[s].formal); words_push(&w, binders[s].domain_field); }
    RefId t = construct_request(w.w, w.n);
    words_free(&w);
    return t;
}
RefId construct(Tag tag, uint64_t payload, const Field *fields, size_t nf, const Binder *binders, size_t nb) {
    return construction_request(tag, payload, fields, nf, binders, nb, 0, 0);
}

/* ================= references ================= */
/* record: [1, x] for VAR ; [3, node, environment] for TVIEW */

static void ref_side_set(RefId id, DimSetId support, VarSetId fv, FaceId req) {
    RefSide *r = RSIDE(id); r->support = support; r->freevars = fv; r->required = req;
    __atomic_store_n(&r->published, 1, __ATOMIC_RELEASE);
}
/* a reference found by its content: complete (record and side data) or 0.
 * Interner membership alone is not completion: the record becomes
 * discoverable before its producer has written the side data. */
RefId ref_lookup(const uint64_t *w, size_t n) {
    RefId id = interner_find(&M.refs, w, n);
    if (!id || !__atomic_load_n(&RSIDE(id)->published, __ATOMIC_ACQUIRE)) return 0;
    return id;
}

RefId ref_var(TermVarId x) {
    uint64_t w[2] = { 1, x };
    if (is_local_atom(x)) {
        /* a bound local occurrence (§50): no declaration record; its type and
         * guard live in the enclosing scope's or node's records */
        term_lock();
        RefId id = interner_find(&M.refs, w, 2);
        if (!id) {
            bool created;
            id = interner_intern(&M.refs, w, 2, &created);
            uint64_t xs[1] = { x };
            ref_side_set(id, dimset_make(NULL, 0), varset_make(xs, 1), fc_true());
        }
        term_unlock();
        return id;
    }
    require(x >= 1 && x <= n_terms_now(), "VAR of undeclared variable %llu", (unsigned long long)x);
    RefId id = ref_lookup(w, 2);
    if (id) return id;
    return ref_var_family(x);              /* its one owner publishes record and side data; an unfinished one is awaited */
}
/* VAR(x) with its typed boundary (computed by the ref.var family): x, the
 * closed boundary of its declaration type, the dimensions of its required
 * face; the record and its side data are published together */
RefId ref_var_publish(TermVarId x, DimSetId support, VarSetId fv, FaceId req) {
    uint64_t w[2] = { 1, x };
    bool created;
    term_lock();
    RefId id = interner_intern(&M.refs, w, 2, &created);
    if (created) ref_side_set(id, support, fv, req);
    term_unlock();
    return id;
}

bool ref_is_var(RefId t) { size_t n; return interner_get(&M.refs, t, &n)[0] == 1; }
bool ref_is_tview(RefId t) { return !ref_is_var(t); }
uint64_t ref_tnode(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 3, "not a TVIEW"); return w[1]; }
uint64_t ref_tenv(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 3, "not a TVIEW"); return w[2]; }
/* intern a TVIEW record with its computed side data (template layer) */
RefId ref_intern_tview(uint64_t node, uint64_t env, DimSetId support, VarSetId fv, FaceId required) {
    uint64_t w[3] = { 3, node, env };
    bool created;
    term_lock();
    RefId id = interner_intern(&M.refs, w, 3, &created);
    if (created) ref_side_set(id, support, fv, required);
    term_unlock();
    return id;
}
TermVarId ref_var_id(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] == 1, "not a VAR"); return w[1]; }
Tag ref_tag(RefId t) { size_t n; const uint64_t *w = interner_get(&M.refs, t, &n); require(w[0] != 1, "ref_tag of a variable"); return tnode_tag(w[1]); }
DimSetId ref_support(RefId t) { return RSIDE(t)->support; }
VarSetId ref_freevars(RefId t) { return RSIDE(t)->freevars; }
FaceId ref_required(RefId t) { return RSIDE(t)->required; }

RefId reindex1(RefId t, TermVarId x, RefId a) { return reindex(t, map_single_term(x, a)); }
RefId reindex_dim(RefId t, DimVarId i, IntervalId r) { return reindex(t, map_single_dim(i, r)); }

/* ================= binders ================= */

static uint64_t nominal_lookup(const KeyWord *key, size_t n, bool *created) {
    Words w; words_init(&w);
    for (size_t k = 0; k < n; k++) { words_push(&w, key[k].kind); words_push(&w, key[k].v); }
    uint64_t id = interner_intern(&M.nominal, w.w, w.n, created);
    words_free(&w);
    return id;
}
const uint64_t *nominal_key(uint64_t nid, size_t *npairs) {
    size_t n; const uint64_t *w = interner_get(&M.nominal, nid, &n);
    *npairs = n / 2;
    return w;
}
static void set_term_prov(TermVarId x, uint64_t nid) { TDECL(x)->prov = nid; }
static void set_dim_prov(DimVarId i, uint64_t nid) { *DPROV(i) = nid; }
uint64_t term_var_provenance(TermVarId x) { return TDECL(x)->prov; }
uint64_t dim_var_provenance(DimVarId i) { return *DPROV(i); }

TermVarId binder_term_var(RefId owner, BinderSlot slot, RefId type) {
    KeyWord key[4] = { { KW_CONST, 1 }, { KW_REF, owner }, { KW_CONST, slot }, { KW_CONST, S_TERM } };
    bool created;
    term_lock();
    uint64_t id = nominal_lookup(key, 4, &created);
    if (created) { *NVAL(id) = declare_term(type, fc_true()); set_term_prov(*NVAL(id), id); }
    TermVarId r = (TermVarId)*NVAL(id);
    term_unlock();
    return r;
}
DimVarId binder_dim_var(RefId owner, BinderSlot slot) {
    KeyWord key[4] = { { KW_CONST, 1 }, { KW_REF, owner }, { KW_CONST, slot }, { KW_CONST, S_DIM } };
    bool created;
    term_lock();
    uint64_t id = nominal_lookup(key, 4, &created);
    if (created) { *NVAL(id) = declare_dim(); set_dim_prov(*NVAL(id), id); }
    DimVarId r = (DimVarId)*NVAL(id);
    term_unlock();
    return r;
}
TermVarId fresh_term_keyed_req(const KeyWord *key, size_t n, RefId type, FaceId required) {
    KeyWord *w = malloc((n + 1) * sizeof(KeyWord)); require(w, "out of memory");
    w[0].kind = KW_CONST; w[0].v = 2; memcpy(w + 1, key, n * sizeof(KeyWord));
    bool created;
    term_lock();
    uint64_t id = nominal_lookup(w, n + 1, &created);
    free(w);
    if (created) { *NVAL(id) = declare_term(type, required); set_term_prov(*NVAL(id), id); }
    else require(term_var_type((TermVarId)*NVAL(id)) == type && term_var_required((TermVarId)*NVAL(id)) == required,
                 "keyed fresh variable reused at a different type or required face");
    TermVarId r = (TermVarId)*NVAL(id);
    term_unlock();
    return r;
}
TermVarId fresh_term_keyed(const KeyWord *key, size_t n, RefId type) { return fresh_term_keyed_req(key, n, type, fc_true()); }
DimVarId fresh_dim_keyed(const KeyWord *key, size_t n) {
    KeyWord *w = malloc((n + 1) * sizeof(KeyWord)); require(w, "out of memory");
    w[0].kind = KW_CONST; w[0].v = 3; memcpy(w + 1, key, n * sizeof(KeyWord));
    bool created;
    term_lock();
    uint64_t id = nominal_lookup(w, n + 1, &created);
    free(w);
    if (created) { *NVAL(id) = declare_dim(); set_dim_prov(*NVAL(id), id); }
    DimVarId r = (DimVarId)*NVAL(id);
    term_unlock();
    return r;
}

MapId lifted_map(RefId owner, BinderSlot slot, uint64_t *fresh) {
    require(!ref_is_var(owner), "lifted map of a variable");
    return tview_lifted_map(owner, slot, fresh);
}

TermOpen resolve_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    require(!ref_is_var(owner), "binder of a variable");
    return tview_term_binder(owner, slot, body_field);
}

DimOpen resolve_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    require(!ref_is_var(owner), "binder of a variable");
    return tview_dim_binder(owner, slot, body_field);
}

/* a construction's binder applied: its body constant with the binder's atom
 * ↦ the argument (no fresh name); a template instance opens and reindexes */
RefId apply_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field, RefId a) {
    require(!ref_is_var(owner), "binder of a variable");
    if (tview_is_construction(owner)) return construction_binder(owner, S_TERM, slot, body_field, a);
    TermOpen o = resolve_term_binder(owner, slot, body_field);
    return reindex1(o.body, o.x, a);
}
RefId apply_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field, IntervalId r) {
    require(!ref_is_var(owner), "binder of a variable");
    if (tview_is_construction(owner)) return construction_binder(owner, S_DIM, slot, body_field, r);
    DimOpen o = resolve_dim_binder(owner, slot, body_field);
    return reindex_dim(o.body, o.j, r);
}

/* ================= opening ================= */

void open_ref(RefId t, Head *h) {
    memset(h, 0, sizeof *h);
    h->owner = t;
    if (ref_is_var(t)) { h->is_var = true; h->var = ref_var_id(t); return; }
    tview_open(t, h);
}

HField head_field(const Head *h, size_t k) {
    require(!h->is_var && k < h->n, "head field out of range");
    if (!tnode_is_construction(h->tnode)) return tview_field(h, k);
    HField x; memset(&x, 0, sizeof x);
    x.kind = tnode_field_kind(h->tnode, k); x.index = (FieldIndex)k; x.slot = tnode_field_slot(h->tnode, k);
    if (x.slot != NO_SLOT) { x.is_binder = true; x.sort = tnode_binder_sort(h->tnode, x.slot); return x; }
    x.id = construction_field(h->owner, k);
    return x;
}

void head_free(Head *h) { h->n = 0; }

/* ================= occurrence contexts ================= */
/* record: [n, (sort, id, type)*, assumption] */

static ContextId context_intern(Words *w) { ContextId id = interner_intern(&M.contexts, w->w, w->n, NULL); words_free(w); return id; }

ContextId context_make(size_t n, const CtxDecl *decls, FaceId assumption) {
    /* well-formed: no duplicate declaration; a term declaration's type
     * depends only on earlier declarations */
    for (size_t k = 0; k < n; k++) {
        for (size_t j = 0; j < k; j++) require(!(decls[j].sort == decls[k].sort && decls[j].id == decls[k].id), "duplicate declaration in context");
        if (decls[k].sort != S_TERM) continue;
        size_t m; const uint64_t *xs = varset_get(ref_freevars(decls[k].type), &m);
        for (size_t q = 0; q < m; q++) { bool found = false; for (size_t j = 0; j < k; j++) if (decls[j].sort == S_TERM && decls[j].id == xs[q]) found = true; require(found, "context declaration type mentions a variable not declared earlier"); }
        const uint64_t *ds = dimset_get(ref_support(decls[k].type), &m);
        for (size_t q = 0; q < m; q++) { bool found = false; for (size_t j = 0; j < k; j++) if (decls[j].sort == S_DIM && decls[j].id == ds[q]) found = true; require(found, "context declaration type mentions a dimension not declared earlier"); }
    }
    Words w; words_init(&w);
    words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, decls[k].sort); words_push(&w, decls[k].id); words_push(&w, decls[k].sort == S_TERM ? decls[k].type : 0); }
    words_push(&w, assumption);
    return context_intern(&w);
}
static const uint64_t *ctx_words(ContextId c, size_t *n) { return interner_get(&M.contexts, c, n); }
size_t context_size(ContextId c) { size_t n; return (size_t)ctx_words(c, &n)[0]; }
FaceId context_assumption(ContextId c) { size_t n; const uint64_t *w = ctx_words(c, &n); return w[1 + 3 * w[0]]; }
CtxDecl context_decl(ContextId c, size_t k) {
    size_t n; const uint64_t *w = ctx_words(c, &n);
    require(k < w[0], "context declaration out of range");
    CtxDecl d = { (Sort)w[1 + 3 * k], w[2 + 3 * k], w[3 + 3 * k] };
    return d;
}
static ContextId context_with(ContextId c, const CtxDecl *extra, FaceId assumption) {
    size_t n = context_size(c);
    CtxDecl *ds = malloc((n + 1) * sizeof(CtxDecl));
    require(ds, "out of memory");
    for (size_t k = 0; k < n; k++) ds[k] = context_decl(c, k);
    if (extra) ds[n] = *extra;
    ContextId out = context_make(extra ? n + 1 : n, ds, assumption);
    free(ds);
    return out;
}
ContextId context_extend_term(ContextId c, TermVarId x, RefId type) { CtxDecl d = { S_TERM, x, type }; return context_with(c, &d, context_assumption(c)); }
ContextId context_extend_dim(ContextId c, DimVarId i) { CtxDecl d = { S_DIM, i, 0 }; return context_with(c, &d, context_assumption(c)); }
ContextId context_restrict(ContextId c, FaceId phi) { return context_with(c, NULL, fc_meet(context_assumption(c), phi)); }
bool context_declares_term(ContextId c, TermVarId x, RefId *type_out) {
    size_t n = context_size(c);
    for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(c, k); if (d.sort == S_TERM && d.id == x) { if (type_out) *type_out = d.type; return true; } }
    return false;
}
bool context_declares_dim(ContextId c, DimVarId i) {
    size_t n = context_size(c);
    for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(c, k); if (d.sort == S_DIM && d.id == i) return true; }
    return false;
}

OccStatus occurrence_validate(RefId t, ContextId ctx, uint64_t *culprit) {
    size_t n;
    const uint64_t *xs = varset_get(ref_freevars(t), &n);
    for (size_t k = 0; k < n; k++) {
        RefId ty;
        if (!context_declares_term(ctx, xs[k], &ty)) { if (culprit) *culprit = xs[k]; return OCC_UNDECLARED_TERM; }
        if (ty != term_var_type(xs[k])) { if (culprit) *culprit = xs[k]; return OCC_TYPE_MISMATCH; }
    }
    const uint64_t *ds = dimset_get(ref_support(t), &n);
    for (size_t k = 0; k < n; k++) if (!context_declares_dim(ctx, ds[k])) { if (culprit) *culprit = ds[k]; return OCC_UNDECLARED_DIM; }
    if (!fc_entails(context_assumption(ctx), ref_required(t))) return OCC_FACE_NOT_ENTAILED;
    return OCC_VALID;
}

/* ================= globals ================= */

/* the definition environment's version: every declaration or body
 * registration begins a new environment (§57 R1, §59.4) */
static uint64_t env_version_ctr;
uint64_t global_env_version(void) { return __atomic_load_n(&env_version_ctr, __ATOMIC_ACQUIRE); }
static void env_bump(void) { __atomic_add_fetch(&env_version_ctr, 1, __ATOMIC_ACQ_REL); }
/* §57 R1 / §59.4: the admitted environment is frozen; registration into a
 * frozen environment fails closed (a new candidate environment is opened by
 * the checker, which retires its caches) */
static bool env_frozen_flag;
/* a new machine starts with an open environment; the version counter is
 * never reused, so stale keys of a destroyed machine cannot alias */
void env_control_init(void) { __atomic_store_n(&env_frozen_flag, false, __ATOMIC_RELEASE); env_bump(); }
void env_freeze(void) { __atomic_store_n(&env_frozen_flag, true, __ATOMIC_RELEASE); }
void env_unfreeze(void) { __atomic_store_n(&env_frozen_flag, false, __ATOMIC_RELEASE); env_bump(); }
bool env_is_frozen(void) { return __atomic_load_n(&env_frozen_flag, __ATOMIC_ACQUIRE); }

SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type) {
    term_lock();
    if (env_is_frozen()) { term_unlock(); return 0; }
    SymbolId s = (SymbolId)(M.n_defs + 1);
    Def *d = DEF(s);
    d->body = 0; d->params = params; d->dims = dims; d->name = name; d->type = type;
    M.n_defs++;
    env_bump();
    term_unlock();
    return s;
}

bool set_global_body(SymbolId s, RefId body) {
    require(s >= 1 && s <= M.n_defs, "unknown symbol");
    Def *d = DEF(s);
    require(d->body == 0, "definition environment is immutable: %s already defined", d->name);
    if (env_is_frozen()) return false;
    size_t n; const uint64_t *xs = varset_get(ref_freevars(body), &n);
    for (size_t k = 0; k < n; k++) require(varset_contains(d->params, xs[k]), "global body has an undeclared free variable");
    const uint64_t *ds = dimset_get(ref_support(body), &n);
    for (size_t k = 0; k < n; k++) require(dimset_contains(d->dims, ds[k]), "global body has an undeclared free dimension");
    __atomic_store_n(&d->body, body, __ATOMIC_RELEASE);
    env_bump();
    return true;
}

RefId global_type(SymbolId s) { return DEF(s)->type; }
RefId global_body(SymbolId s) { return __atomic_load_n(&DEF(s)->body, __ATOMIC_ACQUIRE); }
VarSetId global_params(SymbolId s) { return DEF(s)->params; }
DimSetId global_dims(SymbolId s) { return DEF(s)->dims; }
const char *global_name(SymbolId s) { return DEF(s)->name; }
size_t global_count(void) { return M.n_defs; }

RefId global_ref(SymbolId s) {
    require(s >= 1 && s <= M.n_defs, "unknown symbol");
    return construction_request(T_GLOBAL, s, NULL, 0, NULL, 0, DEF(s)->params, DEF(s)->dims);
}

/* a global reference's environment as a substitution of the definition's
 * parameters (its node's parameters are the definition's dimensions, then
 * its parameters, in the construction order) */
MapId global_args(RefId t) {
    require(!ref_is_var(t) && ref_tag(t) == T_GLOBAL, "global arguments of a non-global");
    Head h; open_ref(t, &h);
    SymbolId s = (SymbolId)h.payload;
    size_t nd, nt;
    const uint64_t *ds = dimset_get(DEF(s)->dims, &nd), *xs = varset_get(DEF(s)->params, &nt);
    TEnvId E = ref_tenv(t);
    require(tenv_size(E) == nd + nt, "global reference with a strengthened boundary");
    MapBuilder b; mapb_init(&b);
    for (size_t k = 0; k < nd + nt; k++) {
        uint64_t slot; TVal v; tenv_entry(E, k, &slot, &v);
        if (k < nd) mapb_dim(&b, ds[k], v.id); else mapb_term(&b, xs[k - nd], v.id);
    }
    return mapb_finish(&b);
}

RefId unfold_global(RefId t) {
    require(!ref_is_var(t), "unfold of a variable");
    require(ref_tag(t) == T_GLOBAL, "unfold of a non-global");
    Head h; open_ref(t, &h);
    SymbolId s = (SymbolId)h.payload;
    RefId body = __atomic_load_n(&DEF(s)->body, __ATOMIC_ACQUIRE);
    require(body != 0, "global %s has no body", DEF(s)->name);
    return reindex(body, global_args(t));
}

/* ================= constructors ================= */

static RefId view0(Tag tag, uint64_t payload, const Field *f, size_t nf, const Binder *b, size_t nb) {
    return construct(tag, payload, f, nf, b, nb);
}

RefId mk_universe(uint64_t level) { require(level < LEVEL_NONE, "universe level out of the representable range"); return view0(T_UNIVERSE, level, NULL, 0, NULL, 0); }

/* annotated forms (§59.1): the formation levels are set for the origin
 * being built and recorded in its record */
static RefId with_levels(uint64_t lv, RefId (*build)(void *), void *ctx) {
    uint64_t saved = tl_levels; tl_levels = lv;
    RefId r = build(ctx);
    tl_levels = saved;
    return r;
}
static RefId mk_term_binder_form(Tag tag, TermVarId x, RefId A, RefId body) {
    require(term_var_type(x) == A, "binder formal declared at a different type");
    Field f[2] = { { F_REF, NO_SLOT, A }, { F_REF, 0, body } };
    Binder b[1] = { { S_TERM, x, 0 } };
    return view0(tag, 0, f, 2, b, 1);
}
RefId mk_pi(TermVarId x, RefId A, RefId B) { return mk_term_binder_form(T_PI, x, A, B); }
RefId mk_sigma(TermVarId x, RefId A, RefId B) { return mk_term_binder_form(T_SIGMA, x, A, B); }
RefId mk_lam(TermVarId x, RefId A, RefId body) { return mk_term_binder_form(T_LAM, x, A, body); }
typedef struct { Tag tag; TermVarId x; RefId A, B; } BinderArgs;
static RefId build_binder(void *c) { BinderArgs *a = c; return mk_term_binder_form(a->tag, a->x, a->A, a->B); }
RefId mk_pi_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B) { BinderArgs a = { T_PI, x, A, B }; return with_levels(levels_pack(m, n), build_binder, &a); }
RefId mk_sigma_lv(uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B) { BinderArgs a = { T_SIGMA, x, A, B }; return with_levels(levels_pack(m, n), build_binder, &a); }
RefId mk_lam_lv(uint64_t m, TermVarId x, RefId A, RefId body) { BinderArgs a = { T_LAM, x, A, body }; return with_levels(levels_pack(m, LEVEL_NONE), build_binder, &a); }
void term_levels_push(uint64_t m, uint64_t n) { tl_levels = levels_pack(m, n); }
void term_levels_pop(void) { tl_levels = LEVELS_NONE; }
RefId mk_app(RefId fn, RefId a) { Field f[2] = { { F_REF, NO_SLOT, fn }, { F_REF, NO_SLOT, a } }; return view0(T_APP, 0, f, 2, NULL, 0); }
RefId mk_pair(RefId a, RefId b) { Field f[2] = { { F_REF, NO_SLOT, a }, { F_REF, NO_SLOT, b } }; return view0(T_PAIR, 0, f, 2, NULL, 0); }
/* a pair annotated with its Σ type (§33: a checking-only form synthesizes
 * from its stored annotation); the annotation is the third field */
RefId mk_pair_at(RefId S, RefId a, RefId b) { Field f[3] = { { F_REF, NO_SLOT, a }, { F_REF, NO_SLOT, b }, { F_REF, NO_SLOT, S } }; return view0(T_PAIR, 0, f, 3, NULL, 0); }
RefId mk_fst(RefId p) { Field f[1] = { { F_REF, NO_SLOT, p } }; return view0(T_FST, 0, f, 1, NULL, 0); }
RefId mk_snd(RefId p) { Field f[1] = { { F_REF, NO_SLOT, p } }; return view0(T_SND, 0, f, 1, NULL, 0); }
RefId mk_path(DimVarId j, RefId B_j, RefId l, RefId r) {
    Field f[3] = { { F_REF, 0, B_j }, { F_REF, NO_SLOT, l }, { F_REF, NO_SLOT, r } };
    Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return view0(T_PATH, 0, f, 3, b, 1);
}
RefId mk_plam(DimVarId j, RefId body) {
    Field f[1] = { { F_REF, 0, body } };
    Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return view0(T_PLAM, 0, f, 1, b, 1);
}
RefId mk_papp(DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s) {
    Field f[5] = { { F_REF, 0, B_j }, { F_REF, NO_SLOT, l }, { F_REF, NO_SLOT, r }, { F_REF, NO_SLOT, p }, { F_INTERVAL, NO_SLOT, s } };
    Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return view0(T_PAPP, 0, f, 5, b, 1);
}
RefId mk_glue_type(RefId A, FaceId alpha, RefId T, RefId e) {
    Field f[4] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e } };
    return view0(T_GLUE_TYPE, 0, f, 4, NULL, 0);
}
RefId mk_glue_intro(RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a) {
    Field f[6] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e }, { F_REF, NO_SLOT, t }, { F_REF, NO_SLOT, a } };
    return view0(T_GLUE_INTRO, 0, f, 6, NULL, 0);
}
RefId mk_unglue(RefId A, FaceId alpha, RefId T, RefId e, RefId v) {
    Field f[5] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e }, { F_REF, NO_SLOT, v } };
    return view0(T_UNGLUE, 0, f, 5, NULL, 0);
}
RefId mk_comp(DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap) {
    Field f[4] = { { F_REF, 0, A_j }, { F_FACE, NO_SLOT, phi }, { F_REF, 0, u_j }, { F_REF, NO_SLOT, cap } };
    Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return view0(T_COMP, 0, f, 4, b, 1);
}
RefId mk_comp_lv(uint64_t n, DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap) {
    term_levels_push(n, LEVEL_NONE);
    RefId r = mk_comp(j, A_j, phi, u_j, cap);
    term_levels_pop();
    return r;
}
RefId mk_path_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r) { term_levels_push(n, LEVEL_NONE); RefId o = mk_path(j, B_j, l, r); term_levels_pop(); return o; }
RefId mk_papp_lv(uint64_t n, DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s) { term_levels_push(n, LEVEL_NONE); RefId o = mk_papp(j, B_j, l, r, p, s); term_levels_pop(); return o; }
RefId mk_glue_type_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e) { term_levels_push(n, LEVEL_NONE); RefId o = mk_glue_type(A, alpha, T, e); term_levels_pop(); return o; }
RefId mk_glue_intro_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a) { term_levels_push(n, LEVEL_NONE); RefId o = mk_glue_intro(A, alpha, T, e, t, a); term_levels_pop(); return o; }
RefId mk_unglue_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId v) { term_levels_push(n, LEVEL_NONE); RefId o = mk_unglue(A, alpha, T, e, v); term_levels_pop(); return o; }
RefId mk_pair_at_lv(uint64_t l, RefId S, RefId a, RefId b) { term_levels_push(l, LEVEL_NONE); RefId o = mk_pair_at(S, a, b); term_levels_pop(); return o; }
RefId mk_tcall(uint64_t id, int dir, size_t nparams, const Field *params, RefId a, RefId in_type, RefId out_type, FaceId required) {
    Field *f = malloc((nparams + 3) * sizeof(Field)); require(f, "out of memory");
    for (size_t k = 0; k < nparams; k++) { f[k] = params[k]; f[k].slot = NO_SLOT; }
    f[nparams] = (Field){ F_REF, NO_SLOT, a };
    f[nparams + 1] = (Field){ F_REF, NO_SLOT, in_type };
    f[nparams + 2] = (Field){ F_REF, NO_SLOT, out_type };
    term_require_push(required);
    RefId out = view0(T_TCALL, 2 * id + (dir ? 1 : 0), f, nparams + 3, NULL, 0);
    term_require_pop();
    free(f);
    return out;
}

RefId mk_system(size_t n, const FaceId *faces, const RefId *terms) {
    Field *f = malloc((n ? 2 * n : 1) * sizeof(Field));
    require(f, "out of memory");
    for (size_t k = 0; k < n; k++) {
        f[2 * k].kind = F_FACE; f[2 * k].slot = NO_SLOT; f[2 * k].id = faces[k];
        f[2 * k + 1].kind = F_REF; f[2 * k + 1].slot = NO_SLOT; f[2 * k + 1].id = terms[k];
    }
    RefId r = view0(T_SYSTEM, n, f, 2 * n, NULL, 0);
    free(f);
    return r;
}

/* ================= printing ================= */

static void pr(RefId t, FILE *f, int depth);

static void pr_field(const Head *h, size_t k, FILE *f, int depth) {
    HField xv = HF(h, k); const HField *x = &xv;
    if (x->is_binder) {
        if (x->sort == S_TERM) {
            TermOpen o = resolve_term_binder(h->owner, x->slot, x->index);
            fprintf(f, "x%llu. ", (unsigned long long)o.x);
            pr(o.body, f, depth - 1);
        } else {
            DimOpen o = resolve_dim_binder(h->owner, x->slot, x->index);
            fprintf(f, "d%llu. ", (unsigned long long)o.j);
            pr(o.body, f, depth - 1);
        }
        return;
    }
    switch (x->kind) {
    case F_REF: pr(x->id, f, depth - 1); break;
    case F_INTERVAL: iv_print(x->id, f); break;
    case F_FACE: fc_print(x->id, f); break;
    }
}

static void pr(RefId t, FILE *f, int depth) {
    if (ref_is_var(t)) { fprintf(f, "x%llu", (unsigned long long)ref_var_id(t)); return; }
    if (depth <= 0) { fprintf(f, "#%llu", (unsigned long long)t); return; }
    Head h; open_ref(t, &h);
    if (h.tag == T_UNIVERSE) { fprintf(f, "U%llu", (unsigned long long)h.payload); head_free(&h); return; }
    if (h.tag == T_GLOBAL) {
        fprintf(f, "%s", DEF(h.payload)->name);
        MapId args = global_args(t);
        if (!map_is_identity(args)) {
            fprintf(f, "[");
            size_t nt = map_n_terms(args), nd = map_n_dims(args);
            for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(args, k, &x, &im); fprintf(f, "%sx%llu:=", k ? "," : "", (unsigned long long)x); pr(im, f, depth - 1); }
            for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(args, k, &i, &im); fprintf(f, "%sd%llu:=", (k || nt) ? "," : "", (unsigned long long)i); iv_print(im, f); }
            fprintf(f, "]");
        }
        head_free(&h); return;
    }
    fprintf(f, "(%s", tag_name(h.tag));
    for (size_t k = 0; k < h.n; k++) { fprintf(f, " "); pr_field(&h, k, f, depth); }
    fprintf(f, ")");
    head_free(&h);
}

void print_ref_depth(RefId t, FILE *f, int depth) { pr(t, f, depth); }
void print_ref(RefId t, FILE *f) { pr(t, f, 12); }

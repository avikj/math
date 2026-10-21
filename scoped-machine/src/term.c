#include "term.h"
#include "template.h"
#include "eval.h"

const char *tag_name(Tag t) {
    switch (t) {
    case T_UNIVERSE: return "U"; case T_PI: return "Π"; case T_SIGMA: return "Σ";
    case T_LAM: return "λ"; case T_APP: return "app"; case T_PAIR: return "pair";
    case T_FST: return "fst"; case T_SND: return "snd"; case T_PATH: return "PathP";
    case T_PLAM: return "plam"; case T_PAPP: return "papp"; case T_GLUE_TYPE: return "Glue";
    case T_GLUE_INTRO: return "glue"; case T_UNGLUE: return "unglue"; case T_COMP: return "comp";
    case T_SYSTEM: return "system"; case T_GLOBAL: return "global";
    case T_CODE: return "Code"; case T_QUOTE: return "quote"; case T_QIV: return "qiv"; case T_QFC: return "qfc";
    case T_CMATCH: return "cmatch"; case T_CINST: return "cinst"; case T_CEQ: return "ceq";
    case T_CENT: return "cent"; case T_CFCEND: return "cfcend"; case T_CUNFOLD: return "cunfold";
    case T_CSET: return "cset"; case T_CLEVELS: return "clevels"; case T_CSETLV: return "csetlv"; case T_QLV: return "qlv";
    case T_CLSUCC: return "clsucc"; case T_CLMAX: return "clmax"; case T_COP: return "cop"; case T_CSYSCONS: return "csyscons";
    case T_CVAR: return "cvar"; case T_CSUBST: return "csubst";
    }
    return "?";
}

#define DEF(s) ((Def *)chunked_at(&M.defs, (s) - 1))

/* ================= declarations =================
 * A variable is its nominal record: the words of its key, then its sort and,
 * for a term variable, its type and required face —
 *   [tag, (kind, v)*, S_TERM, type, required]   |   [tag, (kind, v)*, S_DIM]
 * tag 1 a binder's name (owner, slot), 2 a keyed fresh term name, 3 a keyed
 * fresh dimension, 4 a host declaration (a serial number: each is fresh).
 * Its identity is the record id; ids grow with creation, so a variable's id
 * exceeds those of the variables its type mentions. */
static uint64_t var_record(const uint64_t *key, size_t nk, Sort sort, RefId type, FaceId required) {
    uint64_t w[INTERN_SMALL + 4]; size_t n = 0;
    require(nk + 3 <= sizeof w / sizeof w[0], "a nominal key of %zu words", nk);
    for (size_t q = 0; q < nk; q++) w[n++] = key[q];
    w[n++] = sort;
    if (sort == S_TERM) { require(type, "a term declaration has a type"); w[n++] = type; w[n++] = required; }
    return interner_intern(&M.keys, w, n, NULL);
}
TermVarId declare_term(RefId type, FaceId required) {
    uint64_t key[2] = { 4, __atomic_add_fetch(&M.n_fresh, 1, __ATOMIC_RELAXED) };
    return var_record(key, 2, S_TERM, type, required);
}
DimVarId declare_dim(void) {
    uint64_t key[2] = { 4, __atomic_add_fetch(&M.n_fresh, 1, __ATOMIC_RELAXED) };
    return var_record(key, 2, S_DIM, 0, 0);
}
static const uint64_t *term_decl(TermVarId x) {
    require(x >= 1 && !is_bound_id(x) && x <= interner_count(&M.keys), "undeclared term variable");
    size_t n; const uint64_t *w = rget(x, &n);
    require(n >= 4 && w[n - 3] == S_TERM, "not a term variable");
    return w + n - 2;
}
RefId term_var_type(TermVarId x) { return term_decl(x)[0]; }
FaceId term_var_required(TermVarId x) { return term_decl(x)[1]; }

/* ================= constructions ================= */
/* A construction is a node of the one constructor-program representation
 * (template.h): its fields are constants closed over (depth, slot) atoms —
 * parameter k of its typed free boundary is bound_id(0, k), the local of
 * its binder bound_id(0, np) — and its reference is TVIEW(node, images).
 * Alpha-equivalent constructions are one node; a construction and a
 * template view are one reference form. */

/* §59.1: the interned pair of two optional levels (a small record) */
uint64_t levels_pack(uint64_t m, uint64_t n) { return m == LEVEL_NONE && n == LEVEL_NONE ? LEVELS_NONE : RQ(m, n); }
uint64_t levels_first(uint64_t lv) { return lv == LEVELS_NONE ? LEVEL_NONE : rword(lv, 0); }
uint64_t levels_second(uint64_t lv) { return lv == LEVELS_NONE ? LEVEL_NONE : rword(lv, 1); }


/* ================= references ================= */
/* record: [1, x] for VAR ; [3, node, environment] for TVIEW */

/* records: [1, x, support, freevars, required] for VAR; [3, node,
 * environment, support, freevars, required] for TVIEW. The side data is a
 * function of (x) or (node, environment), so the record with it is still
 * one record per reference, and interning publishes it whole. */
RefId ref_var(TermVarId x) {
    if (is_bound_id(x)) {
        /* a bound local occurrence (§50): no declaration record; its type and
         * guard live in the enclosing scope's or node's records */
        uint64_t xs[1] = { x };
        uint64_t w[5] = { 1, x, set_make(NULL, 0), set_make(xs, 1), fc_true() };
        return interner_intern(&M.keys, w, 5, NULL);
    }
    (void)term_decl(x);
    return ref_var_family(x);              /* the ref.var producer computes its typed boundary */
}
/* VAR(x) with its typed boundary (computed by the ref.var family) */
RefId ref_var_publish(TermVarId x, DimSetId support, VarSetId fv, FaceId req) {
    uint64_t w[5] = { 1, x, support, fv, req };
    return interner_intern(&M.keys, w, 5, NULL);
}
bool ref_is_var(RefId t) { return rword(t, 0) == 1; }
uint64_t ref_tnode(RefId t) { size_t n; const uint64_t *w = rget(t, &n); require(w[0] == 3, "not a TVIEW"); return w[1]; }
uint64_t ref_tenv(RefId t) { size_t n; const uint64_t *w = rget(t, &n); require(w[0] == 3, "not a TVIEW"); return w[2]; }
RefId ref_intern_tview(uint64_t node, uint64_t env, DimSetId support, VarSetId fv, FaceId required) {
    uint64_t w[6] = { 3, node, env, support, fv, required };
    return interner_intern(&M.keys, w, 6, NULL);
}
TermVarId ref_var_id(RefId t) { size_t n; const uint64_t *w = rget(t, &n); require(w[0] == 1, "not a VAR"); return w[1]; }
Tag ref_tag(RefId t) { size_t n; const uint64_t *w = rget(t, &n); require(w[0] != 1, "ref_tag of a variable"); return tnode_tag(w[1]); }
DimSetId ref_support(RefId t) { size_t n; const uint64_t *w = rget(t, &n); return w[n - 3]; }
VarSetId ref_freevars(RefId t) { size_t n; const uint64_t *w = rget(t, &n); return w[n - 2]; }
FaceId ref_required(RefId t) { size_t n; const uint64_t *w = rget(t, &n); return w[n - 1]; }

RefId reindex1(RefId t, TermVarId x, RefId a) { return reindex(t, map_single_term(x, a)); }

/* ================= binders ================= */

TermVarId binder_term_var(RefId owner, BinderSlot slot, RefId type) {
    uint64_t w[5] = { 1, KW_REF, owner, KW_CONST, slot };
    return var_record(w, 5, S_TERM, type, fc_true());
}
DimVarId binder_dim_var(RefId owner, BinderSlot slot) {
    uint64_t w[5] = { 1, KW_REF, owner, KW_CONST, slot };
    return var_record(w, 5, S_DIM, 0, 0);
}

TermOpen resolve_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    require(!ref_is_var(owner), "binder of a variable");
    return tview_term_binder(owner, slot, body_field);
}

DimOpen resolve_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field) {
    require(!ref_is_var(owner), "binder of a variable");
    return tview_dim_binder(owner, slot, body_field);
}

/* a binder applied: the binder's local set to the argument in the node's
 * environment and the body interpreted (one family for both node kinds; no
 * fresh name) */
RefId apply_term_binder(RefId owner, BinderSlot slot, FieldIndex body_field, RefId a) {
    require(!ref_is_var(owner), "binder of a variable");
    return construction_binder(owner, S_TERM, slot, body_field, a);
}
RefId apply_dim_binder(RefId owner, BinderSlot slot, FieldIndex body_field, IntervalId r) {
    require(!ref_is_var(owner), "binder of a variable");
    return construction_binder(owner, S_DIM, slot, body_field, r);
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
    HField x; memset(&x, 0, sizeof x);
    x.kind = tnode_field_kind(h->tnode, k); x.index = (FieldIndex)k; x.slot = tnode_field_slot(h->tnode, k);
    if (x.slot != NO_SLOT) { x.is_binder = true; x.sort = tnode_binder_sort(h->tnode, x.slot); return x; }
    x.id = construction_field(h->owner, k);       /* the field family: one interpretation for both node kinds */
    return x;
}

void head_free(Head *h) { h->n = 0; }

/* ================= globals ================= */


SymbolId define_global(const char *name, VarSetId params, DimSetId dims, RefId type) {
    SymbolId s = (SymbolId)__atomic_add_fetch(&M.n_defs, 1, __ATOMIC_RELAXED);
    Def *d = DEF(s);
    d->params = params; d->dims = dims; d->name = name; d->type = type;
    return s;
}

/* One word decides a symbol's body: 0 while open; a body set by one CAS from
 * 0; DEF_OPAQUE set by the first observation of an open symbol. Either way
 * the word never changes again, so every evaluation sees the same body. */
bool set_global_body(SymbolId s, RefId body) {
    require(s >= 1 && s <= __atomic_load_n(&M.n_defs, __ATOMIC_RELAXED), "unknown symbol");
    require(body && !(body & DEF_OPAQUE), "a body is a reference");
    uint64_t open = 0;
    require(__atomic_compare_exchange_n(&DEF(s)->body, &open, body, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE),
            "%s already has a body or was observed without one", DEF(s)->name);
    return true;
}
RefId global_body_sealed(SymbolId s) {
    uint64_t v = 0;
    if (__atomic_compare_exchange_n(&DEF(s)->body, &v, DEF_OPAQUE, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return 0;
    return v == DEF_OPAQUE ? 0 : v;
}

VarSetId global_params(SymbolId s) { return DEF(s)->params; }
DimSetId global_dims(SymbolId s) { return DEF(s)->dims; }

RefId global_ref(SymbolId s) {
    require(s >= 1 && s <= __atomic_load_n(&M.n_defs, __ATOMIC_RELAXED), "unknown symbol");
    WordBuf w; creq_begin(&w, T_GLOBAL, s, LEVELS_NONE, DEF(s)->params, DEF(s)->dims, 0);
    wordbuf_push(&w, 0);
    return construct_buf(&w);
}

/* ================= constructors (by the schema, construct.c) ================= */

RefId mk_universe(uint64_t level) { require(level != LEVEL_NONE, "a universe needs a level"); return mk_tag(T_UNIVERSE, level, LEVELS_NONE, 0, NULL, 0); }
static RefId mk_term_binder_form(Tag tag, uint64_t lv, TermVarId x, RefId A, RefId body) {
    require(term_var_type(x) == A, "binder formal declared at a different type");
    return MK(tag, 0, lv, x, A, body);
}
RefId mk_pi(TermVarId x, RefId A, RefId B) { return mk_term_binder_form(T_PI, LEVELS_NONE, x, A, B); }
RefId mk_lam(TermVarId x, RefId A, RefId body) { return mk_term_binder_form(T_LAM, LEVELS_NONE, x, A, body); }
RefId mk_lam_lv(uint64_t m, TermVarId x, RefId A, RefId body) { return mk_term_binder_form(T_LAM, levels_pack(m, LEVEL_NONE), x, A, body); }
RefId mk_app(RefId fn, RefId a) { return MK(T_APP, 0, LEVELS_NONE, 0, fn, a); }
RefId mk_pair(RefId a, RefId b) { return MK(T_PAIR, 0, LEVELS_NONE, 0, a, b); }
/* a pair annotated with its Σ type (§33: a checking-only form synthesizes
 * from its stored annotation); the annotation is the third field */
RefId mk_fst(RefId p) { return MK(T_FST, 0, LEVELS_NONE, 0, p); }
RefId mk_snd(RefId p) { return MK(T_SND, 0, LEVELS_NONE, 0, p); }
RefId mk_path(DimVarId j, RefId B_j, RefId l, RefId r) { return MK(T_PATH, 0, LEVELS_NONE, j, B_j, l, r); }
RefId mk_plam(DimVarId j, RefId body) { return MK(T_PLAM, 0, LEVELS_NONE, j, body); }
RefId mk_papp(DimVarId j, RefId B_j, RefId l, RefId r, RefId p, IntervalId s) { return MK(T_PAPP, 0, LEVELS_NONE, j, B_j, l, r, p, s); }
RefId mk_glue_type_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e) { return MK(T_GLUE_TYPE, 0, levels_pack(n, LEVEL_NONE), 0, A, alpha, T, e); }
RefId mk_glue_intro_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId t, RefId a) { return MK(T_GLUE_INTRO, 0, levels_pack(n, LEVEL_NONE), 0, A, alpha, T, e, t, a); }
RefId mk_unglue_lv(uint64_t n, RefId A, FaceId alpha, RefId T, RefId e, RefId v) { return MK(T_UNGLUE, 0, levels_pack(n, LEVEL_NONE), 0, A, alpha, T, e, v); }
RefId mk_comp_lv(uint64_t n, DimVarId j, RefId A_j, FaceId phi, RefId u_j, RefId cap) { return MK(T_COMP, 0, levels_pack(n, LEVEL_NONE), j, A_j, phi, u_j, cap); }
RefId mk_system(size_t n, const FaceId *faces, const RefId *terms) {
    WordBuf w; creq_system_begin(&w, n);
    for (size_t k = 0; k < n; k++) creq_system_branch(&w, faces[k], terms[k]);
    wordbuf_push(&w, 0);
    return construct_buf(&w);
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
    if (h.tag == T_UNIVERSE) { fprintf(f, "U"); level_print(h.payload, f); head_free(&h); return; }
    if (h.tag == T_GLOBAL) {
        fprintf(f, "%s", DEF(h.payload)->name);
        /* the arguments: the environment's values, dimensions then terms */
        uint64_t E = ref_tenv(t); size_t n = subst_size(E);
        if (n) {
            fprintf(f, "[");
            for (size_t k = 0; k < n; k++) {
                uint64_t slot; TVal v; subst_get(E, k, &slot, &v);
                if (k) fprintf(f, ",");
                if (v.sort == PS_INTERVAL) iv_print(v.id, f); else pr(v.id, f, depth - 1);
            }
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

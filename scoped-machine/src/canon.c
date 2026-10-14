#define _POSIX_C_SOURCE 200809L
#include "canon.h"

struct Canon {
    /* memo of hashes, indexed by id-1; 0 = not computed */
    uint64_t *href; size_t href_cap;
    uint64_t *hface; size_t hface_cap;
    uint64_t *hiv; size_t hiv_cap;
    uint64_t *hnom; size_t hnom_cap;
    /* DFS numbers of dumped records (refs and nominal records), 0 = not yet */
    size_t *nref; size_t nref_cap;
    size_t *nnom; size_t nnom_cap;
    size_t next;
    char *buf; size_t len, cap;
};

#define GROW(arr, cap, need, T) do { if ((need) > (cap)) { size_t nc = (cap) ? (cap) * 2 : 256; while (nc < (need)) nc *= 2; \
    (arr) = realloc((arr), nc * sizeof(T)); require((arr), "out of memory"); memset((arr) + (cap), 0, (nc - (cap)) * sizeof(T)); (cap) = nc; } } while (0)

Canon *canon_new(void) { Canon *c = calloc(1, sizeof *c); require(c, "out of memory"); c->cap = 4096; c->buf = calloc(1, c->cap); require(c->buf, "out of memory"); return c; }
void canon_free(Canon *c) { free(c->href); free(c->hface); free(c->hiv); free(c->hnom); free(c->nref); free(c->nnom); free(c->buf); free(c); }

static uint64_t mix(uint64_t h, uint64_t x) { h ^= x + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 31; return h; }
static uint64_t hstr(uint64_t h, const char *s) { while (*s) h = mix(h, (unsigned char)*s++); return h; }

void canon_text(Canon *c, const char *s) {
    size_t n = strlen(s);
    if (c->len + n + 1 > c->cap) { size_t nc = c->cap ? c->cap * 2 : 4096; while (nc < c->len + n + 1) nc *= 2; c->buf = realloc(c->buf, nc); require(c->buf, "out of memory"); c->cap = nc; }
    memcpy(c->buf + c->len, s, n + 1); c->len += n;
}
static void textf(Canon *c, const char *fmt, uint64_t a) { char tmp[64]; snprintf(tmp, sizeof tmp, fmt, (unsigned long long)a); canon_text(c, tmp); }
const char *canon_buffer(Canon *c, size_t *len) { if (len) *len = c->len; return c->buf ? c->buf : ""; }

/* ---- input indices: position among input (provenance-free) names ---- */
static uint64_t input_index_term(TermVarId x) { uint64_t k = 0; for (TermVarId y = 1; y < x; y++) if (term_var_provenance(y) == 0) k++; return k; }
static uint64_t input_index_dim(DimVarId i) { uint64_t k = 0; for (DimVarId j = 1; j < i; j++) if (dim_var_provenance(j) == 0) k++; return k; }

/* ---- hashes ---- */
static uint64_t hash_nominal(Canon *c, uint64_t nid);
static uint64_t hash_var(Canon *c, TermVarId x) { uint64_t p = term_var_provenance(x); return p ? mix(hash_nominal(c, p), 0x7E) : mix(mix(0x1A, 0x11), input_index_term(x)); }
static uint64_t hash_dim(Canon *c, DimVarId i) { uint64_t p = dim_var_provenance(i); return p ? mix(hash_nominal(c, p), 0xD1) : mix(mix(0x1A, 0x22), input_index_dim(i)); }

static uint64_t hash_dnf(Canon *c, const Dnf *d, bool face) {
    uint64_t total = 0x51;
    for (size_t i = 0; i < d->n; i++) {
        uint64_t cl = 0x52;
        for (size_t k = 0; k < d->c[i].n; k++) {
            uint64_t a = d->c[i].a[k];
            uint64_t ha = mix(hash_dim(c, a >> 1), (a & 1) + (face ? 10 : 20));
            cl += mix(ha, 0x53);                 /* commutative within a clause */
        }
        total += mix(cl, 0x54);                  /* commutative across clauses */
    }
    return mix(total, d->n);
}

uint64_t canon_hash_interval(Canon *c, IntervalId r) {
    GROW(c->hiv, c->hiv_cap, r, uint64_t);
    if (c->hiv[r - 1]) return c->hiv[r - 1];
    Dnf d; iv_to_dnf(r, &d);
    uint64_t h = mix(hash_dnf(c, &d, false), 0x1F);
    dnf_free(&d);
    return c->hiv[r - 1] = h ? h : 1;
}
uint64_t canon_hash_face(Canon *c, FaceId f) {
    GROW(c->hface, c->hface_cap, f, uint64_t);
    if (c->hface[f - 1]) return c->hface[f - 1];
    Dnf d; fc_to_dnf(f, &d);
    uint64_t h = mix(hash_dnf(c, &d, true), 0x2F);
    dnf_free(&d);
    return c->hface[f - 1] = h ? h : 1;
}

static uint64_t hash_nominal(Canon *c, uint64_t nid) {
    GROW(c->hnom, c->hnom_cap, nid, uint64_t);
    if (c->hnom[nid - 1]) return c->hnom[nid - 1];
    size_t n; const uint64_t *w = nominal_key(nid, &n);
    uint64_t h = 0xA0;
    for (size_t k = 0; k < n; k++) {
        uint64_t kind = w[2 * k], v = w[2 * k + 1];
        h = mix(h, kind);
        switch ((KeyKind)kind) {
        case KW_CONST: h = mix(h, v); break;
        case KW_REF: h = mix(h, canon_hash_ref(c, v)); break;
        case KW_FACE: h = mix(h, canon_hash_face(c, v)); break;
        case KW_INTERVAL: h = mix(h, canon_hash_interval(c, v)); break;
        case KW_DIM: h = mix(h, hash_dim(c, v)); break;
        case KW_VAR: h = mix(h, hash_var(c, v)); break;
        }
    }
    return c->hnom[nid - 1] = h ? h : 1;
}

uint64_t canon_hash_ref(Canon *c, RefId t) {
    GROW(c->href, c->href_cap, t, uint64_t);
    if (c->href[t - 1]) return c->href[t - 1];
    uint64_t h;
    if (ref_is_var(t)) h = mix(0xB0, hash_var(c, ref_var_id(t)));
    else {
        OriginId o = ref_origin(t); MapId m = ref_map(t);
        Tag tag = origin_tag(o);
        h = mix(0xB1, tag);
        if (tag == T_GLOBAL) h = hstr(h, M.defs[origin_payload(o) - 1].name); else h = mix(h, origin_payload(o));
        size_t nb = origin_nbinders(o);
        for (size_t k = 0; k < nb; k++) {
            Binder b = origin_binder(o, (BinderSlot)k);
            h = mix(mix(h, b.sort), b.domain_field);
            h = mix(h, b.sort == S_TERM ? hash_var(c, b.formal) : hash_dim(c, b.formal));
        }
        size_t nf = origin_nfields(o);
        for (size_t k = 0; k < nf; k++) {
            Field f = origin_field(o, (FieldIndex)k);
            h = mix(mix(h, f.kind), f.slot);
            switch (f.kind) {
            case F_REF: h = mix(h, canon_hash_ref(c, f.id)); break;
            case F_INTERVAL: h = mix(h, canon_hash_interval(c, f.id)); break;
            case F_FACE: h = mix(h, canon_hash_face(c, f.id)); break;
            }
        }
        uint64_t hm = 0xC0;
        size_t nt = map_n_terms(m), nd = map_n_dims(m);
        for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(m, k, &x, &im); hm += mix(mix(hash_var(c, x), canon_hash_ref(c, im)), 0xC1); }
        for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(m, k, &i, &im); hm += mix(mix(hash_dim(c, i), canon_hash_interval(c, im)), 0xC2); }
        h = mix(h, hm);
    }
    return c->href[t - 1] = h ? h : 1;
}

/* ---- dump ---- */
static size_t dump_nominal(Canon *c, uint64_t nid);

static void name_var(Canon *c, TermVarId x) {
    uint64_t p = term_var_provenance(x);
    if (p) textf(c, "v#%llu", dump_nominal(c, p)); else textf(c, "x%llu", input_index_term(x));
}
static void name_dim(Canon *c, DimVarId i) {
    uint64_t p = dim_var_provenance(i);
    if (p) textf(c, "d#%llu", dump_nominal(c, p)); else textf(c, "i%llu", input_index_dim(i));
}

/* render a DNF as sorted clause strings over canonical dimension names */
typedef struct { char *s; } Str;
static int cmp_str(const void *a, const void *b) { return strcmp(((const Str *)a)->s, ((const Str *)b)->s); }

static void dump_dnf(Canon *c, const Dnf *d, bool face) {
    /* make sure every dimension's provenance record is numbered first, in hash order */
    Words dims; words_init(&dims);
    for (size_t i = 0; i < d->n; i++) for (size_t k = 0; k < d->c[i].n; k++) words_push(&dims, d->c[i].a[k] >> 1);
    dims.n = sort_unique_u64(dims.w, dims.n);
    for (size_t pass = 0; pass < dims.n; pass++) {            /* selection by hash: O(n^2), n tiny */
        uint64_t best = 0, bh = 0; bool have = false;
        for (size_t k = 0; k < dims.n; k++) {
            if (dims.w[k] == 0) continue;
            uint64_t h = hash_dim(c, dims.w[k]);
            if (!have || h < bh) { have = true; bh = h; best = k; }
        }
        if (!have) break;
        uint64_t p = dim_var_provenance(dims.w[best]);
        if (p) dump_nominal(c, p);
        dims.w[best] = 0;
    }
    words_free(&dims);
    /* render */
    Str *cls = malloc((d->n ? d->n : 1) * sizeof(Str));
    for (size_t i = 0; i < d->n; i++) {
        Str *lits = malloc((d->c[i].n ? d->c[i].n : 1) * sizeof(Str));
        for (size_t k = 0; k < d->c[i].n; k++) {
            uint64_t a = d->c[i].a[k];
            size_t mark = c->len;
            name_dim(c, a >> 1);
            canon_text(c, face ? ((a & 1) ? "=1" : "=0") : ((a & 1) ? "-" : "+"));
            lits[k].s = strdup(c->buf + mark); c->len = mark; c->buf[mark] = 0;
        }
        qsort(lits, d->c[i].n, sizeof(Str), cmp_str);
        size_t mark = c->len;
        canon_text(c, "{");
        for (size_t k = 0; k < d->c[i].n; k++) { if (k) canon_text(c, " "); canon_text(c, lits[k].s); free(lits[k].s); }
        canon_text(c, "}");
        free(lits);
        cls[i].s = strdup(c->buf + mark); c->len = mark; c->buf[mark] = 0;
    }
    qsort(cls, d->n, sizeof(Str), cmp_str);
    canon_text(c, "[");
    for (size_t i = 0; i < d->n; i++) { canon_text(c, cls[i].s); free(cls[i].s); }
    canon_text(c, "]");
    free(cls);
}
void canon_dump_face_text(Canon *c, FaceId f) { Dnf d; fc_to_dnf(f, &d); dump_dnf(c, &d, true); dnf_free(&d); }
static void dump_interval_text(Canon *c, IntervalId r) { Dnf d; iv_to_dnf(r, &d); dump_dnf(c, &d, false); dnf_free(&d); }

static size_t dump_nominal(Canon *c, uint64_t nid) {
    GROW(c->nnom, c->nnom_cap, nid, size_t);
    if (c->nnom[nid - 1]) return c->nnom[nid - 1];
    /* children first (they get lower numbers), in key order */
    size_t n; const uint64_t *w = nominal_key(nid, &n);
    for (size_t k = 0; k < n; k++) {
        uint64_t kind = w[2 * k], v = w[2 * k + 1];
        if (kind == KW_REF) canon_dump_ref(c, v);
        else if (kind == KW_DIM && dim_var_provenance(v)) dump_nominal(c, dim_var_provenance(v));
        else if (kind == KW_VAR && term_var_provenance(v)) dump_nominal(c, term_var_provenance(v));
    }
    if (c->nnom[nid - 1]) return c->nnom[nid - 1];
    size_t num = ++c->next;
    c->nnom[nid - 1] = num;
    textf(c, "#%llu N", num);
    for (size_t k = 0; k < n; k++) {
        uint64_t kind = w[2 * k], v = w[2 * k + 1];
        canon_text(c, " ");
        switch ((KeyKind)kind) {
        case KW_CONST: textf(c, "c%llu", v); break;
        case KW_REF: textf(c, "r#%llu", canon_dump_ref(c, v)); break;
        case KW_FACE: canon_dump_face_text(c, v); break;
        case KW_INTERVAL: dump_interval_text(c, v); break;
        case KW_DIM: name_dim(c, v); break;
        case KW_VAR: name_var(c, v); break;
        }
    }
    canon_text(c, "\n");
    return num;
}

typedef struct { uint64_t h1, h2; size_t k; } Ord;
static int cmp_ord(const void *a, const void *b) {
    const Ord *x = a, *y = b;
    if (x->h1 != y->h1) return x->h1 < y->h1 ? -1 : 1;
    if (x->h2 != y->h2) return x->h2 < y->h2 ? -1 : 1;
    return 0;
}

size_t canon_dump_ref(Canon *c, RefId t) {
    GROW(c->nref, c->nref_cap, t, size_t);
    if (c->nref[t - 1]) return c->nref[t - 1];
    if (ref_is_var(t)) {
        TermVarId x = ref_var_id(t);
        if (term_var_provenance(x)) dump_nominal(c, term_var_provenance(x));
        if (c->nref[t - 1]) return c->nref[t - 1];
        size_t num = ++c->next; c->nref[t - 1] = num;
        textf(c, "#%llu V ", num); name_var(c, x); canon_text(c, "\n");
        return num;
    }
    OriginId o = ref_origin(t); MapId m = ref_map(t);
    Tag tag = origin_tag(o);
    size_t nb = origin_nbinders(o), nf = origin_nfields(o);
    size_t nt = map_n_terms(m), nd = map_n_dims(m);
    /* children first: binder formals' provenance, fields in order, then map
     * entries in renaming-invariant (hash) order */
    for (size_t k = 0; k < nb; k++) {
        Binder b = origin_binder(o, (BinderSlot)k);
        uint64_t p = b.sort == S_TERM ? term_var_provenance(b.formal) : dim_var_provenance(b.formal);
        if (p) dump_nominal(c, p);
    }
    for (size_t k = 0; k < nf; k++) {
        Field f = origin_field(o, (FieldIndex)k);
        if (f.kind == F_REF) canon_dump_ref(c, f.id);
    }
    Ord *ord = malloc(((nt + nd) ? (nt + nd) : 1) * sizeof(Ord));
    for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(m, k, &x, &im); ord[k].h1 = hash_var(c, x); ord[k].h2 = canon_hash_ref(c, im); ord[k].k = k; }
    for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(m, k, &i, &im); ord[nt + k].h1 = hash_dim(c, i); ord[nt + k].h2 = canon_hash_interval(c, im); ord[nt + k].k = nt + k; }
    if (nt > 1) qsort(ord, nt, sizeof(Ord), cmp_ord);
    if (nd > 1) qsort(ord + nt, nd, sizeof(Ord), cmp_ord);
    for (size_t q = 0; q < nt; q++) { TermVarId x; RefId im; map_term_entry(m, ord[q].k, &x, &im); if (term_var_provenance(x)) dump_nominal(c, term_var_provenance(x)); canon_dump_ref(c, im); }
    if (c->nref[t - 1]) { free(ord); return c->nref[t - 1]; }
    size_t num = ++c->next; c->nref[t - 1] = num;
    textf(c, "#%llu W ", num);
    canon_text(c, tag_name(tag));
    if (tag == T_GLOBAL) { canon_text(c, ":"); canon_text(c, M.defs[origin_payload(o) - 1].name); }
    else textf(c, ":%llu", origin_payload(o));
    for (size_t k = 0; k < nb; k++) {
        Binder b = origin_binder(o, (BinderSlot)k);
        canon_text(c, b.sort == S_TERM ? " [x " : " [d ");
        if (b.sort == S_TERM) name_var(c, b.formal); else name_dim(c, b.formal);
        textf(c, " dom%llu]", b.domain_field == NO_FIELD ? 99999 : b.domain_field);
    }
    for (size_t k = 0; k < nf; k++) {
        Field f = origin_field(o, (FieldIndex)k);
        canon_text(c, " ");
        if (f.slot != NO_SLOT) textf(c, "@%llu", f.slot);
        switch (f.kind) {
        case F_REF: textf(c, "r#%llu", canon_dump_ref(c, f.id)); break;
        case F_INTERVAL: canon_text(c, "I"); dump_interval_text(c, f.id); break;
        case F_FACE: canon_text(c, "F"); canon_dump_face_text(c, f.id); break;
        }
    }
    canon_text(c, " |");
    for (size_t q = 0; q < nt; q++) { TermVarId x; RefId im; map_term_entry(m, ord[q].k, &x, &im); canon_text(c, " "); name_var(c, x); textf(c, ":=r#%llu", canon_dump_ref(c, im)); }
    for (size_t q = 0; q < nd; q++) { DimVarId i; IntervalId im; map_dim_entry(m, ord[nt + q].k - nt, &i, &im); canon_text(c, " "); name_dim(c, i); canon_text(c, ":="); dump_interval_text(c, im); }
    canon_text(c, "\n");
    free(ord);
    return num;
}

void canon_dump_result(Canon *c, const EvalResult *r) {
    switch (r->cls) {
    case R_INTRODUCTION: textf(c, "RESULT INTRO r#%llu\n", canon_dump_ref(c, r->ref)); break;
    case R_NEUTRAL: textf(c, "RESULT NEUTRAL r#%llu\n", canon_dump_ref(c, r->ref)); break;
    case R_SYSTEM:
        canon_text(c, "RESULT SYSTEM");
        for (size_t i = 0; i < r->nbr; i++) { canon_text(c, " "); canon_dump_face_text(c, r->faces[i]); textf(c, "->r#%llu", canon_dump_ref(c, r->terms[i])); }
        textf(c, " owner r#%llu\n", canon_dump_ref(c, r->ref));
        break;
    case R_NO_OBSERVATION: canon_text(c, "RESULT NO_OBSERVATION\n"); break;
    case R_INVALID: canon_text(c, "RESULT INVALID "); canon_text(c, r->message ? r->message : ""); canon_text(c, "\n"); break;
    }
}

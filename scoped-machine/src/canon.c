#define _POSIX_C_SOURCE 200809L
#include "canon.h"
#include "template.h"

/* ---- graph ---- */
typedef enum { G_REF = 1, G_NOMINAL, G_FACE, G_INTERVAL, G_CLAUSE, G_LITERAL, G_ENTRY, G_INPUT_VAR, G_INPUT_DIM, G_CONST, G_RESULT, G_KEY } GKind;

struct Canon {
    Graph *g;                 /* nodes, roots (results), setroots (keys) */
    WordMap index;            /* (kind, id) → node index + 1 */
    VEC(char *) root_labels;
    size_t *cls, *num;        /* diagnostic dump only */
    char *buf; size_t len, cap;
};

Canon *canon_new(void) { Canon *c = calloc(1, sizeof *c); require(c, "out of memory"); c->g = graph_new(); wordmap_init(&c->index); return c; }
void canon_free(Canon *c) {
    graph_free(c->g); wordmap_free(&c->index);
    for (size_t i = 0; i < c->root_labels.len; i++) free(c->root_labels.data[i]);
    vec_free(&c->root_labels);
    free(c->cls); free(c->num); free(c->buf); free(c);
}
Graph *canon_export(Canon *c) { Graph *g = c->g; c->g = graph_new(); return g; }

static void text(Canon *c, const char *s) {
    size_t n = strlen(s);
    if (c->len + n + 1 > c->cap) { size_t nc = c->cap ? c->cap * 2 : 4096; while (nc < c->len + n + 1) nc *= 2; c->buf = realloc(c->buf, nc); require(c->buf, "out of memory"); c->cap = nc; }
    memcpy(c->buf + c->len, s, n + 1); c->len += n;
}

static size_t node_new(Canon *c, GKind kind, const char *label) { return graph_node(c->g, (int)kind, label); }
static bool lookup(Canon *c, GKind kind, uint64_t id, size_t *out) {
    uint64_t k[2] = { kind, id }, v;
    if (!wordmap_get(&c->index, k, 2, &v)) return false;
    *out = (size_t)(v - 1); return true;
}
static void remember(Canon *c, GKind kind, uint64_t id, size_t idx) { uint64_t k[2] = { kind, id }; wordmap_put(&c->index, k, 2, idx + 1); }
static void add_ordered(Canon *c, size_t parent, size_t child) { graph_ordered(c->g, parent, child); }
static void add_unordered(Canon *c, size_t parent, size_t child) { graph_unordered(c->g, parent, child); }

static uint64_t input_index_term(TermVarId x) { uint64_t k = 0; for (TermVarId y = 1; y < x; y++) if (term_var_provenance(y) == 0) k++; return k; }
static uint64_t input_index_dim(DimVarId i) { uint64_t k = 0; for (DimVarId j = 1; j < i; j++) if (dim_var_provenance(j) == 0) k++; return k; }

static size_t g_ref(Canon *c, RefId t);
static size_t g_face(Canon *c, FaceId f);
static size_t g_interval(Canon *c, IntervalId r);
static size_t g_nominal(Canon *c, uint64_t nid);

/* bound atoms (§50): exact (depth, slot) labels */
static size_t g_bound(Canon *c, GKind kind, uint64_t id) {
    size_t idx; if (lookup(c, kind, id, &idx)) return idx;
    char lab[64]; snprintf(lab, sizeof lab, "%s %u/%u", kind == G_INPUT_VAR ? "bx" : "bi", (unsigned)bound_depth(id), (unsigned)bound_slot(id));
    idx = node_new(c, kind, lab); remember(c, kind, id, idx); return idx;
}
static size_t g_var(Canon *c, TermVarId x) {
    if (is_bound_id(x)) return g_bound(c, G_INPUT_VAR, x);
    uint64_t p = term_var_provenance(x);
    if (p) return g_nominal(c, p);
    size_t idx;
    if (lookup(c, G_INPUT_VAR, x, &idx)) return idx;
    char lab[64]; snprintf(lab, sizeof lab, "x%llu", (unsigned long long)input_index_term(x));
    idx = node_new(c, G_INPUT_VAR, lab); remember(c, G_INPUT_VAR, x, idx);
    return idx;
}
static size_t g_dim(Canon *c, DimVarId i) {
    if (is_bound_id(i)) return g_bound(c, G_INPUT_DIM, i);
    uint64_t p = dim_var_provenance(i);
    if (p) return g_nominal(c, p);
    size_t idx;
    if (lookup(c, G_INPUT_DIM, i, &idx)) return idx;
    char lab[64]; snprintf(lab, sizeof lab, "i%llu", (unsigned long long)input_index_dim(i));
    idx = node_new(c, G_INPUT_DIM, lab); remember(c, G_INPUT_DIM, i, idx);
    return idx;
}

static size_t g_nominal(Canon *c, uint64_t nid) {
    size_t idx;
    if (lookup(c, G_NOMINAL, nid, &idx)) return idx;
    idx = node_new(c, G_NOMINAL, "N");
    remember(c, G_NOMINAL, nid, idx);
    size_t n; const uint64_t *w = nominal_key(nid, &n);
    for (size_t k = 0; k < n; k++) {
        uint64_t kind = w[2 * k], v = w[2 * k + 1];
        size_t ch;
        char lab[64];
        switch ((KeyKind)kind) {
        case KW_CONST: snprintf(lab, sizeof lab, "c%llu", (unsigned long long)v); ch = node_new(c, G_CONST, lab); break;
        case KW_REF: ch = g_ref(c, v); break;
        case KW_FACE: ch = g_face(c, v); break;
        case KW_INTERVAL: ch = g_interval(c, v); break;
        case KW_DIM: ch = g_dim(c, v); break;
        case KW_VAR: ch = g_var(c, v); break;
        default: die("bad key kind");
        }
        add_ordered(c, idx, ch);
    }
    return idx;
}

static size_t g_dnf(Canon *c, GKind kind, uint64_t id, const Dnf *d, bool face) {
    size_t idx = node_new(c, kind, face ? "F" : "I");
    remember(c, kind, id, idx);
    for (size_t i = 0; i < d->n; i++) {
        size_t cl = node_new(c, G_CLAUSE, "C");
        for (size_t k = 0; k < d->c[i].n; k++) {
            uint64_t a = d->c[i].a[k];
            size_t lit = node_new(c, G_LITERAL, face ? ((a & 1) ? "=1" : "=0") : ((a & 1) ? "-" : "+"));
            add_ordered(c, lit, g_dim(c, a >> 1));
            add_unordered(c, cl, lit);
        }
        add_unordered(c, idx, cl);
    }
    return idx;
}
static size_t g_face(Canon *c, FaceId f) { size_t idx; if (lookup(c, G_FACE, f, &idx)) return idx; Dnf d; fc_to_dnf(f, &d); idx = g_dnf(c, G_FACE, f, &d, true); dnf_free(&d); return idx; }
static size_t g_interval(Canon *c, IntervalId r) { size_t idx; if (lookup(c, G_INTERVAL, r, &idx)) return idx; Dnf d; iv_to_dnf(r, &d); idx = g_dnf(c, G_INTERVAL, r, &d, false); dnf_free(&d); return idx; }

static size_t g_val(Canon *c, ValSort s, uint64_t id) { return s == VS_REF ? g_ref(c, id) : s == VS_INTERVAL ? g_interval(c, id) : g_face(c, id); }
/* a scope (§50): its ordered local telescope (sort, type, level, required),
 * body, result type / level and guard; bound atoms are exact labels */
static size_t g_scope(Canon *c, ScopeId S) {
    size_t idx; if (lookup(c, G_NOMINAL, S | (1ULL << 62), &idx)) return idx;
    size_t n = scope_arity(S);
    char lab[64]; snprintf(lab, sizeof lab, "SCOPE %zu lv=%llu", n, (unsigned long long)scope_level(S));
    idx = node_new(c, G_REF, lab); remember(c, G_NOMINAL, S | (1ULL << 62), idx);
    for (size_t k = 0; k < n; k++) {
        LocalDecl d = scope_local(S, k);
        char dl[64]; snprintf(dl, sizeof dl, "LOCAL %d lv=%llu", (int)d.sort, (unsigned long long)d.level);
        size_t e = node_new(c, G_ENTRY, dl);
        add_ordered(c, e, d.type ? g_ref(c, d.type) : node_new(c, G_CONST, "notype"));
        add_ordered(c, e, g_face(c, d.required));
        add_ordered(c, idx, e);
    }
    Val b = scope_body(S);
    add_ordered(c, idx, g_val(c, b.sort, b.id));
    add_ordered(c, idx, scope_type(S) ? g_ref(c, scope_type(S)) : node_new(c, G_CONST, "notype"));
    add_ordered(c, idx, g_face(c, scope_guard(S)));
    return idx;
}
/* a template view (§49): the definition name and node index label the fixed
 * node; the environment's (slot, value) entries follow in slot order */
static size_t g_tview(Canon *c, RefId t) {
    size_t idx;
    TNodeId Q = tnode_of(t); TEnvId E = tenv_of(t);
    char lab[128]; snprintf(lab, sizeof lab, "T %s:%llu %s", tdef_name(tnode_def(Q)), (unsigned long long)tnode_index(Q), tag_name(tnode_tag(Q)));
    idx = node_new(c, G_REF, lab); remember(c, G_REF, t, idx);
    size_t n = tenv_size(E);
    for (size_t k = 0; k < n; k++) {
        uint64_t slot; TVal v; tenv_entry(E, k, &slot, &v);
        char el[64]; snprintf(el, sizeof el, "Es %llu/%d", (unsigned long long)slot, (int)v.sort);
        size_t e = node_new(c, G_ENTRY, el);
        size_t ch;
        switch (v.sort) {
        case PS_REF: ch = g_ref(c, v.id); break;
        case PS_INTERVAL: ch = g_interval(c, v.id); break;
        case PS_FACE: ch = g_face(c, v.id); break;
        case PS_SCOPE: ch = g_scope(c, v.id); break;
        default: { char ll[32]; snprintf(ll, sizeof ll, "lv %llu", (unsigned long long)v.id); ch = node_new(c, G_LITERAL, ll); break; }
        }
        add_ordered(c, e, ch); add_ordered(c, idx, e);
    }
    return idx;
}
static size_t g_ref(Canon *c, RefId t) {
    size_t idx;
    if (lookup(c, G_REF, t, &idx)) return idx;
    if (ref_is_var(t)) {
        idx = node_new(c, G_REF, "V");
        remember(c, G_REF, t, idx);
        add_ordered(c, idx, g_var(c, ref_var_id(t)));
        return idx;
    }
    if (ref_is_tview(t)) return g_tview(c, t);
    OriginId o = ref_origin(t); MapId m = ref_map(t);
    Tag tag = origin_tag(o);
    char full[512]; size_t sl;
    if (tag == T_GLOBAL) sl = (size_t)snprintf(full, sizeof full, "W %s:%s", tag_name(tag), ((Def *)chunked_at(&M.defs, origin_payload(o) - 1))->name);
    else sl = (size_t)snprintf(full, sizeof full, "W %s:%llu", tag_name(tag), (unsigned long long)origin_payload(o));
    { uint64_t lv = origin_levels(o);        /* §59.1: the immutable level annotation is part of the record */
      if (lv == LEVELS_NONE) sl += (size_t)snprintf(full + sl, sizeof full - sl, " lv=-");
      else sl += (size_t)snprintf(full + sl, sizeof full - sl, " lv=%llu/%llu", (unsigned long long)levels_first(lv), (unsigned long long)levels_second(lv)); }
    size_t nb = origin_nbinders(o), nf = origin_nfields(o);
    for (size_t k = 0; k < nb && sl < 400; k++) { Binder b = origin_binder(o, (BinderSlot)k); sl += (size_t)snprintf(full + sl, sizeof full - sl, " b%d/%u", (int)b.sort, b.domain_field == NO_FIELD ? 99999u : (unsigned)b.domain_field); }
    for (size_t k = 0; k < nf && sl < 400; k++) { Field f = origin_field(o, (FieldIndex)k); sl += (size_t)snprintf(full + sl, sizeof full - sl, " f%d@%d", (int)f.kind, f.slot == NO_SLOT ? -1 : (int)f.slot); }
    idx = node_new(c, G_REF, full);
    remember(c, G_REF, t, idx);
    { FaceId declared = origin_declared_required(o);        /* §2 annotation is part of the record */
      size_t ann = declared ? g_face(c, declared) : node_new(c, G_CONST, "noreq");
      add_ordered(c, idx, ann); }
    for (size_t k = 0; k < nb; k++) {
        Binder b = origin_binder(o, (BinderSlot)k);
        add_ordered(c, idx, b.sort == S_TERM ? g_var(c, b.formal) : g_dim(c, b.formal));
    }
    for (size_t k = 0; k < nf; k++) {
        Field f = origin_field(o, (FieldIndex)k);
        size_t ch = f.kind == F_REF ? g_ref(c, f.id) : f.kind == F_INTERVAL ? g_interval(c, f.id) : g_face(c, f.id);
        add_ordered(c, idx, ch);
    }
    size_t nt = map_n_terms(m), nd = map_n_dims(m);
    for (size_t k = 0; k < nt; k++) {
        TermVarId x; RefId im; map_term_entry(m, k, &x, &im);
        size_t e = node_new(c, G_ENTRY, "Et"); add_ordered(c, e, g_var(c, x)); add_ordered(c, e, g_ref(c, im)); add_unordered(c, idx, e);
    }
    for (size_t k = 0; k < nd; k++) {
        DimVarId i; IntervalId im; map_dim_entry(m, k, &i, &im);
        size_t e = node_new(c, G_ENTRY, "Ed"); add_ordered(c, e, g_dim(c, i)); add_ordered(c, e, g_interval(c, im)); add_unordered(c, idx, e);
    }
    return idx;
}

void canon_add_result(Canon *c, const char *label, const EvalResult *r) {
    size_t idx;
    if (!r) idx = node_new(c, G_RESULT, "RESULT PENDING");
    else switch (r->cls) {
    case R_INTRODUCTION: idx = node_new(c, G_RESULT, "RESULT INTRO"); add_ordered(c, idx, g_ref(c, r->ref)); break;
    case R_NEUTRAL: idx = node_new(c, G_RESULT, "RESULT NEUTRAL"); add_ordered(c, idx, g_ref(c, r->ref)); break;
    case R_SYSTEM:
        idx = node_new(c, G_RESULT, "RESULT SYSTEM");
        for (size_t i = 0; i < r->nbr; i++) { size_t br = node_new(c, G_ENTRY, "Br"); add_ordered(c, br, g_face(c, r->faces[i])); add_ordered(c, br, g_ref(c, r->terms[i])); add_ordered(c, idx, br); }
        add_ordered(c, idx, g_ref(c, r->ref));
        break;
    case R_NO_OBSERVATION: idx = node_new(c, G_RESULT, "RESULT NO_OBSERVATION"); break;
    default: { char lab[256]; snprintf(lab, sizeof lab, "RESULT INVALID %s", r->message ? r->message : ""); idx = node_new(c, G_RESULT, lab); break; }
    }
    graph_root(c->g, idx);
    vec_push(&c->root_labels, strdup(label));
}

void canon_add_key(Canon *c, RefId ref, FaceId face, size_t req, size_t del, size_t pub, int state) {
    char lab[128]; snprintf(lab, sizeof lab, "KEY REQ=%zu DELIVER=%zu PUB=%zu state=%d", req, del, pub, state);
    size_t idx = node_new(c, G_KEY, lab);
    add_ordered(c, idx, g_ref(c, ref));
    add_ordered(c, idx, g_face(c, face));
    graph_setroot(c->g, idx);
}

/* ---- diagnostic dump: refinement classes + DFS numbering ---- */

typedef struct { size_t node; Words sig; } Sig;
static Canon *sort_ctx;
static int cmp_sig(const void *a, const void *b) {
    const Sig *x = a, *y = b;
    size_t n = x->sig.n < y->sig.n ? x->sig.n : y->sig.n;
    for (size_t i = 0; i < n; i++) if (x->sig.w[i] != y->sig.w[i]) return x->sig.w[i] < y->sig.w[i] ? -1 : 1;
    if (x->sig.n != y->sig.n) return x->sig.n < y->sig.n ? -1 : 1;
    return 0;
}
static int cmp_label_idx(const void *a, const void *b) {
    size_t x = *(const size_t *)a, y = *(const size_t *)b;
    const GNode *p = &sort_ctx->g->nodes.data[x], *q = &sort_ctx->g->nodes.data[y];
    if (p->kind != q->kind) return p->kind < q->kind ? -1 : 1;
    return strcmp(p->label, q->label);
}
static int cmp_by_cls(const void *a, const void *b) {
    size_t x = *(const size_t *)a, y = *(const size_t *)b;
    size_t cx = sort_ctx->cls[x], cy = sort_ctx->cls[y];
    return cx < cy ? -1 : cx > cy ? 1 : 0;
}

static size_t refine(Canon *c) {
    size_t n = c->g->nodes.len;
    free(c->cls); c->cls = calloc(n ? n : 1, sizeof(size_t));
    size_t *order = malloc((n ? n : 1) * sizeof(size_t));
    for (size_t i = 0; i < n; i++) order[i] = i;
    sort_ctx = c;
    qsort(order, n, sizeof(size_t), cmp_label_idx);
    size_t ncls = 0;
    for (size_t i = 0; i < n; i++) {
        if (i > 0 && cmp_label_idx(&order[i], &order[i - 1]) != 0) ncls++;
        c->cls[order[i]] = ncls + 1;
    }
    ncls = n ? ncls + 1 : 0;
    free(order);
    Sig *sigs = malloc((n ? n : 1) * sizeof(Sig));
    for (size_t round = 0; round < n + 2; round++) {
        for (size_t i = 0; i < n; i++) {
            GNode *g = &c->g->nodes.data[i];
            sigs[i].node = i; words_init(&sigs[i].sig);
            words_push(&sigs[i].sig, c->cls[i]);
            words_push(&sigs[i].sig, g->ordered.len);
            for (size_t k = 0; k < g->ordered.len; k++) words_push(&sigs[i].sig, c->cls[g->ordered.data[k]]);
            size_t base = sigs[i].sig.n;
            for (size_t k = 0; k < g->unordered.len; k++) words_push(&sigs[i].sig, c->cls[g->unordered.data[k]]);
            qsort(sigs[i].sig.w + base, g->unordered.len, sizeof(uint64_t), cmp_u64);
        }
        qsort(sigs, n, sizeof(Sig), cmp_sig);
        size_t k = 0;
        for (size_t i = 0; i < n; i++) { if (i > 0 && cmp_sig(&sigs[i], &sigs[i - 1]) != 0) k++; c->cls[sigs[i].node] = k + 1; }
        for (size_t i = 0; i < n; i++) words_free(&sigs[i].sig);
        size_t newn = n ? k + 1 : 0;
        if (newn == ncls) break;
        ncls = newn;
    }
    free(sigs);
    return ncls;
}

static size_t dump(Canon *c, size_t idx, size_t *next) {
    if (c->num[idx]) return c->num[idx];
    c->num[idx] = ++*next;
    size_t mine = c->num[idx];
    GNode *g = &c->g->nodes.data[idx];
    size_t nord = g->ordered.len, nun = g->unordered.len;
    size_t *ord = malloc((nord ? nord : 1) * sizeof(size_t));
    for (size_t k = 0; k < nord; k++) ord[k] = dump(c, c->g->nodes.data[idx].ordered.data[k], next);
    size_t *un = malloc((nun ? nun : 1) * sizeof(size_t));
    if (nun) memcpy(un, c->g->nodes.data[idx].unordered.data, nun * sizeof(size_t));
    sort_ctx = c;
    qsort(un, nun, sizeof(size_t), cmp_by_cls);
    size_t *unn = malloc((nun ? nun : 1) * sizeof(size_t));
    for (size_t k = 0; k < nun; k++) unn[k] = dump(c, un[k], next);
    g = &c->g->nodes.data[idx];
    char head[96];
    snprintf(head, sizeof head, "#%zu ", mine); text(c, head); text(c, g->label);
    for (size_t k = 0; k < nord; k++) { snprintf(head, sizeof head, " #%zu", ord[k]); text(c, head); }
    if (nun) text(c, " {");
    for (size_t k = 0; k < nun; k++) { snprintf(head, sizeof head, " #%zu", unn[k]); text(c, head); }
    if (nun) text(c, " }");
    text(c, "\n");
    free(ord); free(un); free(unn);
    return mine;
}

const char *canon_finish(Canon *c, size_t *len) {
    size_t ncls = refine(c);
    size_t n = c->g->nodes.len;
    free(c->num); c->num = calloc(n ? n : 1, sizeof(size_t));
    c->len = 0;
    size_t next = 0;
    char head[160];
    snprintf(head, sizeof head, "GRAPH nodes=%zu classes=%zu\n", n, ncls); text(c, head);
    for (size_t i = 0; i < c->g->roots.len; i++) {
        size_t num = dump(c, c->g->roots.data[i], &next);
        snprintf(head, sizeof head, "ROOT %s -> #%zu\n", c->root_labels.data[i], num); text(c, head);
    }
    size_t *ks = malloc((c->g->setroots.len ? c->g->setroots.len : 1) * sizeof(size_t));
    if (c->g->setroots.len) memcpy(ks, c->g->setroots.data, c->g->setroots.len * sizeof(size_t));
    sort_ctx = c;
    qsort(ks, c->g->setroots.len, sizeof(size_t), cmp_by_cls);
    for (size_t i = 0; i < c->g->setroots.len; i++) { size_t num = dump(c, ks[i], &next); snprintf(head, sizeof head, "KEYROOT -> #%zu\n", num); text(c, head); }
    free(ks);
    if (len) *len = c->len;
    return c->buf ? c->buf : "";
}

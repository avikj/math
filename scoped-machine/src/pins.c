/* pins.c — pin sets (pins.h): a canonical 4-ary hash trie over symbol ids,
 * one small interned record per node [PIN_NODE, level, bitmap, entries],
 * an entry a leaf (symbol, body) or a child (0, node); and the closure of an
 * observation's premises as a stepped subroutine. */
#include "pins.h"
#include "term.h"
#include "face.h"

#define PIN_NODE 0xF1A5ULL

static uint64_t node_make(uint64_t level, uint64_t bitmap, const uint64_t *ents, size_t ne) {
    uint64_t w[3 + 8];
    w[0] = PIN_NODE; w[1] = level; w[2] = bitmap;
    for (size_t q = 0; q < 2 * ne; q++) w[3 + q] = ents[q];
    return interner_intern(&M.keys, w, 3 + 2 * ne, NULL);
}
static unsigned digit(uint64_t s, uint64_t level) { return (unsigned)(s >> (2 * level)) & 3; }
static unsigned below(uint64_t bitmap, unsigned d) { return (unsigned)__builtin_popcountll(bitmap & ((1ULL << d) - 1)); }

PinSet pins_empty(void) { return node_make(0, 0, NULL, 0); }

/* two leaves from level l down to the first digit that separates them */
static uint64_t pair(uint64_t level, uint64_t s1, uint64_t b1, uint64_t s2, uint64_t b2) {
    require(level < PIN_LEVELS, "pin set depth");
    unsigned d1 = digit(s1, level), d2 = digit(s2, level);
    if (d1 != d2) {
        uint64_t e[4];
        if (d1 < d2) { e[0] = s1; e[1] = b1; e[2] = s2; e[3] = b2; } else { e[0] = s2; e[1] = b2; e[2] = s1; e[3] = b1; }
        return node_make(level, (1ULL << d1) | (1ULL << d2), e, 2);
    }
    uint64_t e[2] = { 0, pair(level + 1, s1, b1, s2, b2) };
    return node_make(level, 1ULL << d1, e, 1);
}
static uint64_t ins(uint64_t node, uint64_t s, uint64_t b) {
    size_t n; const uint64_t *w = interner_get(&M.keys, node, &n);
    require(w[0] == PIN_NODE, "not a pin set");
    uint64_t level = w[1], bm = w[2];
    size_t ne = (n - 3) / 2;
    uint64_t e[8]; for (size_t q = 0; q < 2 * ne; q++) e[q] = w[3 + q];
    unsigned d = digit(s, level), p = below(bm, d);
    if (!(bm & (1ULL << d))) {
        for (size_t q = 2 * ne; q > 2 * p; q--) e[q + 1] = e[q - 1];
        e[2 * p] = s; e[2 * p + 1] = b; bm |= 1ULL << d; ne++;
    } else if (e[2 * p] == 0) {
        e[2 * p + 1] = ins(e[2 * p + 1], s, b);
    } else if (e[2 * p] == s) {
        if (e[2 * p + 1] == b) return node;
        e[2 * p + 1] = b;
    } else {
        uint64_t c = pair(level + 1, e[2 * p], e[2 * p + 1], s, b);
        e[2 * p] = 0; e[2 * p + 1] = c;
    }
    return node_make(level, bm, e, ne);
}
PinSet pins_insert(PinSet P, SymbolId s, RefId body) { require(s >= 1, "pin of symbol 0"); return ins(P, s, body); }

bool pins_lookup(PinSet P, SymbolId s, RefId *body) {
    uint64_t node = P;
    for (;;) {
        size_t n; const uint64_t *w = interner_get(&M.keys, node, &n);
        unsigned d = digit(s, w[1]);
        if (!(w[2] & (1ULL << d))) return false;
        unsigned p = below(w[2], d);
        if (w[3 + 2 * p] == 0) { node = w[4 + 2 * p]; continue; }
        if (w[3 + 2 * p] != s) return false;
        if (body) *body = w[4 + 2 * p];
        return true;
    }
}
static size_t list(uint64_t node, SymbolId *out, size_t max, size_t at) {
    size_t n; const uint64_t *w = interner_get(&M.keys, node, &n);
    for (size_t q = 0; q < (n - 3) / 2; q++) {
        if (w[3 + 2 * q] == 0) at = list(w[4 + 2 * q], out, max, at);
        else { if (at < max) out[at] = (SymbolId)w[3 + 2 * q]; at++; }
    }
    return at;
}
size_t pins_symbols(PinSet P, SymbolId *out, size_t max) { return list(P, out, max, 0); }

void pins_iter_init(PinIter *it, PinSet P) { it->depth = 0; it->node[0] = P; it->pos[0] = 0; }
bool pins_iter_next(PinIter *it, SymbolId *s, RefId *body) {
    while (it->depth >= 0) {
        size_t n; const uint64_t *w = interner_get(&M.keys, it->node[it->depth], &n);
        size_t ne = (n - 3) / 2; unsigned p = it->pos[it->depth];
        if (p >= ne) { it->depth--; if (it->depth >= 0) it->pos[it->depth]++; continue; }
        if (w[3 + 2 * p] == 0) {
            require(it->depth < PIN_LEVELS, "pin set depth");
            it->depth++; it->node[it->depth] = w[4 + 2 * p]; it->pos[it->depth] = 0; continue;
        }
        if (s) *s = (SymbolId)w[3 + 2 * p];
        if (body) *body = w[4 + 2 * p];
        it->pos[it->depth]++;
        return true;
    }
    return false;
}

/* ---- the closure: symbols named by the roots, then by the bodies of the
 * revisions read, each symbol pinned once at the revision read then ---- */
typedef struct { WordBuf roots, queue; size_t rpos, rbase, qpos, qbase; const uint64_t *g; size_t ng, q; uint64_t P, x, kind; bool audit; } ClLoc;
static Family F_CLOSURE, F_GLOBALSP, F_EDGES;
/* pop the next word of a buffer consumed from its head (pages released) */
static bool buf_pop(WordBuf *b, size_t *pos, size_t *base, uint64_t *out) {
    if (*pos >= b->n) return false;
    if (*pos - *base == WB_PAGE) { wordbuf_drain_one(b); *base += WB_PAGE; }
    *out = b->head->w[*pos - *base]; (*pos)++;
    return true;
}
static void closure_step(Cont *k, uint64_t v) {
    ClLoc *L = FR_LOC(k, ClLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    L->P = pins_empty();
    wordbuf_init(&L->queue);
    while (buf_pop(&L->roots, &L->rpos, &L->rbase, &L->kind)) {
        buf_pop(&L->roots, &L->rpos, &L->rbase, &L->x);
        FR_AWAIT(k, r, F_GLOBALSP, L->x, L->kind + (L->audit ? 2 : 0));
        L->g = varset_get(r, &L->ng);
        for (L->q = 0; L->q < L->ng; L->q++) { wordbuf_push(&L->queue, L->g[L->q]); FR_YIELD(k); }
    }
    wordbuf_clear(&L->roots);
    while (buf_pop(&L->queue, &L->qpos, &L->qbase, &L->x)) {
        if (pins_lookup(L->P, (SymbolId)L->x, NULL)) { FR_YIELD(k); continue; }   /* already pinned: one step */
        {   RefId b = global_body((SymbolId)L->x);              /* the revision read, once */
            L->P = pins_insert(L->P, (SymbolId)L->x, b);
            L->kind = b; }
        if (L->audit) {
            FR_AWAIT(k, r, F_EDGES, L->x, L->kind);              /* type, parameter types, body */
            L->g = varset_get(r, &L->ng);
            for (L->q = 0; L->q < L->ng; L->q++) { wordbuf_push(&L->queue, L->g[L->q]); FR_YIELD(k); }
        } else if (L->kind) {
            FR_AWAIT(k, r, F_GLOBALSP, L->kind, 0);
            L->g = varset_get(r, &L->ng);
            for (L->q = 0; L->q < L->ng; L->q++) { wordbuf_push(&L->queue, L->g[L->q]); FR_YIELD(k); }
        }
        FR_YIELD(k);
    }
    wordbuf_clear(&L->queue);
    FR_FINISH(k, L->P);
    FR_END(k);
}
Cont *pins_closure_sub(const Cont *caller, WordBuf *roots) {
    Cont *c = frame_sub(F_CLOSURE, caller);
    ClLoc *L = FR_LOC(c, ClLoc); L->roots = *roots; wordbuf_init(roots); L->audit = false;
    return c;
}
static PinSet closure_root(size_t n, const RefId *refs, bool audit) {
    Cont *f = frame_new(F_CLOSURE, 0);
    ClLoc *L = FR_LOC(f, ClLoc); wordbuf_init(&L->roots); L->audit = audit;
    for (size_t q = 0; q < n; q++) if (refs[q]) { wordbuf_push(&L->roots, 0); wordbuf_push(&L->roots, refs[q]); }
    WhnfStatus st; PinSet P = frame_run(f, &st);
    require(st == W_OK, "the closure of an observation's premises did not complete");
    return P;
}
PinSet pins_current(size_t n, const RefId *refs) { return closure_root(n, refs, false); }
PinSet pins_audit(size_t n, const RefId *refs) { return closure_root(n, refs, true); }

/* pins.edges(s, body): the symbols reached by the stored syntax of s's type,
 * its parameters' types and the body revision (audit mode), as a varset */
typedef struct { size_t n, q, np; const uint64_t *ps; Join *J; uint64_t acc; } EdLoc;
static Family F_VSUNIONP;
static void edges_step(Cont *k, uint64_t v) {
    EdLoc *L = FR_LOC(k, EdLoc);
    SymbolId s = (SymbolId)k->w[0]; RefId body = k->w[1];
    FR_BEGIN(k);
    L->acc = varset_make(NULL, 0);
    L->ps = varset_get(global_params(s), &L->np);
    L->n = 1 + L->np + (body ? 1 : 0);
    L->J = join_new(k, L->n);
    for (L->q = 0; L->q < L->n; L->q++) {
        {   RefId t = L->q == 0 ? global_type(s) : L->q <= L->np ? term_var_type(L->ps[L->q - 1]) : body;
            join_request(L->J, L->q, F_GLOBALSP, t, 2); }
        if (L->q + 1 < L->n) FR_YIELD(k);
    }
    FR_JOIN(k, L->J);
    for (L->q = 0; L->q < L->n; L->q++) {
        {   size_t m; (void)varset_get(join_value(L->J, L->q), &m); if (!m) { FR_YIELD(k); continue; } }
        FR_AWAIT(k, L->acc, F_VSUNIONP, L->acc, join_value(L->J, L->q));
    }
    join_free(L->J); L->J = NULL;
    FR_FINISH(k, L->acc);
    FR_END(k);
}
void pins_families_init(void) {
    F_GLOBALSP = family_lookup("globals.of");
    require(F_GLOBALSP, "globals.of is registered first");
    F_VSUNIONP = family_lookup("varset.union");
    require(F_VSUNIONP, "set families are registered first");
    F_CLOSURE = family_define("pins.closure", closure_step, sizeof(ClLoc), false);
    F_EDGES = family_define("pins.edges", edges_step, sizeof(EdLoc), true);     /* keyed by (symbol, body revision) */
}

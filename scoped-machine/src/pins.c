/* pins.c — pin sets (pins.h): a canonical 4-ary hash trie over symbol ids,
 * one small interned record per node [PIN_NODE, level, bitmap, entries],
 * an entry a leaf (symbol, body) or a child (0, node); and the closure of an
 * observation's premises as a stepped subroutine. */
#include "pins.h"
#include "term.h"
#include "face.h"

#define PIN_NODE 0xF1A5ULL
#define PIN_LEVELS 32

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

/* ---- the closure: the symbols named by the roots, then by the declaration
 * (type, parameter types) and the body revision of each symbol reached, each
 * symbol pinned once at the revision read then. Keyed by (roots, snapshot):
 * the roots record [kind, id]* (0 a reference, 1 a scope) and the definition
 * environment snapshot it reads (§79.2: dependency validation keyed by the
 * immutable snapshot). One work queue of items (0 | 1, x) to walk and
 * (2, s) to pin. ---- */
typedef struct { WordBuf roots; size_t rpos, rbase, n, q; const uint64_t *g, *w; size_t ng; uint64_t P, x, kind; } ClLoc;
static Family F_CLOSURE, F_GLOBALSP;
/* pop the next word of a buffer consumed from its head (pages released) */
static bool buf_pop(WordBuf *b, size_t *pos, size_t *base, uint64_t *out) {
    if (*pos >= b->n) return false;
    if (*pos - *base == WB_PAGE) { wordbuf_drain_one(b); *base += WB_PAGE; }
    *out = b->head->w[*pos - *base]; (*pos)++;
    return true;
}
static void push2(WordBuf *b, uint64_t k, uint64_t x) { wordbuf_push(b, k); wordbuf_push(b, x); }
static void closure_step(Cont *k, uint64_t v) {
    ClLoc *L = FR_LOC(k, ClLoc);
    uint64_t r = 0;
    FR_BEGIN(k);
    require(k->w[1] == __atomic_load_n(&M.env_gen, __ATOMIC_ACQUIRE), "a closure of a snapshot that is no longer current");
    L->w = interner_get(&M.keys, k->w[0], &L->n);
    wordbuf_init(&L->roots);
    for (L->q = 0; L->q < L->n; L->q++) { wordbuf_push(&L->roots, L->w[L->q]); FR_YIELD(k); }
    L->P = pins_empty();
    while (buf_pop(&L->roots, &L->rpos, &L->rbase, &L->kind)) {
        buf_pop(&L->roots, &L->rpos, &L->rbase, &L->x);
        if (L->kind == 2) {
            if (pins_lookup(L->P, (SymbolId)L->x, NULL)) { FR_YIELD(k); continue; }   /* already pinned: one step */
            {   RefId b = global_body((SymbolId)L->x);              /* the revision read, once */
                L->P = pins_insert(L->P, (SymbolId)L->x, b);
                push2(&L->roots, 0, global_type((SymbolId)L->x));
                if (b) push2(&L->roots, 0, b);
                L->g = varset_get(global_params((SymbolId)L->x), &L->ng); }
            for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->roots, 0, term_var_type(L->g[L->q])); FR_YIELD(k); }
            FR_YIELD(k);
            continue;
        }
        if (!L->x) { FR_YIELD(k); continue; }
        FR_AWAIT(k, r, F_GLOBALSP, L->x, L->kind);
        L->g = varset_get(r, &L->ng);
        for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->roots, 2, L->g[L->q]); FR_YIELD(k); }
    }
    wordbuf_clear(&L->roots);
    FR_FINISH(k, L->P);
    FR_END(k);
}
Family pins_closure_family(void) { return F_CLOSURE; }
uint64_t env_snapshot(void) { return __atomic_load_n(&M.env_gen, __ATOMIC_ACQUIRE); }
PinSet pins_current(size_t n, const RefId *refs) {
    uint64_t *w = malloc((2 * n + 1) * sizeof *w); require(w, "out of memory");
    size_t m = 0;
    for (size_t q = 0; q < n; q++) if (refs[q]) { w[m++] = 0; w[m++] = refs[q]; }
    uint64_t roots = interner_intern(&M.keys, w, m, NULL);
    free(w);
    return family_call(F_CLOSURE, roots, env_snapshot());
}
void pins_families_init(void) {
    F_GLOBALSP = family_lookup("globals.of");
    require(F_GLOBALSP, "globals.of is registered first");
    F_CLOSURE = family_define("pins.closure", closure_step, sizeof(ClLoc));
}

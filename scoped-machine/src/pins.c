/* pins.c — pin sets (pins.h) and the closure of an observation's premises
 * as a stepped subroutine. A pin set is the total substitution record
 * [(symbol, PS_REF, body)*, 0] (subst.c): read and extended by the one
 * lookup and set. */
#include "pins.h"
#include "term.h"
#include "face.h"

PinSet pins_empty(void) { return env_empty(0); }

/* ---- the closure: the symbols named by the roots, then by the declaration
 * (type, parameter types) and the body revision of each symbol reached, each
 * symbol pinned once at the revision read then. Keyed by (roots, snapshot):
 * the roots record [kind, id]* (0 a reference, 1 a scope) and the definition
 * environment snapshot it reads (§79.2: dependency validation keyed by the
 * immutable snapshot). One work queue of items (0 | 1, x) to walk and
 * (2, s) to pin. ---- */
typedef struct { WordBuf roots; size_t rpos, rbase, n, q; const uint64_t *g, *w; size_t ng; uint64_t P, x, kind; } ClLoc;
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
            FR_AWAIT(k, r, F_LOOKUP, L->P, L->x);
            if (r) continue;                                     /* already pinned */
            r = global_body((SymbolId)L->x);                     /* the revision read, once */
            push2(&L->roots, 0, global_type((SymbolId)L->x));
            if (r) push2(&L->roots, 0, r);
            FR_AWAIT(k, L->P, F_SET, L->P, subst_entry(L->x, PS_REF, r));
            L->g = varset_get(global_params((SymbolId)L->x), &L->ng);
            for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->roots, 0, term_var_type(L->g[L->q])); FR_YIELD(k); }
            FR_YIELD(k);
            continue;
        }
        if (!L->x) { FR_YIELD(k); continue; }
        FR_AWAIT(k, r, F_GLOBALS, L->x, L->kind);
        L->g = varset_get(r, &L->ng);
        for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->roots, 2, L->g[L->q]); FR_YIELD(k); }
    }
    wordbuf_clear(&L->roots);
    FR_FINISH(k, L->P);
    FR_END(k);
}
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
    family_define(F_CLOSURE, "pins.closure", closure_step, sizeof(ClLoc));
}

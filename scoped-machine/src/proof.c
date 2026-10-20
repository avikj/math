/* proof.c — the proof-use boundary (proof.h). */
#include "proof.h"
#include "face.h"


/* a word stack as interned cons records [x, rest] (0 is empty) */
static void push(uint64_t *s, uint64_t x) { *s = RQ(x, *s); }
static uint64_t pop(uint64_t *s) { size_t n; const uint64_t *w = interner_get(&M.keys, *s, &n); *s = w[1]; return w[0]; }

/* proof.scc(P): Tarjan over the symbols of the pin set P. Vertex table: a
 * total substitution record s ↦ [index, low, on-stack, self-edge, edges];
 * the edges of s are the symbols its type, parameter types and pinned body
 * name. One edge, one discovery source, one pop or one member per step,
 * each table read or write one lookup or set.
 * Result [status, opaque set, recursive set, #opaque, #recursive]. */
typedef struct {
    uint64_t V, opq, rec, next, nopq, nrec, cnt, root, s, b, x, cur, d, acc, m, p, pc;
    uint64_t xr[5], dr[5];
    size_t ri, np, si; const uint64_t *ps; uint64_t dfs, stk, comp; bool cyc;
} SccLoc;
/* the vertex record at lookup position r of V */
static void vget(uint64_t V, uint64_t r, uint64_t *out) { size_t n; memcpy(out, interner_get(&M.keys, subst_value(V, r - 1), &n), 5 * sizeof *out); }
static uint64_t vent(SymbolId s, uint64_t i, uint64_t lo, uint64_t on, uint64_t self, uint64_t e) { return subst_entry(s, PS_REF, RQ(i, lo, on, self, e)); }
static void scc_step(Cont *k, uint64_t v) {
    SccLoc *L = FR_LOC(k, SccLoc);
    uint64_t P = k->w[0], r = 0;
    FR_BEGIN(k);
    L->V = L->opq = L->rec = env_empty(0);
    for (L->ri = 0; L->ri < subst_size(P); L->ri++) {
        { uint64_t s; TVal b; subst_get(P, L->ri, &s, &b); L->d = s; }
        FR_AWAIT(k, r, F_LOOKUP, L->V, L->d);
        if (r) continue;
    discover:
        /* the edges of d: its type, parameter types and pinned body */
        FR_AWAIT(k, r, F_LOOKUP, P, L->d);
        require(r, "an audited symbol outside the pin set");
        L->b = subst_value(P, r - 1);
        L->acc = set_make(NULL, 0);
        L->ps = set_get(global_params(L->d), &L->np);
        for (L->si = 0; L->si < L->np + 2; L->si++) {
            {   RefId src = L->si == 0 ? global_type(L->d) : L->si <= L->np ? term_var_type(L->ps[L->si - 1]) : L->b; L->s = src; }
            if (!L->s) { FR_YIELD(k); continue; }
            FR_AWAIT(k, r, F_GLOBALS, L->s, 0);
            FR_AWAIT(k, L->acc, F_SUNION, L->acc, r);
        }
        L->next++;
        FR_AWAIT(k, L->V, F_SET, L->V, vent(L->d, L->next, L->next, 1, 0, L->acc));
        if (!L->b) { L->nopq++; FR_AWAIT(k, L->opq, F_SET, L->opq, subst_entry(L->d, PS_REF, 1)); }
        push(&L->stk, L->d); push(&L->dfs, L->d); push(&L->dfs, 0);
        while (L->dfs) {
            L->cur = pop(&L->dfs); L->x = pop(&L->dfs);
            FR_AWAIT(k, r, F_LOOKUP, L->V, L->x);
            vget(L->V, r, L->xr);
            {   size_t ne; const uint64_t *es = set_get(L->xr[4], &ne);
                if (L->cur < ne) { L->d = es[L->cur]; push(&L->dfs, L->x); push(&L->dfs, L->cur + 1); }
                else L->d = 0; }
            if (L->d) {
                if (L->d == L->x) { FR_AWAIT(k, L->V, F_SET, L->V, vent(L->x, L->xr[0], L->xr[1], L->xr[2], 1, L->xr[4])); continue; }
                FR_AWAIT(k, r, F_LOOKUP, L->V, L->d);
                if (!r) goto discover;
                vget(L->V, r, L->dr);
                if (L->dr[2] && L->dr[0] < L->xr[1]) FR_AWAIT(k, L->V, F_SET, L->V, vent(L->x, L->xr[0], L->dr[0], L->xr[2], L->xr[3], L->xr[4]));
                continue;
            }
            /* x finished; a root pops its component, one member per step */
            L->cyc = L->xr[3] != 0; L->cnt = 0; L->root = L->xr[1] == L->xr[0];
            if (L->root) {
                do {
                    L->m = pop(&L->stk);
                    FR_AWAIT(k, r, F_LOOKUP, L->V, L->m);
                    vget(L->V, r, L->dr);
                    FR_AWAIT(k, L->V, F_SET, L->V, vent(L->m, L->dr[0], L->dr[1], 0, L->dr[3], L->dr[4]));
                    push(&L->comp, L->m); L->cnt++;
                } while (L->m != L->x);
                if (L->cnt > 1) L->cyc = true;
                while (L->comp) {
                    L->m = pop(&L->comp);
                    if (L->cyc) { L->nrec++; FR_AWAIT(k, L->rec, F_SET, L->rec, subst_entry(L->m, PS_REF, 1)); }
                    else FR_YIELD(k);
                }
            }
            if (L->dfs) {
                /* the parent's low link takes the finished vertex's */
                L->pc = pop(&L->dfs); L->p = pop(&L->dfs);
                push(&L->dfs, L->p); push(&L->dfs, L->pc);
                FR_AWAIT(k, r, F_LOOKUP, L->V, L->x);
                vget(L->V, r, L->xr);
                FR_AWAIT(k, r, F_LOOKUP, L->V, L->p);
                vget(L->V, r, L->dr);
                if (L->xr[1] < L->dr[1]) FR_AWAIT(k, L->V, F_SET, L->V, vent(L->p, L->dr[0], L->xr[1], L->dr[2], L->dr[3], L->dr[4]));
            }
        }
    }
    FR_FINISH(k, RQ(L->nrec ? PU_PENDING : L->nopq ? PU_ASSUMED : PU_CORE, L->opq, L->rec, L->nopq, L->nrec));
    FR_END(k);
}
void proof_families_init(void) {
    family_define(F_SCC, "proof.scc", scc_step, sizeof(SccLoc));
}

const char *proof_status_name(ProofStatus s) {
    switch (s) { case PU_CORE: return "CORE"; case PU_ASSUMED: return "ASSUMED"; case PU_PENDING: return "PENDING"; case PU_INVALID: return "INVALID"; case PU_UNRESOLVED: return "UNRESOLVED"; }
    return "?";
}
static SymbolId *listing(uint64_t T, size_t n) {
    SymbolId *out = malloc((n ? n : 1) * sizeof(SymbolId)); require(out, "out of memory");
    require(subst_size(T) == n, "proof-use listing");
    for (size_t q = 0; q < n; q++) { uint64_t s; TVal b; subst_get(T, q, &s, &b); out[q] = (SymbolId)s; }
    return out;
}
ProofUse proof_use(ContextId G, FaceId chi, RefId e, RefId E) {
    ProofUse out; memset(&out, 0, sizeof out); out.reason = "";
    uint64_t lv;
    CheckStatus st = check_context(G, &out.reason);
    if (st == CK_VALID) st = check_is_type(G, chi, E, &lv, &out.reason);
    if (st == CK_VALID) st = check(G, chi, e, E, &out.reason);
    if (st != CK_VALID) { out.status = st == CK_INVALID ? PU_INVALID : PU_UNRESOLVED; return out; }
    if (fc_is_false(chi)) { out.status = PU_CORE; out.reason = "a judgment local to the false face"; return out; }
    size_t nd = context_size(G), nr = 0;
    RefId *roots = malloc((nd + 2) * sizeof(RefId)); require(roots, "out of memory");
    for (size_t q = 0; q < nd; q++) { CtxDecl d = context_decl(G, q); if (d.sort == S_TERM) roots[nr++] = term_var_type(d.id); }
    roots[nr++] = E; roots[nr++] = e;
    out.revisions = pins_current(nr, roots);
    free(roots);
    WhnfStatus ws; uint64_t res = family_run_budget(F_SCC, out.revisions, 0, check_budget(), &ws);
    if (ws != W_OK) { out.status = PU_UNRESOLVED; out.reason = "unresolved: the audit did not complete"; return out; }
    size_t n; const uint64_t *w = interner_get(&M.keys, res, &n);
    out.status = (ProofStatus)w[0];
    out.reason = w[0] == PU_PENDING ? "recursive dependencies need a logical witness" : w[0] == PU_ASSUMED ? "relative to explicit opaque assumptions" : "acyclic core proof relative to the occurrence context";
    out.n_assumptions = w[3]; out.n_recursive = w[4];
    out.assumptions = listing(w[1], w[3]); out.recursive = listing(w[2], w[4]);
    return out;
}
void proof_use_free(ProofUse *u) { free(u->assumptions); free(u->recursive); u->assumptions = u->recursive = NULL; }

/* proof.c — the proof-use boundary (proof.h). */
#include "proof.h"
#include "face.h"

static uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })

/* a word stack as interned cons records [x, rest] (0 is empty) */
static void push(uint64_t *s, uint64_t x) { *s = RQ(x, *s); }
static uint64_t pop(uint64_t *s) { size_t n; const uint64_t *w = interner_get(&M.keys, *s, &n); *s = w[1]; return w[0]; }

/* proof.scc(P, S): S the symbols of P. Vertex table: a pin trie
 * s ↦ [index, low, on-stack, self-edge, edges]; the edges of s are the
 * symbols its type, parameter types and pinned body name. One edge, one
 * discovery source, one pop or one member per step.
 * Result [status, opaque trie, recursive trie, #opaque, #recursive]. */
typedef struct {
    uint64_t V, opq, rec, next, nopq, nrec, cnt, root, s, b, x, cur, d, acc, m;
    size_t ri, np, si; const uint64_t *ps; uint64_t dfs, stk, comp; bool cyc;
} SccLoc;
static Family F_SCC, Fp_GLOBALS, Fp_VSUNION;
static const uint64_t *vrec(uint64_t V, SymbolId s) { RefId r; size_t n; return pins_lookup(V, s, &r) ? interner_get(&M.keys, r, &n) : NULL; }
static uint64_t vset(uint64_t V, SymbolId s, uint64_t i, uint64_t lo, uint64_t on, uint64_t self, uint64_t e) { return pins_insert(V, s, RQ(i, lo, on, self, e)); }
static void scc_step(Cont *k, uint64_t v) {
    SccLoc *L = FR_LOC(k, SccLoc);
    uint64_t P = k->w[0], r = 0; size_t nS; const uint64_t *S = varset_get(k->w[1], &nS);
    FR_BEGIN(k);
    L->V = L->opq = L->rec = pins_empty();
    for (L->ri = 0; L->ri < nS; L->ri++) {
        if (vrec(L->V, S[L->ri])) { FR_YIELD(k); continue; }
        L->d = S[L->ri];
    discover:
        /* the edges of d: its type, parameter types and pinned body */
        {   RefId b = 0; require(pins_lookup(P, L->d, &b), "an audited symbol outside the pin set"); L->b = b; }
        L->acc = varset_make(NULL, 0);
        L->ps = varset_get(global_params(L->d), &L->np);
        for (L->si = 0; L->si < L->np + 2; L->si++) {
            {   RefId src = L->si == 0 ? global_type(L->d) : L->si <= L->np ? term_var_type(L->ps[L->si - 1]) : L->b; L->s = src; }
            if (!L->s) continue;
            FR_AWAIT(k, r, Fp_GLOBALS, L->s, 0);
            FR_AWAIT(k, L->acc, Fp_VSUNION, L->acc, r);
        }
        L->next++;
        L->V = vset(L->V, L->d, L->next, L->next, 1, 0, L->acc);
        if (!L->b) { L->opq = pins_insert(L->opq, L->d, 1); L->nopq++; }
        push(&L->stk, L->d); push(&L->dfs, L->d); push(&L->dfs, 0);
        while (L->dfs) {
            L->cur = pop(&L->dfs); L->x = pop(&L->dfs);
            {   const uint64_t *xr = vrec(L->V, L->x); size_t ne; const uint64_t *es = varset_get(xr[4], &ne);
                if (L->cur < ne) {
                    L->d = es[L->cur]; push(&L->dfs, L->x); push(&L->dfs, L->cur + 1);
                    if (L->d == L->x) L->V = vset(L->V, L->x, xr[0], xr[1], xr[2], 1, xr[4]);
                    else {
                        const uint64_t *dr = vrec(L->V, L->d);
                        if (!dr) goto discover;
                        if (dr[2] && dr[0] < xr[1]) L->V = vset(L->V, L->x, xr[0], dr[0], xr[2], xr[3], xr[4]);
                    }
                    FR_YIELD(k);
                    continue;
                } }
            /* x finished; a root pops its component, one member per step */
            {   const uint64_t *xr = vrec(L->V, L->x); L->cyc = xr[3] != 0; L->cnt = 0; L->root = xr[1] == xr[0]; }
            if (L->root) {
                do {
                    L->m = pop(&L->stk);
                    {   const uint64_t *mr = vrec(L->V, L->m); L->V = vset(L->V, L->m, mr[0], mr[1], 0, mr[3], mr[4]); }
                    push(&L->comp, L->m); L->cnt++;
                    FR_YIELD(k);
                } while (L->m != L->x);
                if (L->cnt > 1) L->cyc = true;
                while (L->comp) { L->m = pop(&L->comp); if (L->cyc) { L->rec = pins_insert(L->rec, L->m, 1); L->nrec++; } FR_YIELD(k); }
            }
            if (L->dfs) {
                uint64_t pc = pop(&L->dfs), p = pop(&L->dfs);
                const uint64_t *pr = vrec(L->V, p), *xr = vrec(L->V, L->x);
                if (xr[1] < pr[1]) L->V = vset(L->V, p, pr[0], xr[1], pr[2], pr[3], pr[4]);
                push(&L->dfs, p); push(&L->dfs, pc);
            }
            FR_YIELD(k);
        }
    }
    FR_FINISH(k, RQ(L->nrec ? PU_PENDING : L->nopq ? PU_ASSUMED : PU_CORE, L->opq, L->rec, L->nopq, L->nrec));
    FR_END(k);
}
void proof_families_init(void) {
    Fp_GLOBALS = family_lookup("globals.of"); Fp_VSUNION = family_lookup("varset.union");
    require(Fp_GLOBALS && Fp_VSUNION, "globals.of and varset.union are registered first");
    F_SCC = family_define("proof.scc", scc_step, sizeof(SccLoc));
}

const char *proof_status_name(ProofStatus s) {
    switch (s) { case PU_CORE: return "CORE"; case PU_ASSUMED: return "ASSUMED"; case PU_PENDING: return "PENDING"; case PU_INVALID: return "INVALID"; case PU_UNRESOLVED: return "UNRESOLVED"; }
    return "?";
}
static SymbolId *listing(PinSet T, size_t n) {
    SymbolId *out = malloc((n ? n : 1) * sizeof(SymbolId)); require(out, "out of memory");
    require(pins_symbols(T, out, n) == n, "proof-use listing");
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
    size_t ns = pins_symbols(out.revisions, NULL, 0);
    SymbolId *ss = listing(out.revisions, ns);
    VarSetId S = varset_make(ss, ns); free(ss);
    WhnfStatus ws; uint64_t res = family_run_budget(F_SCC, out.revisions, S, check_budget(), &ws);
    if (ws != W_OK) { out.status = PU_UNRESOLVED; out.reason = "unresolved: the audit did not complete"; return out; }
    size_t n; const uint64_t *w = interner_get(&M.keys, res, &n);
    out.status = (ProofStatus)w[0];
    out.reason = w[0] == PU_PENDING ? "recursive dependencies need a logical witness" : w[0] == PU_ASSUMED ? "relative to explicit opaque assumptions" : "acyclic core proof relative to the occurrence context";
    out.n_assumptions = w[3]; out.n_recursive = w[4];
    out.assumptions = listing(w[1], w[3]); out.recursive = listing(w[2], w[4]);
    return out;
}
void proof_use_free(ProofUse *u) { free(u->assumptions); free(u->recursive); u->assumptions = u->recursive = NULL; }

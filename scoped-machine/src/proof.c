/* proof.c — the proof-use boundary (proof.h). */
#include "proof.h"
#include "judge.h"
#include "term.h"
#include "face.h"

static uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })
static const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }

/* a stack of words in fixed-size frame-owned chunks: push and pop O(1) */
#define STK_CHUNK 500
typedef struct StkC { struct StkC *prev; size_t n; uint64_t w[STK_CHUNK]; } StkC;
typedef struct { StkC *top; } Stk;
static void stk_push(Stk *s, uint64_t x) {
    if (!s->top || s->top->n == STK_CHUNK) { StkC *c = frame_mem(sizeof *c); c->prev = s->top; c->n = 0; s->top = c; }
    s->top->w[s->top->n++] = x;
}
static uint64_t stk_pop(Stk *s) {
    uint64_t x = s->top->w[--s->top->n];
    if (!s->top->n) { StkC *c = s->top; s->top = c->prev; frame_mem_free(c); }
    return x;
}
static bool stk_empty(const Stk *s) { return !s->top; }

/* ---------------- proof.scc(Pa) ----------------
 * Tarjan over every symbol of the audited pin set (the reached graph), the
 * edges of a vertex being pins.edges(s, pinned body). The vertex table is a
 * pin trie s ↦ [index, low, on-stack, self-edge, edges]. One edge, one
 * discovery, one stack pop or one component member per step.
 * Result [status, opaque trie, recursive trie, #opaque, #recursive]. */
typedef struct {
    PinIter it; uint64_t V, opq, rec; size_t next, nopq, nrec, cnt;
    Stk dfs, stk, comp; uint64_t s, sb, x, cur, d, edges, m; bool cyc;
} SccLoc;
static Family F_SCC, F_USE, F_EDGESP;
static const uint64_t *vrec(uint64_t V, SymbolId s) { RefId r; if (!pins_lookup(V, s, &r)) return NULL; size_t n; return rget(r, &n); }
static uint64_t vset(uint64_t V, SymbolId s, uint64_t idx, uint64_t low, uint64_t on, uint64_t self, uint64_t edges) {
    return pins_insert(V, s, RQ(idx, low, on, self, edges));
}
static void scc_step(Cont *k, uint64_t v) {
    SccLoc *L = FR_LOC(k, SccLoc);
    uint64_t Pa = k->w[0];
    FR_BEGIN(k);
    L->V = pins_empty(); L->opq = pins_empty(); L->rec = pins_empty(); L->next = 0; L->nopq = 0; L->nrec = 0;
    L->dfs.top = L->stk.top = L->comp.top = NULL;
    pins_iter_init(&L->it, Pa);
    while (pins_iter_next(&L->it, (SymbolId *)&L->s, &L->sb)) {
        if (vrec(L->V, L->s)) { FR_YIELD(k); continue; }
        L->d = L->s;
        /* discover d (its revision from Pa), then run the DFS from it */
        for (;;) {
            {   RefId b = 0; require(pins_lookup(Pa, L->d, &b), "an audited symbol outside the audited pin set"); L->sb = b; }
            FR_AWAIT(k, L->edges, F_EDGESP, L->d, L->sb);
            L->next++;
            L->V = vset(L->V, L->d, L->next, L->next, 1, 0, L->edges);
            if (!L->sb) { L->opq = pins_insert(L->opq, L->d, 1); L->nopq++; }
            stk_push(&L->stk, L->d); stk_push(&L->dfs, L->d); stk_push(&L->dfs, 0);
            /* advance the DFS until a new vertex is to be discovered or it is empty */
            for (;;) {
                if (stk_empty(&L->dfs)) break;
                L->cur = stk_pop(&L->dfs); L->x = stk_pop(&L->dfs);
                {   const uint64_t *xr = vrec(L->V, L->x); size_t ne; const uint64_t *es = varset_get(xr[4], &ne);
                    if (L->cur < ne) {
                        L->d = es[L->cur];
                        stk_push(&L->dfs, L->x); stk_push(&L->dfs, L->cur + 1);
                        if (L->d == L->x) { L->V = vset(L->V, L->x, xr[0], xr[1], xr[2], 1, xr[4]); goto edge_done; }
                        {   const uint64_t *dr = vrec(L->V, L->d);
                            if (!dr) goto discover;
                            if (dr[2] && dr[0] < xr[1]) L->V = vset(L->V, L->x, xr[0], dr[0], xr[2], xr[3], xr[4]); }
                        goto edge_done;
                    } }
                /* x finished: a root pops its component, one member per step */
                {   const uint64_t *xr = vrec(L->V, L->x); L->cyc = xr[3] != 0; L->cnt = 0;
                    if (xr[1] != xr[0]) goto propagate; }
                do {
                    L->m = stk_pop(&L->stk);
                    {   const uint64_t *mr = vrec(L->V, L->m); L->V = vset(L->V, L->m, mr[0], mr[1], 0, mr[3], mr[4]); }
                    stk_push(&L->comp, L->m); L->cnt++;
                    FR_YIELD(k);
                } while (L->m != L->x);
                if (L->cnt > 1) L->cyc = true;
                while (!stk_empty(&L->comp)) {
                    L->m = stk_pop(&L->comp);
                    if (L->cyc) { L->rec = pins_insert(L->rec, L->m, 1); L->nrec++; }
                    FR_YIELD(k);
                }
            propagate:
                if (!stk_empty(&L->dfs)) {
                    uint64_t pc = stk_pop(&L->dfs), p = stk_pop(&L->dfs);
                    stk_push(&L->dfs, p); stk_push(&L->dfs, pc);
                    {   const uint64_t *pr = vrec(L->V, p), *xr = vrec(L->V, L->x);
                        if (xr[1] < pr[1]) L->V = vset(L->V, p, pr[0], xr[1], pr[2], pr[3], pr[4]); }
                }
            edge_done:
                FR_YIELD(k);
            }
            break;
        discover:
            continue;
        }
    }
    {   uint64_t status = L->nrec ? PU_PENDING : L->nopq ? PU_ASSUMED : PU_CORE;
        FR_FINISH(k, RQ(status, L->opq, L->rec, L->nopq, L->nrec)); }
    FR_END(k);
}

/* ---------------- proof.use [G, a, χ, e, E, P, Pa] ----------------
 * the context under its assumption a, the formation of E and e : E under
 * each clause of χ, the bodies of the pinned symbols, then (χ ≠ ⊥) the
 * audit. Result [status, reason, opaque trie, recursive trie, #o, #r]. */
typedef struct { uint64_t res, cl; size_t c, nc; PinIter it; SymbolId s; RefId b; } UseLoc;
static uint64_t fail_rec(uint64_t res) {
    uint64_t code = jr_code(res);
    return RQ(code == 2 ? PU_INVALID : PU_UNRESOLVED, (uint64_t)(uintptr_t)jr_why(res), pins_empty(), pins_empty(), 0, 0);
}
static void use_step(Cont *k, uint64_t v) {
    UseLoc *L = FR_LOC(k, UseLoc);
    size_t nq; const uint64_t *q = rget(k->w[0], &nq);
    uint64_t G = q[0], A = q[1], chi = q[2], e = q[3], E = q[4], P = q[5], Pa = q[6];
    FR_BEGIN(k);
    FR_AWAIT(k, L->res, judge_family(JK_CTX), RQ(G, A, P), 0);
    if (jr_code(L->res) != 1) FR_FINISH(k, fail_rec(L->res));
    FR_AWAIT(k, L->cl, judge_family(JK_CLAUSES), chi, 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
        FR_AWAIT(k, L->res, judge_family(JK_LEVEL), RQ(G, rget(L->cl, &L->nc)[L->c], E, P), 0);
        if (jr_code(L->res) != 1) FR_FINISH(k, fail_rec(L->res));
        FR_AWAIT(k, L->res, judge_family(JK_CHECK), RQ(G, rget(L->cl, &L->nc)[L->c], e, E, P), 0);
        if (jr_code(L->res) != 1) FR_FINISH(k, fail_rec(L->res));
    }
    pins_iter_init(&L->it, P);
    while (pins_iter_next(&L->it, &L->s, &L->b)) {
        FR_AWAIT(k, L->res, judge_family(JK_BODY), RQ(L->s, P), 0);
        if (jr_code(L->res) != 1) FR_FINISH(k, fail_rec(L->res));
    }
    if (fc_is_false(chi)) FR_FINISH(k, RQ(PU_CORE, (uint64_t)(uintptr_t)"a judgment local to the false face", pins_empty(), pins_empty(), 0, 0));
    FR_AWAIT(k, L->res, F_SCC, Pa, 0);
    {   size_t n; const uint64_t *w = rget(L->res, &n);
        const char *why = w[0] == PU_PENDING ? "recursive dependencies need a logical witness" : w[0] == PU_ASSUMED ? "relative to explicit opaque assumptions" : "acyclic core proof relative to the occurrence context";
        FR_FINISH(k, RQ(w[0], (uint64_t)(uintptr_t)why, w[1], w[2], w[3], w[4])); }
    FR_END(k);
}

void proof_families_init(void) {
    F_EDGESP = family_lookup("pins.edges");
    require(F_EDGESP, "pins.edges is registered first");
    F_SCC = family_define("proof.scc", scc_step, sizeof(SccLoc), true);
    F_USE = family_define("proof.use", use_step, sizeof(UseLoc), true);
}

const char *proof_status_name(ProofStatus s) {
    switch (s) { case PU_CORE: return "CORE"; case PU_ASSUMED: return "ASSUMED"; case PU_PENDING: return "PENDING"; case PU_INVALID: return "INVALID"; case PU_UNRESOLVED: return "UNRESOLVED"; }
    return "?";
}

static SymbolId *listing(PinSet T, size_t n) {
    SymbolId *out = malloc((n ? n : 1) * sizeof(SymbolId)); require(out, "out of memory");
    size_t got = pins_symbols(T, out, n); require(got == n, "proof-use listing");
    return out;
}
ProofUse proof_use(ContextId F, FaceId chi, RefId e, RefId E) {
    ProofUse out; memset(&out, 0, sizeof out);
    out.context = F; out.face = chi; out.evidence = e; out.type = E; out.reason = "";
    RefId refs[2] = { e, E };
    uint64_t G; PinSet P;
    CheckStatus st = check_root_prepare(F, chi, 2, refs, &G, &P, &out.reason);
    if (st != CK_VALID) { out.status = st == CK_INVALID ? PU_INVALID : PU_UNRESOLVED; return out; }
    size_t nd = context_size(F);
    RefId *roots = malloc((nd + 2) * sizeof(RefId)); require(roots, "out of memory");
    size_t nr = 0;
    for (size_t q = 0; q < nd; q++) { CtxDecl d = context_decl(F, q); if (d.sort == S_TERM) roots[nr++] = d.type; }
    roots[nr++] = E; roots[nr++] = e;
    out.revisions = pins_audit(nr, roots);
    free(roots);
    WhnfStatus ws;
    uint64_t res = family_run_budget(F_USE, RQ(G, context_assumption(F), chi, e, E, P, out.revisions), 0, check_budget(), &ws);
    if (ws != W_OK) { out.status = PU_UNRESOLVED; out.reason = "unresolved: the proof-use judgment did not complete"; return out; }
    size_t n; const uint64_t *w = rget(res, &n);
    out.status = (ProofStatus)w[0];
    out.reason = (const char *)(uintptr_t)w[1];
    if (!out.reason) out.reason = out.status == PU_INVALID ? "invalid" : "unresolved";
    out.n_assumptions = w[4]; out.n_recursive = w[5];
    out.assumptions = listing(w[2], w[4]); out.recursive = listing(w[3], w[5]);
    return out;
}
void proof_use_free(ProofUse *u) { free(u->assumptions); free(u->recursive); u->assumptions = u->recursive = NULL; }

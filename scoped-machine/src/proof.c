/* proof.c — the proof-use boundary (proof.h). */
#include "proof.h"
#include "judge.h"
#include "face.h"

/* proof.audit(G, e, E): the conservative stored-syntax audit, an explicitly
 * requested judgment, never a prerequisite of observation — the symbols
 * named by the context's types, E and e, then by the declaration (type,
 * parameter types) and the body of each symbol reached, each read once
 * through the request's binding view: the map symbol ↦ revision read. One
 * work item per step. */
typedef struct { WordBuf todo; size_t pos, base, q; const uint64_t *g; size_t ng; uint64_t P, x, kind, G, rev; } AuLoc;
/* pop the next word of a buffer consumed from its head (pages released) */
static bool buf_pop(WordBuf *b, size_t *pos, size_t *base, uint64_t *out) {
    if (*pos >= b->n) return false;
    if (*pos - *base == WB_PAGE) { wordbuf_drain_one(b); *base += WB_PAGE; }
    *out = b->head->w[*pos - *base]; (*pos)++;
    return true;
}
static void push2(WordBuf *b, uint64_t k, uint64_t x) { wordbuf_push(b, k); wordbuf_push(b, x); }
static void audit_step(Cont *k, uint64_t v) {
    AuLoc *L = FR_LOC(k, AuLoc);
    size_t nq; const uint64_t *q = rget(k->w[0], &nq);
    uint64_t r = 0;
    FR_BEGIN(k);
    wordbuf_init(&L->todo);
    push2(&L->todo, 0, q[1]); push2(&L->todo, 0, q[2]);
    for (L->G = q[0]; !jc_is_empty(L->G); L->G = jc_parent(L->G)) {
        {   Sort s; uint64_t id; jc_decl(L->G, &s, &id); if (s == S_TERM) push2(&L->todo, 0, term_var_type(id)); }
        FR_YIELD(k);
    }
    L->P = env_empty(0);
    while (buf_pop(&L->todo, &L->pos, &L->base, &L->kind)) {
        buf_pop(&L->todo, &L->pos, &L->base, &L->x);
        if (L->kind == 2) {                                      /* a symbol */
            FR_AWAIT(k, r, F_LOOKUP, L->P, L->x);
            if (r) continue;                                     /* already read */
            FR_AWAIT(k, L->rev, F_READ, L->x, k->view);
            require(L->rev, "an audited symbol outside the request's view");
            FR_AWAIT(k, L->P, F_SET, L->P, subst_entry(L->x, PS_REF, L->rev));
            push2(&L->todo, 0, global_type((SymbolId)L->x));
            if (revision_body(L->rev)) push2(&L->todo, 0, revision_body(L->rev));
            L->g = set_get(global_params((SymbolId)L->x), &L->ng);
            for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->todo, 0, term_var_type(L->g[L->q])); FR_YIELD(k); }
            continue;
        }
        if (!L->x) { FR_YIELD(k); continue; }
        FR_AWAIT(k, r, F_GLOBALS, L->x, L->kind);
        L->g = set_get(r, &L->ng);
        for (L->q = 0; L->q < L->ng; L->q++) { push2(&L->todo, 2, L->g[L->q]); FR_YIELD(k); }
    }
    wordbuf_clear(&L->todo);
    FR_FINISH(k, L->P);
    FR_END(k);
}


/* a word stack as interned cons records [x, rest] (0 is empty) */
static void push(uint64_t *s, uint64_t x) { *s = RQ(x, *s); }
static uint64_t pop(uint64_t *s) { size_t n; const uint64_t *w = rget(*s, &n); *s = w[1]; return w[0]; }

/* proof.scc(P): Tarjan over the symbols of the audited map P (symbol ↦
 * revision). Vertex table: a
 * total substitution record s ↦ [index, low, on-stack, self-edge, edges];
 * the edges of s are the symbols its type, parameter types and audited body
 * name. One edge, one discovery source, one pop or one member per step,
 * each table read or write one lookup or set.
 * Result [status, opaque set, recursive set, #opaque, #recursive]. */
typedef struct {
    uint64_t V, opq, rec, next, nopq, nrec, cnt, root, s, b, x, cur, d, acc, m, p, pc;
    uint64_t xr[5], dr[5];
    size_t ri, np, si; const uint64_t *ps; uint64_t dfs, stk, comp; bool cyc;
} SccLoc;
/* the vertex record at lookup position r of V */
static void vget(uint64_t V, uint64_t r, uint64_t *out) { size_t n; memcpy(out, rget(subst_value(V, r - 1), &n), 5 * sizeof *out); }
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
        /* the edges of d: its type, parameter types and audited body */
        FR_AWAIT(k, r, F_LOOKUP, P, L->d);
        require(r, "an audited symbol outside the audit");
        L->b = revision_body(subst_value(P, r - 1));
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
    family_define(F_CLOSURE, "proof.audit", audit_step, sizeof(AuLoc));
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
    uint64_t res = check_admit(AD_PROOF, context_judgment(G), chi, e, E, 0);
    if (!res) { out.status = PU_UNRESOLVED; out.reason = "unresolved: the judgment did not complete"; return out; }
    uint64_t code = rword(res, 0);
    out.revisions = rword(res, 4);
    if (code != 1) { out.status = code == 2 ? PU_INVALID : PU_UNRESOLVED; out.reason = (const char *)(uintptr_t)rword(res, 1); return out; }
    if (fc_is_false(chi)) { out.status = PU_CORE; out.reason = "a judgment local to the false face"; return out; }
    size_t n; const uint64_t *w = rget(rword(res, 5), &n);
    out.status = (ProofStatus)w[0];
    out.reason = w[0] == PU_PENDING ? "recursive dependencies need a logical witness" : w[0] == PU_ASSUMED ? "relative to explicit opaque assumptions" : "acyclic core proof relative to the occurrence context";
    out.n_assumptions = w[3]; out.n_recursive = w[4];
    out.assumptions = listing(w[1], w[3]); out.recursive = listing(w[2], w[4]);
    return out;
}
void proof_use_free(ProofUse *u) { free(u->assumptions); free(u->recursive); u->assumptions = u->recursive = NULL; }

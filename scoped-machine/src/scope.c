#include "scope.h"
#include "template.h"

/* ------------------------------------------------------------------ */
/* scope records: [n, (sort, type, level, required)*, result_sort, type, level, guard, body, support, freevars]
 * (support and free variables, bound atoms excluded, are a function of the
 * rest: scope.side forms the record from its words) */

size_t scope_arity(ScopeId S) { return (size_t)rword(S, 0); }
LocalDecl scope_local(ScopeId S, size_t k) {
    size_t n; const uint64_t *w = rget(S, &n);
    require(k < w[0], "scope slot out of range");
    LocalDecl d = { (Sort)w[1 + 4 * k], w[2 + 4 * k], w[3 + 4 * k], w[4 + 4 * k] };
    return d;
}
static const uint64_t *scope_tail(ScopeId S) { size_t n; const uint64_t *w = rget(S, &n); return w + 1 + 4 * w[0]; }
Val scope_body(ScopeId S) { const uint64_t *t = scope_tail(S); Val v = { (ValSort)t[0], t[4] }; return v; }
RefId scope_type(ScopeId S) { return scope_tail(S)[1]; }
FaceId scope_guard(ScopeId S) { return scope_tail(S)[3]; }
DimSetId scope_support(ScopeId S) { size_t n; const uint64_t *w = rget(S, &n); return w[n - 2]; }
VarSetId scope_freevars(ScopeId S) { size_t n; const uint64_t *w = rget(S, &n); return w[n - 1]; }


/* ------------------------------------------------------------------ */
/* capture: close the concrete locals of Δ into (depth, slot) atoms         */

ScopeId capture_scope(size_t n, const CaptureDecl *delta, Val body, RefId result_type, uint64_t result_level, FaceId guard) {
    Words w; words_init(&w);
    words_push(&w, n);
    for (size_t k = 0; k < n; k++) { words_push(&w, delta[k].sort); words_push(&w, delta[k].id); words_push(&w, delta[k].type); words_push(&w, delta[k].level); words_push(&w, delta[k].required); }
    words_push(&w, body.sort); words_push(&w, body.id); words_push(&w, result_type); words_push(&w, result_level); words_push(&w, guard);
    ScopeId S = capture_request(w.w, w.n);
    words_free(&w);
    return S;
}

/* ambient reindexing: free identities only */


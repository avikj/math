/* check.c — the public checking API over the judgment families (judge.c).
 *
 * A top-level request is an outside client: it pins the closure of the
 * symbols its inputs name at the revisions current when it starts (pins.h),
 * drives one judgment root over the clauses of its face (judge.every), and
 * then the body judgments of the symbols in its pin set (its dependency
 * closure; never the whole environment). A root that does not complete — a
 * judgment depending on itself, or an exhausted budget — is UNRESOLVED; its
 * work stays with the machine and is shared by later requests.
 */
#include "check.h"
#include "judge.h"
#include "pins.h"
#include "scope.h"
#include "template.h"

static size_t budget;                    /* work of a root's dependency support (0 = unlimited) */

void check_init(void) { __atomic_store_n(&budget, 0, __ATOMIC_RELEASE); }
void check_free(void) {}
void check_set_budget(size_t steps) { __atomic_store_n(&budget, steps, __ATOMIC_RELEASE); }
size_t check_budget(void) { return __atomic_load_n(&budget, __ATOMIC_ACQUIRE); }
const char *check_status_name(CheckStatus s) { return s == CK_VALID ? "VALID" : s == CK_INVALID ? "INVALID" : "UNRESOLVED"; }
const char *conv_status_name(ConvStatus s) { return s == CV_EQUAL ? "EQUAL" : s == CV_UNEQUAL ? "UNEQUAL" : "UNRESOLVED"; }

static const char *R_STUCK = "unresolved: the judgment did not complete (a cyclic or suspended dependency, or the budget)";

/* one root of a judgment family: its result record, or 0 when it did not complete */
static uint64_t run(Family f, size_t n, const uint64_t *w) {
    WhnfStatus st;
    uint64_t v = family_run_budget(f, judge_request(n, w), 0, __atomic_load_n(&budget, __ATOMIC_ACQUIRE), &st);
    return st == W_OK ? v : 0;
}
static CheckStatus ck(uint64_t res, const char **reason) {
    if (!res) { *reason = R_STUCK; return CK_UNRESOLVED; }
    uint64_t c = jr_code(res);
    if (c == 1) return CK_VALID;
    *reason = jr_why(res) ? jr_why(res) : (c == 2 ? "invalid" : "unresolved");
    return c == 2 ? CK_INVALID : CK_UNRESOLVED;
}
static ConvStatus cv(uint64_t res) { if (!res) return CV_UNRESOLVED; uint64_t c = jr_code(res); return c == 1 ? CV_EQUAL : c == 2 ? CV_UNEQUAL : CV_UNRESOLVED; }

/* the request's pins: the closure of the symbols its inputs name */
typedef struct { RefId *r; size_t n, cap; } Roots;
static void pr_ref(Roots *R, RefId t) { if (!t) return; if (R->n == R->cap) { R->cap = R->cap ? 2 * R->cap : 16; R->r = realloc(R->r, R->cap * sizeof(RefId)); require(R->r, "out of memory"); } R->r[R->n++] = t; }
static void pr_ctx(Roots *R, ContextId c) { size_t n = context_size(c); for (size_t k = 0; k < n; k++) { CtxDecl d = context_decl(c, k); if (d.sort == S_TERM) pr_ref(R, term_var_type(d.id)); } }
static PinSet pins_of(Roots *R) { PinSet P = pins_current(R->n, R->r); free(R->r); R->r = NULL; return P; }

/* the request's dependency closure: every symbol in P declares and checks */
static CheckStatus premises(PinSet P, const char **reason) {
    CheckStatus st = CK_VALID;
    for (size_t q = 0; q < subst_size(P) && st == CK_VALID; q++) { uint64_t s; TVal b; subst_get(P, q, &s, &b); uint64_t w[2] = { s, P }; st = ck(run(J_BODY, 2, w), reason); }
    return st;
}

/* a flat context as a judgment context */
static CheckStatus jctx(ContextId F, uint64_t *G, const char **reason) {
    WhnfStatus ws; *G = family_run(J_JCOF, F, 0, &ws);
    if (ws != W_OK) { *reason = "unresolved: context"; return CK_UNRESOLVED; }
    return CK_VALID;
}
/* scope: the face's dimensions, the reference's finite structure, its free
 * identities in the context */
static CheckStatus scope_ok(uint64_t G, FaceId chi, RefId t, const char **reason) { uint64_t q[3] = { G, chi, t }; return ck(run(J_SCOPE, 3, q), reason); }

/* structural validity is the judgment family judge.structure */
bool scope_validate(ScopeId S, const char **reason) { uint64_t q[3] = { 1, S, 0 }; return ck(run(J_RV, 3, q), reason) == CK_VALID; }

CheckStatus check_context(ContextId F, const char **reason) {
    Roots R = { 0 }; pr_ctx(&R, F); PinSet P = pins_of(&R);
    uint64_t G; CheckStatus st = jctx(F, &G, reason);
    if (st == CK_VALID) { uint64_t w[3] = { G, context_assumption(F), P }; st = ck(run(J_CTX, 3, w), reason); }
    if (st == CK_VALID) st = premises(P, reason);
    return st;
}

CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason) {
    Roots R = { 0 }; pr_ctx(&R, Delta); pr_ctx(&R, Gamma);
    for (size_t q = 0; q < subst_size(sigma); q++) { uint64_t x; TVal im; subst_get(sigma, q, &x, &im); if (im.sort == PS_REF) pr_ref(&R, im.id); }
    PinSet P = pins_of(&R);
    uint64_t D, G; CheckStatus st = jctx(Delta, &D, reason);
    if (st == CK_VALID) st = jctx(Gamma, &G, reason);
    if (st == CK_VALID) { uint64_t w[6] = { D, psi, sigma, G, chi, P }; st = ck(run(J_MAP, 6, w), reason); }
    if (st == CK_VALID) st = premises(P, reason);
    return st;
}

/* a judgment context back as a flat context with assumption a */


static Inference infer_pinned(ContextId F, FaceId chi, RefId t, PinSet P) {
    Inference out = { CK_VALID, 0, NULL };
    uint64_t G;
    out.st = jctx(F, &G, &out.reason);
    if (out.st == CK_VALID) out.st = scope_ok(G, chi, t, &out.reason);
    if (out.st != CK_VALID) return out;
    uint64_t w[4] = { chi, J_INFER, t, P }; uint64_t res = run(J_JOINT, 4, w);
    out.st = ck(res, &out.reason);
    if (out.st == CK_VALID) out.type = jr_a(res);
    return out;
}
Inference infer(ContextId F, FaceId chi, RefId t) {
    Roots R = { 0 }; pr_ctx(&R, F); pr_ref(&R, t); PinSet P = pins_of(&R);
    Inference out = infer_pinned(F, chi, t, P);
    if (out.st == CK_VALID) { out.st = premises(P, &out.reason); if (out.st != CK_VALID) out.type = 0; }
    return out;
}

CheckStatus check_is_type(ContextId F, FaceId chi, RefId A, uint64_t *level, const char **reason) {
    Roots R = { 0 }; pr_ctx(&R, F); pr_ref(&R, A); PinSet P = pins_of(&R);
    uint64_t G; CheckStatus st = jctx(F, &G, reason);
    if (st == CK_VALID) st = scope_ok(G, chi, A, reason);
    uint64_t lvl = 0;
    if (st == CK_VALID) {
        uint64_t w[4] = { chi, J_LEVEL, A, P }; uint64_t res = run(J_EVERY, 4, w);
        st = ck(res, reason);
        if (st == CK_VALID && !jr_b(res)) { *reason = "type lives in different universes under different clauses"; st = CK_INVALID; }
        if (st == CK_VALID) lvl = jr_a(res);
    }
    if (st == CK_VALID) st = premises(P, reason);
    if (st == CK_VALID && level) *level = lvl;
    return st;
}

CheckStatus check(ContextId F, FaceId chi, RefId t, RefId A, const char **reason) {
    Roots R = { 0 }; pr_ctx(&R, F); pr_ref(&R, t); pr_ref(&R, A); PinSet P = pins_of(&R);
    uint64_t G; CheckStatus st = jctx(F, &G, reason);
    if (st == CK_VALID) st = scope_ok(G, chi, t, reason);
    if (st == CK_VALID) st = scope_ok(G, chi, A, reason);
    if (st == CK_VALID) { uint64_t w[5] = { chi, J_CHECK, t, A, P }; st = ck(run(J_EVERY, 5, w), reason); }
    if (st == CK_VALID) st = premises(P, reason);
    return st;
}

static ConvStatus convert(ContextId F, FaceId chi, RefId t, RefId u, RefId A, bool types) {
    Roots R = { 0 }; pr_ctx(&R, F); pr_ref(&R, t); pr_ref(&R, u); pr_ref(&R, A); PinSet P = pins_of(&R);
    const char *why; uint64_t G;
    if (jctx(F, &G, &why) != CK_VALID || scope_ok(G, chi, t, &why) != CK_VALID || scope_ok(G, chi, u, &why) != CK_VALID || (A && scope_ok(G, chi, A, &why) != CK_VALID)) return CV_UNRESOLVED;
    uint64_t res;
    if (types) { uint64_t w[5] = { chi, J_CONVT, t, u, P }; res = run(J_EVERY, 5, w); }
    else { uint64_t w[6] = { chi, J_CONVt, t, u, A, P }; res = run(J_EVERY, 6, w); }
    ConvStatus out = cv(res);
    if (out == CV_EQUAL && premises(P, &why) != CK_VALID) out = CV_UNRESOLVED;
    return out;
}
ConvStatus convert_type(ContextId G, FaceId chi, RefId A, RefId B) { return convert(G, chi, A, B, 0, true); }
ConvStatus convert_term(ContextId G, FaceId chi, RefId t, RefId u, RefId A) { return convert(G, chi, t, u, A, false); }

/* checked observation: the context, the occurrence's inference and the
 * dependency closure validate the pinned revisions, and the observation
 * reads exactly those */
EvalResult observe_checked(ContextId F, RefId t, WhnfStatus *status, const char **reason) {
    Roots R = { 0 }; pr_ctx(&R, F); pr_ref(&R, t); PinSet P = pins_of(&R);
    uint64_t G; CheckStatus st = jctx(F, &G, reason);
    if (st == CK_VALID) { uint64_t w[3] = { G, context_assumption(F), P }; st = ck(run(J_CTX, 3, w), reason); }
    if (st == CK_VALID) { Inference I = infer_pinned(F, context_assumption(F), t, P); st = I.st; if (st != CK_VALID) *reason = I.reason; }
    if (st == CK_VALID) st = premises(P, reason);
    EvalResult none; memset(&none, 0, sizeof none);
    if (st == CK_INVALID) { if (status) *status = W_INVALID; return none; }
    if (st == CK_UNRESOLVED) { if (status) *status = W_STUCK; return none; }
    return whnf_pinned(t, context_assumption(F), P, status);
}

/* an explicit request for every declared symbol (not a gate: no judgment
 * waits for it) */
CheckStatus check_signature(const char **reason) {
    size_t n = global_count();
    Roots R = { 0 }; for (SymbolId s = 1; s <= n; s++) pr_ref(&R, global_ref(s));
    PinSet P = pins_of(&R);
    CheckStatus st = CK_VALID;
    for (SymbolId s = 1; s <= n && st == CK_VALID; s++) { uint64_t w[2] = { s, P }; st = ck(run(J_BODY, 2, w), reason); }
    return st;
}

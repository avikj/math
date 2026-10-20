/* check.c — the public checking API: one composite judgment, judge.admit.
 *
 * judge.admit(kind, G, χ, x, y, z) is the complete judgment a client asks
 * for: its own derivation (context, scope, typing, conversion, map or
 * checked observation, by kind) and, as premises, the validity of the body
 * of every revision that derivation read (view.reads), closed under the
 * reads of those body judgments themselves. Its result names the validated
 * revisions. A public call decodes one root of it; every internal client
 * (proof use, effect preparation) requests the same family. A root that does
 * not complete (a cyclic or suspended dependency, or the budget) is
 * UNRESOLVED; its work stays with the machine and is shared by later
 * requests. Result record [code, reason, a, b, revisions, aux].
 */
#include "check.h"
#include "judge.h"
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
enum { J_OK = 1, J_BAD = 2, J_UNR = 3 };

/* ---------------- judge.admit ---------------- */
typedef struct {
    uint64_t res, d, revs, done, fresh, x, r, aux, code, why, main[4];
    size_t nm, i, n; bool grew, conv;
} AdLoc;
#define AJAW(var, fam, a, b) do { L->main[L->nm++] = frame_request_key(k, (fam), (a), (b)); } while (0); FR_AWAIT(k, var, fam, a, b)
static void admit_step(Cont *k, uint64_t v) {
    AdLoc *L = FR_LOC(k, AdLoc);
    size_t nq; const uint64_t *q = rget(k->w[0], &nq);
    uint64_t kind = q[0], G = q[1], chi = q[2], x = q[3], y = q[4], z = q[5], r = 0;
    FR_BEGIN(k);
    L->conv = kind == AD_CONVT || kind == AD_CONVt;
    /* the derivation */
    if (kind == AD_CTX || kind == AD_OBS || kind == AD_PROOF) {
        AJAW(L->d, J_CTX, RQ(G, chi), 0);
        if (jr_code(L->d) != J_OK) goto premises;
    }
    if (kind == AD_MAP) { AJAW(L->d, J_MAP, RQ(G, chi, x, y, z), 0); goto premises; }
    if (kind == AD_BODY) { AJAW(L->d, J_BODY, RQ(x), 0); goto premises; }
    if (kind == AD_CTX) goto premises;
    FR_AWAIT(k, L->d, J_SCOPE, RQ(G, chi, x), 0);
    if (jr_code(L->d) != J_OK) goto premises;
    if (y && kind != AD_OBS && kind != AD_INFER) { FR_AWAIT(k, L->d, J_SCOPE, RQ(G, chi, y), 0); if (jr_code(L->d) != J_OK) goto premises; }
    if (z) { FR_AWAIT(k, L->d, J_SCOPE, RQ(G, chi, z), 0); if (jr_code(L->d) != J_OK) goto premises; }
    if (kind == AD_INFER || kind == AD_OBS) { AJAW(L->d, J_JOINT, RQ(chi, J_INFER, x), 0); }
    else if (kind == AD_ISTYPE) { AJAW(L->d, J_EVERY, RQ(chi, J_LEVEL, x), 0); }
    else if (kind == AD_CHECK) { AJAW(L->d, J_EVERY, RQ(chi, J_CHECK, x, y), 0); }
    else if (kind == AD_CONVT) { AJAW(L->d, J_EVERY, RQ(chi, J_CONVT, x, y), 0); }
    else if (kind == AD_CONVt) { AJAW(L->d, J_EVERY, RQ(chi, J_CONVt, x, y, z), 0); }
    else if (kind == AD_PROOF) {
        AJAW(L->d, J_EVERY, RQ(chi, J_LEVEL, y), 0);
        if (jr_code(L->d) != J_OK) goto premises;
        AJAW(L->d, J_EVERY, RQ(chi, J_CHECK, x, y), 0);
    }
    if (jr_code(L->d) != J_OK) goto premises;
    if (kind == AD_OBS) { AJAW(L->aux, F_OBS, x, observe_key(chi, 0)); }
    if (kind == AD_PROOF && !fc_is_false(chi)) { AJAW(L->aux, F_CLOSURE, RQ(G, x, y), 0); }   /* the conservative audit's revisions */
premises:
    /* the revisions the derivation read (and the audit reached), each
     * body validated, closed under the reads of those body judgments */
    L->revs = set_make(NULL, 0); L->done = set_make(NULL, 0);
    for (L->i = 0; L->i < L->nm; L->i++) {
        FR_AWAIT(k, r, F_READS, L->main[L->i], 0);
        FR_AWAIT(k, L->revs, F_SUNION, L->revs, r);
    }
    if (kind == AD_PROOF && L->aux) {
        for (L->i = 0; L->i < subst_size(L->aux); L->i++) {
            {   uint64_t s; TVal rv; subst_get(L->aux, L->i, &s, &rv); r = rv.id; }
            FR_AWAIT(k, L->revs, F_SUNION, L->revs, set_make(&r, 1));
        }
    }
    L->res = 0;
    do {
        L->grew = false; L->fresh = set_make(NULL, 0);
        for (L->i = 0; L->i < (set_get(L->revs, &L->n), L->n); L->i++) {
            {   size_t n; L->x = set_get(L->revs, &n)[L->i]; }
            FR_AWAIT(k, r, F_SCONTAINS, L->done, L->x);
            if (r == 2) continue;                                    /* set.contains: 2 member, 1 not */
            FR_AWAIT(k, L->r, J_BODY, RQ(L->x), 0);
            if (jr_code(L->r) != J_OK && !L->res) L->res = L->r;
            FR_AWAIT(k, L->done, F_SUNION, L->done, set_make(&L->x, 1));
            FR_AWAIT(k, r, F_READS, frame_request_key(k, J_BODY, RQ(L->x), 0), 0);
            FR_AWAIT(k, L->fresh, F_SUNION, L->fresh, r);
        }
        FR_AWAIT(k, r, F_SUNION, L->revs, L->fresh);
        if (r != L->revs) { L->revs = r; L->grew = true; }
    } while (L->grew);
    L->code = jr_code(L->d); L->why = (uint64_t)(uintptr_t)jr_why(L->d);
    if (L->code == J_OK && L->res) { L->code = L->conv ? J_UNR : jr_code(L->res); L->why = (uint64_t)(uintptr_t)jr_why(L->res); }
    if (kind == AD_PROOF && L->code == J_OK && L->aux) FR_AWAIT(k, L->aux, F_SCC, L->aux, 0);
    FR_FINISH(k, RQ(L->code, L->why, jr_a(L->d), jr_b(L->d), L->revs, L->aux));
    FR_END(k);
}
void check_families_init(void) { family_define(J_ADMIT, "judge.admit", admit_step, sizeof(AdLoc)); }

/* one root of judge.admit: its result record, or 0 when it did not complete */
static uint64_t admit(uint64_t kind, uint64_t G, FaceId chi, uint64_t x, uint64_t y, uint64_t z) {
    WhnfStatus st;
    uint64_t v = family_run_budget(J_ADMIT, RQ(kind, G, chi, x, y, z), 0, check_budget(), &st);
    return st == W_OK ? v : 0;
}
uint64_t check_admit(uint64_t kind, uint64_t G, FaceId chi, uint64_t x, uint64_t y, uint64_t z) { return admit(kind, G, chi, x, y, z); }
static CheckStatus ck(uint64_t res, const char **reason) {
    if (!res) { *reason = R_STUCK; return CK_UNRESOLVED; }
    uint64_t c = rword(res, 0); const char *why = (const char *)(uintptr_t)rword(res, 1);
    if (c == J_OK) return CK_VALID;
    *reason = why ? why : (c == J_BAD ? "invalid" : "unresolved");
    return c == J_BAD ? CK_INVALID : CK_UNRESOLVED;
}
static ConvStatus cv(uint64_t res) { if (!res) return CV_UNRESOLVED; uint64_t c = rword(res, 0); return c == J_OK ? CV_EQUAL : c == J_BAD ? CV_UNEQUAL : CV_UNRESOLVED; }

/* structural validity is the judgment family judge.structure */
bool scope_validate(ScopeId S, const char **reason) {
    WhnfStatus st; uint64_t v = family_run_budget(J_RV, judge_request(3, (uint64_t[]){ 1, S, 0 }), 0, check_budget(), &st);
    if (st != W_OK) { *reason = R_STUCK; return false; }
    if (jr_code(v) != J_OK) { *reason = jr_why(v); return false; }
    return true;
}

CheckStatus check_context(ContextId F, const char **reason) { return ck(admit(AD_CTX, context_judgment(F), context_assumption(F), 0, 0, 0), reason); }
CheckStatus check_map(ContextId Delta, FaceId psi, MapId sigma, ContextId Gamma, FaceId chi, const char **reason) {
    return ck(admit(AD_MAP, context_judgment(Delta), psi, sigma, context_judgment(Gamma), chi), reason);
}
Inference infer(ContextId F, FaceId chi, RefId t) {
    Inference out = { CK_VALID, 0, NULL };
    uint64_t res = admit(AD_INFER, context_judgment(F), chi, t, 0, 0);
    out.st = ck(res, &out.reason);
    if (out.st == CK_VALID) out.type = rword(res, 2);
    return out;
}
CheckStatus check_is_type(ContextId F, FaceId chi, RefId A, uint64_t *level, const char **reason) {
    uint64_t res = admit(AD_ISTYPE, context_judgment(F), chi, A, 0, 0);
    CheckStatus st = ck(res, reason);
    if (st == CK_VALID && !rword(res, 3)) { *reason = "type lives in different universes under different clauses"; st = CK_INVALID; }
    if (st == CK_VALID && level) *level = rword(res, 2);
    return st;
}
CheckStatus check(ContextId F, FaceId chi, RefId t, RefId A, const char **reason) { return ck(admit(AD_CHECK, context_judgment(F), chi, t, A, 0), reason); }
ConvStatus convert_type(ContextId F, FaceId chi, RefId A, RefId B) { return cv(admit(AD_CONVT, context_judgment(F), chi, A, B, 0)); }
ConvStatus convert_term(ContextId F, FaceId chi, RefId t, RefId u, RefId A) { return cv(admit(AD_CONVt, context_judgment(F), chi, t, u, A)); }

/* checked observation: the context, the occurrence's inference and its
 * observation, with the bodies all three read validated */
EvalResult observe_checked(ContextId F, RefId t, WhnfStatus *status, const char **reason) {
    uint64_t res = admit(AD_OBS, context_judgment(F), context_assumption(F), t, 0, 0);
    CheckStatus st = ck(res, reason);
    EvalResult none; memset(&none, 0, sizeof none);
    if (st == CK_INVALID) { if (status) *status = W_INVALID; return none; }
    if (st == CK_UNRESOLVED) { if (status) *status = W_STUCK; return none; }
    EvalResult out = res_get(rword(res, 5));
    if (status) *status = out.cls == R_NO_OBSERVATION ? W_NO_OBSERVATION : out.cls == R_INVALID ? W_INVALID : W_OK;
    return out;
}

/* an explicit request for the body of every declared symbol at its current
 * revision (not a gate: no judgment waits for it) */
CheckStatus check_signature(const char **reason) {
    uint64_t V = view_current(); CheckStatus st = CK_VALID;
    for (size_t q = 0; q < subst_size(V) && st == CK_VALID; q++) { uint64_t s; TVal rv; subst_get(V, q, &s, &rv); st = ck(admit(AD_BODY, 0, 0, rv.id, 0, 0), reason); }
    return st;
}

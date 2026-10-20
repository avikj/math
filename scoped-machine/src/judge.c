/* judge.c — checking and conversion as frame families.
 *
 * Every judgment is a family keyed by its request record: its premises are
 * awaited requests of other judgment, evaluation and construction families,
 * independent ones launched and then awaited. Judgments that observe are
 * relative (eval.h): resolved under the requester's binding view, their
 * nodes keyed without it. One judgment is executed once and shared by every
 * requester. A judgment that depends on itself is an unresolved dependency
 * of the protocol; the one resolution rule is the declaration of a global
 * symbol: inference of an occurrence of s requires only that s's declaration
 * forms (decl), never its body, so recursion through bodies is no cycle. The
 * bodies a derivation actually unfolded are its premises in judge.admit.
 *
 * Contexts inside judgments are cons records [JC, parent, sort, id, type,
 * index]: the index (a substitution record over 2x / 2j+1) answers declaration
 * lookups in bounded work; a prefix context is the parent; the face is
 * carried in the request, not in the context.
 *
 * Results are records [code, reason, a, b, c]: code 1 VALID/EQUAL,
 * 2 INVALID/UNEQUAL, 3 UNRESOLVED; reason a static or session diagnostic.
 */
#include "judge.h"
#include "check.h"
#include "template.h"
#include "scope.h"
#include "lib.h"

/* ---------------- records ---------------- */
uint64_t judge_res(uint64_t code, const char *why, uint64_t a, uint64_t b, uint64_t c) { return RQ(code, (uint64_t)(uintptr_t)why, a, b, c); }
uint64_t jr_code(uint64_t v) { return rword(v, 0); }
const char *jr_why(uint64_t v) { return (const char *)(uintptr_t)rword(v, 1); }
uint64_t jr_a(uint64_t v) { return rword(v, 2); }
uint64_t jr_b(uint64_t v) { return rword(v, 3); }
uint64_t jr_c(uint64_t v) { return rword(v, 4); }
#define J_OK 1
#define J_BAD 2
#define J_UNR 3
#define DONE(code, why, a, b, c) FR_FINISH(k, judge_res((code), (why), (a), (b), (c)))
#define OK0() DONE(J_OK, NULL, 0, 0, 0)
#define BAD(why) DONE(J_BAD, (why), 0, 0, 0)
#define UNR(why) DONE(J_UNR, (why), 0, 0, 0)
/* pass a non-VALID sub-verdict through (with its reason, or a replacement) */
#define PASS(res) do { if (jr_code(res) != J_OK) DONE(jr_code(res), jr_why(res), 0, 0, 0); } while (0)

/* session diagnostics: immutable strings reachable for the process lifetime */
/* a diagnostic composed inside a step: its text as an interned record of
 * NUL-padded words (interned by the stepped subroutine) */
static void diag_words(WordBuf *wb, const char *text) {
    size_t n = strlen(text) + 1;
    wordbuf_init(wb);
    for (size_t i = 0; i < n; i += 8) { uint64_t w = 0; memcpy(&w, text + i, n - i < 8 ? n - i : 8); wordbuf_push(wb, w); }
}
static const char *diag_text(uint64_t rec) { size_t n; return (const char *)rget(rec, &n); }

/* ---------------- contexts ----------------
 * A judgment context is the record [tag, parent, sort, id, index]: one
 * declaration over its prefix. An occurrence context (term.h) is the pair
 * [judgment context, assumption]. */
#define JC_TAG 0x7C7CULL
/* [tag, parent, sort, id, index]: a variable's type is its own; the index
 * is the total substitution record of the declared identities (id, sort, 0) */
uint64_t jc_empty(void) { return RQ(JC_TAG, 0, 0, 0, env_empty(0)); }
static const uint64_t *jcw(uint64_t G) { size_t n; const uint64_t *w = rget(G, &n); require(n == 5 && w[0] == JC_TAG, "not a judgment context"); return w; }
uint64_t jc_parent(uint64_t G) { return jcw(G)[1]; }
bool jc_is_empty(uint64_t G) { return jcw(G)[1] == 0 && jcw(G)[2] == 0; }
void jc_decl(uint64_t G, Sort *sort, uint64_t *id) { const uint64_t *w = jcw(G); *sort = (Sort)w[2]; *id = w[3]; }
static uint64_t jc_index(uint64_t G) { return jcw(G)[4]; }
/* whether lookup position r of G's index is a declaration of sort */
static bool jc_found(uint64_t G, uint64_t r, Sort sort) { if (!r) return false; uint64_t id; TVal e; subst_get(jc_index(G), r - 1, &id, &e); return (Sort)e.sort == sort; }
/* jc.ext(G, [id, sort, 0]): G extended by one declaration */
static void jcext_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    FR_AWAIT(k, r, F_SET, jc_index(k->w[0]), k->w[1]);
    { size_t n; const uint64_t *e = rget(k->w[1], &n); FR_FINISH(k, RQ(JC_TAG, k->w[0], e[1], e[0], r)); }
    FR_END(k);
}

/* the occurrence contexts (host) */
static uint64_t jc_host_ext(uint64_t G, Sort sort, uint64_t id) { return family_call(J_EXT, G, subst_entry(id, sort, 0)); }
static ContextId ctx_pair(uint64_t G, FaceId a) { uint64_t w[2] = { G, a }; return interner_intern(&M.keys, w, 2, NULL); }
uint64_t context_judgment(ContextId c) { return rword(c, 0); }
FaceId context_assumption(ContextId c) { return rword(c, 1); }
ContextId context_make(size_t n, const CtxDecl *decls, FaceId assumption) {
    uint64_t G = jc_empty();
    for (size_t k = 0; k < n; k++) G = jc_host_ext(G, decls[k].sort, decls[k].id);
    return ctx_pair(G, assumption);
}
size_t context_size(ContextId c) { size_t n = 0; for (uint64_t G = context_judgment(c); !jc_is_empty(G); G = jc_parent(G)) n++; return n; }
ContextId context_extend_term(ContextId c, TermVarId x) { return ctx_pair(jc_host_ext(context_judgment(c), S_TERM, x), context_assumption(c)); }
ContextId context_extend_dim(ContextId c, DimVarId i) { return ctx_pair(jc_host_ext(context_judgment(c), S_DIM, i), context_assumption(c)); }
ContextId context_restrict(ContextId c, FaceId phi) { return ctx_pair(context_judgment(c), fc_meet(context_assumption(c), phi)); }

/* ---------------- families used ---------------- */

/* one locals record for every judgment frame */
typedef struct {
    uint64_t x, y, z, u, a0, a1, a2, a3, a4, a5, T, D, PP, G2, l1, l2, res, cl, tag, lv, m, w0;
    size_t q, n, nc, c, i, j2, d, dn;
    const uint64_t *lw;
    uint64_t r1, r2;
    WordBuf wb, wc; bool created;
} JL;
#define JLOC JL *L = FR_LOC(k, JL); uint64_t r = 0; size_t nq_; const uint64_t *q = rget(k->w[0], &nq_); (void)q; (void)r
#define JAW(var, fam, req) FR_AWAIT(k, var, fam, req, 0)
#define R1 res_get(L->r1)
#define R2 res_get(L->r2)
/* a local judgment [χ, subjects…] is keyed at (π_S χ, subjects…), S the
 * support of its subjects (§5 projection theorem), as whnf.observe keys whnf */
typedef struct { uint64_t s, c; size_t i; } ReqLoc;
static void jreq_step(Cont *k, uint64_t v) {
    ReqLoc *L = FR_LOC(k, ReqLoc); uint64_t r = 0; size_t n; const uint64_t *q = rget(k->w[0], &n);
    FR_BEGIN(k);
    L->s = ref_support(q[1]);
    for (L->i = 2; L->i < n; L->i++) FR_AWAIT(k, L->s, F_SUNION, L->s, ref_support(q[L->i]));
    FR_AWAIT(k, L->c, F_FCPROJ, q[0], L->s);
    if (L->c != q[0]) { uint64_t w[8]; memcpy(w, q, n * sizeof *w); w[0] = L->c; k->w[0] = rq(n, w); }
    FR_AWAIT(k, r, (Family)k->w[1], k->w[0], 0);
    FR_FINISH(k, r);
    FR_END(k);
}
static Cont *jreq_sub(const Cont *k, Family f, uint64_t req) { Cont *c = frame_sub(J_REQ, k); c->w[0] = req; c->w[1] = f; return c; }
#define JRQ(var, fam, req) FR_CALL(k, var, jreq_sub(k, fam, req))

static uint64_t dim_at(DimVarId j, IntervalId r) { return re_key(map_single_dim(j, r)); }   /* the traversal j ↦ r */
static TermVarId conv_var(RefId l, RefId rr, RefId head, uint64_t slot, RefId type) {
    KeyWord kw[5] = { { KW_CONST, 5000 }, { KW_REF, l }, { KW_REF, rr }, { KW_REF, head }, { KW_CONST, slot } };
    return fresh_term_keyed(kw, 5, type);
}
static DimVarId conv_dim(RefId l, RefId rr, uint64_t slot) {
    KeyWord kw[4] = { { KW_CONST, 5001 }, { KW_REF, l }, { KW_REF, rr }, { KW_CONST, slot } };
    return fresh_dim_keyed(kw, 4);
}
static bool level_ok1(uint64_t levels, uint64_t i) { return levels_first(levels) == i; }
static bool level_ok2(uint64_t levels, uint64_t i, uint64_t j) { return levels_first(levels) == i && levels_second(levels) == j; }
static const char *level_why(uint64_t levels, const char *differs) { return levels == LEVELS_NONE || levels_first(levels) == LEVEL_NONE ? "missing universe annotation at a required type position (§59.1)" : differs; }

/* every(φ, f, args…): the judgment f at [c, args…] for every clause c of
 * φ — the clauses' requests launched, then awaited in clause order. The
 * result: the first invalid one, else the first unresolved one, else valid
 * with a the clauses' common a, b = 1 when they all agree (vacuously for no
 * clause) and c the record [clause, a]*. */
static uint64_t every_req(const uint64_t *q, size_t n, uint64_t c) { uint64_t w[8]; w[0] = c; memcpy(w + 1, q + 2, (n - 2) * sizeof *w); return rq(n - 1, w); }
static void every_step(Cont *k, uint64_t v) {
    JLOC;   /* q: φ, f, args… */
    FR_BEGIN(k);
    FR_AWAIT(k, L->cl, J_CLAUSES, q[0], 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) { family_launch(J_REQ, every_req(q, nq_, rget(L->cl, &L->nc)[L->c]), q[1]); FR_YIELD(k); }
    /* every clause awaited before the record is built: no buffer is live
     * across a wait that can expose a revision read */
    L->res = 0; L->y = 1; L->d = 0;
    for (L->c = 0; L->c < L->nc; L->c++) {
        FR_AWAIT(k, L->x, J_REQ, every_req(q, nq_, rget(L->cl, &L->nc)[L->c]), q[1]);
        if (jr_code(L->x) == J_BAD) { if (!L->res || jr_code(L->res) != J_BAD) L->res = L->x; }
        else if (jr_code(L->x) == J_UNR) { if (!L->res) L->res = L->x; }
        else if (L->d++ == 0) L->T = jr_a(L->x);
        else if (jr_a(L->x) != L->T) L->y = 0;
    }
    if (L->res) FR_FINISH(k, L->res);
    wordbuf_init(&L->wb);
    for (L->c = 0; L->c < L->nc; L->c++) {
        FR_AWAIT(k, L->x, J_REQ, every_req(q, nq_, rget(L->cl, &L->nc)[L->c]), q[1]);
        wordbuf_push(&L->wb, rget(L->cl, &L->nc)[L->c]); wordbuf_push(&L->wb, jr_a(L->x));
    }
    FR_CALL(k, L->z, intern_sub(k, &M.keys, &L->wb, &L->created));
    DONE(J_OK, NULL, L->d ? L->T : 0, L->y, L->z);
    FR_END(k);
}
#define EVERY(var, face, fam, ...) JAW(var, J_EVERY, RQ(face, fam, __VA_ARGS__))
#define ALL_OR(res, bad, unr) do { if (jr_code(res) == J_BAD) BAD(bad); if (jr_code(res) == J_UNR) UNR(unr); } while (0)
/* joint(φ, f, args…): the clauses' common reference when there is a clause
 * and they agree, else the system of the clauses' references */
static void joint_step(Cont *k, uint64_t v) {
    JLOC;
    FR_BEGIN(k);
    FR_AWAIT(k, L->res, J_EVERY, k->w[0], 0);
    PASS(L->res);
    L->lw = rget(jr_c(L->res), &L->n);
    if (jr_b(L->res) && L->n) DONE(J_OK, NULL, jr_a(L->res), 0, 0);
    creq_system_begin(&L->wb, L->n / 2);
    for (L->i = 0; L->i < L->n; L->i += 2) { L->lw = rget(jr_c(L->res), &L->n); creq_system_branch(&L->wb, L->lw[L->i], L->lw[L->i + 1]); FR_YIELD(k); }
    wordbuf_push(&L->wb, 0);
    FR_CALL(k, r, construct_buf_sub(k, &L->wb));
    DONE(J_OK, NULL, r, 0, 0);
    FR_END(k);
}

/* ---------------- faces ---------------- */
/* clauses(φ): the list record of φ's clauses, each a one-clause face (a
 * clause of a canonical DNF is canonical: its literals, then the separator) */
static void clauses_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL); uint64_t r = 0;
    FR_BEGIN(k);
    L->lw = rget(k->w[0], &L->n);
    wordbuf_init(&L->wb);
    L->i = 0;
    while (L->i < L->n) {
        wordbuf_init(&L->wc);
        while (L->lw[L->i] != DNF_SEP) { wordbuf_push(&L->wc, L->lw[L->i]); L->i++; FR_YIELD(k); }
        wordbuf_push(&L->wc, DNF_SEP); L->i++;
        FR_CALL(k, r, intern_sub(k, &M.keys, &L->wc, &L->created));
        wordbuf_push(&L->wb, r);
    }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}
/* dims_in(G, S): every dimension of the set S is declared in G (1) or not (2) */
static void dimsin_step(Cont *k, uint64_t v) {
    JLOC;
    FR_BEGIN(k);
    L->lw = set_get(q[1], &L->n);
    for (L->i = 0; L->i < L->n; L->i++) {
        FR_AWAIT(k, r, F_LOOKUP, jc_index(q[0]), L->lw[L->i]);
        if (!jc_found(q[0], r, S_DIM)) FR_FINISH(k, J_BAD);
    }
    FR_FINISH(k, J_OK);
    FR_END(k);
}
/* the declared dimensions of a context */
static void jdims_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    if (jc_is_empty(k->w[0])) FR_FINISH(k, set_make(NULL, 0));
    FR_AWAIT(k, r, J_JDIMS, jc_parent(k->w[0]), 0);
    {   Sort so; uint64_t id; jc_decl(k->w[0], &so, &id);
        if (so != S_DIM) FR_FINISH(k, r);
        k->w[2] = set_make(&id, 1); }
    FR_AWAIT(k, r, F_SUNION, r, k->w[2]);
    FR_FINISH(k, r);
    FR_END(k);
}
/* scope(G, χ, t): the face's dimensions, the reference's finite structure,
 * its free variables and dimensions are declared in G */
static void scope_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, χ, t */
    FR_BEGIN(k);
    FR_AWAIT(k, L->y, F_DIMS, q[1], 0);
    JAW(r, J_DIMSIN, RQ(q[0], L->y));
    if (r != J_OK) BAD("face mentions an undeclared dimension");
    JAW(L->res, J_RV, RQ(0, q[2], 0));
    PASS(L->res);
    L->lw = set_get(ref_freevars(q[2]), &L->n);
    for (L->i = 0; L->i < L->n; L->i++) {
        FR_AWAIT(k, r, F_LOOKUP, jc_index(q[0]), L->lw[L->i]);
        if (!jc_found(q[0], r, S_TERM)) BAD("unbound variable");
    }
    JAW(r, J_DIMSIN, RQ(q[0], ref_support(q[2])));
    if (r != J_OK) BAD("unbound dimension");
    OK0();
    FR_END(k);
}
/* gctx(s): the parameter context of a global — its dimensions, then its
 * term parameters in id order (dependency order: a variable's id exceeds
 * those its type mentions) */
static void gctx_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    FR_BEGIN(k);
    L->x = jc_empty();
    for (L->lw = set_get(global_dims((SymbolId)k->w[0]), &L->n), L->i = 0; L->i < L->n; L->i++) FR_AWAIT(k, L->x, J_EXT, L->x, subst_entry(L->lw[L->i], S_DIM, 0));
    for (L->lw = set_get(global_params((SymbolId)k->w[0]), &L->n), L->i = 0; L->i < L->n; L->i++) FR_AWAIT(k, L->x, J_EXT, L->x, subst_entry(L->lw[L->i], S_TERM, 0));
    FR_FINISH(k, L->x);
    FR_END(k);
}
/* tel(Q, b): a construction node's parameter telescope as a scope record —
 * its parameters at their closed types and guards, and (b = 1) its binder's
 * local — the binder its field constants are closed under */
static void ntel_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    TNodeId Q = k->w[0];
    FR_BEGIN(k);
    L->n = tnode_nparams(Q);
    L->i = k->w[1] && tnode_nbinders(Q) ? 1 : 0;
    wordbuf_init(&L->wb); wordbuf_push(&L->wb, L->n + L->i);
    for (L->q = 0; L->q < L->n; L->q++) {
        {   PSort so; RefId ty; FaceId g; tnode_param(Q, L->q, &so, &ty, &g);
            wordbuf_push(&L->wb, so == PS_INTERVAL ? S_DIM : S_TERM); wordbuf_push(&L->wb, ty); wordbuf_push(&L->wb, LEVEL_NONE); wordbuf_push(&L->wb, g ? g : fc_true()); }
        FR_YIELD(k);
    }
    if (L->i) { wordbuf_push(&L->wb, tnode_binder_sort(Q, 0)); wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, LEVEL_NONE); wordbuf_push(&L->wb, fc_true()); }
    wordbuf_push(&L->wb, VS_FACE); wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, LEVEL_NONE); wordbuf_push(&L->wb, fc_true()); wordbuf_push(&L->wb, fc_true());
    FR_CALL(k, L->x, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_FINISH(k, L->x);
    FR_END(k);
}
/* open(S, key): the telescope of scope record S at fresh locals keyed by
 * (key, S, slot), each declared at its type applied to the environment of
 * the earlier ones: [ids, environment, judgment context] */
static void open_step(Cont *k, uint64_t v) {
    JLOC;   /* q: S, key */
    ScopeId S = q[0];
    FR_BEGIN(k);
    L->n = scope_arity(S); L->G2 = jc_empty(); L->m = env_empty(0);
    wordbuf_init(&L->wc);
    for (L->i = 0; L->i < L->n; L->i++) {
        {   LocalDecl d = scope_local(S, L->i); L->tag = d.sort; L->T = d.type; L->a0 = d.required; }
        if (L->tag == S_DIM) {
            {   KeyWord kw[4] = { { KW_CONST, 9000 }, { KW_CONST, q[1] }, { KW_CONST, S }, { KW_CONST, L->i } };
                L->x = fresh_dim_keyed(kw, 4); L->z = iv_var(L->x); }
        } else {
            FR_AWAIT(k, L->T, F_TREF, L->T, apply_key(L->m));
            FR_AWAIT(k, L->a0, F_TFC, L->a0, apply_key(L->m));
            {   KeyWord kw[4] = { { KW_CONST, 9000 }, { KW_CONST, q[1] }, { KW_CONST, S }, { KW_CONST, L->i } };
                L->x = fresh_term_keyed_req(kw, 4, L->T, L->a0); }
            FR_AWAIT(k, L->z, F_REFVAR, L->x, 0);
        }
        wordbuf_push(&L->wc, L->x);
        FR_AWAIT(k, L->G2, J_EXT, L->G2, subst_entry(L->x, L->tag, 0));
        FR_AWAIT(k, L->m, F_SET, L->m, subst_entry(L->i, L->tag == S_DIM ? PS_INTERVAL : PS_REF, L->z));
    }
    FR_CALL(k, L->a1, intern_sub(k, &M.keys, &L->wc, &L->created));
    FR_FINISH(k, RQ(L->a1, L->m, L->G2));
    FR_END(k);
}
/* generic(Q): a construction node at its opened parameter telescope:
 * [context, required face, instance, list of the fresh identities] */
static void generic_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    TNodeId Q = k->w[0];
    FR_BEGIN(k);
    FR_AWAIT(k, L->T, J_NTEL, Q, 0);
    FR_AWAIT(k, L->x, J_OPEN, RQ(L->T, 0x93), 0);
    { size_t n; const uint64_t *w = rget(L->x, &n); L->a3 = w[0]; L->m = w[1]; L->G2 = w[2]; }
    FR_AWAIT(k, L->a1, F_TFC, tnode_const_required(Q), apply_key(L->m));
    FR_AWAIT(k, L->a2, F_TVMAKE, Q, L->m);
    FR_FINISH(k, RQ(L->G2, L->a1, L->a2, L->a3));
    FR_END(k);
}
/* gmap(t): the substitution of the generic identities of t's node by t's
 * environment (the substitution lemma's map) */
static void gmap_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    RefId t = k->w[0];
    FR_BEGIN(k);
    FR_AWAIT(k, L->x, J_GENERIC, ref_tnode(t), 0);
    { L->a3 = rword(L->x, 3); }
    L->m = map_identity(); L->n = tnode_nparams(ref_tnode(t));
    for (L->i = 0; L->i < L->n; L->i++) {
        {   size_t n; const uint64_t *ids = rget(L->a3, &n);
            uint64_t slot; TVal val; subst_get(ref_tenv(t), L->i, &slot, &val);
            L->y = subst_entry(ids[L->i], val.sort, val.id); }
        FR_AWAIT(k, L->m, F_SET, L->m, L->y);
    }
    FR_FINISH(k, L->m);
    FR_END(k);
}
/* observe T under C and require an introduction with tag `want`:
 * [code, reason, the observed reference] */
static void obshead_step(Cont *k, uint64_t v) {
    JLOC;
    FR_BEGIN(k);
    FR_AWAIT(k, L->r1, F_OBS, q[1], observe_key(q[0], 0));
    if (R1.cls == R_INVALID || R1.cls == R_NO_OBSERVATION) BAD(R1.message ? R1.message : "invalid observation");
    if (R1.cls != R_INTRODUCTION) BAD("expected a type former, found a neutral or system");
    if (ref_tag(R1.ref) != (Tag)q[2]) BAD("type former mismatch");
    DONE(J_OK, NULL, R1.ref, 0, 0);
    FR_END(k);
}
/* the universe level of a type under a clause: [code, reason, level] */
static void level_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A */
    FR_BEGIN(k);
    JRQ(L->res, J_INFER, RQ(q[0], q[1]));
    PASS(L->res);
    JAW(L->res, J_OBSHEAD, RQ(q[0], jr_a(L->res), T_UNIVERSE));
    if (jr_code(L->res) == J_BAD) BAD("not a type: its type is not a universe");
    PASS(L->res);
    FR_AWAIT(k, r, F_HEAD, jr_a(L->res), 0);
    DONE(J_OK, NULL, r, 0, 0);
    FR_END(k);
}
/* Equiv(l, m, X, Y): the library program (one interpretation) */
static void equiv_step(Cont *k, uint64_t v) {
    JLOC;   /* q: l, m, X, Y */
    FR_BEGIN(k);
    {   TVal a[4] = { { PS_LEVEL, q[0] }, { PS_LEVEL, q[1] }, { PS_REF, q[2] }, { PS_REF, q[3] } };
        ExprId root; template_call_env(TD_EQUIV, 4, a, &L->wb, &root); L->x = root; }
    FR_CALL(k, L->y, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_AWAIT(k, r, F_INTERP, L->x, L->y);
    { size_t n; FR_FINISH(k, rget(r, &n)[1]); }
    FR_END(k);
}

/* ---------------- inference ---------------- */
/* infer(G, C, t): variables directly; a construction through the
 * substitution lemma (its node validated once at its generic instance, t's
 * map into that context checked); a template instance by its own rule; a
 * global occurrence by its head rule. [code, reason, type] */
static void infer_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t */
    RefId t = q[1];
    FR_BEGIN(k);
    if (ref_is_var(t)) {
        L->T = term_var_type(ref_var_id(t));                 /* a variable carries its type */
        FR_AWAIT(k, r, F_FCENT, q[0], term_var_required(ref_var_id(t)));
        if (r != 2) BAD("variable used outside its required face");
        DONE(J_OK, NULL, L->T, 0, 0);
    }
    FR_AWAIT(k, r, F_FCENT, q[0], ref_required(t));
    if (r != 2) BAD("occurrence outside its required face");
    if (!tview_is_construction(t)) { JAW(r, J_TVIEW, RQ(q[0], t)); FR_FINISH(k, r); }
    if (ref_tag(t) == T_GLOBAL) { JAW(r, J_HEAD, RQ(q[0], t)); FR_FINISH(k, r); }
    /* the node typed once at its generic instance; this instance's images
     * at their slots' types; the type by the substitution lemma */
    JAW(L->res, J_NODE, RQ(ref_tnode(t)));
    PASS(L->res);
    L->D = L->res;
    JAW(L->res, J_TBOUND, RQ(q[0], t));
    PASS(L->res);
    FR_AWAIT(k, L->m, J_GMAP, t, 0);
    FR_AWAIT(k, r, F_TREF, jr_c(L->D), re_key(L->m));
    DONE(J_OK, NULL, r, 0, 0);
    FR_END(k);
}

/* the head rules (infer_head of §33): the inferred type of an opened head */
static void head_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t */
    uint64_t C = q[0]; RefId t = q[1];
    FR_BEGIN(k);
    L->tag = ref_tag(t);
    FR_AWAIT(k, L->lv, F_HEAD, t, 1);
    if (L->tag == T_UNIVERSE) {
        FR_AWAIT(k, L->x, F_HEAD, t, 0);
        FR_LSUCC(k, L->x, L->x);
        FR_CALL(k, r, mk_tag_sub(k, T_UNIVERSE, L->x, LEVELS_NONE, 0, NULL, 0));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PI || L->tag == T_SIGMA) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_LEVEL, RQ(C, L->a0));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        L->x = binder_term_var(t, 0, L->a0);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, binder_req(S_TERM, 0, 1, L->y));
        JRQ(L->res, J_LEVEL, RQ(C, L->a1));
        PASS(L->res);
        L->l2 = jr_a(L->res);
        if (!level_ok2(L->lv, L->l1, L->l2)) BAD(level_why(L->lv, "universe annotation differs from the formation levels"));
        FR_LMAX(k, L->l1, L->l1, L->l2);
        FR_CALL(k, r, mk_tag_sub(k, T_UNIVERSE, L->l1, LEVELS_NONE, 0, NULL, 0));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_LAM) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_LEVEL, RQ(C, L->a0));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, "lambda domain level annotation differs"));
        L->x = binder_term_var(t, 0, L->a0);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, binder_req(S_TERM, 0, 1, L->y));
        JRQ(L->res, J_INFER, RQ(C, L->a1));
        PASS(L->res);
        L->T = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->T));
        PASS(L->res);
        FR_CALL(k, r, MK_SUB(k, T_PI, 0, levels_pack(L->l1, jr_a(L->res)), L->x, L->a0, L->T));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_APP) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        JRQ(L->res, J_INFER, RQ(C, L->a0));
        PASS(L->res);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_PI));
        if (jr_code(L->res) == J_BAD) BAD("application of a non-function");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        JRQ(L->res, J_CHECK, RQ(C, L->a1, L->D));
        PASS(L->res);
        FR_AWAIT(k, r, F_BINDER, L->PP, binder_req(S_TERM, 0, 1, L->a1));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PAIR) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        if (tnode_nfields(ref_tnode(t)) == 3) {
            /* annotated: the stored Σ forms and the form checks against it (§33) */
            FR_AWAIT(k, L->a2, F_FIELD, t, 2);
            JRQ(L->res, J_LEVEL, RQ(C, L->a2));
            PASS(L->res);
            if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "pair annotation level differs"));
            JRQ(L->res, J_CHECK, RQ(C, t, L->a2));
            PASS(L->res);
            DONE(J_OK, NULL, L->a2, 0, 0);
        }
        JRQ(L->res, J_INFER, RQ(C, L->a0));
        PASS(L->res);
        L->a2 = jr_a(L->res);
        JRQ(L->res, J_INFER, RQ(C, L->a1));
        PASS(L->res);
        L->a3 = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->a2));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->a3));
        PASS(L->res);
        L->x = conv_var(t, t, L->a2, 0, L->a2);
        FR_CALL(k, r, MK_SUB(k, T_SIGMA, 0, levels_pack(L->l1, jr_a(L->res)), L->x, L->a2, L->a3));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_FST || L->tag == T_SND) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_INFER, RQ(C, L->a0));
        PASS(L->res);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_SIGMA));
        if (jr_code(L->res) == J_BAD) BAD("projection of a non-pair");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        if (L->tag == T_FST) DONE(J_OK, NULL, L->D, 0, 0);
        FR_CALL(k, L->x, MK_SUB(k, T_FST, 0, LEVELS_NONE, 0, L->a0));
        FR_AWAIT(k, r, F_BINDER, L->PP, binder_req(S_TERM, 0, 1, L->x));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PATH || L->tag == T_PAPP) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_LEVEL, RQ(C, L->a0));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, L->tag == T_PATH ? "path family level annotation differs" : "path application family level annotation differs"));
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, L->a2, F_FIELD, t, 2);
        FR_AWAIT(k, L->a3, F_TREF, L->a0, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CHECK, RQ(C, L->a1, L->a3));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_TREF, L->a0, dim_at(L->x, iv_one()));
        JRQ(L->res, J_CHECK, RQ(C, L->a2, L->a3));
        PASS(L->res);
        if (L->tag == T_PATH) { FR_CALL(k, r, mk_tag_sub(k, T_UNIVERSE, L->l1, LEVELS_NONE, 0, NULL, 0)); DONE(J_OK, NULL, r, 0, 0); }
        FR_AWAIT(k, L->a4, F_FIELD, t, 4);
        FR_AWAIT(k, L->y, F_DIMS, L->a4, 0);
        for (L->lw = set_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_bound_id(L->lw[L->d])) BAD("path applied to an out-of-scope interval"); FR_YIELD(k); }
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);
        FR_CALL(k, L->T, MK_SUB(k, T_PATH, 0, levels_pack(L->l1, LEVEL_NONE), (DimVarId)L->x, L->a0, L->a1, L->a2));
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->T));
        PASS(L->res);
        FR_AWAIT(k, r, F_TREF, L->a0, dim_at(L->x, L->a4));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PLAM) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_INFER, RQ(C, L->a0));
        PASS(L->res);
        L->T = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->T));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        FR_AWAIT(k, L->a1, F_TREF, L->a0, dim_at(L->x, iv_zero()));
        FR_AWAIT(k, L->a2, F_TREF, L->a0, dim_at(L->x, iv_one()));
        FR_CALL(k, r, MK_SUB(k, T_PATH, 0, levels_pack(L->l1, LEVEL_NONE), (DimVarId)L->x, L->T, L->a1, L->a2));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_GLUE_TYPE || L->tag == T_GLUE_INTRO || L->tag == T_UNGLUE) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, L->a2, F_FIELD, t, 2);
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);
        JAW(L->res, J_GLUEOK, RQ(C, L->a0, L->a1, L->a2, L->a3));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, L->tag == T_GLUE_TYPE ? "Glue level annotation differs" : L->tag == T_GLUE_INTRO ? "glue level annotation differs" : "unglue level annotation differs"));
        if (L->tag == T_GLUE_TYPE) { FR_CALL(k, r, mk_tag_sub(k, T_UNIVERSE, L->l1, LEVELS_NONE, 0, NULL, 0)); DONE(J_OK, NULL, r, 0, 0); }
        FR_CALL(k, L->T, MK_SUB(k, T_GLUE_TYPE, 0, levels_pack(L->l1, LEVEL_NONE), 0, L->a0, L->a1, L->a2, L->a3));
        if (L->tag == T_UNGLUE) {
            FR_AWAIT(k, L->a4, F_FIELD, t, 4);
            JRQ(L->res, J_CHECK, RQ(C, L->a4, L->T));
            PASS(L->res);
            DONE(J_OK, NULL, L->a0, 0, 0);
        }
        FR_AWAIT(k, L->a4, F_FIELD, t, 4);
        FR_AWAIT(k, L->a5, F_FIELD, t, 5);
        JRQ(L->res, J_CHECK, RQ(C, L->a5, L->a0));
        PASS(L->res);
        FR_AWAIT(k, L->x, F_FCMEET, C, L->a1);
        EVERY(L->res, L->x, J_CHECK, L->a4, L->a2);
        PASS(L->res);
        FR_CALL(k, L->z, MK_SUB(k, T_FST, 0, LEVELS_NONE, 0, L->a3));
        FR_CALL(k, L->z, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, L->z, L->a4));
        EVERY(L->res, L->x, J_CONVt, L->z, L->a5, L->a0);
        ALL_OR(L->res, "glue: e.map(t) is not the base term on the Glue face", "unresolved: glue map agreement");
        DONE(J_OK, NULL, L->T, 0, 0);
    }
    if (L->tag == T_COMP) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_var(L->x)));      /* the family A(j) */
        FR_AWAIT(k, L->a2, F_BINDER, t, binder_req(S_DIM, 0, 2, iv_var(L->x)));      /* the tube u(j) */
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);                                      /* φ */
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);                                      /* the cap */
        JRQ(L->res, J_LEVEL, RQ(C, L->a0));
        PASS(L->res);
        if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "composition family level annotation differs"));
        FR_AWAIT(k, L->y, F_DIMS, L->a1, 0);
        for (L->lw = set_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_bound_id(L->lw[L->d])) BAD("composition face must be in scope and independent of the bound dimension"); FR_YIELD(k); }
        L->lw = set_get(L->y, &L->n);
        for (L->i = 0; L->i < L->n; L->i++) { if (L->lw[L->i] == L->x) BAD("composition face must be in scope and independent of the bound dimension"); FR_YIELD(k); }
        FR_AWAIT(k, L->a4, F_TREF, L->a0, dim_at(L->x, iv_zero()));          /* A(0) */
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->a4));
        PASS(L->res);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a1);
        EVERY(L->res, L->z, J_CHECK, L->a2, L->a0);
        PASS(L->res);
        FR_AWAIT(k, L->a5, F_TREF, L->a2, dim_at(L->x, iv_zero()));          /* u(0) */
        EVERY(L->res, L->z, J_CONVt, L->a5, L->a3, L->a4);
        ALL_OR(L->res, "composition: tube at 0 disagrees with the cap", "unresolved: cap/tube agreement");
        FR_AWAIT(k, r, F_TREF, L->a0, dim_at(L->x, iv_one()));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_SYSTEM) { JAW(r, J_SYSTEM, RQ(C, t, 0)); FR_FINISH(k, r); }
    if (L->tag == T_GLOBAL) {
        FR_AWAIT(k, L->x, F_HEAD, t, 0);
        JAW(L->res, J_DECL, RQ(L->x));
        PASS(L->res);
        JAW(L->res, J_TBOUND, RQ(C, t));        /* the arguments at the declared parameter types */
        PASS(L->res);
        FR_AWAIT(k, r, F_UNFOLD, t, global_type((SymbolId)L->x));
        DONE(J_OK, NULL, r, 0, 0);
    }
    BAD("no inference rule for this head");
    FR_END(k);
}

/* Glue data: A forms at l; α in scope; under each clause of C ∧ α the fibre T
 * forms at the same level and e : Equiv(T, A). [code, reason, l] */
static void glueok_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A, α, T, e */
    FR_BEGIN(k);
    JRQ(L->res, J_LEVEL, RQ(q[0], q[1]));
    PASS(L->res);
    L->l1 = jr_a(L->res);
    FR_AWAIT(k, L->x, F_FCMEET, q[0], q[2]);
    if (fc_is_false(L->x)) DONE(J_OK, NULL, L->l1, 0, 0);
    EVERY(L->res, L->x, J_LEVEL, q[3]);
    PASS(L->res);
    if (!jr_b(L->res) || jr_a(L->res) != L->l1) BAD("Glue fibre type is not in the base's universe");
    JAW(L->z, J_EQUIV, RQ(L->l1, L->l1, q[3], q[1]));
    EVERY(L->res, L->x, J_CHECK, q[4], L->z);
    PASS(L->res);
    DONE(J_OK, NULL, L->l1, 0, 0);
    FR_END(k);
}

/* system(C, t, T): a system under C — its guards cover C and are in
 * scope; each branch under C ∧ its guard is checked against T, or inferred
 * when T = 0; on each overlap the branches agree (their types first, when
 * inferred). Inferred: the type of a branch whose guard C entails. */
static void system_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, T */
    uint64_t C = q[0]; RefId t = q[1];
    FR_BEGIN(k);
    L->n = tnode_nfields(ref_tnode(t)) / 2;
    L->x = fc_false();
    for (L->i = 0; L->i < L->n; L->i++) {
        FR_AWAIT(k, L->y, F_FIELD, t, 2 * L->i);
        FR_AWAIT(k, L->x, F_JOIN, L->x, L->y);
    }
    FR_AWAIT(k, r, F_FCENT, C, L->x);
    if (r != 2) BAD("system does not cover the face");
    L->j2 = L->n;                                                   /* the selected branch */
    for (L->i = 0; L->i < L->n; L->i++) {
        FR_AWAIT(k, L->u, F_FIELD, t, 2 * L->i);
        FR_AWAIT(k, L->y, F_DIMS, L->u, 0);
        for (L->lw = set_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_bound_id(L->lw[L->d])) BAD("system guard mentions an undeclared dimension"); FR_YIELD(k); }
        FR_AWAIT(k, L->y, F_FCMEET, C, L->u);
        if (fc_is_false(L->y)) continue;
        FR_AWAIT(k, L->z, F_FIELD, t, 2 * L->i + 1);
        if (q[2]) EVERY(L->res, L->y, J_CHECK, L->z, q[2]);
        else JRQ(L->res, J_INFER, RQ(L->y, L->z));
        PASS(L->res);
        if (L->j2 == L->n) {
            FR_AWAIT(k, r, F_FCENT, C, L->u);
            if (r == 2) L->j2 = L->i;
        }
    }
    for (L->i = 0; L->i < L->n; L->i++) {
        for (L->q = L->i + 1; L->q < L->n; L->q++) {
            FR_AWAIT(k, L->a2, F_FIELD, t, 2 * L->i);
            FR_AWAIT(k, L->a3, F_FIELD, t, 2 * L->q);
            FR_AWAIT(k, L->y, F_FCMEET, L->a2, L->a3);
            FR_AWAIT(k, L->y, F_FCMEET, C, L->y);
            if (fc_is_false(L->y)) continue;
            FR_AWAIT(k, L->a0, F_FIELD, t, 2 * L->i + 1);
            FR_AWAIT(k, L->a1, F_FIELD, t, 2 * L->q + 1);
            L->l1 = q[2];
            if (!L->l1) {
                FR_AWAIT(k, L->u, F_FCMEET, C, L->a2);
                JRQ(L->res, J_INFER, RQ(L->u, L->a0));
                L->l1 = jr_a(L->res);
                FR_AWAIT(k, L->u, F_FCMEET, C, L->a3);
                JRQ(L->res, J_INFER, RQ(L->u, L->a1));
                EVERY(L->res, L->y, J_CONVT, L->l1, jr_a(L->res));
                ALL_OR(L->res, "system branches disagree on an overlap", "unresolved: system overlap");
            }
            EVERY(L->res, L->y, J_CONVt, L->a0, L->a1, L->l1);
            ALL_OR(L->res, "system branches disagree on an overlap", "unresolved: system overlap");
        }
    }
    if (q[2]) OK0();
    require(L->j2 < L->n, "a covered system has an entailed branch under a single clause");
    FR_AWAIT(k, L->u, F_FIELD, t, 2 * L->j2);
    FR_AWAIT(k, L->y, F_FCMEET, C, L->u);
    FR_AWAIT(k, L->z, F_FIELD, t, 2 * L->j2 + 1);
    JRQ(L->res, J_INFER, RQ(L->y, L->z));
    DONE(J_OK, NULL, jr_a(L->res), 0, 0);
    FR_END(k);
}

/* ---------------- checking against an expected type ---------------- */
static void check_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, A */
    uint64_t C = q[0]; RefId t = q[1];
    FR_BEGIN(k);
    L->T = q[2];
    if (!ref_is_var(t)) {
        FR_AWAIT(k, r, F_FCENT, C, ref_required(t));
        if (r != 2) BAD("occurrence outside its required face");
        L->tag = ref_tag(t);
    } else L->tag = 0;
    if (L->tag == T_LAM || L->tag == T_PAIR || L->tag == T_PLAM || L->tag == T_SYSTEM) {
        /* the checking forms; a template instance's boundary is not bypassed */
        JAW(L->res, J_TBOUND, RQ(C, t));
        PASS(L->res);
        FR_AWAIT(k, L->lv, F_HEAD, t, 1);
    }
    if (L->tag == T_LAM) {
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_PI));
        if (jr_code(L->res) == J_BAD) BAD("lambda checked against a non-product type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_CONVT, RQ(C, L->a0, L->D));
        if (jr_code(L->res) == J_BAD) BAD("lambda domain differs from the expected domain");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: lambda domain conversion");
        JRQ(L->res, J_LEVEL, RQ(C, L->a0));
        PASS(L->res);
        if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "lambda domain level annotation differs"));
        L->x = conv_var(t, L->PP, L->PP, 0, L->D);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, binder_req(S_TERM, 0, 1, L->y));
        FR_AWAIT(k, L->a2, F_BINDER, L->PP, binder_req(S_TERM, 0, 1, L->y));
        JRQ(r, J_CHECK, RQ(C, L->a1, L->a2));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PAIR) {
        if (tnode_nfields(ref_tnode(t)) == 3) {
            /* annotated (§59.2): the stored Σ forms at its stored level, converts
             * with the expected type and governs the components */
            FR_AWAIT(k, L->a2, F_FIELD, t, 2);
            JRQ(L->res, J_LEVEL, RQ(C, L->a2));
            PASS(L->res);
            if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "pair annotation level differs"));
            JRQ(L->res, J_CONVT, RQ(C, L->a2, L->T));
            if (jr_code(L->res) == J_BAD) BAD("pair annotation differs from the expected type");
            if (jr_code(L->res) == J_UNR) UNR("unresolved: pair annotation conversion");
            L->T = L->a2;
        }
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_SIGMA));
        if (jr_code(L->res) == J_BAD) BAD("pair checked against a non-sum type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        JRQ(L->res, J_CHECK, RQ(C, L->a0, L->D));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_BINDER, L->PP, binder_req(S_TERM, 0, 1, L->a0));
        JRQ(r, J_CHECK, RQ(C, L->a1, L->a3));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PLAM) {
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_PATH));
        if (jr_code(L->res) == J_BAD) BAD("path lambda checked against a non-path type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->a1, F_FIELD, L->PP, 1);
        FR_AWAIT(k, L->a2, F_FIELD, L->PP, 2);
        L->x = conv_dim(t, L->PP, 0);
        FR_AWAIT(k, L->a3, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a4, F_BINDER, L->PP, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->a4));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_zero()));
        FR_AWAIT(k, L->a4, F_BINDER, L->PP, binder_req(S_DIM, 0, 0, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->a3, L->a1, L->a4));
        if (jr_code(L->res) == J_OK) {
            FR_AWAIT(k, L->a3, F_BINDER, t, binder_req(S_DIM, 0, 0, iv_one()));
            FR_AWAIT(k, L->a4, F_BINDER, L->PP, binder_req(S_DIM, 0, 0, iv_one()));
            JRQ(L->res, J_CONVt, RQ(C, L->a3, L->a2, L->a4));
        }
        if (jr_code(L->res) == J_BAD) BAD("path lambda endpoints differ from the path type's endpoints");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: path endpoint conversion");
        OK0();
    }
    if (L->tag == T_SYSTEM) { JAW(r, J_SYSTEM, RQ(C, t, L->T)); FR_FINISH(k, r); }
    JRQ(L->res, J_INFER, RQ(C, t));
    PASS(L->res);
    JRQ(L->res, J_CONVT, RQ(C, jr_a(L->res), L->T));
    if (jr_code(L->res) == J_OK) OK0();
    if (jr_code(L->res) == J_BAD) BAD("inferred type is not convertible to the expected type");
    UNR("unresolved: type conversion");
    FR_END(k);
}

/* ---------------- conversion ---------------- */
/* two observations under C as one join: 0 unless both completed normally */
/* two independent observations under C: launched, then awaited in order */
#define OBS_TWO(Cx, a, b) do { \
        family_launch(F_OBS, (a), observe_key((Cx), 0)); family_launch(F_OBS, (b), observe_key((Cx), 0)); \
    } while (0)
static bool obs_ok(EvalResult r) { return r.cls != R_INVALID && r.cls != R_NO_OBSERVATION; }
/* the common level of a Glue's base and fibre: the annotation, else inferred */
/* glue.eq(C, n1, n2): two nodes carrying Glue data in fields 0–3 (a Glue
 * type or an unglue: base A, face α, fibre T, equivalence e) agree — the
 * same C ∧ α, convertible bases and, under each clause of C ∧ α,
 * convertible fibres and equivalences at the common level (the annotation,
 * else the base's level) */
static void glueeq_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, n1, n2 */
    uint64_t C = q[0]; RefId n1 = q[1], n2 = q[2];
    FR_BEGIN(k);
    FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
    FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
    FR_AWAIT(k, L->y, F_FCMEET, C, L->a2);
    FR_AWAIT(k, L->z, F_FCMEET, C, L->a3);
    if (L->y != L->z) BAD(NULL);
    FR_AWAIT(k, L->a4, F_FIELD, n1, 0);
    FR_AWAIT(k, L->a5, F_FIELD, n2, 0);
    JRQ(L->res, J_CONVT, RQ(C, L->a4, L->a5));
    if (jr_code(L->res) != J_OK || fc_is_false(L->y)) FR_FINISH(k, L->res);
    FR_AWAIT(k, L->a2, F_FIELD, n1, 2);
    FR_AWAIT(k, L->a3, F_FIELD, n2, 2);
    EVERY(L->res, L->y, J_CONVT, L->a2, L->a3);
    if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
    FR_AWAIT(k, L->lv, F_HEAD, n1, 1);
    L->l1 = levels_first(L->lv);
    if (L->l1 == LEVEL_NONE) {
        EVERY(L->res, L->y, J_LEVEL, L->a4);
        if (jr_code(L->res) != J_OK || !jr_b(L->res)) UNR(NULL);
        L->l1 = jr_a(L->res);
    }
    JAW(L->T, J_EQUIV, RQ(L->l1, L->l1, L->a2, L->a4));
    FR_AWAIT(k, L->a2, F_FIELD, n1, 3);
    FR_AWAIT(k, L->a3, F_FIELD, n2, 3);
    EVERY(r, L->y, J_CONVt, L->a2, L->a3, L->T);
    FR_FINISH(k, r);
    FR_END(k);
}

static void convT_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A, B */
    uint64_t C = q[0];
    FR_BEGIN(k);
    if (q[1] == q[2]) FR_FINISH(k, judge_res(J_OK, NULL, 0, 0, 0));
    OBS_TWO(C, q[1], q[2]);
    FR_AWAIT(k, L->r1, F_OBS, q[1], observe_key(C, 0));
    FR_AWAIT(k, L->r2, F_OBS, q[2], observe_key(C, 0));
    if (!obs_ok(R1) || !obs_ok(R2)) UNR(NULL);
    if (R1.ref == R2.ref) OK0();
    if (R1.cls == R_SYSTEM || R2.cls == R_SYSTEM) UNR(NULL);
    if (R1.cls != R2.cls) BAD(NULL);
    if (R1.cls == R_NEUTRAL) { JAW(r, J_SPINE, RQ(C, R1.ref, R2.ref)); FR_FINISH(k, r); }
    L->a0 = R1.ref; L->a1 = R2.ref;
    L->tag = ref_tag(L->a0);
    if (L->tag != ref_tag(L->a1)) BAD(NULL);
    if (L->tag == T_UNIVERSE) {
        FR_AWAIT(k, L->x, F_HEAD, L->a0, 0);
        FR_AWAIT(k, L->y, F_HEAD, L->a1, 0);
        if (L->x == L->y) OK0();
        BAD(NULL);
    }
    if (L->tag == T_PI || L->tag == T_SIGMA) {
        FR_AWAIT(k, L->a2, F_FIELD, L->a0, 0);
        FR_AWAIT(k, L->a3, F_FIELD, L->a1, 0);
        JRQ(L->res, J_CONVT, RQ(C, L->a2, L->a3));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        L->x = conv_var(L->a0, L->a1, L->a0, 0, L->a2);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a4, F_BINDER, L->a0, binder_req(S_TERM, 0, 1, L->y));
        FR_AWAIT(k, L->a5, F_BINDER, L->a1, binder_req(S_TERM, 0, 1, L->y));
        JRQ(r, J_CONVT, RQ(C, L->a4, L->a5));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PATH) {
        L->x = conv_dim(L->a0, L->a1, 0);
        FR_AWAIT(k, L->a2, F_BINDER, L->a0, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a3, F_BINDER, L->a1, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CONVT, RQ(C, L->a2, L->a3));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->y, F_FIELD, L->a0, 1);
        FR_AWAIT(k, L->z, F_FIELD, L->a1, 1);
        FR_AWAIT(k, L->a4, F_TREF, L->a2, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->y, L->z, L->a4));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->y, F_FIELD, L->a0, 2);
        FR_AWAIT(k, L->z, F_FIELD, L->a1, 2);
        FR_AWAIT(k, L->a4, F_TREF, L->a2, dim_at(L->x, iv_one()));
        JRQ(r, J_CONVt, RQ(C, L->y, L->z, L->a4));
        FR_FINISH(k, r);
    }
    if (L->tag == T_GLUE_TYPE) { JAW(r, J_GLUEEQ, RQ(C, L->a0, L->a1)); FR_FINISH(k, r); }
    BAD(NULL);                                     /* an introduction that is not a type former */
    FR_END(k);
}

static void convt_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, u, A */
    uint64_t C = q[0]; RefId t = q[1], u = q[2];
    FR_BEGIN(k);
    if (t == u) OK0();
    FR_AWAIT(k, L->r1, F_OBS, q[3], observe_key(C, 0));
    if (!obs_ok(R1)) UNR(NULL);
    if (R1.cls == R_INTRODUCTION) {
        L->a0 = R1.ref; L->tag = ref_tag(L->a0);
        if (L->tag == T_PI) {
            FR_AWAIT(k, L->D, F_FIELD, L->a0, 0);
            L->x = conv_var(t, u, L->a0, 0, L->D);
            FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, binder_req(S_TERM, 0, 1, L->y));
            FR_CALL(k, L->a2, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, t, L->y));
            FR_CALL(k, L->a3, MK_SUB(k, T_APP, 0, LEVELS_NONE, 0, u, L->y));
            JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->a1));
            FR_FINISH(k, r);
        }
        if (L->tag == T_SIGMA) {
            FR_AWAIT(k, L->D, F_FIELD, L->a0, 0);
            FR_CALL(k, L->a2, MK_SUB(k, T_FST, 0, LEVELS_NONE, 0, t));
            FR_CALL(k, L->a3, MK_SUB(k, T_FST, 0, LEVELS_NONE, 0, u));
            JRQ(L->res, J_CONVt, RQ(C, L->a2, L->a3, L->D));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, binder_req(S_TERM, 0, 1, L->a2));
            FR_CALL(k, L->a2, MK_SUB(k, T_SND, 0, LEVELS_NONE, 0, t));
            FR_CALL(k, L->a3, MK_SUB(k, T_SND, 0, LEVELS_NONE, 0, u));
            JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->a1));
            FR_FINISH(k, r);
        }
        if (L->tag == T_PATH) {
            L->x = conv_dim(t, u, 0);
            L->y = binder_dim_var(L->a0, 0);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, binder_req(S_DIM, 0, 0, iv_var(L->y)));     /* B(j') at the binder's own name */
            FR_AWAIT(k, L->a2, F_TREF, L->a1, dim_at(L->y, iv_var(L->x)));          /* B(j) */
            FR_AWAIT(k, L->a3, F_FIELD, L->a0, 1);
            FR_AWAIT(k, L->a4, F_FIELD, L->a0, 2);
            FR_AWAIT(k, L->lv, F_HEAD, L->a0, 1);
            FR_CALL(k, L->a5, MK_SUB(k, T_PAPP, 0, levels_pack(levels_first(L->lv), LEVEL_NONE), (DimVarId)L->y, L->a1, L->a3, L->a4, t, iv_var(L->x)));
            FR_CALL(k, L->T, MK_SUB(k, T_PAPP, 0, levels_pack(levels_first(L->lv), LEVEL_NONE), (DimVarId)L->y, L->a1, L->a3, L->a4, u, iv_var(L->x)));
            JRQ(r, J_CONVt, RQ(C, L->a5, L->T, L->a2));
            FR_FINISH(k, r);
        }
        if (L->tag == T_GLUE_TYPE) {
            /* non-collapsed Glue: Glue η */
            FR_AWAIT(k, L->a1, F_FIELD, L->a0, 0);
            FR_AWAIT(k, L->a2, F_FIELD, L->a0, 1);
            FR_AWAIT(k, L->a3, F_FIELD, L->a0, 2);
            FR_AWAIT(k, L->a4, F_FIELD, L->a0, 3);
            FR_AWAIT(k, L->lv, F_HEAD, L->a0, 1);
            FR_CALL(k, L->y, MK_SUB(k, T_UNGLUE, 0, levels_pack(levels_first(L->lv), LEVEL_NONE), 0, L->a1, L->a2, L->a3, L->a4, t));
            FR_CALL(k, L->z, MK_SUB(k, T_UNGLUE, 0, levels_pack(levels_first(L->lv), LEVEL_NONE), 0, L->a1, L->a2, L->a3, L->a4, u));
            JRQ(L->res, J_CONVt, RQ(C, L->y, L->z, L->a1));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            FR_AWAIT(k, L->x, F_FCMEET, C, L->a2);
            EVERY(r, L->x, J_CONVt, t, u, L->a3);
            FR_FINISH(k, r);
        }
        if (L->tag == T_UNIVERSE) { JRQ(r, J_CONVT, RQ(C, t, u)); FR_FINISH(k, r); }
        BAD(NULL);
    }
    if (R1.cls == R_NEUTRAL) {
        /* neutral expected type: observe the terms and compare their neutral structures */
        OBS_TWO(C, t, u);
        FR_AWAIT(k, L->r1, F_OBS, t, observe_key(C, 0));
        FR_AWAIT(k, L->r2, F_OBS, u, observe_key(C, 0));
        if (!obs_ok(R1) || !obs_ok(R2)) UNR(NULL);
        if (R1.ref == R2.ref) OK0();
        if (R1.cls == R_NEUTRAL && R2.cls == R_NEUTRAL) { JAW(r, J_SPINE, RQ(C, R1.ref, R2.ref)); FR_FINISH(k, r); }
        if (R1.cls == R_SYSTEM || R2.cls == R_SYSTEM) UNR(NULL);
        BAD(NULL);
    }
    UNR(NULL);                                     /* a system type under a single clause is not a covered type */
    FR_END(k);
}

/* structural comparison of neutral spines */
static void spine_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, n1, n2 */
    uint64_t C = q[0]; RefId n1 = q[1], n2 = q[2];
    FR_BEGIN(k);
    if (n1 == n2) OK0();
    if (ref_is_var(n1) || ref_is_var(n2)) { if (ref_is_var(n1) && ref_is_var(n2) && ref_var_id(n1) == ref_var_id(n2)) OK0(); BAD(NULL); }
    L->tag = ref_tag(n1);
    if (L->tag != ref_tag(n2)) BAD(NULL);
    if (L->tag == T_APP || L->tag == T_FST || L->tag == T_SND || L->tag == T_PAPP || L->tag == T_UNGLUE) {
        if (L->tag == T_PAPP) {
            FR_AWAIT(k, L->a0, F_FIELD, n1, 4);
            FR_AWAIT(k, L->a1, F_FIELD, n2, 4);
            FR_AWAIT(k, L->m, J_CMAP, C, 0);                 /* the endpoints the clause fixes */
            FR_AWAIT(k, L->a0, F_TIV, L->a0, re_key(L->m));
            FR_AWAIT(k, L->a1, F_TIV, L->a1, re_key(L->m));
            if (L->a0 != L->a1) BAD(NULL);
        }
        if (L->tag == T_UNGLUE) {
            JAW(L->res, J_GLUEEQ, RQ(C, n1, n2));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        }
        /* the scrutinees, observed as one join; both must be neutral */
        {   size_t f = L->tag == T_PAPP ? 3 : L->tag == T_UNGLUE ? 4 : 0; L->i = f; }
        FR_AWAIT(k, L->a0, F_FIELD, n1, L->i);
        FR_AWAIT(k, L->a1, F_FIELD, n2, L->i);
        OBS_TWO(C, L->a0, L->a1);
        FR_AWAIT(k, L->r1, F_OBS, L->a0, observe_key(C, 0));
        FR_AWAIT(k, L->r2, F_OBS, L->a1, observe_key(C, 0));
        if (!obs_ok(R1) || !obs_ok(R2) || R1.cls != R_NEUTRAL || R2.cls != R_NEUTRAL) UNR(NULL);
        JAW(L->res, J_SPINE, RQ(C, R1.ref, R2.ref));
        if (jr_code(L->res) != J_OK || L->tag != T_APP) FR_FINISH(k, L->res);
        /* an application: the arguments at the function's domain */
        JRQ(L->res, J_INFER, RQ(C, L->a0));
        if (jr_code(L->res) != J_OK) UNR(NULL);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_PI));
        if (jr_code(L->res) != J_OK) UNR(NULL);
        FR_AWAIT(k, L->D, F_FIELD, jr_a(L->res), 0);
        FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
        FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
        JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->D));
        FR_FINISH(k, r);
    }
    if (L->tag == T_COMP) {
        FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
        FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
        FR_AWAIT(k, L->y, F_FCMEET, C, L->a2);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a3);
        if (L->y != L->z) BAD(NULL);
        L->x = conv_dim(n1, n2, 0);
        FR_AWAIT(k, L->a0, F_BINDER, n1, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a1, F_BINDER, n2, binder_req(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CONVT, RQ(C, L->a0, L->a1));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->a4, F_FIELD, n1, 3);
        FR_AWAIT(k, L->a5, F_FIELD, n2, 3);
        FR_AWAIT(k, L->T, F_TREF, L->a0, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->a4, L->a5, L->T));
        if (jr_code(L->res) != J_OK || fc_is_false(L->y)) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->a4, F_BINDER, n1, binder_req(S_DIM, 0, 2, iv_var(L->x)));
        FR_AWAIT(k, L->a5, F_BINDER, n2, binder_req(S_DIM, 0, 2, iv_var(L->x)));
        EVERY(r, L->y, J_CONVt, L->a4, L->a5, L->a0);
        FR_FINISH(k, r);
    }
    if (L->tag == T_GLOBAL) {
        FR_AWAIT(k, L->x, F_HEAD, n1, 0);
        FR_AWAIT(k, L->y, F_HEAD, n2, 0);
        if (L->x != L->y) BAD(NULL);
        /* the arguments slot by slot (both nodes are the definition's): an
         * interval up to the endpoints the clause fixes, a term at its
         * parameter's type read from the first environment */
        L->n = subst_size(ref_tenv(n1));
        for (L->i = 0; L->i < L->n; L->i++) {
            {   uint64_t slot; TVal a, b; subst_get(ref_tenv(n1), L->i, &slot, &a); subst_get(ref_tenv(n2), L->i, &slot, &b);
                L->tag = a.sort; L->a2 = a.id; L->a3 = b.id; }
            if (L->tag == PS_INTERVAL) {
                FR_AWAIT(k, L->m, J_CMAP, C, 0);
                FR_AWAIT(k, L->a2, F_TIV, L->a2, re_key(L->m));
                FR_AWAIT(k, L->a3, F_TIV, L->a3, re_key(L->m));
                if (L->a2 != L->a3) BAD(NULL);
            } else {
                {   PSort so; RefId ty; FaceId g; tnode_param(ref_tnode(n1), L->i, &so, &ty, &g); L->T = ty; }
                FR_AWAIT(k, L->a4, F_TREF, L->T, apply_key(ref_tenv(n1)));
                JRQ(L->res, J_CONVt, RQ(C, L->a2, L->a3, L->a4));
                if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            }
        }
        OK0();
    }
    BAD(NULL);
    FR_END(k);
}

/* the endpoints fixed by a clause, as a dimension map (one literal per step) */
static void cmap_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL); uint64_t r = 0;
    FR_BEGIN(k);
    L->lw = rget(k->w[0], &L->n);
    wordbuf_init(&L->wb);
    for (L->i = 0; L->i < L->n && L->lw[L->i] != DNF_SEP; L->i++) {
        wordbuf_push(&L->wb, FC_LIT_DIM(L->lw[L->i])); wordbuf_push(&L->wb, PS_INTERVAL); wordbuf_push(&L->wb, FC_LIT_EPS(L->lw[L->i]) ? iv_one() : iv_zero());
        FR_YIELD(k);
    }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}

/* ---------------- template instances ---------------- */
static void tview_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t */
    RefId t = q[1];
    FR_BEGIN(k);
    JAW(L->res, J_TBOUND, RQ(q[0], t));
    PASS(L->res);
    JAW(L->res, J_HEAD, RQ(q[0], t));
    PASS(L->res);
    L->T = jr_a(L->res);
    {   ExprId te, le; if (!tnode_result_exprs(ref_tnode(t), &te, &le)) DONE(J_OK, NULL, L->T, 0, 0); L->x = te; }
    L->y = ref_tenv(t);
    FR_AWAIT(k, r, F_INTERP, L->x, L->y);
    { L->D = rword(r, 1); }
    JRQ(L->res, J_CONVT, RQ(q[0], L->T, L->D));
    if (jr_code(L->res) == J_BAD) {
        { char buf[256]; snprintf(buf, sizeof buf, "library instance type differs from its declared result type (%s)", tdef_name(tnode_def(ref_tnode(t)))); diag_words(&L->wb, buf); }
        FR_CALL(k, L->w0, intern_sub(k, &M.keys, &L->wb, &L->created));
        BAD(diag_text(L->w0));
    }
    if (jr_code(L->res) == J_UNR) UNR("unresolved: declared result type conversion");
    DONE(J_OK, NULL, L->T, 0, 0);
    FR_END(k);
}
/* the boundary of an instance (§51.4, §59.1): each retained image well
 * formed and of its slot's declared type under the slot's guard */
static void tbound_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t */
    uint64_t C = q[0]; RefId t = q[1];
    FR_BEGIN(k);
    if (ref_is_var(t)) OK0();
    /* finite structure of every retained image first (§50.1–2) */
    L->n = subst_size(ref_tenv(t));
    for (L->i = 0; L->i < L->n; L->i++) {
        {   uint64_t slot; TVal val; subst_get(ref_tenv(t), L->i, &slot, &val); L->tag = val.sort; L->x = val.id; }
        if (L->tag == PS_SCOPE || L->tag == PS_REF) {
            JAW(L->res, J_RV, RQ(L->tag == PS_SCOPE ? 1 : 0, L->x, 0));
            PASS(L->res);
        } else FR_YIELD(k);
    }
    L->D = ref_tenv(t);
    L->n = tnode_sig_count(ref_tnode(t));
    for (L->i = 0; L->i < L->n; L->i++) {
        {   size_t slot; PSort so; ExprId te, le, se, ge;
            if (!tnode_sig_exprs(ref_tnode(t), L->i, &slot, &so, &te, &le, &se, &ge) || (so == PS_REF && !te) || (so == PS_SCOPE && !se) || (so != PS_REF && so != PS_SCOPE)) { L->tag = 0; }
            else { L->tag = so; L->j2 = slot; L->a0 = so == PS_REF ? te : se; L->a1 = ge; } }
        if (!L->tag) { FR_YIELD(k); continue; }
        FR_AWAIT(k, r, F_LOOKUP, L->D, L->j2);
        require(r, "template boundary: a retained slot has no image");
        L->x = subst_value(L->D, r - 1);
        FR_AWAIT(k, r, F_INTERP, L->a0, L->D);
        { L->T = rword(r, 1); }
        if (L->tag == PS_REF) {
            L->y = fc_true();
            if (L->a1) { FR_AWAIT(k, r, F_INTERP, L->a1, L->D); L->y = rword(r, 1); }
            FR_AWAIT(k, L->y, F_FCMEET, C, L->y);
            EVERY(L->res, L->y, J_CHECK, L->x, L->T);
            if (jr_code(L->res) == J_BAD) {
                { char buf[256]; snprintf(buf, sizeof buf, "template parameter image is not of its declared type (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(t))), L->j2, jr_why(L->res) ? jr_why(L->res) : ""); diag_words(&L->wb, buf); }
                FR_CALL(k, L->w0, intern_sub(k, &M.keys, &L->wb, &L->created));
                BAD(diag_text(L->w0));
            }
            PASS(L->res);
        } else {
            JAW(L->res, J_SCARG, RQ(C, L->x, L->T));
            if (jr_code(L->res) == J_BAD) {
                { char buf[256]; snprintf(buf, sizeof buf, "template scope argument does not meet its signature (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(t))), L->j2, jr_why(L->res) ? jr_why(L->res) : ""); diag_words(&L->wb, buf); }
                FR_CALL(k, L->w0, intern_sub(k, &M.keys, &L->wb, &L->created));
                BAD(diag_text(L->w0));
            }
            PASS(L->res);
        }
    }
    OK0();
    FR_END(k);
}

/* ---------------- scopes ---------------- */
/* §50.1–4: a supplied scope's own validity in its own ambient-plus-local context */
static void scown_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, S */
    uint64_t C = q[0]; ScopeId S = q[1];
    FR_BEGIN(k);
    JAW(L->res, J_RV, RQ(1, S, 0));
    PASS(L->res);
    JAW(L->a5, J_OPEN, RQ(S, 0x52));
    L->a3 = rword(L->a5, 0); L->a4 = rword(L->a5, 1);
    L->n = scope_arity(S); for (L->i = 0; L->i < L->n; L->i++) {
        {   LocalDecl d = scope_local(S, L->i); L->tag = d.sort; L->T = d.type; L->a0 = d.required; L->lv = d.level;
            L->x = rword(L->a3, L->i); }
        if (L->tag == S_DIM) { FR_YIELD(k); continue; }
        if (!L->T) BAD("scope local has no declared type");
        if (L->lv == LEVEL_NONE) BAD("missing universe annotation on a scope local (§59.1)");
        L->y = apply_key(L->a4);
        FR_AWAIT(k, L->T, F_TREF, L->T, L->y);
        FR_AWAIT(k, L->a0, F_TFC, L->a0, L->y);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a0);
        EVERY(L->res, L->z, J_LEVEL, L->T);
        ALL_OR(L->res, "scope local type is not a type", jr_why(L->res));
        rget(jr_c(L->res), &L->nc);
        if (L->nc && (!jr_b(L->res) || jr_a(L->res) != L->lv)) BAD("scope local level annotation differs from its formation level");
    }
    if (scope_body(S).sort != VS_REF) OK0();
    if (!scope_type(S)) BAD("scope has no declared result type");
    if (scope_level(S) == LEVEL_NONE) BAD("missing universe annotation on a scope result (§59.1)");
    L->y = apply_key(L->a4);
    FR_AWAIT(k, L->T, F_TREF, scope_type(S), L->y);
    FR_AWAIT(k, L->a0, F_TFC, scope_guard(S), L->y);
    FR_AWAIT(k, L->a1, F_TREF, scope_body(S).id, L->y);
    FR_AWAIT(k, L->z, F_FCMEET, C, L->a0);
    EVERY(L->res, L->z, J_LEVEL, L->T);
    ALL_OR(L->res, "scope result type is not a type", jr_why(L->res));
    rget(jr_c(L->res), &L->nc);
    if (L->nc && (!jr_b(L->res) || jr_a(L->res) != scope_level(S))) BAD("scope result level annotation differs from its formation level");
    EVERY(r, L->z, J_CHECK, L->a1, L->T);
    FR_FINISH(k, r);
    FR_END(k);
}
/* §51.4: a valid scope argument S at the expected contextual signature Sig,
 * both opened at the signature's fresh telescope */
static void scarg_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, S, Sig */
    uint64_t C = q[0]; ScopeId S = q[1], Sig = q[2];
    FR_BEGIN(k);
    L->n = scope_arity(S);
    if (L->n != scope_arity(Sig)) BAD("scope argument telescope length differs from the signature");
    for (L->i = 0; L->i < L->n; L->i++) { if (scope_local(S, L->i).sort != scope_local(Sig, L->i).sort) BAD("scope argument telescope sorts differ from the signature"); FR_YIELD(k); }
    if (scope_body(S).sort != scope_body(Sig).sort) BAD("scope argument body sort differs from the signature");
    JAW(L->res, J_SCOWN, RQ(C, S));
    PASS(L->res);
    JAW(L->a5, J_OPEN, RQ(Sig, 0x51));
    L->a3 = rword(L->a5, 0); L->a4 = rword(L->a5, 1);
    for (L->i = 0; L->i < L->n; L->i++) {
        {   L->x = rword(L->a3, L->i); L->tag = scope_local(Sig, L->i).sort; L->T = scope_local(S, L->i).type; }
        if (L->tag == S_DIM) { FR_YIELD(k); continue; }
        L->y = apply_key(L->a4);
        FR_AWAIT(k, L->T, F_TREF, L->T, L->y);
        JRQ(L->res, J_CONVT, RQ(C, L->T, term_var_type(L->x)));
        if (jr_code(L->res) == J_BAD) BAD("scope argument local type differs from the signature");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: scope argument local type conversion");
    }
    L->y = apply_key(L->a4);
    FR_AWAIT(k, L->a0, F_TFC, scope_guard(S), L->y);       /* supplied guard */
    FR_AWAIT(k, L->a1, F_TFC, scope_guard(Sig), L->y);     /* expected guard */
    FR_AWAIT(k, L->z, F_FCMEET, C, L->a1);
    FR_AWAIT(k, r, F_FCENT, L->z, L->a0);
    if (r != 2) BAD("scope argument is not available where the signature requires it");
    if (scope_body(S).sort != VS_REF) OK0();
    FR_AWAIT(k, L->T, F_TREF, scope_type(S), L->y);
    FR_AWAIT(k, L->D, F_TREF, scope_body(Sig).id, L->y);
    EVERY(L->res, L->z, J_CONVT, L->T, L->D);
    ALL_OR(L->res, "scope argument result type differs from the signature", "unresolved: scope argument result type conversion");
    OK0();
    FR_END(k);
}

/* ---------------- typed maps and contexts ---------------- */
/* σ : (D; ψ) → (Γ; χ) */
static void map_step(Cont *k, uint64_t v) {
    JLOC;   /* q: D, ψ, σ, Γ, χ */
    uint64_t D = q[0], psi = q[1], sigma = q[2];
    FR_BEGIN(k);
    JAW(L->res, J_CTX, RQ(q[3], q[4]));
    PASS(L->res);
    JAW(L->res, J_CTX, RQ(D, psi));
    PASS(L->res);
    for (L->G2 = q[3]; !jc_is_empty(L->G2); L->G2 = jc_parent(L->G2)) {
        {   Sort so; uint64_t id; jc_decl(L->G2, &so, &id); L->tag = so; L->x = id; L->T = so == S_TERM ? term_var_type(id) : 0; }
        if (L->tag == S_DIM) {
            FR_AWAIT(k, L->y, F_TIMGD, L->x, re_key(sigma));
            FR_AWAIT(k, L->y, F_DIMS, L->y, 0);
            JAW(r, J_DIMSIN, RQ(D, L->y));
            if (r != J_OK) BAD("dimension image mentions an undeclared source dimension");
            continue;
        }
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->y, F_TREF, L->y, re_key(sigma));
        JAW(L->res, J_SCOPE, RQ(D, fc_true(), L->y));
        if (jr_code(L->res) != J_OK) BAD("term image is not in scope of the source context");
        FR_AWAIT(k, L->T, F_TREF, L->T, re_key(sigma));
        FR_AWAIT(k, L->z, F_TFC, term_var_required(L->x), re_key(sigma));
        FR_AWAIT(k, L->z, F_FCMEET, psi, L->z);
        EVERY(L->res, L->z, J_CHECK, L->y, L->T);
        PASS(L->res);
    }
    FR_AWAIT(k, L->z, F_TFC, q[4], re_key(sigma));
    FR_AWAIT(k, r, F_FCENT, psi, L->z);
    if (r != 2) BAD("source face does not entail the substituted target assumption");
    OK0();
    FR_END(k);
}
/* a context with assumption a: the assumption uses declared dimensions, and
 * every declaration is valid over its prefix */
static void ctx_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a */
    FR_BEGIN(k);
    FR_AWAIT(k, L->y, F_DIMS, q[1], 0);
    JAW(r, J_DIMSIN, RQ(q[0], L->y));
    if (r != J_OK) BAD("assumption mentions an undeclared dimension");
    JAW(r, J_CTXD, RQ(q[0], q[1]));
    FR_FINISH(k, r);
    FR_END(k);
}
static void ctxd_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a */
    FR_BEGIN(k);
    if (jc_is_empty(q[0])) OK0();
    family_launch(J_CTXD, RQ(jc_parent(q[0]), q[1]), 0);
    family_launch(J_DECLOK, RQ(q[0], q[1]), 0);
    JAW(L->x, J_CTXD, RQ(jc_parent(q[0]), q[1]));
    JAW(L->y, J_DECLOK, RQ(q[0], q[1]));
    FR_FINISH(k, jr_code(L->x) != J_OK ? L->x : L->y);
    FR_END(k);
}
/* the top declaration of G over its prefix (§2, §33 item 3, §59.2): not
 * declared earlier; a term variable's own type is a type in scope of the
 * earlier declarations */
static void declok_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a */
    FR_BEGIN(k);
    {   Sort so; uint64_t id; jc_decl(q[0], &so, &id); L->tag = so; L->x = id; }
    L->G2 = jc_parent(q[0]);
    FR_AWAIT(k, r, F_LOOKUP, jc_index(L->G2), L->x);
    if (jc_found(L->G2, r, (Sort)L->tag)) BAD("duplicate declaration");
    if (L->tag != S_TERM) OK0();
    L->T = term_var_type(L->x);
    JAW(L->res, J_SCOPE, RQ(L->G2, term_var_required(L->x), L->T));
    if (jr_code(L->res) != J_OK) BAD("declaration type is not in scope of the earlier declarations");
    FR_AWAIT(k, L->y, J_JDIMS, L->G2, 0);
    FR_AWAIT(k, L->y, F_FCPROJ, q[1], L->y);
    FR_AWAIT(k, L->y, F_FCMEET, L->y, term_var_required(L->x));
    EVERY(L->res, L->y, J_LEVEL, L->T);
    PASS(L->res);
    OK0();
    FR_END(k);
}
/* a construction node at its generic instance: [code, reason, context,
 * required face, type] (every instance is typed by the substitution lemma) */
static void node_step(Cont *k, uint64_t v) {
    JLOC;   /* q: Q */
    FR_BEGIN(k);
    FR_AWAIT(k, L->x, J_GENERIC, q[0], 0);
    { size_t n; const uint64_t *w = rget(L->x, &n); L->G2 = w[0]; L->a0 = w[1]; L->a1 = w[2]; }
    JAW(L->res, J_CTX, RQ(L->G2, L->a0));
    PASS(L->res);
    JAW(L->res, J_JOINT, RQ(L->a0, J_HEAD, L->a1));
    PASS(L->res);
    DONE(J_OK, NULL, L->G2, L->a0, jr_a(L->res));
    FR_END(k);
}

/* ---------------- global symbols ---------------- */
/* decl(s): s is declared in the view (its revision is read: a use of s is a
 * use of that revision, whose body judge.admit validates) and its declared
 * type is a type over the parameters */
static void decl_step(Cont *k, uint64_t v) {
    JLOC;   /* q: s */
    FR_BEGIN(k);
    if (!global_type((SymbolId)q[0])) BAD("symbol without a declared type");
    FR_AWAIT(k, L->G2, J_GCTX, q[0], 0);
    JAW(L->res, J_CTX, RQ(L->G2, fc_true()));
    PASS(L->res);
    JAW(L->res, J_SCOPE, RQ(L->G2, fc_true(), global_type((SymbolId)q[0])));
    PASS(L->res);
    JRQ(L->res, J_LEVEL, RQ(fc_true(), global_type((SymbolId)q[0])));
    PASS(L->res);
    OK0();
    FR_END(k);
}
/* body(rev): the revision's body checks against its symbol's declaration
 * (an opaque revision has no body obligation) */
static void body_step(Cont *k, uint64_t v) {
    JLOC;   /* q: rev */
    SymbolId s = revision_symbol(q[0]); RefId b = revision_body(q[0]);
    FR_BEGIN(k);
    JAW(L->res, J_DECL, RQ(s));
    PASS(L->res);
    if (!b) OK0();
    FR_AWAIT(k, L->G2, J_GCTX, s, 0);
    JAW(L->res, J_SCOPE, RQ(L->G2, fc_true(), b));
    PASS(L->res);
    JRQ(r, J_CHECK, RQ(fc_true(), b, global_type(s)));
    FR_FINISH(k, r);
    FR_END(k);
}

/* ---------------- finite structure (§50.1–2) ---------------- */
/* rv(kind, x, stack): a reference (0) or scope (1) is well formed at the
 * enclosing telescope stack (cons records [parent, scope]); rvd(kind, x,
 * stack): the bound dimensions of an interval (0) or face (1) */
#define STK_TAG 0x57ACULL
static uint64_t stk_push(uint64_t stk, ScopeId S) { return RQ(STK_TAG, stk, S); }
/* an atom against the stack, one level per step: 0 well formed, else the reason */
#define ATOM_CHECK(id, want) do { \
        L->u = bound_depth(id); L->w0 = bound_slot(id); L->m = stk; \
        for (L->q = 0; L->q < L->u && L->m; L->q++) { size_t n_; L->m = rget(L->m, &n_)[1]; FR_YIELD(k); } \
        if (!L->m) BAD("bound occurrence names no enclosing telescope"); \
        { size_t n_; ScopeId T_ = rget(L->m, &n_)[2]; \
          if (L->w0 >= scope_arity(T_)) BAD("bound occurrence names a slot outside its telescope"); \
          if (scope_local(T_, L->w0).sort != (want)) BAD("bound occurrence has the wrong sort for its slot"); } \
    } while (0)
static void rvd_step(Cont *k, uint64_t v) {
    JLOC;   /* q: kind, x, stack */
    uint64_t stk = q[2];
    FR_BEGIN(k);
    FR_AWAIT(k, L->y, F_DIMS, q[1], 0);
    L->lw = set_get(L->y, &L->n);
    for (L->i = 0; L->i < L->n; L->i++) {
        if (is_bound_id(L->lw[L->i])) ATOM_CHECK(L->lw[L->i], S_DIM);
        FR_YIELD(k);
    }
    OK0();
    FR_END(k);
}
static void rv_step(Cont *k, uint64_t v) {
    JLOC;   /* q: kind, x, stack */
    uint64_t stk = q[2], x = q[1];
    FR_BEGIN(k);
    if (q[0] == 0) {
        if (ref_is_var(x)) { if (is_bound_id(ref_var_id(x))) ATOM_CHECK(ref_var_id(x), S_TERM); OK0(); }
        /* the environment's images, then a construction's stored field
         * constants and declared face (a scope stored in one is validated at
         * the actual stack) */
        L->n = subst_size(ref_tenv(x));
        for (L->i = 0; L->i < L->n; L->i++) {
            {   uint64_t slot; TVal val; subst_get(ref_tenv(x), L->i, &slot, &val); L->tag = val.sort; L->y = val.id; }
            if (L->tag == PS_LEVEL) { FR_YIELD(k); continue; }
            if (L->tag == PS_REF || L->tag == PS_SCOPE) JAW(L->res, J_RV, RQ(L->tag == PS_SCOPE ? 1 : 0, L->y, stk));
            else JAW(L->res, J_RVD, RQ(L->tag == PS_FACE ? 1 : 0, L->y, stk));
            PASS(L->res);
        }
        if (tnode_is_construction(ref_tnode(x))) {
            FR_AWAIT(k, L->y, J_NTEL, ref_tnode(x), 1);
            L->D = stk_push(stk, L->y);                     /* the constants are closed under the node's telescope */
            L->n = tnode_nfields(ref_tnode(x));
            for (L->i = 0; L->i < L->n; L->i++) {
                {   TNodeId Q = ref_tnode(x); L->tag = tnode_field_kind(Q, L->i); L->y = tnode_const_field(Q, L->i); }
                if (L->tag == F_REF) JAW(L->res, J_RV, RQ(0, L->y, L->D));
                else JAW(L->res, J_RVD, RQ(L->tag == F_FACE ? 1 : 0, L->y, L->D));
                PASS(L->res);
            }
            if (tnode_const_declared(ref_tnode(x))) { JAW(L->res, J_RVD, RQ(1, tnode_const_declared(ref_tnode(x)), L->D)); PASS(L->res); }
        }
        OK0();
    }
    /* a scope */
    L->n = scope_arity(x);
    for (L->i = 0; L->i < L->n; L->i++) {
        {   LocalDecl d = scope_local(x, L->i);
            if (d.sort == S_TERM && !d.type) BAD("term local without a declared type");
            if (d.sort == S_DIM && d.type) BAD("dimension local with a type"); }
        FR_YIELD(k);
    }
    if (scope_body(x).sort == VS_REF && !scope_type(x)) BAD("reference scope without a declared result type");
    for (L->i = 0; L->i < L->n; L->i++) {
        /* the prefix view of the telescope: its first i locals */
        wordbuf_init(&L->wb); wordbuf_push(&L->wb, L->i);
        for (L->q = 0; L->q < L->i; L->q++) {
            { LocalDecl d = scope_local(x, L->q); wordbuf_push(&L->wb, d.sort); wordbuf_push(&L->wb, d.type); wordbuf_push(&L->wb, d.level); wordbuf_push(&L->wb, d.required); }
            FR_YIELD(k);
        }
        wordbuf_push(&L->wb, VS_FACE); wordbuf_push(&L->wb, 0); wordbuf_push(&L->wb, LEVEL_NONE); wordbuf_push(&L->wb, fc_true()); wordbuf_push(&L->wb, fc_true());
        FR_CALL(k, L->y, intern_sub(k, &M.keys, &L->wb, &L->created));
        FR_AWAIT(k, L->y, F_SCOPESIDE, L->y, 0);
        L->z = stk_push(stk, L->y);
        if (scope_local(x, L->i).type) {
            JAW(L->res, J_RV, RQ(0, scope_local(x, L->i).type, L->z));
            if (jr_code(L->res) != J_OK) BAD("local declaration uses a later or absent slot");
        }
        JAW(L->res, J_RVD, RQ(1, scope_local(x, L->i).required, L->z));
        if (jr_code(L->res) != J_OK) BAD("local declaration uses a later or absent slot");
    }
    L->z = stk_push(stk, x);
    {   Val b = scope_body(x); L->tag = b.sort; L->y = b.id; }
    if (L->tag == VS_REF) JAW(L->res, J_RV, RQ(0, L->y, L->z));
    else JAW(L->res, J_RVD, RQ(L->tag == VS_FACE ? 1 : 0, L->y, L->z));
    PASS(L->res);
    if (scope_type(x)) { JAW(L->res, J_RV, RQ(0, scope_type(x), L->z)); PASS(L->res); }
    JAW(L->res, J_RVD, RQ(1, scope_guard(x), L->z));
    PASS(L->res);
    OK0();
    FR_END(k);
}

/* ---------------- registration ---------------- */
void judge_families_init(void) {
    family_define(J_CLAUSES, "judge.clauses", clauses_step, sizeof(JL));
    family_define(J_CMAP, "judge.clause_map", cmap_step, sizeof(JL));
    family_define(J_DIMSIN, "judge.dims_in", dimsin_step, sizeof(JL));
    family_define(J_JDIMS, "judge.ctx_dims", jdims_step, 0);
    family_define(J_GCTX, "judge.global_context", gctx_step, sizeof(JL));
    family_define(J_GENERIC, "judge.generic", generic_step, sizeof(JL));
    family_define(J_GMAP, "judge.generic_map", gmap_step, sizeof(JL));
    family_define(J_OBSHEAD, "judge.observe_head", obshead_step, sizeof(JL));
    family_define(J_LEVEL, "judge.level", level_step, sizeof(JL));
    family_define(J_EQUIV, "judge.equiv", equiv_step, sizeof(JL));
    family_define(J_INFER, "judge.infer", infer_step, sizeof(JL));
    family_define(J_HEAD, "judge.head", head_step, sizeof(JL));
    family_define(J_GLUEOK, "judge.glue", glueok_step, sizeof(JL));
    family_define(J_CHECK, "judge.check", check_step, sizeof(JL));
    family_define(J_CONVT, "judge.conv_type", convT_step, sizeof(JL));
    family_define(J_CONVt, "judge.conv_term", convt_step, sizeof(JL));
    family_define(J_SPINE, "judge.spine", spine_step, sizeof(JL));
    family_define(J_TVIEW, "judge.instance", tview_step, sizeof(JL));
    family_define(J_TBOUND, "judge.boundary", tbound_step, sizeof(JL));
    family_define(J_OPEN, "judge.open", open_step, sizeof(JL));
    family_define(J_NTEL, "judge.node_telescope", ntel_step, sizeof(JL));
    family_define(J_REQ, "judge.request", jreq_step, sizeof(ReqLoc));
    family_define(J_SCOWN, "judge.scope_own", scown_step, sizeof(JL));
    family_define(J_SCARG, "judge.scope_arg", scarg_step, sizeof(JL));
    family_define(J_MAP, "judge.map", map_step, sizeof(JL));
    family_define(J_CTX, "judge.ctx", ctx_step, sizeof(JL));
    family_define(J_CTXD, "judge.ctx_decls", ctxd_step, sizeof(JL));
    family_define(J_DECLOK, "judge.ctx_decl", declok_step, sizeof(JL));
    family_define(J_NODE, "judge.node", node_step, sizeof(JL));
    family_define(J_DECL, "judge.decl", decl_step, sizeof(JL));
    family_define(J_BODY, "judge.body", body_step, sizeof(JL));
    family_define(J_RV, "judge.structure", rv_step, sizeof(JL));
    family_define(J_RVD, "judge.structure_dims", rvd_step, sizeof(JL));
    family_define(J_SCOPE, "judge.scope", scope_step, sizeof(JL));
    family_define(J_EXT, "judge.context_ext", jcext_step, 0);
    family_define(J_EVERY, "judge.every", every_step, sizeof(JL));
    family_define(J_JOINT, "judge.joint", joint_step, sizeof(JL));
    family_define(J_SYSTEM, "judge.system", system_step, sizeof(JL));
    family_define(J_GLUEEQ, "judge.glue_eq", glueeq_step, sizeof(JL));
}
uint64_t judge_request(size_t n, const uint64_t *w) { return rq(n, w); }

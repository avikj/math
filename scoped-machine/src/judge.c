/* judge.c — checking and conversion as frame families (PLAN step 4).
 *
 * Every judgment is a pure family keyed by its request record and the pin
 * set P of the top-level request (pins.h): its premises are awaited requests
 * of other judgment, evaluation and construction families, independent ones
 * as joins. One judgment is executed once and shared by every requester. A
 * judgment that depends on itself is an unresolved dependency of the
 * protocol (its root is reported UNRESOLVED); the one resolution rule is the
 * declaration of a global symbol: inference of an occurrence of s requires
 * only that s's declaration forms (decl), never its body, so recursion
 * through bodies is no cycle; a request's verdict is the conjunction of its
 * own derivation and the body judgments of the symbols in its pin set.
 *
 * Contexts inside judgments are cons records [JC, parent, sort, id, type,
 * index]: the index (a pin-set trie over 2x / 2j+1) answers declaration
 * lookups in bounded work; a prefix context is the parent; the face is
 * carried in the request, not in the context.
 *
 * Results are records [code, reason, a, b, c]: code 1 VALID/EQUAL,
 * 2 INVALID/UNEQUAL, 3 UNRESOLVED; reason a static or session diagnostic.
 */
#include "judge.h"
#include "pins.h"
#include "template.h"
#include "scope.h"
#include "lib.h"

/* ---------------- records ---------------- */
static uint64_t rq(size_t n, const uint64_t *w) { return interner_intern(&M.keys, w, n, NULL); }
#define RQ(...) rq(sizeof((uint64_t[]){ __VA_ARGS__ }) / sizeof(uint64_t), (uint64_t[]){ __VA_ARGS__ })
static const uint64_t *rget(uint64_t id, size_t *n) { return interner_get(&M.keys, id, n); }
uint64_t judge_res(uint64_t code, const char *why, uint64_t a, uint64_t b, uint64_t c) { return RQ(code, (uint64_t)(uintptr_t)why, a, b, c); }
uint64_t jr_code(uint64_t v) { size_t n; return rget(v, &n)[0]; }
const char *jr_why(uint64_t v) { size_t n; return (const char *)(uintptr_t)rget(v, &n)[1]; }
uint64_t jr_a(uint64_t v) { size_t n; return rget(v, &n)[2]; }
uint64_t jr_b(uint64_t v) { size_t n; return rget(v, &n)[3]; }
uint64_t jr_c(uint64_t v) { size_t n; return rget(v, &n)[4]; }
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
static const char *diag_text(uint64_t rec) { size_t n; return (const char *)interner_get(&M.keys, rec, &n); }

/* ---------------- contexts ---------------- */
#define JC_TAG 0x7C7CULL
/* [tag, parent, sort, id, index]: a variable's type is its own */
uint64_t jc_empty(void) { return RQ(JC_TAG, 0, 0, 0, pins_empty()); }
static const uint64_t *jcw(uint64_t G) { size_t n; const uint64_t *w = rget(G, &n); require(n == 5 && w[0] == JC_TAG, "not a judgment context"); return w; }
uint64_t jc_parent(uint64_t G) { return jcw(G)[1]; }
bool jc_is_empty(uint64_t G) { return jcw(G)[1] == 0 && jcw(G)[2] == 0; }
void jc_decl(uint64_t G, Sort *sort, uint64_t *id) { const uint64_t *w = jcw(G); *sort = (Sort)w[2]; *id = w[3]; }
uint64_t jc_ext(uint64_t G, Sort sort, uint64_t id) {
    const uint64_t *w = jcw(G);
    uint64_t idx = pins_insert(w[4], sort == S_TERM ? 2 * id : 2 * id + 1, 1);
    return RQ(JC_TAG, G, sort, id, idx);
}
bool jc_term(uint64_t G, TermVarId x) { return pins_lookup(jcw(G)[4], 2 * x, NULL); }
bool jc_dim(uint64_t G, DimVarId j) { return pins_lookup(jcw(G)[4], 2 * j + 1, NULL); }

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
/* a local judgment [χ, subjects…, P] is keyed at (π_S χ, subjects, P), S the
 * support of its subjects (§5 projection theorem), as whnf.observe keys whnf */
typedef struct { uint64_t s, c; size_t i; } ReqLoc;
static void jreq_step(Cont *k, uint64_t v) {
    ReqLoc *L = FR_LOC(k, ReqLoc); uint64_t r = 0; size_t n; const uint64_t *q = rget(k->w[0], &n);
    FR_BEGIN(k);
    L->s = ref_support(q[1]);
    for (L->i = 2; L->i + 1 < n; L->i++) FR_AWAIT(k, L->s, F_DSUNION, L->s, ref_support(q[L->i]));
    FR_AWAIT(k, L->c, F_FCPROJ, q[0], L->s);
    if (L->c != q[0]) { uint64_t w[8]; memcpy(w, q, n * sizeof *w); w[0] = L->c; k->w[0] = rq(n, w); }
    FR_AWAIT(k, r, (Family)k->w[1], k->w[0], 0);
    FR_FINISH(k, r);
    FR_END(k);
}
static Cont *jreq_sub(const Cont *k, Family f, uint64_t req) { Cont *c = frame_sub(J_REQ, k); c->w[0] = req; c->w[1] = f; return c; }
#define JRQ(var, fam, req) FR_CALL(k, var, jreq_sub(k, fam, req))

/* constructions (the request records the root constructors build) */
static Cont *mk_sub(const Cont *k, Tag tag, uint64_t levels, size_t nf, const Field *f, size_t nb, const Binder *b) { return construct_sub(k, tag, 0, levels, nf, f, nb, b); }
static Cont *mk_universe_sub(const Cont *k, uint64_t l) { return construct_sub(k, T_UNIVERSE, l, LEVELS_NONE, 0, NULL, 0, NULL); }
static Cont *mk_app_sub(const Cont *k, RefId fn, RefId a) { Field f[2] = { { F_REF, NO_SLOT, fn }, { F_REF, NO_SLOT, a } }; return mk_sub(k, T_APP, LEVELS_NONE, 2, f, 0, NULL); }
static Cont *mk_proj_sub(const Cont *k, Tag tag, RefId p) { Field f[1] = { { F_REF, NO_SLOT, p } }; return mk_sub(k, tag, LEVELS_NONE, 1, f, 0, NULL); }
static Cont *mk_binder_form_sub(const Cont *k, Tag tag, uint64_t m, uint64_t n, TermVarId x, RefId A, RefId B) {
    Field f[2] = { { F_REF, NO_SLOT, A }, { F_REF, 0, B } }; Binder b[1] = { { S_TERM, x, 0 } };
    return mk_sub(k, tag, levels_pack(m, n), 2, f, 1, b);
}
static Cont *mk_path_sub(const Cont *k, uint64_t l, DimVarId j, RefId Bj, RefId a0, RefId a1) {
    Field f[3] = { { F_REF, 0, Bj }, { F_REF, NO_SLOT, a0 }, { F_REF, NO_SLOT, a1 } }; Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return mk_sub(k, T_PATH, levels_pack(l, LEVEL_NONE), 3, f, 1, b);
}
static Cont *mk_papp_sub(const Cont *k, uint64_t l, DimVarId j, RefId Bj, RefId a0, RefId a1, RefId p, IntervalId s) {
    Field f[5] = { { F_REF, 0, Bj }, { F_REF, NO_SLOT, a0 }, { F_REF, NO_SLOT, a1 }, { F_REF, NO_SLOT, p }, { F_INTERVAL, NO_SLOT, s } }; Binder b[1] = { { S_DIM, j, NO_FIELD } };
    return mk_sub(k, T_PAPP, levels_pack(l, LEVEL_NONE), 5, f, 1, b);
}
static Cont *mk_glue_sub(const Cont *k, uint64_t l, RefId A, FaceId alpha, RefId T, RefId e) {
    Field f[4] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e } };
    return mk_sub(k, T_GLUE_TYPE, levels_pack(l, LEVEL_NONE), 4, f, 0, NULL);
}
static Cont *mk_unglue_sub(const Cont *k, uint64_t l, RefId A, FaceId alpha, RefId T, RefId e, RefId v) {
    Field f[5] = { { F_REF, NO_SLOT, A }, { F_FACE, NO_SLOT, alpha }, { F_REF, NO_SLOT, T }, { F_REF, NO_SLOT, e }, { F_REF, NO_SLOT, v } };
    return mk_sub(k, T_UNGLUE, levels_pack(l, LEVEL_NONE), 5, f, 0, NULL);
}
static uint64_t brec(Sort sort, uint64_t slot, uint64_t field, uint64_t image) { return RQ(sort, slot, field, image); }
static MapId dim_at(DimVarId j, IntervalId r) { return map_single_dim(j, r); }
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

/* a system's construction request, built one branch per step */
static void creq_system_begin(WordBuf *w, size_t n) {
    wordbuf_init(w);
    wordbuf_push(w, T_SYSTEM); wordbuf_push(w, n); wordbuf_push(w, LEVELS_NONE); wordbuf_push(w, 0); wordbuf_push(w, 0); wordbuf_push(w, 0); wordbuf_push(w, 2 * n);
}
static void creq_system_branch(WordBuf *w, FaceId f, RefId t) {
    wordbuf_push(w, F_FACE); wordbuf_push(w, NO_SLOT); wordbuf_push(w, f);
    wordbuf_push(w, F_REF); wordbuf_push(w, NO_SLOT); wordbuf_push(w, t);
}

/* ---------------- faces ---------------- */
/* clauses(φ): the list record of φ's clauses, each a one-clause face (a
 * clause of a canonical DNF is canonical: its literals, then the separator) */
static void clauses_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL); uint64_t r = 0;
    FR_BEGIN(k);
    L->lw = interner_get(&M.faces, k->w[0], &L->n);
    wordbuf_init(&L->wb);
    L->i = 0;
    while (L->i < L->n) {
        wordbuf_init(&L->wc);
        while (L->lw[L->i] != DNF_SEP) { wordbuf_push(&L->wc, L->lw[L->i]); L->i++; FR_YIELD(k); }
        wordbuf_push(&L->wc, DNF_SEP); L->i++;
        FR_CALL(k, r, intern_sub(k, &M.faces, &L->wc, &L->created));
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
    L->lw = dimset_get(q[1], &L->n);
    for (L->i = 0; L->i < L->n; L->i++) {
        if (!jc_dim(q[0], L->lw[L->i])) FR_FINISH(k, J_BAD);
        FR_YIELD(k);
    }
    FR_FINISH(k, J_OK);
    FR_END(k);
}
/* the declared dimensions of a context */
static void jdims_step(Cont *k, uint64_t v) {
    uint64_t r = 0;
    FR_BEGIN(k);
    if (jc_is_empty(k->w[0])) FR_FINISH(k, dimset_make(NULL, 0));
    FR_AWAIT(k, r, J_JDIMS, jc_parent(k->w[0]), 0);
    {   Sort so; uint64_t id; jc_decl(k->w[0], &so, &id);
        if (so != S_DIM) FR_FINISH(k, r);
        k->w[2] = dimset_make(&id, 1); }
    FR_AWAIT(k, r, F_DSUNION, r, k->w[2]);
    FR_FINISH(k, r);
    FR_END(k);
}
/* scope(G, χ, t): the face's dimensions, the reference's finite structure,
 * its free variables and dimensions are declared in G */
static void scope_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, χ, t */
    FR_BEGIN(k);
    FR_AWAIT(k, L->y, F_FCDIMS, q[1], 0);
    JAW(r, J_DIMSIN, RQ(q[0], L->y));
    if (r != J_OK) BAD("face mentions an undeclared dimension");
    JAW(L->res, J_RV, RQ(0, q[2], 0));
    PASS(L->res);
    L->lw = varset_get(ref_freevars(q[2]), &L->n);
    for (L->i = 0; L->i < L->n; L->i++) { if (!jc_term(q[0], L->lw[L->i])) BAD("unbound variable"); FR_YIELD(k); }
    JAW(r, J_DIMSIN, RQ(q[0], ref_support(q[2])));
    if (r != J_OK) BAD("unbound dimension");
    OK0();
    FR_END(k);
}
/* a flat context as a judgment context (one declaration per step) */
static void jcof_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    FR_BEGIN(k);
    L->x = jc_empty(); L->n = context_size(k->w[0]);
    for (L->i = 0; L->i < L->n; L->i++) { CtxDecl d = context_decl(k->w[0], L->i); L->x = jc_ext(L->x, d.sort, d.id); FR_YIELD(k); }
    FR_FINISH(k, L->x);
    FR_END(k);
}
/* generic(Q): a construction node at fresh parameters keyed by (node, slot),
 * declared at the instantiated closed types: [context, required face,
 * instance, list of the fresh identities] */
static void generic_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL);
    TNodeId Q = k->w[0];
    FR_BEGIN(k);
    L->n = tnode_nparams(Q); L->G2 = jc_empty(); L->m = map_identity();
    wordbuf_init(&L->wb); wordbuf_init(&L->wc); wordbuf_push(&L->wb, 0);   /* the environment record of a construction node */
    for (L->i = 0; L->i < L->n; L->i++) {
        {   PSort so; RefId ty; FaceId g; tnode_param(Q, L->i, &so, &ty, &g); L->tag = so; L->T = ty; L->a0 = g; }
        if (L->tag == PS_INTERVAL) {
            {   KeyWord key[3] = { { KW_CONST, 9300 }, { KW_CONST, Q }, { KW_CONST, L->i } };
                DimVarId j = fresh_dim_keyed(key, 3);
                L->x = j; L->y = iv_var(j); L->G2 = jc_ext(L->G2, S_DIM, j); }
        } else {
            FR_AWAIT(k, L->T, F_REINDEX, L->T, L->m);
            if (L->a0) FR_AWAIT(k, L->a0, F_FCRE, L->a0, L->m);
            else L->a0 = fc_true();
            {   KeyWord key[3] = { { KW_CONST, 9300 }, { KW_CONST, Q }, { KW_CONST, L->i } };
                L->x = fresh_term_keyed_req(key, 3, L->T, L->a0); }
            FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
            L->G2 = jc_ext(L->G2, S_TERM, L->x);
        }
        wordbuf_push(&L->wb, L->i); wordbuf_push(&L->wb, L->tag); wordbuf_push(&L->wb, L->y);
        wordbuf_push(&L->wc, L->x);
        FR_AWAIT(k, L->m, F_OVERRIDE, L->m, RQ(L->tag == PS_INTERVAL ? S_DIM : S_TERM, obound_id((uint32_t)L->i), L->y));
    }
    FR_AWAIT(k, L->a1, F_FCRE, tnode_const_required(Q), L->m);
    FR_CALL(k, L->a2, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_AWAIT(k, L->a2, F_TVMAKE, Q, L->a2);
    FR_CALL(k, L->a3, intern_sub(k, &M.keys, &L->wc, &L->created));
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
    { size_t n; L->a3 = rget(L->x, &n)[3]; }
    L->m = map_identity(); L->n = tnode_nparams(ref_tnode(t));
    for (L->i = 0; L->i < L->n; L->i++) {
        {   size_t n; const uint64_t *ids = rget(L->a3, &n);
            uint64_t slot; TVal val; tenv_entry(ref_tenv(t), L->i, &slot, &val);
            L->y = RQ(val.sort == PS_INTERVAL ? S_DIM : S_TERM, ids[L->i], val.id); }
        FR_AWAIT(k, L->m, F_OVERRIDE, L->m, L->y);
    }
    FR_FINISH(k, L->m);
    FR_END(k);
}
/* observe T under C (pins P) and require an introduction with tag `want`:
 * [code, reason, the observed reference] */
static void obshead_step(Cont *k, uint64_t v) {
    JLOC;
    FR_BEGIN(k);
    FR_AWAIT(k, L->r1, F_OBS, q[1], observe_key(q[0], 0, q[3]));
    if (R1.cls == R_INVALID || R1.cls == R_NO_OBSERVATION) BAD(R1.message ? R1.message : "invalid observation");
    if (R1.cls != R_INTRODUCTION) BAD("expected a type former, found a neutral or system");
    if (ref_tag(R1.ref) != (Tag)q[2]) BAD("type former mismatch");
    DONE(J_OK, NULL, R1.ref, 0, 0);
    FR_END(k);
}
/* the universe level of a type under a clause: [code, reason, level] */
static void level_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A, P */
    FR_BEGIN(k);
    JRQ(L->res, J_INFER, RQ(q[0], q[1], q[2]));
    PASS(L->res);
    JAW(L->res, J_OBSHEAD, RQ(q[0], jr_a(L->res), T_UNIVERSE, q[2]));
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
    JLOC;   /* q: C, t, P */
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
    if (!tview_is_construction(t)) { JAW(r, J_TVIEW, RQ(q[0], t, q[2])); FR_FINISH(k, r); }
    if (ref_tag(t) == T_GLOBAL) { JAW(r, J_HEAD, RQ(q[0], t, q[2])); FR_FINISH(k, r); }
    /* the node typed once at its generic instance; this instance's images
     * at their slots' types; the type by the substitution lemma */
    JAW(L->res, J_NODE, RQ(ref_tnode(t), q[2]));
    PASS(L->res);
    L->D = L->res;
    JAW(L->res, J_TBOUND, RQ(q[0], t, q[2]));
    PASS(L->res);
    FR_AWAIT(k, L->m, J_GMAP, t, 0);
    FR_AWAIT(k, r, F_REINDEX, jr_c(L->D), L->m);
    DONE(J_OK, NULL, r, 0, 0);
    FR_END(k);
}

/* the head rules (infer_head of §33): the inferred type of an opened head */
static void head_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, P */
    uint64_t C = q[0], P = q[2]; RefId t = q[1];
    FR_BEGIN(k);
    L->tag = ref_tag(t);
    FR_AWAIT(k, L->lv, F_HEAD, t, 1);
    if (L->tag == T_UNIVERSE) {
        FR_AWAIT(k, L->x, F_HEAD, t, 0);
        FR_CALL(k, r, mk_universe_sub(k, level_succ(L->x)));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PI || L->tag == T_SIGMA) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_LEVEL, RQ(C, L->a0, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        L->x = binder_term_var(t, 0, L->a0);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, brec(S_TERM, 0, 1, L->y));
        JRQ(L->res, J_LEVEL, RQ(C, L->a1, P));
        PASS(L->res);
        L->l2 = jr_a(L->res);
        if (!level_ok2(L->lv, L->l1, L->l2)) BAD(level_why(L->lv, "universe annotation differs from the formation levels"));
        FR_CALL(k, r, mk_universe_sub(k, L->l1 > L->l2 ? L->l1 : L->l2));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_LAM) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_LEVEL, RQ(C, L->a0, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, "lambda domain level annotation differs"));
        L->x = binder_term_var(t, 0, L->a0);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, brec(S_TERM, 0, 1, L->y));
        JRQ(L->res, J_INFER, RQ(C, L->a1, P));
        PASS(L->res);
        L->T = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->T, P));
        PASS(L->res);
        FR_CALL(k, r, mk_binder_form_sub(k, T_PI, L->l1, jr_a(L->res), L->x, L->a0, L->T));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_APP) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        JRQ(L->res, J_INFER, RQ(C, L->a0, P));
        PASS(L->res);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_PI, P));
        if (jr_code(L->res) == J_BAD) BAD("application of a non-function");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        JRQ(L->res, J_CHECK, RQ(C, L->a1, L->D, P));
        PASS(L->res);
        FR_AWAIT(k, r, F_BINDER, L->PP, brec(S_TERM, 0, 1, L->a1));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PAIR) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        if (tnode_nfields(ref_tnode(t)) == 3) {
            /* annotated: the stored Σ forms and the form checks against it (§33) */
            FR_AWAIT(k, L->a2, F_FIELD, t, 2);
            JRQ(L->res, J_LEVEL, RQ(C, L->a2, P));
            PASS(L->res);
            if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "pair annotation level differs"));
            JRQ(L->res, J_CHECK, RQ(C, t, L->a2, P));
            PASS(L->res);
            DONE(J_OK, NULL, L->a2, 0, 0);
        }
        JRQ(L->res, J_INFER, RQ(C, L->a0, P));
        PASS(L->res);
        L->a2 = jr_a(L->res);
        JRQ(L->res, J_INFER, RQ(C, L->a1, P));
        PASS(L->res);
        L->a3 = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->a2, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->a3, P));
        PASS(L->res);
        L->x = conv_var(t, t, L->a2, 0, L->a2);
        FR_CALL(k, r, mk_binder_form_sub(k, T_SIGMA, L->l1, jr_a(L->res), L->x, L->a2, L->a3));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_FST || L->tag == T_SND) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_INFER, RQ(C, L->a0, P));
        PASS(L->res);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_SIGMA, P));
        if (jr_code(L->res) == J_BAD) BAD("projection of a non-pair");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        if (L->tag == T_FST) DONE(J_OK, NULL, L->D, 0, 0);
        FR_CALL(k, L->x, mk_proj_sub(k, T_FST, L->a0));
        FR_AWAIT(k, r, F_BINDER, L->PP, brec(S_TERM, 0, 1, L->x));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PATH || L->tag == T_PAPP) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, brec(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_LEVEL, RQ(C, L->a0, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, L->tag == T_PATH ? "path family level annotation differs" : "path application family level annotation differs"));
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, L->a2, F_FIELD, t, 2);
        FR_AWAIT(k, L->a3, F_REINDEX, L->a0, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CHECK, RQ(C, L->a1, L->a3, P));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_REINDEX, L->a0, dim_at(L->x, iv_one()));
        JRQ(L->res, J_CHECK, RQ(C, L->a2, L->a3, P));
        PASS(L->res);
        if (L->tag == T_PATH) { FR_CALL(k, r, mk_universe_sub(k, L->l1)); DONE(J_OK, NULL, r, 0, 0); }
        FR_AWAIT(k, L->a4, F_FIELD, t, 4);
        FR_AWAIT(k, L->y, F_IVDIMS, L->a4, 0);
        for (L->lw = dimset_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_local_atom(L->lw[L->d])) BAD("path applied to an out-of-scope interval"); FR_YIELD(k); }
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);
        FR_CALL(k, L->T, mk_path_sub(k, L->l1, (DimVarId)L->x, L->a0, L->a1, L->a2));
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->T, P));
        PASS(L->res);
        FR_AWAIT(k, r, F_REINDEX, L->a0, dim_at(L->x, L->a4));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_PLAM) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, brec(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_INFER, RQ(C, L->a0, P));
        PASS(L->res);
        L->T = jr_a(L->res);
        JRQ(L->res, J_LEVEL, RQ(C, L->T, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        FR_AWAIT(k, L->a1, F_REINDEX, L->a0, dim_at(L->x, iv_zero()));
        FR_AWAIT(k, L->a2, F_REINDEX, L->a0, dim_at(L->x, iv_one()));
        FR_CALL(k, r, mk_path_sub(k, L->l1, (DimVarId)L->x, L->T, L->a1, L->a2));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_GLUE_TYPE || L->tag == T_GLUE_INTRO || L->tag == T_UNGLUE) {
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        FR_AWAIT(k, L->a2, F_FIELD, t, 2);
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);
        JAW(L->res, J_GLUEOK, RQ(C, L->a0, L->a1, L->a2, L->a3, P));
        PASS(L->res);
        L->l1 = jr_a(L->res);
        if (!level_ok1(L->lv, L->l1)) BAD(level_why(L->lv, L->tag == T_GLUE_TYPE ? "Glue level annotation differs" : L->tag == T_GLUE_INTRO ? "glue level annotation differs" : "unglue level annotation differs"));
        if (L->tag == T_GLUE_TYPE) { FR_CALL(k, r, mk_universe_sub(k, L->l1)); DONE(J_OK, NULL, r, 0, 0); }
        FR_CALL(k, L->T, mk_glue_sub(k, L->l1, L->a0, L->a1, L->a2, L->a3));
        if (L->tag == T_UNGLUE) {
            FR_AWAIT(k, L->a4, F_FIELD, t, 4);
            JRQ(L->res, J_CHECK, RQ(C, L->a4, L->T, P));
            PASS(L->res);
            DONE(J_OK, NULL, L->a0, 0, 0);
        }
        FR_AWAIT(k, L->a4, F_FIELD, t, 4);
        FR_AWAIT(k, L->a5, F_FIELD, t, 5);
        JRQ(L->res, J_CHECK, RQ(C, L->a5, L->a0, P));
        PASS(L->res);
        FR_AWAIT(k, L->x, F_FCMEET, C, L->a1);
        if (!fc_is_false(L->x)) {
            FR_AWAIT(k, L->cl, J_CLAUSES, L->x, 0);
            for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                L->y = rget(L->cl, &L->nc)[L->c];
                JRQ(L->res, J_CHECK, RQ(L->y, L->a4, L->a2, P));
                PASS(L->res);
                FR_CALL(k, L->z, mk_proj_sub(k, T_FST, L->a3));
                FR_CALL(k, L->z, mk_app_sub(k, L->z, L->a4));
                JRQ(L->res, J_CONVt, RQ(L->y, L->z, L->a5, L->a0, P));
                if (jr_code(L->res) == J_BAD) BAD("glue: e.map(t) is not the base term on the Glue face");
                if (jr_code(L->res) == J_UNR) UNR("unresolved: glue map agreement");
            }
        }
        DONE(J_OK, NULL, L->T, 0, 0);
    }
    if (L->tag == T_COMP) {
        L->x = binder_dim_var(t, 0);
        FR_AWAIT(k, L->a0, F_BINDER, t, brec(S_DIM, 0, 0, iv_var(L->x)));      /* the family A(j) */
        FR_AWAIT(k, L->a2, F_BINDER, t, brec(S_DIM, 0, 2, iv_var(L->x)));      /* the tube u(j) */
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);                                      /* φ */
        FR_AWAIT(k, L->a3, F_FIELD, t, 3);                                      /* the cap */
        JRQ(L->res, J_LEVEL, RQ(C, L->a0, P));
        PASS(L->res);
        if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "composition family level annotation differs"));
        FR_AWAIT(k, L->y, F_FCDIMS, L->a1, 0);
        for (L->lw = dimset_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_local_atom(L->lw[L->d])) BAD("composition face must be in scope and independent of the bound dimension"); FR_YIELD(k); }
        L->lw = dimset_get(L->y, &L->n);
        for (L->i = 0; L->i < L->n; L->i++) { if (L->lw[L->i] == L->x) BAD("composition face must be in scope and independent of the bound dimension"); FR_YIELD(k); }
        FR_AWAIT(k, L->a4, F_REINDEX, L->a0, dim_at(L->x, iv_zero()));          /* A(0) */
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->a4, P));
        PASS(L->res);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a1);
        if (!fc_is_false(L->z)) {
            FR_AWAIT(k, L->a5, F_REINDEX, L->a2, dim_at(L->x, iv_zero()));      /* u(0) */
            FR_AWAIT(k, L->cl, J_CLAUSES, L->z, 0);
            for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                L->y = rget(L->cl, &L->nc)[L->c];
                JRQ(L->res, J_CHECK, RQ(L->y, L->a2, L->a0, P));
                PASS(L->res);
                JRQ(L->res, J_CONVt, RQ(L->y, L->a5, L->a3, L->a4, P));
                if (jr_code(L->res) == J_BAD) BAD("composition: tube at 0 disagrees with the cap");
                if (jr_code(L->res) == J_UNR) UNR("unresolved: cap/tube agreement");
            }
        }
        FR_AWAIT(k, r, F_REINDEX, L->a0, dim_at(L->x, iv_one()));
        DONE(J_OK, NULL, r, 0, 0);
    }
    if (L->tag == T_SYSTEM) {
        /* guards and branch types are keyed values (fields, the inference of
         * a branch under its consistent guard): read again where needed */
        L->n = tnode_nfields(ref_tnode(t)) / 2;
        L->x = fc_false();
        for (L->i = 0; L->i < L->n; L->i++) {
            FR_AWAIT(k, L->y, F_FIELD, t, 2 * L->i);
            FR_AWAIT(k, L->x, F_FCJOIN, L->x, L->y);
        }
        FR_AWAIT(k, r, F_FCENT, C, L->x);
        if (r != 2) BAD("system does not cover the face");
        L->j2 = L->n;                                                   /* the selected branch */
        for (L->i = 0; L->i < L->n; L->i++) {
            FR_AWAIT(k, L->u, F_FIELD, t, 2 * L->i);
            FR_AWAIT(k, L->y, F_FCDIMS, L->u, 0);
            for (L->lw = dimset_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_local_atom(L->lw[L->d])) BAD("system guard mentions an undeclared dimension"); FR_YIELD(k); }
            FR_AWAIT(k, L->y, F_FCMEET, C, L->u);
            if (fc_is_false(L->y)) continue;
            FR_AWAIT(k, L->z, F_FIELD, t, 2 * L->i + 1);
            JRQ(L->res, J_INFER, RQ(L->y, L->z, P));
            if (jr_code(L->res) != J_OK) DONE(jr_code(L->res), jr_why(L->res), 0, 0, 0);
            if (L->j2 == L->n) {
                FR_AWAIT(k, r, F_FCENT, C, L->u);
                if (r == 2) L->j2 = L->i;
            }
        }
        /* overlaps: branches agree in their (convertible) types and values */
        for (L->i = 0; L->i < L->n; L->i++) {
            for (L->q = L->i + 1; L->q < L->n; L->q++) {
                FR_AWAIT(k, L->a2, F_FIELD, t, 2 * L->i);
                FR_AWAIT(k, L->a3, F_FIELD, t, 2 * L->q);
                FR_AWAIT(k, L->y, F_FCMEET, L->a2, L->a3);
                FR_AWAIT(k, L->y, F_FCMEET, C, L->y);
                if (fc_is_false(L->y)) continue;
                FR_AWAIT(k, L->a0, F_FIELD, t, 2 * L->i + 1);
                FR_AWAIT(k, L->a1, F_FIELD, t, 2 * L->q + 1);
                FR_AWAIT(k, L->u, F_FCMEET, C, L->a2);
                JRQ(L->res, J_INFER, RQ(L->u, L->a0, P));
                L->l1 = jr_a(L->res);
                FR_AWAIT(k, L->u, F_FCMEET, C, L->a3);
                JRQ(L->res, J_INFER, RQ(L->u, L->a1, P));
                L->l2 = jr_a(L->res);
                FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
                for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                    L->w0 = rget(L->cl, &L->nc)[L->c];
                    JRQ(L->res, J_CONVT, RQ(L->w0, L->l1, L->l2, P));
                    if (jr_code(L->res) == J_OK) JRQ(L->res, J_CONVt, RQ(L->w0, L->a0, L->a1, L->l1, P));
                    if (jr_code(L->res) == J_BAD) BAD("system branches disagree on an overlap");
                    if (jr_code(L->res) == J_UNR) UNR("unresolved: system overlap");
                }
            }
        }
        require(L->j2 < L->n, "a covered system has an entailed branch under a single clause");
        FR_AWAIT(k, L->u, F_FIELD, t, 2 * L->j2);
        FR_AWAIT(k, L->y, F_FCMEET, C, L->u);
        FR_AWAIT(k, L->z, F_FIELD, t, 2 * L->j2 + 1);
        JRQ(L->res, J_INFER, RQ(L->y, L->z, P));
        DONE(J_OK, NULL, jr_a(L->res), 0, 0);
    }
    if (L->tag == T_GLOBAL) {
        FR_AWAIT(k, L->x, F_HEAD, t, 0);
        JAW(L->res, J_DECL, RQ(L->x, P));
        PASS(L->res);
        JAW(L->res, J_TBOUND, RQ(C, t, P));        /* the arguments at the declared parameter types */
        PASS(L->res);
        FR_AWAIT(k, L->m, F_GARGS, t, 0);
        FR_AWAIT(k, r, F_REINDEX, global_type((SymbolId)L->x), L->m);
        DONE(J_OK, NULL, r, 0, 0);
    }
    BAD("no inference rule for this head");
    FR_END(k);
}

/* Glue data: A forms at l; α in scope; under each clause of C ∧ α the fibre T
 * forms at the same level and e : Equiv(T, A). [code, reason, l] */
static void glueok_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A, α, T, e, P */
    FR_BEGIN(k);
    JRQ(L->res, J_LEVEL, RQ(q[0], q[1], q[5]));
    PASS(L->res);
    L->l1 = jr_a(L->res);
    FR_AWAIT(k, L->x, F_FCMEET, q[0], q[2]);
    if (fc_is_false(L->x)) DONE(J_OK, NULL, L->l1, 0, 0);
    FR_AWAIT(k, L->cl, J_CLAUSES, L->x, 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
        L->y = rget(L->cl, &L->nc)[L->c];
        JRQ(L->res, J_LEVEL, RQ(L->y, q[3], q[5]));
        PASS(L->res);
        if (jr_a(L->res) != L->l1) BAD("Glue fibre type is not in the base's universe");
        JAW(L->z, J_EQUIV, RQ(L->l1, L->l1, q[3], q[1]));
        JRQ(L->res, J_CHECK, RQ(L->y, q[4], L->z, q[5]));
        PASS(L->res);
    }
    DONE(J_OK, NULL, L->l1, 0, 0);
    FR_END(k);
}

/* ---------------- checking against an expected type ---------------- */
static void check_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, A, P */
    uint64_t C = q[0], P = q[3]; RefId t = q[1];
    FR_BEGIN(k);
    L->T = q[2];
    if (!ref_is_var(t)) {
        FR_AWAIT(k, r, F_FCENT, C, ref_required(t));
        if (r != 2) BAD("occurrence outside its required face");
        L->tag = ref_tag(t);
    } else L->tag = 0;
    if (L->tag == T_LAM || L->tag == T_PAIR || L->tag == T_PLAM || L->tag == T_SYSTEM) {
        /* the checking forms; a template instance's boundary is not bypassed */
        JAW(L->res, J_TBOUND, RQ(C, t, P));
        PASS(L->res);
        FR_AWAIT(k, L->lv, F_HEAD, t, 1);
    }
    if (L->tag == T_LAM) {
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_PI, P));
        if (jr_code(L->res) == J_BAD) BAD("lambda checked against a non-product type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        JRQ(L->res, J_CONVT, RQ(C, L->a0, L->D, P));
        if (jr_code(L->res) == J_BAD) BAD("lambda domain differs from the expected domain");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: lambda domain conversion");
        JRQ(L->res, J_LEVEL, RQ(C, L->a0, P));
        PASS(L->res);
        if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "lambda domain level annotation differs"));
        L->x = conv_var(t, L->PP, L->PP, 0, L->D);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a1, F_BINDER, t, brec(S_TERM, 0, 1, L->y));
        FR_AWAIT(k, L->a2, F_BINDER, L->PP, brec(S_TERM, 0, 1, L->y));
        JRQ(r, J_CHECK, RQ(C, L->a1, L->a2, P));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PAIR) {
        if (tnode_nfields(ref_tnode(t)) == 3) {
            /* annotated (§59.2): the stored Σ forms at its stored level, converts
             * with the expected type and governs the components */
            FR_AWAIT(k, L->a2, F_FIELD, t, 2);
            JRQ(L->res, J_LEVEL, RQ(C, L->a2, P));
            PASS(L->res);
            if (!level_ok1(L->lv, jr_a(L->res))) BAD(level_why(L->lv, "pair annotation level differs"));
            JRQ(L->res, J_CONVT, RQ(C, L->a2, L->T, P));
            if (jr_code(L->res) == J_BAD) BAD("pair annotation differs from the expected type");
            if (jr_code(L->res) == J_UNR) UNR("unresolved: pair annotation conversion");
            L->T = L->a2;
        }
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_SIGMA, P));
        if (jr_code(L->res) == J_BAD) BAD("pair checked against a non-sum type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->D, F_FIELD, L->PP, 0);
        FR_AWAIT(k, L->a0, F_FIELD, t, 0);
        FR_AWAIT(k, L->a1, F_FIELD, t, 1);
        JRQ(L->res, J_CHECK, RQ(C, L->a0, L->D, P));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_BINDER, L->PP, brec(S_TERM, 0, 1, L->a0));
        JRQ(r, J_CHECK, RQ(C, L->a1, L->a3, P));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PLAM) {
        JAW(L->res, J_OBSHEAD, RQ(C, L->T, T_PATH, P));
        if (jr_code(L->res) == J_BAD) BAD("path lambda checked against a non-path type");
        PASS(L->res);
        L->PP = jr_a(L->res);
        FR_AWAIT(k, L->a1, F_FIELD, L->PP, 1);
        FR_AWAIT(k, L->a2, F_FIELD, L->PP, 2);
        L->x = conv_dim(t, L->PP, 0);
        FR_AWAIT(k, L->a3, F_BINDER, t, brec(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a4, F_BINDER, L->PP, brec(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CHECK, RQ(C, L->a3, L->a4, P));
        PASS(L->res);
        FR_AWAIT(k, L->a3, F_BINDER, t, brec(S_DIM, 0, 0, iv_zero()));
        FR_AWAIT(k, L->a4, F_BINDER, L->PP, brec(S_DIM, 0, 0, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->a3, L->a1, L->a4, P));
        if (jr_code(L->res) == J_OK) {
            FR_AWAIT(k, L->a3, F_BINDER, t, brec(S_DIM, 0, 0, iv_one()));
            FR_AWAIT(k, L->a4, F_BINDER, L->PP, brec(S_DIM, 0, 0, iv_one()));
            JRQ(L->res, J_CONVt, RQ(C, L->a3, L->a2, L->a4, P));
        }
        if (jr_code(L->res) == J_BAD) BAD("path lambda endpoints differ from the path type's endpoints");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: path endpoint conversion");
        OK0();
    }
    if (L->tag == T_SYSTEM) {
        L->n = tnode_nfields(ref_tnode(t)) / 2;
        L->x = fc_false();
        for (L->i = 0; L->i < L->n; L->i++) {
            FR_AWAIT(k, L->y, F_FIELD, t, 2 * L->i);
            FR_AWAIT(k, L->x, F_FCJOIN, L->x, L->y);
        }
        FR_AWAIT(k, r, F_FCENT, C, L->x);
        if (r != 2) BAD("system does not cover the face");
        for (L->i = 0; L->i < L->n; L->i++) {
            FR_AWAIT(k, L->u, F_FIELD, t, 2 * L->i);
            FR_AWAIT(k, L->y, F_FCDIMS, L->u, 0);
            for (L->lw = dimset_get(L->y, &L->dn), L->d = 0; L->d < L->dn; L->d++) { if (is_local_atom(L->lw[L->d])) BAD("system guard mentions an undeclared dimension"); FR_YIELD(k); }
            FR_AWAIT(k, L->y, F_FCMEET, C, L->u);
            if (fc_is_false(L->y)) continue;
            FR_AWAIT(k, L->z, F_FIELD, t, 2 * L->i + 1);
            FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
            for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                JRQ(L->res, J_CHECK, RQ(rget(L->cl, &L->nc)[L->c], L->z, L->T, P));
                if (jr_code(L->res) != J_OK) DONE(jr_code(L->res), jr_why(L->res), 0, 0, 0);
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
                FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
                for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                    JRQ(L->res, J_CONVt, RQ(rget(L->cl, &L->nc)[L->c], L->a0, L->a1, L->T, P));
                    if (jr_code(L->res) == J_BAD) BAD("system branches disagree on an overlap");
                    if (jr_code(L->res) == J_UNR) UNR("unresolved: system overlap");
                }
            }
        }
        OK0();
    }
    JRQ(L->res, J_INFER, RQ(C, t, P));
    PASS(L->res);
    JRQ(L->res, J_CONVT, RQ(C, jr_a(L->res), L->T, P));
    if (jr_code(L->res) == J_OK) OK0();
    if (jr_code(L->res) == J_BAD) BAD("inferred type is not convertible to the expected type");
    UNR("unresolved: type conversion");
    FR_END(k);
}

/* ---------------- conversion ---------------- */
/* two observations under C as one join: 0 unless both completed normally */
/* two independent observations under C: launched, then awaited in order */
#define OBS_TWO(Cx, a, b) do { \
        family_launch(F_OBS, (a), observe_key((Cx), 0, P)); family_launch(F_OBS, (b), observe_key((Cx), 0, P)); \
    } while (0)
static bool obs_ok(EvalResult r) { return r.cls != R_INVALID && r.cls != R_NO_OBSERVATION; }
/* the common level of a Glue's base and fibre: the annotation, else inferred */
#define GLUE_LEVEL(dst, levels, Cx, A) do { \
        if (levels_first(levels) != LEVEL_NONE) dst = levels_first(levels); \
        else { JRQ(L->res, J_LEVEL, RQ((Cx), (A), P)); dst = jr_code(L->res) == J_OK ? jr_a(L->res) : LEVEL_NONE; } \
    } while (0)

static void convT_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, A, B, P */
    uint64_t C = q[0], P = q[3];
    FR_BEGIN(k);
    if (q[1] == q[2]) FR_FINISH(k, judge_res(J_OK, NULL, 0, 0, 0));
    OBS_TWO(C, q[1], q[2]);
    FR_AWAIT(k, L->r1, F_OBS, q[1], observe_key(C, 0, P));
    FR_AWAIT(k, L->r2, F_OBS, q[2], observe_key(C, 0, P));
    if (!obs_ok(R1) || !obs_ok(R2)) UNR(NULL);
    if (R1.ref == R2.ref) OK0();
    if (R1.cls == R_SYSTEM || R2.cls == R_SYSTEM) UNR(NULL);
    if (R1.cls != R2.cls) BAD(NULL);
    if (R1.cls == R_NEUTRAL) { JAW(r, J_SPINE, RQ(C, R1.ref, R2.ref, P)); FR_FINISH(k, r); }
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
        JRQ(L->res, J_CONVT, RQ(C, L->a2, L->a3, P));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        L->x = conv_var(L->a0, L->a1, L->a0, 0, L->a2);
        FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
        FR_AWAIT(k, L->a4, F_BINDER, L->a0, brec(S_TERM, 0, 1, L->y));
        FR_AWAIT(k, L->a5, F_BINDER, L->a1, brec(S_TERM, 0, 1, L->y));
        JRQ(r, J_CONVT, RQ(C, L->a4, L->a5, P));
        FR_FINISH(k, r);
    }
    if (L->tag == T_PATH) {
        L->x = conv_dim(L->a0, L->a1, 0);
        FR_AWAIT(k, L->a2, F_BINDER, L->a0, brec(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a3, F_BINDER, L->a1, brec(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CONVT, RQ(C, L->a2, L->a3, P));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->y, F_FIELD, L->a0, 1);
        FR_AWAIT(k, L->z, F_FIELD, L->a1, 1);
        FR_AWAIT(k, L->a4, F_REINDEX, L->a2, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->y, L->z, L->a4, P));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->y, F_FIELD, L->a0, 2);
        FR_AWAIT(k, L->z, F_FIELD, L->a1, 2);
        FR_AWAIT(k, L->a4, F_REINDEX, L->a2, dim_at(L->x, iv_one()));
        JRQ(r, J_CONVt, RQ(C, L->y, L->z, L->a4, P));
        FR_FINISH(k, r);
    }
    if (L->tag == T_GLUE_TYPE) {
        FR_AWAIT(k, L->a2, F_FIELD, L->a0, 1);
        FR_AWAIT(k, L->a3, F_FIELD, L->a1, 1);
        FR_AWAIT(k, L->y, F_FCMEET, C, L->a2);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a3);
        if (L->y != L->z) BAD(NULL);
        FR_AWAIT(k, L->a4, F_FIELD, L->a0, 0);
        FR_AWAIT(k, L->a5, F_FIELD, L->a1, 0);
        JRQ(L->res, J_CONVT, RQ(C, L->a4, L->a5, P));
        if (jr_code(L->res) != J_OK || fc_is_false(L->y)) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->lv, F_HEAD, L->a0, 1);
        FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
        for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
            L->u = rget(L->cl, &L->nc)[L->c];
            FR_AWAIT(k, L->y, F_FIELD, L->a0, 2);
            FR_AWAIT(k, L->z, F_FIELD, L->a1, 2);
            JRQ(L->res, J_CONVT, RQ(L->u, L->y, L->z, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            GLUE_LEVEL(L->l1, L->lv, L->u, L->a4);
            if (L->l1 == LEVEL_NONE) UNR(NULL);
            JAW(L->T, J_EQUIV, RQ(L->l1, L->l1, L->y, L->a4));
            FR_AWAIT(k, L->y, F_FIELD, L->a0, 3);
            FR_AWAIT(k, L->z, F_FIELD, L->a1, 3);
            JRQ(L->res, J_CONVt, RQ(L->u, L->y, L->z, L->T, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        }
        OK0();
    }
    BAD(NULL);                                     /* an introduction that is not a type former */
    FR_END(k);
}

static void convt_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, u, A, P */
    uint64_t C = q[0], P = q[4]; RefId t = q[1], u = q[2];
    FR_BEGIN(k);
    if (t == u) OK0();
    FR_AWAIT(k, L->r1, F_OBS, q[3], observe_key(C, 0, P));
    if (!obs_ok(R1)) UNR(NULL);
    if (R1.cls == R_INTRODUCTION) {
        L->a0 = R1.ref; L->tag = ref_tag(L->a0);
        if (L->tag == T_PI) {
            FR_AWAIT(k, L->D, F_FIELD, L->a0, 0);
            L->x = conv_var(t, u, L->a0, 0, L->D);
            FR_AWAIT(k, L->y, F_REFVAR, L->x, 0);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, brec(S_TERM, 0, 1, L->y));
            FR_CALL(k, L->a2, mk_app_sub(k, t, L->y));
            FR_CALL(k, L->a3, mk_app_sub(k, u, L->y));
            JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->a1, P));
            FR_FINISH(k, r);
        }
        if (L->tag == T_SIGMA) {
            FR_AWAIT(k, L->D, F_FIELD, L->a0, 0);
            FR_CALL(k, L->a2, mk_proj_sub(k, T_FST, t));
            FR_CALL(k, L->a3, mk_proj_sub(k, T_FST, u));
            JRQ(L->res, J_CONVt, RQ(C, L->a2, L->a3, L->D, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, brec(S_TERM, 0, 1, L->a2));
            FR_CALL(k, L->a2, mk_proj_sub(k, T_SND, t));
            FR_CALL(k, L->a3, mk_proj_sub(k, T_SND, u));
            JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->a1, P));
            FR_FINISH(k, r);
        }
        if (L->tag == T_PATH) {
            L->x = conv_dim(t, u, 0);
            L->y = binder_dim_var(L->a0, 0);
            FR_AWAIT(k, L->a1, F_BINDER, L->a0, brec(S_DIM, 0, 0, iv_var(L->y)));     /* B(j') at the binder's own name */
            FR_AWAIT(k, L->a2, F_REINDEX, L->a1, dim_at(L->y, iv_var(L->x)));          /* B(j) */
            FR_AWAIT(k, L->a3, F_FIELD, L->a0, 1);
            FR_AWAIT(k, L->a4, F_FIELD, L->a0, 2);
            FR_AWAIT(k, L->lv, F_HEAD, L->a0, 1);
            FR_CALL(k, L->a5, mk_papp_sub(k, levels_first(L->lv), (DimVarId)L->y, L->a1, L->a3, L->a4, t, iv_var(L->x)));
            FR_CALL(k, L->T, mk_papp_sub(k, levels_first(L->lv), (DimVarId)L->y, L->a1, L->a3, L->a4, u, iv_var(L->x)));
            JRQ(r, J_CONVt, RQ(C, L->a5, L->T, L->a2, P));
            FR_FINISH(k, r);
        }
        if (L->tag == T_GLUE_TYPE) {
            /* non-collapsed Glue: Glue η */
            FR_AWAIT(k, L->a1, F_FIELD, L->a0, 0);
            FR_AWAIT(k, L->a2, F_FIELD, L->a0, 1);
            FR_AWAIT(k, L->a3, F_FIELD, L->a0, 2);
            FR_AWAIT(k, L->a4, F_FIELD, L->a0, 3);
            FR_AWAIT(k, L->lv, F_HEAD, L->a0, 1);
            FR_CALL(k, L->y, mk_unglue_sub(k, levels_first(L->lv), L->a1, L->a2, L->a3, L->a4, t));
            FR_CALL(k, L->z, mk_unglue_sub(k, levels_first(L->lv), L->a1, L->a2, L->a3, L->a4, u));
            JRQ(L->res, J_CONVt, RQ(C, L->y, L->z, L->a1, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            FR_AWAIT(k, L->x, F_FCMEET, C, L->a2);
            if (fc_is_false(L->x)) OK0();
            FR_AWAIT(k, L->cl, J_CLAUSES, L->x, 0);
            for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                JRQ(L->res, J_CONVt, RQ(rget(L->cl, &L->nc)[L->c], t, u, L->a3, P));
                if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            }
            OK0();
        }
        if (L->tag == T_UNIVERSE) { JRQ(r, J_CONVT, RQ(C, t, u, P)); FR_FINISH(k, r); }
        BAD(NULL);
    }
    if (R1.cls == R_NEUTRAL) {
        /* neutral expected type: observe the terms and compare their neutral structures */
        OBS_TWO(C, t, u);
        FR_AWAIT(k, L->r1, F_OBS, t, observe_key(C, 0, P));
        FR_AWAIT(k, L->r2, F_OBS, u, observe_key(C, 0, P));
        if (!obs_ok(R1) || !obs_ok(R2)) UNR(NULL);
        if (R1.ref == R2.ref) OK0();
        if (R1.cls == R_NEUTRAL && R2.cls == R_NEUTRAL) { JAW(r, J_SPINE, RQ(C, R1.ref, R2.ref, P)); FR_FINISH(k, r); }
        if (R1.cls == R_SYSTEM || R2.cls == R_SYSTEM) UNR(NULL);
        BAD(NULL);
    }
    UNR(NULL);                                     /* a system type under a single clause is not a covered type */
    FR_END(k);
}

/* structural comparison of neutral spines */
static void spine_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, n1, n2, P */
    uint64_t C = q[0], P = q[3]; RefId n1 = q[1], n2 = q[2];
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
            FR_AWAIT(k, L->a0, F_IVRE, L->a0, L->m);
            FR_AWAIT(k, L->a1, F_IVRE, L->a1, L->m);
            if (L->a0 != L->a1) BAD(NULL);
        }
        if (L->tag == T_UNGLUE) {
            FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
            FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
            FR_AWAIT(k, L->y, F_FCMEET, C, L->a2);
            FR_AWAIT(k, L->z, F_FCMEET, C, L->a3);
            if (L->y != L->z) BAD(NULL);
            FR_AWAIT(k, L->a4, F_FIELD, n1, 0);
            FR_AWAIT(k, L->a5, F_FIELD, n2, 0);
            JRQ(L->res, J_CONVT, RQ(C, L->a4, L->a5, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
            if (!fc_is_false(L->y)) {
                FR_AWAIT(k, L->lv, F_HEAD, n1, 1);
                FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
                for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                    L->u = rget(L->cl, &L->nc)[L->c];
                    FR_AWAIT(k, L->y, F_FIELD, n1, 2);
                    FR_AWAIT(k, L->z, F_FIELD, n2, 2);
                    JRQ(L->res, J_CONVT, RQ(L->u, L->y, L->z, P));
                    if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
                    GLUE_LEVEL(L->l1, L->lv, L->u, L->a4);
                    if (L->l1 == LEVEL_NONE) UNR(NULL);
                    JAW(L->T, J_EQUIV, RQ(L->l1, L->l1, L->y, L->a4));
                    FR_AWAIT(k, L->y, F_FIELD, n1, 3);
                    FR_AWAIT(k, L->z, F_FIELD, n2, 3);
                    JRQ(L->res, J_CONVt, RQ(L->u, L->y, L->z, L->T, P));
                    if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
                }
            }
        }
        /* the scrutinees, observed as one join; both must be neutral */
        {   size_t f = L->tag == T_PAPP ? 3 : L->tag == T_UNGLUE ? 4 : 0; L->i = f; }
        FR_AWAIT(k, L->a0, F_FIELD, n1, L->i);
        FR_AWAIT(k, L->a1, F_FIELD, n2, L->i);
        OBS_TWO(C, L->a0, L->a1);
        FR_AWAIT(k, L->r1, F_OBS, L->a0, observe_key(C, 0, P));
        FR_AWAIT(k, L->r2, F_OBS, L->a1, observe_key(C, 0, P));
        if (!obs_ok(R1) || !obs_ok(R2) || R1.cls != R_NEUTRAL || R2.cls != R_NEUTRAL) UNR(NULL);
        JAW(L->res, J_SPINE, RQ(C, R1.ref, R2.ref, P));
        if (jr_code(L->res) != J_OK || L->tag != T_APP) FR_FINISH(k, L->res);
        /* an application: the arguments at the function's domain */
        JRQ(L->res, J_INFER, RQ(C, L->a0, P));
        if (jr_code(L->res) != J_OK) UNR(NULL);
        JAW(L->res, J_OBSHEAD, RQ(C, jr_a(L->res), T_PI, P));
        if (jr_code(L->res) != J_OK) UNR(NULL);
        FR_AWAIT(k, L->D, F_FIELD, jr_a(L->res), 0);
        FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
        FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
        JRQ(r, J_CONVt, RQ(C, L->a2, L->a3, L->D, P));
        FR_FINISH(k, r);
    }
    if (L->tag == T_COMP) {
        FR_AWAIT(k, L->a2, F_FIELD, n1, 1);
        FR_AWAIT(k, L->a3, F_FIELD, n2, 1);
        FR_AWAIT(k, L->y, F_FCMEET, C, L->a2);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a3);
        if (L->y != L->z) BAD(NULL);
        L->x = conv_dim(n1, n2, 0);
        FR_AWAIT(k, L->a0, F_BINDER, n1, brec(S_DIM, 0, 0, iv_var(L->x)));
        FR_AWAIT(k, L->a1, F_BINDER, n2, brec(S_DIM, 0, 0, iv_var(L->x)));
        JRQ(L->res, J_CONVT, RQ(C, L->a0, L->a1, P));
        if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->a4, F_FIELD, n1, 3);
        FR_AWAIT(k, L->a5, F_FIELD, n2, 3);
        FR_AWAIT(k, L->T, F_REINDEX, L->a0, dim_at(L->x, iv_zero()));
        JRQ(L->res, J_CONVt, RQ(C, L->a4, L->a5, L->T, P));
        if (jr_code(L->res) != J_OK || fc_is_false(L->y)) FR_FINISH(k, L->res);
        FR_AWAIT(k, L->a4, F_BINDER, n1, brec(S_DIM, 0, 2, iv_var(L->x)));
        FR_AWAIT(k, L->a5, F_BINDER, n2, brec(S_DIM, 0, 2, iv_var(L->x)));
        FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
        for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
            JRQ(L->res, J_CONVt, RQ(rget(L->cl, &L->nc)[L->c], L->a4, L->a5, L->a0, P));
            if (jr_code(L->res) != J_OK) FR_FINISH(k, L->res);
        }
        OK0();
    }
    if (L->tag == T_GLOBAL) {
        FR_AWAIT(k, L->x, F_HEAD, n1, 0);
        FR_AWAIT(k, L->y, F_HEAD, n2, 0);
        if (L->x != L->y) BAD(NULL);
        FR_AWAIT(k, L->a0, F_GARGS, n1, 0);
        FR_AWAIT(k, L->a1, F_GARGS, n2, 0);
        L->D = global_context_flat((SymbolId)L->x);
        L->n = context_size(L->D);
        for (L->i = 0; L->i < L->n; L->i++) {
            {   CtxDecl d = context_decl(L->D, L->i); L->tag = d.sort; L->u = d.id; L->T = d.sort == S_TERM ? term_var_type(d.id) : 0; }
            if (L->tag == S_DIM) {
                FR_AWAIT(k, L->a2, F_MAPD, L->a0, L->u);
                FR_AWAIT(k, L->a3, F_MAPD, L->a1, L->u);
                FR_AWAIT(k, L->m, J_CMAP, C, 0);
                FR_AWAIT(k, L->a2, F_IVRE, L->a2, L->m);
                FR_AWAIT(k, L->a3, F_IVRE, L->a3, L->m);
                if (L->a2 != L->a3) BAD(NULL);
            } else {
                FR_AWAIT(k, L->a2, F_MAPT, L->a0, L->u);
                FR_AWAIT(k, L->a3, F_MAPT, L->a1, L->u);
                FR_AWAIT(k, L->a4, F_REINDEX, L->T, L->a0);
                JRQ(L->res, J_CONVt, RQ(C, L->a2, L->a3, L->a4, P));
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
    L->lw = interner_get(&M.faces, k->w[0], &L->n);
    wordbuf_init(&L->wb);
    for (L->i = 0; L->i < L->n && L->lw[L->i] != DNF_SEP; L->i++) {
        wordbuf_push(&L->wb, FC_LIT_DIM(L->lw[L->i])); wordbuf_push(&L->wb, FC_LIT_EPS(L->lw[L->i]) ? iv_one() : iv_zero());
        FR_YIELD(k);
    }
    wordbuf_push(&L->wb, 0);
    FR_CALL(k, r, intern_sub(k, &M.maps, &L->wb, &L->created));
    FR_FINISH(k, r);
    FR_END(k);
}

/* ---------------- template instances ---------------- */
static void tview_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, t, P */
    RefId t = q[1];
    FR_BEGIN(k);
    JAW(L->res, J_TBOUND, RQ(q[0], t, q[2]));
    PASS(L->res);
    JAW(L->res, J_HEAD, RQ(q[0], t, q[2]));
    PASS(L->res);
    L->T = jr_a(L->res);
    {   ExprId te, le; if (!tnode_result_exprs(ref_tnode(t), &te, &le)) DONE(J_OK, NULL, L->T, 0, 0); L->x = te; }
    L->y = ref_tenv(t);
    FR_AWAIT(k, r, F_INTERP, L->x, L->y);
    { size_t n; L->D = rget(r, &n)[1]; }
    JRQ(L->res, J_CONVT, RQ(q[0], L->T, L->D, q[2]));
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
    JLOC;   /* q: C, t, P */
    uint64_t C = q[0], P = q[2]; RefId t = q[1];
    FR_BEGIN(k);
    if (ref_is_var(t)) OK0();
    /* finite structure of every retained image first (§50.1–2) */
    L->n = tenv_size(ref_tenv(t));
    for (L->i = 0; L->i < L->n; L->i++) {
        {   uint64_t slot; TVal val; tenv_entry(ref_tenv(t), L->i, &slot, &val); L->tag = val.sort; L->x = val.id; }
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
        FR_AWAIT(k, r, F_ENVLOOK, L->D, L->j2);
        require(r, "template boundary: a retained slot has no image");
        { size_t n; const uint64_t *ew = rget(L->D, &n); L->x = ew[1 + 3 * (r - 1) + 2]; }
        FR_AWAIT(k, r, F_INTERP, L->a0, L->D);
        { size_t n; L->T = rget(r, &n)[1]; }
        if (L->tag == PS_REF) {
            L->y = fc_true();
            if (L->a1) { FR_AWAIT(k, r, F_INTERP, L->a1, L->D); size_t n; L->y = rget(r, &n)[1]; }
            FR_AWAIT(k, L->y, F_FCMEET, C, L->y);
            FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
            for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
                JRQ(L->res, J_CHECK, RQ(rget(L->cl, &L->nc)[L->c], L->x, L->T, P));
                if (jr_code(L->res) == J_BAD) {
                    { char buf[256]; snprintf(buf, sizeof buf, "template parameter image is not of its declared type (%s slot %zu: %s)", tdef_name(tnode_def(ref_tnode(t))), L->j2, jr_why(L->res) ? jr_why(L->res) : ""); diag_words(&L->wb, buf); }
                    FR_CALL(k, L->w0, intern_sub(k, &M.keys, &L->wb, &L->created));
                    BAD(diag_text(L->w0));
                }
                PASS(L->res);
            }
        } else {
            JAW(L->res, J_SCARG, RQ(C, L->x, L->T, P));
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
/* open(S, key): the telescope at fresh locals keyed by (key, S, slot), each
 * declared at its type over the earlier fresh locals: [ids, arguments] */
static void scopen_step(Cont *k, uint64_t v) {
    JLOC;   /* q: S, key */
    ScopeId S = q[0];
    FR_BEGIN(k);
    L->n = scope_arity(S);
    wordbuf_init(&L->wc);
    L->a2 = interner_intern(&M.keys, NULL, 0, NULL);               /* the arguments so far: a record extended per local */
    for (L->i = 0; L->i < L->n; L->i++) {
        {   LocalDecl d = scope_local(S, L->i); L->tag = d.sort; L->T = d.type; L->a0 = d.required; }
        if (L->tag == S_DIM) {
            {   KeyWord kw[4] = { { KW_CONST, 9000 }, { KW_CONST, q[1] }, { KW_CONST, S }, { KW_CONST, L->i } };
                DimVarId j = fresh_dim_keyed(kw, 4); L->x = j; L->u = VS_INTERVAL; L->z = iv_var(j); }
        } else {
            L->y = trav_key(TR_APPLY, 0, L->a2);
            FR_AWAIT(k, L->T, F_TREF, L->T, L->y);
            FR_AWAIT(k, L->a0, F_TFC, L->a0, L->y);
            {   KeyWord kw[4] = { { KW_CONST, 9000 }, { KW_CONST, q[1] }, { KW_CONST, S }, { KW_CONST, L->i } };
                L->x = fresh_term_keyed_req(kw, 4, L->T, L->a0); }
            FR_AWAIT(k, L->z, F_REFVAR, L->x, 0);
            L->u = VS_REF;
        }
        wordbuf_push(&L->wc, L->x);
        wordbuf_init(&L->wb);
        for (L->q = 0; L->q < 2 * L->i; L->q++) { { size_t n_; wordbuf_push(&L->wb, rget(L->a2, &n_)[L->q]); } FR_YIELD(k); }
        wordbuf_push(&L->wb, L->u); wordbuf_push(&L->wb, L->z);
        FR_CALL(k, L->a2, intern_sub(k, &M.keys, &L->wb, &L->created));
    }
    FR_CALL(k, L->a1, intern_sub(k, &M.keys, &L->wc, &L->created));
    FR_FINISH(k, RQ(L->a1, L->a2));
    FR_END(k);
}
/* the APPLY key of the first k arguments of a full argument record */
static void aprefix_step(Cont *k, uint64_t v) {
    JL *L = FR_LOC(k, JL); uint64_t r = 0;
    FR_BEGIN(k);
    wordbuf_init(&L->wb);
    for (L->q = 0; L->q < 2 * k->w[1]; L->q++) { { size_t n; wordbuf_push(&L->wb, rget(k->w[0], &n)[L->q]); } FR_YIELD(k); }
    FR_CALL(k, r, intern_sub(k, &M.keys, &L->wb, &L->created));
    FR_FINISH(k, trav_key(TR_APPLY, 0, r));
    FR_END(k);
}

/* §50.1–4: a supplied scope's own validity in its own ambient-plus-local context */
static void scown_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, S, P */
    uint64_t C = q[0], P = q[2]; ScopeId S = q[1];
    FR_BEGIN(k);
    JAW(L->res, J_RV, RQ(1, S, 0));
    PASS(L->res);
    JAW(L->a5, J_SCOPEN, RQ(S, 0x52));
    { size_t n; const uint64_t *w = rget(L->a5, &n); L->a3 = w[0]; L->a4 = w[1]; }
    L->n = scope_arity(S); for (L->i = 0; L->i < L->n; L->i++) {
        {   LocalDecl d = scope_local(S, L->i); L->tag = d.sort; L->T = d.type; L->a0 = d.required; L->lv = d.level;
            size_t n; L->x = rget(L->a3, &n)[L->i]; }
        if (L->tag == S_DIM) { FR_YIELD(k); continue; }
        if (!L->T) BAD("scope local has no declared type");
        if (L->lv == LEVEL_NONE) BAD("missing universe annotation on a scope local (§59.1)");
        FR_AWAIT(k, L->y, J_APREFIX, L->a4, L->i);
        FR_AWAIT(k, L->T, F_TREF, L->T, L->y);
        FR_AWAIT(k, L->a0, F_TFC, L->a0, L->y);
        FR_AWAIT(k, L->z, F_FCMEET, C, L->a0);
        FR_AWAIT(k, L->cl, J_CLAUSES, L->z, 0);
        for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
            JRQ(L->res, J_LEVEL, RQ(rget(L->cl, &L->nc)[L->c], L->T, P));
            if (jr_code(L->res) == J_BAD) BAD("scope local type is not a type");
            PASS(L->res);
            if (jr_a(L->res) != L->lv) BAD("scope local level annotation differs from its formation level");
        }
    }
    if (scope_body(S).sort != VS_REF) OK0();
    if (!scope_type(S)) BAD("scope has no declared result type");
    if (scope_level(S) == LEVEL_NONE) BAD("missing universe annotation on a scope result (§59.1)");
    FR_AWAIT(k, L->y, J_APREFIX, L->a4, L->n);
    FR_AWAIT(k, L->T, F_TREF, scope_type(S), L->y);
    FR_AWAIT(k, L->a0, F_TFC, scope_guard(S), L->y);
    FR_AWAIT(k, L->a1, F_TREF, scope_body(S).id, L->y);
    FR_AWAIT(k, L->z, F_FCMEET, C, L->a0);
    FR_AWAIT(k, L->cl, J_CLAUSES, L->z, 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
        L->u = rget(L->cl, &L->nc)[L->c];
        JRQ(L->res, J_LEVEL, RQ(L->u, L->T, P));
        if (jr_code(L->res) == J_BAD) BAD("scope result type is not a type");
        PASS(L->res);
        if (jr_a(L->res) != scope_level(S)) BAD("scope result level annotation differs from its formation level");
        JRQ(L->res, J_CHECK, RQ(L->u, L->a1, L->T, P));
        PASS(L->res);
    }
    OK0();
    FR_END(k);
}
/* §51.4: a valid scope argument S at the expected contextual signature Sig,
 * both opened at the signature's fresh telescope */
static void scarg_step(Cont *k, uint64_t v) {
    JLOC;   /* q: C, S, Sig, P */
    uint64_t C = q[0], P = q[3]; ScopeId S = q[1], Sig = q[2];
    FR_BEGIN(k);
    L->n = scope_arity(S);
    if (L->n != scope_arity(Sig)) BAD("scope argument telescope length differs from the signature");
    for (L->i = 0; L->i < L->n; L->i++) { if (scope_local(S, L->i).sort != scope_local(Sig, L->i).sort) BAD("scope argument telescope sorts differ from the signature"); FR_YIELD(k); }
    if (scope_body(S).sort != scope_body(Sig).sort) BAD("scope argument body sort differs from the signature");
    JAW(L->res, J_SCOWN, RQ(C, S, P));
    PASS(L->res);
    JAW(L->a5, J_SCOPEN, RQ(Sig, 0x51));
    { size_t n; const uint64_t *w = rget(L->a5, &n); L->a3 = w[0]; L->a4 = w[1]; }
    for (L->i = 0; L->i < L->n; L->i++) {
        {   size_t n; L->x = rget(L->a3, &n)[L->i]; L->tag = scope_local(Sig, L->i).sort; L->T = scope_local(S, L->i).type; }
        if (L->tag == S_DIM) { FR_YIELD(k); continue; }
        FR_AWAIT(k, L->y, J_APREFIX, L->a4, L->i);
        FR_AWAIT(k, L->T, F_TREF, L->T, L->y);
        JRQ(L->res, J_CONVT, RQ(C, L->T, term_var_type(L->x), P));
        if (jr_code(L->res) == J_BAD) BAD("scope argument local type differs from the signature");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: scope argument local type conversion");
    }
    FR_AWAIT(k, L->y, J_APREFIX, L->a4, L->n);
    FR_AWAIT(k, L->a0, F_TFC, scope_guard(S), L->y);       /* supplied guard */
    FR_AWAIT(k, L->a1, F_TFC, scope_guard(Sig), L->y);     /* expected guard */
    FR_AWAIT(k, L->z, F_FCMEET, C, L->a1);
    FR_AWAIT(k, r, F_FCENT, L->z, L->a0);
    if (r != 2) BAD("scope argument is not available where the signature requires it");
    if (scope_body(S).sort != VS_REF) OK0();
    FR_AWAIT(k, L->T, F_TREF, scope_type(S), L->y);
    FR_AWAIT(k, L->D, F_TREF, scope_body(Sig).id, L->y);
    FR_AWAIT(k, L->cl, J_CLAUSES, L->z, 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
        JRQ(L->res, J_CONVT, RQ(rget(L->cl, &L->nc)[L->c], L->T, L->D, P));
        if (jr_code(L->res) == J_BAD) BAD("scope argument result type differs from the signature");
        if (jr_code(L->res) == J_UNR) UNR("unresolved: scope argument result type conversion");
    }
    OK0();
    FR_END(k);
}

/* ---------------- typed maps and contexts ---------------- */
/* σ : (D; ψ) → (Γ; χ) */
static void map_step(Cont *k, uint64_t v) {
    JLOC;   /* q: D, ψ, σ, Γ, χ, P */
    uint64_t D = q[0], psi = q[1], sigma = q[2], P = q[5];
    FR_BEGIN(k);
    JAW(L->res, J_CTX, RQ(q[3], q[4], P));
    PASS(L->res);
    JAW(L->res, J_CTX, RQ(D, psi, P));
    PASS(L->res);
    for (L->G2 = q[3]; !jc_is_empty(L->G2); L->G2 = jc_parent(L->G2)) {
        {   Sort so; uint64_t id; jc_decl(L->G2, &so, &id); L->tag = so; L->x = id; L->T = so == S_TERM ? term_var_type(id) : 0; }
        if (L->tag == S_DIM) {
            FR_AWAIT(k, L->y, F_MAPD, sigma, L->x);
            FR_AWAIT(k, L->y, F_IVDIMS, L->y, 0);
            JAW(r, J_DIMSIN, RQ(D, L->y));
            if (r != J_OK) BAD("dimension image mentions an undeclared source dimension");
            continue;
        }
        FR_AWAIT(k, L->y, F_MAPT, sigma, L->x);
        JAW(L->res, J_SCOPE, RQ(D, fc_true(), L->y));
        if (jr_code(L->res) != J_OK) BAD("term image is not in scope of the source context");
        FR_AWAIT(k, L->T, F_REINDEX, L->T, sigma);
        FR_AWAIT(k, L->z, F_FCRE, term_var_required(L->x), sigma);
        FR_AWAIT(k, L->z, F_FCMEET, psi, L->z);
        FR_AWAIT(k, L->cl, J_CLAUSES, L->z, 0);
        for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
            JRQ(L->res, J_CHECK, RQ(rget(L->cl, &L->nc)[L->c], L->y, L->T, P));
            PASS(L->res);
        }
    }
    FR_AWAIT(k, L->z, F_FCRE, q[4], sigma);
    FR_AWAIT(k, r, F_FCENT, psi, L->z);
    if (r != 2) BAD("source face does not entail the substituted target assumption");
    OK0();
    FR_END(k);
}
/* a context with assumption a: the assumption uses declared dimensions, and
 * every declaration is valid over its prefix */
static void ctx_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a, P */
    FR_BEGIN(k);
    FR_AWAIT(k, L->y, F_FCDIMS, q[1], 0);
    JAW(r, J_DIMSIN, RQ(q[0], L->y));
    if (r != J_OK) BAD("assumption mentions an undeclared dimension");
    JAW(r, J_CTXD, RQ(q[0], q[1], q[2]));
    FR_FINISH(k, r);
    FR_END(k);
}
static void ctxd_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a, P */
    FR_BEGIN(k);
    if (jc_is_empty(q[0])) OK0();
    family_launch(J_CTXD, RQ(jc_parent(q[0]), q[1], q[2]), 0);
    family_launch(J_DECLOK, RQ(q[0], q[1], q[2]), 0);
    JAW(L->x, J_CTXD, RQ(jc_parent(q[0]), q[1], q[2]));
    JAW(L->y, J_DECLOK, RQ(q[0], q[1], q[2]));
    FR_FINISH(k, jr_code(L->x) != J_OK ? L->x : L->y);
    FR_END(k);
}
/* the top declaration of G over its prefix (§2, §33 item 3, §59.2): not
 * declared earlier; a term variable's own type is a type in scope of the
 * earlier declarations */
static void declok_step(Cont *k, uint64_t v) {
    JLOC;   /* q: G, a, P */
    uint64_t P = q[2];
    FR_BEGIN(k);
    {   Sort so; uint64_t id; jc_decl(q[0], &so, &id); L->tag = so; L->x = id; }
    L->G2 = jc_parent(q[0]);
    if (L->tag == S_TERM ? jc_term(L->G2, L->x) : jc_dim(L->G2, L->x)) BAD("duplicate declaration");
    if (L->tag != S_TERM) OK0();
    L->T = term_var_type(L->x);
    JAW(L->res, J_SCOPE, RQ(L->G2, term_var_required(L->x), L->T));
    if (jr_code(L->res) != J_OK) BAD("declaration type is not in scope of the earlier declarations");
    FR_AWAIT(k, L->y, J_JDIMS, L->G2, 0);
    FR_AWAIT(k, L->y, F_FCPROJ, q[1], L->y);
    FR_AWAIT(k, L->y, F_FCMEET, L->y, term_var_required(L->x));
    FR_AWAIT(k, L->cl, J_CLAUSES, L->y, 0);
    for (L->c = 0; L->c < (rget(L->cl, &L->nc), L->nc); L->c++) {
        JRQ(L->res, J_LEVEL, RQ(rget(L->cl, &L->nc)[L->c], L->T, P));
        PASS(L->res);
    }
    OK0();
    FR_END(k);
}
/* a construction node at its generic instance: [code, reason, context,
 * required face, type] (every instance is typed by the substitution lemma) */
static void node_step(Cont *k, uint64_t v) {
    JLOC;   /* q: Q, P */
    uint64_t P = q[1];
    FR_BEGIN(k);
    FR_AWAIT(k, L->x, J_GENERIC, q[0], 0);
    { size_t n; const uint64_t *w = rget(L->x, &n); L->G2 = w[0]; L->a0 = w[1]; L->a1 = w[2]; }
    JAW(L->res, J_CTX, RQ(L->G2, L->a0, P));
    PASS(L->res);
    FR_AWAIT(k, L->cl, J_CLAUSES, L->a0, 0);
    rget(L->cl, &L->nc);
    L->y = 1; L->T = 0;
    for (L->c = 0; L->c < L->nc; L->c++) {
        JAW(L->res, J_HEAD, RQ(rget(L->cl, &L->n)[L->c], L->a1, P));
        if (jr_code(L->res) != J_OK) DONE(jr_code(L->res), jr_why(L->res), 0, 0, 0);
        if (L->c == 0) L->T = jr_a(L->res); else if (jr_a(L->res) != L->T) L->y = 0;
    }
    if (L->nc && L->y) DONE(J_OK, NULL, L->G2, L->a0, L->T);
    /* differing types per clause (or the false face): a system of them (each
     * clause's head type is its keyed judgment, read again) */
    creq_system_begin(&L->wb, L->nc);
    for (L->c = 0; L->c < L->nc; L->c++) {
        JAW(L->res, J_HEAD, RQ(rget(L->cl, &L->n)[L->c], L->a1, P));
        creq_system_branch(&L->wb, rget(L->cl, &L->n)[L->c], jr_a(L->res));
    }
    wordbuf_push(&L->wb, 0);
    FR_CALL(k, L->T, construct_buf_sub(k, &L->wb));
    DONE(J_OK, NULL, L->G2, L->a0, L->T);
    FR_END(k);
}

/* ---------------- global symbols ---------------- */
/* decl(s): the declared type is a type over the parameters */
static void decl_step(Cont *k, uint64_t v) {
    JLOC;   /* q: s, P */
    FR_BEGIN(k);
    if (!global_type((SymbolId)q[0])) BAD("symbol without a declared type");
    FR_AWAIT(k, L->G2, J_JCOF, global_context_flat((SymbolId)q[0]), 0);
    JAW(L->res, J_CTX, RQ(L->G2, fc_true(), q[1]));
    PASS(L->res);
    JAW(L->res, J_SCOPE, RQ(L->G2, fc_true(), global_type((SymbolId)q[0])));
    PASS(L->res);
    JRQ(L->res, J_LEVEL, RQ(fc_true(), global_type((SymbolId)q[0]), q[1]));
    PASS(L->res);
    OK0();
    FR_END(k);
}
/* body(s): the pinned body checks against the declaration */
static void body_step(Cont *k, uint64_t v) {
    JLOC;   /* q: s, P */
    FR_BEGIN(k);
    JAW(L->res, J_DECL, RQ(q[0], q[1]));
    PASS(L->res);
    {   RefId b = 0; if (!pins_lookup(q[1], (SymbolId)q[0], &b)) UNR("unresolved: a symbol outside the request's premises"); if (!b) OK0(); L->x = b; }
    FR_AWAIT(k, L->G2, J_JCOF, global_context_flat((SymbolId)q[0]), 0);
    JAW(L->res, J_SCOPE, RQ(L->G2, fc_true(), L->x));
    PASS(L->res);
    JRQ(r, J_CHECK, RQ(fc_true(), L->x, global_type((SymbolId)q[0]), q[1]));
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
    FR_AWAIT(k, L->y, q[0] ? F_FCDIMS : F_IVDIMS, q[1], 0);
    L->lw = dimset_get(L->y, &L->n);
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
        L->n = tenv_size(ref_tenv(x));
        for (L->i = 0; L->i < L->n; L->i++) {
            {   uint64_t slot; TVal val; tenv_entry(ref_tenv(x), L->i, &slot, &val); L->tag = val.sort; L->y = val.id; }
            if (L->tag == PS_LEVEL) { FR_YIELD(k); continue; }
            if (L->tag == PS_REF || L->tag == PS_SCOPE) JAW(L->res, J_RV, RQ(L->tag == PS_SCOPE ? 1 : 0, L->y, stk));
            else JAW(L->res, J_RVD, RQ(L->tag == PS_FACE ? 1 : 0, L->y, stk));
            PASS(L->res);
        }
        if (tnode_is_construction(ref_tnode(x))) {
            L->n = tnode_nfields(ref_tnode(x));
            for (L->i = 0; L->i < L->n; L->i++) {
                {   TNodeId Q = ref_tnode(x); L->tag = tnode_field_kind(Q, L->i); L->y = tnode_const_field(Q, L->i); }
                if (L->tag == F_REF) JAW(L->res, J_RV, RQ(0, L->y, stk));
                else JAW(L->res, J_RVD, RQ(L->tag == F_FACE ? 1 : 0, L->y, stk));
                PASS(L->res);
            }
            if (tnode_const_declared(ref_tnode(x))) { JAW(L->res, J_RVD, RQ(1, tnode_const_declared(ref_tnode(x)), stk)); PASS(L->res); }
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
    family_define(J_JCOF, "judge.ctx_of", jcof_step, sizeof(JL));
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
    family_define(J_SCOPEN, "judge.scope_open", scopen_step, sizeof(JL));
    family_define(J_APREFIX, "judge.args_prefix", aprefix_step, sizeof(JL));
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
}
Family judge_family(JudgeKind kind) {
    switch (kind) {
    case JK_INFER: return J_INFER; case JK_CHECK: return J_CHECK; case JK_LEVEL: return J_LEVEL;
    case JK_CONVT: return J_CONVT; case JK_CONVt: return J_CONVt; case JK_MAP: return J_MAP; case JK_CTX: return J_CTX;
    case JK_NODE: return J_NODE; case JK_DECL: return J_DECL; case JK_BODY: return J_BODY; case JK_STRUCT: return J_RV; case JK_SCOPE: return J_SCOPE; case JK_CLAUSES: return J_CLAUSES;
    }
    return 0;
}
uint64_t judge_request(size_t n, const uint64_t *w) { return rq(n, w); }

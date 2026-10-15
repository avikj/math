/* §37/§38 comparison checks: accept a consistent renaming with preserved
 * sharing; reject a changed payload, endpoint, guard or aliasing pattern;
 * include an ambiguous-refinement case so equality is never decided by
 * refinement classes alone. */
#define _POSIX_C_SOURCE 200809L
#include "../src/eval.h"
#include "../src/lib.h"
#include "../src/canon.h"

static int np = 0, nf = 0;
#define CHECK(c, ...) do { if (c) np++; else { nf++; printf("  FAIL: "); printf(__VA_ARGS__); printf("\n"); } } while (0)

static RefId var(RefId t) { return ref_var(declare_term(t, fc_true())); }

/* ---- hand-built graphs: refinement cannot separate these, matching must ---- */
static void test_ambiguous(void) {
    /* G1: root -> {A, A'} where A and A' share one child c       (aliased)
     * G2: root -> {B, B'} where B -> c1, B' -> c2 (identical labels, not shared)
     * Every node of G1 has the same refinement colour as its counterpart in G2;
     * the graphs are not isomorphic (sharing differs). */
    Graph *g1 = graph_new(), *g2 = graph_new();
    size_t r1 = graph_node(g1, 1, "root"), a1 = graph_node(g1, 2, "A"), a2 = graph_node(g1, 2, "A"), c = graph_node(g1, 3, "c");
    graph_unordered(g1, r1, a1); graph_unordered(g1, r1, a2); graph_ordered(g1, a1, c); graph_ordered(g1, a2, c); graph_root(g1, r1);
    size_t r2 = graph_node(g2, 1, "root"), b1 = graph_node(g2, 2, "A"), b2 = graph_node(g2, 2, "A"), c1 = graph_node(g2, 3, "c"), c2 = graph_node(g2, 3, "c");
    graph_unordered(g2, r2, b1); graph_unordered(g2, r2, b2); graph_ordered(g2, b1, c1); graph_ordered(g2, b2, c2); graph_root(g2, r2);
    MatchReport mr;
    bool eq = graph_match(g1, g2, &mr);
    CHECK(!eq, "aliasing difference under identical refinement colours is rejected");
    CHECK(strstr(mr.reason, "sharing") != NULL, "the reason names sharing (%s)", mr.reason);
    /* same sharing, children listed in the other order, plus an extra aliased pair → accepted by backtracking */
    Graph *g3 = graph_new();
    size_t r3 = graph_node(g3, 1, "root"), d2 = graph_node(g3, 2, "A"), d1 = graph_node(g3, 2, "A"), cc = graph_node(g3, 3, "c");
    graph_unordered(g3, r3, d2); graph_unordered(g3, r3, d1); graph_ordered(g3, d1, cc); graph_ordered(g3, d2, cc); graph_root(g3, r3);
    CHECK(graph_match(g1, g3, &mr), "same sharing in another order is accepted");
    /* ambiguous unordered children where the first candidate choice is wrong: two
     * pairs {P,Q} with P->x, Q->y on the left and the mirror on the right, x,y
     * themselves aliased elsewhere so the choice matters */
    Graph *g4 = graph_new(), *g5 = graph_new();
    {
        size_t r = graph_node(g4, 1, "root"), p = graph_node(g4, 2, "P"), q = graph_node(g4, 2, "P"), x = graph_node(g4, 3, "x"), y = graph_node(g4, 3, "x"), w = graph_node(g4, 4, "w");
        graph_unordered(g4, r, p); graph_unordered(g4, r, q); graph_ordered(g4, p, x); graph_ordered(g4, q, y); graph_ordered(g4, r, w); graph_ordered(g4, w, x); graph_root(g4, r);
    }
    {
        size_t r = graph_node(g5, 1, "root"), p = graph_node(g5, 2, "P"), q = graph_node(g5, 2, "P"), x = graph_node(g5, 3, "x"), y = graph_node(g5, 3, "x"), w = graph_node(g5, 4, "w");
        graph_unordered(g5, r, q); graph_unordered(g5, r, p); graph_ordered(g5, p, x); graph_ordered(g5, q, y); graph_ordered(g5, r, w); graph_ordered(g5, w, y); graph_root(g5, r);
    }
    CHECK(graph_match(g4, g5, &mr), "isomorphic graphs needing backtracking are accepted (%zu backtracks)", mr.backtracks);
    /* nested choice revisited: R -> [P, X]; P -> {a, b}; X -> [a]  vs  the same with X -> [b]
     * (isomorphic by a↔b', b↔a'; refinement cannot split a from b; the inner
     * choice for P must be revisited when X's ordered edge contradicts it) */
    Graph *g6 = graph_new(), *g7 = graph_new();
    {
        size_t r = graph_node(g6, 1, "R"), p = graph_node(g6, 2, "P"), xx = graph_node(g6, 3, "X"), a1 = graph_node(g6, 4, "a"), b1 = graph_node(g6, 4, "a");
        graph_ordered(g6, r, p); graph_ordered(g6, r, xx); graph_unordered(g6, p, a1); graph_unordered(g6, p, b1); graph_ordered(g6, xx, a1); graph_root(g6, r);
    }
    {
        size_t r = graph_node(g7, 1, "R"), p = graph_node(g7, 2, "P"), xx = graph_node(g7, 3, "X"), a1 = graph_node(g7, 4, "a"), b1 = graph_node(g7, 4, "a");
        graph_ordered(g7, r, p); graph_ordered(g7, r, xx); graph_unordered(g7, p, a1); graph_unordered(g7, p, b1); graph_ordered(g7, xx, b1); graph_root(g7, r);
    }
    CHECK(graph_match(g6, g7, &mr), "an inner unordered choice is revisited when a later ordered edge contradicts it (%zu backtracks)", mr.backtracks);
    graph_free(g6); graph_free(g7);
    graph_free(g1); graph_free(g2); graph_free(g3); graph_free(g4); graph_free(g5);
}

/* ---- real machine graphs ---- */
typedef enum { V_BASE, V_RENAMED, V_PAYLOAD, V_ENDPOINT, V_GUARD, V_ALIAS } Variant;

static Graph *build(Variant v) {
    machine_init(); eval_init();
    RefId U0 = mk_universe(0), A = var(U0), T = var(U0);
    DimVarId d1 = declare_dim(), d2 = declare_dim();
    DimVarId i = (v == V_RENAMED) ? d2 : d1, m = (v == V_RENAMED) ? d1 : d2;
    /* V_RENAMED swaps which input dimension plays which role: input names are
     * anchored by declaration index, so this must be rejected like any other
     * change of the input; generated names are renamed freely across runs */
    RefId a = var(A), b = var(A);
    RefId e = var(mk_equiv(0, 0, T, A));
    FaceId guard = (v == V_GUARD) ? fc_lit(m, 0) : fc_lit(m, 1);
    RefId Gm = mk_glue_type_lv(0, A, guard, T, e);
    RefId cg = mk_coe_at(0, i, Gm, var(Gm));
    RefId p = var(mk_path_const(0, A, a, b));
    IntervalId s = (v == V_ENDPOINT) ? iv_negate(iv_var(i)) : iv_var(i);
    RefId pi = mk_papp_const(0, A, a, b, p, s);
    RefId pair = (v == V_ALIAS) ? mk_pair(cg, mk_coe_at(0, i, Gm, var(Gm))) : mk_pair(cg, cg);   /* aliasing: both fields one reference */
    RefId lvl = (v == V_PAYLOAD) ? mk_universe(1) : mk_universe(0);
    WhnfStatus st;
    Canon *c = canon_new();
    canon_add_result(c, "cg", whnf(cg, fc_true(), &st));
    canon_add_result(c, "unglue", whnf(mk_unglue_lv(0, A, guard, T, e, cg), fc_true(), &st));
    canon_add_result(c, "pi", whnf(pi, fc_true(), &st));
    canon_add_result(c, "pair", whnf(pair, fc_true(), &st));
    canon_add_result(c, "lvl", whnf(lvl, fc_true(), &st));
    size_t ne = eval_entry_count();
    for (EntryId eid = 1; eid <= ne; eid++) { size_t r, d, pb; eval_entry_events(eid, &r, &d, &pb); canon_add_key(c, eval_entry_ref(eid), eval_entry_face(eid), r, d, pb, (int)eval_entry_state(eid)); }
    Graph *g = canon_export(c);
    canon_free(c); eval_free(); machine_free();
    return g;
}

static void test_machine_graphs(void) {
    Graph *base = build(V_BASE), *again = build(V_BASE);
    MatchReport mr;
    CHECK(graph_match(base, again, &mr), "two runs of the same configuration match (%zu classes)", mr.classes_joint);
    Graph *g;
    g = build(V_PAYLOAD); CHECK(!graph_match(base, g, &mr), "changed universe level (payload) is rejected: %s", mr.reason); graph_free(g);
    g = build(V_ENDPOINT); CHECK(!graph_match(base, g, &mr), "changed interval endpoint is rejected: %s", mr.reason); graph_free(g);
    g = build(V_GUARD); CHECK(!graph_match(base, g, &mr), "changed Glue guard is rejected: %s", mr.reason); graph_free(g);
    g = build(V_ALIAS); CHECK(!graph_match(base, g, &mr), "changed aliasing (two copies vs one shared reference) is rejected: %s", mr.reason); graph_free(g);
    g = build(V_RENAMED); CHECK(!graph_match(base, g, &mr), "swapping anchored input dimensions is rejected: %s", mr.reason); graph_free(g);
    graph_free(base); graph_free(again);
}

/* generated names renamed: evaluate the same configuration after minting
 * unrelated generated names first, so every generated identity differs
 * numerically while provenance is unchanged */
static Graph *build_shifted(bool shift) {
    machine_init(); eval_init();
    RefId U0 = mk_universe(0), A = var(U0), B = var(U0);
    DimVarId i = declare_dim();
    if (shift) { for (uint64_t k = 0; k < 7; k++) { KeyWord kw[2] = { { KW_CONST, 777 }, { KW_CONST, k } }; fresh_dim_keyed(kw, 2); } }   /* unrelated generated names first */
    TermVarId xx = declare_term(A, fc_true());
    RefId S = mk_sigma_lv(0, 0, xx, A, B);
    RefId csg = mk_coe_at(0, i, S, var(S));
    WhnfStatus st;
    Canon *c = canon_new();
    canon_add_result(c, "csg", whnf(csg, fc_true(), &st));
    canon_add_result(c, "fst", whnf(mk_fst(csg), fc_true(), &st));
    canon_add_result(c, "snd", whnf(mk_snd(csg), fc_true(), &st));
    Graph *g = canon_export(c);
    canon_free(c); eval_free(); machine_free();
    return g;
}

int main(void) {
    printf("== §37 exact comparison modulo renaming\n");
    test_ambiguous();
    test_machine_graphs();
    {
        Graph *a = build_shifted(false), *b = build_shifted(true);
        MatchReport mr;
        CHECK(graph_match(a, b, &mr), "generated names with shifted numeric identities but equal provenance are accepted: %s", mr.reason);
        graph_free(a); graph_free(b);
    }
    printf("  %d passed, %d failed\n", np, nf);
    return nf ? 1 : 0;
}

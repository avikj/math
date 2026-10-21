/* test_code.c — the evaluator as a program of the language. `eval` below is
 * written in the language over codes; the machine runs it like any other
 * program, and its value at the code of a term is the code of the term the
 * machine's own weak-head evaluation reaches. */
#include "../src/read.h"
#include "../src/eval.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

/* the program text of prog/core.ctt */
static char *slurp(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) return NULL;
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = malloc((size_t)n + 1); if (!b) { fclose(f); return NULL; }
    size_t got = fread(b, 1, (size_t)n, f); b[got] = 0; fclose(f); return b;
}

/* the first place two term records differ (diagnostics) */
#include "../src/template.h"
static bool diff(RefId a, RefId b, const char *path) {
    static int quiet = -1; if (quiet < 0) quiet = !getenv("DIFF_VERBOSE");
    if (a == b) return true;
    if (ref_is_var(a) || ref_is_var(b)) { if (!quiet) printf("  differ at %s: variable\n", path); return false; }
    Tag ta = ref_tag(a), tb = ref_tag(b);
    uint64_t pa = family_call(F_HEAD, a, 0), pb = family_call(F_HEAD, b, 0);
    uint64_t la = family_call(F_HEAD, a, 1), lb = family_call(F_HEAD, b, 1);
    size_t na = tnode_nfields(ref_tnode(a)), nb = tnode_nfields(ref_tnode(b));
    if (ta != tb || pa != pb || la != lb || na != nb) {
        if (!quiet) printf("  differ at %s: %s/%s payload %llu/%llu levels %llu/%llu fields %zu/%zu\n", path, tag_name(ta), tag_name(tb),
               (unsigned long long)pa, (unsigned long long)pb, (unsigned long long)la, (unsigned long long)lb, na, nb);
        return false;
    }
    bool same = true;
    for (size_t q = 0; q < na; q++) {
        char sub[256]; snprintf(sub, sizeof sub, "%s.%s%zu", path, tag_name(ta), q);
        if (schema_kind(ta, q) != F_REF) {
            uint64_t fa = construction_field(a, q), fb = construction_field(b, q);
            if (fa != fb) { if (!quiet) printf("  differ at %s: interval/face field\n", sub); same = false; }
            continue;
        }
        if (schema_slot(ta, q) == NO_SLOT) { same = diff(construction_field(a, q), construction_field(b, q), sub) && same; continue; }
        Sort so = (Sort)tag_schema(ta)->bsort;
        if (so == S_DIM) { DimVarId j = declare_dim(); same = diff(apply_dim_binder(a, 0, q, iv_var(j)), apply_dim_binder(b, 0, q, iv_var(j)), sub) && same; }
        else { RefId dom = construction_field(a, 0); TermVarId x = declare_term(dom, fc_true()); same = diff(apply_term_binder(a, 0, q, ref_var(x)), apply_term_binder(b, 0, q, ref_var(x)), sub) && same; }
    }
    return same;
}

static RefId EV, INVALID;
static size_t n_structural;
/* the machine's whnf of t under χ, and the program eval at the codes of χ
 * and t: the same value (the code of the machine's record; invalid; or both
 * pending) */
static void agree(RefId t, FaceId chi, const char *label) {
    WhnfStatus s1, s2;
    EvalResult native = whnf(t, chi, &s1);
    RefId run = mk_app(mk_app(EV, MK(T_QFC, 0, LEVELS_NONE, 0, chi)), MK(T_QUOTE, 0, LEVELS_NONE, 0, t));
    EvalResult prog = whnf(run, fc_true(), &s2);
    RefId pv = s2 == W_OK && prog.cls == R_INTRODUCTION && ref_tag(prog.ref) == T_QUOTE ? construction_field(prog.ref, 0) : 0;
    bool exact = (s1 == W_INVALID && pv == INVALID) || (s1 == W_STUCK && s2 == W_STUCK) || (s1 == W_OK && pv && pv == native.ref);
    bool structural = !exact && s1 == W_OK && pv && pv != INVALID && diff(native.ref, pv, "");
    char m[200]; snprintf(m, sizeof m, "eval agrees with the machine: %s%s", label, structural ? " (up to required faces)" : "");
    CHECK(exact || structural, m);
    n_structural += structural;
    if (!exact && !structural) {
        printf("  native: status %d class %d ", (int)s1, (int)native.cls); if (native.ref) print_ref_depth(native.ref, stdout, 6);
        printf("\n  program: status %d class %d %s ", (int)s2, (int)prog.cls, prog.message ? prog.message : ""); if (pv) print_ref_depth(pv, stdout, 6);
        printf("\n");
    }
}

int main(void) {
    machine_init();
    Reader *r = reader_new();
    bool ok = reader_program(r,
        "(axiom A (U 0))\n"
        "(axiom a A) (axiom b A)\n"
        "(axiom q (Sigma (x A) A))\n"
        "(def K (Pi (x A) (Pi (y A) A)) (lam (x A) (lam (y A) x)))\n"
        "(def KP (Pi (x A) (Pi (y A) (Sigma (z A) A))) (lam (x A) (lam (y A) (pair y x))))\n"
        "(axiom p (Path (i) A a b))\n"
        "(def refl-a (Path (i) A a a) (plam (i) a))\n"
        "(def loop A loop)\n"
        "(axiom f (Pi (x A) A)) (axiom z (Sigma (x A) A))\n"
        "(axiom pa (Path 0 (i) A a a))\n"
        "(axiom B (U 0)) (axiom g (Pi (x A) B))\n");
    char *core = slurp("prog/core.ctt");
    CHECK(core != NULL, "prog/core.ctt is readable");
    ok = ok && core && reader_program(r, core);
    free(core);
    CHECK(ok, reader_error(r) ? reader_error(r) : "the evaluator program reads");
    if (!ok) return 1;

    static const char *T[] = {
        "a", "q", "K", "(K a b)", "((K a) b)", "(fst (pair a b))", "(snd (pair a b))",
        "((lam (x A) x) b)", "(fst (KP a b))", "(snd (KP a b))", "(fst q)", "(K (fst (KP b a)) a)",
        "(papp (i) A a b p 0)", "(papp (i) A a b p 1)", "(papp (i) A a a refl-a 0)",
        "((lam (x A) (papp (i) A a b p 1)) a)", "(plam (j) (papp (i) A a b p j))",
        "(fst ((lam (x (Sigma (z A) A)) x) (pair b a)))", "(Pi (x A) A)", "(U 0)",
        /* composition: each clause, and what its instance reduces to */
        "(comp 0 (i) (Pi 0 0 (x A) A) false (sys) f)",
        "((comp 0 (i) (Pi 0 0 (x A) A) false (sys) f) a)",
        "((comp 0 (i) (Pi 0 0 (x A) B) false (sys) g) a)",
        "(comp 0 (i) (Pi 0 0 (x A) A) true f f)",
        "(comp 0 (i) (Sigma 0 0 (x A) A) false (sys) z)",
        "(fst (comp 0 (i) (Sigma 0 0 (x A) A) false (sys) z))",
        "(snd (comp 0 (i) (Sigma 0 0 (x A) A) false (sys) z))",
        "(comp 0 (i) (Path 0 (j) A a a) false (sys) pa)",
        "(papp 0 (j) A a a (comp 0 (i) (Path 0 (j) A a a) false (sys) pa) 0)",
        "(papp 0 (j) A a a (comp 0 (i) (Path 0 (j) A a a) false (sys) pa) 1)",
        "(comp 1 (i) (U 0) false (sys) A)",
        "(comp 0 (i) A false (sys) a)",
        "(comp 0 (i) (sys (true (Pi 0 0 (x A) A))) false (sys) f)",
        "(unglue 0 A true A (pair (lam (x A) x) a) a)",
        "(Glue 0 A true B f)", "(Glue 0 A false B f)", "(glue 0 A true B f b a)",
    };
    EV = reader_term(r, "eval"); INVALID = reader_term(r, "invalid");
    RefId ev = EV, chi = reader_term(r, "(qfc true)");
    for (size_t n = 0; n < sizeof T / sizeof T[0]; n++) agree(reader_term(r, T[n]), fc_true(), T[n]);

    {   /* under faces: systems, distribution, family systems, Glue (from the machine's own tests) */
        RefId A = reader_term(r, "A"), B = reader_term(r, "B"), a = reader_term(r, "a"), b = reader_term(r, "b");
        RefId f = reader_term(r, "f");
        DimVarId i = declare_dim(), j = declare_dim(), m = declare_dim(), n = declare_dim();
        FaceId i1 = fc_lit(i, 1), j0 = fc_lit(j, 0), j1 = fc_lit(j, 1);
        RefId G = mk_glue_type_lv(0, A, i1, B, f);
        agree(G, fc_true(), "Glue off its face");
        agree(G, i1, "Glue on its face");
        RefId gl = mk_glue_intro_lv(0, A, i1, B, f, b, a);
        agree(gl, i1, "glue on its face");
        agree(mk_unglue_lv(0, A, i1, B, f, gl), fc_true(), "unglue of glue");
        FaceId fs[2] = { j0, j1 }; RefId ts[2] = { a, b };
        RefId sys = mk_system(2, fs, ts);
        agree(sys, j0, "a system selects its covering branch");
        agree(sys, fc_join(j0, j1), "a covered, unselected system");
        agree(sys, fc_true(), "a system outside its required face");
        RefId ts2[2] = { reader_term(r, "(lam (x A) a)"), f };
        agree(mk_app(mk_system(2, fs, ts2), b), fc_join(j0, j1), "application distributes over a system");
        agree(mk_fst(mk_system(2, fs, (RefId[]){ reader_term(r, "(pair a b)"), reader_term(r, "q") })), fc_join(j0, j1), "projection distributes");
        RefId X = reader_term(r, "B");
        agree(mk_comp_lv(0, m, X, fc_false(), mk_system(0, NULL, NULL), a), fc_true(), "composition in a neutral family");
        FaceId gs[2] = { fc_lit(m, 0), fc_lit(m, 1) }; RefId Ys[2] = { X, A };
        agree(mk_comp_lv(0, m, mk_system(2, gs, Ys), fc_false(), mk_system(0, NULL, NULL), a), fc_true(), "endpoint-only family branches do not cover the line");
        FaceId gs2[2] = { fc_lit(n, 0), fc_lit(n, 1) }; RefId Ys2[2] = { X, reader_term(r, "(Pi 0 0 (x A) A)") };
        RefId cmp4 = mk_comp_lv(0, m, mk_system(2, gs2, Ys2), fc_false(), mk_system(0, NULL, NULL), a);
        agree(cmp4, fc_join(gs2[0], gs2[1]), "a system of compositions under ∀m guards");
        agree(cmp4, gs2[1], "the Π branch selected");
        RefId Gm = mk_glue_type_lv(0, A, fc_lit(m, 1), B, f);
        RefId cg = mk_comp_lv(0, i, Gm, fc_false(), mk_system(0, NULL, NULL), reader_term(r, "a"));
        agree(cg, fc_true(), "composition in Glue off its face");
        agree(cg, fc_lit(m, 1), "composition in Glue on its face");
        agree(mk_unglue_lv(0, A, fc_lit(m, 1), B, f, cg), fc_true(), "unglue of a composition in Glue");
        RefId pth = reader_term(r, "p");
        RefId pl = mk_plam(j, mk_papp(i, A, a, b, pth, iv_negate(iv_var(j))));
        agree(mk_papp(i, A, b, a, pl, iv_var(n)), fc_lit(n, 0), "a path at a face endpoint");
        agree(mk_papp(i, A, b, a, pl, iv_var(n)), fc_true(), "a path in its interior");
    }
    {   /* transport along ua(idEquiv A): the Glue clause */
        WhnfStatus st;
        EvalResult u = whnf(reader_term(r, "(ua (qlv 0) (quote A) (quote A) (id-equiv (qlv 0) (quote A)))"), fc_true(), &st);
        CHECK(st == W_OK && ref_tag(u.ref) == T_QUOTE, "ua builds a path of types");
        RefId P = construction_field(u.ref, 0), A = reader_term(r, "A");
        DimVarId i = declare_dim(), kk = declare_dim();
        RefId fam = MK(T_PAPP, 0, levels_pack(1, LEVEL_NONE), kk, reader_term(r, "(U 0)"), A, A, P, iv_var(i));
        RefId tr = MK(T_COMP, 0, levels_pack(0, LEVEL_NONE), i, fam, fc_false(), mk_system(0, NULL, NULL), reader_term(r, "a"));
        WhnfStatus s1, s2;
        EvalResult native = whnf(tr, fc_true(), &s1);
        EvalResult prog = whnf(mk_app(mk_app(ev, chi), MK(T_QUOTE, 0, LEVELS_NONE, 0, tr)), fc_true(), &s2);
        bool ok2 = s1 == W_OK && s2 == W_OK && ref_tag(prog.ref) == T_QUOTE; (void)ev;
        if (!ok2) printf("  native %d program %d %s\n", (int)s1, (int)s2, prog.message ? prog.message : "");
        CHECK(ok2 && diff(native.ref, construction_field(prog.ref, 0), ""), "transport along ua: the program's Glue clause has the machine's structure");
    }
    {   /* ceq: one record or not */
        WhnfStatus st;
        CHECK(whnf(reader_term(r, "(ceq (quote (lam (x A) x)) (quote (lam (y A) y)) a b)"), fc_true(), &st).ref == reader_term(r, "a"), "ceq: alpha-equal codes are one record");
        CHECK(whnf(reader_term(r, "(ceq (quote a) (quote b) a b)"), fc_true(), &st).ref == reader_term(r, "b"), "ceq: distinct codes");
    }
    {   /* a computation that does not end is pending under both, not an error */
        WhnfStatus s1, s2;
        (void)whnf(reader_term(r, "loop"), fc_true(), &s1);
        (void)whnf(mk_app(mk_app(ev, chi), MK(T_QUOTE, 0, LEVELS_NONE, 0, reader_term(r, "loop"))), fc_true(), &s2);
        CHECK(s1 == W_STUCK && s2 == W_STUCK, "the program and the machine are both pending on a definition that demands itself");
    }
    reader_free(r);
    machine_free();
    printf("%zu agreements up to required faces\n%d failures\n", n_structural, failures);
    return failures != 0;
}

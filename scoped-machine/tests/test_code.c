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

static RefId EV, INVALID;
/* the program's value of t under χ (the record its code holds; 0 when the
 * evaluation did not complete) */
static RefId val(RefId t, FaceId chi) {
    WhnfStatus st;
    EvalResult e = whnf(mk_app(mk_app(EV, MK(T_QFC, 0, LEVELS_NONE, 0, chi)), MK(T_QUOTE, 0, LEVELS_NONE, 0, t)), fc_true(), &st);
    return st == W_OK && e.cls == R_INTRODUCTION && ref_tag(e.ref) == T_QUOTE ? construction_field(e.ref, 0) : 0;
}
static Tag tag_of(RefId t) { return t && !ref_is_var(t) ? ref_tag(t) : 0; }
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
    char m[200]; snprintf(m, sizeof m, "eval agrees with the machine: %s", label);
    CHECK(exact, m);
    if (!exact) {
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
        "(fst ((lam (x (Sigma (z A) A)) x) (pair b a)))", "(Pi (x A) A)", "(U 0)",
        "(plam (j) (papp (i) A a b p j))",
    };
    EV = reader_term(r, "eval"); INVALID = reader_term(r, "invalid");
    RefId ev = EV, chi = reader_term(r, "(qfc true)");
    for (size_t n = 0; n < sizeof T / sizeof T[0]; n++) agree(reader_term(r, T[n]), fc_true(), T[n]);

    /* the cubical computation is the program's alone: its values */
    {
        RefId A = reader_term(r, "A"), B = reader_term(r, "B"), a = reader_term(r, "a"), b = reader_term(r, "b");
        RefId f = reader_term(r, "f"), p = reader_term(r, "p");
#define V(src) val(reader_term(r, src), fc_true())
        CHECK(V("(papp (i) A a b p 0)") == a && V("(papp (i) A a b p 1)") == b, "a path at an endpoint is that endpoint");
        CHECK(V("(papp (i) A a a refl-a 0)") == a && V("((lam (x A) (papp (i) A a b p 1)) a)") == b, "through a definition and a β step");
        RefId c = V("(comp 0 (i) (Pi 0 0 (x A) A) false (sys) f)");
        CHECK(tag_of(c) == T_LAM, "transport in a Π family is a λ");
        RefId ca = V("((comp 0 (i) (Pi 0 0 (x A) B) false (sys) g) a)");
        CHECK(tag_of(ca) == T_COMP && tag_of(construction_field(ca, 3)) == T_APP, "applied, it is a composition in the codomain whose base applies the function");
        CHECK(V("(comp 0 (i) (Pi 0 0 (x A) A) true f f)") == f, "a covering tube is the value");
        RefId cs = V("(comp 0 (i) (Sigma 0 0 (x A) A) false (sys) z)");
        CHECK(tag_of(cs) == T_PAIR && tag_of(V("(fst (comp 0 (i) (Sigma 0 0 (x A) A) false (sys) z))")) == T_COMP, "transport in a Σ family is a pair of compositions");
        CHECK(tag_of(V("(comp 0 (i) (Path 0 (j) A a a) false (sys) pa)")) == T_PLAM, "transport in a Path family is a path abstraction");
        CHECK(V("(papp 0 (j) A a a (comp 0 (i) (Path 0 (j) A a a) false (sys) pa) 0)") == a, "whose endpoints are the endpoints");
        RefId cu = V("(comp 1 (i) (U 0) false (sys) A)");
        CHECK(tag_of(cu) == T_GLUE_TYPE && construction_field(cu, 0) == A && fc_is_false(construction_field(cu, 1)), "transport in the universe is a Glue type over the base");
        CHECK(tag_of(V("(comp 0 (i) (sys (true (Pi 0 0 (x A) A))) false (sys) f)")) == T_LAM, "a family system's covering branch");
        CHECK(V("(unglue 0 A true A (pair (lam (x A) x) a) a)") == a, "unglue on its face applies the equivalence");
        CHECK(V("(Glue 0 A true B f)") == B && V("(glue 0 A true B f b a)") == b, "Glue and glue on their face");
        RefId cn = reader_term(r, "(comp 0 (i) B false (sys) a)");
        CHECK(val(cn, fc_true()) == cn, "a composition in a neutral family is neutral");

        DimVarId i = declare_dim(), j = declare_dim(), m = declare_dim(), n = declare_dim();
        FaceId i1 = fc_lit(i, 1), j0 = fc_lit(j, 0), j1 = fc_lit(j, 1);
        RefId G = mk_glue_type_lv(0, A, i1, B, f);
        CHECK(val(G, fc_true()) == G && val(G, i1) == B, "Glue off and on its face");
        RefId gl = mk_glue_intro_lv(0, A, i1, B, f, b, a);
        CHECK(val(gl, i1) == b && val(mk_unglue_lv(0, A, i1, B, f, gl), fc_true()) == a, "glue on its face; unglue of glue");
        FaceId fs[2] = { j0, j1 }; RefId ts[2] = { a, b };
        RefId sys = mk_system(2, fs, ts);
        CHECK(val(sys, j0) == a, "a system selects its covering branch");
        CHECK(val(sys, fc_join(j0, j1)) == sys, "a covered, unselected system is a system value");
        CHECK(val(sys, fc_true()) == INVALID, "a system outside the face it covers is invalid");
        RefId ts2[2] = { reader_term(r, "(lam (x A) a)"), f };
        RefId d = val(mk_app(mk_system(2, fs, ts2), b), fc_join(j0, j1));
        CHECK(tag_of(d) == T_SYSTEM && construction_field(d, 0) == j0 && construction_field(d, 1) == a
              && construction_field(d, 2) == j1 && construction_field(d, 3) == mk_app(f, b), "application distributes over a system, each branch evaluated under its guard");
        RefId X = B;
        FaceId gs[2] = { fc_lit(m, 0), fc_lit(m, 1) }; RefId Ys[2] = { X, A };
        CHECK(val(mk_comp_lv(0, m, mk_system(2, gs, Ys), fc_false(), mk_system(0, NULL, NULL), a), fc_true()) == INVALID,
              "endpoint-only family branches do not cover the line");
        FaceId gs2[2] = { fc_lit(n, 0), fc_lit(n, 1) }; RefId Ys2[2] = { X, reader_term(r, "(Pi 0 0 (x A) A)") };
        RefId cmp4 = mk_comp_lv(0, m, mk_system(2, gs2, Ys2), fc_false(), mk_system(0, NULL, NULL), f);
        RefId s4 = val(cmp4, fc_join(gs2[0], gs2[1]));
        CHECK(tag_of(s4) == T_SYSTEM && construction_field(s4, 0) == gs2[0] && construction_field(s4, 2) == gs2[1] && tag_of(construction_field(s4, 3)) == T_LAM,
              "a family system: one composition per branch, guarded along the whole line");
        CHECK(tag_of(val(cmp4, gs2[1])) == T_LAM, "under (n=1) the Π branch is selected");
        RefId Gm = mk_glue_type_lv(0, A, fc_lit(m, 1), B, f);
        RefId cg = mk_comp_lv(0, i, Gm, fc_false(), mk_system(0, NULL, NULL), a);
        CHECK(tag_of(val(cg, fc_true())) == T_GLUE_INTRO, "transport in Glue off its face is a glue");
        CHECK(tag_of(val(mk_unglue_lv(0, A, fc_lit(m, 1), B, f, cg), fc_true())) == T_COMP, "whose base is the repaired composition");
        RefId pl = mk_plam(j, mk_papp(i, A, a, b, p, iv_negate(iv_var(j))));
        CHECK(val(mk_papp(i, A, b, a, pl, iv_var(n)), fc_lit(n, 0)) == b, "a path at a face endpoint");
        RefId in = val(mk_papp(i, A, b, a, pl, iv_var(n)), fc_true());
        CHECK(tag_of(in) == T_PAPP && construction_field(in, 3) == p && construction_field(in, 4) == iv_negate(iv_var(n)), "in its interior, β to p(¬n)");

        /* transport along ua(idEquiv A) */
        WhnfStatus ust;
        RefId P = whnf(reader_term(r, "(ua (qlv 0) (quote A) (quote A) (id-equiv (qlv 0) (quote A)))"), fc_true(), &ust).ref;
        CHECK(tag_of(P) == T_QUOTE, "ua builds the code of a path of types");
        DimVarId kk = declare_dim();
        RefId fam = MK(T_PAPP, 0, levels_pack(1, LEVEL_NONE), kk, reader_term(r, "(U 0)"), A, A, construction_field(P, 0), iv_var(i));
        RefId tr = MK(T_COMP, 0, levels_pack(0, LEVEL_NONE), i, fam, fc_false(), mk_system(0, NULL, NULL), a);
        RefId tv = val(tr, fc_true());
        CHECK(tv && tv != INVALID && tag_of(tv) == T_COMP && tv != tr, "transport along ua evaluates through the Glue clause to a composition in A (neutral)");
        if (tv && tv != INVALID) { printf("  transport along ua(idEquiv A) of a: "); print_ref_depth(tv, stdout, 3); printf("\n"); }
#undef V
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
    printf("%d failures\n", failures);
    return failures != 0;
}

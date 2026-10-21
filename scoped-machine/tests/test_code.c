/* test_code.c — the evaluator as a program of the language. `eval` below is
 * written in the language over codes; the machine runs it like any other
 * program, and its value at the code of a term is the code of the term the
 * machine's own weak-head evaluation reaches. */
#include "../src/read.h"
#include "../src/eval.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static const char *EVAL =
    "(def eval (Pi (chi (Code)) (Pi (c (Code)) (Code)))\n"
    "  (lam (chi (Code)) (lam (c (Code))\n"
    "    (cmatch app c\n"
    "      (lam (f (Code)) (lam (a (Code))\n"
    "        (cmatch lam (eval chi f)\n"
    "          (lam (A (Code)) (lam (b (Pi (x (Code)) (Code))) (eval chi (b a))))\n"
    "          c)))\n"
    "    (cmatch fst c\n"
    "      (lam (p (Code)) (cmatch pair (eval chi p) (lam (x (Code)) (lam (y (Code)) (eval chi x))) c))\n"
    "    (cmatch snd c\n"
    "      (lam (p (Code)) (cmatch pair (eval chi p) (lam (x (Code)) (lam (y (Code)) (eval chi y))) c))\n"
    "    (cmatch papp c\n"
    "      (lam (A (Pi (i (Code)) (Code))) (lam (a (Code)) (lam (b (Code)) (lam (p (Code)) (lam (r (Code))\n"
    "        (cent chi (cfcend 0 r) (eval chi a)\n"
    "        (cent chi (cfcend 1 r) (eval chi b)\n"
    "          (cmatch plam (eval chi p) (lam (t (Pi (i (Code)) (Code))) (eval chi (t r))) c))))))))\n"
    "    (cmatch global c\n"
    "      (cunfold c (lam (u (Code)) (eval chi u)) c)\n"
    "      c))))))))\n";

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
        "(def loop A loop)\n");
    ok = ok && reader_program(r, EVAL);
    CHECK(ok, reader_error(r) ? reader_error(r) : "the evaluator program reads");
    if (!ok) return 1;

    static const char *T[] = {
        "a", "q", "K", "(K a b)", "((K a) b)", "(fst (pair a b))", "(snd (pair a b))",
        "((lam (x A) x) b)", "(fst (KP a b))", "(snd (KP a b))", "(fst q)", "(K (fst (KP b a)) a)",
        "(papp (i) A a b p 0)", "(papp (i) A a b p 1)", "(papp (i) A a a refl-a 0)",
        "((lam (x A) (papp (i) A a b p 1)) a)", "(plam (j) (papp (i) A a b p j))",
        "(fst ((lam (x (Sigma (z A) A)) x) (pair b a)))", "(Pi (x A) A)", "(U 0)",
    };
    RefId ev = reader_term(r, "eval"), chi = reader_term(r, "(qfc true)");
    for (size_t n = 0; n < sizeof T / sizeof T[0]; n++) {
        RefId t = reader_term(r, T[n]);
        WhnfStatus s1, s2;
        EvalResult native = whnf(t, fc_true(), &s1);
        RefId run = mk_app(mk_app(ev, chi), MK(T_QUOTE, 0, LEVELS_NONE, 0, t));
        EvalResult prog = whnf(run, fc_true(), &s2);
        bool same = s1 == W_OK && s2 == W_OK && prog.cls == R_INTRODUCTION && ref_tag(prog.ref) == T_QUOTE
                 && construction_field(prog.ref, 0) == native.ref;
        char m[160]; snprintf(m, sizeof m, "eval program agrees with the machine on %s", T[n]);
        CHECK(same, m);
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

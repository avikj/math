/* test_read.c — programs read from text run on the machine: the records the
 * reader builds are the records the machine evaluates. */
#include "../src/read.h"
#include "../src/eval.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static RefId whnf_ref(RefId t, FaceId chi, WhnfStatus *st) { EvalResult r = whnf(t, chi, st); return r.ref; }

int main(void) {
    machine_init();
    Reader *r = reader_new();
    bool ok = reader_program(r,
        "(axiom A (U 0))\n"
        "(axiom a A) (axiom b A)\n"
        "(def K (Pi (x A) (Pi (y A) A)) (lam (x A) (lam (y A) x)))\n"
        "(axiom p (Path (i) A a b))\n"
        "(def loop A loop)\n");
    CHECK(ok, reader_error(r) ? reader_error(r) : "the program reads");
    RefId a = reader_global(r, "a"), b = reader_global(r, "b");
    WhnfStatus st;
    CHECK(whnf_ref(reader_term(r, "(K a b)"), fc_true(), &st) == a && st == W_OK, "(K a b) evaluates to a");
    CHECK(whnf_ref(reader_term(r, "(fst (pair a b))"), fc_true(), &st) == a, "fst of a pair");
    CHECK(whnf_ref(reader_term(r, "((lam (x A) x) b)"), fc_true(), &st) == b, "beta");
    CHECK(ref_tag(reader_term(r, "(papp (i) A a b p 0)")) == T_PAPP && construction_field(reader_term(r, "(papp (i) A a b p 0)"), 3) == reader_global(r, "p"), "a path application reads to its record");
    CHECK(ref_tag(reader_term(r, "(sys (true a))")) == T_SYSTEM && construction_field(reader_term(r, "(sys (true a))"), 1) == a, "a system reads to its record");
    CHECK(reader_term(r, "(lam (x A) x)") == reader_term(r, "(lam (y A) y)"), "alpha-equivalent text reads to one record");
    (void)whnf(reader_term(r, "loop"), fc_true(), &st);
    CHECK(st == W_STUCK, "a definition that demands itself is pending");
    CHECK(reader_term(r, "(lam (x A) zz)") == 0 && reader_error(r), "an unbound name is a read error");
    reader_free(r);
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

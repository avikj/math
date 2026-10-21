/* test_check.c — the type checker as a program of the language
 * (prog/check.ctt): judgements on terms, on the library's own constructions,
 * and rejections. */
#include "../src/read.h"
#include "../src/eval.h"

static int failures;
#define CHECK(c, m) do { if (!(c)) { failures++; printf("FAIL: %s\n", m); } else printf("ok: %s\n", m); } while (0)

static char *slurp(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) return NULL;
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = malloc((size_t)n + 1); if (!b) { fclose(f); return NULL; }
    size_t got = fread(b, 1, (size_t)n, f); b[got] = 0; fclose(f); return b;
}
static Reader *R;
static RefId OK;
/* the checker's verdict on a judgement written in the language */
static RefId run(const char *src) {
    RefId t = reader_term(R, src);
    if (!t) { printf("  read error: %s\n", reader_error(R)); return 0; }
    WhnfStatus st; EvalResult e = whnf(t, fc_true(), &st);
    return st == W_OK && e.cls == R_INTRODUCTION && ref_tag(e.ref) == T_QUOTE ? construction_field(e.ref, 0) : 0;
}
static void accept(const char *judgement) { char m[300]; snprintf(m, sizeof m, "accepts %s", judgement); CHECK(run(judgement) == OK, m); }
static void reject(const char *judgement) { char m[300]; snprintf(m, sizeof m, "rejects %s", judgement); RefId v = run(judgement); CHECK(v && v != OK, m); }

int main(void) {
    machine_init();
    R = reader_new();
    bool ok = reader_program(R,
        "(axiom A (U 0)) (axiom B (U 0))\n"
        "(axiom a A) (axiom a2 A) (axiom b B)\n"
        "(axiom f (Pi (x A) A))\n"
        "(def K (Pi (x A) (Pi (y A) A)) (lam (x A) (lam (y A) x)))\n"
        "(axiom p (Path (i) A a a2))\n");
    char *core = slurp("prog/core.ctt"), *chk = slurp("prog/check.ctt");
    ok = ok && core && chk && reader_program(R, core) && reader_program(R, chk);
    CHECK(ok, reader_error(R) ? reader_error(R) : "the checker program reads");
    if (!ok) return 1;
    OK = reader_global(R, "ok");
    RefId A = reader_global(R, "A");
    CHECK(run("(infer (qfc true) (quote (K a a2)))") == A, "infers (K a a2) : A");
    CHECK(run("(infer (qfc true) (quote (fst (pair a b))))") == A, "infers fst of a pair");
    accept("(check (qfc true) (quote (lam (x A) x)) (quote (Pi (x A) A)))");
    accept("(check (qfc true) (quote (pair a b)) (quote (Sigma (x A) B)))");
    accept("(check (qfc true) (quote (plam (i) a)) (quote (Path (i) A a a)))");
    accept("(check (qfc true) (quote (papp (i) A a a2 p 0)) (quote A))");
    accept("(check (qfc true) (quote (Pi (x A) A)) (quote (U 0)))");
    accept("(check (qfc true) (quote (U 0)) (quote (U 1)))");
    accept("(check (qfc true) (quote A) (quote (U 3)))");
    accept("(check (qfc true) (quote (comp 0 (i) A false (sys) a)) (quote A))");
    accept("(check (qfc true) (quote (comp 0 (i) A true (papp (k) A a a2 p i) a)) (quote A))");
    accept("(check (qfc true) (quote (lam (x A) (f (f x)))) (quote (Pi (y A) A)))");
    /* the library's constructions, checked by the checker */
    accept("(check (qfc true) (id-equiv (qlv 0) (quote A)) (equiv (qlv 0) (qlv 0) (quote A) (quote A)))");
    accept("(check (qfc true) (ua (qlv 0) (quote A) (quote A) (id-equiv (qlv 0) (quote A))) (path-const (qlv 1) (quote (U 0)) (quote A) (quote A)))");
    accept("(check (qfc true) (line-equiv (qlv 0) (fn (i) (quote A))) (equiv (qlv 0) (qlv 0) (quote A) (quote A)))");
    accept("(check (qfc true) (fill (qlv 0) (fn (i) (quote A)) (qfc false) (fn (i) (quote (sys))) (quote a) (qiv 1)) (quote A))");
    /* the evaluator's composition reducts have the composition's type */
    accept("(check (qfc true) (eval (qfc true) (quote (comp 0 (i) (Pi 0 0 (x A) A) false (sys) f))) (quote (Pi (x A) A)))");
    accept("(check (qfc true) (eval (qfc true) (quote (comp 0 (i) (Sigma 0 0 (x A) B) false (sys) (pair a b)))) (quote (Sigma (x A) B)))");
    accept("(check (qfc true) (eval (qfc true) (quote (comp 0 (i) (Path 0 (j) A a a2) false (sys) p))) (quote (Path (j) A a a2)))");
    accept("(check (qfc true) (eval (qfc true) (quote (comp 1 (i) (U 0) false (sys) A))) (quote (U 0)))");
    accept("(check (qfc true) (eval (qfc true) (mk-comp (qlv 0) (fn (i) (mk-papp (qlv 1) (fn (k) (quote (U 0))) (quote A) (quote A) (ua (qlv 0) (quote A) (quote A) (id-equiv (qlv 0) (quote A))) i)) (qfc false) (fn (i) (quote (sys))) (quote a))) (quote A))");
    /* rejections */
    reject("(check (qfc true) (quote (f b)) (quote A))");
    reject("(check (qfc true) (quote (plam (i) a)) (quote (Path (i) A a a2)))");
    reject("(check (qfc true) (quote (pair a b)) (quote (Pi (x A) A)))");
    reject("(check (qfc true) (quote (U 1)) (quote (U 1)))");
    reject("(check (qfc true) (quote (comp 0 (i) A true (papp (k) A a a2 p i) a2)) (quote A))");
    /* the programs themselves: every definition of the evaluator, the
     * library and the checker has its declared type, by the checker */
    {   const char *files[2] = { core, chk }; size_t n = 0, good = 0;
        for (int f = 0; f < 2; f++)
            for (const char *q = files[f]; (q = strstr(q, "(defn ")); q += 6) {
                char name[64]; size_t len = strcspn(q + 6, " \n()"); if (len >= sizeof name) continue;
                memcpy(name, q + 6, len); name[len] = 0;
                char j[256]; snprintf(j, sizeof j, "(check (qfc true) (cunfold (quote %s) (fn (b) b) (quote invalid)) (ctype (quote %s)))", name, name);
                n++;
                if (run(j) == OK) good++; else printf("  not checked: %s\n", name);
            }
        char m[120]; snprintf(m, sizeof m, "the checker checks %zu/%zu program definitions (evaluator, library, checker)", good, n);
        CHECK(good == n && n > 0, m);
    }
    free(core); free(chk);
    reader_free(R);
    machine_free();
    printf("%d failures\n", failures);
    return failures != 0;
}

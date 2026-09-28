/* hyper — main.c: run | bend | check | interact.
 *
 * The machine is Fibre.CorpusInteraction (fibre/src/Fibre/CorpusInteraction.agda): a state is a typed point
 * (A, a) : Σ A. A; a question is a typed map (B, f) out of the current type; the answer is the point (B, f a);
 * the receipt is the path target s q ≡ s', refl at the canonical step; the process continues at the new point
 * (ISC, react).  `run` is the trivial-query case.  `interact` reads questions from the world, one per line.
 * Every run reports its charge (research/sat_fibre/InteractionLedger.agda: interactions and heap words).  The
 * census of a question, the joint state and the encounter of two peers are programs (t/census.hyper,
 * t/jiva.hyper, t/meet.hyper), written with declared fibres, `trace` and `leaves`; the runtime has one entry. */
#include "cell.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/resource.h>
void read_file(const char *path);
int read_question(const char *text);
int check_book(const char *prefix);
Term app2(Term f, Term a);
Term node2(unsigned t, uint32_t e, Term a, Term b);

/* §5: the machine that asks. The root is the typed point; each line of the world is a question q, a
   term; the point presents itself along q: root := (q a, (a, refl)). A reduction that stalls at an
   ASK cell prints the question and waits for the world's section; the continuation resumes on it. */
static char *read_line(FILE *in) {
  static char buf[1 << 16]; if (!fgets(buf, sizeof buf, in)) return 0;
  size_t n = strlen(buf); while (n && (buf[n-1] == '\n' || buf[n-1] == '\r')) buf[--n] = 0;
  return buf;
}
static Term answer_asks(Term v, bool bend) {
  for (;;) {
    v = whnf(v);
    if (tag(v) != T_ASK) return v;
    printf("? "); if (bend) print_bend(HEAP[loc(v)], 64); else print_term(HEAP[loc(v)], 64); printf("\n"); fflush(stdout);
    char *line = read_line(stdin); if (!line) { fprintf(stderr, "hyper: the world went silent at a question\n"); exit(1); }
    int q = read_question(line);
    v = app2(HEAP[loc(v)+1], mk(T_REF, 0, (uint32_t)q));
  }
}
static int interact(const char *entry, bool bend) {
  int id = book_find(entry); if (id < 0) { fprintf(stderr, "hyper: no %s\n", entry); return 1; }
  uint64_t before = ITRS;
  Term root = answer_asks(mk(T_REF, 0, (uint32_t)id), bend);
  if (bend) collapse_print(root); else { print_term(root, 64); printf("\n"); }
  printf("- Itrs: %llu\n", (unsigned long long)(ITRS - before)); fflush(stdout);
  for (char *line; (line = read_line(stdin)); ) {
    if (!*line || *line == ';') continue;
    int q = read_question(line); before = ITRS;
    Term qa = answer_asks(app2(mk(T_REF, 0, (uint32_t)q), root), bend);
    if (bend) collapse_print(qa); else { print_term(qa, 64); printf("\n"); }
    printf("- Itrs: %llu\n", (unsigned long long)(ITRS - before)); fflush(stdout);
    root = node2(T_CTR, ctr_ext(C_PAIR, 2), qa, node2(T_CTR, ctr_ext(C_PAIR, 2), root, mk(T_CTR, ctr_ext(C_REFL, 0), 1)));   /* present: (q a, (a, refl)) */
  }
  return 0;
}
static void load_next_to_exe(const char *exe, const char *name) {
  char pre[4096]; const char *slash = strrchr(exe, '/');
  snprintf(pre, sizeof pre, "%.*s%s%s", slash ? (int)(slash - exe) : 1, slash ? exe : ".", "/", name);
  read_file(pre);
}
int main(int argc, char **argv) {
  { struct rlimit rl; if (!getrlimit(RLIMIT_STACK, &rl)) { rl.rlim_cur = rl.rlim_max == RLIM_INFINITY ? (rlim_t)4 << 30 : rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }   /* deep terms recurse deep */
  sched_init();
  if (argc < 3) { fprintf(stderr, "usage: hyper run FILE [DEF] | hyper bend FILE | hyper check FILE | hyper interact FILE [DEF]\n"); return 1; }
  bool bend = !strcmp(argv[1], "bend") || !strcmp(argv[1], "check");
  bool inter = !strcmp(argv[1], "interact");
  if (inter) bend = true;                                /* the dialect's rows are loaded; presentation follows the entry's namespace */
  load_next_to_exe(argv[0], "prelude.hyper");            /* the Kan rule rows, next to the executable */
  if (bend) load_next_to_exe(argv[0], "bend.hyper");     /* the Bend2 dialect's rows */
  read_file(argv[2]);
  load_prelude();
  if (!strcmp(argv[1], "check")) return check_book("b/") ? 1 : 0;
  if (inter) { const char *e = argc > 3 ? argv[3] : (book_find("b/main") >= 0 ? "b/main" : "main"); return interact(e, !strncmp(e, "b/", 2)); }
  const char *entry = argc > 3 ? argv[3] : (bend ? "b/main" : "main");
  int id = book_find(entry); if (id < 0) { fprintf(stderr, "hyper: no %s\n", entry); return 1; }
  Term r = run_def((uint32_t)id);
  if (bend) { collapse_print(r); fprintf(stderr, "- Itrs: %llu\n- Words: %u\n- Rounds: %llu\n", (unsigned long long)ITRS, (unsigned)HEAP_LEN, (unsigned long long)ROUNDS); if (getenv("HYPER_CENSUS")) print_census(); return 0; }
  print_term(r, 64); printf("\n");
  printf("- Itrs: %llu\n- Words: %u\n", (unsigned long long)ITRS, (unsigned)HEAP_LEN); if (getenv("HYPER_CENSUS")) printf("- Rounds: %llu\n", (unsigned long long)ROUNDS);
  if (getenv("HYPER_CENSUS")) print_census();
  if (getenv("HYPER_TRACE")) { printf("- Trace: "); print_trace(0); }
  return 0;
}

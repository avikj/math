/* hyper.c: Hyperactive.
 *
 * The element is the identification; the operation is folding: what is identified is one cell.
 * A cell is its construction (a name and its parts, the parts read through the folds); building a construction
 * that exists gives that cell.  Identities are equations between constructions, read from a file; a cell is
 * folded into what its equations make it.  The core knows no domain.  The one place a value is read is the meet
 * of two input elements, min(a, b): the input gives its order, and that fold is a new relation.
 *
 * usage: hyper EQUATIONS ELEMENTS
 *   EQUATIONS: lhs = rhs;  names starting upper-case are variables; // comments
 *   ELEMENTS:  the elements, whitespace separated; they are the finite set `input`, built as one(e) and
 *              union(A, B) of halves; the term evaluated is present(input). */
#include <ctype.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXARG 4
static char **SYM; static uint32_t NSYM;
static uint32_t sym(const char *s) {
  for (uint32_t i = 0; i < NSYM; i++) if (!strcmp(SYM[i], s)) return i;
  SYM = realloc(SYM, (NSYM + 1) * sizeof *SYM); SYM[NSYM] = strdup(s); return NSYM++;
}

/* ---- the store ---------------------------------------------------------------------------------------- */
typedef struct { uint32_t sym, n, arg[MAXARG], parent; long long val; uint8_t done; } Cell;
static Cell *C; static uint32_t NC, CCAP;
static uint64_t FOLDS, STEPS, NEW_RELATIONS;
static uint32_t S_MIN, S_ELEM;

static uint32_t find(uint32_t c) { while (C[c].parent != c) { C[c].parent = C[C[c].parent].parent; c = C[c].parent; } return c; }
static void fold(uint32_t c, uint32_t into) { c = find(c); into = find(into); if (c != into) { C[c].parent = into; FOLDS++; } }

static uint32_t *TAB, TCAP, TUSED;
static uint64_t hkey(uint32_t s, uint32_t n, const uint32_t *a) {
  uint64_t h = (s + 1) * 0x9E3779B97F4A7C15ull;
  for (uint32_t i = 0; i < n; i++) h = (h ^ (a[i] + 1)) * 0xC2B2AE3D27D4EB4Full;
  return h ^ (h >> 31);
}
static void tab_grow(void) {
  uint32_t old = TCAP, *ot = TAB; TCAP = TCAP ? TCAP * 2 : 1 << 16; TAB = calloc(TCAP, 4);
  for (uint32_t i = 0; i < old; i++) if (ot[i]) {
    Cell *x = &C[ot[i] - 1]; uint32_t a[MAXARG]; for (uint32_t k = 0; k < x->n; k++) a[k] = find(x->arg[k]);
    uint64_t h = hkey(x->sym, x->n, a) & (TCAP - 1); while (TAB[h]) h = (h + 1) & (TCAP - 1); TAB[h] = ot[i];
  }
  free(ot);
}
static uint32_t new_cell(uint32_t s, uint32_t n, const uint32_t *a, long long v) {
  if (NC == CCAP) { CCAP = CCAP ? CCAP * 2 : 1 << 16; C = realloc(C, CCAP * sizeof *C); if (!C) { fprintf(stderr, "hyper: out of memory\n"); exit(2); } }
  Cell *x = &C[NC]; x->sym = s; x->n = n; for (uint32_t i = 0; i < n; i++) x->arg[i] = a[i];
  x->parent = NC; x->val = v; x->done = 0; return NC++;
}
static uint32_t construct(uint32_t s, uint32_t n, const uint32_t *args) {
  uint32_t a[MAXARG]; for (uint32_t i = 0; i < n; i++) a[i] = find(args[i]);
  if (s == S_MIN && n == 2 && a[0] > a[1]) { uint32_t t = a[0]; a[0] = a[1]; a[1] = t; }   /* the meet: one construction either way */
  if (2 * (TUSED + 1) >= TCAP) tab_grow();
  uint64_t h = hkey(s, n, a) & (TCAP - 1);
  for (; TAB[h]; h = (h + 1) & (TCAP - 1)) {
    Cell *x = &C[TAB[h] - 1];
    if (x->sym != s || x->n != n) continue;
    uint32_t k = 0; while (k < n && find(x->arg[k]) == a[k]) k++;
    if (k == n) return find(TAB[h] - 1);                                  /* the same construction: that cell */
  }
  uint32_t c = new_cell(s, n, a, 0); TAB[h] = c + 1; TUSED++; return c;
}

/* ---- equations ---------------------------------------------------------------------------------------- */
typedef struct Pat { int var; uint32_t sym, n; struct Pat *arg[MAXARG]; } Pat;   /* var >= 0: a variable */
typedef struct { Pat *lhs, *rhs; int nvars; } Eq;
static Eq *EQS; static uint32_t NEQ;

static uint32_t whnf(uint32_t c);
static int match(Pat *p, uint32_t c, uint32_t *bind, uint8_t *bound) {
  if (p->var >= 0) {
    if (!bound[p->var]) { bind[p->var] = c; bound[p->var] = 1; return 1; }
    return whnf(bind[p->var]) == whnf(c);                                 /* the same variable twice: identified? */
  }
  c = whnf(c);
  if (C[c].sym != p->sym || C[c].n != p->n) return 0;
  for (uint32_t i = 0; i < p->n; i++) if (!match(p->arg[i], C[c].arg[i], bind, bound)) return 0;
  return 1;
}
static uint32_t build(Pat *p, const uint32_t *bind) {
  if (p->var >= 0) return bind[p->var];
  uint32_t a[MAXARG]; for (uint32_t i = 0; i < p->n; i++) a[i] = build(p->arg[i], bind);
  return construct(p->sym, p->n, a);
}

/* a cell folded into what its equations make it; a cell no equation applies to is its own value */
static uint32_t whnf(uint32_t c) {
  c = find(c);
  if (C[c].done) return c;
  if (C[c].sym == S_MIN && C[c].n == 2) {                                  /* the meet of two elements */
    uint32_t x = whnf(C[c].arg[0]), y = whnf(C[c].arg[1]);
    if (C[x].sym == S_ELEM && C[y].sym == S_ELEM) {
      uint32_t xy[2] = { x, y }, m = construct(S_MIN, 2, xy);      /* built from the folded parts: that cell */
      if (m != c) { fold(c, m); return whnf(m); }
      uint32_t lo = x;
      if (x != y) { NEW_RELATIONS++; lo = C[x].val <= C[y].val ? x : y; }
      fold(c, lo); return find(lo);
    }
  }
  for (uint32_t e = 0; e < NEQ; e++) {
    Pat *l = EQS[e].lhs;
    if (l->sym != C[c].sym || l->n != C[c].n) continue;
    uint32_t bind[32]; uint8_t bound[32] = {0};
    int ok = 1;
    for (uint32_t i = 0; i < l->n && ok; i++) ok = match(l->arg[i], C[c].arg[i], bind, bound);
    if (!ok) continue;
    STEPS++;
    uint32_t r = whnf(build(EQS[e].rhs, bind));
    fold(c, r); return find(r);
  }
  C[c].done = 1; return c;
}

/* ---- reading equations ---------------------------------------------------------------------------------- */
static const char *S; static size_t P;
static void ws(void) { for (;;) { while (isspace((unsigned char)S[P])) P++; if (S[P] == '/' && S[P+1] == '/') { while (S[P] && S[P] != '\n') P++; continue; } return; } }
static char *VARS[32]; static int NVARS;
static Pat *pat(void) {
  ws(); size_t s = P; while (isalnum((unsigned char)S[P]) || S[P] == '_') P++;
  if (s == P) { fprintf(stderr, "hyper: expected a name at offset %zu\n", P); exit(2); }
  char name[128]; snprintf(name, sizeof name, "%.*s", (int)(P - s), S + s);
  Pat *p = calloc(1, sizeof *p); p->var = -1;
  if (isupper((unsigned char)name[0])) {
    for (int i = 0; i < NVARS; i++) if (!strcmp(VARS[i], name)) { p->var = i; return p; }
    VARS[NVARS] = strdup(name); p->var = NVARS++; return p;
  }
  p->sym = sym(name); ws();
  if (S[P] == '(') {
    P++;
    for (;;) { ws(); if (S[P] == ')') { P++; break; } p->arg[p->n++] = pat(); ws(); if (S[P] == ',') P++; }
  }
  return p;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: hyper EQUATIONS ELEMENTS\n"); return 1; }
  FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = malloc((size_t)len + 1); if (fread(src, 1, (size_t)len, f) != (size_t)len) { perror(argv[1]); return 1; }
  src[len] = 0; fclose(f);
  S_MIN = sym("min"); S_ELEM = sym("elem");
  S = src; P = 0;
  for (ws(); S[P]; ws()) {
    NVARS = 0; EQS = realloc(EQS, (NEQ + 1) * sizeof *EQS);
    EQS[NEQ].lhs = pat(); ws(); if (S[P] != '=') { fprintf(stderr, "hyper: expected '=' at offset %zu\n", P); return 2; } P++;
    EQS[NEQ].rhs = pat(); ws(); if (S[P] != ';') { fprintf(stderr, "hyper: expected ';' at offset %zu\n", P); return 2; } P++;
    EQS[NEQ].nvars = NVARS; NEQ++;
  }
  tab_grow();
  /* the elements: the finite set `input`, built as one(e) and the union of halves */
  FILE *g = fopen(argv[2], "r"); if (!g) { perror(argv[2]); return 1; }
  long long v; uint32_t n = 0, cap = 0, *el = 0;
  while (fscanf(g, "%lld", &v) == 1) { if (n == cap) { cap = cap ? cap * 2 : 64; el = realloc(el, cap * 4ul); } el[n] = new_cell(S_ELEM, 0, 0, v); C[el[n]].done = 1; n++; }
  fclose(g);
  uint32_t S_ONE = sym("one"), S_UNION = sym("union"), S_PRESENT = sym("present"), S_CONS = sym("cons");
  uint32_t *level = malloc((n ? n : 1) * 4ul);
  for (uint32_t i = 0; i < n; i++) level[i] = construct(S_ONE, 1, &el[i]);
  /* Fin n as the union of halves */
  uint32_t input;
  {
    uint32_t build_set(uint32_t lo, uint32_t hi) {
      if (hi - lo == 1) return level[lo];
      uint32_t mid = lo + (hi - lo) / 2, a[2] = { build_set(lo, mid), build_set(mid, hi) };
      return construct(S_UNION, 2, a);
    }
    input = n ? build_set(0, n) : construct(sym("empty"), 0, 0);
  }
  uint32_t term = construct(S_PRESENT, 1, &input);
  /* the presentation, read off: each cons is folded as it is reached */
  long long prev = 0; int ordered = 1; uint32_t k = 0;
  for (uint32_t t = whnf(term); C[t].sym == S_CONS && C[t].n == 2; t = whnf(C[t].arg[1])) {
    uint32_t h = whnf(C[t].arg[0]);
    if (k && C[h].val < prev) ordered = 0;
    prev = C[h].val;
    if (n <= 64) printf("%s%lld", k ? " " : "", C[h].val);
    k++;
  }
  if (n <= 64) printf("\n");
  double lg = 0; for (uint32_t i = 2; i <= n; i++) lg += log2((double)i);
  printf("- n: %u\n- presented: %u\n- ordered: %s\n- new relations: %llu\n- log2 n!: %.1f\n- equation steps: %llu\n- folds: %llu\n- cells: %u\n",
         n, k, ordered && k == n ? "yes" : "NO", (unsigned long long)NEW_RELATIONS, lg,
         (unsigned long long)STEPS, (unsigned long long)FOLDS, NC);
  return 0;
}

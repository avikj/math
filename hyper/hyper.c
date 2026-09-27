/* hyper.c: Hyperactive (hyper/HYPERACTIVE.md).
 *
 * One object: the identification.  One operation: folding; what is identified is one cell.
 *
 * One store.  A cell is its construction (kind, part, part), the parts read through the folds; building a
 * construction that already exists gives that cell.  Folding is union.  The identities of the constructions are
 * applied when a cell is built, so a construction an identity makes equal to an existing cell is that cell from
 * birth.  Nothing else acts.
 *
 *   ELEM(v)        an element of V; its value is its construction
 *   EMPTY, ONE(x), UNION(A, B)       finite sets; UNION is disjoint union (Numbers: addition)
 *   MIN2(a, b)     the meet of two elements; order is this cell: a <= b is MIN2(a, b) folded into a
 *   LEAST(S)       the least element of S
 *   REST(S)        S without its least element
 *
 * Identities:  UNION(EMPTY, B) = B,  UNION(A, EMPTY) = A,  LEAST(ONE x) = x,  REST(ONE x) = EMPTY,
 *   MIN2(a, a) = a,  MIN2(a, b) = MIN2(b, a),
 *   LEAST(UNION(A, B)) = MIN2(LEAST A, LEAST B)                      (the meet is associative)
 *   REST(UNION(A, B))  = UNION(REST A, B) if that meet is LEAST A, else UNION(A, REST B)
 *   MIN2(a, c) = a  when a <= b and b <= c are folded                 (transitivity is associativity)
 * A MIN2 of two distinct elements that no fold and no composite of folds identifies is a new relation: the one
 * place an element's value is read, and one part of the witness.
 *
 * sort is its definition: the ordered presentation of S is LEAST(S) followed by the ordered presentation of
 * REST(S).  The set is Fin n labelled into V, Fin n built as the union of halves. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

enum { ELEM, EMPTY_K, ONE, UNION, MIN2, LEAST, REST };
static uint8_t *KIND; static uint32_t *P1, *P2, *PARENT; static long long *VALUE;
static uint32_t NCELLS, CAP;
static uint64_t FOLDS, NEW_RELATIONS, COMPOSITES;
static uint32_t EMPTY;

static uint32_t find(uint32_t c) { while (PARENT[c] != c) { PARENT[c] = PARENT[PARENT[c]]; c = PARENT[c]; } return c; }
static void fold(uint32_t c, uint32_t into) { c = find(c); into = find(into); if (c != into) { PARENT[c] = into; FOLDS++; } }

static uint32_t new_cell(uint32_t kind, uint32_t a, uint32_t b, long long v) {
  if (NCELLS == CAP) {
    CAP = CAP ? CAP * 2 : 1 << 16;
    KIND = realloc(KIND, CAP); P1 = realloc(P1, CAP * 4ul); P2 = realloc(P2, CAP * 4ul);
    PARENT = realloc(PARENT, CAP * 4ul); VALUE = realloc(VALUE, CAP * 8ul);
    if (!KIND || !P1 || !P2 || !PARENT || !VALUE) { fprintf(stderr, "hyper: out of memory\n"); exit(2); }
  }
  uint32_t c = NCELLS++; KIND[c] = (uint8_t)kind; P1[c] = a; P2[c] = b; PARENT[c] = c; VALUE[c] = v; return c;
}

/* the store: construction -> the one cell */
static uint32_t *TABLE, TCAP, TUSED;
static uint64_t key(uint32_t k, uint32_t a, uint32_t b) { uint64_t h = (k + 1) * 0x9E3779B97F4A7C15ull ^ a * 0xC2B2AE3D27D4EB4Full ^ (uint64_t)b * 0x165667B19E3779F9ull; return h ^ (h >> 31); }
static void table_grow(void) {
  uint32_t old = TCAP, *ot = TABLE;
  TCAP = TCAP ? TCAP * 2 : 1 << 16; TABLE = calloc(TCAP, 4);
  for (uint32_t i = 0; i < old; i++) if (ot[i]) {
    uint32_t c = ot[i] - 1; uint64_t h = key(KIND[c], find(P1[c]), find(P2[c])) & (TCAP - 1);
    while (TABLE[h]) h = (h + 1) & (TCAP - 1);
    TABLE[h] = c + 1;
  }
  free(ot);
}
static uint32_t construct(uint32_t kind, uint32_t a, uint32_t b) {
  a = find(a); b = find(b);
  switch (kind) {                                                        /* identities, at construction */
    case UNION: if (a == EMPTY) return b; if (b == EMPTY) return a; break;
    case LEAST: if (KIND[a] == ONE) return find(P1[a]); break;
    case REST:  if (KIND[a] == ONE) return EMPTY; break;
    case MIN2:  if (a == b) return a; if (a > b) { uint32_t t = a; a = b; b = t; } break;
  }
  if (2 * (TUSED + 1) >= TCAP) table_grow();
  uint64_t h = key(kind, a, b) & (TCAP - 1);
  for (; TABLE[h]; h = (h + 1) & (TCAP - 1)) {
    uint32_t c = TABLE[h] - 1;
    if (KIND[c] == kind && find(P1[c]) == a && find(P2[c]) == b) return find(c);   /* the same construction */
  }
  uint32_t c = new_cell(kind, a, b, 0);
  TABLE[h] = c + 1; TUSED++;
  return c;
}

/* the folded relations, indexed by their lower element: the composite of folds is read here */
static uint32_t **UP, *NUP, *UPCAP, *MARK, EPOCH, *STACK;
static void index_relation(uint32_t lo, uint32_t hi) {
  if (NUP[lo] == UPCAP[lo]) { UPCAP[lo] = UPCAP[lo] ? UPCAP[lo] * 2 : 4; UP[lo] = realloc(UP[lo], UPCAP[lo] * 4ul); }
  UP[lo][NUP[lo]++] = hi;
}
static int composite(uint32_t from, uint32_t to) {
  EPOCH++; uint32_t sp = 0; STACK[sp++] = from; MARK[from] = EPOCH;
  while (sp) {
    uint32_t x = STACK[--sp];
    for (uint32_t i = 0; i < NUP[x]; i++) {
      uint32_t y = UP[x][i];
      if (y == to) return 1;
      if (MARK[y] != EPOCH) { MARK[y] = EPOCH; STACK[sp++] = y; }
    }
  }
  return 0;
}

/* the meet of two elements: a cell of the store, folded into the lesser */
static uint32_t meet(uint32_t a, uint32_t b) {
  uint32_t c = construct(MIN2, a, b);
  if (KIND[c] != MIN2) return c;                                         /* an identity: a single element */
  uint32_t x = find(P1[c]), y = find(P2[c]), lo;
  if (composite(x, y)) { lo = x; COMPOSITES++; }
  else if (composite(y, x)) { lo = y; COMPOSITES++; }
  else { NEW_RELATIONS++; lo = VALUE[x] <= VALUE[y] ? x : y; index_relation(lo, lo == x ? y : x); }
  fold(c, lo);
  return lo;
}

static uint32_t least(uint32_t s);
static uint32_t rest(uint32_t s) {
  uint32_t c = construct(REST, s, 0);
  if (KIND[c] != REST) return c;
  uint32_t a = find(P1[find(P1[c])]), b = find(P2[find(P1[c])]);        /* s = UNION(a, b) */
  uint32_t r = least(P1[c]) == least(a) ? construct(UNION, rest(a), b) : construct(UNION, a, rest(b));
  fold(c, r);
  return find(r);
}
static uint32_t least(uint32_t s) {
  uint32_t c = construct(LEAST, s, 0);
  if (KIND[c] != LEAST) return c;
  uint32_t u = find(P1[c]);                                               /* s = UNION(a, b) */
  uint32_t m = meet(least(P1[u]), least(P2[u]));
  fold(c, m);
  return find(m);
}

/* Fin n labelled into V, built as the union of halves */
static uint32_t *ELEMS;
static uint32_t finite_set(uint32_t from, uint32_t to) {
  if (to - from == 1) return construct(ONE, ELEMS[from], 0);
  uint32_t mid = from + (to - from) / 2;
  return construct(UNION, finite_set(from, mid), finite_set(mid, to));
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: hyper FILE   (FILE: the elements, whitespace separated)\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  long long *in = 0, v; uint32_t n = 0, cap = 0;
  while (fscanf(f, "%lld", &v) == 1) { if (n == cap) { cap = cap ? cap * 2 : 64; in = realloc(in, cap * 8ul); } in[n++] = v; }
  fclose(f);
  if (!n) { printf("\n"); return 0; }
  table_grow();
  EMPTY = new_cell(EMPTY_K, 0, 0, 0);
  ELEMS = malloc(n * 4ul);
  for (uint32_t i = 0; i < n; i++) ELEMS[i] = new_cell(ELEM, i, 0, in[i]);
  size_t m = (size_t)n + 8;
  UP = calloc(m, sizeof *UP); NUP = calloc(m, 4); UPCAP = calloc(m, 4); MARK = calloc(m, 4); STACK = malloc(m * 4);
  /* the ordered presentation: LEAST(S), then the ordered presentation of REST(S) */
  uint32_t *out = malloc(n * 4ul), k = 0;
  for (uint32_t s = finite_set(0, n); s != EMPTY; s = rest(s)) out[k++] = least(s);
  double lg = 0; for (uint32_t i = 2; i <= n; i++) lg += log2((double)i);
  uint32_t ceil_lg_n = 0; while ((1u << ceil_lg_n) < n) ceil_lg_n++;
  int ordered = k == n; for (uint32_t i = 1; i < k; i++) if (VALUE[out[i-1]] > VALUE[out[i]]) ordered = 0;
  if (n <= 64) { for (uint32_t i = 0; i < k; i++) printf("%s%lld", i ? " " : "", VALUE[out[i]]); printf("\n"); }
  printf("- n: %u\n- ordered: %s\n- new relations: %llu\n- composites: %llu\n- log2 n!: %.1f\n- n*ceil(log2 n)-n+1: %u\n- folds: %llu\n- cells: %u\n",
         n, ordered ? "yes" : "NO", (unsigned long long)NEW_RELATIONS, (unsigned long long)COMPOSITES, lg,
         n * ceil_lg_n - n + 1, (unsigned long long)FOLDS, NCELLS);
  return 0;
}

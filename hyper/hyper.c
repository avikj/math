/* hyper.c: Hyperactive (hyper/HYPERACTIVE.md).
 *
 * One object: the identification.  One operation: folding; what is identified is one cell.
 *
 * The store is a set of cells.  A cell is identified by its construction: building the same construction twice
 * gives the same cell.  Folding two cells makes them one (union); a cell built from folded cells is built from
 * the one cell, because its construction is read through the folds (congruence is definitional, not a step).
 *
 * Order is an identification: a <= b is  min(a, b) = a  (the lattice; docs/divisibility.html).  Its identities
 * fold like any other: idempotence, commutativity, the bottom, and transitivity, which is associativity:
 *   min(a,b) = a  and  min(b,c) = b   give   min(a,c) = min(min(a,b),c) = min(a,min(b,c)) = min(a,b) = a.
 * A relation already reachable through folded relations is that composite: the same cell, nothing new.
 * A relation not yet reachable is new: one fold that reads the order of the two values.  That is the only fold
 * that contributes to the witness; its count is the length of the route (index.html §5).
 *
 * sort is its definition.  The elements are a finite set labelled into V; Fin n is built by disjoint union
 * (Numbers: addition is disjoint union), and the ordered presentation of a union is, by the lattice alone,
 *   c_k = min over i + j = k of max(a_i, b_j)        (a_0 = b_0 = bottom)
 * where a and b are the ordered presentations of the two parts.  Nothing below names a strategy; the cells of
 * this definition are built and folded until each c_k is one value. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { VAL, BOT, MIN, MAX };
static uint8_t *OP; static uint32_t *KA, *KB, *PARENT; static long long *V;   /* per cell */
static uint32_t NCELLS, CAP;
static uint64_t FOLDS, NEW_RELATIONS;                                      /* all folds; relations not yet reachable */

static uint32_t find(uint32_t c) { while (PARENT[c] != c) { PARENT[c] = PARENT[PARENT[c]]; c = PARENT[c]; } return c; }
static void fold(uint32_t c, uint32_t into) { c = find(c); into = find(into); if (c != into) { PARENT[c] = into; FOLDS++; } }

/* construction-keyed store: (op, parts read through the folds) -> the one cell */
static uint32_t *TABLE; static uint32_t TCAP;
static uint64_t hash3(uint32_t op, uint32_t a, uint32_t b) { uint64_t h = op * 0x9E3779B97F4A7C15ull ^ a * 0xC2B2AE3D27D4EB4Full ^ (uint64_t)b * 0x165667B19E3779F9ull; return h ^ (h >> 29); }
static uint32_t cell(uint32_t op, uint32_t a, uint32_t b, long long v);
static void grow(void) {
  CAP = CAP ? CAP * 2 : 1 << 16;
  OP = realloc(OP, CAP); KA = realloc(KA, CAP * 4ul); KB = realloc(KB, CAP * 4ul);
  PARENT = realloc(PARENT, CAP * 4ul); V = realloc(V, CAP * 8ul);
  if (!OP || !KA || !KB || !PARENT || !V) { fprintf(stderr, "hyper: out of memory\n"); exit(2); }
}
static void rehash(void) {
  uint32_t old = TCAP, *ot = TABLE;
  TCAP = TCAP ? TCAP * 2 : 1 << 17; TABLE = calloc(TCAP, 4);
  for (uint32_t i = 0; i < old; i++) if (ot[i]) {
    uint32_t c = ot[i] - 1; uint64_t h = hash3(OP[c], KA[c], KB[c]) & (TCAP - 1);
    while (TABLE[h]) h = (h + 1) & (TCAP - 1);
    TABLE[h] = c + 1;
  }
  free(ot);
}
static uint32_t cell(uint32_t op, uint32_t a, uint32_t b, long long v) {
  if (op == VAL || op == BOT) {                                             /* a value, or the bottom: leaves */
    if (NCELLS == CAP) grow();
    uint32_t c = NCELLS++; OP[c] = (uint8_t)op; KA[c] = KB[c] = 0; V[c] = v; PARENT[c] = c; return c;
  }
  a = find(a); b = find(b);
  if (a == b) return a;                                                     /* idempotence: min(a,a) = a */
  if (OP[a] == BOT) return op == MIN ? a : b;                               /* the bottom */
  if (OP[b] == BOT) return op == MIN ? b : a;
  if (a > b) { uint32_t t = a; a = b; b = t; }                              /* commutativity: one construction */
  if ((uint64_t)NCELLS * 2 >= TCAP) rehash();
  uint64_t h = hash3(op, a, b) & (TCAP - 1);
  for (; TABLE[h]; h = (h + 1) & (TCAP - 1)) {
    uint32_t c = TABLE[h] - 1;
    if (OP[c] == op && find(KA[c]) == a && find(KB[c]) == b) return find(c);   /* the same construction: the same cell */
  }
  if (NCELLS == CAP) grow();
  uint32_t c = NCELLS++; OP[c] = (uint8_t)op; KA[c] = a; KB[c] = b; V[c] = 0; PARENT[c] = c;
  TABLE[h] = c + 1; return c;
}

/* the relations between values, as folded: an edge lo -> hi for each  min(lo, hi) = lo  that was made new */
static uint32_t **UP; static uint32_t *NUP, *UPCAP; static uint32_t *MARK, EPOCH;
static void edge(uint32_t lo, uint32_t hi) {
  if (NUP[lo] == UPCAP[lo]) { UPCAP[lo] = UPCAP[lo] ? UPCAP[lo] * 2 : 4; UP[lo] = realloc(UP[lo], UPCAP[lo] * 4ul); }
  UP[lo][NUP[lo]++] = hi;
}
static int reachable(uint32_t from, uint32_t to) {                          /* the composite of folded relations */
  static uint32_t *stack; static uint32_t scap;
  if (scap < NCELLS) { scap = NCELLS; stack = realloc(stack, scap * 4ul); }
  EPOCH++; uint32_t sp = 0; stack[sp++] = from; MARK[from] = EPOCH;
  while (sp) {
    uint32_t x = stack[--sp];
    if (x == to) return 1;
    for (uint32_t i = 0; i < NUP[x]; i++) { uint32_t y = UP[x][i]; if (MARK[y] != EPOCH) { MARK[y] = EPOCH; stack[sp++] = y; } }
  }
  return 0;
}

/* fold a cell until it is one value: its parts first, then the relation between the two values they are */
static uint32_t value(uint32_t c) {
  c = find(c);
  if (OP[c] == VAL || OP[c] == BOT) return c;
  uint32_t x = value(KA[c]), y = value(KB[c]);
  uint32_t lo, hi;
  if (x == y) lo = hi = x;
  else if (OP[x] == BOT || OP[y] == BOT) { lo = OP[x] == BOT ? x : y; hi = lo == x ? y : x; }
  else if (reachable(x, y)) { lo = x; hi = y; }                              /* already the composite */
  else if (reachable(y, x)) { lo = y; hi = x; }
  else {                                                                    /* new: the order of the two values */
    NEW_RELATIONS++;
    if (V[x] <= V[y]) { lo = x; hi = y; } else { lo = y; hi = x; }
    edge(lo, hi);
  }
  uint32_t r = OP[c] == MIN ? lo : hi;
  fold(c, r);
  return find(r);
}

/* the ordered presentation of the labelled finite set over [from, to): Fin n built by disjoint union */
static uint32_t BOTTOM;
static uint32_t *presentation(const uint32_t *x, uint32_t from, uint32_t to) {
  uint32_t n = to - from, *out = malloc((n ? n : 1) * 4ul);
  if (n == 1) { out[0] = x[from]; return out; }
  uint32_t mid = from + n / 2, na = mid - from, nb = to - mid;
  uint32_t *a = presentation(x, from, mid), *b = presentation(x, mid, to);
  for (uint32_t k = 1; k <= n; k++) {                                       /* c_k = min over i+j=k of max(a_i, b_j) */
    uint32_t ck = 0; int have = 0;
    uint32_t ilo = k > nb ? k - nb : 0, ihi = k < na ? k : na;
    for (uint32_t i = ihi + 1; i-- > ilo;) {
      uint32_t j = k - i;
      uint32_t ai = i ? a[i-1] : BOTTOM, bj = j ? b[j-1] : BOTTOM;
      uint32_t m = cell(MAX, ai, bj, 0);
      ck = have ? cell(MIN, ck, m, 0) : m; have = 1;
    }
    out[k-1] = value(ck);
  }
  free(a); free(b);
  return out;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: hyper FILE   (FILE: the elements, whitespace separated)\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  long long *in = 0; uint32_t n = 0, cap = 0; long long v;
  while (fscanf(f, "%lld", &v) == 1) { if (n == cap) { cap = cap ? cap * 2 : 64; in = realloc(in, cap * 8ul); } in[n++] = v; }
  fclose(f);
  if (!n) { printf("\n"); return 0; }
  grow(); rehash();
  BOTTOM = cell(BOT, 0, 0, 0);
  uint32_t *x = malloc(n * 4ul);
  for (uint32_t i = 0; i < n; i++) x[i] = cell(VAL, 0, 0, in[i]);
  UP = calloc(4ul * n + 8, sizeof *UP); NUP = calloc(4ul * n + 8, 4); UPCAP = calloc(4ul * n + 8, 4); MARK = calloc(4ul * n + 8, 4);
  uint32_t *y = presentation(x, 0, n);
  double bound = 0; for (uint32_t k = 2; k <= n; k++) bound += log2((double)k);
  if (n <= 64) { for (uint32_t i = 0; i < n; i++) printf("%s%lld", i ? " " : "", V[y[i]]); printf("\n"); }
  int ok = 1; for (uint32_t i = 1; i < n; i++) if (V[y[i-1]] > V[y[i]]) ok = 0;
  printf("- n: %u\n- ordered: %s\n- new relations: %llu\n- log2 n!: %.1f (ceil %.0f)\n- folds: %llu\n- cells: %u\n",
         n, ok ? "yes" : "NO", (unsigned long long)NEW_RELATIONS, bound, ceil(bound), (unsigned long long)FOLDS, NCELLS);
  return 0;
}

/* hyper.c: Hyperactive.
 *
 * One store of cells; one operation, folding.
 *
 * A cell is a construction: a symbol and its parts, the parts read through the folds.  Building a construction
 * that already exists gives that cell.  A symbol with no parts is a cell too.
 *
 * The declarations are cells in the same store.  `l = r` is the cell =(l, r); `l = r when p = q, p # q` is the
 * cell when(=(l, r), =(p, q), #(p, q)).  An uppercase name is a variable: a cell wired to every place it occurs
 * in its declaration.  A cell that contains a variable is open: it is a declaration's own, and it is not folded.
 *
 * An identity holds at every instance of its shape.  A closed cell with the symbol of an identity's left side
 * is such an instance: the identity's right side, with its variables wired to the cell's parts, is folded with
 * it; its premises are instances too.  A cell with the symbol of a premise's left side, once the premise holds,
 * folds the identity's left side where that cell exists.  Every identity, at every instance, once.
 *
 * Folding: two cells made equal are one class; everything built on them is read again, and a construction that
 * now coincides with another is that other.  A symbol that is no identity's left side and has no cases is a
 * constructor, its own value; two constructors in one class with the same symbol have their parts identified,
 * with different symbols the case is empty.  `S in a b …;` makes S range over those constructors, each case
 * folded on its own.  The result is what remains when nothing more folds.
 *
 * How parts are presented: `ac f;` flat and unordered, `idem f;` once each, `unit f e;` without e.  A sum of a
 * free commutative monoid (ac, not idem) that is one class with another is one after their common parts are
 * taken from both; a sum that is the unit has every part the unit.  In a pattern, R* is the remaining parts of
 * an ac construction, and p* stands for every part: each part meets p, and a right side's q* is q at each.
 *
 * usage: hyper FILE… NUMBERS | FORMULA.cnf
 *   NUMBERS: the list `input` = cons(elem(v0), cons(elem(v1), … nil)), each v the construction suc(…suc(zero)).
 *            The result is the class of `main`, read as cons/nil.
 *   FORMULA.cnf: DIMACS.  x1 … xn are declared `in true false`; each clause or(…) is folded with true. */
#include <ctype.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

#define NONE 0xFFFFFFFFu
typedef uint32_t u32;

/* ---- symbols ---------------------------------------------------------------------------------------------- */
typedef struct { char *name; uint8_t ac, idem, defined, var, rest; u32 unit, *cases, ncases, *anc, nanc; } Sym;
static Sym *SY; static u32 NSY;
static u32 sym(const char *s) {
  for (u32 i = 0; i < NSY; i++) if (!strcmp(SY[i].name, s)) return i;
  SY = realloc(SY, (NSY + 1) * sizeof *SY); memset(&SY[NSY], 0, sizeof *SY);
  SY[NSY].name = strdup(s); SY[NSY].unit = NONE;
  return NSY++;
}

/* ---- the store ---------------------------------------------------------------------------------------------- */
typedef struct {
  u32 sym, n, *arg, parent, size, value, *uses, nuses, cuses, next, how;
  uint64_t fired; uint8_t queued, open;
} Cell;
static Cell *C; static u32 NC, CCAP;
static int EMPTY;
static uint64_t FOLDS;

typedef struct { u32 kind, cell; uint64_t old; } Tr;              /* what a case changes */
static Tr *TR; static u32 NTR, CTR, INCASE;
static void trail(u32 kind, u32 cell, uint64_t old) {
  if (!INCASE) return;
  if (NTR == CTR) { CTR = CTR ? CTR * 2 : 4096; TR = realloc(TR, CTR * sizeof *TR); }
  TR[NTR++] = (Tr){ kind, cell, old };
}

static u32 find(u32 c) { while (C[c].parent != c) c = C[c].parent; return c; }
static u32 val(u32 c) { return C[find(c)].value; }

static u32 *TAB, TCAP, TUSED;
static uint64_t hkey(u32 s, u32 n, const u32 *a) {
  uint64_t h = (s + 1) * 0x9E3779B97F4A7C15ull;
  for (u32 i = 0; i < n; i++) h = (h ^ (a[i] + 1)) * 0xC2B2AE3D27D4EB4Full;
  return h ^ (h >> 31);
}
static u32 lookup(u32 s, u32 n, const u32 *a) {
  for (uint64_t h = hkey(s, n, a) & (TCAP - 1); TAB[h]; h = (h + 1) & (TCAP - 1)) {
    Cell *x = &C[TAB[h] - 1]; if (x->sym != s || x->n != n) continue;
    u32 k = 0; while (k < n && find(x->arg[k]) == a[k]) k++;
    if (k == n) return TAB[h] - 1;
  }
  return NONE;
}
static void insert_key(u32 c, u32 n, const u32 *a) {
  if (2 * (TUSED + 1) >= TCAP) {
    free(TAB); TCAP *= 2; TAB = calloc(TCAP, 4); TUSED = 0;
    for (u32 d = 0; d < NC; d++) {
      if (d == c) continue;
      u32 b[C[d].n + 1]; for (u32 k = 0; k < C[d].n; k++) b[k] = find(C[d].arg[k]);
      uint64_t h = hkey(C[d].sym, C[d].n, b) & (TCAP - 1); while (TAB[h]) h = (h + 1) & (TCAP - 1);
      TAB[h] = d + 1; TUSED++;
    }
  }
  uint64_t h = hkey(C[c].sym, n, a) & (TCAP - 1); while (TAB[h]) h = (h + 1) & (TCAP - 1);
  TAB[h] = c + 1; TUSED++;
}
static void rebuild_table(void) {
  memset(TAB, 0, TCAP * 4ul); TUSED = 0;
  for (u32 c = 0; c < NC; c++) { u32 b[C[c].n + 1]; for (u32 k = 0; k < C[c].n; k++) b[k] = find(C[c].arg[k]); insert_key(c, C[c].n, b); }
}
static void add_use(u32 cls, u32 c) {
  Cell *x = &C[cls]; trail(3, cls, x->nuses);
  if (x->nuses == x->cuses) { x->cuses = x->cuses ? x->cuses * 2 : 4; x->uses = realloc(x->uses, x->cuses * 4ul); }
  x->uses[x->nuses++] = c;
}

static u32 *Q, NQ, CQ;
static void queue(u32 c) {
  if (C[c].queued || C[c].open) return;
  C[c].queued = 1;
  if (NQ == CQ) { CQ = CQ ? CQ * 2 : 4096; Q = realloc(Q, CQ * 4ul); }
  Q[NQ++] = c;
}

static int cmpu(const void *a, const void *b) { u32 x = *(const u32 *)a, y = *(const u32 *)b; return x < y ? -1 : x > y; }

static u32 S_EACH_ = NONE;
/* the parts as the declarations present them; returns the class the construction is when it is one part */
static u32 present(u32 s, u32 n, const u32 *args, u32 **out, u32 *m_out) {
  u32 cap = n + 8, *a = malloc(cap * 4ul), m = 0;
  for (u32 i = 0; i < n; i++) {
    u32 x = find(args[i]);
    if (SY[s].ac) {
      u32 v = C[x].value;
      if (v != NONE && C[v].sym == s) {
        if (m + C[v].n >= cap) { cap = (m + C[v].n) * 2 + 8; a = realloc(a, cap * 4ul); }
        for (u32 k = 0; k < C[v].n; k++) a[m++] = find(C[v].arg[k]);
        continue;
      }
      if (SY[s].unit != NONE && v != NONE && C[v].sym == SY[s].unit && C[v].n == 0) continue;
    }
    if (m == cap) { cap *= 2; a = realloc(a, cap * 4ul); }
    a[m++] = x;
  }
  if (SY[s].ac) {
    qsort(a, m, 4, cmpu);
    if (SY[s].idem) { u32 w = 0; for (u32 i = 0; i < m; i++) if (!w || a[w - 1] != a[i]) a[w++] = a[i]; m = w; }
  }
  *out = a; *m_out = m;
  if (SY[s].ac && m == 1 && !(SY[C[a[0]].sym].var && SY[C[a[0]].sym].rest) && C[a[0]].sym != S_EACH_) return a[0];
  return NONE;                          /* a pattern's lone R* or p* stands for many parts, not for one */
}

/* an ac construction is a value once every part is: until then a part may yet be the unit or another sum */
static int ac_known(u32 c) {
  if (!SY[C[c].sym].ac) return 1;
  for (u32 k = 0; k < C[c].n; k++) {                                /* and presented flat, without the unit */
    u32 v = C[find(C[c].arg[k])].value;
    if (v == NONE || C[v].sym == C[c].sym || (C[v].sym == SY[C[c].sym].unit && C[v].n == 0)) return 0;
  }
  return 1;
}

static u32 construct(u32 s, u32 n, const u32 *args, int create) {
  u32 *a, m; u32 one = present(s, n, args, &a, &m);
  if (one != NONE) { free(a); return one; }
  if (SY[s].ac && m == 0 && SY[s].unit != NONE) { free(a); return construct(SY[s].unit, 0, 0, create); }
  u32 e = lookup(s, m, a);
  if (e != NONE) { free(a); return find(e); }
  if (!create) { free(a); return NONE; }
  if (NC == CCAP) { CCAP = CCAP ? CCAP * 2 : 1 << 16; C = realloc(C, CCAP * sizeof *C); }
  u32 c = NC++; Cell *x = &C[c]; memset(x, 0, sizeof *x);
  x->sym = s; x->n = m; x->arg = a; x->parent = c; x->size = 1; x->next = c; x->how = NONE;
  x->open = SY[s].var;
  for (u32 i = 0; i < m; i++) { if (C[a[i]].open) x->open = 1; add_use(a[i], c); }
  x->value = x->open || SY[s].defined || !ac_known(c) ? NONE : c;     /* a constructor is its own value */
  insert_key(c, m, a);
  queue(c);
  return c;
}
static u32 atom(const char *s) { return construct(sym(s), 0, 0, 1); }

/* ---- folding ----------------------------------------------------------------------------------------------- */
static u32 *PEND, NPEND, CPEND;
static void pend(u32 a, u32 b) {
  if (NPEND + 2 > CPEND) { CPEND = CPEND ? CPEND * 2 : 1024; PEND = realloc(PEND, CPEND * 4ul); }
  PEND[NPEND++] = a; PEND[NPEND++] = b;
}
static void reread(u32 u) {
  u32 *a, m; u32 one = present(C[u].sym, C[u].n, C[u].arg, &a, &m);
  if (one != NONE) { free(a); if (find(one) != find(u)) pend(u, one); return; }
  if (SY[C[u].sym].ac && m == 0 && SY[C[u].sym].unit != NONE) { free(a); pend(u, construct(SY[C[u].sym].unit, 0, 0, 1)); return; }
  u32 e = lookup(C[u].sym, m, a);
  if (e == NONE) {
    if (m == C[u].n) insert_key(u, m, a);
    else pend(u, construct(C[u].sym, m, a, 1));
  } else if (find(e) != find(u)) pend(u, e);
  free(a);
}
static void drain(void);
static void merge(u32 a, u32 b) {
  if (C[a].open || C[b].open) return;
  pend(a, b);
  drain();
}
static void drain(void) {
  while (NPEND) {
    u32 y = find(PEND[--NPEND]), x = find(PEND[--NPEND]);
    if (x == y) continue;
    FOLDS++;
    if (C[x].size > C[y].size) { u32 t = x; x = y; y = t; }
    u32 vx = C[x].value, vy = C[y].value, ny = C[y].nuses;
    trail(0, x, C[x].parent); C[x].parent = y;
    trail(1, y, C[y].size); C[y].size += C[x].size;
    trail(4, x, C[x].next); trail(4, y, C[y].next);
    { u32 t = C[x].next; C[x].next = C[y].next; C[y].next = t; }
    if (vy == NONE && vx != NONE) { trail(2, y, vy); C[y].value = vx; }
    if (vx != NONE && vy != NONE && vx != vy) {
      if (C[vx].sym != C[vy].sym || (C[vx].n != C[vy].n && !SY[C[vx].sym].ac)) { if (!EMPTY) { trail(5, 0, 0); EMPTY = 1; } }
      else if (!SY[C[vx].sym].ac) for (u32 k = 0; k < C[vx].n; k++) pend(C[vx].arg[k], C[vy].arg[k]);
    }
    for (u32 i = 0; i < C[x].nuses; i++) add_use(y, C[x].uses[i]);
    for (u32 i = 0; i < C[x].nuses; i++) { reread(C[x].uses[i]); queue(C[x].uses[i]); }
    if (vy == NONE && vx != NONE) for (u32 i = 0; i < ny; i++) { reread(C[y].uses[i]); queue(C[y].uses[i]); }
    u32 m = x; do { queue(m); m = C[m].next; } while (m != x);
    if (vy == NONE && vx != NONE) { u32 k = y; do { queue(k); k = C[k].next; } while (k != y); }
  }
}

/* ---- the declarations, as cells ------------------------------------------------------------------------------ */
static u32 *DECL, NDECL; static int *DLINE; static uint64_t *DUSED;
static u32 S_EQ, S_WHEN, S_APART, S_EACH;
static u32 d_eq(u32 d) { return C[d].sym == S_WHEN ? C[d].arg[0] : d; }            /* its =(l, r) */
static u32 d_lhs(u32 d) { return C[d_eq(d)].arg[0]; }
static u32 d_rhs(u32 d) { return C[d_eq(d)].arg[1]; }
static u32 d_np(u32 d) { return C[d].sym == S_WHEN ? C[d].n - 1 : 0; }
static u32 d_prem(u32 d, u32 k) { return C[d].arg[1 + k]; }
/* the parts of a declaration's cells are read from the cells themselves, not through classes: a declaration's
   own cells are open and never folded */

typedef struct { u32 n; u32 var[32], cls[32]; u32 *list[32], nlist[32]; uint8_t rest[32]; } Env;
static int env_get(Env *e, u32 v) { for (u32 i = 0; i < e->n; i++) if (e->var[i] == v) return (int)i; return -1; }
static void env_set(Env *e, u32 v, u32 cls, int rest) { e->var[e->n] = v; e->cls[e->n] = cls; e->rest[e->n] = (uint8_t)rest; e->list[e->n] = 0; e->nlist[e->n] = 0; e->n++; }
static int is_var(u32 p) { return SY[C[p].sym].var && C[p].n == 0; }
static int is_rest(u32 p) { return is_var(p) && SY[C[p].sym].rest; }
static int is_each(u32 p) { return C[p].sym == S_EACH; }

static u32 build(u32 p, Env *e, int create) {
  if (!C[p].open) return find(p);                                  /* a closed cell of a declaration is itself */
  if (is_var(p)) { int i = env_get(e, C[p].sym); return i < 0 ? NONE : e->cls[i]; }
  u32 s = C[p].sym, cap = 64, *a = malloc(cap * 4ul), m = 0;
  for (u32 i = 0; i < C[p].n; i++) {
    u32 q = C[p].arg[i];
    if (m + 64 >= cap) { cap *= 2; a = realloc(a, cap * 4ul); }
    if (is_rest(q)) {                                               /* the remaining parts, placed as parts */
      int j = env_get(e, C[q].sym); if (j < 0) { free(a); return NONE; }
      u32 r = find(e->cls[j]), v = C[r].value;
      if (e->rest[j] && v != NONE && C[v].sym == s && SY[s].ac) {
        while (m + C[v].n >= cap) { cap *= 2; a = realloc(a, cap * 4ul); }
        for (u32 k = 0; k < C[v].n; k++) a[m++] = C[v].arg[k];
        continue;
      }
      if (SY[s].unit != NONE && v != NONE && C[v].sym == SY[s].unit) continue;
      a[m++] = r; continue;
    }
    if (is_each(q)) {                                               /* q at each part the list variable ranges over */
      u32 inner = C[q].arg[0]; int j = -1;
      for (u32 t = 0; t < e->n; t++) if (e->list[t]) { j = (int)t; break; }
      if (j < 0) { free(a); return NONE; }
      u32 v = e->var[j], nl = e->nlist[j], *lst = e->list[j];
      while (m + nl >= cap) { cap *= 2; a = realloc(a, cap * 4ul); }
      for (u32 t = 0; t < nl; t++) {
        Env e2 = *e; e2.list[j] = 0; e2.cls[j] = lst[t]; (void)v;
        u32 x = build(inner, &e2, create); if (x == NONE) { free(a); return NONE; }
        a[m++] = x;
      }
      continue;
    }
    u32 x = build(q, e, create); if (x == NONE) { free(a); return NONE; }
    a[m++] = x;
  }
  u32 r = construct(s, m, a, create); free(a); return r;
}

typedef int (*K)(Env *, void *);
static int match_cls(u32 p, u32 cls, Env *e, K k, void *ctx);
static int match_cell(u32 p, u32 c, Env *e, K k, void *ctx);
static int match_parts(u32 p, const u32 *parts, u32 n, uint64_t used, u32 i, Env *e, K k, void *ctx) {
  u32 pn = C[p].n;
  if (i == pn) return (n == 0 || used == (n >= 64 ? ~0ull : (1ull << n) - 1)) ? k(e, ctx) : 0;
  u32 q = C[p].arg[i];
  if (is_rest(q)) {
    u32 rem[64], m = 0; for (u32 j = 0; j < n; j++) if (!(used >> j & 1)) rem[m++] = parts[j];
    u32 r = construct(C[p].sym, m, rem, 1);
    int j = env_get(e, C[q].sym);
    if (j >= 0) return find(e->cls[j]) == find(r) ? k(e, ctx) : 0;
    Env e2 = *e; env_set(&e2, C[q].sym, r, 1); return k(&e2, ctx);
  }
  if (is_each(q)) {                                                 /* every remaining part meets q's pattern */
    u32 inner = C[q].arg[0], lv = NONE;
    for (u32 t = 0; t < C[inner].n; t++) if (is_var(C[inner].arg[t])) { lv = C[C[inner].arg[t]].sym; break; }
    if (lv == NONE && is_var(inner)) lv = C[inner].sym;
    u32 *lst = malloc((n + 1) * 4ul), nl = 0;
    for (u32 j = 0; j < n; j++) {
      if (used >> j & 1) continue;
      u32 got = NONE;
      int one(Env *ee, void *cc) { (void)cc; int t = env_get(ee, lv); if (t >= 0) got = ee->cls[t]; return 1; }
      Env e1 = *e; if (!match_cls(inner, parts[j], &e1, one, 0) || got == NONE) { free(lst); return 0; }
      lst[nl++] = got;
    }
    Env e2 = *e; env_set(&e2, lv, NONE, 0); e2.list[e2.n - 1] = lst; e2.nlist[e2.n - 1] = nl;
    return k(&e2, ctx);                                              /* the list lives as long as the instance */
  }
  for (u32 j = 0; j < n; j++) {
    if (used >> j & 1) continue;
    if (!SY[C[p].sym].ac && j != i) continue;
    int inner(Env *ee, void *cc) { (void)cc; return match_parts(p, parts, n, used | 1ull << j, i + 1, ee, k, ctx); }
    if (match_cls(q, parts[j], e, inner, 0)) return 1;
  }
  return 0;
}
static int shape_fits(u32 p, u32 n) {
  u32 pn = C[p].n; int open_end = pn && (is_rest(C[p].arg[pn - 1]) || is_each(C[p].arg[pn - 1]));
  return n <= 64 && (open_end ? n + 1 >= pn : n == pn);
}
static int match_cell(u32 p, u32 c, Env *e, K k, void *ctx) {
  if (!C[p].open) return find(p) == find(c) ? k(e, ctx) : 0;
  if (is_var(p)) {
    int j = env_get(e, C[p].sym);
    if (j < 0) { Env e2 = *e; env_set(&e2, C[p].sym, find(c), 0); return k(&e2, ctx); }
    return find(e->cls[j]) == find(c) ? k(e, ctx) : 0;
  }
  if (C[c].sym != C[p].sym || !shape_fits(p, C[c].n)) return 0;
  return match_parts(p, C[c].arg, C[c].n, 0, 0, e, k, ctx);
}
static int match_cls(u32 p, u32 cls, Env *e, K k, void *ctx) {
  cls = find(cls);
  if (!C[p].open || is_var(p)) return match_cell(p, cls, e, k, ctx);
  u32 v = C[cls].value, s = C[p].sym;
  if (SY[s].ac && C[p].n && (is_rest(C[p].arg[C[p].n - 1]) || is_each(C[p].arg[C[p].n - 1])) && v != NONE && C[v].sym != s) {
    int unit = SY[s].unit != NONE && C[v].sym == SY[s].unit && C[v].n == 0;  /* one part, or none: a sum all the same */
    u32 one[1] = { cls };
    return match_parts(p, one, unit ? 0 : 1, 0, 0, e, k, ctx);
  }
  if (v != NONE) return match_cell(p, v, e, k, ctx);
  u32 m = cls; do { if (C[m].sym == C[p].sym && match_cell(p, m, e, k, ctx)) return 1; m = C[m].next; } while (m != cls);
  return 0;
}

static int apart(u32 a, u32 b) {
  u32 x = val(a), y = val(b);
  if (x == NONE || y == NONE || find(x) == find(y)) return 0;
  if (C[x].sym != C[y].sym || C[x].n != C[y].n) return 1;
  if (SY[C[x].sym].ac) return 0;
  for (u32 k = 0; k < C[x].n; k++) if (apart(C[x].arg[k], C[y].arg[k])) return 1;
  return 0;
}
/* the premises other than `skip`; a premise that is fully wired is an instance and is built; one with a
   variable not yet wired meets the cells already built on a wired part */
static int premises(u32 d, u32 i, int skip, Env *e, K k, void *ctx) {
  if (i == d_np(d)) return k(e, ctx);
  if ((int)i == skip) return premises(d, i + 1, skip, e, k, ctx);
  u32 pr = d_prem(d, i), l = C[pr].arg[0], r = C[pr].arg[1];
  if (C[pr].sym == S_APART) {
    u32 a = build(l, e, 0), b = build(r, e, 0);
    return a != NONE && b != NONE && apart(a, b) && premises(d, i + 1, skip, e, k, ctx);
  }
  int unbound = 0, anchor = -1;
  for (u32 j = 0; j < C[l].n; j++) {
    u32 q = C[l].arg[j];
    if (is_var(q) && env_get(e, C[q].sym) < 0) unbound = 1;
    else if (is_var(q) && anchor < 0) anchor = (int)j;
  }
  if (!unbound) {
    u32 c = build(l, e, 1), t = build(r, e, 1);
    return c != NONE && t != NONE && find(c) == find(t) && premises(d, i + 1, skip, e, k, ctx);
  }
  if (anchor < 0) return 0;
  u32 cls = find(e->cls[env_get(e, C[C[l].arg[anchor]].sym)]);
  for (u32 u = 0; u < C[cls].nuses; u++) {
    u32 cell = C[cls].uses[u];
    if (C[cell].sym != C[l].sym || C[cell].open) continue;
    int then(Env *ee, void *cc) {
      (void)cc; u32 t = build(r, ee, 0);
      return t != NONE && find(t) == find(cell) && premises(d, i + 1, skip, ee, k, ctx);
    }
    if (match_cell(l, cell, e, then, 0)) return 1;
  }
  return 0;
}

static int TRACE, DEBUG;
static void show(u32 c, int depth);
static void fold_with(u32 di, u32 target, Env *e) {
  u32 d = DECL[di], r = build(d_rhs(d), e, 1);
  if (r == NONE || find(r) == find(target)) return;
  DUSED[di]++;
  if (TRACE) { printf("  [%d] ", DLINE[di]); show(target, 0); printf("  =  "); show(r, 0); printf("\n"); }
  if (C[target].how == NONE) { trail(6, target, NONE); C[target].how = di; }
  merge(target, r);
}

/* sums of a free commutative monoid */
static void cancel(u32 c) {
  u32 s = C[c].sym, r = find(c), m = r;
  do {
    u32 d = m; m = C[m].next;
    if (d != c && C[d].sym == s) {
      u32 *a, na, *b, nb;
      u32 oa = present(s, C[c].n, C[c].arg, &a, &na), ob = present(s, C[d].n, C[d].arg, &b, &nb);
      if (oa == NONE && ob == NONE) {
        u32 x[na + 1], y[nb + 1], nx = 0, ny = 0, i = 0, j = 0, common = 0;
        while (i < na || j < nb) {
          if (i < na && j < nb && a[i] == b[j]) { i++; j++; common++; }
          else if (j >= nb || (i < na && a[i] < b[j])) x[nx++] = a[i++];
          else y[ny++] = b[j++];
        }
        if (common) { u32 p = construct(s, nx, x, 1), q = construct(s, ny, y, 1); if (find(p) != find(q)) merge(p, q); }
      }
      free(a); free(b);
      if (EMPTY) return;
    }
  } while (m != r);
  if (SY[s].unit != NONE) {
    u32 v = C[r].value;
    if (v != NONE && C[v].sym == SY[s].unit && C[v].n == 0) {
      u32 e = construct(SY[s].unit, 0, 0, 1);
      for (u32 k = 0; k < C[c].n && !EMPTY; k++) if (find(C[c].arg[k]) != find(e)) merge(C[c].arg[k], e);
    }
  }
}

/* the premise instances already made: a set of (cell, declaration, premise) */
static uint64_t *SEEN; static u32 SCAP, SUSED;
static int seen(uint64_t k) {
  if (!SCAP) return 0;
  for (u32 h = (u32)(k * 0x9E3779B97F4A7C15ull >> 32) & (SCAP - 1); SEEN[h]; h = (h + 1) & (SCAP - 1)) if (SEEN[h] == k + 1) return 1;
  return 0;
}
static void see_raw(uint64_t k) {
  u32 h = (u32)(k * 0x9E3779B97F4A7C15ull >> 32) & (SCAP - 1); while (SEEN[h] && SEEN[h] != ~0ull) h = (h + 1) & (SCAP - 1);
  SEEN[h] = k + 1; SUSED++;
}
static void see(uint64_t k) {
  if (2 * (SUSED + 1) >= SCAP) {
    uint64_t *old = SEEN; u32 oc = SCAP; SCAP = SCAP ? SCAP * 2 : 1 << 12; SEEN = calloc(SCAP, 8); SUSED = 0;
    for (u32 i = 0; i < oc; i++) if (old[i] && old[i] != ~0ull) see_raw(old[i] - 1);
    free(old);
  }
  see_raw(k); trail(8, 0, k);
}
static void unsee(uint64_t k) {
  for (u32 h = (u32)(k * 0x9E3779B97F4A7C15ull >> 32) & (SCAP - 1); SEEN[h]; h = (h + 1) & (SCAP - 1)) if (SEEN[h] == k + 1) { SEEN[h] = ~0ull; return; }
}

static void examine(u32 c) {
  if (C[c].open) return;
  u32 s = C[c].sym;
  if (!SY[s].defined && SY[s].ac && !SY[s].idem) cancel(c);
  if (!SY[s].defined && ac_known(c)) {
    u32 r = find(c);
    if (C[r].value == NONE) { trail(2, r, NONE); C[r].value = c; u32 m = r; do { queue(m); m = C[m].next; } while (m != r);
      for (u32 i = 0; i < C[r].nuses; i++) { reread(C[r].uses[i]); queue(C[r].uses[i]); } drain(); }
    else if (C[r].value != c) {
      u32 w = C[r].value;
      if (C[w].sym != C[c].sym || C[w].n != C[c].n) { if (!EMPTY) { trail(5, 0, 0); EMPTY = 1; } return; }
      if (!SY[s].ac) { for (u32 k = 0; k < C[c].n; k++) pend(C[c].arg[k], C[w].arg[k]); merge(c, w); }
    }
  }
  for (u32 a = 0; a < SY[s].nanc && !EMPTY; a++) {
    u32 code = SY[s].anc[a], di = code >> 4, d = DECL[di]; int which = (int)(code & 15) - 1;
    if (which < 0) {                                                  /* an instance of the left side */
      if (C[c].fired >> di & 1) continue;
      Env e; memset(&e, 0, sizeof e); Env got; int ok = 0;
      int done(Env *ee, void *cc) { (void)cc; got = *ee; ok = 1; return 1; }
      int prem(Env *ee, void *cc) { (void)cc; return premises(d, 0, -1, ee, done, 0); }
      int matched = match_cell(d_lhs(d), c, &e, prem, 0);
      if (DEBUG) { printf("  ? [%d] ", DLINE[di]); show(c, 0); printf("  %s\n", ok ? "holds" : "no"); }
      if (!matched || !ok) continue;
      trail(7, c, C[c].fired); C[c].fired |= 1ull << di;
      fold_with(di, c, &got);
    } else {                                                          /* an instance of a premise, holding */
      u32 pr = d_prem(d, (u32)which);
      if (!C[C[pr].arg[1]].open && find(C[pr].arg[1]) != find(c)) continue;          /* not holding yet */
      uint64_t key = (uint64_t)c << 12 | code;
      if (seen(key)) continue;                                        /* this instance, once */
      see(key);
      Env e; memset(&e, 0, sizeof e);
      int after(Env *ee, void *cc) {
        (void)cc;
        int done(Env *e3, void *c3) {
          (void)c3; u32 target = build(d_lhs(d), e3, 0);
          if (target != NONE) fold_with(di, target, e3);
          return 0;
        }
        u32 t = build(C[pr].arg[1], ee, 0);
        if (t == NONE || find(t) != find(c)) return 0;
        return premises(d, 0, which, ee, done, 0);
      }
      match_cell(C[pr].arg[0], c, &e, after, 0);
    }
  }
}
static void propagate(void) { while (NQ && !EMPTY) { u32 c = Q[--NQ]; C[c].queued = 0; examine(c); } }

/* ---- cases --------------------------------------------------------------------------------------------------- */
static void restore(u32 mark, u32 cells) {
  while (NTR > mark) {
    Tr t = TR[--NTR];
    switch (t.kind) {
      case 0: C[t.cell].parent = (u32)t.old; break;
      case 1: C[t.cell].size = (u32)t.old; break;
      case 2: C[t.cell].value = (u32)t.old; break;
      case 3: C[t.cell].nuses = (u32)t.old; break;
      case 4: C[t.cell].next = (u32)t.old; break;
      case 5: EMPTY = 0; break;
      case 6: C[t.cell].how = (u32)t.old; break;
      case 7: C[t.cell].fired = t.old; break;
      case 8: unsee(t.old); break;
    }
  }
  for (u32 c = cells; c < NC; c++) free(C[c].arg), free(C[c].uses);
  NC = cells;
  for (u32 i = 0; i < NQ; i++) if (Q[i] < NC) C[Q[i]].queued = 0;
  NQ = 0; NPEND = 0; rebuild_table();
}
static u32 *CASEV, NCASEV; static uint64_t CASES, EMPTIES, SHARED;
static u32 *CONS, NCONS;
typedef struct { uint64_t a, b; } Key;
static Key *EMPTYSET; static u32 ECAP, EUSED;
static u32 name_of(u32 c) { u32 r = find(c), m = r, best = r; do { if (m < best) best = m; m = C[m].next; } while (m != r); return best; }
static int cmpk(const void *x, const void *y) { const Key *a = x, *b = y; return a->a < b->a ? -1 : a->a > b->a ? 1 : a->b < b->b ? -1 : a->b > b->b; }
/* what a case leaves of the constraints: each one no true part satisfies, as its parts not yet a constructor */
static Key what_remains(void) {
  Key *cl = malloc((NCONS + 1) * sizeof *cl); u32 m = 0, T = sym("true");
  for (u32 i = 0; i < NCONS; i++) {
    u32 c = CONS[i], lit[64], k = 0; int sat = 0;
    for (u32 j = 0; j < C[c].n && !sat; j++) {
      u32 v = val(C[c].arg[j]);
      if (v == NONE) { if (k < 64) lit[k++] = name_of(C[c].arg[j]); }
      else if (C[v].sym == T) sat = 1;
    }
    if (sat) continue;
    qsort(lit, k, 4, cmpu);
    Key h = { 0x243F6A8885A308D3ull, 0x13198A2E03707344ull };
    for (u32 j = 0; j < k; j++) { h.a = (h.a ^ lit[j]) * 0x100000001B3ull; h.b = (h.b + lit[j] + 1) * 0x9E3779B97F4A7C15ull; h.b ^= h.b >> 29; }
    cl[m++] = h;
  }
  qsort(cl, m, sizeof *cl, cmpk);
  Key r = { 0xA4093822299F31D0ull, 0x082EFA98EC4E6C89ull }, prev = { 0, 0 };
  for (u32 i = 0; i < m; i++) {
    if (i && cl[i].a == prev.a && cl[i].b == prev.b) continue;
    prev = cl[i]; r.a = (r.a ^ cl[i].a) * 0x100000001B3ull; r.b = (r.b ^ cl[i].b) * 0xC2B2AE3D27D4EB4Full; r.b ^= r.b >> 31;
  }
  free(cl); return r;
}
static int known_empty(Key k) {
  if (!ECAP) return 0;
  for (u32 h = (u32)k.a & (ECAP - 1); EMPTYSET[h].a | EMPTYSET[h].b; h = (h + 1) & (ECAP - 1))
    if (EMPTYSET[h].a == k.a && EMPTYSET[h].b == k.b) return 1;
  return 0;
}
static void keep_empty(Key k) {
  if (2 * (EUSED + 1) >= ECAP) {
    Key *old = EMPTYSET; u32 oc = ECAP; ECAP = ECAP ? ECAP * 2 : 1 << 12; EMPTYSET = calloc(ECAP, sizeof *EMPTYSET); EUSED = 0;
    for (u32 i = 0; i < oc; i++) if (old[i].a | old[i].b) keep_empty(old[i]);
    free(old);
  }
  u32 h = (u32)k.a & (ECAP - 1); while (EMPTYSET[h].a | EMPTYSET[h].b) h = (h + 1) & (ECAP - 1);
  EMPTYSET[h] = k; EUSED++;
}
static int cases(void) {
  propagate();
  if (EMPTY) { EMPTIES++; return 0; }
  u32 v = NONE; for (u32 i = 0; i < NCASEV; i++) if (val(CASEV[i]) == NONE) { v = CASEV[i]; break; }
  if (v == NONE) return 1;
  Key k = what_remains();
  if (known_empty(k)) { SHARED++; return 0; }
  Sym *s = &SY[C[v].sym];
  for (u32 j = 0; j < s->ncases; j++) {
    u32 mark = NTR, cells = NC; INCASE++;
    CASES++; merge(v, construct(s->cases[j], 0, 0, 1));
    if (cases()) return 1;
    restore(mark, cells); INCASE--;
  }
  keep_empty(k);
  return 0;
}

/* ---- reading: the files become cells ----------------------------------------------------------------------- */
static const char *S; static size_t P; static int LINE;
static void ws(void) {
  for (;;) {
    while (isspace((unsigned char)S[P])) { if (S[P] == '\n') LINE++; P++; }
    if (S[P] == '/' && S[P + 1] == '/') { while (S[P] && S[P] != '\n') P++; continue; }
    return;
  }
}
static char *word(void) {
  ws(); size_t s = P; while (isalnum((unsigned char)S[P]) || S[P] == '_') P++;
  if (s == P) { fprintf(stderr, "hyper: expected a name at line %d\n", LINE); exit(2); }
  char *w = malloc(P - s + 1); memcpy(w, S + s, P - s); w[P - s] = 0; return w;
}
static int SCOPE;                                                   /* a variable is its declaration's own */
static u32 cellp(void) {
  char *name = word();
  if (isupper((unsigned char)name[0])) {
    char nm[256]; int rest = S[P] == '*'; if (rest) P++;
    snprintf(nm, sizeof nm, "%s'%d", name, SCOPE);
    u32 s = sym(nm); SY[s].var = 1; SY[s].rest = (uint8_t)rest;
    return construct(s, 0, 0, 1);
  }
  u32 s = sym(name), a[64], n = 0; ws();
  if (S[P] == '(') {
    P++;
    for (;;) {
      ws(); if (S[P] == ')') { P++; break; }
      u32 x = cellp();
      if (S[P] == '*') { P++; x = construct(S_EACH, 1, &x, 1); }        /* at each part */
      a[n++] = x; ws(); if (S[P] == ',') P++;
    }
  }
  return construct(s, n, a, 1);
}
static int keyword(const char *k) { ws(); size_t n = strlen(k); if (!strncmp(S + P, k, n) && isspace((unsigned char)S[P + n])) { P += n; return 1; } return 0; }
static void expect(char c) { ws(); if (S[P] != c) { fprintf(stderr, "hyper: expected '%c' at line %d\n", c, LINE); exit(2); } P++; }
static void read_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(1); }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = malloc((size_t)len + 1); if (fread(src, 1, (size_t)len, f) != (size_t)len) { perror(path); exit(1); }
  src[len] = 0; fclose(f);
  S = src; P = 0; LINE = 1;
  for (ws(); S[P]; ws()) {
    if (keyword("ac")) { u32 s = sym(word()); SY[s].ac = 1; expect(';'); continue; }
    if (keyword("idem")) { u32 s = sym(word()); SY[s].idem = 1; expect(';'); continue; }
    if (keyword("unit")) { u32 s = sym(word()), e = sym(word()); SY[s].unit = e; expect(';'); continue; }
    size_t save = P; int sl = LINE; char *w = word(); ws();
    if (keyword("in")) {
      u32 s = sym(w); SY[s].defined = 1;
      for (ws(); S[P] != ';'; ws()) { u32 k = sym(word()); SY[s].cases = realloc(SY[s].cases, (SY[s].ncases + 1) * 4ul); SY[s].cases[SY[s].ncases++] = k; }
      expect(';'); continue;
    }
    P = save; LINE = sl; SCOPE++;
    int line = LINE;
    u32 parts[16], np = 0, l = cellp(); expect('='); u32 r = cellp();
    u32 lr[2] = { l, r }; parts[np++] = construct(S_EQ, 2, lr, 1);
    if (keyword("when")) for (;;) {
      u32 p = cellp(); ws(); u32 kind = S_EQ;
      if (S[P] == '#') { P++; kind = S_APART; } else expect('=');
      u32 q = cellp(), pq[2] = { p, q }; parts[np++] = construct(kind, 2, pq, 1);
      ws(); if (S[P] == ',') { P++; continue; } break;
    }
    expect(';');
    u32 d = np == 1 ? parts[0] : construct(S_WHEN, np, parts, 1);
    DECL = realloc(DECL, (NDECL + 1) * 4ul); DLINE = realloc(DLINE, (NDECL + 1) * sizeof *DLINE);
    DUSED = realloc(DUSED, (NDECL + 1) * sizeof *DUSED);
    DECL[NDECL] = d; DLINE[NDECL] = line; DUSED[NDECL] = 0; NDECL++;
    if (NDECL > 64) { fprintf(stderr, "hyper: more than 64 declarations\n"); exit(2); }
  }
}
/* each symbol reaches the declarations whose left side, or a premise's left side, it heads */
static void anchors(void) {
  for (u32 i = 0; i < NDECL; i++) {
    u32 d = DECL[i], l = d_lhs(d);
    if (!is_var(l)) {
      Sym *s = &SY[C[l].sym]; s->defined = 1;
      s->anc = realloc(s->anc, (s->nanc + 1) * 4ul); s->anc[s->nanc++] = i << 4;
    }
    for (u32 k = 0; k < d_np(d); k++) {
      u32 pr = d_prem(d, k), pl = C[pr].arg[0];
      if (C[pr].sym != S_EQ || is_var(pl) || !C[pl].open) continue;
      Sym *s = &SY[C[pl].sym];
      s->anc = realloc(s->anc, (s->nanc + 1) * 4ul); s->anc[s->nanc++] = i << 4 | (k + 1);
    }
  }
  /* a closed cell built while reading is an instance too; its value is read again now that symbols are known */
  for (u32 c = 0; c < NC; c++) if (!C[c].open) { C[c].value = SY[C[c].sym].defined || !ac_known(c) ? NONE : c; queue(c); }
}

static void show(u32 c, int depth) {
  u32 v = val(c); u32 x = v != NONE ? v : find(c);
  if (depth > 8) { fputs("…", stdout); return; }
  fputs(SY[C[x].sym].name, stdout);
  if (C[x].n) { putchar('('); for (u32 i = 0; i < C[x].n; i++) { if (i) putchar(','); show(C[x].arg[i], depth + 1); } putchar(')'); }
}
static void report_declarations(void) {
  printf("- declarations used (line: times):");
  for (u32 i = 0; i < NDECL; i++) if (DUSED[i]) printf(" %d:%llu", DLINE[i], (unsigned long long)DUSED[i]);
  printf("\n");
}

int main(int argc, char **argv) {
  { struct rlimit rl; if (!getrlimit(RLIMIT_STACK, &rl)) { rl.rlim_cur = rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }
  if (argc < 3) { fprintf(stderr, "usage: hyper FILE… NUMBERS|FORMULA.cnf\n"); return 1; }
  TCAP = 1 << 16; TAB = calloc(TCAP, 4); TRACE = getenv("HYPER_TRACE") != 0; DEBUG = getenv("HYPER_DEBUG") != 0;
  S_EQ = sym("="); S_WHEN = sym("when"); S_APART = sym("#"); S_EACH = S_EACH_ = sym("each");
  const char *in = argv[argc - 1]; size_t il = strlen(in);
  int cnf = il > 4 && !strcmp(in + il - 4, ".cnf");
  u32 T = 0, bools[2]; u32 nv = 0;
  FILE *g = fopen(in, "r"); if (!g) { perror(in); return 1; }
  if (cnf) {                                                        /* the variables' cases, before the files */
    char line[1 << 16];
    while (fgets(line, sizeof line, g)) if (line[0] == 'p') { sscanf(line, "p cnf %u", &nv); break; }
    bools[0] = sym("true"); bools[1] = sym("false");
    for (u32 i = 1; i <= nv; i++) { char nm[32]; snprintf(nm, sizeof nm, "x%u", i); u32 s = sym(nm); SY[s].cases = bools; SY[s].ncases = 2; SY[s].defined = 1; }
  }
  for (int i = 1; i < argc - 1; i++) read_file(argv[i]);
  if (!cnf) { u32 s = sym("input"); SY[s].defined = 1; }             /* the data is an identity too */
  anchors();
  if (cnf) {
    T = atom("true"); atom("false");
    CASEV = malloc((nv + 1) * 4ul);
    for (u32 i = 1; i <= nv; i++) { char nm[32]; snprintf(nm, sizeof nm, "x%u", i); CASEV[NCASEV++] = atom(nm); }
    char line[1 << 16]; u32 ncl = 0, lits[4096], nl = 0; int *cl = 0; u32 csz = 0, ccap = 0;
    u32 OR = sym("or"), NEG = sym("neg");
    while (fgets(line, sizeof line, g)) {
      if (line[0] == 'c' || line[0] == '%' || line[0] == 'p') continue;
      for (char *t = strtok(line, " \t\n"); t; t = strtok(0, " \t\n")) {
        int l = atoi(t);
        if (csz == ccap) { ccap = ccap ? ccap * 2 : 1024; cl = realloc(cl, ccap * sizeof *cl); } cl[csz++] = l;
        if (l == 0) { u32 c = construct(OR, nl, lits, 1); CONS = realloc(CONS, (NCONS + 1) * 4ul); CONS[NCONS++] = c; merge(c, T); ncl++; nl = 0; continue; }
        u32 x = CASEV[(l > 0 ? l : -l) - 1]; lits[nl++] = l > 0 ? x : construct(NEG, 1, &x, 1);
      }
    }
    fclose(g);
    int sat = cases(), ok = 1;
    if (sat) {
      int any = 0;
      for (u32 i = 0; i < csz; i++) {
        int l = cl[i]; if (l == 0) { if (!any) ok = 0; any = 0; continue; }
        u32 v = val(CASEV[(l > 0 ? l : -l) - 1]); int b = v != NONE && C[v].sym == sym("true");
        if ((l > 0) == b) any = 1;
      }
    }
    printf("- variables: %u\n- clauses: %u\n- %s%s\n- cases folded: %llu\n- empty cases: %llu\n- remainders already empty: %llu\n- folds: %llu\n- cells: %u\n",
           nv, ncl, sat ? "satisfiable" : "unsatisfiable", sat ? (ok ? " (the case satisfies every clause)" : " (THE CASE FAILS A CLAUSE)") : "",
           (unsigned long long)CASES, (unsigned long long)EMPTIES, (unsigned long long)SHARED, (unsigned long long)FOLDS, NC);
    report_declarations();
    return 0;
  }
  long long v; u32 n = 0, cap = 0, *el = 0; long long *vals = 0;
  u32 SUC = sym("suc"), ELEM = sym("elem"), CONSS = sym("cons"), zero = atom("zero");
  while (fscanf(g, "%lld", &v) == 1) {
    if (n == cap) { cap = cap ? cap * 2 : 64; el = realloc(el, cap * 4ul); vals = realloc(vals, cap * sizeof *vals); }
    u32 x = zero; for (long long k = 0; k < v; k++) x = construct(SUC, 1, &x, 1);
    el[n] = construct(ELEM, 1, &x, 1); vals[n] = v; n++;
  }
  fclose(g);
  u32 list = atom("nil");
  for (u32 i = n; i-- > 0;) { u32 a2[2] = { el[i], list }; list = construct(CONSS, 2, a2, 1); }
  merge(atom("input"), list);
  u32 m = atom("main");
  propagate();
  u32 SN = sym("nil"), k = 0; int ordered = 1; long long prev = -1;
  u32 t = val(m);
  while (t != NONE && C[t].sym == CONSS) {
    u32 h = find(C[t].arg[0]); long long hv = -1;
    for (u32 i = 0; i < n; i++) if (find(el[i]) == h) { hv = vals[i]; break; }
    if (hv < prev) ordered = 0;
    if (n <= 40) printf("%s%lld", k ? " " : "", hv);
    prev = hv; k++; t = val(C[t].arg[1]);
  }
  if (n <= 40) printf("\n");
  if (getenv("HYPER_SHOW")) { show(m, 0); putchar('\n'); }
  /* the relations between two values, and the declaration each folded by first */
  u32 LE = sym("le"), rel = 0, *by = calloc(NDECL + 1, 4);
  uint8_t *isel = calloc(NC, 1); for (u32 i = 0; i < n; i++) isel[find(el[i])] = 1;
  for (u32 c = 0; c < NC; c++)
    if (C[c].sym == LE && C[c].n == 2 && !C[c].open && isel[find(C[c].arg[0])] && isel[find(C[c].arg[1])] && find(C[c].arg[0]) != find(C[c].arg[1])) {
      rel++; by[C[c].how == NONE ? NDECL : C[c].how]++;
    }
  double lg = 0; for (u32 i = 2; i <= n; i++) lg += log2((double)i);
  printf("- n: %u\n- presented: %u\n- ordered: %s\n- log2 n!: %.1f\n- relations le(a, b) between two values: %u (n(n-1) = %u; first folded by line:",
         n, k, ordered && k == n && t != NONE && C[t].sym == SN ? "yes" : "NO", lg, rel, n * (n - 1));
  for (u32 i = 0; i <= NDECL; i++) if (by[i]) printf(" %d:%u", i < NDECL ? DLINE[i] : -1, by[i]);
  printf(")\n- folds: %llu\n- cells: %u%s\n", (unsigned long long)FOLDS, NC, EMPTY ? "\n- EMPTY: two constructors in one class" : "");
  report_declarations();
  return 0;
}

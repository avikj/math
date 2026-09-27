/* hyper.c: Hyperactive.
 *
 * One element, the identification; one operation, folding.
 *
 *   1. A cell is its construction: a symbol and its parts, the parts read through the folds.  Building a
 *      construction that already exists gives that cell.
 *   2. Identities are declarations, `lhs = rhs;` or `lhs = rhs when p = q, …;`.  An identity holds at every
 *      instance of its shape, so it is instantiated at each cell of that shape: at the cell of its left side
 *      (the first such identity in the files whose premises hold), and at a cell of a premise's left side once
 *      that premise holds.  Instantiated from a premise it folds
 *      the left side only where that cell already exists: it identifies, it does not build.
 *   3. Folding: cells an identity makes equal are one class, and everything built on them is read again, so
 *      a construction that now coincides with another is that other.
 *   4. Cases: a symbol declared `S in a b …;` ranges over those constructors.  Each case is folded on its
 *      own; a case in which two different constructors are one class is empty.  What a case leaves of the
 *      declarations is one construction wherever it recurs, so a remainder found empty stays empty.
 *   5. The result is what remains when nothing more folds.
 *
 * A symbol that is the top of no identity's left side, and has no cases, is a constructor.  Two constructors
 * in one class with the same symbol have their parts identified; with different symbols the case is empty.
 *
 * Declarations:
 *   ac f;  idem f;  unit f e;    how f's parts are presented: flat and unordered; once each; without e
 *   S in a b …;                  the cases of a symbol
 *   lhs = rhs [when p = q, p # q, …];
 * In a pattern an uppercase name is a variable; R* is the remaining parts of an ac construction; p # q holds
 * when p and q are classes of different constructors.
 *
 * usage: hyper FILE… [NUMBERS | FORMULA.cnf]
 *   NUMBERS: each value v is the construction elem(suc(…suc(zero))) (v times).  The files see the positions
 *            p0 … p(n-1), end, with next(pi) = p(i+1); the array `input` with at(input, pi) = the i-th value;
 *            and `set`, the union of the values.  The result is the class of `main`, read as cons/nil.
 *   FORMULA.cnf: DIMACS.  Variables x1 … xn are declared `in true false`; each clause or(…) is folded with true. */
#include <ctype.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

#define NONE 0xFFFFFFFFu
typedef uint32_t u32;

/* ---- symbols -------------------------------------------------------------------------------------------- */
typedef struct { char *name; uint8_t ac, idem, defined; u32 unit, *cases, ncases, *anc, nanc; } Sym;
static Sym *SY; static u32 NSY;
static u32 sym(const char *s) {
  for (u32 i = 0; i < NSY; i++) if (!strcmp(SY[i].name, s)) return i;
  SY = realloc(SY, (NSY + 1) * sizeof *SY); memset(&SY[NSY], 0, sizeof *SY);
  SY[NSY].name = strdup(s); SY[NSY].unit = NONE;
  return NSY++;
}

/* ---- the store -------------------------------------------------------------------------------------------- */
typedef struct { u32 sym, n, *arg, parent, size, value, *uses, nuses, cuses, next, how; uint8_t fired, queued; } Cell;
static Cell *C; static u32 NC, CCAP;
static int EMPTY;                                                /* this case has two constructors in one class */
static uint64_t FOLDS;

/* everything a case changes, so the next case starts from the same store */
typedef struct { u32 kind, cell, old; } Tr;
static Tr *TR; static u32 NTR, CTR, INCASE;
static void trail(u32 kind, u32 cell, u32 old) {
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
  if (2 * (TUSED + 1) >= TCAP) {                                  /* grow: every cell under its present key */
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

static u32 *Q, NQ, CQ;                                            /* cells to be read again */
static void queue(u32 c) {
  if (C[c].queued) return;
  C[c].queued = 1;
  if (NQ == CQ) { CQ = CQ ? CQ * 2 : 4096; Q = realloc(Q, CQ * 4ul); }
  Q[NQ++] = c;
}

static int cmpu(const void *a, const void *b) { u32 x = *(const u32 *)a, y = *(const u32 *)b; return x < y ? -1 : x > y; }

/* The parts of a construction as its declarations present them: an ac construction's parts flat (a part
   whose class is the same construction contributes its parts) and unordered, once each if idem, without
   the unit; one part is that part, none is the unit.  Returns the class the construction is, or NONE. */
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
  if (SY[s].ac && m == 1) return a[0];
  return NONE;
}

static u32 construct(u32 s, u32 n, const u32 *args, int create);
static u32 unit_cell(u32 s, int create) { return construct(SY[s].unit, 0, 0, create); }

/* item 1: the construction, once */
static u32 construct(u32 s, u32 n, const u32 *args, int create) {
  u32 *a, m; u32 one = present(s, n, args, &a, &m);
  if (one != NONE) { free(a); return one; }
  if (SY[s].ac && m == 0 && SY[s].unit != NONE) { free(a); return unit_cell(s, create); }
  u32 e = lookup(s, m, a);
  if (e != NONE) { free(a); return find(e); }
  if (!create) { free(a); return NONE; }
  if (NC == CCAP) { CCAP = CCAP ? CCAP * 2 : 1 << 16; C = realloc(C, CCAP * sizeof *C); }
  u32 c = NC++; Cell *x = &C[c]; memset(x, 0, sizeof *x);
  x->sym = s; x->n = m; x->arg = a; x->parent = c; x->size = 1; x->next = c; x->how = NONE;
  x->value = SY[s].defined ? NONE : c;                               /* a constructor is its own value */
  for (u32 i = 0; i < m; i++) add_use(a[i], c);
  insert_key(c, m, a);
  queue(c);
  return c;
}

/* ---- item 3: folding ---------------------------------------------------------------------------------------- */
static u32 *PEND, NPEND, CPEND;
static void pend(u32 a, u32 b) {
  if (NPEND + 2 > CPEND) { CPEND = CPEND ? CPEND * 2 : 1024; PEND = realloc(PEND, CPEND * 4ul); }
  PEND[NPEND++] = a; PEND[NPEND++] = b;
}
/* a cell whose parts' classes changed, read again: the construction it now is */
static void reread(u32 u) {
  u32 *a, m; u32 one = present(C[u].sym, C[u].n, C[u].arg, &a, &m);
  if (one != NONE) { free(a); if (find(one) != find(u)) pend(u, one); return; }
  if (SY[C[u].sym].ac && m == 0 && SY[C[u].sym].unit != NONE) { free(a); pend(u, unit_cell(C[u].sym, 1)); return; }
  u32 e = lookup(C[u].sym, m, a);
  if (e == NONE) {
    if (m == C[u].n) insert_key(u, m, a);                          /* the same construction, under its new key */
    else { u32 r = construct(C[u].sym, m, a, 1); pend(u, r); }     /* presented anew: fewer parts */
  } else if (find(e) != find(u)) pend(u, e);
  free(a);
}
static void merge(u32 a, u32 b) {
  pend(a, b);
  while (NPEND) {
    u32 y = find(PEND[--NPEND]), x = find(PEND[--NPEND]);
    if (x == y) continue;
    FOLDS++;
    if (C[x].size > C[y].size) { u32 t = x; x = y; y = t; }          /* x joins y */
    u32 vx = C[x].value, vy = C[y].value, ny = C[y].nuses;
    trail(0, x, C[x].parent); C[x].parent = y;
    trail(1, y, C[y].size); C[y].size += C[x].size;
    trail(4, x, C[x].next); trail(4, y, C[y].next);
    { u32 t = C[x].next; C[x].next = C[y].next; C[y].next = t; }     /* the members are one list */
    if (vy == NONE && vx != NONE) { trail(2, y, vy); C[y].value = vx; }
    if (vx != NONE && vy != NONE && vx != vy) {
      if (C[vx].sym != C[vy].sym || C[vx].n != C[vy].n) { if (!EMPTY) { trail(5, 0, 0); EMPTY = 1; } }
      else for (u32 k = 0; k < C[vx].n; k++) pend(C[vx].arg[k], C[vy].arg[k]);
    }
    for (u32 i = 0; i < C[x].nuses; i++) add_use(y, C[x].uses[i]);
    for (u32 i = 0; i < C[x].nuses; i++) { reread(C[x].uses[i]); queue(C[x].uses[i]); }
    if (vy == NONE && vx != NONE) for (u32 i = 0; i < ny; i++) { reread(C[y].uses[i]); queue(C[y].uses[i]); }
    /* the members whose class now holds more: premises about them may now hold */
    u32 m = x; do { queue(m); m = C[m].next; } while (m != x);
    if (vy == NONE && vx != NONE) { u32 k = y; do { queue(k); k = C[k].next; } while (k != y); }
  }
}

/* ---- item 2: identities --------------------------------------------------------------------------------------- */
typedef struct Pat { int var, rest; u32 sym, n; struct Pat *arg[8]; } Pat;
typedef struct { Pat *l, *r; int apart; } Prem;
typedef struct { Pat *lhs, *rhs; Prem pr[8]; int np, line; uint64_t used; } Id;
static Id *IDS; static u32 NID;

typedef struct { u32 bind[32]; uint8_t bound[32], rest[32]; } Env;

static u32 build(Pat *p, Env *e, int create) {
  if (p->var >= 0) return e->bind[p->var];
  u32 a[64], m = 0;
  for (u32 i = 0; i < p->n; i++) {
    Pat *q = p->arg[i];
    if (q->var >= 0 && e->rest[q->var]) {                          /* the remaining parts, placed as parts */
      u32 r = find(e->bind[q->var]), v = C[r].value;
      if (v != NONE && C[v].sym == p->sym) { for (u32 k = 0; k < C[v].n && m < 64; k++) a[m++] = C[v].arg[k]; continue; }
      if (SY[p->sym].unit != NONE && v != NONE && C[v].sym == SY[p->sym].unit) continue;
      a[m++] = r; continue;
    }
    u32 x = build(q, e, create); if (x == NONE) return NONE;
    a[m++] = x;
  }
  return construct(p->sym, m, a, create);
}

/* every way a pattern meets a class; k is called on each and stops at the first that succeeds */
typedef int (*K)(Env *, void *);
static int match_cls(Pat *p, u32 cls, Env *e, K k, void *ctx);
static int match_parts(Pat *p, const u32 *parts, u32 n, uint64_t used, u32 i, Env *e, K k, void *ctx) {
  if (i == p->n) return (n == 0 || used == (n >= 64 ? ~0ull : (1ull << n) - 1)) ? k(e, ctx) : 0;
  Pat *q = p->arg[i];
  if (q->rest) {
    u32 rem[64], m = 0; for (u32 j = 0; j < n; j++) if (!(used >> j & 1)) rem[m++] = parts[j];
    u32 r = construct(p->sym, m, rem, 1);
    if (e->bound[q->var]) return find(e->bind[q->var]) == find(r) ? k(e, ctx) : 0;
    Env e2 = *e; e2.bind[q->var] = r; e2.bound[q->var] = 1; e2.rest[q->var] = 1;
    return k(&e2, ctx);
  }
  for (u32 j = 0; j < n; j++) {
    if (used >> j & 1) continue;
    if (!SY[p->sym].ac && j != i) continue;                         /* positional unless ac */
    int inner(Env *ee, void *cc) { (void)cc; return match_parts(p, parts, n, used | 1ull << j, i + 1, ee, k, ctx); }
    if (match_cls(q, parts[j], e, inner, 0)) return 1;
  }
  return 0;
}
static int shape_fits(Pat *p, u32 n) {
  int hasrest = p->n && p->arg[p->n - 1]->rest;
  return n <= 64 && (hasrest ? n + 1 >= p->n : n == p->n);
}
static int match_cell(Pat *p, u32 c, Env *e, K k, void *ctx) {    /* the pattern at the cell's own construction */
  if (p->var >= 0) {
    if (!e->bound[p->var]) { Env e2 = *e; e2.bind[p->var] = find(c); e2.bound[p->var] = 1; return k(&e2, ctx); }
    return find(e->bind[p->var]) == find(c) ? k(e, ctx) : 0;
  }
  if (C[c].sym != p->sym || !shape_fits(p, C[c].n)) return 0;
  return match_parts(p, C[c].arg, C[c].n, 0, 0, e, k, ctx);
}
static int match_cls(Pat *p, u32 cls, Env *e, K k, void *ctx) {   /* the pattern at any construction in the class */
  cls = find(cls);
  if (p->var >= 0) return match_cell(p, cls, e, k, ctx);
  u32 v = C[cls].value;
  if (v != NONE) return match_cell(p, v, e, k, ctx);
  u32 m = cls; do { if (C[m].sym == p->sym && match_cell(p, m, e, k, ctx)) return 1; m = C[m].next; } while (m != cls);
  return 0;
}

/* two classes of different constructions: different constructors, or the same one with parts apart */
static int apart(u32 a, u32 b) {
  u32 x = val(a), y = val(b);
  if (x == NONE || y == NONE || find(x) == find(y)) return 0;
  if (C[x].sym != C[y].sym || C[x].n != C[y].n) return 1;
  for (u32 k = 0; k < C[x].n; k++) if (apart(C[x].arg[k], C[y].arg[k])) return 1;
  return 0;
}
/* the premises other than `skip`, with their variables: a premise whose left side has an unbound variable
   meets the cells already built on a bound part */
static int premises(Id *id, int i, int skip, Env *e, K k, void *ctx) {
  if (i == id->np) return k(e, ctx);
  if (i == skip) return premises(id, i + 1, skip, e, k, ctx);
  Prem *pr = &id->pr[i];
  if (pr->apart) {
    u32 a = build(pr->l, e, 0), b = build(pr->r, e, 0);
    return a != NONE && b != NONE && apart(a, b) && premises(id, i + 1, skip, e, k, ctx);
  }
  Pat *p = pr->l;
  int unbound = 0, anchor = -1;
  for (u32 j = 0; j < p->n; j++) {
    Pat *q = p->arg[j];
    if (q->var >= 0 && !e->bound[q->var]) unbound = 1;
    else if (q->var >= 0 && anchor < 0) anchor = (int)j;
  }
  if (!unbound) {
    u32 c = build(p, e, 0), t = build(pr->r, e, 0);
    return c != NONE && t != NONE && find(c) == find(t) && premises(id, i + 1, skip, e, k, ctx);
  }
  if (anchor < 0) return 0;
  u32 cls = find(e->bind[p->arg[anchor]->var]);
  for (u32 u = 0; u < C[cls].nuses; u++) {
    u32 cell = C[cls].uses[u];
    if (C[cell].sym != p->sym) continue;
    int then(Env *ee, void *cc) {
      (void)cc; u32 t = build(pr->r, ee, 0);
      return t != NONE && find(t) == find(cell) && premises(id, i + 1, skip, ee, k, ctx);
    }
    if (match_cell(p, cell, e, then, 0)) return 1;
  }
  return 0;
}

static int TRACE; static FILE *DECISIONS;
static void show_to(FILE *f, u32 c);
static void show(u32 c, int depth);
static void fold_with(Id *id, u32 target, Env *e) {
  u32 r = build(id->rhs, e, 1);
  if (find(r) == find(target)) return;
  id->used++;
  if (TRACE) { printf("  [%d] ", id->line); show(target, 0); printf("  =  "); show(r, 0); printf("\n"); }
  if (C[target].how == NONE) { trail(6, target, NONE); C[target].how = (u32)(id - IDS); }
  if (DECISIONS && C[target].n == 2 && !strcmp(SY[C[target].sym].name, "le")) {   /* the order relations, as they fold */
    fprintf(DECISIONS, "%d ", id->line); show_to(DECISIONS, C[target].arg[0]); fputc(' ', DECISIONS); show_to(DECISIONS, C[target].arg[1]); fputc('\n', DECISIONS);
  }
  merge(target, r);
}

/* a cell read again: the first identity whose left side it is and whose premises hold; then each identity
   with a premise it is the left side of, which holds */
static void examine(u32 c) {
  u32 s = C[c].sym;
  if (!SY[s].defined) {
    u32 r = find(c);
    if (C[r].value == NONE) { trail(2, r, NONE); C[r].value = c; u32 m = r; do { queue(m); m = C[m].next; } while (m != r);
      for (u32 i = 0; i < C[r].nuses; i++) { reread(C[r].uses[i]); queue(C[r].uses[i]); } }
    else if (C[r].value != c) {                                       /* two constructors in one class */
      u32 w = C[r].value;
      if (C[w].sym != C[c].sym || C[w].n != C[c].n) { if (!EMPTY) { trail(5, 0, 0); EMPTY = 1; } return; }
      for (u32 k = 0; k < C[c].n; k++) pend(C[c].arg[k], C[w].arg[k]);
      merge(c, w);
    }
  }
  for (u32 a = 0; a < SY[s].nanc && !EMPTY; a++) {
    u32 code = SY[s].anc[a]; Id *id = &IDS[code >> 4]; int which = (int)(code & 15) - 1;
    if (which < 0) {                                                  /* the cell of the left side */
      if (C[c].fired) continue;
      Env e; memset(&e, 0, sizeof e); Env got; int ok = 0;
      int done(Env *ee, void *cc) { (void)cc; got = *ee; ok = 1; return 1; }
      int prem(Env *ee, void *cc) { (void)cc; return premises(id, 0, -1, ee, done, 0); }
      if (!match_cell(id->lhs, c, &e, prem, 0)) continue;
      if (!ok) continue;
      trail(7, c, 0); C[c].fired = 1;
      fold_with(id, c, &got);
    } else {                                                          /* a premise's left side, now holding */
      Prem *pr = &id->pr[which]; if (pr->apart) continue;
      Env e; memset(&e, 0, sizeof e);
      int after(Env *ee, void *cc) {
        (void)cc;
        int done(Env *e3, void *c3) {
          (void)c3;
          u32 target = build(id->lhs, e3, 0);                         /* identifies what exists; builds nothing */
          if (target != NONE) fold_with(id, target, e3);
          return 0;                                                   /* every instance */
        }
        u32 t = build(pr->r, ee, 0);
        if (t == NONE || find(t) != find(c)) return 0;
        return premises(id, 0, which, ee, done, 0);
      }
      match_cell(pr->l, c, &e, after, 0);
    }
  }
}

static void propagate(void) {
  while (NQ && !EMPTY) { u32 c = Q[--NQ]; C[c].queued = 0; examine(c); }
}

/* ---- item 4: cases ------------------------------------------------------------------------------------------------ */
static void restore(u32 mark, u32 cells) {
  while (NTR > mark) {
    Tr t = TR[--NTR];
    switch (t.kind) {
      case 0: C[t.cell].parent = t.old; break;
      case 1: C[t.cell].size = t.old; break;
      case 2: C[t.cell].value = t.old; break;
      case 3: C[t.cell].nuses = t.old; break;
      case 4: C[t.cell].next = t.old; break;
      case 5: EMPTY = 0; break;
      case 6: C[t.cell].how = t.old; break;
      case 7: C[t.cell].fired = 0; break;
    }
  }
  for (u32 c = cells; c < NC; c++) free(C[c].arg), free(C[c].uses);
  NC = cells;
  for (u32 i = 0; i < NQ; i++) if (Q[i] < NC) C[Q[i]].queued = 0;
  NQ = 0; NPEND = 0; rebuild_table();
}
static u32 *CASEV, NCASEV; static uint64_t CASES, EMPTIES, SHARED;
static u32 *CONS, NCONS;                                             /* the cells declared one with true */

/* What a case leaves of the declarations: each constraint that no true part satisfies, as its parts that are
   not yet a constructor.  A class is named by its least member, so the same construction has one name in every
   case.  An empty remainder is one construction wherever it recurs: it is kept past the case. */
typedef struct { uint64_t a, b; } Key;
static Key *EMPTYSET; static u32 ECAP, EUSED;
static u32 name_of(u32 c) { u32 r = find(c), m = r, best = r; do { if (m < best) best = m; m = C[m].next; } while (m != r); return best; }
static int cmpk(const void *x, const void *y) { const Key *a = x, *b = y; return a->a < b->a ? -1 : a->a > b->a ? 1 : a->b < b->b ? -1 : a->b > b->b; }
static Key what_remains(void) {
  Key *cl = malloc((NCONS + 1) * sizeof *cl); u32 m = 0;
  for (u32 i = 0; i < NCONS; i++) {
    u32 c = CONS[i], lit[64], k = 0; int sat = 0;
    for (u32 j = 0; j < C[c].n && !sat; j++) {
      u32 v = val(C[c].arg[j]);
      if (v == NONE) { if (k < 64) lit[k++] = name_of(C[c].arg[j]); }
      else if (!strcmp(SY[C[v].sym].name, "true")) sat = 1;
    }
    if (sat) continue;
    qsort(lit, k, 4, cmpu);
    Key h = { 0x243F6A8885A308D3ull, 0x13198A2E03707344ull };
    for (u32 j = 0; j < k; j++) { h.a = (h.a ^ lit[j]) * 0x100000001B3ull; h.b = (h.b + lit[j] + 1) * 0x9E3779B97F4A7C15ull; h.b ^= h.b >> 29; }
    cl[m++] = h;
  }
  qsort(cl, m, sizeof *cl, cmpk);
  Key r = { 0xA4093822299F31D0ull, 0x082EFA98EC4E6C89ull }; Key prev = { 0, 0 };
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
static int cases(void) {                                             /* 1: a case that is not empty */
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

/* ---- reading ------------------------------------------------------------------------------------------------------ */
static const char *S; static size_t P; static int LINE;
static void ws(void) {
  for (;;) {
    while (isspace((unsigned char)S[P])) { if (S[P] == '\n') LINE++; P++; }
    if (S[P] == '/' && S[P + 1] == '/') { while (S[P] && S[P] != '\n') P++; continue; }
    return;
  }
}
static char *VARS[32]; static int NVARS;
static char *word(void) {
  ws(); size_t s = P; while (isalnum((unsigned char)S[P]) || S[P] == '_') P++;
  if (s == P) { fprintf(stderr, "hyper: expected a name at line %d\n", LINE); exit(2); }
  char *w = malloc(P - s + 1); memcpy(w, S + s, P - s); w[P - s] = 0; return w;
}
static Pat *pat(void) {
  char *name = word(); Pat *p = calloc(1, sizeof *p); p->var = -1;
  if (isupper((unsigned char)name[0])) {
    int i = 0; for (; i < NVARS; i++) if (!strcmp(VARS[i], name)) break;
    if (i == NVARS) VARS[NVARS++] = name;
    p->var = i; if (S[P] == '*') { P++; p->rest = 1; } return p;
  }
  p->sym = sym(name); ws();
  if (S[P] == '(') { P++; for (;;) { ws(); if (S[P] == ')') { P++; break; } p->arg[p->n++] = pat(); ws(); if (S[P] == ',') P++; } }
  return p;
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
    if (keyword("in")) {                                             /* an unknown, not a constructor */
      u32 s = sym(w); SY[s].defined = 1;
      for (ws(); S[P] != ';'; ws()) { u32 k = sym(word()); SY[s].cases = realloc(SY[s].cases, (SY[s].ncases + 1) * 4ul); SY[s].cases[SY[s].ncases++] = k; }
      expect(';'); continue;
    }
    P = save; LINE = sl;
    NVARS = 0; IDS = realloc(IDS, (NID + 1) * sizeof *IDS); Id *id = &IDS[NID]; memset(id, 0, sizeof *id);
    id->line = LINE;
    id->lhs = pat(); expect('='); id->rhs = pat();
    if (keyword("when")) for (;;) {
      Prem *pr = &id->pr[id->np++]; pr->l = pat(); ws();
      if (S[P] == '#') { P++; pr->apart = 1; } else expect('=');
      pr->r = pat(); ws(); if (S[P] == ',') { P++; continue; } break;
    }
    expect(';'); NID++;
  }
}
static void anchors(void) {
  for (u32 i = 0; i < NID; i++) {
    Id *id = &IDS[i];
    if (id->lhs->var < 0) {
      Sym *s = &SY[id->lhs->sym]; s->defined = 1;
      s->anc = realloc(s->anc, (s->nanc + 1) * 4ul); s->anc[s->nanc++] = i << 4;
    }
    for (int k = 0; k < id->np; k++) if (!id->pr[k].apart && id->pr[k].l->var < 0) {
      Sym *s = &SY[id->pr[k].l->sym];
      s->anc = realloc(s->anc, (s->nanc + 1) * 4ul); s->anc[s->nanc++] = i << 4 | (u32)(k + 1);
    }
  }
}

static u32 atom(const char *s) { return construct(sym(s), 0, 0, 1); }
static u32 app(const char *f, u32 n, u32 *a) { return construct(sym(f), n, a, 1); }
static void show(u32 c, int depth) {
  u32 v = val(c); u32 x = v != NONE ? v : find(c);
  if (depth > 8) { fputs("…", stdout); return; }
  fputs(SY[C[x].sym].name, stdout);
  if (C[x].n) { putchar('('); for (u32 i = 0; i < C[x].n; i++) { if (i) putchar(','); show(C[x].arg[i], depth + 1); } putchar(')'); }
}
static void show_to(FILE *f, u32 c) {                               /* a value elem(suc^k zero) as k */
  u32 x = val(c); if (x == NONE || strcmp(SY[C[x].sym].name, "elem")) { fputs("?", f); return; }
  long k = 0; for (u32 y = val(C[x].arg[0]); y != NONE && !strcmp(SY[C[y].sym].name, "suc"); y = val(C[y].arg[0])) k++;
  fprintf(f, "%ld", k);
}
static void report_identities(void) {
  printf("- identities used (line: times):");
  for (u32 i = 0; i < NID; i++) if (IDS[i].used) printf(" %d:%llu", IDS[i].line, (unsigned long long)IDS[i].used);
  printf("\n");
}

int main(int argc, char **argv) {
  { struct rlimit rl; if (!getrlimit(RLIMIT_STACK, &rl)) { rl.rlim_cur = rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }
  if (argc < 3) { fprintf(stderr, "usage: hyper FILE… NUMBERS|FORMULA.cnf\n"); return 1; }
  TCAP = 1 << 16; TAB = calloc(TCAP, 4); TRACE = getenv("HYPER_TRACE") != 0;
  if (getenv("HYPER_DECISIONS")) DECISIONS = fopen(getenv("HYPER_DECISIONS"), "w");
  for (int i = 1; i < argc - 1; i++) read_file(argv[i]);
  const char *in = argv[argc - 1]; size_t il = strlen(in);
  if (il > 4 && !strcmp(in + il - 4, ".cnf")) {
    FILE *g = fopen(in, "r"); if (!g) { perror(in); return 1; }
    u32 bools[2] = { sym("true"), sym("false") };
    char line[1 << 16]; u32 nv = 0, ncl = 0, lits[4096], nl = 0; int *cl = 0; u32 csz = 0, ccap = 0;
    u32 T = NONE;
    while (fgets(line, sizeof line, g)) {
      if (line[0] == 'c' || line[0] == '%') continue;
      if (line[0] == 'p') {
        sscanf(line, "p cnf %u", &nv); CASEV = malloc((nv + 1) * 4ul);
        for (u32 i = 1; i <= nv; i++) { char nm[32]; snprintf(nm, sizeof nm, "x%u", i); u32 s = sym(nm); SY[s].cases = bools; SY[s].ncases = 2; SY[s].defined = 1; }
        anchors(); T = atom("true"); atom("false");
        for (u32 i = 1; i <= nv; i++) { char nm[32]; snprintf(nm, sizeof nm, "x%u", i); CASEV[NCASEV++] = atom(nm); }
        continue;
      }
      for (char *t = strtok(line, " \t\n"); t; t = strtok(0, " \t\n")) {
        int l = atoi(t);
        if (csz == ccap) { ccap = ccap ? ccap * 2 : 1024; cl = realloc(cl, ccap * sizeof *cl); } cl[csz++] = l;
        if (l == 0) { u32 c = app("or", nl, lits); CONS = realloc(CONS, (NCONS + 1) * 4ul); CONS[NCONS++] = c; merge(c, T); ncl++; nl = 0; continue; }
        u32 x = CASEV[(l > 0 ? l : -l) - 1]; lits[nl++] = l > 0 ? x : app("neg", 1, &x);
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
    report_identities();
    return 0;
  }
  { u32 a = sym("next"), b = sym("at"), c = sym("set"); SY[a].defined = SY[b].defined = SY[c].defined = 1; }   /* the data are identities too */
  anchors();
  FILE *g = fopen(in, "r"); if (!g) { perror(in); return 1; }
  long long v; u32 n = 0, cap = 0, *el = 0; long long *vals = 0;
  u32 zero = atom("zero"), SUC = sym("suc"), ELEM = sym("elem");
  while (fscanf(g, "%lld", &v) == 1) {
    if (n == cap) { cap = cap ? cap * 2 : 64; el = realloc(el, cap * 4ul); vals = realloc(vals, cap * sizeof *vals); }
    u32 x = zero; for (long long k = 0; k < v; k++) x = construct(SUC, 1, &x, 1);
    x = construct(ELEM, 1, &x, 1);
    el[n] = x; vals[n] = v; n++;
  }
  fclose(g);
  char nm[32]; u32 *pos = malloc((n + 1) * 4ul), end = atom("end");
  for (u32 i = 0; i < n; i++) { snprintf(nm, sizeof nm, "p%u", i); pos[i] = atom(nm); }
  u32 input = atom("input");
  for (u32 i = 0; i < n; i++) {
    u32 nx = i + 1 < n ? pos[i + 1] : end; merge(app("next", 1, &pos[i]), nx);
    u32 a2[2] = { input, pos[i] }; merge(app("at", 2, a2), el[i]);
  }
  merge(atom("set"), app("union", n, el));
  u32 m = atom("main");
  propagate();
  /* the result: the class of main, read as cons/nil */
  u32 SC = sym("cons"), SN = sym("nil"), k = 0; int ordered = 1; long long prev = -1;
  u32 t = val(m);
  while (t != NONE && C[t].sym == SC) {
    u32 h = find(C[t].arg[0]); long long hv = -1;
    for (u32 i = 0; i < n; i++) if (find(el[i]) == h) { hv = vals[i]; break; }
    if (hv < prev) ordered = 0;
    if (n <= 40) printf("%s%lld", k ? " " : "", hv);
    prev = hv; k++; t = val(C[t].arg[1]);
  }
  if (n <= 40) printf("\n");
  if (getenv("HYPER_SHOW")) { show(m, 0); putchar('\n'); }
  /* the relations between two values that folded, and by which identity each did */
  u32 LE = sym("le"), direct = 0, *byid = calloc(NID + 1, 4);
  uint8_t *isel = calloc(NC, 1); for (u32 i = 0; i < n; i++) isel[find(el[i])] = 1;
  for (u32 c = 0; c < NC; c++)
    if (C[c].sym == LE && C[c].n == 2 && isel[find(C[c].arg[0])] && isel[find(C[c].arg[1])] && find(C[c].arg[0]) != find(C[c].arg[1])) {
      direct++; byid[C[c].how == NONE ? NID : C[c].how]++;
    }
  double lg = 0; for (u32 i = 2; i <= n; i++) lg += log2((double)i);
  printf("- n: %u\n- presented: %u\n- ordered: %s\n- log2 n!: %.1f\n- le between two values: %u (by line:",
         n, k, ordered && k == n && (t != NONE && C[t].sym == SN) ? "yes" : "NO", lg, direct);
  for (u32 i = 0; i <= NID; i++) if (byid[i]) printf(" %d:%u", i < NID ? IDS[i].line : -1, byid[i]);
  printf(")\n- folds: %llu\n- cells: %u%s\n", (unsigned long long)FOLDS, NC, EMPTY ? "\n- EMPTY: two constructors in one class" : "");
  report_identities();
  return 0;
}

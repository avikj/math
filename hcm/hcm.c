/* hcm.c -- the hypercubical interaction machine (MACHINE_SPEC.md).

   One cubical primitive, COMP.  hcomp, coe, fill, path composition, Glue
   composition, univalence, equivalence extension, identity agents and
   annihilation are terms of core.ctt, expanded into COMP and the ordinary
   interactions.  An identity p : (γ : Γ) → Path B L R named in an
   `agent p` line is compiled into its forward and backward programs.

   usage: hcm [-p core.ctt] file.ctt name                                     */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <ctype.h>

static void die(const char *fmt, ...) {
  va_list a; va_start(a, fmt); fprintf(stderr, "error: ");
  vfprintf(stderr, fmt, a); fprintf(stderr, "\n"); va_end(a); exit(1);
}
static void *xmalloc(size_t n) { void *p = malloc(n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xrealloc(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static char *xstrdup(const char *s) { size_t n = strlen(s) + 1; char *d = xmalloc(n); memcpy(d, s, n); return d; }

/* ------------------------------------------------------------------ names */

static char **names; static int nnames, cnames;
static int newname(const char *s) {
  if (nnames == cnames) { cnames = cnames ? 2 * cnames : 64; names = xrealloc(names, cnames * sizeof *names); }
  names[nnames] = xstrdup(s); return nnames++;
}
static int freshname(const char *stem) { char b[64]; snprintf(b, sizeof b, "%s%d", stem, nnames); return newname(b); }

/* ------------------------------------------------- clause sets (antichains)
   A form is an antichain of clauses; a clause is a sorted set of literals.
   Interval literals: name*2 for i, name*2+1 for ~i.
   Face literals:     name*2 for (i = 0), name*2+1 for (i = 1).            */

typedef struct { int n; int *l; } Clause;
typedef struct { int n; Clause *c; } Form;

static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
static Clause clause_make(const int *l, int n) {
  Clause c; c.l = xmalloc(n * sizeof(int)); if (n) memcpy(c.l, l, n * sizeof(int));
  qsort(c.l, n, sizeof(int), cmpint);
  int m = 0; for (int i = 0; i < n; i++) if (m == 0 || c.l[m - 1] != c.l[i]) c.l[m++] = c.l[i];
  c.n = m; return c;
}
static int clause_sub(Clause a, Clause b) { /* a ⊆ b */
  int i = 0, j = 0;
  while (i < a.n && j < b.n) { if (a.l[i] == b.l[j]) { i++; j++; } else if (a.l[i] > b.l[j]) j++; else return 0; }
  return i == a.n;
}
static int clause_cmp(const void *x, const void *y) {
  const Clause *a = x, *b = y;
  if (a->n != b->n) return a->n - b->n;
  for (int i = 0; i < a->n; i++) if (a->l[i] != b->l[i]) return a->l[i] < b->l[i] ? -1 : 1;
  return 0;
}
static int clause_contra(Clause c) { /* holds both (i = 0) and (i = 1) */
  for (int i = 0; i + 1 < c.n; i++) if (c.l[i] / 2 == c.l[i + 1] / 2) return 1;
  return 0;
}
/* drop contradictory clauses (faces only), duplicates and subsumed clauses */
static Form *form_norm(Clause *c, int n, int face) {
  int m = 0;
  for (int i = 0; i < n; i++) if (!(face && clause_contra(c[i]))) c[m++] = c[i];
  n = m;
  int *keep = xmalloc((n ? n : 1) * sizeof(int));
  for (int i = 0; i < n; i++) {
    keep[i] = 1;
    for (int j = 0; j < n && keep[i]; j++) {
      if (i == j || !clause_sub(c[j], c[i])) continue;
      if (c[j].n < c[i].n || j < i) keep[i] = 0;
    }
  }
  m = 0; for (int i = 0; i < n; i++) if (keep[i]) c[m++] = c[i];
  free(keep);
  qsort(c, m, sizeof(Clause), clause_cmp);
  Form *d = xmalloc(sizeof *d); d->n = m; d->c = c; return d;
}
static Form *form_bot(void) { return form_norm(xmalloc(sizeof(Clause)), 0, 0); }
static Form *form_top(void) { Clause *c = xmalloc(sizeof(Clause)); c[0] = clause_make(NULL, 0); return form_norm(c, 1, 0); }
static Form *form_lit(int lit) { Clause *c = xmalloc(sizeof(Clause)); c[0] = clause_make(&lit, 1); return form_norm(c, 1, 0); }
static int form_istop(const Form *d) { return d->n >= 1 && d->c[0].n == 0; }
static int form_isbot(const Form *d) { return d->n == 0; }
static Form *form_or(const Form *a, const Form *b, int face) {
  int n = a->n + b->n; Clause *c = xmalloc((n ? n : 1) * sizeof(Clause));
  for (int i = 0; i < a->n; i++) c[i] = clause_make(a->c[i].l, a->c[i].n);
  for (int i = 0; i < b->n; i++) c[a->n + i] = clause_make(b->c[i].l, b->c[i].n);
  return form_norm(c, n, face);
}
static Form *form_and(const Form *a, const Form *b, int face) {
  int n = a->n * b->n, k = 0; Clause *c = xmalloc((n ? n : 1) * sizeof(Clause));
  for (int i = 0; i < a->n; i++)
    for (int j = 0; j < b->n; j++) {
      int na = a->c[i].n, nb = b->c[j].n; int *t = xmalloc((na + nb + 1) * sizeof(int));
      if (na) memcpy(t, a->c[i].l, na * sizeof(int));
      if (nb) memcpy(t + na, b->c[j].l, nb * sizeof(int));
      c[k++] = clause_make(t, na + nb); free(t);
    }
  return form_norm(c, n, face);
}
/* interval negation: De Morgan */
static Form *iv_not(const Form *a) {
  Form *acc = form_top();
  for (int i = 0; i < a->n; i++) {
    int m = a->c[i].n; Clause *d = xmalloc((m ? m : 1) * sizeof(Clause));
    for (int j = 0; j < m; j++) { int l = a->c[i].l[j] ^ 1; d[j] = clause_make(&l, 1); }
    acc = form_and(acc, form_norm(d, m, 0), 0);
  }
  return acc;
}
/* the face (r = b) of an interval value r */
static Form *face_eq(const Form *r, int b) {
  const Form *s = b ? r : iv_not(r);       /* (r = 0) is (~r = 1) */
  /* (s = 1): each interval literal i becomes (i = 1), ~i becomes (i = 0) */
  Clause *c = xmalloc((s->n ? s->n : 1) * sizeof(Clause));
  for (int i = 0; i < s->n; i++) {
    int *t = xmalloc((s->c[i].n + 1) * sizeof(int));
    for (int j = 0; j < s->c[i].n; j++) { int l = s->c[i].l[j]; t[j] = (l / 2) * 2 + ((l & 1) ? 0 : 1); }
    c[i] = clause_make(t, s->c[i].n); free(t);
  }
  return form_norm(c, s->n, 1);
}
static Form *face_forall(const Form *a, int name) { /* the clauses not mentioning name */
  Clause *c = xmalloc((a->n ? a->n : 1) * sizeof(Clause)); int k = 0;
  for (int i = 0; i < a->n; i++) {
    int men = 0; for (int j = 0; j < a->c[i].n; j++) if (a->c[i].l[j] / 2 == name) men = 1;
    if (!men) c[k++] = clause_make(a->c[i].l, a->c[i].n);
  }
  return form_norm(c, k, 1);
}

/* reindexing a form: the name nu replaced by the interval value r */
static Form *iv_subst(const Form *a, int nu, const Form *r) {
  Form *acc = form_bot();
  for (int i = 0; i < a->n; i++) {
    Form *c = form_top();
    for (int j = 0; j < a->c[i].n; j++) {
      int l = a->c[i].l[j];
      c = form_and(c, l / 2 == nu ? ((l & 1) ? iv_not(r) : (Form *)r) : form_lit(l), 0);
    }
    acc = form_or(acc, c, 0);
  }
  return acc;
}
static Form *face_subst(const Form *a, int nu, const Form *r) {
  Form *acc = form_bot();
  for (int i = 0; i < a->n; i++) {
    Form *c = form_top();
    for (int j = 0; j < a->c[i].n; j++) {
      int l = a->c[i].l[j];
      c = form_and(c, l / 2 == nu ? face_eq(r, l & 1) : form_lit(l), 1);
    }
    acc = form_or(acc, c, 1);
  }
  return acc;
}

/* ------------------------------------------------------------------ the net */

typedef struct { uint32_t n, s; } Ptr;

enum {
  K_FREE, K_ROOT, K_WIRE, K_HOLD, K_ERA, K_REF,
  /* values: principal port = output */
  K_LAM, K_PLAM, K_PAIR, K_SUP, K_IV, K_FACE, K_ATOM, K_UNIV, K_PI, K_SIG, K_PATHT, K_GLUEV, K_GLUEEL,
  K_CTOR, K_SYSV, K_NOSYS,
  /* consumers: principal port = demanded input */
  K_APP, K_PAPP, K_FST, K_SND, K_DUP, K_NOT, K_MEET1, K_MEET2, K_JOIN1, K_JOIN2,
  K_FEQ0, K_FEQ1, K_FAND1, K_FAND2, K_FOR1, K_FOR2, K_FALL,
  K_SEL, K_SEL2, K_SELR, K_COMP, K_COMPH,
  K_GLUEE, K_GLUEF, K_UNG1, K_UNG2, K_UNG3, K_ELIM, K_REFLECT, K_NPAPP, K_SUB1, K_SUB2,
  K_PIDOM, K_PICOD, K_SIGDOM, K_SIGCOD, K_PFAM, K_PLEFT, K_PRIGHT, K_GALPHA, K_GBASE, K_GSYS,
  NK
};
enum { PR, IN, OUT, NO };

static const struct { const char *name; int np; int cls[5]; } KS[NK] = {
  [K_FREE] = {"free", 0, {NO}},
  [K_ROOT] = {"root", 2, {NO, IN}},
  [K_WIRE] = {"wire", 3, {NO, IN, IN}},
  [K_HOLD] = {"hold", 4, {NO, NO, IN, NO}},
  [K_ERA] = {"era", 1, {PR}},
  [K_REF] = {"ref", 1, {PR}},
  [K_LAM] = {"lam", 4, {PR, OUT, IN, IN}},        /* variable, body, domain type */
  [K_PLAM] = {"plam", 3, {PR, OUT, IN}},          /* dimension, body */
  [K_PAIR] = {"pair", 3, {PR, IN, IN}},
  [K_SUP] = {"sup", 3, {PR, IN, IN}},
  [K_IV] = {"interval", 1, {PR}},                 /* d = interval form */
  [K_FACE] = {"face", 1, {PR}},                   /* d = face form */
  [K_ATOM] = {"atom", 1, {PR}},                   /* lab = name */
  [K_UNIV] = {"U", 1, {PR}},                      /* lab = level */
  [K_PI] = {"Pi", 3, {PR, IN, IN}},               /* domain, codomain */
  [K_SIG] = {"Sigma", 3, {PR, IN, IN}},
  [K_PATHT] = {"PathP", 4, {PR, IN, IN, IN}},     /* family, end 0, end 1 */
  [K_GLUEV] = {"Glue", 4, {PR, IN, IN, IN}},      /* face, base, system of (T , e) */
  [K_GLUEEL] = {"glue", 3, {PR, IN, IN}},         /* system of t, base element; d = face */
  [K_CTOR] = {"ctor", 0, {PR}},                  /* a construction with a rule: ports from its arity */
  [K_SYSV] = {"sys", 4, {PR, IN, IN, IN}},        /* face, entry, rest */
  [K_NOSYS] = {"nosys", 1, {PR}},
  [K_APP] = {"app", 3, {PR, IN, OUT}},            /* function; argument, result */
  [K_PAPP] = {"papp", 3, {PR, IN, OUT}},          /* path; interval, result */
  [K_FST] = {"fst", 2, {PR, OUT}}, [K_SND] = {"snd", 2, {PR, OUT}},
  [K_DUP] = {"dup", 3, {PR, OUT, OUT}},
  [K_NOT] = {"not", 2, {PR, OUT}},
  [K_MEET1] = {"meet", 3, {PR, IN, OUT}}, [K_MEET2] = {"meet", 2, {PR, OUT}},
  [K_JOIN1] = {"join", 3, {PR, IN, OUT}}, [K_JOIN2] = {"join", 2, {PR, OUT}},
  [K_FEQ0] = {"eq0", 2, {PR, OUT}}, [K_FEQ1] = {"eq1", 2, {PR, OUT}},
  [K_FAND1] = {"fand", 3, {PR, IN, OUT}}, [K_FAND2] = {"fand", 2, {PR, OUT}},
  [K_FOR1] = {"for", 3, {PR, IN, OUT}}, [K_FOR2] = {"for", 2, {PR, OUT}},
  [K_FALL] = {"forall", 2, {PR, OUT}},            /* lab = the fresh name */
  [K_SEL] = {"sel", 2, {PR, OUT}},
  [K_SEL2] = {"sel", 4, {PR, IN, IN, OUT}},       /* face; entry, rest, result */
  [K_SELR] = {"sel", 3, {PR, IN, OUT}},           /* selection of the rest; entry, result; d = face */
  [K_COMP] = {"comp", 5, {PR, IN, IN, IN, OUT}},  /* face; line, tube, cap, result */
  [K_COMPH] = {"comp", 5, {PR, IN, IN, IN, OUT}}, /* head of the line; line, tube, cap, result; d = face */
  [K_GLUEE] = {"glue", 4, {PR, IN, IN, OUT}},     /* face; system, base, result */
  [K_UNG1] = {"unglue", 3, {PR, IN, OUT}},        /* Glue type; element, result */
  [K_UNG2] = {"unglue", 4, {PR, IN, IN, OUT}},    /* face; system, element, result */
  [K_UNG3] = {"unglue", 2, {PR, OUT}},            /* element; result */
  [K_ELIM] = {"elim", 0, {PR}},                   /* a construction applied: principal argument; others, result */
  [K_REFLECT] = {"reflect", 3, {PR, IN, OUT}},    /* type; neutral, result */
  [K_NPAPP] = {"npapp", 5, {PR, IN, IN, IN, OUT}},/* interval; neutral path, end 0, end 1, result */
  [K_GLUEF] = {"Glue", 4, {PR, IN, IN, OUT}},     /* face; base, system of (T , e), result */
  [K_SUB1] = {"reindex", 3, {PR, IN, OUT}},       /* r; term, result; lab = ν: the term with ν := r */
  [K_SUB2] = {"reindex", 2, {PR, OUT}},           /* term; result; lab = ν, d = r */
  [K_PIDOM] = {"pidom", 2, {PR, OUT}}, [K_PICOD] = {"picod", 2, {PR, OUT}},
  [K_SIGDOM] = {"sigdom", 2, {PR, OUT}}, [K_SIGCOD] = {"sigcod", 2, {PR, OUT}},
  [K_PFAM] = {"pfam", 2, {PR, OUT}}, [K_PLEFT] = {"pleft", 2, {PR, OUT}}, [K_PRIGHT] = {"pright", 2, {PR, OUT}},
  [K_GALPHA] = {"galpha", 2, {PR, OUT}}, [K_GBASE] = {"gbase", 2, {PR, OUT}}, [K_GSYS] = {"gsys", 2, {PR, OUT}},
};

static int is_value(int k) { return k >= K_LAM && k <= K_NOSYS; }
static int is_cons(int k) { return k >= K_APP && k < NK; }
/* eliminators that act on a partial system branch by branch (§6) */
static int is_dist(int k) {
  switch (k) {
  case K_APP: case K_PAPP: case K_FST: case K_SND: case K_UNG3: case K_ELIM:
  case K_PIDOM: case K_PICOD: case K_SIGDOM: case K_SIGCOD: case K_PFAM: case K_PLEFT: case K_PRIGHT:
  case K_GALPHA: case K_GBASE: case K_GSYS: return 1;
  }
  return 0;
}

#define MAXARITY 8
#define MAXSLOT 16
typedef struct { uint8_t k; uint32_t lab; Form *d; Ptr p[MAXSLOT + 1]; } Node;
static Node *N; static uint32_t nn, cn;
static uint32_t *fl; static uint32_t nfl, cfl;
static unsigned long long steps, erasures, unfolds;
static uint32_t nlab = 1;

/* the arity of each construction that a rule makes an agent (by definition id) */
static int *con_arity;
static int NPORTS(uint32_t x);
static int elim_slots(uint32_t st);
static int CLS(uint32_t x, int s);
static uint32_t mk(int k) {
  uint32_t i;
  if (nfl) i = fl[--nfl];
  else { if (nn == cn) { cn = cn ? 2 * cn : 4096; N = xrealloc(N, cn * sizeof(Node)); } i = nn++; }
  memset(&N[i], 0, sizeof(Node)); N[i].k = k; return i;
}
static void rm(uint32_t i) {
  N[i].k = K_FREE;
  if (nfl == cfl) { cfl = cfl ? 2 * cfl : 4096; fl = xrealloc(fl, cfl * sizeof *fl); }
  fl[nfl++] = i;
}
static Ptr P(uint32_t n, uint32_t s) { Ptr p = {n, s}; return p; }
/* ports of a node: fixed per kind, or from the arity of its construction.
   A construction agent of arity n: principal = the argument its rules
   inspect, then the other arguments in order, then the result.          */
static int NPORTS(uint32_t x) {
  int k = N[x].k;
  if (k == K_CTOR) return 1 + con_arity[N[x].lab];
  if (k == K_ELIM) return 1 + elim_slots(N[x].lab);
  return KS[k].np;
}
static int CLS(uint32_t x, int s) {
  int k = N[x].k;
  if (k == K_CTOR) return s == 0 ? PR : IN;
  if (k == K_ELIM) return s == 0 ? PR : s == elim_slots(N[x].lab) ? OUT : IN;
  return KS[k].cls[s];
}
static Ptr T(uint32_t n, uint32_t s) { return N[n].p[s]; }
static void lnk(Ptr a, Ptr b) { N[a.n].p[a.s] = b; N[b.n].p[b.s] = a; }
static void era(Ptr t) { uint32_t e = mk(K_ERA); lnk(P(e, 0), t); }
static Ptr leaf(int k) { return P(mk(k), 0); }
static Ptr ivp(Form *d) { uint32_t i = mk(K_IV); N[i].d = d; return P(i, 0); }
static Ptr facep(Form *d) { uint32_t i = mk(K_FACE); N[i].d = d; return P(i, 0); }
static void erase_node(uint32_t x) {
  for (int s = 1; s < NPORTS(x); s++) if (CLS(x, s) != NO) era(T(x, s));
  rm(x);
}
/* a consumer node with its principal port fed by `in`; returns its output port */
static Ptr cons1(int k, Ptr in) { uint32_t x = mk(k); lnk(P(x, 0), in); return P(x, 1); }
static Ptr app(Ptr f, Ptr a) { uint32_t x = mk(K_APP); lnk(P(x, 0), f); lnk(P(x, 1), a); return P(x, 2); }
static Ptr papp(Ptr p, Ptr r) { uint32_t x = mk(K_PAPP); lnk(P(x, 0), p); lnk(P(x, 1), r); return P(x, 2); }
static void dup2(Ptr src, Ptr *a, Ptr *b) { uint32_t d = mk(K_DUP); N[d].lab = nlab++; lnk(P(d, 0), src); *a = P(d, 1); *b = P(d, 2); }

/* An auxiliary port of an active pair wired to an auxiliary port of the same
   pair is first given a wire node, so that each rule reads the outside end
   of every auxiliary port; the wire nodes are spliced out afterwards.      */
static uint32_t wires[16]; static int nwires;
static void prep(uint32_t a, uint32_t b) {
  nwires = 0; uint32_t xs[2] = {a, b};
  for (int q = 0; q < 2; q++) {
    uint32_t x = xs[q];
    for (int s = 1; s < NPORTS(x); s++) {
      if (CLS(x, s) == NO) continue;
      Ptr t = T(x, s);
      if (t.n == a || t.n == b) { uint32_t w = mk(K_WIRE); lnk(P(x, s), P(w, 1)); lnk(P(w, 2), t); wires[nwires++] = w; }
    }
  }
}
static void unwire(void) {
  for (int i = 0; i < nwires; i++) {
    uint32_t w = wires[i]; Ptr x = T(w, 1), y = T(w, 2);
    if (x.n == w) { rm(w); continue; }
    lnk(x, y); rm(w);
  }
  nwires = 0;
}

/* ------------------------------------------------------------------ syntax */

enum {
  A_VAR, A_REF, A_LAM, A_PLAM, A_APP, A_PAPP, A_PAIR, A_FST, A_SND, A_U, A_PI, A_SIG, A_PATHT,
  A_I0, A_I1, A_NEG, A_MEET, A_JOIN, A_FEQ0, A_FEQ1, A_FTOP, A_FBOT, A_FAND, A_FOR, A_FORALL,
  A_SYS, A_COMP, A_GLUET, A_GLUEE, A_UNGLUE, A_UNGLUEF, A_SEL, A_PROJ
};
typedef struct Bind { char *name; int uses, next; Ptr *outs; } Bind;
typedef struct Def Def;
typedef struct Ast {
  int k; struct Ast *a[4]; Bind *b; Def *def; int proj;
  int n; struct Ast **fs, **ts;      /* systems */
} Ast;
struct Def {
  char *name; Ast *body; Ast *sig; int has_sig; int atom; int id;
  int role, arity, st0;       /* role: 0 none, 1 constructor, 2 head of rules (st0: its first state) */
  int kan_rhs, kan_perm[3];   /* a Kan identity for this type: right side, and which of φ u c each variable is */
};
static Def **defs; static int ndefs, cdefs;

static Def *def_find(const char *name) {
  for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i]->name, name)) return defs[i];
  return NULL;
}
static const char *defs_name(uint32_t id);
static Def *def_get(const char *name) {
  Def *d = def_find(name); if (d) return d;
  if (ndefs == cdefs) { cdefs = cdefs ? 2 * cdefs : 64; defs = xrealloc(defs, cdefs * sizeof *defs); }
  d = xmalloc(sizeof *d); memset(d, 0, sizeof *d); d->name = xstrdup(name); d->id = ndefs; d->atom = -1; d->kan_rhs = -1;
  defs[ndefs++] = d; return d;
}

static const char *defs_name(uint32_t id) { return defs[id]->name; }

/* ------------------------------------------------------------- term to net */

static Ptr build(Ast *t);
static Ptr build_atom(Def *d);
static void bindv(Bind *b, Ptr src) {
  b->next = 0;
  if (b->uses == 0) { era(src); return; }
  if (b->uses == 1) { b->outs[0] = src; return; }
  Ptr cur = src;
  for (int i = 0; i < b->uses - 1; i++) {
    uint32_t d = mk(K_DUP); N[d].lab = nlab++; lnk(cur, P(d, 0));
    b->outs[i] = P(d, 1); cur = P(d, 2);
  }
  b->outs[b->uses - 1] = cur;
}
static Ptr build_sys(Ast *t, int i) {
  if (i == t->n) return leaf(K_NOSYS);
  uint32_t x = mk(K_SYSV);
  lnk(build(t->fs[i]), P(x, 1)); lnk(build(t->ts[i]), P(x, 2)); lnk(build_sys(t, i + 1), P(x, 3));
  return P(x, 0);
}
static Ptr build2(int k, Ast *a, Ast *b) { uint32_t x = mk(k); lnk(build(a), P(x, 0)); lnk(build(b), P(x, 1)); return P(x, 2); }
static Ptr build(Ast *t) {
  uint32_t x;
  switch (t->k) {
  case A_VAR: {
    Bind *b = t->b; if (b->next >= b->uses) die("internal: occurrence count of %s", b->name);
    return b->outs[b->next++];
  }
  case A_REF:
    if (!t->def->body) return build_atom(t->def);
    x = mk(K_REF); N[x].lab = t->def->id; return P(x, 0);
  case A_LAM:
    x = mk(K_LAM); bindv(t->b, P(x, 1)); lnk(build(t->a[0]), P(x, 2));
    lnk(t->a[1] ? build(t->a[1]) : leaf(K_ERA), P(x, 3)); return P(x, 0);
  case A_PLAM: x = mk(K_PLAM); bindv(t->b, P(x, 1)); lnk(build(t->a[0]), P(x, 2)); return P(x, 0);
  case A_APP: return build2(K_APP, t->a[0], t->a[1]);
  case A_PAPP: return build2(K_PAPP, t->a[0], t->a[1]);
  case A_PAIR: x = mk(K_PAIR); lnk(build(t->a[0]), P(x, 1)); lnk(build(t->a[1]), P(x, 2)); return P(x, 0);
  case A_FST: return cons1(K_FST, build(t->a[0]));
  case A_SND: return cons1(K_SND, build(t->a[0]));
  case A_U: x = mk(K_UNIV); N[x].lab = (uint32_t)t->proj; return P(x, 0);
  case A_PI: case A_SIG: {
    x = mk(t->k == A_PI ? K_PI : K_SIG); lnk(build(t->a[0]), P(x, 1));
    uint32_t l = mk(K_LAM); bindv(t->b, P(l, 1)); lnk(build(t->a[1]), P(l, 2)); lnk(leaf(K_ERA), P(l, 3));
    lnk(P(l, 0), P(x, 2)); return P(x, 0);
  }
  case A_PATHT:
    x = mk(K_PATHT); lnk(build(t->a[0]), P(x, 1)); lnk(build(t->a[1]), P(x, 2)); lnk(build(t->a[2]), P(x, 3));
    return P(x, 0);
  case A_I0: return ivp(form_bot());
  case A_I1: return ivp(form_top());
  case A_NEG: return cons1(K_NOT, build(t->a[0]));
  case A_MEET: return build2(K_MEET1, t->a[0], t->a[1]);
  case A_JOIN: return build2(K_JOIN1, t->a[0], t->a[1]);
  case A_FEQ0: return cons1(K_FEQ0, build(t->a[0]));
  case A_FEQ1: return cons1(K_FEQ1, build(t->a[0]));
  case A_FTOP: return facep(form_top());
  case A_FBOT: return facep(form_bot());
  case A_FAND: return build2(K_FAND1, t->a[0], t->a[1]);
  case A_FOR: return build2(K_FOR1, t->a[0], t->a[1]);
  case A_FORALL: {
    int nm = freshname("ν"); x = mk(K_FALL); N[x].lab = (uint32_t)nm;
    lnk(papp(build(t->a[0]), ivp(form_lit(nm * 2))), P(x, 0));
    return P(x, 1);
  }
  case A_SYS: return build_sys(t, 0);
  case A_COMP:
    x = mk(K_COMP); lnk(build(t->a[1]), P(x, 0)); lnk(build(t->a[0]), P(x, 1));
    lnk(build(t->a[2]), P(x, 2)); lnk(build(t->a[3]), P(x, 3)); return P(x, 4);
  case A_GLUET:
    x = mk(K_GLUEF); lnk(build(t->a[1]), P(x, 0)); lnk(build(t->a[0]), P(x, 1)); lnk(build(t->a[2]), P(x, 2));
    return P(x, 3);
  case A_UNGLUEF:
    x = mk(K_UNG2); lnk(build(t->a[0]), P(x, 0)); lnk(build(t->a[1]), P(x, 1)); lnk(build(t->a[2]), P(x, 2));
    return P(x, 3);
  case A_GLUEE:
    x = mk(K_GLUEE); lnk(build(t->a[0]), P(x, 0)); lnk(build(t->a[1]), P(x, 1)); lnk(build(t->a[2]), P(x, 2));
    return P(x, 3);
  case A_UNGLUE: return build2(K_UNG1, t->a[0], t->a[1]);
  case A_SEL: return cons1(K_SEL, build(t->a[0]));
  case A_PROJ: return cons1(t->proj, build(t->a[0]));
  }
  die("internal: build %d", t->k); return P(0, 0);
}
/* a postulate is a neutral atom, reflected at its declared type (§7: a
   neutral path exposes its declared ends) */
static Ptr reflect(Ptr type, Ptr neutral) {
  uint32_t r = mk(K_REFLECT); lnk(P(r, 0), type); lnk(P(r, 1), neutral); return P(r, 2);
}
/* A construction that a rule names is an agent: λ x1 … xn → node(x1 … xn),
   the node a constructor (all arguments auxiliary) or, for the head of a
   rule's left face, an agent whose principal port is the inspected argument. */
static int port_of(int st, int slot);
static Ptr build_construction(Def *d) {
  int a = d->arity;
  uint32_t x = mk(d->role == 1 ? K_CTOR : K_ELIM); N[x].lab = (uint32_t)(d->role == 1 ? d->id : d->st0);
  if (a == 0) return P(x, 0);
  uint32_t lam[MAXARITY];
  for (int j = 0; j < a; j++) {
    lam[j] = mk(K_LAM); lnk(leaf(K_ERA), P(lam[j], 3));
    if (j) lnk(P(lam[j], 0), P(lam[j - 1], 2));
    lnk(P(lam[j], 1), P(x, d->role == 1 ? 1 + j : port_of(d->st0, j)));
  }
  lnk(P(x, d->role == 1 ? 0 : a), P(lam[a - 1], 2));
  return P(lam[0], 0);
}
static Ptr build_atom(Def *d) {
  if (d->role) return build_construction(d);
  uint32_t a = mk(K_ATOM); N[a].lab = (uint32_t)d->atom;
  if (!d->sig || (d->sig->k != A_PI && d->sig->k != A_PATHT && d->sig->k != A_SIG)) return P(a, 0);
  return reflect(build(d->sig), P(a, 0));
}
static Ptr build_def(int id) {
  Def *d = defs[id];
  if (!d->body) return build_atom(d);
  return build(d->body);
}
/* a rule template: the named definition of core.ctt applied to operands */
static Ptr apply_tmpl(const char *name, int n, Ptr *args) {
  Def *d = def_find(name); if (!d || !d->body) die("core.ctt lacks %s", name);
  uint32_t r = mk(K_REF); N[r].lab = d->id; Ptr cur = P(r, 0);
  for (int i = 0; i < n; i++) cur = app(cur, args[i]);
  return cur;
}

/* ------------------------------------------------------------- interactions */

/* <i> (t with ν := i) */
static Ptr line_of(Ptr t, int nu) {
  uint32_t l = mk(K_PLAM), s = mk(K_SUB1); N[s].lab = (uint32_t)nu;
  lnk(P(l, 1), P(s, 0)); lnk(P(s, 1), t); lnk(P(s, 2), P(l, 2));
  return P(l, 0);
}
static Ptr sub2(Ptr t, uint32_t nu, Form *r) {
  uint32_t s = mk(K_SUB2); N[s].lab = nu; N[s].d = r; lnk(P(s, 0), t); return P(s, 1);
}
static int form_kind(int k) {   /* the form a node carries: 1 interval, 2 face, 0 none */
  switch (k) {
  case K_IV: case K_MEET2: case K_JOIN2: case K_SUB2: return 1;
  case K_FACE: case K_FAND2: case K_FOR2: case K_COMPH: case K_SELR: case K_GLUEEL: return 2;
  }
  return 0;
}
/* Reindexing reaches the output port of a consumer that has not produced a
   value: it moves to the consumer's inputs (substitution commutes with every
   construction), so a face that the reindexing makes true can fire.  A bound
   variable needs none: ν is fresh, so nothing from outside mentions it.
   A duplicator's output is shared with its other branch, so there the
   reindexing waits for the duplicated value instead.                        */
static void push_through(uint32_t sb, Ptr p) {
  uint32_t n = p.n; uint32_t nu = N[sb].lab; Form *r = N[sb].d; Ptr out = T(sb, 1);
  int k = N[n].k;
  if (k == K_LAM || k == K_PLAM) { lnk(p, out); rm(sb); return; }
  for (int t = 0; t < NPORTS(n); t++) {
    int cl = CLS(n, t); if (cl != PR && cl != IN) continue;
    Ptr x = T(n, t); lnk(sub2(x, nu, r), P(n, t));
  }
  int fk = form_kind(k);
  if (fk == 1) N[n].d = iv_subst(N[n].d, (int)nu, r);
  if (fk == 2) N[n].d = face_subst(N[n].d, (int)nu, r);
  lnk(p, out); rm(sb);
}

/* ---- rules generated from identities (rule p): a matching automaton
   A state of the head f holds the argument positions not yet inspected
   (slots, as paths into f's arguments), the rules still possible, and the
   constructors already seen.  Its agent has the inspected slot as principal
   port, the other slots as auxiliary ports in order, and the result last.
   A constructor arriving at the principal port moves to the next state, its
   arguments taking the place of the slot; a state with one rule left and
   nothing more to inspect fires: the rule's right side applied to the
   values its variables matched.                                            */
#define MAXPATH 8
typedef struct { int len; int ix[MAXPATH]; } Path;
typedef struct Pat { Bind *b; int ctor; int n; struct Pat *sub[MAXARITY]; } Pat;  /* b: a variable; else ctor */
typedef struct { int f; int n; Pat *args[MAXARITY]; Def *rhs; int ng; Bind *g[64]; } GRule;
typedef struct {
  int f, n;                                   /* the head and its arity */
  int nslots; Path slots[MAXSLOT]; int inspect; uint64_t cand; int fire;
  int nm; Path mpath[MAXSLOT]; int mctor[MAXSLOT];
  int nt; int tctor[MAXSLOT]; int tnext[MAXSLOT];
} MState;
static GRule *grules; static int ngrules;
static MState *mst; static int nmst;
static int elim_slots(uint32_t st) { return mst[st].nslots; }
static int path_eq(const Path *a, const Path *b) { return a->len == b->len && !memcmp(a->ix, b->ix, a->len * sizeof(int)); }
static int path_prefix(const Path *a, const Path *b) { return a->len <= b->len && !memcmp(a->ix, b->ix, a->len * sizeof(int)); }
/* the pattern of a rule at a path; NULL beneath a variable */
static Pat *pat_at(GRule *r, const Path *p) {
  Pat *q = r->args[p->ix[0]];
  for (int i = 1; i < p->len; i++) { if (!q || q->b) return NULL; q = q->sub[p->ix[i]]; }
  return q;
}
static int port_of(int st, int slot) {    /* the agent port carrying a slot */
  int ins = mst[st].inspect;
  if (slot == ins) return 0;
  return 1 + (slot < ins ? slot : slot - 1);
}
/* the value at a path, given the ports of the slots: a slot's own port, or
   the constructor seen there rebuilt from the values beneath it            */
static Ptr materialize(int st, const Path *p, Ptr *slotport) {
  MState *m = &mst[st];
  for (int i = 0; i < m->nslots; i++) if (path_eq(&m->slots[i], p)) return slotport[i];
  for (int i = 0; i < m->nm; i++) if (path_eq(&m->mpath[i], p)) {
    int c = m->mctor[i]; uint32_t x = mk(K_CTOR); N[x].lab = (uint32_t)c;
    for (int q = 0; q < con_arity[c]; q++) { Path pq = *p; pq.ix[pq.len++] = q; lnk(materialize(st, &pq, slotport), P(x, 1 + q)); }
    return P(x, 0);
  }
  die("internal: no value at a matched path"); return P(0, 0);
}
static int fire_rule(uint32_t c, uint32_t v) {
  if (N[v].k != K_CTOR) return 0;
  int st = (int)N[c].lab, ctor = (int)N[v].lab, ns = -1;
  for (int t = 0; t < mst[st].nt; t++) if (mst[st].tctor[t] == ctor) ns = mst[st].tnext[t];
  if (ns < 0) return 0;                       /* no rule for this constructor: suspended */
  MState *m = &mst[st], *n2 = &mst[ns];
  Ptr res = T(c, m->nslots);
  Ptr sp[MAXSLOT]; int k = 0;
  for (int i = 0; i < m->nslots; i++) {
    if (i != m->inspect) sp[k++] = T(c, port_of(st, i));
    else for (int q = 0; q < con_arity[ctor]; q++) sp[k++] = T(v, 1 + q);
  }
  rm(c); rm(v);
  if (n2->fire >= 0) {
    GRule *r = &grules[n2->fire];
    Ptr args[64];
    for (int i = 0; i < r->ng; i++) {
      /* the path of variable g[i] in the rule's patterns */
      Path p; int found = 0;
      for (int j = 0; j < r->n && !found; j++) {
        Pat *stack[64]; Path ps[64]; int top = 0;
        stack[top] = r->args[j]; ps[top].len = 1; ps[top].ix[0] = j; top++;
        while (top && !found) {
          top--; Pat *q = stack[top]; Path pp = ps[top];
          if (q->b) { if (q->b == r->g[i]) { p = pp; found = 1; } continue; }
          for (int s2 = 0; s2 < q->n; s2++) { stack[top] = q->sub[s2]; ps[top] = pp; ps[top].ix[ps[top].len++] = s2; top++; }
        }
      }
      if (!found) die("internal: a rule variable has no path");
      args[i] = materialize(ns, &p, sp);
    }
    uint32_t ref = mk(K_REF); N[ref].lab = r->rhs->id; Ptr cur = P(ref, 0);
    for (int i = 0; i < r->ng; i++) cur = app(cur, args[i]);
    lnk(cur, res); return 1;
  }
  uint32_t x = mk(K_ELIM); N[x].lab = (uint32_t)ns;
  for (int i = 0; i < n2->nslots; i++) lnk(sp[i], P(x, port_of(ns, i)));
  lnk(P(x, n2->nslots), res);
  return 1;
}
/* Kan identities compF (<_> T) φ u c = R for a postulated type T */
static int *atom_def; static int natom_def;

/* duplicator meets value: copy it, duplicating inputs, superposing outputs */
static void dupcopy(uint32_t d, uint32_t v) {
  uint32_t k = N[d].lab; int kv = N[v].k;
  uint32_t v2 = mk(kv); N[v2].lab = N[v].lab; N[v2].d = N[v].d;
  for (int s = 1; s < NPORTS(v); s++) {
    int c = CLS(v, s); if (c == NO) continue;
    Ptr t = T(v, s);
    uint32_t x = mk(c == IN ? K_DUP : K_SUP); N[x].lab = k;
    lnk(P(x, 0), t); lnk(P(x, 1), P(v, s)); lnk(P(x, 2), P(v2, s));
  }
  Ptr o1 = T(d, 1), o2 = T(d, 2);
  lnk(P(v, 0), o1); lnk(P(v2, 0), o2); rm(d);
}
/* consumer meets superposition: copy the consumer */
static void supcomm(uint32_t c, uint32_t s) {
  uint32_t k = N[s].lab; int kc = N[c].k;
  uint32_t c2 = mk(kc); N[c2].lab = N[c].lab; N[c2].d = N[c].d;
  for (int t = 1; t < NPORTS(c); t++) {
    int cl = CLS(c, t); if (cl == NO) continue;
    Ptr e = T(c, t);
    uint32_t x = mk(cl == IN ? K_DUP : K_SUP); N[x].lab = k;
    lnk(P(x, 0), e); lnk(P(x, 1), P(c, t)); lnk(P(x, 2), P(c2, t));
  }
  Ptr a = T(s, 1), b = T(s, 2);
  lnk(P(c, 0), a); lnk(P(c2, 0), b); rm(s);
}
/* an eliminator meets a partial system: apply it to each branch (§6) */
static void distribute(uint32_t c, uint32_t s) {
  int kc = N[c].k; int out = -1;
  for (int t = 1; t < NPORTS(c); t++) if (CLS(c, t) == OUT) out = t;
  Ptr res = T(c, out);
  if (N[s].k == K_NOSYS) {
    for (int t = 1; t < NPORTS(c); t++) if (CLS(c, t) == IN) era(T(c, t));
    lnk(P(s, 0), res); rm(c); return;
  }
  uint32_t c2 = mk(kc); N[c2].lab = N[c].lab; N[c2].d = N[c].d;
  for (int t = 1; t < NPORTS(c); t++) {
    if (CLS(c, t) != IN) continue;
    Ptr e = T(c, t); uint32_t x = mk(K_DUP); N[x].lab = nlab++;
    lnk(P(x, 0), e); lnk(P(x, 1), P(c, t)); lnk(P(x, 2), P(c2, t));
  }
  uint32_t s2 = mk(K_SYSV);
  lnk(P(s2, 1), T(s, 1));                                   /* the face */
  lnk(P(c, 0), T(s, 2)); lnk(P(c, out), P(s2, 2));          /* the entry, eliminated */
  lnk(P(c2, 0), T(s, 3)); lnk(P(c2, out), P(s2, 3));        /* the rest, eliminated */
  lnk(P(s2, 0), res); rm(s);
}
static void proj(uint32_t c, uint32_t v, int slot) {
  Ptr res = T(c, 1);
  for (int s = 1; s < NPORTS(v); s++) { if (s == slot) lnk(T(v, s), res); else era(T(v, s)); }
  rm(c); rm(v);
}

/* consumer c meets value v; returns 0, changing nothing, if no rule applies */
static int rule(uint32_t c, uint32_t v) {
  int kc = N[c].k, kv = N[v].k;
  if (is_dist(kc) && (kv == K_SYSV || kv == K_NOSYS)) { distribute(c, v); return 1; }
  switch (kc) {
  case K_APP: {
    if (kv != K_LAM) return 0;
    Ptr arg = T(c, 1), res = T(c, 2), var = T(v, 1), body = T(v, 2);
    era(T(v, 3)); lnk(var, arg); lnk(body, res); rm(c); rm(v); return 1;
  }
  case K_PAPP: {
    if (kv != K_PLAM) return 0;
    Ptr r = T(c, 1), res = T(c, 2), var = T(v, 1), body = T(v, 2);
    lnk(var, r); lnk(body, res); rm(c); rm(v); return 1;
  }
  case K_FST: case K_SND: {
    if (kv != K_PAIR) return 0;
    Ptr res = T(c, 1), x = T(v, 1), y = T(v, 2);
    if (kc == K_FST) { lnk(x, res); era(y); } else { lnk(y, res); era(x); }
    rm(c); rm(v); return 1;
  }
  case K_NOT: if (kv != K_IV) return 0; lnk(ivp(iv_not(N[v].d)), T(c, 1)); rm(c); rm(v); return 1;
  case K_MEET1: case K_JOIN1: case K_FAND1: case K_FOR1: {
    if (kv != (kc == K_MEET1 || kc == K_JOIN1 ? K_IV : K_FACE)) return 0;
    int k2 = kc == K_MEET1 ? K_MEET2 : kc == K_JOIN1 ? K_JOIN2 : kc == K_FAND1 ? K_FAND2 : K_FOR2;
    uint32_t m = mk(k2); N[m].d = N[v].d;
    Ptr y = T(c, 1), res = T(c, 2); lnk(P(m, 0), y); lnk(P(m, 1), res); rm(c); rm(v); return 1;
  }
  case K_MEET2: case K_JOIN2: {
    if (kv != K_IV) return 0;
    Form *r = kc == K_MEET2 ? form_and(N[c].d, N[v].d, 0) : form_or(N[c].d, N[v].d, 0);
    lnk(ivp(r), T(c, 1)); rm(c); rm(v); return 1;
  }
  case K_FAND2: case K_FOR2: {
    if (kv != K_FACE) return 0;
    Form *r = kc == K_FAND2 ? form_and(N[c].d, N[v].d, 1) : form_or(N[c].d, N[v].d, 1);
    lnk(facep(r), T(c, 1)); rm(c); rm(v); return 1;
  }
  case K_FEQ0: case K_FEQ1:
    if (kv != K_IV) return 0;
    lnk(facep(face_eq(N[v].d, kc == K_FEQ1)), T(c, 1)); rm(c); rm(v); return 1;
  case K_FALL:
    if (kv != K_FACE) return 0;
    lnk(facep(face_forall(N[v].d, (int)N[c].lab)), T(c, 1)); rm(c); rm(v); return 1;

  /* selection of a partial element on the current context (χ = ⊤) */
  case K_SEL: {
    if (kv == K_NOSYS) return 0;                       /* no branch holds: suspended */
    Ptr res = T(c, 1);
    if (kv != K_SYSV) { lnk(P(v, 0), res); rm(c); return 1; }
    uint32_t s = mk(K_SEL2);
    lnk(P(s, 0), T(v, 1)); lnk(P(s, 1), T(v, 2)); lnk(P(s, 2), T(v, 3)); lnk(P(s, 3), res);
    rm(c); rm(v); return 1;
  }
  case K_SEL2: {
    if (kv != K_FACE) return 0;
    Ptr entry = T(c, 1), rest = T(c, 2), res = T(c, 3);
    if (form_istop(N[v].d)) { lnk(cons1(K_SEL, entry), res); era(rest); }
    else if (form_isbot(N[v].d)) { lnk(cons1(K_SEL, rest), res); era(entry); }
    else { uint32_t r = mk(K_SELR); N[r].d = N[v].d; lnk(P(r, 0), cons1(K_SEL, rest)); lnk(P(r, 1), entry); lnk(P(r, 2), res); }
    rm(c); rm(v); return 1;
  }
  case K_SELR: { lnk(P(v, 0), T(c, 2)); era(T(c, 1)); rm(c); return 1; }

  /* COMP, face stage (§8): the full-face rule, else demand the type head */
  case K_COMP: {
    if (kv != K_FACE) return 0;
    Ptr line = T(c, 1), tube = T(c, 2), cap = T(c, 3), res = T(c, 4);
    if (form_istop(N[v].d)) { lnk(cons1(K_SEL, papp(tube, ivp(form_top()))), res); era(line); era(cap); }
    else {
      Ptr l1, l2; dup2(line, &l1, &l2);
      int nu = freshname("ν");
      uint32_t h = mk(K_COMPH); N[h].d = N[v].d; N[h].lab = (uint32_t)nu;
      lnk(P(h, 0), papp(l1, ivp(form_lit(nu * 2)))); lnk(P(h, 1), l2); lnk(P(h, 2), tube); lnk(P(h, 3), cap); lnk(P(h, 4), res);
    }
    rm(c); rm(v); return 1;
  }
  /* COMP, head stage: the dispatch table of §28 */
  case K_COMPH: {
    Ptr line = T(c, 1), tube = T(c, 2), cap = T(c, 3), res = T(c, 4); Form *f = N[c].d;
    const char *tm = NULL;
    switch (kv) {
    case K_PI: tm = "compPi"; break;
    case K_SIG: tm = "compSig"; break;
    case K_PATHT: tm = "compPath"; break;
    case K_GLUEV: {
      /* the components of the head at the fresh name ν, made lines in i by
         reindexing ν := i; the Glue type itself may be its T at some i */
      int nu = (int)N[c].lab;
      Ptr Al = line_of(T(v, 2), nu), al = line_of(T(v, 1), nu), Sl = line_of(T(v, 3), nu);
      rm(v); era(line);
      Ptr args[6] = {Al, al, Sl, facep(f), tube, cap}; lnk(apply_tmpl("compGlue", 6, args), res); rm(c); return 1;
    }
    case K_UNIV: {
      erase_node(v); era(line);
      Ptr args[3] = {facep(f), tube, cap}; lnk(apply_tmpl("compU", 3, args), res); rm(c); return 1;
    }
    case K_ATOM: {
      /* a postulated type: its Kan identity, if one was given (rule p) */
      if ((int)N[v].lab >= natom_def || atom_def[N[v].lab] < 0) return 0;   /* a variable: suspended */
      Def *td = defs[atom_def[N[v].lab]];
      if (td->kan_rhs < 0) return 0;                  /* none: suspended */
      Ptr ops[3] = {facep(f), tube, cap}, args[3];
      for (int i = 0; i < 3; i++) args[i] = ops[td->kan_perm[i]];
      rm(v); era(line);
      uint32_t ref = mk(K_REF); N[ref].lab = (uint32_t)td->kan_rhs; Ptr cur = P(ref, 0);
      for (int i = 0; i < 3; i++) cur = app(cur, args[i]);
      lnk(cur, res); rm(c); return 1;
    }
    default: return 0;                                  /* a neutral head: suspended */
    }
    erase_node(v);
    Ptr args[4] = {line, facep(f), tube, cap}; lnk(apply_tmpl(tm, 4, args), res); rm(c); return 1;
  }
  /* §16 Glue: on its face the Glue type is its T */
  case K_GLUEF: {
    if (kv != K_FACE) return 0;
    Ptr base = T(c, 1), sys = T(c, 2), res = T(c, 3);
    if (form_istop(N[v].d)) { lnk(cons1(K_FST, cons1(K_SEL, sys)), res); era(base); rm(v); }
    else { uint32_t g = mk(K_GLUEV); lnk(P(g, 1), P(v, 0)); lnk(P(g, 2), base); lnk(P(g, 3), sys); lnk(P(g, 0), res); }
    rm(c); return 1;
  }
  /* reindexing: wait for r, then for the term */
  case K_SUB1: {
    if (kv != K_IV) return 0;
    lnk(sub2(T(c, 1), N[c].lab, N[v].d), T(c, 2)); rm(c); rm(v); return 1;
  }
  case K_SUB2: {
    uint32_t nu = N[c].lab; Form *r = N[c].d; Ptr res = T(c, 1);
    if (kv == K_IV) { lnk(ivp(iv_subst(N[v].d, (int)nu, r)), res); rm(v); rm(c); return 1; }
    if (kv == K_FACE) { lnk(facep(face_subst(N[v].d, (int)nu, r)), res); rm(v); rm(c); return 1; }
    if (kv == K_GLUEV) {          /* formed again, so its face is decided afresh */
      uint32_t g = mk(K_GLUEF);
      lnk(sub2(T(v, 1), nu, r), P(g, 0)); lnk(sub2(T(v, 2), nu, r), P(g, 1)); lnk(sub2(T(v, 3), nu, r), P(g, 2));
      lnk(P(g, 3), res); rm(v); rm(c); return 1;
    }
    if (kv == K_GLUEEL) {
      uint32_t g = mk(K_GLUEE);
      lnk(facep(face_subst(N[v].d, (int)nu, r)), P(g, 0)); lnk(sub2(T(v, 1), nu, r), P(g, 1)); lnk(sub2(T(v, 2), nu, r), P(g, 2));
      lnk(P(g, 3), res); rm(v); rm(c); return 1;
    }
    for (int t = 1; t < NPORTS(v); t++) if (CLS(v, t) == IN) { Ptr x = T(v, t); lnk(sub2(x, nu, r), P(v, t)); }
    lnk(P(v, 0), res); rm(c); return 1;
  }
  /* §16 glue elements */
  case K_GLUEE: {
    if (kv != K_FACE) return 0;
    Ptr sys = T(c, 1), a = T(c, 2), res = T(c, 3);
    if (form_istop(N[v].d)) { lnk(cons1(K_SEL, sys), res); era(a); }
    else { uint32_t g = mk(K_GLUEEL); N[g].d = N[v].d; lnk(P(g, 1), sys); lnk(P(g, 2), a); lnk(P(g, 0), res); }
    rm(c); rm(v); return 1;
  }
  case K_UNG1: {
    if (kv != K_GLUEV) return 0;
    uint32_t u = mk(K_UNG2);
    lnk(P(u, 0), T(v, 1)); lnk(P(u, 1), T(v, 3)); lnk(P(u, 2), T(c, 1)); lnk(P(u, 3), T(c, 2));
    era(T(v, 2)); rm(v); rm(c); return 1;
  }
  case K_UNG2: {
    if (kv != K_FACE) return 0;
    Ptr sys = T(c, 1), x = T(c, 2), res = T(c, 3);
    if (form_istop(N[v].d)) {                         /* on α: e.f applied to the element */
      Ptr e = cons1(K_SND, cons1(K_SEL, sys));
      lnk(app(cons1(K_FST, e), x), res);
    } else { uint32_t u = mk(K_UNG3); lnk(P(u, 0), x); lnk(P(u, 1), res); era(sys); }
    rm(c); rm(v); return 1;
  }
  case K_UNG3: if (kv != K_GLUEEL) return 0; lnk(T(v, 2), T(c, 1)); era(T(v, 1)); rm(v); rm(c); return 1;

  /* a construction meets a construction: the rule generated from the
     identity whose left face is this pair (rule p), if there is one */
  case K_ELIM: return fire_rule(c, v);

  /* typed neutrals: a variable of a Π or path type is expanded at its type */
  case K_REFLECT: {
    Ptr n = T(c, 1), res = T(c, 2);
    if (kv == K_PI) {
      Ptr dom = T(v, 1), cod = T(v, 2); rm(v);
      uint32_t l = mk(K_LAM); Ptr x1, x2; dup2(P(l, 1), &x1, &x2);
      lnk(reflect(app(cod, x1), app(n, x2)), P(l, 2)); lnk(dom, P(l, 3)); lnk(P(l, 0), res);
    } else if (kv == K_PATHT) {
      Ptr fam = T(v, 1), a0 = T(v, 2), a1 = T(v, 3); rm(v);
      uint32_t l = mk(K_PLAM); Ptr i1, i2; dup2(P(l, 1), &i1, &i2);
      uint32_t np = mk(K_NPAPP); lnk(P(np, 0), i2); lnk(P(np, 1), n); lnk(P(np, 2), a0); lnk(P(np, 3), a1);
      lnk(reflect(papp(fam, i1), P(np, 4)), P(l, 2)); lnk(P(l, 0), res);
    } else if (kv == K_SIG) {
      /* (reflect dom (n .1) , reflect (cod (n .1)) (n .2)) */
      Ptr dom = T(v, 1), cod = T(v, 2); rm(v);
      Ptr n1, n2, f1, f2; dup2(n, &n1, &n2); dup2(cons1(K_FST, n1), &f1, &f2);
      uint32_t pr = mk(K_PAIR);
      lnk(reflect(dom, f1), P(pr, 1)); lnk(reflect(app(cod, f2), cons1(K_SND, n2)), P(pr, 2)); lnk(P(pr, 0), res);
    } else { erase_node(v); lnk(n, res); }
    rm(c); return 1;
  }
  case K_NPAPP: {
    if (kv != K_IV) return 0;
    if (!form_isbot(N[v].d) && !form_istop(N[v].d)) return 0;   /* inside the path: neutral */
    Ptr n = T(c, 1), a0 = T(c, 2), a1 = T(c, 3), res = T(c, 4);
    if (form_istop(N[v].d)) { lnk(a1, res); era(a0); } else { lnk(a0, res); era(a1); }
    era(n); rm(v); rm(c); return 1;
  }
  case K_PIDOM: case K_PICOD: if (kv != K_PI) return 0; proj(c, v, kc == K_PIDOM ? 1 : 2); return 1;
  case K_SIGDOM: case K_SIGCOD: if (kv != K_SIG) return 0; proj(c, v, kc == K_SIGDOM ? 1 : 2); return 1;
  case K_PFAM: case K_PLEFT: case K_PRIGHT: if (kv != K_PATHT) return 0; proj(c, v, kc - K_PFAM + 1); return 1;
  case K_GALPHA: case K_GBASE: case K_GSYS: if (kv != K_GLUEV) return 0; proj(c, v, kc - K_GALPHA + 1); return 1;
  }
  return 0;
}

static int interact(uint32_t a, uint32_t b) {
  int ka = N[a].k, kb = N[b].k;
  if (ka == K_ERA && kb == K_ERA) { rm(a); rm(b); steps++; erasures++; return 1; }
  if (ka == K_ERA || kb == K_ERA) {
    uint32_t e = ka == K_ERA ? a : b, x = ka == K_ERA ? b : a;
    if (N[x].k == K_REF) { rm(x); rm(e); steps++; erasures++; return 1; }
    prep(e, x); erase_node(x); rm(e); unwire(); steps++; erasures++; return 1;
  }
  if (ka == K_REF || kb == K_REF) {
    uint32_t r = ka == K_REF ? a : b, x = ka == K_REF ? b : a;
    if (N[x].k == K_DUP) {
      Ptr o1 = T(x, 1), o2 = T(x, 2); uint32_t r2 = mk(K_REF); N[r2].lab = N[r].lab;
      lnk(P(r, 0), o1); lnk(P(r2, 0), o2); rm(x); steps++; return 1;
    }
    if (!is_cons(N[x].k)) return 0;
    Ptr root = build_def((int)N[r].lab); lnk(root, P(x, 0)); rm(r); steps++; unfolds++; return 1;
  }
  if ((ka == K_DUP && kb == K_SUP) || (ka == K_SUP && kb == K_DUP)) {
    uint32_t d = ka == K_DUP ? a : b, s = ka == K_DUP ? b : a;
    prep(d, s);
    if (N[d].lab == N[s].lab) {
      Ptr x1 = T(s, 1), x2 = T(s, 2), o1 = T(d, 1), o2 = T(d, 2);
      lnk(x1, o1); lnk(x2, o2); rm(d); rm(s);
    } else dupcopy(d, s);
    unwire(); steps++; return 1;
  }
  if (ka == K_DUP && is_value(kb)) { prep(a, b); dupcopy(a, b); unwire(); steps++; return 1; }
  if (kb == K_DUP && is_value(ka)) { prep(b, a); dupcopy(b, a); unwire(); steps++; return 1; }
  if (ka == K_SUP && is_cons(kb)) { prep(b, a); supcomm(b, a); unwire(); steps++; return 1; }
  if (kb == K_SUP && is_cons(ka)) { prep(a, b); supcomm(a, b); unwire(); steps++; return 1; }
  uint32_t c, v;
  if (is_cons(ka) && is_value(kb)) { c = a; v = b; }
  else if (is_cons(kb) && is_value(ka)) { c = b; v = a; }
  else return 0;
  prep(c, v); int ok = rule(c, v); unwire();
  if (ok) steps++;
  return ok;
}

/* ------------------------------------------------- reduction to head form */

static Ptr *stk; static int nstk, cstk;
static void push(Ptr p) { if (nstk == cstk) { cstk = cstk ? 2 * cstk : 256; stk = xrealloc(stk, cstk * sizeof *stk); } stk[nstk++] = p; }

static Ptr whnf(Ptr host) {
restart:
  nstk = 0;
  {
    Ptr p = T(host.n, host.s);
    for (;;) {
      uint32_t n = p.n; int k = N[n].k;
      if (p.s == 0) {
        if (k == K_REF && nstk == 0) {
          Ptr o = T(n, 0); Ptr r = build_def((int)N[n].lab); lnk(r, o); rm(n); steps++; unfolds++;
          goto restart;
        }
        if (nstk == 0) return p;
        uint32_t d = stk[--nstk].n;
        if (interact(d, n)) goto restart;
        return T(host.n, host.s);
      }
      if (CLS(n, (int)p.s) == OUT) {
        if (nstk > 0 && N[stk[nstk - 1].n].k == K_SUB2 && k != K_DUP) { push_through(stk[nstk - 1].n, p); steps++; goto restart; }
        push(p); p = T(n, 0); continue;
      }
      return T(host.n, host.s);
    }
  }
}

/* ------------------------------------------------------------------ read back */

typedef struct { char *s; size_t n, c; } Buf;
static void bput(Buf *b, const char *s) {
  size_t m = strlen(s);
  if (b->n + m + 1 > b->c) { b->c = (b->n + m + 1) * 2; b->s = xrealloc(b->s, b->c); }
  memcpy(b->s + b->n, s, m + 1); b->n += m;
}
static void bform(Buf *b, const Form *d, int face) {
  if (form_isbot(d)) { bput(b, face ? "bot" : "0"); return; }
  if (form_istop(d)) { bput(b, face ? "top" : "1"); return; }
  int paren = d->n > 1 || d->c[0].n > 1 || (!face && (d->c[0].l[0] & 1));
  if (paren) bput(b, "(");
  for (int i = 0; i < d->n; i++) {
    if (i) bput(b, face ? " \\/ " : " ∨ ");
    for (int j = 0; j < d->c[i].n; j++) {
      if (j) bput(b, face ? " /\\ " : " ∧ ");
      int l = d->c[i].l[j];
      if (face) { bput(b, "("); bput(b, names[l / 2]); bput(b, (l & 1) ? " = 1)" : " = 0)"); }
      else { if (l & 1) bput(b, "~ "); bput(b, names[l / 2]); }
    }
  }
  if (paren) bput(b, ")");
}

static uint32_t dctx_lab[1 << 12]; static int dctx_br[1 << 12]; static int ndctx;

static void rb(Ptr host, Buf *o);
static void rb_args(Buf *o, const char *head, uint32_t n, const int *slots, int ns) {
  bput(o, "("); bput(o, head);
  for (int i = 0; i < ns; i++) { bput(o, " "); rb(P(n, slots[i]), o); }
  bput(o, ")");
}
static int is_era_port(Ptr p) { return N[p.n].k == K_ERA && p.s == 0; }
/* Open a binder for reading.  Outside duplicator branches its variable is
   instantiated by a fresh atom (reflected at the domain type when one is
   known) or, for a dimension, a fresh interval name, so the body computes.
   Inside a branch the binder is shared and is read uninstantiated.        */
static const char *open_binder(uint32_t l, Ptr dty) {
  if (ndctx == 0) {
    int nm = freshname(N[l].k == K_PLAM ? "i" : "x");
    Ptr val;
    if (N[l].k == K_PLAM) val = ivp(form_lit(nm * 2));
    else {
      /* reflect at the domain only when it is a Π or path type; a neutral
         domain would otherwise hold the variable back */
      uint32_t a = mk(K_ATOM); N[a].lab = (uint32_t)nm; val = P(a, 0);
      if (dty.n && !is_era_port(dty)) {
        Ptr ty = whnf(P(l, 3));
        if (ty.s == 0 && (N[ty.n].k == K_PI || N[ty.n].k == K_PATHT || N[ty.n].k == K_SIG)) val = reflect(ty, val);
        else era(ty);
      }
    }
    lnk(val, T(l, 1));
    N[l].k = K_HOLD; return names[nm];
  }
  if (!N[l].lab) N[l].lab = (uint32_t)freshname(N[l].k == K_PLAM ? "i" : "x") + 1;
  return names[N[l].lab - 1];
}
static void rb_path(Buf *o, uint32_t n, int st, Path *p) {
  MState *m = &mst[st];
  for (int i = 0; i < m->nslots; i++) if (path_eq(&m->slots[i], p)) { rb(P(n, port_of(st, i)), o); return; }
  for (int i = 0; i < m->nm; i++) if (path_eq(&m->mpath[i], p)) {
    int c = m->mctor[i], a = con_arity[c];
    if (a) bput(o, "(");
    bput(o, defs_name((uint32_t)c));
    for (int q = 0; q < a; q++) { Path pq = *p; pq.ix[pq.len++] = q; bput(o, " "); rb_path(o, n, st, &pq); }
    if (a) bput(o, ")");
    return;
  }
  bput(o, "?");
}
static void rb(Ptr host, Buf *o) {
  Ptr p = whnf(host); uint32_t n = p.n; int k = N[n].k;
  if (p.s == 0) {
    switch (k) {
    case K_LAM: {
      Ptr dty = T(n, 3); const char *x = open_binder(n, dty);
      bput(o, "(\\ "); bput(o, x); bput(o, " → "); rb(P(n, 2), o); bput(o, ")"); return;
    }
    case K_PLAM: {
      const char *x = open_binder(n, P(0, 0));
      bput(o, "(<"); bput(o, x); bput(o, "> "); rb(P(n, 2), o); bput(o, ")"); return;
    }
    case K_PAIR: bput(o, "("); rb(P(n, 1), o); bput(o, " , "); rb(P(n, 2), o); bput(o, ")"); return;
    case K_SUP: {
      int i; for (i = ndctx - 1; i >= 0; i--) if (dctx_lab[i] == N[n].lab) break;
      if (i >= 0) { uint32_t keep = dctx_lab[i]; dctx_lab[i] = 0; rb(P(n, 1 + dctx_br[i]), o); dctx_lab[i] = keep; }
      else { bput(o, "⟪"); rb(P(n, 1), o); bput(o, " | "); rb(P(n, 2), o); bput(o, "⟫"); }
      return;
    }
    case K_IV: bform(o, N[n].d, 0); return;
    case K_FACE: bform(o, N[n].d, 1); return;
    case K_ATOM: bput(o, names[N[n].lab]); return;
    case K_UNIV: { char b[32]; snprintf(b, sizeof b, N[n].lab ? "U%u" : "U", N[n].lab); bput(o, b); return; }
    case K_PI: case K_SIG: {
      /* the domain is read from one copy, the binder reflected at the other */
      Ptr d1, d2; dup2(T(n, 1), &d1, &d2);
      uint32_t h = mk(K_ROOT); lnk(P(h, 1), d1);
      Buf dom = {0}; rb(P(h, 1), &dom);
      Ptr q = whnf(P(n, 2));
      if (q.s == 0 && N[q.n].k == K_LAM) {
        uint32_t l = q.n; era(T(l, 3)); lnk(d2, P(l, 3));
        const char *x = open_binder(l, T(l, 3));
        bput(o, "(("); bput(o, x); bput(o, " : "); bput(o, dom.s); bput(o, k == K_PI ? ") → " : ") * ");
        rb(P(l, 2), o); bput(o, ")");
      } else {
        era(d2);
        bput(o, k == K_PI ? "(Π " : "(Σ "); bput(o, dom.s); bput(o, " "); rb(P(n, 2), o); bput(o, ")");
      }
      free(dom.s); return;
    }
    case K_PATHT: { int s[3] = {1, 2, 3}; rb_args(o, "PathP", n, s, 3); return; }
    case K_GLUEV: {               /* §16: on its face a Glue type is its T */
      uint32_t h = mk(K_ROOT); lnk(P(h, 1), T(n, 1));
      Ptr f = whnf(P(h, 1));
      if (f.s == 0 && N[f.n].k == K_FACE && form_istop(N[f.n].d)) {
        era(T(n, 2)); lnk(P(h, 1), cons1(K_FST, cons1(K_SEL, T(n, 3)))); era(f);
        rb(P(h, 1), o); return;
      }
      lnk(T(h, 1), P(n, 1));
      int s[3] = {2, 1, 3}; rb_args(o, "GlueF", n, s, 3); return;
    }
    case K_GLUEEL: {
      bput(o, "(glueF "); bform(o, N[n].d, 1); bput(o, " "); rb(P(n, 1), o); bput(o, " "); rb(P(n, 2), o); bput(o, ")");
      return;
    }
    case K_SYSV: {
      bput(o, "[ "); Ptr q = p;
      for (int first = 1;;) {
        uint32_t s = q.n;
        Ptr fq = whnf(P(s, 1));
        if (!(fq.s == 0 && N[fq.n].k == K_FACE && form_isbot(N[fq.n].d))) {   /* a ⊥ branch is absent */
          if (!first) bput(o, " ; ");
          first = 0; rb(P(s, 1), o); bput(o, " → "); rb(P(s, 2), o);
        }
        q = whnf(P(s, 3));
        if (!(q.s == 0 && N[q.n].k == K_SYSV)) {
          if (!(q.s == 0 && N[q.n].k == K_NOSYS)) { bput(o, " ; ... "); rb(P(s, 3), o); }
          break;
        }
      }
      bput(o, " ]"); return;
    }
    case K_NOSYS: bput(o, "[]"); return;
    case K_CTOR: {
      int a = con_arity[N[n].lab];
      if (a) bput(o, "(");
      bput(o, defs_name(N[n].lab));
      for (int j = 1; j <= a; j++) { bput(o, " "); rb(P(n, j), o); }
      if (a) bput(o, ")");
      return;
    }
    case K_ERA: bput(o, "∅"); return;
    default: bput(o, KS[k].name); return;
    }
  }
  switch (k) {
  case K_LAM: case K_PLAM: if (N[n].lab) bput(o, names[N[n].lab - 1]); else bput(o, "<var>"); return;
  case K_DUP:
    if (ndctx == (int)(sizeof dctx_lab / sizeof *dctx_lab)) die("read-back nests too deep");
    dctx_lab[ndctx] = N[n].lab; dctx_br[ndctx] = (int)p.s - 1; ndctx++;
    rb(P(n, 0), o); ndctx--; return;
  case K_APP: bput(o, "("); rb(P(n, 0), o); bput(o, " "); rb(P(n, 1), o); bput(o, ")"); return;
  case K_PAPP: bput(o, "("); rb(P(n, 0), o); bput(o, " @ "); rb(P(n, 1), o); bput(o, ")"); return;
  case K_FST: bput(o, "("); rb(P(n, 0), o); bput(o, " .1)"); return;
  case K_SND: bput(o, "("); rb(P(n, 0), o); bput(o, " .2)"); return;
  case K_NOT: bput(o, "(~ "); rb(P(n, 0), o); bput(o, ")"); return;
  case K_COMP: { int s[4] = {1, 0, 2, 3}; rb_args(o, "compF", n, s, 4); return; }
  case K_COMPH: {
    bput(o, "(compF "); rb(P(n, 1), o); bput(o, " "); bform(o, N[n].d, 1); bput(o, " ");
    rb(P(n, 2), o); bput(o, " "); rb(P(n, 3), o); bput(o, ")"); return;
  }
  case K_REFLECT: rb(P(n, 1), o); return;
  case K_NPAPP: bput(o, "("); rb(P(n, 1), o); bput(o, " @ "); rb(P(n, 0), o); bput(o, ")"); return;
  case K_SEL: {                  /* stuck on a total term: selection is the identity there */
    Ptr q = whnf(P(n, 0));
    if (!(q.s == 0 && (N[q.n].k == K_SYSV || N[q.n].k == K_NOSYS))) { rb(P(n, 0), o); return; }
    int s[1] = {0}; rb_args(o, "sel", n, s, 1); return;
  }
  case K_SELR: {
    bput(o, "(sel [ "); bform(o, N[n].d, 1); bput(o, " → "); rb(P(n, 1), o); bput(o, " ; ... "); rb(P(n, 0), o); bput(o, " ])");
    return;
  }
  case K_UNG1: { int s[2] = {0, 1}; rb_args(o, "unglue", n, s, 2); return; }
  case K_UNG3: { int s[1] = {0}; rb_args(o, "unglue", n, s, 1); return; }
  case K_ELIM: {                 /* the head applied to its arguments as matched so far */
    int st = (int)N[n].lab;
    bput(o, "("); bput(o, defs_name((uint32_t)mst[st].f));
    for (int j = 0; j < mst[st].n; j++) { Path p; p.len = 1; p.ix[0] = j; bput(o, " "); rb_path(o, n, st, &p); }
    bput(o, ")"); return;
  }
  default: {
    int s[MAXARITY + 1], ns = 0;
    for (int t = 0; t < NPORTS(n); t++) if (CLS(n, t) == PR || CLS(n, t) == IN) s[ns++] = t;
    rb_args(o, KS[k].name, n, s, ns); return;
  }
  }
}

/* ------------------------------------------------------------------ lexer */

enum { T_EOF, T_ID, T_SYM };
typedef struct { int t; char *s; int col, line; const char *file; } Tok;
static Tok *toks; static int ntoks, ctoks, ti;

static void addtok(int t, const char *s, size_t len, int col, int line, const char *file) {
  if (ntoks == ctoks) { ctoks = ctoks ? 2 * ctoks : 1024; toks = xrealloc(toks, ctoks * sizeof *toks); }
  char *c = xmalloc(len + 1); memcpy(c, s, len); c[len] = 0;
  toks[ntoks].t = t; toks[ntoks].s = c; toks[ntoks].col = col; toks[ntoks].line = line; toks[ntoks].file = file; ntoks++;
}
/* symbols; interval ∧ ∨ (ASCII && ||) are distinct from face /\ \/ */
static const struct { const char *u, *a; } USYM[] = {
  {"λ", "\\"}, {"→", "->"}, {"×", "*"}, {"∧", "&&"}, {"∨", "||"}, {"⊤", "top"}, {"⊥", "bot"}, {NULL, NULL}
};
static int usym(const char *p) {
  for (int i = 0; USYM[i].u; i++) if (!strncmp(p, USYM[i].u, strlen(USYM[i].u))) return i;
  return -1;
}
static int idstart(const char *p) {
  unsigned char c = (unsigned char)*p;
  if (c >= 0x80) return usym(p) < 0;
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || (c >= '0' && c <= '9');
}
static int idchar(const char *p) {
  unsigned char c = (unsigned char)*p;
  if (c >= 0x80) return usym(p) < 0;
  if (c == '-') return p[1] != '-' && p[1] != '>';
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_' || c == '\'';
}
static void lex(const char *src, const char *file) {
  int line = 1; const char *ls = src; const char *p = src;
  for (;;) {
    if (*p == 0) break;
    if (*p == '\n') { p++; line++; ls = p; continue; }
    if (*p == ' ' || *p == '\t' || *p == '\r') { p++; continue; }
    if (p[0] == '-' && p[1] == '-') { while (*p && *p != '\n') p++; continue; }
    if (p[0] == '{' && p[1] == '-') {
      int depth = 1; p += 2;
      while (*p && depth) {
        if (p[0] == '{' && p[1] == '-') { depth++; p += 2; }
        else if (p[0] == '-' && p[1] == '}') { depth--; p += 2; }
        else { if (*p == '\n') { line++; ls = p + 1; } p++; }
      }
      continue;
    }
    int col = (int)(p - ls);
    int u = usym(p);
    if (u >= 0) {
      const char *a = USYM[u].a;
      addtok(isalpha((unsigned char)a[0]) ? T_ID : T_SYM, a, strlen(a), col, line, file);
      p += strlen(USYM[u].u); continue;
    }
    if (p[0] == '-' && p[1] == '>') { addtok(T_SYM, "->", 2, col, line, file); p += 2; continue; }
    if (p[0] == '/' && p[1] == '\\') { addtok(T_SYM, "/\\", 2, col, line, file); p += 2; continue; }
    if (p[0] == '\\' && p[1] == '/') { addtok(T_SYM, "\\/", 2, col, line, file); p += 2; continue; }
    if (p[0] == '&' && p[1] == '&') { addtok(T_SYM, "&&", 2, col, line, file); p += 2; continue; }
    if (p[0] == '|' && p[1] == '|') { addtok(T_SYM, "||", 2, col, line, file); p += 2; continue; }
    if (p[0] == '.' && (p[1] == '1' || p[1] == '2')) { addtok(T_SYM, p, 2, col, line, file); p += 2; continue; }
    if (strchr("()[],;:=~*\\<>@", *p)) { addtok(T_SYM, p, 1, col, line, file); p++; continue; }
    if (idstart(p)) {
      const char *q = p; while (*q && idchar(q)) q++;
      addtok(T_ID, p, (size_t)(q - p), col, line, file); p = q; continue;
    }
    die("%s:%d: unexpected character '%c'", file, line, *p);
  }
  addtok(T_EOF, "", 0, 0, line, file);
}

/* ------------------------------------------------------------------ parser */

static Bind **scope; static int nscope, cscope;
static void scope_push(Bind *b) { if (nscope == cscope) { cscope = cscope ? 2 * cscope : 64; scope = xrealloc(scope, cscope * sizeof *scope); } scope[nscope++] = b; }

static Tok *cur(void) { return &toks[ti]; }
static void perr(const char *msg) { die("%s:%d: %s (at '%s')", cur()->file, cur()->line, msg, cur()->s); }
static int stopped(void) { return cur()->t == T_EOF || cur()->col == 0; }
static int issym(const char *s) { return !stopped() && cur()->t == T_SYM && !strcmp(cur()->s, s); }
static int isid(const char *s) { return !stopped() && cur()->t == T_ID && !strcmp(cur()->s, s); }
static void expect(const char *s) { if (!issym(s)) { char m[64]; snprintf(m, sizeof m, "expected '%s'", s); perr(m); } ti++; }

static Ast *ast(int k) { Ast *t = xmalloc(sizeof *t); memset(t, 0, sizeof *t); t->k = k; return t; }
static Ast *ast1(int k, Ast *a) { Ast *t = ast(k); t->a[0] = a; return t; }
static Ast *ast2(int k, Ast *a, Ast *b) { Ast *t = ast(k); t->a[0] = a; t->a[1] = b; return t; }
static Ast *ast3(int k, Ast *a, Ast *b, Ast *c) { Ast *t = ast2(k, a, b); t->a[2] = c; return t; }
static Bind *newbind(const char *name) { Bind *b = xmalloc(sizeof *b); memset(b, 0, sizeof *b); b->name = xstrdup(name); return b; }
static int binds(int k) { return k == A_LAM || k == A_PLAM || k == A_PI || k == A_SIG; }

/* copy of a term with its inner binders renewed; variables in `from` are
   renamed to `to`, and variables in `sfrom` are replaced by copies of `sto` */
static Bind **cm_from, **cm_to; static int ncm, ccm;
static Bind **sm_from; static Ast **sm_to; static int nsm;
static Bind *cm_forbid;
static void cm_push(Bind *f, Bind *t) {
  if (ncm == ccm) { ccm = ccm ? 2 * ccm : 64; cm_from = xrealloc(cm_from, ccm * sizeof *cm_from); cm_to = xrealloc(cm_to, ccm * sizeof *cm_to); }
  cm_from[ncm] = f; cm_to[ncm] = t; ncm++;
}
static Ast *copy_rec(Ast *t) {
  if (!t) return NULL;
  if (t->k == A_VAR) {
    if (t->b == cm_forbid) die("a face of a system mentions the bound dimension %s", cm_forbid->name);
    for (int i = ncm - 1; i >= 0; i--) if (cm_from[i] == t->b) { Ast *c = ast(A_VAR); c->b = cm_to[i]; return c; }
    for (int i = nsm - 1; i >= 0; i--) if (sm_from[i] == t->b) {
      int save = nsm; nsm = 0; Ast *c = copy_rec(sm_to[i]); nsm = save; return c;
    }
    Ast *c = ast(A_VAR); c->b = t->b; return c;
  }
  Ast *c = xmalloc(sizeof *c); *c = *t;
  int save = ncm;
  if (binds(t->k)) { Bind *nb = newbind(t->b->name); cm_push(t->b, nb); c->b = nb; }
  for (int i = 0; i < 4; i++) c->a[i] = copy_rec(t->a[i]);
  if (t->k == A_SYS) {
    c->fs = xmalloc((t->n ? t->n : 1) * sizeof(Ast *)); c->ts = xmalloc((t->n ? t->n : 1) * sizeof(Ast *));
    for (int i = 0; i < t->n; i++) { c->fs[i] = copy_rec(t->fs[i]); c->ts[i] = copy_rec(t->ts[i]); }
  }
  ncm = save;
  return c;
}
static Ast *copy_ast(Ast *t, Bind *forbid) { ncm = 0; nsm = 0; cm_forbid = forbid; Ast *c = copy_rec(t); cm_forbid = NULL; return c; }
static Ast *subst_ast(Ast *t, Bind *b, Ast *v) {
  static Bind *f1[1]; static Ast *t1[1];
  f1[0] = b; t1[0] = v; ncm = 0; sm_from = f1; sm_to = t1; nsm = 1; cm_forbid = NULL;
  Ast *c = copy_rec(t); nsm = 0; return c;
}
/* φ of a literal system: the join of its faces */
static Ast *sys_phi(Ast *s, Bind *forbid) {
  if (s->k != A_SYS) perr("a literal system [ face -> term ; ... ] is required here");
  if (s->n == 0) return ast(A_FBOT);
  Ast *phi = copy_ast(s->fs[0], forbid);
  for (int i = 1; i < s->n; i++) phi = ast2(A_FOR, phi, copy_ast(s->fs[i], forbid));
  return phi;
}

static Ast *parse_term(void);
static Ast *parse_or(void);
static Ast *parse_atom(void);

static Ast *parse_atom_post(void) {
  Ast *t = parse_atom();
  for (;;) {
    if (issym(".1")) { ti++; t = ast1(A_FST, t); }
    else if (issym(".2")) { ti++; t = ast1(A_SND, t); }
    else if (issym("@")) { ti++; t = ast2(A_PAPP, t, parse_atom()); }
    else return t;
  }
}
static int starts_atom(void) {
  if (stopped()) return 0;
  if (cur()->t == T_ID) return strcmp(cur()->s, "in") != 0;
  return issym("(") || issym("[") || issym("~") || issym("\\") || issym("<");
}

static const struct { const char *name; int arity; } KW[] = {
  {"Path", 3}, {"PathP", 3}, {"comp", 3}, {"compF", 4}, {"Glue", 2}, {"GlueF", 3}, {"glue", 2}, {"glueF", 3},
  {"unglue", 2}, {"unglueF", 3}, {"forall", 1}, {"sel", 1},
  {"pidom", 1}, {"picod", 1}, {"sigdom", 1}, {"sigcod", 1}, {"pfam", 1}, {"pleft", 1}, {"pright", 1},
  {"galpha", 1}, {"gbase", 1}, {"gsys", 1}, {NULL, 0}
};
static int kw_index(const char *s) { for (int i = 0; KW[i].name; i++) if (!strcmp(KW[i].name, s)) return i; return -1; }

static Ast *keyword(int kw, Ast **x) {
  const char *k = KW[kw].name;
  if (!strcmp(k, "Path")) { Ast *l = ast(A_PLAM); l->b = newbind("_"); l->a[0] = x[0]; return ast3(A_PATHT, l, x[1], x[2]); }
  if (!strcmp(k, "PathP")) return ast3(A_PATHT, x[0], x[1], x[2]);
  if (!strcmp(k, "comp")) {
    if (x[1]->k != A_PLAM || x[1]->a[0]->k != A_SYS) perr("comp needs its tube as <i> [ ... ]");
    Ast *t = ast(A_COMP); t->a[0] = x[0]; t->a[1] = sys_phi(x[1]->a[0], x[1]->b); t->a[2] = x[1]; t->a[3] = x[2];
    return t;
  }
  if (!strcmp(k, "compF")) { Ast *t = ast(A_COMP); for (int i = 0; i < 4; i++) t->a[i] = x[i]; return t; }
  if (!strcmp(k, "Glue")) return ast3(A_GLUET, x[0], sys_phi(x[1], NULL), x[1]);
  if (!strcmp(k, "GlueF")) return ast3(A_GLUET, x[0], x[1], x[2]);
  if (!strcmp(k, "glue")) return ast3(A_GLUEE, sys_phi(x[0], NULL), x[0], x[1]);
  if (!strcmp(k, "glueF")) return ast3(A_GLUEE, x[0], x[1], x[2]);
  if (!strcmp(k, "unglue")) {     /* Unglue keeps the glue-type data (§16) */
    if (x[0]->k == A_GLUET) return ast3(A_UNGLUEF, x[0]->a[1], x[0]->a[2], x[1]);
    return ast2(A_UNGLUE, x[0], x[1]);
  }
  if (!strcmp(k, "unglueF")) return ast3(A_UNGLUEF, x[0], x[1], x[2]);
  if (!strcmp(k, "forall")) return ast1(A_FORALL, x[0]);
  if (!strcmp(k, "sel")) return ast1(A_SEL, x[0]);
  static const struct { const char *n; int k; } PJ[] = {
    {"pidom", K_PIDOM}, {"picod", K_PICOD}, {"sigdom", K_SIGDOM}, {"sigcod", K_SIGCOD}, {"pfam", K_PFAM},
    {"pleft", K_PLEFT}, {"pright", K_PRIGHT}, {"galpha", K_GALPHA}, {"gbase", K_GBASE}, {"gsys", K_GSYS}, {NULL, 0}
  };
  for (int i = 0; PJ[i].n; i++) if (!strcmp(k, PJ[i].n)) { Ast *t = ast1(A_PROJ, x[0]); t->proj = PJ[i].k; return t; }
  die("internal: keyword %s", k); return NULL;
}
static Ast *parse_keyword(void) {
  int kw = kw_index(cur()->s); ti++;
  Ast *x[4];
  for (int i = 0; i < KW[kw].arity; i++) { if (!starts_atom()) perr("too few arguments to a primitive"); x[i] = parse_atom_post(); }
  return keyword(kw, x);
}
static Ast *parse_app(void) {
  Ast *t = parse_atom_post();
  while (starts_atom()) t = ast2(A_APP, t, parse_atom_post());
  return t;
}
static Ast *parse_and(void) {
  Ast *t = parse_app();
  for (;;) {
    if (issym("&&")) { ti++; t = ast2(A_MEET, t, parse_app()); }
    else if (issym("/\\")) { ti++; t = ast2(A_FAND, t, parse_app()); }
    else return t;
  }
}
static Ast *parse_or(void) {
  Ast *t = parse_and();
  for (;;) {
    if (issym("||")) { ti++; t = ast2(A_JOIN, t, parse_and()); }
    else if (issym("\\/")) { ti++; t = ast2(A_FOR, t, parse_and()); }
    else return t;
  }
}
static Ast *parse_prod(void) {
  Ast *l = parse_or();
  if (issym("*")) { ti++; Ast *r = parse_prod(); Ast *t = ast2(A_SIG, l, r); t->b = newbind("_"); return t; }
  return l;
}
static Ast *parse_arrow(void) {
  Ast *l = parse_prod();
  if (issym("->")) { ti++; Ast *r = parse_term(); Ast *t = ast2(A_PI, l, r); t->b = newbind("_"); return t; }
  return l;
}
static int binder_group_ahead(void) {
  if (!issym("(")) return 0;
  int j = ti + 1, k = 0;
  while (toks[j].t == T_ID && toks[j].col != 0) { j++; k++; }
  return k > 0 && toks[j].t == T_SYM && !strcmp(toks[j].s, ":") && toks[j].col != 0;
}
/* binders of a λ: names, or groups (x y : A) giving each a domain type */
static int parse_binders(Bind **bs, Ast **tys, const char *until) {
  int nb = 0;
  while (!issym(until)) {
    if (binder_group_ahead()) {
      ti++; int first = nb;
      while (cur()->t == T_ID && !issym(":")) { if (nb == 64) perr("too many binders"); bs[nb] = newbind(cur()->s); tys[nb] = NULL; nb++; ti++; }
      expect(":");
      int save = nscope; for (int i = 0; i < first; i++) scope_push(bs[i]);
      Ast *ty = parse_term(); nscope = save; expect(")");
      for (int i = first; i < nb; i++) tys[i] = i == first ? ty : copy_ast(ty, NULL);
      continue;
    }
    if (cur()->t != T_ID || stopped()) perr("a binder is expected");
    if (nb == 64) perr("too many binders");
    bs[nb] = newbind(cur()->s); tys[nb] = NULL; nb++; ti++;
  }
  return nb;
}
static Ast *parse_term(void) {
  if (stopped()) perr("a term is expected");
  if (issym("\\")) {
    ti++; Bind *bs[64]; Ast *tys[64];
    int save = nscope;
    /* each binder's type may mention the earlier binders */
    int nb = parse_binders(bs, tys, "->");
    expect("->");
    for (int i = 0; i < nb; i++) scope_push(bs[i]);
    Ast *body = parse_term(); nscope = save;
    for (int i = nb - 1; i >= 0; i--) { Ast *l = ast(A_LAM); l->b = bs[i]; l->a[0] = body; l->a[1] = tys[i]; body = l; }
    return body;
  }
  if (issym("<")) {
    ti++; Bind *bs[64]; int nb = 0;
    while (!issym(">")) { if (cur()->t != T_ID || stopped()) perr("a dimension is expected"); if (nb == 64) perr("too many binders"); bs[nb++] = newbind(cur()->s); ti++; }
    expect(">");
    int save = nscope; for (int i = 0; i < nb; i++) scope_push(bs[i]);
    Ast *body = parse_term(); nscope = save;
    for (int i = nb - 1; i >= 0; i--) { Ast *l = ast(A_PLAM); l->b = bs[i]; l->a[0] = body; body = l; }
    return body;
  }
  if (isid("let")) {
    ti++; if (cur()->t != T_ID || stopped()) perr("a name is expected after let");
    Bind *b = newbind(cur()->s); ti++;
    expect("="); Ast *val = parse_term();
    if (!isid("in")) perr("expected 'in'");
    ti++;
    int save = nscope; scope_push(b); Ast *body = parse_term(); nscope = save;
    Ast *l = ast(A_LAM); l->b = b; l->a[0] = body;
    return ast2(A_APP, l, val);
  }
  if (binder_group_ahead()) {
    Bind *bs[64]; Ast *tys[64]; int nb = 0; int save = nscope;
    while (binder_group_ahead()) {
      ti++; int first = nb;
      while (cur()->t == T_ID && !issym(":")) { if (nb == 64) perr("too many binders"); bs[nb++] = newbind(cur()->s); ti++; }
      expect(":"); Ast *ty = parse_term(); expect(")");
      for (int i = first; i < nb; i++) { tys[i] = i == first ? ty : copy_ast(ty, NULL); scope_push(bs[i]); }
    }
    int sig = 0;
    if (issym("->")) sig = 0; else if (issym("*")) sig = 1; else perr("expected → or × after a telescope");
    ti++;
    Ast *body = parse_term(); nscope = save;
    for (int i = nb - 1; i >= 0; i--) { Ast *t = ast2(sig ? A_SIG : A_PI, tys[i], body); t->b = bs[i]; body = t; }
    return body;
  }
  return parse_arrow();
}
static Ast *parse_system(void) {
  expect("[");
  Ast *s = ast(A_SYS); int cap = 4; s->fs = xmalloc(cap * sizeof(Ast *)); s->ts = xmalloc(cap * sizeof(Ast *));
  if (issym("]")) { ti++; return s; }
  for (;;) {
    Ast *f = parse_or(); expect("->"); Ast *t = parse_term();
    if (s->n == cap) { cap *= 2; s->fs = xrealloc(s->fs, cap * sizeof(Ast *)); s->ts = xrealloc(s->ts, cap * sizeof(Ast *)); }
    s->fs[s->n] = f; s->ts[s->n] = t; s->n++;
    if (issym(";")) { ti++; continue; }
    expect("]"); return s;
  }
}
static Ast *parse_atom(void) {
  if (stopped()) perr("a term is expected");
  if (issym("~")) { ti++; return ast1(A_NEG, parse_atom_post()); }
  if (issym("\\") || issym("<")) return parse_term();
  if (issym("[")) return parse_system();
  if (issym("(")) {
    ti++; Ast *t = parse_term();
    if (issym("=")) {           /* a face (r = 0) or (r = 1) */
      ti++;
      if (isid("0")) { ti++; expect(")"); return ast1(A_FEQ0, t); }
      if (isid("1")) { ti++; expect(")"); return ast1(A_FEQ1, t); }
      perr("a face compares with 0 or 1");
    }
    if (issym(",")) { ti++; Ast *u = parse_term(); expect(")"); return ast2(A_PAIR, t, u); }
    expect(")"); return t;
  }
  if (cur()->t != T_ID) perr("unexpected symbol");
  const char *s = cur()->s;
  if (s[0] == 'U' && (s[1] == 0 || (s[1] >= '0' && s[1] <= '9'))) { ti++; Ast *t = ast(A_U); t->proj = atoi(s + 1); return t; }
  if (!strcmp(s, "Type")) { ti++; return ast(A_U); }
  static const struct { const char *n; int k; } LIT[] = {
    {"0", A_I0}, {"1", A_I1}, {"top", A_FTOP}, {"bot", A_FBOT}, {"I", A_U}, {NULL, 0}
  };
  for (int i = 0; LIT[i].n; i++) if (!strcmp(s, LIT[i].n)) { ti++; return ast(LIT[i].k); }
  if (kw_index(s) >= 0) return parse_keyword();
  ti++;
  for (int i = nscope - 1; i >= 0; i--)
    if (!strcmp(scope[i]->name, s) && strcmp(s, "_")) { Ast *t = ast(A_VAR); t->b = scope[i]; return t; }
  Ast *t = ast(A_REF); t->def = def_get(s); return t;
}

/* occurrences of each binder, counted after parsing (copies included) */
static void count_uses(Ast *t) {
  if (!t) return;
  if (t->k == A_VAR) { t->b->uses++; return; }
  for (int i = 0; i < 4; i++) count_uses(t->a[i]);
  if (t->k == A_SYS) for (int i = 0; i < t->n; i++) { count_uses(t->fs[i]); count_uses(t->ts[i]); }
}
static void alloc_outs(Ast *t) {
  if (!t) return;
  if (binds(t->k) && !t->b->outs) t->b->outs = xmalloc((t->b->uses ? t->b->uses : 1) * sizeof(Ptr));
  for (int i = 0; i < 4; i++) alloc_outs(t->a[i]);
  if (t->k == A_SYS) for (int i = 0; i < t->n; i++) { alloc_outs(t->fs[i]); alloc_outs(t->ts[i]); }
}
static void finish(Ast *t) { count_uses(t); alloc_outs(t); }

/* ------------------------------------- the identity-agent compiler (§24)
   For p : (γ : Γ) → Path B L R, with L and R construction trees (heads
   applied to arguments), build
     Real(C, y)   the patch of C with its internal wires bound:
                  a leaf (a variable, a constant) is  Path T C y;
                  h a1 … am is Σ over each compound argument ak of
                  (uk : Tk) × Real(ak, uk), ending in Path T (h a1' … am') y,
                  where ak' is uk for a compound argument and ak otherwise;
     c_C : Real(C, y) → Path T C y     ap of h over the arguments' c, then · t;
     c_C⁻¹ : Path T C y → Real(C, y)   the actual values with refl, then w;
   and the programs
     p-forward  γ y u = c_R⁻¹ (compose B R (reverse (p γ)) (c_L u))
     p-backward γ y v = c_L⁻¹ (compose B L (p γ) (c_R v)).                 */

static Bind *ag_bind[64]; static Ast *ag_type[64]; static int ag_n;
static Ast *mkvar(Bind *b) { Ast *t = ast(A_VAR); t->b = b; return t; }
static Ast *mkref(const char *n) { Ast *t = ast(A_REF); t->def = def_get(n); return t; }
static Ast *mkapp(Ast *f, Ast *x) { return ast2(A_APP, f, x); }
static Ast *mkpath(Ast *A, Ast *a, Ast *b) { Ast *l = ast(A_PLAM); l->b = newbind("_"); l->a[0] = copy_ast(A, NULL); return ast3(A_PATHT, l, a, b); }
static Ast *mksig(Bind *b, Ast *A, Ast *B) { Ast *t = ast2(A_SIG, A, B); t->b = b; return t; }

static int spine(Ast *c, Ast **head, Ast **args) {
  int m = 0;
  while (c->k == A_APP) { if (m == 64) die("agent: too many arguments"); args[m++] = c->a[1]; c = c->a[0]; }
  for (int i = 0; i < m / 2; i++) { Ast *t = args[i]; args[i] = args[m - 1 - i]; args[m - 1 - i] = t; }
  *head = c; return m;
}
static int is_node(Ast *c) { Ast *h, *a[64]; return spine(c, &h, a) > 0; }
/* the type of a construction tree, from the telescope and the signatures */
static Ast *infer(Ast *c) {
  Ast *h, *a[64]; int m = spine(c, &h, a);
  Ast *ty = NULL;
  if (h->k == A_VAR) { for (int i = 0; i < ag_n; i++) if (ag_bind[i] == h->b) ty = ag_type[i]; }
  else if (h->k == A_REF && h->def->sig) ty = h->def->sig;
  if (!ty) die("agent: the head of a construction has no known type");
  ty = copy_ast(ty, NULL);
  for (int i = 0; i < m; i++) {
    if (ty->k != A_PI) die("agent: a head is applied beyond its Π type");
    ty = subst_ast(ty->a[1], ty->b, a[i]);
  }
  return ty;
}
static Ast *real(Ast *c, Ast *y) {
  Ast *T = infer(c);
  if (!is_node(c)) return mkpath(T, copy_ast(c, NULL), y);
  Ast *h, *a[64]; int m = spine(c, &h, a);
  Bind *u[64]; Ast *inner = copy_ast(h, NULL);
  for (int k = 0; k < m; k++) {
    if (is_node(a[k])) { u[k] = newbind("u"); inner = mkapp(inner, mkvar(u[k])); }
    else { u[k] = NULL; inner = mkapp(inner, copy_ast(a[k], NULL)); }
  }
  Ast *acc = mkpath(T, inner, y);
  for (int k = m - 1; k >= 0; k--) {
    if (!u[k]) continue;
    acc = mksig(newbind("s"), real(a[k], mkvar(u[k])), acc);
    acc = mksig(u[k], infer(a[k]), acc);
  }
  return acc;
}
/* the components of a packed Real value x: each compound argument gives
   its u then its s; the final path comes last */
static Ast *component(Ast *x, int k, int last) {
  Ast *t = copy_ast(x, NULL);
  for (int i = 0; i < k; i++) t = ast1(A_SND, t);
  return last ? t : ast1(A_FST, t);
}
static Ast *c_fwd(Ast *c, Ast *x) {
  if (!is_node(c)) return copy_ast(x, NULL);
  Ast *T = infer(c);
  Ast *h, *a[64]; int m = spine(c, &h, a);
  int nc = 0; for (int k = 0; k < m; k++) if (is_node(a[k])) nc++;
  /* ap of h over the arguments' paths: <i> h b1(i) … bm(i) */
  Bind *i = newbind("i"); Ast *body = copy_ast(h, NULL); int j = 0;
  for (int k = 0; k < m; k++) {
    if (is_node(a[k])) { Ast *s = component(x, 2 * j + 1, 0); body = mkapp(body, ast2(A_PAPP, c_fwd(a[k], s), mkvar(i))); j++; }
    else body = mkapp(body, copy_ast(a[k], NULL));
  }
  Ast *ap = ast(A_PLAM); ap->b = i; ap->a[0] = body;
  Ast *t = component(x, 2 * nc, 1);
  return mkapp(mkapp(mkapp(mkapp(mkref("compose"), T), copy_ast(c, NULL)), ap), t);
}
static Ast *c_inv(Ast *c, Ast *w) {
  if (!is_node(c)) return w;
  Ast *h, *a[64]; int m = spine(c, &h, a);
  Ast *acc = w;
  for (int k = m - 1; k >= 0; k--) {
    if (!is_node(a[k])) continue;
    Ast *refl = ast(A_PLAM); refl->b = newbind("_"); refl->a[0] = copy_ast(a[k], NULL);
    acc = ast2(A_PAIR, c_inv(a[k], refl), acc);
    acc = ast2(A_PAIR, copy_ast(a[k], NULL), acc);
  }
  return acc;
}
static void gen_agent(const char *name) {
  Def *p = def_find(name);
  if (!p || !p->sig) die("agent %s: no signature", name);
  Ast *ty = p->sig; ag_n = 0;
  while (ty->k == A_PI) { if (ag_n == 64) die("agent: telescope too long"); ag_bind[ag_n] = ty->b; ag_type[ag_n] = ty->a[0]; ag_n++; ty = ty->a[1]; }
  if (ty->k != A_PATHT || ty->a[0]->k != A_PLAM) die("agent %s: the signature does not end in Path B L R", name);
  Ast *B = ty->a[0]->a[0], *L = ty->a[1], *R = ty->a[2];
  /* p γ */
  Ast *pg = mkref(name); for (int i = 0; i < ag_n; i++) pg = mkapp(pg, mkvar(ag_bind[i]));
  for (int side = 0; side < 4; side++) {
    Bind *y = newbind("y"), *u = newbind(side < 2 ? "u" : "_");
    Ast *body; const char *suffix;
    if (side == 0) {          /* forward */
      Ast *sym = ast(A_PLAM); Bind *i = newbind("i"); sym->b = i; sym->a[0] = ast2(A_PAPP, copy_ast(pg, NULL), ast1(A_NEG, mkvar(i)));
      body = c_inv(R, mkapp(mkapp(mkapp(mkapp(mkref("compose"), copy_ast(B, NULL)), copy_ast(R, NULL)), sym), c_fwd(L, mkvar(u))));
      suffix = "-forward";
    } else if (side == 1) {   /* backward */
      body = c_inv(L, mkapp(mkapp(mkapp(mkapp(mkref("compose"), copy_ast(B, NULL)), copy_ast(L, NULL)), copy_ast(pg, NULL)), c_fwd(R, mkvar(u))));
      suffix = "-backward";
    } else { body = real(side == 2 ? L : R, mkvar(y)); suffix = side == 2 ? "-realL" : "-realR"; }
    if (side < 2) { Ast *l = ast(A_LAM); l->b = u; l->a[0] = body; body = l; }
    Ast *l = ast(A_LAM); l->b = y; l->a[0] = body; body = l;
    for (int i = ag_n - 1; i >= 0; i--) { Ast *g = ast(A_LAM); g->b = ag_bind[i]; g->a[0] = body; body = g; }
    /* renew every binder so the generated term owns its own binders */
    body = copy_ast(body, NULL);
    char nm[256]; snprintf(nm, sizeof nm, "%s%s", name, suffix);
    Def *d = def_get(nm); if (d->body) die("%s is defined twice", nm);
    finish(body); d->body = body;
  }
}

static char **agents; static int *agent_rule; static int nagents;

/* An identity p : (γ : Γ) → Path B L R generates interaction rules:
   - L = f t1 … tn, f a postulated construction and each ti a pattern (a
     variable of γ, or a postulated construction applied to patterns), each
     variable of γ occurring exactly once: f becomes the head of a matching
     automaton and every construction in the patterns a constructor agent;
   - L = compF (<_> T) φ u c, T a postulated type and φ u c the variables
     of γ: the Kan identity of T, applied when a composition meets T.
   The right side is the generated term p-rhs γ.  A variable occurs once
   because matching it twice would need an equality test, which the machine
   does not have; a left face with no construction to inspect is a
   definition, not an interaction.                                          */
static int pi_count(Ast *t) { int n = 0; while (t && t->k == A_PI) { n++; t = t->a[1]; } return n; }
static Pat *mkpat(Ast *t, Bind **g, int ng, int *used, const char *name) {
  Pat *p = xmalloc(sizeof *p); memset(p, 0, sizeof *p);
  if (t->k == A_VAR) {
    int i; for (i = 0; i < ng; i++) if (g[i] == t->b) break;
    if (i == ng || used[i]) die("rule %s: %s is not a fresh variable of the telescope", name, t->b->name);
    used[i] = 1; p->b = t->b; return p;
  }
  Ast *h, *a[64]; int m = spine(t, &h, a);
  if (h->k != A_REF || h->def->body) die("rule %s: a pattern must apply a postulated construction", name);
  Def *c = h->def;
  if (m > MAXARITY || pi_count(c->sig) != m) die("rule %s: %s must be fully applied", name, c->name);
  if (c->role == 2) die("rule %s: %s is both a head and a constructor", name, c->name);
  c->role = 1; c->arity = m; p->ctor = c->id; p->n = m;
  for (int q = 0; q < m; q++) p->sub[q] = mkpat(a[q], g, ng, used, name);
  return p;
}
static Def *gen_rhs(const char *name, Bind **g, int ng, Ast *R) {
  Ast *body = R;
  for (int i = ng - 1; i >= 0; i--) { Ast *l = ast(A_LAM); l->b = g[i]; l->a[0] = body; body = l; }
  body = copy_ast(body, NULL);
  char nm[256]; snprintf(nm, sizeof nm, "%s-rhs", name);
  Def *d = def_get(nm); if (d->body) die("%s is defined twice", nm);
  finish(body); d->body = body; return d;
}
static void gen_rule(const char *name) {
  Def *p = def_find(name);
  if (!p || !p->sig) die("rule %s: no signature", name);
  Ast *ty = p->sig; Bind *g[64]; int ng = 0;
  while (ty->k == A_PI) { if (ng == 64) die("rule: telescope too long"); g[ng++] = ty->b; ty = ty->a[1]; }
  if (ty->k != A_PATHT) die("rule %s: the signature does not end in a path type", name);
  Ast *L = ty->a[1], *R = ty->a[2];
  if (L->k == A_COMP) {
    Ast *line = L->a[0];
    if (line->k != A_PLAM || line->b->uses || line->a[0]->k != A_REF || line->a[0]->def->body)
      die("rule %s: a Kan identity composes in a constant postulated type", name);
    Def *T0 = line->a[0]->def;
    if (ng != 3) die("rule %s: a Kan identity binds exactly φ u c", name);
    if (T0->kan_rhs >= 0) die("rule %s: %s already has a Kan identity", name, T0->name);
    for (int i = 0; i < 3; i++) {
      int which = -1;
      for (int w = 1; w <= 3; w++) if (L->a[w]->k == A_VAR && L->a[w]->b == g[i]) which = w == 1 ? 0 : w == 2 ? 1 : 2;
      if (which < 0) die("rule %s: φ, u and c must be the variables of the telescope", name);
      T0->kan_perm[i] = which;
    }
    T0->kan_rhs = gen_rhs(name, g, ng, R)->id;
    return;
  }
  Ast *h, *a[64]; int n = spine(L, &h, a);
  if (h->k != A_REF || h->def->body || n == 0) die("rule %s: the left face must apply a postulated construction", name);
  Def *f = h->def;
  if (n > MAXARITY || pi_count(f->sig) != n) die("rule %s: %s must be fully applied", name, f->name);
  if (f->role == 1) die("rule %s: %s is both a head and a constructor", name, f->name);
  f->role = 2; f->arity = n;
  int used[64] = {0};
  GRule r; memset(&r, 0, sizeof r); r.f = f->id; r.n = n; r.ng = ng;
  for (int i = 0; i < ng; i++) r.g[i] = g[i];
  for (int j = 0; j < n; j++) r.args[j] = mkpat(a[j], g, ng, used, name);
  for (int i = 0; i < ng; i++) if (!used[i]) die("rule %s: %s does not occur in the left face", name, g[i]->name);
  r.rhs = gen_rhs(name, g, ng, R);
  if (ngrules == 64) die("more than 64 rules");
  grules = xrealloc(grules, (ngrules + 1) * sizeof *grules); grules[ngrules++] = r;
}
/* the matching automaton of a head, state by state */
static int new_state(void) {
  mst = xrealloc(mst, (nmst + 1) * sizeof *mst); memset(&mst[nmst], 0, sizeof *mst); mst[nmst].fire = -1; return nmst++;
}
static void build_state(int st) {
  int ins = -1;
  for (int i = 0; i < mst[st].nslots && ins < 0; i++)
    for (int r = 0; r < ngrules; r++) {
      if (!(mst[st].cand >> r & 1)) continue;
      Pat *q = pat_at(&grules[r], &mst[st].slots[i]);
      if (q && !q->b) { ins = i; break; }
    }
  if (ins < 0) {
    int cnt = 0, which = -1;
    for (int r = 0; r < ngrules; r++) if (mst[st].cand >> r & 1) { cnt++; which = r; }
    if (cnt != 1) die("the rules for %s overlap", defs[mst[st].f]->name);
    mst[st].fire = which; return;
  }
  mst[st].inspect = ins;
  int ctors[64], nc = 0;
  for (int r = 0; r < ngrules; r++) {
    if (!(mst[st].cand >> r & 1)) continue;
    Pat *q = pat_at(&grules[r], &mst[st].slots[ins]);
    if (!q || q->b) continue;
    int seen = 0; for (int k = 0; k < nc; k++) if (ctors[k] == q->ctor) seen = 1;
    if (!seen) ctors[nc++] = q->ctor;
  }
  for (int k = 0; k < nc; k++) {
    int c = ctors[k], m = defs[c]->arity, ns = new_state();
    MState *a = &mst[st], *b = &mst[ns];
    b->f = a->f; b->n = a->n;
    if (a->nslots - 1 + m > MAXSLOT || a->slots[ins].len + 1 > MAXPATH) die("the patterns for %s nest too deep", defs[a->f]->name);
    for (int i = 0; i < a->nslots; i++) {
      if (i != ins) { b->slots[b->nslots++] = a->slots[i]; continue; }
      for (int q = 0; q < m; q++) { Path p = a->slots[i]; p.ix[p.len++] = q; b->slots[b->nslots++] = p; }
    }
    for (int r = 0; r < ngrules; r++) {
      if (!(a->cand >> r & 1)) continue;
      Pat *q = pat_at(&grules[r], &a->slots[ins]);
      if (!q || q->b || q->ctor == c) b->cand |= (uint64_t)1 << r;
    }
    b->nm = a->nm; memcpy(b->mpath, a->mpath, sizeof a->mpath); memcpy(b->mctor, a->mctor, sizeof a->mctor);
    if (b->nm == MAXSLOT) die("the patterns for %s nest too deep", defs[a->f]->name);
    b->mpath[b->nm] = a->slots[ins]; b->mctor[b->nm] = c; b->nm++;
    a->tctor[a->nt] = c; a->tnext[a->nt] = ns; a->nt++;
    build_state(ns);
  }
}
static void build_automata(void) {
  for (int d = 0; d < ndefs; d++) {
    if (defs[d]->role != 2) continue;
    int st = new_state(); defs[d]->st0 = st;
    mst[st].f = d; mst[st].n = defs[d]->arity; mst[st].nslots = defs[d]->arity;
    for (int j = 0; j < defs[d]->arity; j++) { mst[st].slots[j].len = 1; mst[st].slots[j].ix[0] = j; }
    for (int r = 0; r < ngrules; r++) if (grules[r].f == d) mst[st].cand |= (uint64_t)1 << r;
    build_state(st);
    if (mst[st].fire >= 0) die("rule for %s inspects nothing: it is a definition", defs[d]->name);
  }
}

static void parse_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) die("cannot open %s", path);
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = xmalloc((size_t)n + 1); if (fread(src, 1, (size_t)n, f) != (size_t)n) die("cannot read %s", path);
  src[n] = 0; fclose(f);
  ntoks = 0; ti = 0; lex(src, path);
  while (cur()->t != T_EOF) {
    if (cur()->t != T_ID || cur()->col != 0) perr("a declaration starts with a name in the first column");
    if ((!strcmp(cur()->s, "agent") || !strcmp(cur()->s, "rule")) && toks[ti + 1].t == T_ID && toks[ti + 1].col != 0) {
      agents = xrealloc(agents, (nagents + 1) * sizeof *agents);
      agent_rule = xrealloc(agent_rule, (nagents + 1) * sizeof *agent_rule);
      agent_rule[nagents] = !strcmp(cur()->s, "rule");
      agents[nagents++] = xstrdup(toks[ti + 1].s);
      ti += 2; continue;
    }
    Def *d = def_get(cur()->s); ti++;
    if (issym(":")) { ti++; nscope = 0; d->sig = parse_term(); d->has_sig = 1; finish(d->sig); continue; }
    if (d->body) perr("defined twice");
    nscope = 0; Bind *bs[64]; Ast *tys[64];
    int nb = parse_binders(bs, tys, "=");
    expect("=");
    for (int i = 0; i < nb; i++) scope_push(bs[i]);
    Ast *body = parse_term();
    if (!stopped()) perr("unexpected text after a definition");
    /* argument domains from the signature's telescope, where given */
    Ast *sg = d->sig;
    for (int i = 0; i < nb; i++) {
      if (!tys[i] && sg && sg->k == A_PI) {
        tys[i] = copy_ast(sg->a[0], NULL);          /* earlier binders already renamed to the arguments */
      }
      if (sg && sg->k == A_PI) sg = subst_ast(sg->a[1], sg->b, mkvar(bs[i]));
      else sg = NULL;
    }
    for (int i = nb - 1; i >= 0; i--) { Ast *l = ast(A_LAM); l->b = bs[i]; l->a[0] = body; l->a[1] = tys[i]; body = l; }
    finish(body);
    d->body = body;
  }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
  const char *core = NULL; int i = 1;
  if (i + 1 < argc && !strcmp(argv[i], "-p")) { core = argv[i + 1]; i += 2; }
  if (argc - i != 2) { fprintf(stderr, "usage: hcm [-p core.ctt] file.ctt name\n"); return 2; }
  char buf[4096];
  if (!core) {
    const char *slash = strrchr(argv[0], '/');
    if (slash) snprintf(buf, sizeof buf, "%.*s/core.ctt", (int)(slash - argv[0]), argv[0]);
    else snprintf(buf, sizeof buf, "core.ctt");
    core = buf;
  }
  mk(K_FREE);
  parse_file(core);
  parse_file(argv[i]);
  for (int j = 0; j < nagents; j++) if (agent_rule[j]) gen_rule(agents[j]);
  build_automata();
  for (int j = 0; j < nagents; j++) if (!agent_rule[j]) gen_agent(agents[j]);
  con_arity = xmalloc((ndefs + 1) * sizeof(int));
  for (int j = 0; j < ndefs; j++) con_arity[j] = defs[j]->arity;
  for (int j = 0; j < ndefs; j++) {
    if (defs[j]->body) continue;
    if (!defs[j]->has_sig) die("unknown name %s", defs[j]->name);
    defs[j]->atom = newname(defs[j]->name);
  }
  natom_def = nnames; atom_def = xmalloc((nnames + 1) * sizeof(int));
  for (int j = 0; j < nnames; j++) atom_def[j] = -1;
  for (int j = 0; j < ndefs; j++) if (defs[j]->atom >= 0) atom_def[defs[j]->atom] = j;
  Def *d = def_find(argv[i + 1]); if (!d) die("no definition named %s", argv[i + 1]);
  uint32_t root = mk(K_ROOT);
  lnk(P(root, 1), build_def(d->id));
  Buf o = {0}; rb(P(root, 1), &o);
  printf("%s\n", o.s ? o.s : "");
  printf("-- %llu interactions (%llu erasures, %llu unfoldings)\n", steps, erasures, unfolds);
  return 0;
}

/* net/net.c -- optimal reduction by interaction, for the lambda calculus
 * with data.
 *
 * Owner's requirement (NET_SPEC 7, and the binder correction): duplication
 * and substitution under binders follow Lamping 1990 / Asperti-Guerrini
 * 1998, "The Optimal Implementation of Functional Programming Languages",
 * pp. 40-42: a binder is its body subnet (LAM(x,t) >< APP(r,a) -> x=a,
 * t=r), and sharing goes through fans, DUP_k(SUP_k(a,b)) -> (a,b).
 *
 * Transcribed, not invented.  Sources:
 *   [AG]  the rule set and initial encoding of Asperti-Guerrini pp. 40-42,
 *         as stated in Salikhmetov, "Token-passing Optimal Reduction with
 *         Embedded Read-back", EPTCS 225 (2016), section 4, and as carried
 *         by codedot/lambda, encoding/standard/{index.js,template.txt};
 *   [RB]  read-back: the same paper, section 7, and the same template.
 *
 * Data (the owner's correction: a datatype is its construction, a tag adds
 * no semantics).  A datatype's construction is its Scott encoding:
 *     K e1..em  =  \c1..cn. c_k e1..em        T s B1..Bn  =  s B1..Bn
 * Encoded by [AG] at level l, the fields e_j are arguments (level l+1,
 * bracketed), each branch B_k an argument, and c_k an occurrence (a
 * croissant).  CON_l and CASE_l are that encoding with its binders already
 * met, so read-back can name the constructor:
 *     CASE_l[r, B1..Bn] >< CON_l^k[e1..em]
 *       -> r = APP_l(..APP_l(CRO_l(B_k), e1).., em),  other B_j erased
 * which is exactly the n beta steps of the Scott term followed by the
 * croissant at c_k's occurrence.  It counts as n beta steps.  CON and CASE
 * take the [AG] propagation rules of any agent alpha_j.
 *
 * Agents:
 *   LAM_l  principal: function;  aux 0: bound variable; aux 1: body
 *   APP_l  principal: function;  aux 0: result;         aux 1: argument
 *   CON_l  principal: value;     aux j: field j
 *   CASE_l principal: scrutinee; aux 0: result;         aux 1+k: branch k
 *   FAN_l, BRA_l, CRO_l, ERA     as [AG] (delta, t, e, epsilon)
 *   ATOM   a free variable, or a variable read-back put in a binder
 *   NAPP   an application whose head is neutral; aux: head, argument
 *   NCASE  a case whose scrutinee is neutral; aux: scrutinee, branches
 *   ROOT   a place read-back reads from; it never interacts
 *
 * Output: the normal form and its length (5.6), the number of
 * interactions.  Interactions that exist only because read-back put an
 * atom in a binder are counted apart (5.21).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>

static void die(const char *fmt, ...) {
  va_list ap; va_start(ap, fmt);
  fprintf(stderr, "net: "); vfprintf(stderr, fmt, ap); fprintf(stderr, "\n");
  va_end(ap); exit(1);
}
static void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xgrow(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static char *xdup(const char *s) { char *d = xalloc(strlen(s) + 1); strcpy(d, s); return d; }
#define PUSH(arr, n, cap, v) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 16; \
    (arr) = xgrow((arr), sizeof(*(arr)) * (cap)); } (arr)[(n)++] = (v); } while (0)

/* ------------------------------------------------------------------------
 * Data declarations
 * ---------------------------------------------------------------------- */
typedef struct { char *name; int data, index, arity; } Con;
typedef struct { char *name; int ncon, first; } Data;
static Con *cons; static int ncons, capcons;
static Data *datas; static int ndatas, capdatas;
static int findCon(const char *s) { for (int i = 0; i < ncons; i++) if (!strcmp(cons[i].name, s)) return i; return -1; }
static int findData(const char *s) { for (int i = 0; i < ndatas; i++) if (!strcmp(datas[i].name, s)) return i; return -1; }

/* ------------------------------------------------------------------------
 * Source syntax: codedot/lambda's grammar, with data and let.
 *   text : (def | data)* term
 *   def  : NAME '=' term ';'
 *   data : 'data' NAME '=' con ('|' con)* ';'      con : NAME NAME*
 *   term : NAME ',' abst-rest | NAME ':' term
 *        | 'let' NAME '=' term 'in' term | appl
 *   appl : atom+              atom : '(' term ')' | NAME
 * A constructor applied to its fields builds data; a datatype's name
 * applied to a scrutinee and one branch per constructor takes it apart.
 * Comments are {...} and # to end of line.
 * ---------------------------------------------------------------------- */
enum { TV, TL, TA, TK, TC };
typedef struct T { int k; char *name; int w, free, tag, n; struct T **ch; } T;
static T *tmk(int k, const char *name, int n) {
  T *t = xalloc(sizeof *t); t->k = k; t->name = name ? xdup(name) : NULL; t->w = -1; t->n = n;
  t->ch = xalloc(sizeof(T *) * (n ? n : 1)); return t;
}
static T *tv(const char *x) { return tmk(TV, x, 0); }
static T *tl(const char *x, T *b) { T *t = tmk(TL, x, 1); t->ch[0] = b; return t; }
static T *ta(T *f, T *a) { T *t = tmk(TA, NULL, 2); t->ch[0] = f; t->ch[1] = a; return t; }

static char **tok; static int ntok, captok, pos;
static int namech(int c) { return c && !isspace(c) && !strchr("{}#=;,:()|", c); }
static void lex(const char *s) {
  while (*s) {
    if (isspace((unsigned char)*s)) { s++; continue; }
    if (*s == '#') { while (*s && *s != '\n') s++; continue; }
    if (*s == '{') { while (*s && *s != '}') s++; if (*s) s++; continue; }
    if (*s == '}') die("unbalanced '}'");
    const char *b = s;
    if (strchr("=;,:()|", *s)) s++;
    else while (namech((unsigned char)*s)) s++;
    char *t = xalloc(s - b + 1); memcpy(t, b, s - b);
    PUSH(tok, ntok, captok, t);
  }
}
static const char *pk(int k) { return pos + k < ntok ? tok[pos + k] : ""; }
static int isname(const char *t) { return *t && namech((unsigned char)*t); }
static const char *nxt(void) { if (pos >= ntok) die("unexpected end of input"); return tok[pos++]; }
static void want(const char *s) { if (strcmp(pk(0), s)) die("expected '%s', got '%s'", s, pk(0)); pos++; }
static int isLet(void) { return !strcmp(pk(0), "let") && isname(pk(1)) && !strcmp(pk(2), "="); }

static T *pterm(void);
static T *patom(void) {
  if (!strcmp(pk(0), "(")) { pos++; T *t = pterm(); want(")"); return t; }
  if (!isname(pk(0))) die("unexpected '%s'", pk(0));
  return tv(nxt());
}
static T *pabst(void) {           /* NAME (',' NAME)* ':' term */
  const char *x = nxt();
  if (!strcmp(pk(0), ",")) { pos++; return tl(x, pabst()); }
  want(":");
  return tl(x, pterm());
}
static T *pterm(void) {
  if (isLet()) {
    pos++; const char *x = nxt(); pos++;
    T *v = pterm(); want("in");
    return ta(tl(x, pterm()), v);
  }
  if (isname(pk(0)) && (!strcmp(pk(1), ",") || !strcmp(pk(1), ":"))) return pabst();
  T *t = patom();
  while (!strcmp(pk(0), "(") || (isname(pk(0)) && strcmp(pk(0), "in"))) t = ta(t, patom());
  return t;
}
typedef struct { char *name; T *def; } Def;
static Def *defs; static int ndefs, capdefs;
static T *ptext(void) {
  for (;;) {
    if (!strcmp(pk(0), "data") && isname(pk(1)) && !strcmp(pk(2), "=")) {
      pos++; Data d; d.name = xdup(nxt()); pos++; d.first = ncons; d.ncon = 0;
      if (findData(d.name) >= 0) die("datatype %s declared twice", d.name);
      for (;;) {
        Con c; c.name = xdup(nxt()); c.data = ndatas; c.index = d.ncon++; c.arity = 0;
        if (findCon(c.name) >= 0) die("constructor %s declared twice", c.name);
        while (isname(pk(0))) { pos++; c.arity++; }
        PUSH(cons, ncons, capcons, c);
        if (!strcmp(pk(0), "|")) { pos++; continue; }
        want(";"); break;
      }
      PUSH(datas, ndatas, capdatas, d);
      continue;
    }
    if (isname(pk(0)) && !strcmp(pk(1), "=")) {
      Def d; d.name = xdup(nxt()); pos++; d.def = pterm(); want(";");
      PUSH(defs, ndefs, capdefs, d);
      continue;
    }
    break;
  }
  T *t = pterm();
  if (pos != ntok) die("trailing '%s'", pk(0));
  return t;
}

/* Free names of a source term (constructor and datatype names are not). */
typedef struct { char **s; int n, cap; } Names;
static int hasName(Names *v, const char *x) { for (int i = 0; i < v->n; i++) if (!strcmp(v->s[i], x)) return 1; return 0; }
static void freeNames(T *t, char **bound, int nb, Names *out) {
  if (t->k == TV) {
    for (int i = 0; i < nb; i++) if (!strcmp(bound[i], t->name)) return;
    if (findCon(t->name) >= 0 || findData(t->name) >= 0) return;
    if (!hasName(out, t->name)) PUSH(out->s, out->n, out->cap, t->name);
    return;
  }
  if (t->k == TL) {
    char **b2 = xalloc(sizeof(char *) * (nb + 1)); memcpy(b2, bound, sizeof(char *) * nb); b2[nb] = t->name;
    freeNames(t->ch[0], b2, nb + 1, out); free(b2); return;
  }
  for (int i = 0; i < t->n; i++) freeNames(t->ch[i], bound, nb, out);
}
/* Definitions, as codedot/lambda generic.js expand(): latest first, each
 * used one wraps the term as (\name. term) def.  A definition is therefore
 * one shared subnet, bound once and fanned to its uses. */
static T *expand(T *t) {
  for (int i = ndefs - 1; i >= 0; i--) {
    Names fv = { 0 }; freeNames(t, NULL, 0, &fv);
    if (hasName(&fv, defs[i].name)) t = ta(tl(defs[i].name, t), defs[i].def);
    free(fv.s);
  }
  return t;
}

/* alpha (generic.js): each binder gets a wire; an occurrence names its
 * binder's wire; a free name stays free.  A constructor or a datatype's
 * eliminator applied to its arguments becomes TK or TC; with too few it is
 * eta-expanded, with too many the rest are applied. */
static int nwires, etaCtr;
typedef struct Env { const char *x; int w; struct Env *up; } Env;
static int bound(Env *e, const char *x) { for (; e; e = e->up) if (!strcmp(e->x, x)) return e->w; return -1; }
static T *alpha(T *t, Env *e);
static T *saturate(int kind, int tag, int need, T **args, int nargs, Env *e) {
  /* args are source terms; build kind node with `need` children */
  T *body = tmk(kind, NULL, need); body->tag = tag;
  int have = nargs < need ? nargs : need;
  T *wrapped = body; char **names = xalloc(sizeof(char *) * (need + 1));
  for (int i = have; i < need; i++) { char b[32]; snprintf(b, sizeof b, "%%eta%d", ++etaCtr); names[i] = xdup(b); }
  /* binders for the missing arguments, outermost first */
  for (int i = need - 1; i >= have; i--) wrapped = tl(names[i], wrapped);
  /* now alpha the whole: children are filled before alpha via source terms */
  for (int i = 0; i < have; i++) body->ch[i] = args[i];
  for (int i = have; i < need; i++) body->ch[i] = tv(names[i]);
  T *r = wrapped;
  for (int i = need; i < nargs; i++) r = ta(r, args[i]);
  return alpha(r, e);
}
static T *alpha(T *t, Env *e) {
  if (t->k == TA || t->k == TV) {
    /* spine */
    T *h = t; int n = 0;
    while (h->k == TA) { n++; h = h->ch[0]; }
    if (h->k == TV && bound(e, h->name) < 0) {
      int c = findCon(h->name), d = findData(h->name);
      if (c >= 0 || d >= 0) {
        T **args = xalloc(sizeof(T *) * (n + 1)); T *s = t;
        for (int i = n - 1; i >= 0; i--) { args[i] = s->ch[1]; s = s->ch[0]; }
        if (c >= 0) return saturate(TK, c, cons[c].arity, args, n, e);
        return saturate(TC, d, 1 + datas[d].ncon, args, n, e);
      }
    }
  }
  if (t->k == TV) {
    T *v = tv(t->name); int w = bound(e, t->name);
    if (w >= 0) v->w = w; else v->free = 1;
    return v;
  }
  if (t->k == TL) {
    Env e2 = { t->name, nwires++, e };
    T *l = tl(t->name, alpha(t->ch[0], &e2)); l->w = e2.w; return l;
  }
  T *r = tmk(t->k, t->name, t->n); r->tag = t->tag;
  for (int i = 0; i < t->n; i++) r->ch[i] = alpha(t->ch[i], e);
  return r;
}
typedef struct { int *w, n, cap; } Wires;
static int hasW(Wires *v, int w) { for (int i = 0; i < v->n; i++) if (v->w[i] == w) return 1; return 0; }
static void fvW(T *t, Wires *out) {          /* bound wires free in t */
  if (t->k == TV) { if (!t->free && !hasW(out, t->w)) PUSH(out->w, out->n, out->cap, t->w); return; }
  if (t->k == TL) {
    Wires in = { 0 }; fvW(t->ch[0], &in);
    for (int i = 0; i < in.n; i++) if (in.w[i] != t->w && !hasW(out, in.w[i])) PUSH(out->w, out->n, out->cap, in.w[i]);
    free(in.w); return;
  }
  for (int i = 0; i < t->n; i++) fvW(t->ch[i], out);
}
static void rename(T *t, int from, int to) {
  if (t->k == TV) { if (!t->free && t->w == from) t->w = to; return; }
  for (int i = 0; i < t->n; i++) rename(t->ch[i], from, to);
}

/* ------------------------------------------------------------------------
 * The net
 * ---------------------------------------------------------------------- */
enum { LAM, APP, CON, CASE, FAN, BRA, CRO, ERA, ATOM, NAPP, NCASE, ROOT, NKIND };
static const char *kname[NKIND] = { "LAM", "APP", "CON", "CASE", "FAN", "BRA", "CRO", "ERA", "ATOM", "NAPP", "NCASE", "ROOT" };
typedef struct { int n, p; } PR;
/* lev: the level; for ATOM its label; for NAPP and NCASE 1 when read-back
 * made it.  tag: the constructor (CON) or datatype (CASE, NCASE). */
typedef struct { int kind, tag, ar; long lev; PR *port; } Node;
static Node *nodes; static int nnodes, capnodes;
static int arityOf(int kind, int tag) {
  switch (kind) {
  case LAM: case APP: case FAN: case NAPP: return 2;
  case BRA: case CRO: return 1;
  case CON: return cons[tag].arity;
  case CASE: case NCASE: return 1 + datas[tag].ncon;
  default: return 0;
  }
}
static int alloc(int kind, long lev, int tag) {
  Node x; memset(&x, 0, sizeof x); x.kind = kind; x.lev = lev; x.tag = tag; x.ar = arityOf(kind, tag);
  x.port = xalloc(sizeof(PR) * (x.ar + 1));
  for (int i = 0; i <= x.ar; i++) x.port[i].n = -1;
  PUSH(nodes, nnodes, capnodes, x); return nnodes - 1;
}
static PR pr(int n, int p) { PR r = { n, p }; return r; }
static PR partner(PR a) { return nodes[a.n].port[a.p]; }
static void link(PR a, PR b) { nodes[a.n].port[a.p] = b; nodes[b.n].port[b.p] = a; }
static int prEq(PR a, PR b) { return a.n == b.n && a.p == b.p; }
static int prLess(PR a, PR b) { return a.n < b.n || (a.n == b.n && a.p < b.p); }

/* Wires of the initial encoding: each name occurs exactly twice. */
static PR *wfirst; static int capw;
static void attach(int w, PR p) {
  if (w >= capw) { int nc = w * 2 + 64; wfirst = xgrow(wfirst, sizeof(PR) * nc); for (int i = capw; i < nc; i++) wfirst[i].n = -1; capw = nc; }
  if (wfirst[w].n < 0) { wfirst[w] = p; return; }
  if (wfirst[w].n == -2) die("internal: wire %d used three times", w);
  link(wfirst[w], p); wfirst[w].n = -2;
}

static char **labels; static int nlabels, caplabels;
static long intern(const char *s) {
  for (int i = 0; i < nlabels; i++) if (!strcmp(labels[i], s)) return i;
  PUSH(labels, nlabels, caplabels, xdup(s)); return nlabels - 1;
}

/* Initial encoding [AG pp. 41-42] (codedot/lambda encoding/standard
 * gamma()), with a node of several children read as the nested binary
 * applications it abbreviates: APP is (f a); CASE is (((s B1) B2) ..);
 * CON is the constant applied to its fields.  The child in function
 * position is at the node's level; every other child is an argument, one
 * level deeper, its free variables bracketed at the node's level; a
 * variable used by several children is fanned at the node's level, the
 * last child against the rest first (psi of the nested applications). */
static void gamma(T *t, int root, long lvl) {
  if (t->k == TV) {
    if (t->free) { int a = alloc(ATOM, intern(t->name), 0); attach(root, pr(a, 0)); return; }
    int c = alloc(CRO, lvl, 0);                        /* name = \cro_{lvl}(root) */
    attach(t->w, pr(c, 0)); attach(root, pr(c, 1));
    return;
  }
  if (t->k == TL) {                                    /* root = \lam_{lvl}(agent, wire) */
    int l = alloc(LAM, lvl, 0);
    attach(root, pr(l, 0));
    Wires fv = { 0 }; fvW(t->ch[0], &fv);
    if (hasW(&fv, t->w)) attach(t->w, pr(l, 1));
    else { int e = alloc(ERA, 0, 0); link(pr(l, 1), pr(e, 0)); }
    free(fv.w);
    int bw = nwires++; attach(bw, pr(l, 2));
    gamma(t->ch[0], bw, lvl);
    return;
  }
  int n = t->n, fun = (t->k == TA || t->k == TC);     /* child 0 in function position */
  /* psi: variables used by several children */
  Wires all = { 0 };
  Wires *fv = xalloc(sizeof(Wires) * n);
  for (int i = 0; i < n; i++) { fvW(t->ch[i], &fv[i]); for (int j = 0; j < fv[i].n; j++) if (!hasW(&all, fv[i].w[j])) PUSH(all.w, all.n, all.cap, fv[i].w[j]); }
  typedef struct { int orig, child, rest; } Twin;
  Twin *tw = NULL; int ntw = 0, captw = 0;
  for (int v = 0; v < all.n; v++) {
    int w = all.w[v], cur = w, users = 0;
    for (int i = 0; i < n; i++) if (hasW(&fv[i], w)) users++;
    if (users < 2) continue;
    int seen = 0;
    for (int i = n - 1; i >= 0; i--) {
      if (!hasW(&fv[i], w)) continue;
      if (++seen == users) { rename(t->ch[i], w, cur); break; }   /* the first user */
      int wk = nwires++, wr = nwires++;
      rename(t->ch[i], w, wk);
      Twin x = { cur, wk, wr }; PUSH(tw, ntw, captw, x);
      cur = wr;
    }
  }
  for (int i = 0; i < n; i++) free(fv[i].w);
  /* box: each argument's free variables behind a bracket */
  typedef struct { int outer, inner; } Box;
  Box *bx = NULL; int nbx = 0, capbx = 0;
  for (int i = 0; i < n; i++) {
    if (fun && i == 0) continue;
    Wires fa = { 0 }; fvW(t->ch[i], &fa);
    for (int j = 0; j < fa.n; j++) { int w2 = nwires++; rename(t->ch[i], fa.w[j], w2); Box b = { fa.w[j], w2 }; PUSH(bx, nbx, capbx, b); }
    free(fa.w);
  }
  int *cw = xalloc(sizeof(int) * n);
  for (int i = 0; i < n; i++) cw[i] = nwires++;
  int node;
  if (t->k == TA) {                                    /* wleft = \app_{lvl}(wright, root) */
    node = alloc(APP, lvl, 0);
    attach(cw[0], pr(node, 0)); attach(root, pr(node, 1)); attach(cw[1], pr(node, 2));
  } else if (t->k == TC) {
    node = alloc(CASE, lvl, t->tag);
    attach(cw[0], pr(node, 0)); attach(root, pr(node, 1));
    for (int i = 1; i < n; i++) attach(cw[i], pr(node, i + 1));
  } else {
    node = alloc(CON, lvl, t->tag);
    attach(root, pr(node, 0));
    for (int i = 0; i < n; i++) attach(cw[i], pr(node, i + 1));
  }
  for (int i = 0; i < n; i++) gamma(t->ch[i], cw[i], (fun && i == 0) ? lvl : lvl + 1);
  for (int i = 0; i < nbx; i++) {                      /* atom = \bra_{lvl}(ref) */
    int b = alloc(BRA, lvl, 0); attach(bx[i].outer, pr(b, 0)); attach(bx[i].inner, pr(b, 1));
  }
  for (int i = 0; i < ntw; i++) {                      /* atom = \fan_{lvl}(right, left) */
    int f = alloc(FAN, lvl, 0); attach(tw[i].orig, pr(f, 0)); attach(tw[i].child, pr(f, 1)); attach(tw[i].rest, pr(f, 2));
  }
  free(fv); free(all.w); free(tw); free(bx); free(cw);
}

/* ------------------------------------------------------------------------
 * Replacement: fresh agents and connections among old auxiliary ends and
 * new ports; every end used once.  Old-to-old connections are followed
 * through, so a wire between the two agents of the pair is handled.
 * ---------------------------------------------------------------------- */
typedef struct { char k; int a, b; } End;   /* 'L' aux a of x, 'R' aux a of y, 'N' new node a port b */
typedef struct { int kind, tag; long lev; } Fresh;
static Fresh *fr; static int nfr, capfr;
static End *cs; static int ncs, capcs;
static End EL(int i) { End e = { 'L', i, 0 }; return e; }
static End ER(int i) { End e = { 'R', i, 0 }; return e; }
static End EN(int k, int p) { End e = { 'N', k, p }; return e; }
static int nn(int kind, long lev, int tag) { Fresh f = { kind, tag, lev }; PUSH(fr, nfr, capfr, f); return nfr - 1; }
static void cn(End a, End b) { PUSH(cs, ncs, capcs, a); PUSH(cs, ncs, capcs, b); }

static void replace(int x, int y) {
  int la = nodes[x].ar, ra = nodes[y].ar;
  int *ul = xalloc(sizeof(int) * (la + 1)), *ur = xalloc(sizeof(int) * (ra + 1));
  int **un = xalloc(sizeof(int *) * (nfr + 1));
  for (int k = 0; k < nfr; k++) un[k] = xalloc(sizeof(int) * (arityOf(fr[k].kind, fr[k].tag) + 1));
  for (int i = 0; i < ncs; i++) {
    End e = cs[i];
    if (e.k == 'L') ul[e.a]++; else if (e.k == 'R') ur[e.a]++; else un[e.a][e.b]++;
  }
  for (int i = 0; i < la; i++) if (ul[i] != 1) die("internal: %s >< %s: left aux %d used %d times", kname[nodes[x].kind], kname[nodes[y].kind], i, ul[i]);
  for (int i = 0; i < ra; i++) if (ur[i] != 1) die("internal: %s >< %s: right aux %d used %d times", kname[nodes[x].kind], kname[nodes[y].kind], i, ur[i]);
  for (int k = 0; k < nfr; k++) for (int p = 0; p <= arityOf(fr[k].kind, fr[k].tag); p++)
    if (un[k][p] != 1) die("internal: new %s port %d used %d times", kname[fr[k].kind], p, un[k][p]);
  for (int k = 0; k < nfr; k++) free(un[k]);
  free(un); free(ul); free(ur);
  int base = nnodes, *nw = xalloc(sizeof(int) * (nfr + 1));
  for (int i = 0; i < nfr; i++) nw[i] = alloc(fr[i].kind, fr[i].lev, fr[i].tag);
#define TOPR(e) ((e).k == 'L' ? pr(x, (e).a + 1) : (e).k == 'R' ? pr(y, (e).a + 1) : pr(nw[(e).a], (e).b))
#define ISOLD(q) ((q).n == x || (q).n == y)
#define ISNEW(q) ((q).n >= base)
  PR *dL = xalloc(sizeof(PR) * (la + 1)), *dR = xalloc(sizeof(PR) * (ra + 1));
  PR *xL = xalloc(sizeof(PR) * (la + 1)), *xR = xalloc(sizeof(PR) * (ra + 1));
  for (int i = 0; i < la; i++) xL[i] = nodes[x].port[i + 1];
  for (int j = 0; j < ra; j++) xR[j] = nodes[y].port[j + 1];
#define DOF(q) ((q).n == x ? dL[(q).p - 1] : dR[(q).p - 1])
#define EXT(q) ((q).n == x ? xL[(q).p - 1] : xR[(q).p - 1])
  for (int i = 0; i < ncs; i += 2) {
    PR a = TOPR(cs[i]), b = TOPR(cs[i + 1]);
    if (ISOLD(a)) { if (a.n == x) dL[a.p - 1] = b; else dR[a.p - 1] = b; }
    if (ISOLD(b)) { if (b.n == x) dL[b.p - 1] = a; else dR[b.p - 1] = a; }
  }
  for (int i = 0; i < ncs; i += 2) {
    PR a = TOPR(cs[i]), b = TOPR(cs[i + 1]);
    for (int o = 0; o < 2; o++) {
      PR nwp = o ? b : a, old = o ? a : b;
      if (!ISNEW(nwp)) continue;
      if (ISNEW(old)) { if (!o) link(nwp, old); continue; }
      PR cur = old, res;
      for (;;) {
        PR q = EXT(cur); if (!ISOLD(q)) { res = q; break; }
        PR r = DOF(q); if (!ISOLD(r)) { res = r; break; }
        cur = r;
      }
      if (ISNEW(res)) { if (prLess(nwp, res)) link(nwp, res); }
      else link(nwp, res);
    }
  }
  for (int side = 0; side < 2; side++) {
    int n = side ? y : x, ar = side ? ra : la;
    for (int i = 0; i < ar; i++) {
      PR o = pr(n, i + 1), E0 = EXT(o);
      if (ISOLD(E0)) continue;
      PR cur = o;
      for (;;) {
        PR r = DOF(cur); if (ISNEW(r)) break;
        PR q = EXT(r);
        if (!ISOLD(q)) { if (prLess(E0, q)) link(E0, q); break; }
        cur = q;
      }
    }
  }
#undef TOPR
#undef ISOLD
#undef ISNEW
#undef DOF
#undef EXT
  free(dL); free(dR); free(xL); free(xR); free(nw);
  nodes[x].kind = nodes[y].kind = -1;
  nfr = ncs = 0;
}

/* ------------------------------------------------------------------------
 * Rules
 * ---------------------------------------------------------------------- */
static long steps, betas, rbsteps;
static int isControl(int k) { return k == FAN || k == BRA || k == CRO; }
static int isProper(int k) { return k == LAM || k == APP || k == CON || k == CASE; }
static int isNeutral(int k) { return k == ATOM || k == NAPP || k == NCASE; }
/* Does this agent exist only because read-back put an atom in a binder? */
static int fromReadback(int n) {
  int k = nodes[n].kind;
  return (k == ATOM && nodes[n].lev >= nlabels) || ((k == NAPP || k == NCASE) && nodes[n].lev == 1);
}

/* Control agent x (level i) acting on agent y, which is copied or moved:
 *   [AG] delta_i[a_j(x..), a_j(y..)] >< a_j[delta_i(x1,y1), ...]       i < j
 *   [AG] t_i[a_{j+1}(x..)] >< a_j[t_i(x1), ...]                       i < j
 *   [AG] e_i[a_{j-1}(x..)] >< a_j[e_i(x1), ...]                       i < j
 * For a neutral agent the same, with no level: [RB] the fan duplicates an
 * atom, a bracket or croissant returns it; a neutral application or case
 * holds what its APP or CASE held, and the control agent passes into it as
 * it would have passed into that APP or CASE. */
static void act(int x, int y) {
  int kx = nodes[x].kind, ky = nodes[y].kind, tg = nodes[y].tag, m = nodes[y].ar;
  long i = nodes[x].lev, j = nodes[y].lev;
  int levelled = isControl(ky) || isProper(ky);
  if (kx == FAN) {
    int c0 = nn(ky, j, tg), c1 = nn(ky, j, tg);
    cn(EL(0), EN(c0, 0)); cn(EL(1), EN(c1, 0));
    for (int k = 0; k < m; k++) {
      int f = nn(FAN, i, 0);
      cn(EN(f, 0), ER(k)); cn(EN(f, 1), EN(c0, k + 1)); cn(EN(f, 2), EN(c1, k + 1));
    }
    return;
  }
  long nj = !levelled ? j : kx == BRA ? j + 1 : j - 1;
  int c = nn(ky, nj, tg);
  cn(EL(0), EN(c, 0));
  for (int k = 0; k < m; k++) {
    int t = nn(kx, i, 0);
    cn(EN(t, 0), ER(k)); cn(EN(t, 1), EN(c, k + 1));
  }
}

static void swap(int *a, int *b) { int t = *a; *a = *b; *b = t; }
static void fire(int a, int b) {
  int ka = nodes[a].kind, kb = nodes[b].kind;
  nfr = ncs = 0;
  if (ka == ROOT || kb == ROOT) die("internal: ROOT in an active pair");
  int rb = fromReadback(a) || fromReadback(b);
  long *count = rb ? &rbsteps : &steps;
  /* [AG] epsilon >< a[epsilon, ..., epsilon] */
  if (kb == ERA) { swap(&a, &b); swap(&ka, &kb); }
  if (ka == ERA) {
    for (int k = 0; k < nodes[b].ar; k++) { int e = nn(ERA, 0, 0); cn(EN(e, 0), ER(k)); }
    replace(a, b); ++*count; return;
  }
  if (kb == APP || kb == CASE) { swap(&a, &b); swap(&ka, &kb); }
  /* [AG] lambda_i[x, y] >< @_i[x, y]: LAM(x,t) >< APP(r,a) -> x = a, t = r */
  if (ka == APP && kb == LAM) {
    if (nodes[a].lev != nodes[b].lev) die("APP_%ld meets LAM_%ld", nodes[a].lev, nodes[b].lev);
    cn(EL(0), ER(1)); cn(EL(1), ER(0));
    replace(a, b); ++*count; if (!rb) betas++; return;
  }
  /* The Scott construction, its binders met: n beta steps (header). */
  if (ka == CASE && kb == CON) {
    long l = nodes[a].lev; int k = cons[nodes[b].tag].index, m = nodes[b].ar, nb = datas[nodes[a].tag].ncon;
    if (cons[nodes[b].tag].data != nodes[a].tag) die("case of %s meets constructor %s", datas[nodes[a].tag].name, cons[nodes[b].tag].name);
    if (nodes[b].lev != l) die("CASE_%ld meets CON_%ld", l, nodes[b].lev);
    int c = nn(CRO, l, 0);
    cn(EN(c, 0), EL(1 + k));
    End f = EN(c, 1);
    for (int j = 0; j < m; j++) {
      int ap = nn(APP, l, 0);
      cn(EN(ap, 0), f); cn(EN(ap, 2), ER(j)); f = EN(ap, 1);
    }
    cn(f, EL(0));
    for (int j = 0; j < nb; j++) if (j != k) { int e = nn(ERA, 0, 0); cn(EN(e, 0), EL(1 + j)); }
    replace(a, b); *count += nb; if (!rb) betas += nb; return;
  }
  /* [RB] \app_{i}[\read_{appl(M)}(a), a] >< \atom_{M}: an elimination of a
   * neutral value is itself neutral; it keeps what the eliminator held. */
  if ((ka == APP || ka == CASE) && isNeutral(kb)) {
    int h = nn(kb, nodes[b].lev, nodes[b].tag);
    for (int k = 0; k < nodes[b].ar; k++) cn(EN(h, k + 1), ER(k));
    int n = nn(ka == APP ? NAPP : NCASE, fromReadback(b), nodes[a].tag);
    cn(EN(n, 0), EL(0)); cn(EN(n, 1), EN(h, 0));
    for (int k = 1; k < nodes[a].ar; k++) cn(EN(n, k + 1), EL(k));
    replace(a, b); ++*count; return;
  }
  if (isControl(ka) && isControl(kb)) {
    long i = nodes[a].lev, j = nodes[b].lev;
    if (i == j) {
      /* [AG] e_i[x] >< e_i[x];  t_i[x] >< t_i[x];  delta_i[x,y] >< delta_i[x,y] */
      if (ka != kb) die("%s_%ld meets %s_%ld", kname[ka], i, kname[kb], j);
      for (int k = 0; k < nodes[a].ar; k++) cn(EL(k), ER(k));
      replace(a, b); ++*count; return;
    }
    if (i < j) { act(a, b); replace(a, b); } else { act(b, a); replace(b, a); }
    ++*count; return;
  }
  if (isControl(kb)) { swap(&a, &b); swap(&ka, &kb); }
  if (isControl(ka)) {
    if (isProper(kb) && !(nodes[a].lev < nodes[b].lev))
      die("%s_%ld meets %s_%ld", kname[ka], nodes[a].lev, kname[kb], nodes[b].lev);
    act(a, b); replace(a, b); ++*count; return;
  }
  die("no rule for %s >< %s (ill-typed term)", kname[ka], kname[kb]);
}

/* Demand from a port: follow the wire; an auxiliary end waits on its
 * agent's principal port, down to an active pair, which fires. */
static PR *stk; static int nstk, capstk;
static void whnf(PR p) {
  nstk = 0; PUSH(stk, nstk, capstk, p);
  while (nstk) {
    PR top = stk[nstk - 1], q = partner(top);
    if (q.n < 0) die("internal: dangling port");
    if (q.p == 0) {
      if (top.p == 0 && nodes[top.n].kind != ROOT) fire(top.n, q.n);
      nstk--; continue;
    }
    PUSH(stk, nstk, capstk, pr(q.n, 0));
  }
}

/* ------------------------------------------------------------------------
 * Read-back [RB]: a binder gets an atom; brackets and croissants facing the
 * reader are passed (read passes through, print ignores them); a fan facing
 * the reader is read on both sides, which must agree.  A constructor is
 * read field by field.  A path, the constructor `plam` of the library, is
 * read by putting the generic interval `igen (ename x)` in its binder, so
 * what is decided at a generic point is decided under it.
 * ---------------------------------------------------------------------- */
enum { RV, RL, RA, RC, RN, RP };
typedef struct R { int k, tag, n, free; long lab; struct R **ch; } R;
static R *rmk(int k, long lab, int n) { R *r = xalloc(sizeof *r); r->k = k; r->lab = lab; r->n = n; r->ch = xalloc(sizeof(R *) * (n ? n : 1)); return r; }
static long nextLabel;
static int C_plam = -1, C_igen = -1, C_ename = -1;
static PR holder(PR at) { int h = alloc(ROOT, 0, 0); link(pr(h, 0), at); return pr(h, 0); }
static int alphaEq(R *a, R *b, long *ma, long *mb, int n) {
  if (a->k != b->k || a->tag != b->tag || a->n != b->n) return 0;
  if (a->k == RV) {
    for (int i = n - 1; i >= 0; i--) if (ma[i] == a->lab || mb[i] == b->lab) return ma[i] == a->lab && mb[i] == b->lab;
    return a->lab == b->lab;
  }
  if (a->k == RL || a->k == RP) { ma[n] = a->lab; mb[n] = b->lab; return alphaEq(a->ch[0], b->ch[0], ma, mb, n + 1); }
  for (int i = 0; i < a->n; i++) if (!alphaEq(a->ch[i], b->ch[i], ma, mb, n)) return 0;
  return 1;
}
static int size(R *r) { int s = 1; for (int i = 0; i < r->n; i++) s += size(r->ch[i]); return s; }
static R *readback(PR p);
/* Bring a value to p, passing brackets and croissants that face the reader. */
static void settle(PR p) {
  for (;;) {
    whnf(p);
    PR q = partner(p); int k = nodes[q.n].kind;
    if (k != BRA && k != CRO) return;
    PR u = partner(pr(q.n, 1)); nodes[q.n].kind = -1; link(p, u);
  }
}
static R *readLam(int n, int pathBinder) {
  long lab = nlabels + (nextLabel++);
  int atom = alloc(ATOM, lab, 0), v0 = atom;
  if (pathBinder) {   /* igen_{l+1}(ename_{l+2}(x)), at the level an argument would have */
    long l = nodes[n].lev;
    int ig = alloc(CON, l + 1, C_igen), en = alloc(CON, l + 2, C_ename);
    link(pr(ig, 1), pr(en, 0)); link(pr(en, 1), pr(atom, 0));
    v0 = ig;
  }
  PR v = partner(pr(n, 1)), b = partner(pr(n, 2)), h;
  if (prEq(v, pr(n, 2))) h = holder(pr(v0, 0));            /* \x. x */
  else { link(pr(v0, 0), v); h = holder(b); }
  nodes[n].kind = -1;
  R *r = rmk(pathBinder ? RP : RL, lab, 1); r->ch[0] = readback(h); return r;
}
static R *readback(PR p) {
  {
    settle(p);
    PR q = partner(p); int n = q.n, k = nodes[n].kind;
    if (k == ATOM) { R *r = rmk(RV, nodes[n].lev, 0); r->free = nodes[n].lev < nlabels; return r; }
    if (k == LAM) return readLam(n, 0);
    if (k == CON && nodes[n].tag == C_plam) {
      PR f = holder(partner(pr(n, 1)));
      nodes[n].kind = -1;
      settle(f);
      PR g = partner(f);
      if (nodes[g.n].kind == LAM) return readLam(g.n, 1);
      R *r = rmk(RC, 0, 1); r->tag = C_plam; r->ch[0] = readback(f); return r;
    }
    if (k == CON || k == NAPP || k == NCASE) {
      int m = nodes[n].ar; PR *hs = xalloc(sizeof(PR) * (m + 1));
      for (int i = 0; i < m; i++) hs[i] = holder(partner(pr(n, i + 1)));
      R *r = rmk(k == CON ? RC : k == NAPP ? RA : RN, 0, m); r->tag = nodes[n].tag;
      nodes[n].kind = -1;
      for (int i = 0; i < m; i++) r->ch[i] = readback(hs[i]);
      free(hs); return r;
    }
    if (k == FAN) {
      PR h0 = holder(partner(pr(n, 1))), h1 = holder(partner(pr(n, 2)));
      nodes[n].kind = -1;
      R *r0 = readback(h0), *r1 = readback(h1);
      int d = size(r0) + size(r1) + 1;
      long *ma = xalloc(sizeof(long) * d), *mb = xalloc(sizeof(long) * d);
      if (!alphaEq(r0, r1, ma, mb, 0)) die("read-back: the two sides of a fan differ");
      free(ma); free(mb);
      return r0;
    }
    die("read-back meets %s", k >= 0 ? kname[k] : "a freed agent");
  }
  return NULL;
}

/* Printing in the input syntax: binders v1, v2, ... in order; a path
 * binder as <v1> body; a neutral case as (T s B1 ..). */
typedef struct { long *lab; int n, cap; } Named;
static void print(R *r, Named *nm, int paren) {
  if (r->k == RV) {
    if (r->free) { printf("%s", labels[r->lab]); return; }
    for (int i = 0; i < nm->n; i++) if (nm->lab[i] == r->lab) { printf("v%d", i + 1); return; }
    die("internal: unbound read-back variable");
  }
  if (r->k == RP) {
    if (paren) printf("(");
    PUSH(nm->lab, nm->n, nm->cap, r->lab);
    printf("<v%d> ", nm->n); print(r->ch[0], nm, 0);
    if (paren) printf(")");
    return;
  }
  if (r->k == RL) {
    if (paren) printf("(");
    int first = 1;
    while (r->k == RL) {
      PUSH(nm->lab, nm->n, nm->cap, r->lab);
      printf("%sv%d", first ? "" : ", ", nm->n); first = 0; r = r->ch[0];
    }
    printf(": "); print(r, nm, 0);
    if (paren) printf(")");
    return;
  }
  if (r->k == RC && r->n == 0) { printf("%s", cons[r->tag].name); return; }
  if (paren) printf("(");
  if (r->k == RC) printf("%s", cons[r->tag].name);
  else if (r->k == RN) printf("%s", datas[r->tag].name);
  else print(r->ch[0], nm, r->ch[0]->k == RL || r->ch[0]->k == RP);
  for (int i = (r->k == RA ? 1 : 0); i < r->n; i++) { printf(" "); print(r->ch[i], nm, r->ch[i]->k != RV && !(r->ch[i]->k == RC && r->ch[i]->n == 0)); }
  if (paren) printf(")");
}

static char *slurp(const char *fn) {
  FILE *f = fopen(fn, "rb"); if (!f) die("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *b = xalloc(n + 2); if (fread(b, 1, n, f) != (size_t)n) die("cannot read %s", fn); fclose(f);
  b[n] = '\n'; return b;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: net file ...   (declarations of earlier files are visible to later ones)\n"); return 2; }
  for (int i = 1; i < argc; i++) lex(slurp(argv[i]));
  T *src = ptext();
  C_plam = findCon("plam"); C_igen = findCon("igen"); C_ename = findCon("ename");
  if (C_plam >= 0 && (C_igen < 0 || C_ename < 0)) die("plam is declared without igen and ename");
  T *t = alpha(expand(src), NULL);
  int root = nwires++;
  gamma(t, root, 0);
  PR top = pr(alloc(ROOT, 0, 0), 0);
  attach(root, top);
  for (int w = 0; w < capw; w++) if (wfirst[w].n >= 0) die("internal: wire %d used once", w);
  R *r = readback(top);
  Named nm = { 0 };
  print(r, &nm, 0);
  printf("\nlength %ld (beta %ld); read-back %ld\n", steps, betas, rbsteps);
  return 0;
}

/* net/net.c -- optimal reduction of the lambda calculus by interaction.
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
 *   [RB]  read-back: the same paper, section 7, and codedot/lambda
 *         encoding/standard/template.txt (atom and read rules).
 * Each rule below names its source line.  The one addition of mine is
 * marked ADDED.
 *
 * Agents (signature Sigma_O of [AG], plus read-back):
 *   LAM_i  principal: the function; aux 0: bound variable; aux 1: body
 *   APP_i  principal: the function;  aux 0: result;          aux 1: argument
 *   FAN_i  principal; aux 0, aux 1                         (delta_i)
 *   BRA_i  principal; aux 0       bracket, raises levels    (t_i)
 *   CRO_i  principal; aux 0       croissant, lowers levels  (e_i)
 *   ERA    principal                                         (epsilon)
 *   ATOM   principal; label: a free variable or a read-back variable
 *   NAPP   principal; aux 0: head; aux 1: argument  -- an application whose
 *          head is an atom; its level field is 1 when that atom (or the head
 *          NAPP) was put there by read-back, else 0
 *   ROOT   one port, a place read-back reads from; it never interacts
 *
 * Output: the normal form, and its length (5.6): the number of
 * interactions.  Interactions that only exist because read-back put an
 * atom in a binder are counted apart, so read-back adds no step to the
 * length (5.21).  Interactions with free variables of the input count.
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
 * Source syntax: the grammar of codedot/lambda (grammar.jison).
 *   text : defs term          defs : (NAME '=' term ';')*
 *   term : NAME ',' abst-rest | NAME ':' term | appl
 *   appl : atom+              atom : '(' term ')' | NAME
 * Comments are {...} and # to end of line.
 * ---------------------------------------------------------------------- */
enum { TV, TL, TA };
typedef struct T { int k; char *name; int w, free; struct T *a, *b; } T;
static T *tmk(int k, const char *name, T *a, T *b) {
  T *t = xalloc(sizeof *t); t->k = k; t->name = name ? xdup(name) : NULL; t->a = a; t->b = b; t->w = -1; return t;
}

static char **tok; static int ntok, captok, pos;
static int namech(int c) { return c && !isspace(c) && !strchr("{}#=;,:()", c); }
static void lex(const char *s) {
  while (*s) {
    if (isspace((unsigned char)*s)) { s++; continue; }
    if (*s == '#') { while (*s && *s != '\n') s++; continue; }
    if (*s == '{') { while (*s && *s != '}') s++; if (*s) s++; continue; }
    if (*s == '}') die("unbalanced '}'");
    const char *b = s;
    if (strchr("=;,:()", *s)) s++;
    else while (namech((unsigned char)*s)) s++;
    char *t = xalloc(s - b + 1); memcpy(t, b, s - b);
    PUSH(tok, ntok, captok, t);
  }
}
static const char *pk(int k) { return pos + k < ntok ? tok[pos + k] : ""; }
static int isname(const char *t) { return *t && namech((unsigned char)*t); }
static const char *nxt(void) { if (pos >= ntok) die("unexpected end of input"); return tok[pos++]; }
static void want(const char *s) { if (strcmp(pk(0), s)) die("expected '%s', got '%s'", s, pk(0)); pos++; }

static T *pterm(void);
static T *patom(void) {
  if (!strcmp(pk(0), "(")) { pos++; T *t = pterm(); want(")"); return t; }
  if (!isname(pk(0))) die("unexpected '%s'", pk(0));
  return tmk(TV, nxt(), NULL, NULL);
}
static T *pabst(void) {           /* NAME (',' NAME)* ':' term */
  const char *x = nxt();
  if (!strcmp(pk(0), ",")) { pos++; return tmk(TL, x, pabst(), NULL); }
  want(":");
  return tmk(TL, x, pterm(), NULL);
}
static T *pterm(void) {
  if (isname(pk(0)) && (!strcmp(pk(1), ",") || !strcmp(pk(1), ":"))) return pabst();
  T *t = patom();
  while (!strcmp(pk(0), "(") || isname(pk(0))) t = tmk(TA, NULL, t, patom());
  return t;
}
typedef struct { char *name; T *def; } Def;
static Def *defs; static int ndefs, capdefs;
static T *ptext(void) {
  while (isname(pk(0)) && !strcmp(pk(1), "=")) {
    Def d; d.name = xdup(nxt()); pos++; d.def = pterm(); want(";");
    PUSH(defs, ndefs, capdefs, d);
  }
  T *t = pterm();
  if (pos != ntok) die("trailing '%s'", pk(0));
  return t;
}

/* Free names of a source term. */
typedef struct { char **s; int n, cap; } Names;
static int hasName(Names *v, const char *x) { for (int i = 0; i < v->n; i++) if (!strcmp(v->s[i], x)) return 1; return 0; }
static void freeNames(T *t, char **bound, int nb, Names *out) {
  if (t->k == TV) {
    for (int i = 0; i < nb; i++) if (!strcmp(bound[i], t->name)) return;
    if (!hasName(out, t->name)) PUSH(out->s, out->n, out->cap, t->name);
  } else if (t->k == TL) {
    char **b2 = xalloc(sizeof(char *) * (nb + 1)); memcpy(b2, bound, sizeof(char *) * nb); b2[nb] = t->name;
    freeNames(t->a, b2, nb + 1, out); free(b2);
  } else { freeNames(t->a, bound, nb, out); freeNames(t->b, bound, nb, out); }
}
/* Definitions, as codedot/lambda generic.js expand(): latest first, each
 * used one wraps the term as (\name. term) def.  A definition is therefore
 * one shared subnet, bound once and fanned to its uses. */
static T *expand(T *t) {
  for (int i = ndefs - 1; i >= 0; i--) {
    Names fv = { 0 }; freeNames(t, NULL, 0, &fv);
    if (hasName(&fv, defs[i].name)) t = tmk(TA, NULL, tmk(TL, defs[i].name, t, NULL), defs[i].def);
    free(fv.s);
  }
  return t;
}

/* alpha (generic.js): each binder gets a wire; an occurrence names its
 * binder's wire; a free name stays free. */
static int nwires;
typedef struct Env { const char *x; int w; struct Env *up; } Env;
static T *alpha(T *t, Env *e) {
  if (t->k == TV) {
    for (; e; e = e->up) if (!strcmp(e->x, t->name)) { T *v = tmk(TV, t->name, NULL, NULL); v->w = e->w; return v; }
    T *v = tmk(TV, t->name, NULL, NULL); v->free = 1; return v;
  }
  if (t->k == TL) {
    Env e2 = { t->name, nwires++, e };
    T *l = tmk(TL, t->name, alpha(t->a, &e2), NULL); l->w = e2.w; return l;
  }
  return tmk(TA, NULL, alpha(t->a, e), alpha(t->b, e));
}
typedef struct { int *w, n, cap; } Wires;
static int hasW(Wires *v, int w) { for (int i = 0; i < v->n; i++) if (v->w[i] == w) return 1; return 0; }
static void fvW(T *t, Wires *out) {          /* bound wires free in t */
  if (t->k == TV) { if (!t->free && !hasW(out, t->w)) PUSH(out->w, out->n, out->cap, t->w); return; }
  if (t->k == TL) {
    Wires in = { 0 }; fvW(t->a, &in);
    for (int i = 0; i < in.n; i++) if (in.w[i] != t->w && !hasW(out, in.w[i])) PUSH(out->w, out->n, out->cap, in.w[i]);
    free(in.w); return;
  }
  fvW(t->a, out); fvW(t->b, out);
}
static void rename(T *t, int from, int to) {
  if (t->k == TV) { if (!t->free && t->w == from) t->w = to; return; }
  rename(t->a, from, to); if (t->k == TA) rename(t->b, from, to);
}

/* ------------------------------------------------------------------------
 * The net
 * ---------------------------------------------------------------------- */
enum { LAM, APP, FAN, BRA, CRO, ERA, ATOM, NAPP, ROOT, NKIND };
static const int arity[NKIND] = { 2, 2, 2, 1, 1, 0, 0, 2, 0 };
static const char *kname[NKIND] = { "LAM", "APP", "FAN", "BRA", "CRO", "ERA", "ATOM", "NAPP", "ROOT" };
typedef struct { int n, p; } PR;
typedef struct { int kind; long lev; PR port[3]; } Node;   /* lev: level, or the atom's label */
static Node *nodes; static int nnodes, capnodes;
static int alloc(int kind, long lev) {
  Node x; memset(&x, 0, sizeof x); x.kind = kind; x.lev = lev;
  for (int i = 0; i < 3; i++) x.port[i].n = -1;
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

/* Free-variable labels. */
static char **labels; static int nlabels, caplabels;
static long intern(const char *s) {
  for (int i = 0; i < nlabels; i++) if (!strcmp(labels[i], s)) return i;
  PUSH(labels, nlabels, caplabels, xdup(s)); return nlabels - 1;
}

/* Initial encoding [AG pp. 41-42], transcribed from codedot/lambda
 * encoding/standard/index.js gamma().  An abstraction and an application
 * are at the level of their position; an argument one level deeper; a
 * bracket at the level of the application on each free variable of the
 * argument; a croissant at its level on each variable occurrence; a fan at
 * the application's level on each variable both sides use. */
static void gamma(T *t, int root, long lvl) {
  if (t->k == TV) {
    if (t->free) { int a = alloc(ATOM, intern(t->name)); attach(root, pr(a, 0)); return; }
    int c = alloc(CRO, lvl);                           /* name = \cro_{lvl}(root) */
    attach(t->w, pr(c, 0)); attach(root, pr(c, 1));
    return;
  }
  if (t->k == TL) {                                    /* root = \lam_{lvl}(agent, wire) */
    int l = alloc(LAM, lvl);
    attach(root, pr(l, 0));
    Wires fv = { 0 }; fvW(t->a, &fv);
    if (hasW(&fv, t->w)) attach(t->w, pr(l, 1));
    else { int e = alloc(ERA, 0); link(pr(l, 1), pr(e, 0)); }
    free(fv.w);
    int bw = nwires++; attach(bw, pr(l, 2));
    gamma(t->a, bw, lvl);
    return;
  }
  /* shared = mktwins(left, right) */
  Wires fl = { 0 }, fr = { 0 }; fvW(t->a, &fl); fvW(t->b, &fr);
  Wires sh = { 0 }, shl = { 0 }, shr = { 0 };
  for (int i = 0; i < fl.n; i++) if (hasW(&fr, fl.w[i])) {
    int wl = nwires++, wr = nwires++;
    rename(t->a, fl.w[i], wl); rename(t->b, fl.w[i], wr);
    PUSH(sh.w, sh.n, sh.cap, fl.w[i]); PUSH(shl.w, shl.n, shl.cap, wl); PUSH(shr.w, shr.n, shr.cap, wr);
  }
  free(fl.w); free(fr.w);
  /* the argument's free variables, each renamed behind a bracket */
  Wires fa = { 0 }, fa2 = { 0 }; fvW(t->b, &fa);
  for (int i = 0; i < fa.n; i++) { int w2 = nwires++; rename(t->b, fa.w[i], w2); PUSH(fa2.w, fa2.n, fa2.cap, w2); }
  int wleft = nwires++, wright = nwires++;
  int ap = alloc(APP, lvl);                            /* wleft = \app_{lvl}(wright, root) */
  attach(wleft, pr(ap, 0)); attach(root, pr(ap, 1)); attach(wright, pr(ap, 2));
  gamma(t->a, wleft, lvl);
  gamma(t->b, wright, lvl + 1);
  for (int i = 0; i < fa.n; i++) {                     /* box: atom = \bra_{lvl}(ref) */
    int b = alloc(BRA, lvl); attach(fa.w[i], pr(b, 0)); attach(fa2.w[i], pr(b, 1));
  }
  for (int i = 0; i < sh.n; i++) {                     /* psi: atom = \fan_{lvl}(right, left) */
    int f = alloc(FAN, lvl); attach(sh.w[i], pr(f, 0)); attach(shr.w[i], pr(f, 1)); attach(shl.w[i], pr(f, 2));
  }
  free(fa.w); free(fa2.w); free(sh.w); free(shl.w); free(shr.w);
}

/* ------------------------------------------------------------------------
 * Replacement: fresh agents and connections among old auxiliary ends and
 * new ports; every end used once.  Old-to-old connections are followed
 * through, so a wire between the two agents of the pair is handled.
 * ---------------------------------------------------------------------- */
typedef struct { char k; int a, b; } End;   /* 'L' aux a of x, 'R' aux a of y, 'N' new node a port b */
typedef struct { int kind; long lev; } Fresh;
static Fresh fr[16]; static int nfr;
static End cs[64]; static int ncs;
static End EL(int i) { End e = { 'L', i, 0 }; return e; }
static End ER(int i) { End e = { 'R', i, 0 }; return e; }
static End EN(int k, int p) { End e = { 'N', k, p }; return e; }
static int nn(int kind, long lev) { if (nfr == 16) die("internal: replacement too large"); fr[nfr].kind = kind; fr[nfr].lev = lev; return nfr++; }
static void cn(End a, End b) { if (ncs >= 62) die("internal: replacement too large"); cs[ncs++] = a; cs[ncs++] = b; }

static void replace(int x, int y) {
  int la = arity[nodes[x].kind], ra = arity[nodes[y].kind];
  /* each end used exactly once */
  int ul[3] = { 0 }, ur[3] = { 0 }, un[16][3]; memset(un, 0, sizeof un);
  for (int i = 0; i < ncs; i++) {
    End e = cs[i];
    if (e.k == 'L') ul[e.a]++; else if (e.k == 'R') ur[e.a]++; else un[e.a][e.b]++;
  }
  for (int i = 0; i < la; i++) if (ul[i] != 1) die("internal: %s >< %s: left aux %d used %d times", kname[nodes[x].kind], kname[nodes[y].kind], i, ul[i]);
  for (int i = 0; i < ra; i++) if (ur[i] != 1) die("internal: %s >< %s: right aux %d used %d times", kname[nodes[x].kind], kname[nodes[y].kind], i, ur[i]);
  for (int k = 0; k < nfr; k++) for (int p = 0; p <= arity[fr[k].kind]; p++)
    if (un[k][p] != 1) die("internal: new %s port %d used %d times", kname[fr[k].kind], p, un[k][p]);
  int base = nnodes, nw[16];
  for (int i = 0; i < nfr; i++) nw[i] = alloc(fr[i].kind, fr[i].lev);
#define TOPR(e) ((e).k == 'L' ? pr(x, (e).a + 1) : (e).k == 'R' ? pr(y, (e).a + 1) : pr(nw[(e).a], (e).b))
#define ISOLD(q) ((q).n == x || (q).n == y)
#define ISNEW(q) ((q).n >= base)
  PR dL[3], dR[3], xL[3], xR[3];
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
  nodes[x].kind = nodes[y].kind = -1;
}

/* ------------------------------------------------------------------------
 * Rules
 * ---------------------------------------------------------------------- */
static long steps, betas, rbsteps;
/* Does this agent exist only because read-back put an atom in a binder? */
static int fromReadback(int n) {
  int k = nodes[n].kind;
  return (k == ATOM && nodes[n].lev >= nlabels) || (k == NAPP && nodes[n].lev == 1);
}
static int isControl(int k) { return k == FAN || k == BRA || k == CRO; }
static int isProper(int k) { return k == LAM || k == APP; }

/* Control agent x (level i) acting on agent y, which is copied or moved:
 *   [AG] delta_i[a_j(x..), a_j(y..)] >< a_j[delta_i(x1,y1), ...]       i < j
 *   [AG] t_i[a_{j+1}(x..)] >< a_j[t_i(x1), ...]                       i < j
 *   [AG] e_i[a_{j-1}(x..)] >< a_j[e_i(x1), ...]                       i < j
 * For a level-free agent (ATOM, NAPP) the same, with no level change:
 *   [RB] \fan_{i}[\atom_{M}, \atom_{M}] >< \atom_{M}
 *   [RB] \bra_{i}[\atom_{M}] >< \atom_{M},  \cro_{i}[\atom_{M}] >< \atom_{M}
 *   ADDED: the same for NAPP, whose fields are the head and argument of an
 *   application read-back has met; a control agent passes into them as it
 *   would have passed into the APP that NAPP replaced. */
static void act(int x, int y) {
  int kx = nodes[x].kind, ky = nodes[y].kind, m = arity[ky];
  long i = nodes[x].lev, j = nodes[y].lev;
  int levelled = isControl(ky) || isProper(ky);
  if (kx == FAN) {
    int c0 = nn(ky, j), c1 = nn(ky, j);
    cn(EL(0), EN(c0, 0)); cn(EL(1), EN(c1, 0));
    for (int k = 0; k < m; k++) {
      int f = nn(FAN, i);
      cn(EN(f, 0), ER(k)); cn(EN(f, 1), EN(c0, k + 1)); cn(EN(f, 2), EN(c1, k + 1));
    }
    return;
  }
  long nj = !levelled ? j : kx == BRA ? j + 1 : j - 1;
  int c = nn(ky, nj);
  cn(EL(0), EN(c, 0));
  for (int k = 0; k < m; k++) {
    int t = nn(kx, i);
    cn(EN(t, 0), ER(k)); cn(EN(t, 1), EN(c, k + 1));
  }
}

static void fire(int a, int b) {
  int ka = nodes[a].kind, kb = nodes[b].kind;
  nfr = ncs = 0;
  if (ka == ROOT || kb == ROOT) die("internal: ROOT in an active pair");
  if (fromReadback(a) || fromReadback(b)) rbsteps++; else steps++;
  /* [AG] epsilon >< a[epsilon, ..., epsilon] */
  if (kb == ERA) { int t = a; a = b; b = t; ka = nodes[a].kind; kb = nodes[b].kind; }
  if (ka == ERA) {
    for (int k = 0; k < arity[kb]; k++) { int e = nn(ERA, 0); cn(EN(e, 0), ER(k)); }
    replace(a, b); return;
  }
  /* [AG] lambda_i[x, y] >< @_i[x, y]: LAM(x,t) >< APP(r,a) -> x = a, t = r */
  if (ka == LAM && kb == APP) { int t = a; a = b; b = t; ka = APP; kb = LAM; }
  if (ka == APP && kb == LAM) {
    if (nodes[a].lev != nodes[b].lev) die("APP_%ld meets LAM_%ld", nodes[a].lev, nodes[b].lev);
    cn(EL(0), ER(1)); cn(EL(1), ER(0));
    betas++;
    replace(a, b); return;
  }
  /* [RB] \app_{i}[\read_{appl(M)}(a), a] >< \atom_{M}: an application whose
   * head is an atom is read as one, its argument read in place. */
  if (ka == ATOM || ka == NAPP) { int t = a; a = b; b = t; ka = nodes[a].kind; kb = nodes[b].kind; }
  if (ka == APP && (kb == ATOM || kb == NAPP)) {
    int h = nn(kb, nodes[b].lev), n = nn(NAPP, fromReadback(b));
    for (int k = 0; k < arity[kb]; k++) cn(EN(h, k + 1), ER(k));
    cn(EN(n, 0), EL(0)); cn(EN(n, 1), EN(h, 0)); cn(EN(n, 2), EL(1));
    replace(a, b); return;
  }
  if (isControl(ka) && isControl(kb)) {
    long i = nodes[a].lev, j = nodes[b].lev;
    if (i == j) {
      /* [AG] e_i[x] >< e_i[x];  t_i[x] >< t_i[x];  delta_i[x,y] >< delta_i[x,y] */
      if (ka != kb) die("%s_%ld meets %s_%ld", kname[ka], i, kname[kb], j);
      for (int k = 0; k < arity[ka]; k++) cn(EL(k), ER(k));
      replace(a, b); return;
    }
    if (i < j) act(a, b); else act(b, a);
    if (i < j) replace(a, b); else replace(b, a);
    return;
  }
  if (isControl(kb)) { int t = a; a = b; b = t; ka = nodes[a].kind; kb = nodes[b].kind; }
  if (isControl(ka)) {
    if (isProper(kb) && !(nodes[a].lev < nodes[b].lev))
      die("%s_%ld meets %s_%ld", kname[ka], nodes[a].lev, kname[kb], nodes[b].lev);
    act(a, b); replace(a, b); return;
  }
  die("no rule for %s >< %s", kname[ka], kname[kb]);
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
 * the reader is read on both sides, which must agree; an atom is a variable;
 * NAPP is an application with an atom at its head.
 * ---------------------------------------------------------------------- */
enum { RV, RL, RA };
typedef struct R { int k; long lab; int free; struct R *a, *b; } R;
static R *rmk(int k, long lab, R *a, R *b) { R *r = xalloc(sizeof *r); r->k = k; r->lab = lab; r->a = a; r->b = b; return r; }
static long nextLabel;
static PR holder(PR at) { int h = alloc(ROOT, 0); link(pr(h, 0), at); return pr(h, 0); }
static int alphaEq(R *a, R *b, long *ma, long *mb, int n) {
  if (a->k != b->k) return 0;
  if (a->k == RV) {
    for (int i = n - 1; i >= 0; i--) { if (ma[i] == a->lab || mb[i] == b->lab) return ma[i] == a->lab && mb[i] == b->lab; }
    return a->lab == b->lab;
  }
  if (a->k == RL) { ma[n] = a->lab; mb[n] = b->lab; return alphaEq(a->a, b->a, ma, mb, n + 1); }
  return alphaEq(a->a, b->a, ma, mb, n) && alphaEq(a->b, b->b, ma, mb, n);
}
static int depth(R *r) { return r->k == RV ? 1 : r->k == RL ? 1 + depth(r->a) : 1 + (depth(r->a) > depth(r->b) ? depth(r->a) : depth(r->b)); }
static R *readback(PR p) {
  for (;;) {
    whnf(p);
    PR q = partner(p); int n = q.n, k = nodes[n].kind;
    if (k == BRA || k == CRO) { PR u = partner(pr(n, 1)); nodes[n].kind = -1; link(p, u); continue; }
    if (k == ATOM) { R *r = rmk(RV, nodes[n].lev, NULL, NULL); r->free = nodes[n].lev < nlabels; return r; }
    if (k == LAM) {
      long lab = nlabels + (nextLabel++);
      int atom = alloc(ATOM, lab);
      PR v = partner(pr(n, 1)), b = partner(pr(n, 2)), h;
      if (prEq(v, pr(n, 2))) h = holder(pr(atom, 0));           /* \x. x */
      else { link(pr(atom, 0), v); h = holder(b); }
      nodes[n].kind = -1;
      return rmk(RL, lab, readback(h), NULL);
    }
    if (k == NAPP) {
      PR hd = holder(partner(pr(n, 1))), ar = holder(partner(pr(n, 2)));
      nodes[n].kind = -1;
      R *f = readback(hd); return rmk(RA, 0, f, readback(ar));
    }
    if (k == FAN) {
      PR h0 = holder(partner(pr(n, 1))), h1 = holder(partner(pr(n, 2)));
      nodes[n].kind = -1;
      R *r0 = readback(h0), *r1 = readback(h1);
      int d = depth(r0) + depth(r1) + 1;
      long *ma = xalloc(sizeof(long) * d), *mb = xalloc(sizeof(long) * d);
      if (!alphaEq(r0, r1, ma, mb, 0)) die("read-back: the two sides of a fan differ");
      free(ma); free(mb);
      return r0;
    }
    die("read-back meets %s", k >= 0 ? kname[k] : "a freed agent");
  }
}

/* Printing in the syntax of the input; binders named v1, v2, ... in order. */
typedef struct { long *lab; int n, cap; } Named;
static void print(R *r, Named *nm, int paren) {
  if (r->k == RV) {
    if (r->free) { printf("%s", labels[r->lab]); return; }
    for (int i = 0; i < nm->n; i++) if (nm->lab[i] == r->lab) { printf("v%d", i + 1); return; }
    die("internal: unbound read-back variable");
  }
  if (r->k == RL) {
    if (paren) printf("(");
    int first = 1;
    while (r->k == RL) {
      PUSH(nm->lab, nm->n, nm->cap, r->lab);
      printf("%sv%d", first ? "" : ", ", nm->n); first = 0; r = r->a;
    }
    printf(": "); print(r, nm, 0);
    if (paren) printf(")");
    return;
  }
  if (paren) printf("(");
  print(r->a, nm, r->a->k == RL);
  printf(" ");
  print(r->b, nm, r->b->k != RV);
  if (paren) printf(")");
}

static char *slurp(const char *fn) {
  FILE *f = fopen(fn, "rb"); if (!f) die("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *b = xalloc(n + 2); if (fread(b, 1, n, f) != (size_t)n) die("cannot read %s", fn); fclose(f);
  b[n] = '\n'; return b;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: net file ...   (definitions of earlier files are visible to later ones)\n"); return 2; }
  for (int i = 1; i < argc; i++) lex(slurp(argv[i]));
  T *t = alpha(expand(ptext()), NULL);
  int root = nwires++;
  gamma(t, root, 0);
  PR top = pr(alloc(ROOT, 0), 0);
  attach(root, top);
  for (int w = 0; w < capw; w++) if (wfirst[w].n >= 0) die("internal: wire %d used once", w);
  R *r = readback(top);
  Named nm = { 0 };
  print(r, &nm, 0);
  printf("\nlength %ld (beta %ld); read-back %ld\n", steps, betas, rbsteps);
  return 0;
}

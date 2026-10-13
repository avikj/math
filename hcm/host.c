/* hcm/host.c -- the fixed step of the interaction machine.
 *
 * The host holds an agent store and wires, demands active pairs from the
 * root, interprets rule descriptors and reads results back.  Every rule is a
 * descriptor: fresh nodes (tag, label template) and connections between
 * endpoints, each endpoint used exactly once.  No callback runs when a
 * descriptor is applied.  Descriptors are generated from definitions the
 * first time a pair is met (MACHINE_PLAN.md sections 1-4).
 *
 * The host's literal operations are fresh labels and the order of two labels
 * (CMP2 meeting NAME).  It knows the constructors lt/eq/gt, inil/icons,
 * fnil/fcons, sys/nosys, cnil/ccons/pos, at0/at1 and the definitions
 * isubst/fsubst/reflect by name: the representation contract.  It never
 * switches on what any other tag means.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>

static void die(const char *fmt, ...) {
  va_list ap; va_start(ap, fmt);
  fprintf(stderr, "hcm: "); vfprintf(stderr, fmt, ap); fprintf(stderr, "\n");
  va_end(ap); exit(1);
}
static void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xgrow(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static char *xdup(const char *s) { char *d = xalloc(strlen(s) + 1); strcpy(d, s); return d; }
#define PUSH(arr, n, cap, v) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 8; \
    (arr) = xgrow((arr), sizeof(*(arr)) * (cap)); } (arr)[(n)++] = (v); } while (0)

/* ------------------------------------------------------------------------
 * Text buffer
 * ---------------------------------------------------------------------- */
typedef struct { char *s; int n, cap; } Str;
static void sput(Str *b, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt); int k = vsnprintf(NULL, 0, fmt, ap); va_end(ap);
  while (b->n + k + 1 > b->cap) { b->cap = b->cap ? 2 * b->cap : 256; b->s = xgrow(b->s, b->cap); }
  va_start(ap, fmt); vsnprintf(b->s + b->n, k + 1, fmt, ap); va_end(ap);
  b->n += k;
}

/* ------------------------------------------------------------------------
 * Raw syntax (parser output)
 * ---------------------------------------------------------------------- */
enum { R_ID, R_LAM, R_APP, R_FRESH };
typedef struct Raw { int k; char *name; int dim; struct Raw *a, *b; } Raw;
static Raw *rmk(int k, const char *name, Raw *a, Raw *b) {
  Raw *r = xalloc(sizeof *r); r->k = k; r->name = name ? xdup(name) : NULL; r->a = a; r->b = b; return r;
}
static Raw *rid(const char *n) { return rmk(R_ID, n, NULL, NULL); }
static Raw *rapp(Raw *f, Raw *a) { return rmk(R_APP, NULL, f, a); }
static Raw *rapp2(Raw *f, Raw *a, Raw *b) { return rapp(rapp(f, a), b); }
static Raw *rlam(const char *x, int dim, Raw *b) { Raw *r = rmk(R_LAM, x, b, NULL); r->dim = dim; return r; }

/* ------------------------------------------------------------------------
 * Lexer
 * ---------------------------------------------------------------------- */
typedef struct { char **t; int n, cap, pos; const char *where; } Toks;
static int idc(int c) { return isalnum(c) || c == '_' || c == '\''; }
static void lex(Toks *T, const char *s) {
  T->n = 0; T->pos = 0;
  while (*s) {
    if (isspace((unsigned char)*s)) { s++; continue; }
    if (s[0] == '-' && s[1] == '-') { while (*s && *s != '\n') s++; continue; }
    const char *b = s;
    if (isalpha((unsigned char)*s) || *s == '_') {
      while (idc((unsigned char)*s) || (*s == '-' && isalnum((unsigned char)s[1]))) s++;
    } else if (*s == '0' || *s == '1') s++;
    else if ((s[0] == '-' && s[1] == '>') || (s[0] == '\\' && s[1] == '/') || (s[0] == '/' && s[1] == '\\')) s += 2;
    else if (strchr("(),\\<>@~=:|", *s)) s++;
    else die("%s: unexpected character '%c'", T->where, *s);
    char *tok = xalloc(s - b + 1); memcpy(tok, b, s - b);
    PUSH(T->t, T->n, T->cap, tok);
  }
}
static const char *peek(Toks *T, int k) { return T->pos + k < T->n ? T->t[T->pos + k] : ""; }
static int is(Toks *T, const char *s) { return strcmp(peek(T, 0), s) == 0; }
static const char *next(Toks *T) { if (T->pos >= T->n) die("%s: unexpected end", T->where); return T->t[T->pos++]; }
static void expect(Toks *T, const char *s) { if (!is(T, s)) die("%s: expected '%s', got '%s'", T->where, s, peek(T, 0)); T->pos++; }
static int isIdent(const char *s) { return (isalpha((unsigned char)s[0]) || s[0] == '_'); }
static int stopTok(const char *s) {
  static const char *st[] = { "", ")", ",", "->", "\\/", "/\\", "@", "=", "in", "|", ">", ":", NULL };
  for (int i = 0; st[i]; i++) if (!strcmp(s, st[i])) return 1;
  return 0;
}

/* ------------------------------------------------------------------------
 * Term parser.  Sugar goes to core names: 0 inil, 1 itop, ~ ineg, /\ imeet,
 * \/ ijoin, (r = 0) feq0, (r = 1) feq1, (a , b) pair, A -> B and
 * (x : A) -> B Pi, t @ r application, let x = t in u  (\x -> u) t.
 * ---------------------------------------------------------------------- */
static Raw *pTerm(Toks *T);
static Raw *pAtom(Toks *T) {
  const char *t = next(T);
  if (!strcmp(t, "0")) return rid("inil");
  if (!strcmp(t, "1")) return rid("itop");
  if (!strcmp(t, "freshname")) return rmk(R_FRESH, NULL, NULL, NULL);
  if (!strcmp(t, "(")) {
    Raw *a = pTerm(T);
    if (is(T, ",")) { next(T); Raw *b = pTerm(T); expect(T, ")"); return rapp2(rid("pair"), a, b); }
    if (is(T, "=")) {
      next(T); const char *e = next(T); expect(T, ")");
      if (!strcmp(e, "0")) return rapp(rid("feq0"), a);
      if (!strcmp(e, "1")) return rapp(rid("feq1"), a);
      die("%s: (r = %s): an endpoint is 0 or 1", T->where, e);
    }
    expect(T, ")"); return a;
  }
  if (isIdent(t) && strcmp(t, "in") && strcmp(t, "let")) return rid(t);
  die("%s: unexpected '%s'", T->where, t); return NULL;
}
static Raw *pUnary(Toks *T) {
  if (is(T, "~")) { next(T); return rapp(rid("ineg"), pUnary(T)); }
  return pAtom(T);
}
static Raw *pApp(Toks *T) {
  Raw *f = pUnary(T);
  for (;;) {
    if (is(T, "\\") || is(T, "<") || is(T, "let")) { f = rapp(f, pTerm(T)); break; }
    if (stopTok(peek(T, 0))) break;
    f = rapp(f, pUnary(T));
  }
  return f;
}
static Raw *pAt(Toks *T) { Raw *l = pApp(T); while (is(T, "@")) { next(T); l = rapp(l, pApp(T)); } return l; }
static Raw *pMeet(Toks *T) { Raw *l = pAt(T); while (is(T, "/\\")) { next(T); l = rapp2(rid("imeet"), l, pAt(T)); } return l; }
static Raw *pJoin(Toks *T) { Raw *l = pMeet(T); while (is(T, "\\/")) { next(T); l = rapp2(rid("ijoin"), l, pMeet(T)); } return l; }
static Raw *pArrow(Toks *T) {
  if (is(T, "(") && isIdent(peek(T, 1)) && !strcmp(peek(T, 2), ":")) {
    next(T); char *x = xdup(next(T)); expect(T, ":"); Raw *A = pTerm(T); expect(T, ")");
    expect(T, "->"); Raw *B = pTerm(T);
    return rapp2(rid("Pi"), A, rlam(x, 0, B));
  }
  Raw *l = pJoin(T);
  if (is(T, "->")) { next(T); Raw *r = pTerm(T); return rapp2(rid("Pi"), l, rlam("_", 0, r)); }
  return l;
}
static Raw *pBinders(Toks *T, const char *close, int dim) {
  char *xs[64]; int n = 0;
  while (!is(T, close)) { if (n == 64) die("%s: too many binders", T->where); xs[n++] = xdup(next(T)); }
  next(T);
  if (!n) die("%s: binder list is empty", T->where);
  Raw *b = pTerm(T);
  while (n--) b = rlam(xs[n], dim, b);
  return b;
}
static Raw *pTerm(Toks *T) {
  if (is(T, "\\")) { next(T); return pBinders(T, "->", 0); }
  if (is(T, "<")) { next(T); return pBinders(T, ">", 1); }
  if (is(T, "let")) {
    next(T); char *x = xdup(next(T)); expect(T, "="); Raw *t = pTerm(T); expect(T, "in");
    Raw *u = pTerm(T); return rapp(rlam(x, 0, u), t);
  }
  return pArrow(T);
}

/* ------------------------------------------------------------------------
 * Patterns, definitions, symbols
 * ---------------------------------------------------------------------- */
typedef struct RPat { char *name; int n; struct RPat **sub; } RPat;
typedef struct Pat { int con; char *name; int n; struct Pat **sub; } Pat;   /* con < 0: variable */

typedef struct E E;
typedef struct { int npat; RPat **rp; Pat **pat; Raw *rhs; E *erhs; const char *where; } Clause;
typedef struct State State;
typedef struct {
  char *name; int arity; int ncl, capcl; Clause *cl;
  int isPat;          /* inspected by states; otherwise a DEF thunk */
  E *body; int defTag; State *s0; int busy;
} Def;

static Def *defs; static int ndefs, capdefs;
typedef struct { char *name; int tag; } ConSym;
static ConSym *cons; static int ncons, capcons;
typedef struct { char *name; Raw *type; long label; } Post;
static Post *posts; static int nposts, capposts;
typedef struct { char *name; Raw *type; } Sig;
static Sig *sigs; static int nsigs, capsigs;
typedef struct { char *name; const char *where; } AgentReq;
static AgentReq *agents; static int nagents, capagents;
typedef struct { Raw *t; const char *where; } EvalReq;
static EvalReq *evals; static int nevals, capevals;

static int findDef(const char *n) { for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, n)) return i; return -1; }
static int findCon(const char *n) { for (int i = 0; i < ncons; i++) if (!strcmp(cons[i].name, n)) return cons[i].tag; return -1; }
static int findPost(const char *n) { for (int i = 0; i < nposts; i++) if (!strcmp(posts[i].name, n)) return i; return -1; }
static Raw *findSig(const char *n) {
  for (int i = 0; i < nsigs; i++) if (!strcmp(sigs[i].name, n)) return sigs[i].type;
  int p = findPost(n); return p >= 0 ? posts[p].type : NULL;
}
static int getDef(const char *n) {
  int i = findDef(n); if (i >= 0) return i;
  Def d; memset(&d, 0, sizeof d); d.name = xdup(n); d.arity = -1; d.defTag = -1;
  PUSH(defs, ndefs, capdefs, d); return ndefs - 1;
}
static void addClause(const char *name, int npat, RPat **rp, Raw *rhs, const char *where) {
  Def *d = &defs[getDef(name)];
  if (d->arity < 0) d->arity = npat;
  else if (d->arity != npat) die("%s: %s has %d patterns, earlier clauses have %d", where, name, npat, d->arity);
  Clause c; memset(&c, 0, sizeof c); c.npat = npat; c.rp = rp; c.rhs = rhs; c.where = where;
  PUSH(d->cl, d->ncl, d->capcl, c);
}

/* ------------------------------------------------------------------------
 * Tags
 * ---------------------------------------------------------------------- */
enum { C_CON, C_LAM, C_SUP, C_ATOM, C_NE, C_NAME, C_DEF,
       C_APP, C_STATE, C_CMP1, C_CMP2, C_REIDX, C_DUP, C_ERA, C_EVAL, C_ROOT };
typedef struct { char *name; int cls, arity, dim, ref; void *ptr; } Tag;
static Tag *tags; static int ntags, captags;
static int *neOf; static int capNeOf;   /* demand tag -> its NE tag */
static int newTag(const char *name, int cls, int arity) {
  Tag t; memset(&t, 0, sizeof t); t.name = xdup(name); t.cls = cls; t.arity = arity; t.ref = -1;
  PUSH(tags, ntags, captags, t); return ntags - 1;
}
static int isValue(int c) { return c <= C_DEF; }
static int T_LAM, T_LAMD, T_SUP, T_ATOM, T_NAME, T_APP, T_CMP1, T_CMP2, T_REIDX, T_DUP, T_ERA, T_EVAL, T_ROOT;
static int K_lt, K_eq, K_gt, K_inil, K_icons, K_fnil, K_fcons, K_sys, K_nosys, K_cnil, K_ccons, K_pos, K_at0, K_at1;
static int D_isubst, D_fsubst, D_reflect;
static int neTag(int demand) {
  if (demand >= capNeOf) { int nc = demand * 2 + 16; neOf = xgrow(neOf, nc * sizeof(int));
    for (int i = capNeOf; i < nc; i++) neOf[i] = -1; capNeOf = nc; }
  if (neOf[demand] < 0) {
    char buf[256]; snprintf(buf, sizeof buf, "NE_%s", tags[demand].name);
    int t = newTag(buf, C_NE, tags[demand].arity); tags[t].ref = demand; neOf[demand] = t;
  }
  return neOf[demand];
}

/* ------------------------------------------------------------------------
 * Elaborated terms
 * ---------------------------------------------------------------------- */
enum { E_VAR, E_LAM, E_APP, E_CON, E_CALL, E_REF, E_ATOM, E_FRESH, E_REIDX, E_CMP };
struct E { int k; char *name; int dim, id, n; E **a; };
static E *emk(int k, int n) { E *e = xalloc(sizeof *e); e->k = k; e->n = n; e->a = xalloc(sizeof(E *) * (n ? n : 1)); return e; }
static E *evar(const char *x) { E *e = emk(E_VAR, 0); e->name = xdup(x); return e; }
static E *eapp(E *f, E *a) { E *e = emk(E_APP, 2); e->a[0] = f; e->a[1] = a; return e; }

/* Occurrences of the binding x in t (an inner binder of x shadows it). */
static int countUses(E *t, const char *x) {
  if (t->k == E_VAR) return !strcmp(t->name, x);
  if (t->k == E_LAM && !strcmp(t->name, x)) return 0;
  int c = 0; for (int i = 0; i < t->n; i++) c += countUses(t->a[i], x); return c;
}

/* ------------------------------------------------------------------------
 * Elaboration: resolve names, eta-expand partial applications.
 * ---------------------------------------------------------------------- */
static int etaCtr;
typedef struct Scope { const char *x; struct Scope *up; } Scope;
static int inScope(Scope *s, const char *x) { for (; s; s = s->up) if (!strcmp(s->x, x)) return 1; return 0; }
static E *elab(Raw *r, Scope *s, const char *where);
static void classifyDef(Def *d);
static E *saturate(int kind, int id, int arity, E **args, int nargs) {
  /* kind E_CON or E_CALL; eta-expand when short, apply the rest when long */
  int have = nargs < arity ? nargs : arity;
  char **xs = xalloc(sizeof(char *) * (arity + 1));
  E *e = emk(kind, arity); e->id = id;
  for (int i = 0; i < have; i++) e->a[i] = args[i];
  for (int i = have; i < arity; i++) { char b[32]; snprintf(b, sizeof b, "%%e%d", ++etaCtr); xs[i] = xdup(b); e->a[i] = evar(b); }
  for (int i = arity - 1; i >= have; i--) { E *l = emk(E_LAM, 1); l->name = xs[i]; l->a[0] = e; e = l; }
  for (int i = arity; i < nargs; i++) e = eapp(e, args[i]);
  return e;
}
static int rawHeadIsReflectable(Raw *t) {
  while (t->k == R_APP) t = t->a;
  return t->k == R_ID && (!strcmp(t->name, "Pi") || !strcmp(t->name, "Sigma") ||
                          !strcmp(t->name, "PathP") || !strcmp(t->name, "Path"));
}
static E *elab(Raw *r, Scope *s, const char *where) {
  Raw *spine[256]; int n = 0; Raw *h = r;
  while (h->k == R_APP) { if (n == 256) die("%s: application too long", where); spine[n++] = h->b; h = h->a; }
  E **args = xalloc(sizeof(E *) * (n + 1));
  for (int i = 0; i < n; i++) args[i] = elab(spine[n - 1 - i], s, where);
  E *hd = NULL;
  if (h->k == R_LAM) {
    Scope s2 = { h->name, s };
    hd = emk(E_LAM, 1); hd->name = xdup(h->name); hd->dim = h->dim; hd->a[0] = elab(h->a, &s2, where);
  } else if (h->k == R_FRESH) hd = emk(E_FRESH, 0);
  else {
    const char *x = h->name; int k;
    if (!strcmp(x, "_")) die("%s: '_' is not a term", where);
    if (inScope(s, x)) hd = evar(x);
    else if (!strcmp(x, "reidx")) {
      if (n < 3) die("%s: reidx takes a name, an interval and a term", where);
      hd = emk(E_REIDX, 3); for (int i = 0; i < 3; i++) hd->a[i] = args[i];
      for (int i = 3; i < n; i++) hd = eapp(hd, args[i]);
      return hd;
    } else if (!strcmp(x, "cmpname")) {
      if (n < 2) die("%s: cmpname takes two names", where);
      hd = emk(E_CMP, 2); hd->a[0] = args[0]; hd->a[1] = args[1];
      for (int i = 2; i < n; i++) hd = eapp(hd, args[i]);
      return hd;
    } else if ((k = findCon(x)) >= 0) return saturate(E_CON, k, tags[k].arity, args, n);
    else if ((k = findDef(x)) >= 0) {
      classifyDef(&defs[k]);
      if (defs[k].isPat) return saturate(E_CALL, k, defs[k].arity, args, n);
      hd = emk(E_REF, 0); hd->id = k;
    } else if ((k = findPost(x)) >= 0) {
      hd = emk(E_ATOM, 0); hd->id = (int)posts[k].label;
      if (rawHeadIsReflectable(posts[k].type)) {
        E *ty = elab(posts[k].type, NULL, where);
        E *c = emk(E_CALL, 2); c->id = D_reflect; c->a[0] = ty; c->a[1] = hd; hd = c;
      }
    } else die("%s: unknown name '%s'", where, x);
  }
  for (int i = 0; i < n; i++) hd = eapp(hd, args[i]);
  return hd;
}

static Pat *resolvePat(RPat *r, const char *where) {
  Pat *p = xalloc(sizeof *p); int k = findCon(r->name);
  p->name = r->name; p->con = -1;
  if (k >= 0) {
    if (tags[k].arity != r->n) die("%s: constructor %s takes %d fields in a pattern", where, r->name, tags[k].arity);
    p->con = k; p->n = r->n; p->sub = xalloc(sizeof(Pat *) * (r->n + 1));
    for (int i = 0; i < r->n; i++) p->sub[i] = resolvePat(r->sub[i], where);
  } else if (r->n) die("%s: %s is not a constructor", where, r->name);
  return p;
}
static void patVars(Pat *p, Scope **s) {
  if (p->con < 0) { if (strcmp(p->name, "_")) { Scope *n = xalloc(sizeof *n); n->x = p->name; n->up = *s; *s = n; } return; }
  for (int i = 0; i < p->n; i++) patVars(p->sub[i], s);
}
/* A definition is inspected by states unless its first clause is all
 * variables; then it is a thunk whose body is the closure of that clause. */
static void classifyDef(Def *d) {
  if (d->cl[0].pat) return;
  for (int c = 0; c < d->ncl; c++) {
    d->cl[c].pat = xalloc(sizeof(Pat *) * (d->arity + 1));
    for (int i = 0; i < d->arity; i++) d->cl[c].pat[i] = resolvePat(d->cl[c].rp[i], d->cl[c].where);
  }
  int allVar = 1;
  for (int i = 0; i < d->arity; i++) if (d->cl[0].pat[i]->con >= 0) allVar = 0;
  d->isPat = !allVar;
  if (allVar && d->ncl > 1) die("%s: %s: clauses after an all-variable clause are unreachable", d->cl[1].where, d->name);
}
static void elabDef(Def *d) {
  classifyDef(d);
  for (int c = 0; c < d->ncl; c++) {
    Clause *cl = &d->cl[c];
    if (cl->erhs) continue;
    Scope *s = NULL;
    for (int i = 0; i < d->arity; i++) patVars(cl->pat[i], &s);
    /* nonlinear patterns are not admitted */
    for (Scope *a = s; a; a = a->up) for (Scope *b = a->up; b; b = b->up)
      if (!strcmp(a->x, b->x)) die("%s: %s: variable %s bound twice", cl->where, d->name, a->x);
    cl->erhs = elab(cl->rhs, s, cl->where);
  }
  if (!d->isPat) {
    E *b = d->cl[0].erhs;
    for (int i = d->arity - 1; i >= 0; i--) { E *l = emk(E_LAM, 1); l->name = d->cl[0].pat[i]->name; l->a[0] = b; b = l; }
    d->body = b;
    if (d->defTag < 0) { d->defTag = newTag(d->name, C_DEF, 0); tags[d->defTag].ref = (int)(d - defs); }
  }
}

/* ------------------------------------------------------------------------
 * Descriptors
 * ---------------------------------------------------------------------- */
typedef struct { char k; int a, b; } End;           /* 'L' aux a, 'R' aux a, 'N' node a port b */
typedef struct { int tag; char lt; long lab; } Fresh; /* lt: 0 none, 'l' copy left, 'r' copy right, 'f' fresh, 'c' const */
typedef struct { int nf, capf; Fresh *f; int nc, capc; End *c; int la, ra; } Desc;
static Desc *B;
static End EL(int i) { End e = { 'L', i, 0 }; return e; }
static End ER(int i) { End e = { 'R', i, 0 }; return e; }
static End EN(int k, int p) { End e = { 'N', k, p }; return e; }
static int nn(int tag, char lt, long lab) { Fresh f = { tag, lt, lab }; PUSH(B->f, B->nf, B->capf, f); return B->nf - 1; }
static void cn(End a, End b) { PUSH(B->c, B->nc, B->capc, a); PUSH(B->c, B->nc, B->capc, b); }
static void verify(Desc *d, const char *what) {
  int *ul = xalloc(sizeof(int) * (d->la + 1)), *ur = xalloc(sizeof(int) * (d->ra + 1));
  int **un = xalloc(sizeof(int *) * (d->nf + 1));
  for (int i = 0; i < d->nf; i++) un[i] = xalloc(sizeof(int) * (tags[d->f[i].tag].arity + 1));
  for (int i = 0; i < d->nc; i++) {
    End e = d->c[i];
    if (e.k == 'L') { if (e.a < 0 || e.a >= d->la) die("descriptor %s: left aux %d out of range", what, e.a); ul[e.a]++; }
    else if (e.k == 'R') { if (e.a < 0 || e.a >= d->ra) die("descriptor %s: right aux %d out of range", what, e.a); ur[e.a]++; }
    else { if (e.b < 0 || e.b > tags[d->f[e.a].tag].arity) die("descriptor %s: port out of range", what); un[e.a][e.b]++; }
  }
  for (int i = 0; i < d->la; i++) if (ul[i] != 1) die("descriptor %s: left aux %d used %d times", what, i, ul[i]);
  for (int i = 0; i < d->ra; i++) if (ur[i] != 1) die("descriptor %s: right aux %d used %d times", what, i, ur[i]);
  for (int k = 0; k < d->nf; k++) for (int p = 0; p <= tags[d->f[k].tag].arity; p++)
    if (un[k][p] != 1) die("descriptor %s: new %s port %d used %d times", what, tags[d->f[k].tag].name, p, un[k][p]);
  for (int k = 0; k < d->nf; k++) free(un[k]);
  free(un); free(ul); free(ur);
}

/* fan: deliver the value at src to k consumers (ERA, a wire, or a
 * right-leaning DUP tree of k-1 fans). */
static void fan(End src, End *dst, int k) {
  if (k == 0) { int e = nn(T_ERA, 0, 0); cn(EN(e, 0), src); return; }
  End cur = src;
  for (int i = 0; i < k - 1; i++) {
    int d = nn(T_DUP, 'f', 0); cn(EN(d, 0), cur); cn(EN(d, 1), dst[i]); cur = EN(d, 2);
  }
  cn(cur, dst[k - 1]);
}

/* ------------------------------------------------------------------------
 * Emission of a term inside one replacement (plan 3.2)
 * ---------------------------------------------------------------------- */
typedef struct { const char *name; End e; End *leaf; int nleaf, next; } Bind;
static Bind *env; static int nenv, capenv;
static void bindv(const char *x, End e) { Bind b; memset(&b, 0, sizeof b); b.name = x; b.e = e; PUSH(env, nenv, capenv, b); }
/* Split each binding from index `from` on by its uses in t: ERA, a wire, or
 * a DUP tree; every DUP made here is a new duplication, so a fresh label. */
static void prepareFrom(int from, E *t) {
  for (int i = from; i < nenv; i++) {
    Bind *b = &env[i]; int k = countUses(t, b->name);
    b->nleaf = k; b->next = 0;
    if (k == 0) { int e = nn(T_ERA, 0, 0); cn(EN(e, 0), b->e); continue; }
    b->leaf = xalloc(sizeof(End) * k);
    End cur = b->e;
    for (int j = 0; j < k - 1; j++) { int d = nn(T_DUP, 'f', 0); cn(EN(d, 0), cur); b->leaf[j] = EN(d, 1); cur = EN(d, 2); }
    b->leaf[k - 1] = cur;
  }
}
static void envPop(int mark) { for (int i = mark; i < nenv; i++) free(env[i].leaf); nenv = mark; }
static End useVar(const char *x) {
  for (int i = nenv - 1; i >= 0; i--) if (!strcmp(env[i].name, x)) {
    if (env[i].next >= env[i].nleaf) die("internal: variable %s used more than counted", x);
    return env[i].leaf[env[i].next++];
  }
  die("internal: unbound variable %s", x); return EL(0);
}
static State *initialState(int def);
static int slotPort(State *s, int slot);
static int stateTagOf(State *s);
static void emit(E *t, End tg) {
  int k;
  switch (t->k) {
  case E_VAR: cn(useVar(t->name), tg); return;
  case E_LAM: {
    /* the binder is its body subnet: aux 0 the bound-variable wire, aux 1
     * the body result; the body is emitted here, once */
    k = nn(t->dim ? T_LAMD : T_LAM, 0, 0); cn(EN(k, 0), tg);
    int mark = nenv; bindv(t->name, EN(k, 1)); prepareFrom(mark, t->a[0]);
    emit(t->a[0], EN(k, 2));
    envPop(mark);
    return;
  }
  case E_APP: k = nn(T_APP, 0, 0); emit(t->a[0], EN(k, 0)); cn(EN(k, 1), tg); emit(t->a[1], EN(k, 2)); return;
  case E_CON: k = nn(t->id, 0, 0); cn(EN(k, 0), tg); for (int i = 0; i < t->n; i++) emit(t->a[i], EN(k, i + 1)); return;
  case E_CALL: {
    State *s0 = initialState(t->id);
    k = nn(stateTagOf(s0), 0, 0); cn(EN(k, 1), tg);
    for (int i = 0; i < t->n; i++) emit(t->a[i], EN(k, slotPort(s0, i)));
    return;
  }
  case E_REF: elabDef(&defs[t->id]); k = nn(defs[t->id].defTag, 0, 0); cn(EN(k, 0), tg); return;
  case E_ATOM: k = nn(T_ATOM, 'c', t->id); cn(EN(k, 0), tg); return;
  case E_FRESH: k = nn(T_NAME, 'f', 0); cn(EN(k, 0), tg); return;
  case E_REIDX: k = nn(T_REIDX, 0, 0); emit(t->a[2], EN(k, 0)); cn(EN(k, 1), tg); emit(t->a[0], EN(k, 2)); emit(t->a[1], EN(k, 3)); return;
  case E_CMP: k = nn(T_CMP1, 0, 0); emit(t->a[0], EN(k, 0)); cn(EN(k, 1), tg); emit(t->a[1], EN(k, 2)); return;
  }
}
/* Emit t at target with the bindings already made, then clear them. */
static void emitWith(E *t, End tg) { prepareFrom(0, t); emit(t, tg); envPop(0); }

/* ------------------------------------------------------------------------
 * Inspection states (plan 3.4)
 * ---------------------------------------------------------------------- */
typedef struct { int len; int *ix; } Path;
typedef struct { Path p; int con; } Seen;
struct State { int def, nslot, ncand, nseen, insp, fire, tag; Path *slot; int *cand; Seen *seen; char *key; };
static State **states; static int nstates, capstates;
static int stateTagOf(State *s) { return s->tag; }
static int pathEq(Path a, Path b) { return a.len == b.len && !memcmp(a.ix, b.ix, sizeof(int) * a.len); }
static int pathPrefix(Path a, Path b) { return a.len <= b.len && !memcmp(a.ix, b.ix, sizeof(int) * a.len); }
static Path pathExt(Path p, int j) { Path q; q.len = p.len + 1; q.ix = xalloc(sizeof(int) * q.len); memcpy(q.ix, p.ix, sizeof(int) * p.len); q.ix[p.len] = j; return q; }
static Path path1(int j) { Path q; q.len = 1; q.ix = xalloc(sizeof(int)); q.ix[0] = j; return q; }
/* The constructor a clause has at a path, or -1 for a variable there or above. */
static int patCon(Def *d, int c, Path p) {
  Pat *q = d->cl[c].pat[p.ix[0]];
  for (int i = 1; i < p.len; i++) { if (q->con < 0) return -1; q = q->sub[p.ix[i]]; }
  return q->con;
}
/* aux port (1-based port number) of a slot in a state node: principal is
 * the inspected slot, port 1 the result, then the other slots in order. */
static int slotPort(State *s, int slot) {
  if (slot == s->insp) return 0;
  return 2 + (slot < s->insp ? slot : slot - 1);
}
static int slotIndex(State *s, Path p) { for (int i = 0; i < s->nslot; i++) if (pathEq(s->slot[i], p)) return i; return -1; }
static int seenCon(State *s, Path p) { for (int i = 0; i < s->nseen; i++) if (pathEq(s->seen[i].p, p)) return s->seen[i].con; return -1; }
static State *mkState(int def, int nslot, Path *slot, int ncand, int *cand, int nseen, Seen *seen) {
  Str k = { 0 };
  sput(&k, "%d|", def);
  for (int i = 0; i < ncand; i++) sput(&k, "%d,", cand[i]);
  sput(&k, "|");
  for (int i = 0; i < nslot; i++) { for (int j = 0; j < slot[i].len; j++) sput(&k, "%d.", slot[i].ix[j]); sput(&k, ";"); }
  sput(&k, "|");
  for (int i = 0; i < nseen; i++) { for (int j = 0; j < seen[i].p.len; j++) sput(&k, "%d.", seen[i].p.ix[j]); sput(&k, "=%d;", seen[i].con); }
  for (int i = 0; i < nstates; i++) if (!strcmp(states[i]->key, k.s)) { free(k.s); return states[i]; }
  State *s = xalloc(sizeof *s);
  s->def = def; s->nslot = nslot; s->slot = slot; s->ncand = ncand; s->cand = cand; s->nseen = nseen; s->seen = seen; s->key = k.s;
  Def *d = &defs[def];
  if (!ncand) die("internal: state of %s with no candidate", d->name);
  s->insp = -1; s->fire = cand[0];
  for (int i = 0; i < nslot; i++) if (patCon(d, cand[0], slot[i]) >= 0) { s->insp = i; break; }
  if (s->insp >= 0) {
    char buf[256]; snprintf(buf, sizeof buf, "%s#%d", d->name, nstates);
    s->tag = newTag(buf, C_STATE, nslot); tags[s->tag].ptr = s;
  } else s->tag = -1;
  PUSH(states, nstates, capstates, s);
  return s;
}
static State *initialState(int def) {
  Def *d = &defs[def];
  elabDef(d);
  if (!d->isPat) die("internal: %s is not inspected", d->name);
  if (d->s0) return d->s0;
  Path *sl = xalloc(sizeof(Path) * d->arity);
  for (int i = 0; i < d->arity; i++) sl[i] = path1(i);
  int *cand = xalloc(sizeof(int) * d->ncl);
  for (int i = 0; i < d->ncl; i++) cand[i] = i;
  d->s0 = mkState(def, d->arity, sl, d->ncl, cand, 0, NULL);
  if (d->s0->insp < 0) die("internal: %s has a final initial state", d->name);
  return d->s0;
}

/* Rebuild the constructor seen at path p, its fields from the slots. */
static End rebuildAt(State *s, End *ends, Path p) {
  int i = slotIndex(s, p);
  if (i >= 0) return ends[i];
  int c = seenCon(s, p);
  if (c < 0) die("internal: nothing seen at a path of %s", defs[s->def].name);
  int k = nn(c, 0, 0);
  for (int j = 0; j < tags[c].arity; j++) cn(EN(k, j + 1), rebuildAt(s, ends, pathExt(p, j)));
  return EN(k, 0);
}
typedef struct { const char *name; Path p; } PVar;
static void collectVars(Pat *q, Path p, PVar **vs, int *n, int *cap) {
  if (q->con < 0) { PVar v = { q->name, p }; PUSH(*vs, *n, *cap, v); return; }
  for (int j = 0; j < q->n; j++) collectVars(q->sub[j], pathExt(p, j), vs, n, cap);
}
/* Fire the clause of a final state; ends[i] carries slot i. */
static void fireClause(State *s, End *ends) {
  Def *d = &defs[s->def]; Clause *cl = &d->cl[s->fire];
  PVar *vs = NULL; int nv = 0, cap = 0;
  for (int i = 0; i < d->arity; i++) collectVars(cl->pat[i], path1(i), &vs, &nv, &cap);
  int *covered = xalloc(sizeof(int) * (s->nslot + 1));
  for (int v = 0; v < nv; v++) {
    for (int i = 0; i < s->nslot; i++) if (pathPrefix(vs[v].p, s->slot[i])) covered[i]++;
    int uses = strcmp(vs[v].name, "_") ? countUses(cl->erhs, vs[v].name) : 0;
    if (uses == 0) {
      for (int i = 0; i < s->nslot; i++) if (pathPrefix(vs[v].p, s->slot[i])) { int e = nn(T_ERA, 0, 0); cn(EN(e, 0), ends[i]); }
    } else bindv(vs[v].name, rebuildAt(s, ends, vs[v].p));
  }
  for (int i = 0; i < s->nslot; i++) if (covered[i] != 1) die("internal: slot of %s covered %d times", d->name, covered[i]);
  free(covered); free(vs);
  emitWith(cl->erhs, EL(0));
}
/* Continue into state s2 with slot carriers ends: fire or build its node. */
static void enterState(State *s2, End *ends) {
  if (s2->insp < 0) { fireClause(s2, ends); return; }
  int k = nn(s2->tag, 0, 0);
  cn(EN(k, 1), EL(0));
  for (int i = 0; i < s2->nslot; i++) cn(EN(k, slotPort(s2, i)), ends[i]);
}

/* ------------------------------------------------------------------------
 * Generic families (plan 4)
 * ---------------------------------------------------------------------- */
static End rebuildRight(int vt) {
  int v = nn(vt, 'r', 0);
  for (int j = 0; j < tags[vt].arity; j++) cn(EN(v, j + 1), ER(j));
  return EN(v, 0);
}
static void famNE(int ft, int vt) {
  int ne = nn(neTag(ft), 'l', 0);
  cn(EN(ne, 0), EL(0));
  cn(EN(ne, 1), rebuildRight(vt));
  for (int i = 1; i < tags[ft].arity; i++) cn(EN(ne, i + 1), EL(i));
}
static void famBranch(int ft, int vt) {
  int a = tags[ft].arity;
  if (vt == K_nosys) {
    int n = nn(K_nosys, 0, 0); cn(EN(n, 0), EL(0));
    for (int i = 1; i < a; i++) { int e = nn(T_ERA, 0, 0); cn(EN(e, 0), EL(i)); }
    return;
  }
  int s = nn(K_sys, 0, 0); cn(EN(s, 0), EL(0)); cn(EN(s, 1), ER(0));
  int f1 = nn(ft, 'l', 0), f2 = nn(ft, 'l', 0);
  cn(EN(f1, 0), ER(1)); cn(EN(f2, 0), ER(2));
  cn(EN(f1, 1), EN(s, 2)); cn(EN(f2, 1), EN(s, 3));
  for (int i = 1; i < a; i++) {
    int d = nn(T_DUP, 'f', 0); cn(EN(d, 0), EL(i)); cn(EN(d, 1), EN(f1, i + 1)); cn(EN(d, 2), EN(f2, i + 1));
  }
}
/* DUP_k(u,v) >< LAM(x,t): L0, L1, SUP_k on x, DUP_k on t.  The body
 * subnet stays one subnet. */
static void famCopyLam(int vt) {
  int l0 = nn(vt, 0, 0), l1 = nn(vt, 0, 0), sp = nn(T_SUP, 'l', 0), d = nn(T_DUP, 'l', 0);
  cn(EN(l0, 0), EL(0)); cn(EN(l1, 0), EL(1));
  cn(EN(sp, 0), ER(0)); cn(EN(d, 0), ER(1));
  cn(EN(l0, 1), EN(sp, 1)); cn(EN(l1, 1), EN(sp, 2));
  cn(EN(l0, 2), EN(d, 1)); cn(EN(l1, 2), EN(d, 2));
}
/* DUP_k >< SUP_k: annihilate.  DUP_k >< SUP_j: commute. */
static void famDupSup(int same) {
  if (same) { cn(EL(0), ER(0)); cn(EL(1), ER(1)); return; }
  int s0 = nn(T_SUP, 'r', 0), s1 = nn(T_SUP, 'r', 0), d0 = nn(T_DUP, 'l', 0), d1 = nn(T_DUP, 'l', 0);
  cn(EN(s0, 0), EL(0)); cn(EN(s1, 0), EL(1));
  cn(EN(d0, 0), ER(0)); cn(EN(d1, 0), ER(1));
  cn(EN(d0, 1), EN(s0, 1)); cn(EN(d0, 2), EN(s1, 1));
  cn(EN(d1, 1), EN(s0, 2)); cn(EN(d1, 2), EN(s1, 2));
}
/* Any other demand F >< SUP_k(a,b): SUP_k(F a, F b), F's other inputs
 * fanned by DUP_k, so the two sides stay correlated. */
static void famSup(int ft) {
  int a = tags[ft].arity;
  int s = nn(T_SUP, 'r', 0), f0 = nn(ft, 'l', 0), f1 = nn(ft, 'l', 0);
  cn(EN(s, 0), EL(0));
  cn(EN(f0, 0), ER(0)); cn(EN(f1, 0), ER(1));
  cn(EN(f0, 1), EN(s, 1)); cn(EN(f1, 1), EN(s, 2));
  for (int i = 1; i < a; i++) {
    int d = nn(T_DUP, 'r', 0); cn(EN(d, 0), EL(i)); cn(EN(d, 1), EN(f0, i + 1)); cn(EN(d, 2), EN(f1, i + 1));
  }
}
static void famCopy(int vt) {
  int v1 = nn(vt, 'r', 0), v2 = nn(vt, 'r', 0);
  cn(EN(v1, 0), EL(0)); cn(EN(v2, 0), EL(1));
  for (int j = 0; j < tags[vt].arity; j++) {
    int d = nn(T_DUP, 'l', 0); cn(EN(d, 0), ER(j)); cn(EN(d, 1), EN(v1, j + 1)); cn(EN(d, 2), EN(v2, j + 1));
  }
}
static void famErase(int vt) { for (int j = 0; j < tags[vt].arity; j++) { int e = nn(T_ERA, 0, 0); cn(EN(e, 0), ER(j)); } }
static void famForce(int ft, int vt) {
  Def *d = &defs[tags[vt].ref]; elabDef(d);
  int k = nn(ft, 'l', 0);
  for (int i = 0; i < tags[ft].arity; i++) cn(EN(k, i + 1), EL(i));
  emitWith(d->body, EN(k, 0));
}
/* LAM(x,t) >< APP(r,a): x = a, t = r.  The existing body is spliced in. */
static void famBeta(void) { cn(EL(1), ER(0)); cn(EL(0), ER(1)); }
/* REIDX: aux 0 result, aux 1 name, aux 2 interval. */
static void famReidx(int vt) {
  int vc = tags[vt].cls;
  if (vt == K_inil || vt == K_icons || vt == K_fnil || vt == K_fcons) {
    E *c = emk(E_CALL, 3); c->id = (vt == K_inil || vt == K_icons) ? D_isubst : D_fsubst;
    c->a[0] = evar("%n"); c->a[1] = evar("%r"); c->a[2] = evar("%v");
    bindv("%n", EL(1)); bindv("%r", EL(2)); bindv("%v", rebuildRight(vt));
    emitWith(c, EL(0));
    return;
  }
  if (vc == C_LAM) {
    /* the bound variable passes through; the body result is reindexed */
    int l = nn(vt, 0, 0), r = nn(T_REIDX, 0, 0);
    cn(EN(l, 0), EL(0)); cn(EN(l, 1), ER(0));
    cn(EN(r, 0), ER(1)); cn(EN(r, 1), EN(l, 2)); cn(EN(r, 2), EL(1)); cn(EN(r, 3), EL(2));
    return;
  }
  if (vc == C_CON || vc == C_ATOM || vc == C_NAME) {
    int m = tags[vt].arity, v = nn(vt, 'r', 0);
    cn(EN(v, 0), EL(0));
    End *ns = xalloc(sizeof(End) * (m + 1)), *rs = xalloc(sizeof(End) * (m + 1));
    for (int j = 0; j < m; j++) {
      int r = nn(T_REIDX, 0, 0); cn(EN(r, 0), ER(j)); cn(EN(r, 1), EN(v, j + 1));
      ns[j] = EN(r, 2); rs[j] = EN(r, 3);
    }
    fan(EL(1), ns, m); fan(EL(2), rs, m); free(ns); free(rs);
    return;
  }
  if (vc == C_NE) {
    int ft = tags[vt].ref;
    if (tags[ft].cls == C_STATE) {
      /* re-invoke the definition from its initial state on the reindexed
       * arguments, so every test it makes runs again */
      State *s = tags[ft].ptr; Def *d = &defs[s->def]; State *s0 = initialState(s->def);
      End *ends = xalloc(sizeof(End) * (s->nslot + 1));
      for (int i = 0; i < s->nslot; i++) ends[i] = ER(slotPort(s, i) == 0 ? 0 : slotPort(s, i) - 1);
      int k = nn(s0->tag, 0, 0); cn(EN(k, 1), EL(0));
      End *ns = xalloc(sizeof(End) * (d->arity + 1)), *rs = xalloc(sizeof(End) * (d->arity + 1));
      for (int a = 0; a < d->arity; a++) {
        int r = nn(T_REIDX, 0, 0);
        cn(EN(r, 0), rebuildAt(s, ends, path1(a)));
        cn(EN(r, 1), EN(k, slotPort(s0, a)));
        ns[a] = EN(r, 2); rs[a] = EN(r, 3);
      }
      fan(EL(1), ns, d->arity); fan(EL(2), rs, d->arity);
      free(ns); free(rs); free(ends);
      return;
    }
    int a = tags[ft].arity, f = nn(ft, 'r', 0);
    cn(EN(f, 1), EL(0));
    End *ns = xalloc(sizeof(End) * (a + 1)), *rs = xalloc(sizeof(End) * (a + 1));
    for (int j = 0; j < a; j++) {
      int r = nn(T_REIDX, 0, 0); cn(EN(r, 0), ER(j)); cn(EN(r, 1), j == 0 ? EN(f, 0) : EN(f, j + 1));
      ns[j] = EN(r, 2); rs[j] = EN(r, 3);
    }
    fan(EL(1), ns, a); fan(EL(2), rs, a); free(ns); free(rs);
    return;
  }
  die("internal: REIDX meets %s", tags[vt].name);
}
static void famState(int st, int vt) {
  State *s = tags[st].ptr; Def *d = &defs[s->def]; int vc = tags[vt].cls;
  if (vc == C_ATOM || vc == C_NE) { famNE(st, vt); return; }
  Path p = s->slot[s->insp];
  int specific = 0, anyVar = 0;
  for (int i = 0; i < s->ncand; i++) {
    int c = patCon(d, s->cand[i], p);
    if (c < 0) anyVar = 1; else if (vc == C_CON && c == vt) specific = 1;
  }
  End *ends;
  if (specific) {
    int m = tags[vt].arity, ns = s->nslot - 1 + m;
    Path *sl = xalloc(sizeof(Path) * (ns + 1)); ends = xalloc(sizeof(End) * (ns + 1));
    int o = 0;
    for (int i = 0; i < s->nslot; i++) {
      if (i == s->insp) { for (int j = 0; j < m; j++) { sl[o] = pathExt(p, j); ends[o++] = ER(j); } }
      else { sl[o] = s->slot[i]; ends[o++] = EL(slotPort(s, i) - 1); }
    }
    int *cand = xalloc(sizeof(int) * s->ncand), nc = 0;
    for (int i = 0; i < s->ncand; i++) { int c = patCon(d, s->cand[i], p); if (c < 0 || c == vt) cand[nc++] = s->cand[i]; }
    Seen *seen = xalloc(sizeof(Seen) * (s->nseen + 1));
    memcpy(seen, s->seen, sizeof(Seen) * s->nseen); seen[s->nseen].p = p; seen[s->nseen].con = vt;
    enterState(mkState(s->def, ns, sl, nc, cand, s->nseen + 1, seen), ends);
    free(ends);
    return;
  }
  if (vt == K_sys || vt == K_nosys) { famBranch(st, vt); return; }
  if (!anyVar) { famNE(st, vt); return; }
  /* default: the value is definitively not any constructor a candidate
   * expects here; continue with the clauses that have a variable here */
  ends = xalloc(sizeof(End) * (s->nslot + 1));
  for (int i = 0; i < s->nslot; i++) ends[i] = i == s->insp ? rebuildRight(vt) : EL(slotPort(s, i) - 1);
  int *cand = xalloc(sizeof(int) * s->ncand), nc = 0;
  for (int i = 0; i < s->ncand; i++) if (patCon(d, s->cand[i], p) < 0) cand[nc++] = s->cand[i];
  enterState(mkState(s->def, s->nslot, s->slot, nc, cand, s->nseen, s->seen), ends);
  free(ends);
}

/* Build the descriptor for demand lt meeting value rt. */
static Desc *build(int lt, int rt, int extra) {
  Desc *d = xalloc(sizeof *d); B = d; d->la = tags[lt].arity; d->ra = tags[rt].arity;
  int lc = tags[lt].cls, rc = tags[rt].cls;
  if (lc == C_DUP && rc == C_LAM) famCopyLam(rt);
  else if (lc == C_DUP && rc == C_SUP) famDupSup(extra);
  else if (lc == C_DUP) famCopy(rt);
  else if (lc == C_ERA) famErase(rt);
  else if (rc == C_DEF) famForce(lt, rt);
  else if (lc == C_EVAL) cn(EL(0), rebuildRight(rt));
  else if (rc == C_SUP) famSup(lt);
  else if (lc == C_REIDX) famReidx(rt);
  else if (lc == C_STATE) famState(lt, rt);
  else if (rc == C_CON && (rt == K_sys || rt == K_nosys)) famBranch(lt, rt);
  else if (lc == C_APP && rc == C_LAM) famBeta();
  else if (lc == C_CMP1 && rc == C_NAME) { int c = nn(T_CMP2, 'r', 0); cn(EN(c, 0), EL(1)); cn(EN(c, 1), EL(0)); famErase(rt); }
  else if (lc == C_CMP2 && rc == C_NAME) { int o = nn(extra < 0 ? K_lt : extra > 0 ? K_gt : K_eq, 0, 0); cn(EN(o, 0), EL(0)); }
  else famNE(lt, rt);
  char what[600]; snprintf(what, sizeof what, "%s >< %s", tags[lt].name, tags[rt].name);
  verify(d, what);
  B = NULL;
  return d;
}
typedef struct { int lt, rt, extra; Desc *d; } Cached;
static Cached *cache; static int capcache, ncache;
static unsigned hkey(int a, int b, int c) { return (unsigned)a * 2654435761u ^ (unsigned)b * 40503u ^ (unsigned)(c + 1) * 97u; }
static Desc *getDesc(int lt, int rt, int extra) {
  if (ncache * 2 >= capcache) {
    Cached *old = cache; int oc = capcache; capcache = capcache ? capcache * 2 : 1024;
    cache = xalloc(sizeof(Cached) * capcache);
    for (int i = 0; i < oc; i++) if (old[i].d) {
      unsigned h = hkey(old[i].lt, old[i].rt, old[i].extra) % capcache;
      while (cache[h].d) h = (h + 1) % capcache;
      cache[h] = old[i];
    }
    free(old);
  }
  unsigned h = hkey(lt, rt, extra) % capcache;
  while (cache[h].d) { if (cache[h].lt == lt && cache[h].rt == rt && cache[h].extra == extra) return cache[h].d; h = (h + 1) % capcache; }
  Desc *d = build(lt, rt, extra);
  h = hkey(lt, rt, extra) % capcache;
  while (cache[h].d) h = (h + 1) % capcache;
  cache[h].lt = lt; cache[h].rt = rt; cache[h].extra = extra; cache[h].d = d; ncache++;
  return d;
}

/* ------------------------------------------------------------------------
 * The net
 * ---------------------------------------------------------------------- */
typedef struct { int n, p; } PR;
typedef struct { int tag; long lab; PR *port; } Node;
static Node *nodes; static int nnodes, capnodes;
static long labelCtr;
static long steps;
static int alloc(int tag, long lab) {
  Node x; x.tag = tag; x.lab = lab; x.port = xalloc(sizeof(PR) * (tags[tag].arity + 1));
  for (int i = 0; i <= tags[tag].arity; i++) x.port[i].n = -1;
  PUSH(nodes, nnodes, capnodes, x); return nnodes - 1;
}
static PR pr(int n, int p) { PR r = { n, p }; return r; }
static PR partner(PR a) { return nodes[a.n].port[a.p]; }
static void link(PR a, PR b) { nodes[a.n].port[a.p] = b; nodes[b.n].port[b.p] = a; }
static int prLess(PR a, PR b) { return a.n < b.n || (a.n == b.n && a.p < b.p); }
static int prEq(PR a, PR b) { return a.n == b.n && a.p == b.p; }

/* Apply a descriptor to demand x and value y (y = -1: no right side). */
static void instantiate(Desc *d, int x, int y) {
  int base = nnodes;
  int *nw = xalloc(sizeof(int) * (d->nf + 1));
  for (int i = 0; i < d->nf; i++) {
    long lab = 0; Fresh f = d->f[i];
    if (f.lt == 'l') lab = nodes[x].lab; else if (f.lt == 'r') lab = nodes[y].lab;
    else if (f.lt == 'f') lab = ++labelCtr; else if (f.lt == 'c') lab = f.lab;
    nw[i] = alloc(f.tag, lab);
  }
#define TOPR(e) ((e).k == 'L' ? pr(x, (e).a + 1) : (e).k == 'R' ? pr(y, (e).a + 1) : pr(nw[(e).a], (e).b))
#define ISOLD(q) ((q).n == x || (y >= 0 && (q).n == y))
#define ISNEW(q) ((q).n >= base)
  int la = d->la, ra = d->ra;
  PR *dL = xalloc(sizeof(PR) * (la + 1)), *dR = xalloc(sizeof(PR) * (ra + 1));
  PR *xL = xalloc(sizeof(PR) * (la + 1)), *xR = xalloc(sizeof(PR) * (ra + 1));
  for (int i = 0; i < la; i++) xL[i] = nodes[x].port[i + 1];
  for (int j = 0; j < ra; j++) xR[j] = nodes[y].port[j + 1];
#define DOF(q) ((q).n == x ? dL[(q).p - 1] : dR[(q).p - 1])
#define EXT(q) ((q).n == x ? xL[(q).p - 1] : xR[(q).p - 1])
  for (int i = 0; i < d->nc; i += 2) {
    PR a = TOPR(d->c[i]), b = TOPR(d->c[i + 1]);
    if (ISOLD(a)) { if (a.n == x) dL[a.p - 1] = b; else dR[a.p - 1] = b; }
    if (ISOLD(b)) { if (b.n == x) dL[b.p - 1] = a; else dR[b.p - 1] = a; }
  }
  for (int i = 0; i < d->nc; i += 2) {
    PR a = TOPR(d->c[i]), b = TOPR(d->c[i + 1]);
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
    if (n < 0) continue;
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
  free(nodes[x].port); nodes[x].port = NULL; nodes[x].tag = -1;
  if (y >= 0) { free(nodes[y].port); nodes[y].port = NULL; nodes[y].tag = -1; }
}
static void fire(int x, int y) {
  int extra = 0;
  if (tags[nodes[x].tag].cls == C_CMP2 && tags[nodes[y].tag].cls == C_NAME)
    extra = nodes[x].lab < nodes[y].lab ? -1 : nodes[x].lab > nodes[y].lab ? 1 : 0;
  else if (tags[nodes[x].tag].cls == C_DUP && tags[nodes[y].tag].cls == C_SUP)
    extra = nodes[x].lab == nodes[y].lab;
  Desc *d = getDesc(nodes[x].tag, nodes[y].tag, extra);
  instantiate(d, x, y);
  steps++;
}

/* Demand: bring a value to the in-port p (plan 8). */
static PR *stk; static int nstk, capstk;
static void whnf(PR p) {
  nstk = 0; PUSH(stk, nstk, capstk, p);
  while (nstk) {
    PR top = stk[nstk - 1], q = partner(top);
    if (q.n < 0) die("internal: dangling port");
    int qc = tags[nodes[q.n].tag].cls;
    if (q.p == 0 && isValue(qc)) {
      int tc = tags[nodes[top.n].tag].cls;
      if (top.p == 0 && tc >= C_APP && tc != C_ROOT) fire(top.n, q.n);
      nstk--; continue;
    }
    if (q.p == 0) die("internal: two inputs meet (%s, %s)", tags[nodes[top.n].tag].name, tags[nodes[q.n].tag].name);
    PUSH(stk, nstk, capstk, pr(q.n, 0));
  }
}

/* ------------------------------------------------------------------------
 * Read-back (plan 6).  Structural printing.
 * ---------------------------------------------------------------------- */
static Str out;
static void readback(PR p);
static int mkIVar(long lab) {
  int nm = alloc(T_NAME, lab), ps = alloc(K_pos, 0), cc = alloc(K_ccons, 0), cz = alloc(K_cnil, 0);
  int ic = alloc(K_icons, 0), il = alloc(K_inil, 0);
  link(pr(ps, 1), pr(nm, 0)); link(pr(cc, 1), pr(ps, 0)); link(pr(cc, 2), pr(cz, 0));
  link(pr(ic, 1), pr(cc, 0)); link(pr(ic, 2), pr(il, 0));
  return ic;
}
static int mkEndpoint(int one) {
  if (!one) return alloc(K_inil, 0);
  int ic = alloc(K_icons, 0), cz = alloc(K_cnil, 0), il = alloc(K_inil, 0);
  link(pr(ic, 1), pr(cz, 0)); link(pr(ic, 2), pr(il, 0));
  return ic;
}
static void printLabel(int atom, long lab) {
  for (int i = 0; i < nposts; i++) if (posts[i].label == lab) { sput(&out, "%s", posts[i].name); return; }
  sput(&out, atom ? "x%ld" : "#%ld", lab);
}
static void readPath(int ne, State *s, Path p) {
  int i = slotIndex(s, p);
  if (i >= 0) { int sp = slotPort(s, i); readback(pr(ne, sp == 0 ? 1 : sp)); return; }
  int c = seenCon(s, p);
  if (!tags[c].arity) { sput(&out, "%s", tags[c].name); return; }
  sput(&out, "(%s", tags[c].name);
  for (int j = 0; j < tags[c].arity; j++) { sput(&out, " "); readPath(ne, s, pathExt(p, j)); }
  sput(&out, ")");
}
/* The clauses of a face already read: lists of (sign, label).  -1 when
 * the face is not built of constructors throughout (a neutral face). */
typedef struct { int n; int sg[64]; long lab[64]; } FCl;
static int faceClauses(PR p, FCl *cl, int max) {
  int n = 0; PR q = partner(p);
  while (nodes[q.n].tag == K_fcons) {
    if (n == max) die("read-back: face too large");
    FCl *c = &cl[n++]; c->n = 0;
    PR l = partner(pr(q.n, 1));
    while (nodes[l.n].tag == K_ccons) {
      PR lit = partner(pr(l.n, 1)); int lt = nodes[lit.n].tag;
      if (lt != K_at0 && lt != K_at1) return -1;
      PR nm = partner(pr(lit.n, 1));
      if (tags[nodes[nm.n].tag].cls != C_NAME) return -1;
      if (c->n == 64) die("read-back: clause too large");
      c->sg[c->n] = lt == K_at1;
      c->lab[c->n++] = nodes[nm.n].lab;
      l = partner(pr(l.n, 2));
    }
    if (nodes[l.n].tag != K_cnil) return -1;
    q = partner(pr(q.n, 2));
  }
  return nodes[q.n].tag == K_fnil ? n : -1;
}
static void readSys(int s) {
  sput(&out, "(sys ");
  readback(pr(s, 1));
  FCl *cl = xalloc(sizeof(FCl) * 64); int k = faceClauses(pr(s, 1), cl, 64);
  sput(&out, " ");
  if (k == 0) sput(&out, "_");
  else if (k < 0 || (k == 1 && cl[0].n == 0)) readback(pr(s, 2));
  else {
    /* each clause of the face: restrict the branch to it (spec section 6) */
    PR e = partner(pr(s, 2)); nodes[s].port[2].n = -1;
    PR *leaf = xalloc(sizeof(PR) * k);
    PR cur = e;
    for (int i = 0; i < k - 1; i++) { int d = alloc(T_DUP, ++labelCtr); link(pr(d, 0), cur); leaf[i] = pr(d, 1); cur = pr(d, 2); }
    leaf[k - 1] = cur;
    sput(&out, "{");
    for (int i = 0; i < k; i++) {
      PR v = leaf[i];
      for (int j = 0; j < cl[i].n; j++) {
        int r = alloc(T_REIDX, 0), nm = alloc(T_NAME, cl[i].lab[j]), iv = mkEndpoint(cl[i].sg[j]);
        link(pr(r, 0), v); link(pr(r, 2), pr(nm, 0)); link(pr(r, 3), pr(iv, 0));
        v = pr(r, 1);
      }
      int h = alloc(T_ROOT, 0); link(pr(h, 0), v);
      if (i) sput(&out, "; ");
      readback(pr(h, 0));
    }
    sput(&out, "}");
    free(leaf);
  }
  free(cl);
  sput(&out, " ");
  readback(pr(s, 3));
  sput(&out, ")");
}
static void readback(PR p) {
  for (;;) {
    whnf(p);
    PR q = partner(p); int t = nodes[q.n].tag; int c = tags[t].cls;
    if (c == C_DEF) { int e = alloc(T_EVAL, 0); link(pr(e, 0), q); link(pr(e, 1), p); continue; }
    if (c == C_SUP) { sput(&out, "{"); readback(pr(q.n, 1)); sput(&out, " | "); readback(pr(q.n, 2)); sput(&out, "}"); return; }
    if (c == C_LAM) {
      long lab = ++labelCtr; int arg;
      if (tags[t].dim) { arg = mkIVar(lab); sput(&out, "<#%ld> ", lab); }
      else { arg = alloc(T_ATOM, lab); sput(&out, "\\x%ld -> ", lab); }
      int a = alloc(T_APP, 0); link(pr(a, 0), q); link(pr(a, 1), p); link(pr(a, 2), pr(arg, 0));
      continue;
    }
    if (c == C_ATOM) { printLabel(1, nodes[q.n].lab); return; }
    if (c == C_NAME) { printLabel(0, nodes[q.n].lab); return; }
    if (c == C_CON) {
      if (t == K_sys) { readSys(q.n); return; }
      if (!tags[t].arity) { sput(&out, "%s", tags[t].name); return; }
      sput(&out, "(%s", tags[t].name);
      for (int j = 0; j < tags[t].arity; j++) { sput(&out, " "); readback(pr(q.n, j + 1)); }
      sput(&out, ")");
      return;
    }
    if (c == C_NE) {
      int ft = tags[t].ref, fc = tags[ft].cls, n = q.n;
      if (fc == C_STATE) {
        State *s = tags[ft].ptr; Def *d = &defs[s->def];
        sput(&out, "(%s", d->name);
        for (int a = 0; a < d->arity; a++) { sput(&out, " "); readPath(n, s, path1(a)); }
        sput(&out, ")");
      } else if (fc == C_APP) { sput(&out, "("); readback(pr(n, 1)); sput(&out, " "); readback(pr(n, 2)); sput(&out, ")"); }
      else if (fc == C_CMP1) { sput(&out, "(cmpname "); readback(pr(n, 1)); sput(&out, " "); readback(pr(n, 2)); sput(&out, ")"); }
      else if (fc == C_CMP2) { sput(&out, "(cmpname "); printLabel(0, nodes[n].lab); sput(&out, " "); readback(pr(n, 1)); sput(&out, ")"); }
      else die("internal: NE of %s", tags[ft].name);
      return;
    }
    die("internal: read-back meets %s", tags[t].name);
  }
}

/* ------------------------------------------------------------------------
 * The identity agent (plan 7, spec section 24).  A transformation of
 * syntax into definitions, emitted like any other.
 * ---------------------------------------------------------------------- */
static int genCtr;
static char *gname(const char *b) { char buf[64]; snprintf(buf, sizeof buf, "%s%d", b, ++genCtr); return xdup(buf); }
static int rawMentions(Raw *r, const char *x) {
  if (!r) return 0;
  if (r->k == R_ID) return !strcmp(r->name, x);
  if (r->k == R_LAM) return strcmp(r->name, x) && rawMentions(r->a, x);
  if (r->k == R_APP) return rawMentions(r->a, x) || rawMentions(r->b, x);
  return 0;
}
/* Telescope of a Pi type: Pi A (\x -> B). */
typedef struct { int n; char *x[32]; Raw *A[32]; Raw *res; } Tele;
static int isPi(Raw *t, Raw **A, Raw **L) {
  if (t->k == R_APP && t->a->k == R_APP && t->a->a->k == R_ID && !strcmp(t->a->a->name, "Pi") && t->b->k == R_LAM) {
    *A = t->a->b; *L = t->b; return 1;
  }
  return 0;
}
static void tele(Raw *t, Tele *T) {
  Raw *A, *L; T->n = 0;
  while (isPi(t, &A, &L)) { if (T->n == 32) die("agent: telescope too long"); T->x[T->n] = L->name; T->A[T->n++] = A; t = L->a; }
  T->res = t;
}
/* Is t a node: a head with a non-dependent signature of its arity. */
static int nodeOf(Raw *t, Scope *g, Raw **head, Raw **args, int *nargs, Tele *T) {
  int n = 0; Raw *h = t; Raw *sp[32];
  while (h->k == R_APP) { if (n == 32) return 0; sp[n++] = h->b; h = h->a; }
  if (h->k != R_ID || inScope(g, h->name) || n == 0) return 0;
  Raw *sig = findSig(h->name); if (!sig) return 0;
  tele(sig, T);
  if (T->n != n) return 0;
  for (int i = 0; i < T->n; i++) {
    for (int j = i + 1; j < T->n; j++) if (rawMentions(T->A[j], T->x[i])) return 0;
    if (rawMentions(T->res, T->x[i])) return 0;
  }
  *head = h; *nargs = n;
  for (int i = 0; i < n; i++) args[i] = sp[n - 1 - i];
  return 1;
}
static Raw *rPath(Raw *T, Raw *a, Raw *b) { return rapp(rapp2(rid("Path"), T, a), b); }
static Raw *agReal(Raw *t, Raw *T, Raw *y, Scope *g) {
  Raw *h, *args[32]; int n; Tele S;
  if (!nodeOf(t, g, &h, args, &n, &S)) return rPath(T, t, y);
  char *xs[32]; Raw *body;
  for (int k = 0; k < n; k++) xs[k] = gname("x");
  Raw *hx = h; for (int k = 0; k < n; k++) hx = rapp(hx, rid(xs[k]));
  body = rPath(S.res, hx, y);
  for (int k = n - 1; k >= 0; k--) {
    char *r = gname("r");
    body = rapp2(rid("Sigma"), agReal(args[k], S.A[k], rid(xs[k]), g), rlam(r, 0, body));
    body = rapp2(rid("Sigma"), S.A[k], rlam(xs[k], 0, body));
  }
  return body;
}
static Raw *agC(Raw *t, Raw *T, Raw *y, Raw *u, Scope *g) {
  Raw *h, *args[32]; int n; Tele S;
  if (!nodeOf(t, g, &h, args, &n, &S)) return u;
  /* u = (x1 , (r1 , ( ... (xn , (rn , q))))) */
  char *sv = gname("s"), *iv = gname("i");
  Raw *cur = rid(sv), *xk[32], *rk[32];
  for (int k = 0; k < n; k++) {
    xk[k] = rapp(rid("fst"), cur); cur = rapp(rid("snd"), cur);
    rk[k] = rapp(rid("fst"), cur); cur = rapp(rid("snd"), cur);
  }
  Raw *q = cur, *cong = h;
  for (int k = 0; k < n; k++) cong = rapp(cong, rapp(agC(args[k], S.A[k], xk[k], rk[k], g), rid(iv)));
  Raw *body = rapp(rapp2(rid("compose"), S.res, rlam(iv, 1, cong)), q);
  return rapp(rlam(sv, 0, body), u);
}
static Raw *agCinv(Raw *t, Raw *T, Raw *y, Raw *q, Scope *g) {
  Raw *h, *args[32]; int n; Tele S;
  if (!nodeOf(t, g, &h, args, &n, &S)) return q;
  Raw *acc = q;
  for (int k = n - 1; k >= 0; k--) {
    Raw *refl = rlam(gname("_"), 1, args[k]);
    acc = rapp2(rid("pair"), agCinv(args[k], S.A[k], args[k], refl, g), acc);
    acc = rapp2(rid("pair"), args[k], acc);
  }
  return acc;
}
static RPat **varPats(Tele *G, const char *extra) {
  RPat **ps = xalloc(sizeof(RPat *) * (G->n + 2));
  for (int i = 0; i < G->n; i++) { ps[i] = xalloc(sizeof(RPat)); ps[i]->name = G->x[i]; }
  ps[G->n] = xalloc(sizeof(RPat)); ps[G->n]->name = "y";
  ps[G->n + 1] = xalloc(sizeof(RPat)); ps[G->n + 1]->name = (char *)extra;
  return ps;
}
static Raw *callG(Tele *G, const char *name, Raw *last) {
  Raw *c = rid(name);
  for (int i = 0; i < G->n; i++) c = rapp(c, rid(G->x[i]));
  return rapp(rapp(c, rid("y")), last);
}
static void genAgent(AgentReq *a) {
  Raw *sig = findSig(a->name);
  if (!sig) die("%s: agent %s has no signature", a->where, a->name);
  Tele G; tele(sig, &G);
  Raw *t = G.res, *Bt, *L, *R;
  /* Path B L R, or PathP (<_> B) L R with B not depending on the dimension */
  if (t->k != R_APP || t->a->k != R_APP || t->a->a->k != R_APP || t->a->a->a->k != R_ID)
    die("%s: agent %s: the signature does not end in a path type", a->where, a->name);
  const char *hd = t->a->a->a->name; Bt = t->a->a->b; L = t->a->b; R = t->b;
  if (!strcmp(hd, "PathP")) {
    if (Bt->k != R_LAM || rawMentions(Bt->a, Bt->name)) die("%s: agent %s: the path type depends on its dimension", a->where, a->name);
    Bt = Bt->a;
  } else if (strcmp(hd, "Path")) die("%s: agent %s: the signature does not end in a path type", a->where, a->name);
  Scope *g = NULL;
  for (int i = 0; i < G.n; i++) { Scope *s = xalloc(sizeof *s); s->x = G.x[i]; s->up = g; g = s; }
  Raw *pg = rid(a->name); for (int i = 0; i < G.n; i++) pg = rapp(pg, rid(G.x[i]));
  char nm[256]; int np = G.n + 1;
  RPat **ps;
  for (int side = 0; side < 2; side++) {
    Raw *X = side ? R : L; const char *S = side ? "R" : "L";
    ps = varPats(&G, "y"); snprintf(nm, sizeof nm, "%s-real%s", a->name, S);
    addClause(nm, np, ps, agReal(X, Bt, rid("y"), g), a->where);
    ps = varPats(&G, "u"); snprintf(nm, sizeof nm, "%s-c%s", a->name, S);
    addClause(nm, np + 1, ps, agC(X, Bt, rid("y"), rid("u"), g), a->where);
    ps = varPats(&G, "q"); snprintf(nm, sizeof nm, "%s-c%sinv", a->name, S);
    addClause(nm, np + 1, ps, agCinv(X, Bt, rid("y"), rid("q"), g), a->where);
  }
  char cL[256], cR[256], cLi[256], cRi[256];
  snprintf(cL, sizeof cL, "%s-cL", a->name); snprintf(cR, sizeof cR, "%s-cR", a->name);
  snprintf(cLi, sizeof cLi, "%s-cLinv", a->name); snprintf(cRi, sizeof cRi, "%s-cRinv", a->name);
  /* F_p(u) = c_R^-1 (compose (reverse (p g)) (c_L u)),  F_p^-1(v) = c_L^-1 (compose (p g) (c_R v)) */
  ps = varPats(&G, "u"); snprintf(nm, sizeof nm, "%s-forward", a->name);
  addClause(nm, np + 1, ps,
    callG(&G, cRi, rapp(rapp2(rid("compose"), Bt, rapp(rid("reverse"), pg)), callG(&G, cL, rid("u")))), a->where);
  ps = varPats(&G, "v"); snprintf(nm, sizeof nm, "%s-backward", a->name);
  addClause(nm, np + 1, ps,
    callG(&G, cLi, rapp(rapp2(rid("compose"), Bt, pg), callG(&G, cR, rid("v")))), a->where);
}

/* ------------------------------------------------------------------------
 * Files
 * ---------------------------------------------------------------------- */
static RPat *pPat(Toks *T) {
  RPat *p = xalloc(sizeof *p);
  if (is(T, "(")) {
    next(T); p->name = xdup(next(T));
    RPat *sub[32]; int n = 0;
    while (!is(T, ")")) { if (n == 32) die("%s: pattern too wide", T->where); sub[n++] = pPat(T); }
    next(T);
    p->n = n; p->sub = xalloc(sizeof(RPat *) * (n + 1)); memcpy(p->sub, sub, sizeof(RPat *) * n);
    return p;
  }
  const char *t = next(T);
  if (!isIdent(t)) die("%s: bad pattern '%s'", T->where, t);
  p->name = xdup(t);
  return p;
}
static void decl(const char *text, const char *where) {
  Toks T; memset(&T, 0, sizeof T); T.where = where; lex(&T, text);
  if (!T.n) return;
  if (is(&T, "data")) {
    next(&T); next(&T); expect(&T, "=");
    for (;;) {
      char *c = xdup(next(&T)); int n = 0;
      while (T.pos < T.n && !is(&T, "|")) { next(&T); n++; }
      if (findCon(c) >= 0) die("%s: constructor %s declared twice", where, c);
      ConSym s = { c, newTag(c, C_CON, n) }; PUSH(cons, ncons, capcons, s);
      if (T.pos >= T.n) break;
      next(&T);
    }
    return;
  }
  if (is(&T, "postulate")) {
    next(&T); char *x = xdup(next(&T)); expect(&T, ":");
    Post p = { x, pTerm(&T), 0 };
    if (T.pos < T.n) die("%s: trailing '%s'", where, peek(&T, 0));
    PUSH(posts, nposts, capposts, p); return;
  }
  if (is(&T, "agent")) { next(&T); AgentReq a = { xdup(next(&T)), where }; PUSH(agents, nagents, capagents, a); return; }
  if (is(&T, "eval")) {
    next(&T); EvalReq e = { pTerm(&T), where };
    if (T.pos < T.n) die("%s: trailing '%s'", where, peek(&T, 0));
    PUSH(evals, nevals, capevals, e); return;
  }
  char *x = xdup(next(&T));
  if (is(&T, ":")) { next(&T); Sig s = { x, pTerm(&T) }; PUSH(sigs, nsigs, capsigs, s); return; }
  RPat *ps[32]; int n = 0;
  while (!is(&T, "=")) { if (n == 32) die("%s: too many patterns", where); ps[n++] = pPat(&T); }
  next(&T);
  Raw *rhs = pTerm(&T);
  if (T.pos < T.n) die("%s: trailing '%s'", where, peek(&T, 0));
  RPat **pp = xalloc(sizeof(RPat *) * (n + 1)); memcpy(pp, ps, sizeof(RPat *) * n);
  addClause(x, n, pp, rhs, where);
}
static void loadFile(const char *fn) {
  FILE *f = fopen(fn, "rb"); if (!f) die("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  char *buf = xalloc(sz + 1); if (fread(buf, 1, sz, f) != (size_t)sz) die("cannot read %s", fn); fclose(f);
  Str cur = { 0 }; int startLine = 0, line = 0;
  char *s = buf;
  for (;;) {
    char *e = strchr(s, '\n'); int last = !e; if (e) *e = 0;
    line++;
    int blank = 1; for (char *c = s; *c; c++) if (!isspace((unsigned char)*c)) { blank = 0; break; }
    int comment = s[0] == '-' && s[1] == '-';
    if (!blank && !comment && !isspace((unsigned char)s[0])) {
      if (cur.n) { char w[512]; snprintf(w, sizeof w, "%s:%d", fn, startLine); decl(cur.s, xdup(w)); cur.n = 0; cur.s[0] = 0; }
      startLine = line;
    }
    if (!blank && !comment) sput(&cur, "%s\n", s);
    if (last) break;
    s = e + 1;
  }
  if (cur.n) { char w[512]; snprintf(w, sizeof w, "%s:%d", fn, startLine); decl(cur.s, xdup(w)); }
}

static int needCon(const char *n) { int k = findCon(n); if (k < 0) die("core: constructor %s is missing", n); return k; }
static int needDef(const char *n) { int k = findDef(n); if (k < 0) die("core: definition %s is missing", n); return k; }

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: hcm core.ctt file.ctt ...\n"); return 2; }
  T_LAM = newTag("LAM", C_LAM, 2); T_LAMD = newTag("LAMd", C_LAM, 2); tags[T_LAMD].dim = 1;
  T_SUP = newTag("SUP", C_SUP, 2);
  T_ATOM = newTag("ATOM", C_ATOM, 0); T_NAME = newTag("NAME", C_NAME, 0);
  T_APP = newTag("APP", C_APP, 2); T_CMP1 = newTag("CMP1", C_CMP1, 2); T_CMP2 = newTag("CMP2", C_CMP2, 1);
  T_REIDX = newTag("REIDX", C_REIDX, 3); T_DUP = newTag("DUP", C_DUP, 2); T_ERA = newTag("ERA", C_ERA, 0);
  T_EVAL = newTag("EVAL", C_EVAL, 1); T_ROOT = newTag("ROOT", C_ROOT, 0);
  for (int i = 1; i < argc; i++) loadFile(argv[i]);
  K_lt = needCon("lt"); K_eq = needCon("eq"); K_gt = needCon("gt");
  K_inil = needCon("inil"); K_icons = needCon("icons"); K_fnil = needCon("fnil"); K_fcons = needCon("fcons");
  K_sys = needCon("sys"); K_nosys = needCon("nosys"); K_cnil = needCon("cnil"); K_ccons = needCon("ccons");
  K_pos = needCon("pos"); K_at0 = needCon("at0"); K_at1 = needCon("at1");
  D_isubst = needDef("isubst"); D_fsubst = needDef("fsubst"); D_reflect = needDef("reflect");
  for (int i = 0; i < nposts; i++) posts[i].label = ++labelCtr;
  for (int i = 0; i < nagents; i++) genAgent(&agents[i]);
  for (int i = 0; i < ndefs; i++) elabDef(&defs[i]);
  for (int i = 0; i < nevals; i++) {
    E *t = elab(evals[i].t, NULL, evals[i].where);
    int root = alloc(T_ROOT, 0), hold = alloc(T_EVAL, 0);
    link(pr(hold, 1), pr(root, 0));
    Desc d; memset(&d, 0, sizeof d); d.la = 1; B = &d;
    emitWith(t, EL(0));
    verify(&d, "eval");
    B = NULL;
    instantiate(&d, hold, -1);
    long before = steps;
    out.n = 0; if (out.s) out.s[0] = 0;
    readback(pr(root, 0));
    printf("%s\n  = %s\n  [%ld interactions]\n", evals[i].where, out.s ? out.s : "", steps - before);
  }
  return 0;
}

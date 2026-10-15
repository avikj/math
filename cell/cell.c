/* cell/cell.c -- the cubical machine on instantiated cell references.
 *
 * Scope: the owner's scope subsystem, as specified (sections 1-33 of the
 * scope document, recorded in cell/SCOPE.md):
 *   - a cell origin is an immutable construction record; a reference is
 *     VAR(x) or VIEW(origin, substitution restricted to the origin's
 *     dependencies), interned;
 *   - substitution acts on references (reindex), never on bodies;
 *   - interval and face forms are normalized DNF;
 *   - a binder is instantiated from its owner reference and slot;
 *   - opening a reference exposes one constructor with reindexed fields.
 * Evaluation: interactions of operation agents with data agents; one
 * entry per (reference, ambient face projected to the reference's
 * dimension support), RUNNING with its waiters, READY (the owner's cache
 * rule).  Length is the number of interactions.
 * Reduction: the CCHM rules -- application, projections, path application
 * with endpoints first, Glue/glue/unglue at an entailed face, systems by
 * coverage, comp: coverage first, else the family's head at the fresh
 * instantiated dimension shared with the tube, then the Pi, Sigma, PathP,
 * Glue or U clause, its result built as cells from the component
 * references (reindexed, never re-read from the line).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>

static void die(const char *fmt, ...) {
  va_list ap; va_start(ap, fmt);
  fprintf(stderr, "cell: "); vfprintf(stderr, fmt, ap); fprintf(stderr, "\n");
  va_end(ap); exit(1);
}
static void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xgrow(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static char *xdup(const char *s) { char *d = xalloc(strlen(s) + 1); strcpy(d, s); return d; }
#define PUSH(arr, n, cap, v) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 8; \
    (arr) = xgrow((arr), sizeof(*(arr)) * (cap)); } (arr)[(n)++] = (v); } while (0)

/* ------------------------------------------------------------------------
 * Integer vectors and interning (section 1: interning compares the whole
 * record after a hash match)
 * ---------------------------------------------------------------------- */
typedef struct { int *a; int n, cap; } IV;
static void ivp(IV *v, int x) { PUSH(v->a, v->n, v->cap, x); }
static IV ivcopy(const IV *v) { IV r = { 0 }; for (int i = 0; i < v->n; i++) ivp(&r, v->a[i]); return r; }
static int ivhas(const IV *v, int x) { for (int i = 0; i < v->n; i++) if (v->a[i] == x) return 1; return 0; }
static void ivadd(IV *v, int x) { if (!ivhas(v, x)) ivp(v, x); }
static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return x < y ? -1 : x > y; }
static void ivsortu(IV *v) {
  qsort(v->a, v->n, sizeof(int), cmpint);
  int o = 0; for (int i = 0; i < v->n; i++) if (!o || v->a[o - 1] != v->a[i]) v->a[o++] = v->a[i];
  v->n = o;
}

typedef struct { IV *items; int n, cap; int *h; int hcap; } Tab;
static unsigned hashv(const int *v, int n) { unsigned h = 2166136261u; for (int i = 0; i < n; i++) { h ^= (unsigned)v[i]; h *= 16777619u; } return h ^ (unsigned)n; }
static int tabIntern(Tab *t, const int *v, int n) {
  if (t->n * 2 >= t->hcap) {
    int nc = t->hcap ? t->hcap * 2 : 1024; int *nh = xalloc(sizeof(int) * nc);
    for (int i = 0; i < nc; i++) nh[i] = -1;
    for (int i = 0; i < t->n; i++) { unsigned k = hashv(t->items[i].a, t->items[i].n) % nc; while (nh[k] >= 0) k = (k + 1) % nc; nh[k] = i; }
    free(t->h); t->h = nh; t->hcap = nc;
  }
  unsigned k = hashv(v, n) % t->hcap;
  while (t->h[k] >= 0) {
    IV *e = &t->items[t->h[k]];
    if (e->n == n && !memcmp(e->a, v, sizeof(int) * n)) return t->h[k];
    k = (k + 1) % t->hcap;
  }
  IV c = { 0 }; for (int i = 0; i < n; i++) ivp(&c, v[i]);
  PUSH(t->items, t->n, t->cap, c);
  t->h[k] = t->n - 1;
  return t->n - 1;
}

/* ------------------------------------------------------------------------
 * Variables (section 1): unique identities; names only for printing.
 * ---------------------------------------------------------------------- */
enum { S_TERM, S_DIM };
typedef struct { int sort; char *name; int type, plain; } Var;   /* type: a reference, term variables only; plain: printed without its identity */
static Var *vars; static int nvars, capvars;
static int newVar(int sort, const char *name, int type) { Var v = { sort, xdup(name), type, 0 }; PUSH(vars, nvars, capvars, v); return nvars - 1; }

/* ------------------------------------------------------------------------
 * Interval forms (section 7): antichain of clauses of signed dimensions.
 * A signed dimension is 2*i (positive) or 2*i+1 (negative).
 * Face forms (section 8): antichain of clauses of endpoint literals,
 * 2*i (i = 0) or 2*i+1 (i = 1); a clause with both literals is dropped.
 * Encoded for interning as [nclauses, len, lits.., len, lits..].
 * ---------------------------------------------------------------------- */
typedef struct { IV *c; int n, cap; } Form;
static Tab itab, ftab;
static void formAdd(Form *f, IV c) { PUSH(f->c, f->n, f->cap, c); }
static void formFree(Form *f) { for (int i = 0; i < f->n; i++) free(f->c[i].a); free(f->c); f->c = NULL; f->n = f->cap = 0; }
static int subsetv(const IV *a, const IV *b) {     /* both sorted */
  int j = 0; for (int i = 0; i < a->n; i++) { while (j < b->n && b->a[j] < a->a[i]) j++; if (j == b->n || b->a[j] != a->a[i]) return 0; j++; } return 1;
}
static int clauseCmp(const void *x, const void *y) {
  const IV *a = x, *b = y;
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (int i = 0; i < a->n; i++) if (a->a[i] != b->a[i]) return a->a[i] < b->a[i] ? -1 : 1;
  return 0;
}
static int formIntern(Form *f, int face) {
  for (int i = 0; i < f->n; i++) ivsortu(&f->c[i]);
  Form g = { 0 };
  for (int i = 0; i < f->n; i++) {
    IV *c = &f->c[i];
    if (face) { int bad = 0; for (int k = 0; k + 1 < c->n; k++) if ((c->a[k] >> 1) == (c->a[k + 1] >> 1)) bad = 1; if (bad) continue; }
    int drop = 0;
    for (int j = 0; j < f->n && !drop; j++) {
      if (j == i) continue;
      IV *d = &f->c[j];
      if (face) { int bad = 0; for (int k = 0; k + 1 < d->n; k++) if ((d->a[k] >> 1) == (d->a[k + 1] >> 1)) bad = 1; if (bad) continue; }
      if (subsetv(d, c) && (d->n < c->n || j < i)) drop = 1;   /* strictly contains another, or duplicate */
    }
    if (!drop) formAdd(&g, ivcopy(c));
  }
  qsort(g.c, g.n, sizeof(IV), clauseCmp);
  IV enc = { 0 }; ivp(&enc, g.n);
  for (int i = 0; i < g.n; i++) { ivp(&enc, g.c[i].n); for (int k = 0; k < g.c[i].n; k++) ivp(&enc, g.c[i].a[k]); }
  int id = tabIntern(face ? &ftab : &itab, enc.a, enc.n);
  free(enc.a); formFree(&g); formFree(f);
  return id;
}
static Form formGet(int id, int face) {
  IV *e = &(face ? &ftab : &itab)->items[id];
  Form f = { 0 }; int p = 1;
  for (int i = 0; i < e->a[0]; i++) { IV c = { 0 }; int len = e->a[p++]; for (int k = 0; k < len; k++) ivp(&c, e->a[p++]); formAdd(&f, c); }
  return f;
}
static int I0, I1, F0, F1;
static int formConst(int one, int face) { Form f = { 0 }; if (one) formAdd(&f, (IV){ 0 }); return formIntern(&f, face); }
static int ivar(int i) { Form f = { 0 }; IV c = { 0 }; ivp(&c, 2 * i); formAdd(&f, c); return formIntern(&f, 0); }
static int ijoin(int a, int b) {
  Form f = { 0 }, x = formGet(a, 0), y = formGet(b, 0);
  for (int i = 0; i < x.n; i++) formAdd(&f, ivcopy(&x.c[i]));
  for (int i = 0; i < y.n; i++) formAdd(&f, ivcopy(&y.c[i]));
  formFree(&x); formFree(&y); return formIntern(&f, 0);
}
static int imeet(int a, int b) {
  Form f = { 0 }, x = formGet(a, 0), y = formGet(b, 0);
  for (int i = 0; i < x.n; i++) for (int j = 0; j < y.n; j++) {
    IV c = ivcopy(&x.c[i]); for (int k = 0; k < y.c[j].n; k++) ivp(&c, y.c[j].a[k]); formAdd(&f, c);
  }
  formFree(&x); formFree(&y); return formIntern(&f, 0);
}
static int ineg(int a) {
  Form x = formGet(a, 0); int r = I1;
  for (int i = 0; i < x.n; i++) {
    int nc = I0;
    for (int k = 0; k < x.c[i].n; k++) {
      Form s = { 0 }; IV c = { 0 }; ivp(&c, x.c[i].a[k] ^ 1); formAdd(&s, c);
      nc = ijoin(nc, formIntern(&s, 0));
    }
    r = imeet(r, nc);
  }
  formFree(&x); return r;
}
static int fand(int a, int b) {
  Form f = { 0 }, x = formGet(a, 1), y = formGet(b, 1);
  for (int i = 0; i < x.n; i++) for (int j = 0; j < y.n; j++) {
    IV c = ivcopy(&x.c[i]); for (int k = 0; k < y.c[j].n; k++) ivp(&c, y.c[j].a[k]); formAdd(&f, c);
  }
  formFree(&x); formFree(&y); return formIntern(&f, 1);
}
static int forr(int a, int b) {
  Form f = { 0 }, x = formGet(a, 1), y = formGet(b, 1);
  for (int i = 0; i < x.n; i++) formAdd(&f, ivcopy(&x.c[i]));
  for (int i = 0; i < y.n; i++) formAdd(&f, ivcopy(&y.c[i]));
  formFree(&x); formFree(&y); return formIntern(&f, 1);
}
static int flit(int i, int eps) { Form f = { 0 }; IV c = { 0 }; ivp(&c, 2 * i + eps); formAdd(&f, c); return formIntern(&f, 1); }
/* (r = eps): (r=1) = OR_C AND_{a in C} (a=1); (r=0) = AND_C OR_{a in C} (a=0);
 * (~i = eps) = (i = 1 - eps). */
static int endpoint(int r, int eps) {
  Form x = formGet(r, 0); int res;
  if (eps == 1) {
    res = F0;
    for (int i = 0; i < x.n; i++) {
      int c = F1;
      for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; c = fand(c, flit(a >> 1, (a & 1) ? 0 : 1)); }
      res = forr(res, c);
    }
  } else {
    res = F1;
    for (int i = 0; i < x.n; i++) {
      int c = F0;
      for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; c = forr(c, flit(a >> 1, (a & 1) ? 1 : 0)); }
      res = fand(res, c);
    }
  }
  formFree(&x); return res;
}
/* chi => phi iff every clause of chi contains a clause of phi */
static int entails(int chi, int phi) {
  Form x = formGet(chi, 1), y = formGet(phi, 1); int ok = 1;
  for (int i = 0; i < x.n && ok; i++) { int f = 0; for (int j = 0; j < y.n && !f; j++) if (subsetv(&y.c[j], &x.c[i])) f = 1; if (!f) ok = 0; }
  formFree(&x); formFree(&y); return ok;
}
static int forallDim(int i, int phi) {
  Form x = formGet(phi, 1), r = { 0 };
  for (int k = 0; k < x.n; k++) { int m = 0; for (int l = 0; l < x.c[k].n; l++) if ((x.c[k].a[l] >> 1) == i) m = 1; if (!m) formAdd(&r, ivcopy(&x.c[k])); }
  formFree(&x); return formIntern(&r, 1);
}
/* pi_S(chi): drop literals outside S from each clause, renormalize */
static int projectFace(int chi, const IV *S) {
  Form x = formGet(chi, 1), r = { 0 };
  for (int k = 0; k < x.n; k++) { IV c = { 0 }; for (int l = 0; l < x.c[k].n; l++) if (ivhas(S, x.c[k].a[l] >> 1)) ivp(&c, x.c[k].a[l]); formAdd(&r, c); }
  formFree(&x); return formIntern(&r, 1);
}
static void formDims(int id, int face, IV *out) {
  Form x = formGet(id, face);
  for (int k = 0; k < x.n; k++) for (int l = 0; l < x.c[k].n; l++) ivadd(out, x.c[k].a[l] >> 1);
  formFree(&x);
}

/* ------------------------------------------------------------------------
 * Raw maps (section 2), references (sections 1, 4)
 * Map encoding: [nt, x, ref, .., nd, i, interval, ..], keys sorted; no
 * identity entries.
 * ---------------------------------------------------------------------- */
static Tab mtab, rtab;
static int MID;                                     /* the identity map */
typedef struct { int k, v; } KV;
static int kvcmp(const void *a, const void *b) { return cmpint(&((const KV *)a)->k, &((const KV *)b)->k); }
static int refVar(int x);
static int mapMake(KV *t, int nt, KV *d, int nd) {
  qsort(t, nt, sizeof(KV), kvcmp); qsort(d, nd, sizeof(KV), kvcmp);
  IV e = { 0 }; int c = 0;
  for (int i = 0; i < nt; i++) if (t[i].v != refVar(t[i].k)) c++;
  ivp(&e, c);
  for (int i = 0; i < nt; i++) if (t[i].v != refVar(t[i].k)) { ivp(&e, t[i].k); ivp(&e, t[i].v); }
  c = 0; for (int i = 0; i < nd; i++) if (d[i].v != ivar(d[i].k)) c++;
  ivp(&e, c);
  for (int i = 0; i < nd; i++) if (d[i].v != ivar(d[i].k)) { ivp(&e, d[i].k); ivp(&e, d[i].v); }
  int id = tabIntern(&mtab, e.a, e.n); free(e.a); return id;
}
static void mapRead(int m, KV **t, int *nt, KV **d, int *nd) {
  IV *e = &mtab.items[m]; int p = 0;
  *nt = e->a[p++]; *t = xalloc(sizeof(KV) * (*nt + 1));
  for (int i = 0; i < *nt; i++) { (*t)[i].k = e->a[p++]; (*t)[i].v = e->a[p++]; }
  *nd = e->a[p++]; *d = xalloc(sizeof(KV) * (*nd + 1));
  for (int i = 0; i < *nd; i++) { (*d)[i].k = e->a[p++]; (*d)[i].v = e->a[p++]; }
}
static int termImage(int m, int x) {
  IV *e = &mtab.items[m]; int nt = e->a[0];
  for (int i = 0; i < nt; i++) if (e->a[1 + 2 * i] == x) return e->a[2 + 2 * i];
  return refVar(x);
}
static int dimImage(int m, int i) {
  IV *e = &mtab.items[m]; int nt = e->a[0], p = 1 + 2 * nt, nd = e->a[p++];
  for (int k = 0; k < nd; k++) if (e->a[p + 2 * k] == i) return e->a[p + 2 * k + 1];
  return ivar(i);
}
static int map1Dim(int i, int r) { KV d = { i, r }; return mapMake(NULL, 0, &d, 1); }
static int map1Term(int x, int t) { KV k = { x, t }; return mapMake(&k, 1, NULL, 0); }

/* ------------------------------------------------------------------------
 * Origins (section 3) and the constructor signature (section 16)
 * ---------------------------------------------------------------------- */
enum { UNIV, PI, SIGMA, LAM, APP, PAIR, FST, SND, PATH, PLAM, PAPP, GLUE_TYPE, GLUE_INTRO, UNGLUE, COMP, SYSTEM, GLOBAL, NTAG };
static const char *tagName[NTAG] = { "U", "Pi", "Sigma", "lam", "app", "pair", "fst", "snd", "PathP", "plam", "papp", "Glue", "glue", "unglue", "comp", "system", "global" };
enum { K_TERM, K_INTERVAL, K_FACE, K_TERM_BODY, K_DIM_BODY, K_PARTIAL, K_PARTIAL_DIM_BODY };
typedef struct { int kind, val, slot, guard; } Field;
typedef struct { int sort, formal, domain; } Binder;
typedef struct { int tag, scal, nb, nf; Binder *b; Field *f; IV fvt, fvd; } Origin;
static Origin *origins; static int norigins, caporigins;
static Tab otab;

/* free term variables and dimensions of a reference (memoized) */
typedef struct { int done; IV t, d; } FV;
static FV *fvs; static int capfvs;
static FV *fvOf(int ref);
static void addRefFV(int ref, IV *t, IV *d) { FV *f = fvOf(ref); for (int i = 0; i < f->t.n; i++) ivadd(t, f->t.a[i]); for (int i = 0; i < f->d.n; i++) ivadd(d, f->d.a[i]); }

static int makeView(int o, int m);
/* Create (or find) an origin.  For GLOBAL, params gives its declared
 * boundary (term and dimension parameters). */
static int mkOrigin(int tag, int scal, int nb, Binder *b, int nf, Field *f, IV *gT, IV *gD) {
  IV e = { 0 };
  ivp(&e, tag); ivp(&e, scal); ivp(&e, nb);
  for (int i = 0; i < nb; i++) { ivp(&e, b[i].sort); ivp(&e, b[i].formal); ivp(&e, b[i].domain); }
  ivp(&e, nf);
  for (int i = 0; i < nf; i++) { ivp(&e, f[i].kind); ivp(&e, f[i].val); ivp(&e, f[i].slot); ivp(&e, f[i].guard); }
  int before = otab.n, id = tabIntern(&otab, e.a, e.n);
  free(e.a);
  if (id < before) return id;
  Origin o; memset(&o, 0, sizeof o);
  o.tag = tag; o.scal = scal; o.nb = nb; o.nf = nf;
  o.b = xalloc(sizeof(Binder) * (nb + 1)); memcpy(o.b, b, sizeof(Binder) * nb);
  o.f = xalloc(sizeof(Field) * (nf + 1)); memcpy(o.f, f, sizeof(Field) * nf);
  if (tag == GLOBAL) { o.fvt = ivcopy(gT); o.fvd = ivcopy(gD); }
  else {
    for (int i = 0; i < nf; i++) {
      Field *g = &f[i]; IV t = { 0 }, d = { 0 };
      switch (g->kind) {
      case K_TERM: addRefFV(g->val, &t, &d); break;
      case K_INTERVAL: formDims(g->val, 0, &d); break;
      case K_FACE: formDims(g->val, 1, &d); break;
      case K_PARTIAL: addRefFV(g->val, &t, &d); formDims(g->guard, 1, &d); break;
      case K_TERM_BODY: case K_DIM_BODY: case K_PARTIAL_DIM_BODY: {
        Binder *bb = &b[g->slot];
        addRefFV(g->val, &t, &d);
        if (g->kind == K_PARTIAL_DIM_BODY) formDims(g->guard, 1, &d);
        IV t2 = { 0 }, d2 = { 0 };
        for (int k = 0; k < t.n; k++) if (!(bb->sort == S_TERM && t.a[k] == bb->formal)) ivp(&t2, t.a[k]);
        for (int k = 0; k < d.n; k++) if (!(bb->sort == S_DIM && d.a[k] == bb->formal)) ivp(&d2, d.a[k]);
        free(t.a); free(d.a); t = t2; d = d2;
        if (bb->sort == S_TERM && bb->domain >= 0) addRefFV(bb->domain, &t, &d);
        break;
      }
      }
      for (int k = 0; k < t.n; k++) ivadd(&o.fvt, t.a[k]);
      for (int k = 0; k < d.n; k++) ivadd(&o.fvd, d.a[k]);
      free(t.a); free(d.a);
    }
    /* dependencies required by the types of free term variables */
    for (int k = 0; k < o.fvt.n; k++) { int ty = vars[o.fvt.a[k]].type; if (ty >= 0) addRefFV(ty, &o.fvt, &o.fvd); }
  }
  ivsortu(&o.fvt); ivsortu(&o.fvd);
  if (id != norigins) die("internal: origin table out of step");
  PUSH(origins, norigins, caporigins, o);
  return id;
}

/* references: [0, x] or [1, origin, map] */
static int refVar(int x) { int v[2] = { 0, x }; return tabIntern(&rtab, v, 2); }
static int isVar(int r) { return rtab.items[r].a[0] == 0; }
static int refVarId(int r) { return rtab.items[r].a[1]; }
static int refOrigin(int r) { return rtab.items[r].a[1]; }
static int refMap(int r) { return rtab.items[r].a[2]; }
/* section 4: restrict to the origin's dependencies, drop identities, intern */
static int makeView(int o, int m) {
  KV *t, *d; int nt, nd; mapRead(m, &t, &nt, &d, &nd);
  int ot = 0, od = 0;
  for (int i = 0; i < nt; i++) if (ivhas(&origins[o].fvt, t[i].k)) t[ot++] = t[i];
  for (int i = 0; i < nd; i++) if (ivhas(&origins[o].fvd, d[i].k)) d[od++] = d[i];
  int mm = mapMake(t, ot, d, od); free(t); free(d);
  int v[3] = { 1, o, mm }; return tabIntern(&rtab, v, 3);
}
static FV *fvOf(int ref) {
  if (ref >= capfvs) { int nc = ref * 2 + 64; fvs = xgrow(fvs, sizeof(FV) * nc); memset(fvs + capfvs, 0, sizeof(FV) * (nc - capfvs)); capfvs = nc; }
  if (fvs[ref].done) return &fvs[ref];
  IV t = { 0 }, d = { 0 };
  if (isVar(ref)) {
    int x = refVarId(ref);
    if (vars[x].sort != S_TERM) die("internal: a dimension used as a term");
    ivp(&t, x);
    if (vars[x].type >= 0) addRefFV(vars[x].type, &t, &d);
  } else {
    Origin *o = &origins[refOrigin(ref)]; int m = refMap(ref);
    for (int k = 0; k < o->fvt.n; k++) addRefFV(termImage(m, o->fvt.a[k]), &t, &d);
    for (int k = 0; k < o->fvd.n; k++) formDims(dimImage(m, o->fvd.a[k]), 0, &d);
  }
  ivsortu(&t); ivsortu(&d);
  if (ref >= capfvs) die("internal");
  fvs = fvs; fvs[ref].t = t; fvs[ref].d = d; fvs[ref].done = 1;
  return &fvs[ref];
}

/* ------------------------------------------------------------------------
 * Substitution (sections 5, 7, 8): one lookup per variable.
 * ---------------------------------------------------------------------- */
static int substInterval(int r, int m) {
  Form x = formGet(r, 0); int res = I0;
  for (int i = 0; i < x.n; i++) {
    int c = I1;
    for (int k = 0; k < x.c[i].n; k++) {
      int a = x.c[i].a[k], img = dimImage(m, a >> 1);
      if (a & 1) img = ineg(img);
      c = imeet(c, img);
    }
    res = ijoin(res, c);
  }
  formFree(&x); return res;
}
static int substFace(int phi, int m) {
  Form x = formGet(phi, 1); int res = F0;
  for (int i = 0; i < x.n; i++) {
    int c = F1;
    for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; c = fand(c, endpoint(dimImage(m, a >> 1), a & 1)); }
    res = forr(res, c);
  }
  formFree(&x); return res;
}
typedef struct { int a, b, r; } Memo;
static Memo *rmemo; static int caprmemo, nrmemo;
static int reindex(int ref, int m) {
  if (m == MID) return ref;
  if (isVar(ref)) return termImage(m, refVarId(ref));
  if (nrmemo * 2 >= caprmemo) {
    Memo *old = rmemo; int oc = caprmemo; caprmemo = caprmemo ? caprmemo * 2 : 4096;
    rmemo = xalloc(sizeof(Memo) * caprmemo); for (int i = 0; i < caprmemo; i++) rmemo[i].a = -1;
    for (int i = 0; i < oc; i++) if (old[i].a >= 0) { unsigned k = ((unsigned)old[i].a * 2654435761u ^ (unsigned)old[i].b) % caprmemo; while (rmemo[k].a >= 0) k = (k + 1) % caprmemo; rmemo[k] = old[i]; }
    free(old);
  }
  unsigned k = ((unsigned)ref * 2654435761u ^ (unsigned)m) % caprmemo;
  while (rmemo[k].a >= 0) { if (rmemo[k].a == ref && rmemo[k].b == m) return rmemo[k].r; k = (k + 1) % caprmemo; }
  int o = refOrigin(ref), tau = refMap(ref);
  Origin *O = &origins[o];
  KV *t = xalloc(sizeof(KV) * (O->fvt.n + 1)), *d = xalloc(sizeof(KV) * (O->fvd.n + 1));
  for (int i = 0; i < O->fvt.n; i++) { int x = O->fvt.a[i]; t[i].k = x; t[i].v = reindex(termImage(tau, x), m); O = &origins[o]; }
  for (int i = 0; i < O->fvd.n; i++) { int x = O->fvd.a[i]; d[i].k = x; d[i].v = substInterval(dimImage(tau, x), m); }
  int rho = mapMake(t, origins[o].fvt.n, d, origins[o].fvd.n); free(t); free(d);
  int res = makeView(o, rho);
  /* insert (table may have grown during recursion) */
  k = ((unsigned)ref * 2654435761u ^ (unsigned)m) % caprmemo;
  while (rmemo[k].a >= 0) k = (k + 1) % caprmemo;
  rmemo[k].a = ref; rmemo[k].b = m; rmemo[k].r = res; nrmemo++;
  return res;
}

/* ------------------------------------------------------------------------
 * Binders instantiated from their owner (sections 10-15)
 * ---------------------------------------------------------------------- */
static Tab btab; static int *binstVar; static int capbinst;
/* instantiated_binder(owner, slot, sort) (section 10) */
static int instBinder(int owner, int slot, int sort, const char *name, int type) {
  int v[3] = { owner, slot, sort }; int before = btab.n, id = tabIntern(&btab, v, 3);
  if (id >= capbinst) { int nc = id * 2 + 64; binstVar = xgrow(binstVar, sizeof(int) * nc); capbinst = nc; }
  if (id >= before) binstVar[id] = newVar(sort, name, type);
  return binstVar[id];
}
typedef struct { int var, domain, body, guard; } Resolved;
/* resolve the binder of field fi of the owner (a VIEW) */
static Resolved resolve(int owner, int fi) {
  Origin *O = &origins[refOrigin(owner)]; int sigma = refMap(owner);
  Field fl = O->f[fi]; Binder bd = O->b[fl.slot];
  Resolved r; r.domain = -1; r.guard = -1;
  if (bd.sort == S_TERM) r.domain = reindex(bd.domain, sigma);
  r.var = instBinder(owner, fl.slot, bd.sort, vars[bd.formal].name, r.domain);
  KV *t, *d; int nt, nd; mapRead(sigma, &t, &nt, &d, &nd);
  t = xgrow(t, sizeof(KV) * (nt + 2)); d = xgrow(d, sizeof(KV) * (nd + 2));
  int ot = 0, od = 0;
  for (int i = 0; i < nt; i++) if (!(bd.sort == S_TERM && t[i].k == bd.formal)) t[ot++] = t[i];
  for (int i = 0; i < nd; i++) if (!(bd.sort == S_DIM && d[i].k == bd.formal)) d[od++] = d[i];
  if (bd.sort == S_TERM) { t[ot].k = bd.formal; t[ot].v = refVar(r.var); ot++; }
  else { d[od].k = bd.formal; d[od].v = ivar(r.var); od++; }
  int lifted = mapMake(t, ot, d, od); free(t); free(d);
  r.body = reindex(fl.val, lifted);
  if (fl.kind == K_PARTIAL_DIM_BODY) r.guard = substFace(fl.guard, lifted);
  return r;
}
static int applyTerm(int owner, int fi, int arg) { Resolved r = resolve(owner, fi); return reindex(r.body, map1Term(r.var, arg)); }
static int applyDim(int owner, int fi, int itv) { Resolved r = resolve(owner, fi); return reindex(r.body, map1Dim(r.var, itv)); }

/* open (section 17): one constructor, its immediate fields reindexed */
typedef struct { int kind, ref, itv, face, guard; } OField;
typedef struct { int tag, scal, owner, nf; OField f[8]; int sysN; int *sysFace, *sysTerm; } Head;
static Head openRef(int ref) {
  Head h; memset(&h, 0, sizeof h); h.owner = ref;
  if (isVar(ref)) { h.tag = -1; return h; }
  Origin *O = &origins[refOrigin(ref)]; int s = refMap(ref);
  h.tag = O->tag; h.scal = O->scal; h.nf = O->nf;
  if (O->tag == SYSTEM) {
    h.sysN = O->nf / 2; h.sysFace = xalloc(sizeof(int) * (h.sysN + 1)); h.sysTerm = xalloc(sizeof(int) * (h.sysN + 1));
    for (int k = 0; k < h.sysN; k++) { h.sysFace[k] = substFace(O->f[2 * k].val, s); h.sysTerm[k] = reindex(O->f[2 * k + 1].val, s); O = &origins[refOrigin(ref)]; }
    h.nf = 0; return h;
  }
  if (O->nf > 8) die("internal: too many fields");
  for (int i = 0; i < O->nf; i++) {
    Field fl = origins[refOrigin(ref)].f[i];
    h.f[i].kind = fl.kind;
    switch (fl.kind) {
    case K_TERM: h.f[i].ref = reindex(fl.val, s); break;
    case K_INTERVAL: h.f[i].itv = substInterval(fl.val, s); break;
    case K_FACE: h.f[i].face = substFace(fl.val, s); break;
    case K_PARTIAL: h.f[i].guard = substFace(fl.guard, s); h.f[i].ref = reindex(fl.val, s); break;
    default: break;                                   /* binder fields: resolved on demand */
    }
  }
  return h;
}

/* ------------------------------------------------------------------------
 * Building cells
 * ---------------------------------------------------------------------- */
static Field FT(int r) { Field f = { K_TERM, r, 0, 0 }; return f; }
static Field FI(int i) { Field f = { K_INTERVAL, i, 0, 0 }; return f; }
static Field FF(int i) { Field f = { K_FACE, i, 0, 0 }; return f; }
static Field FP(int r, int g) { Field f = { K_PARTIAL, r, 0, g }; return f; }
static Field FB(int kind, int r, int slot, int g) { Field f = { kind, r, slot, g }; return f; }
static int cell(int tag, int nb, Binder *b, int nf, Field *f) { return makeView(mkOrigin(tag, 0, nb, b, nf, f, NULL, NULL), MID); }
static int bApp(int fn, int a) { Field f[2] = { FT(fn), FT(a) }; return cell(APP, 0, NULL, 2, f); }
static int bFst(int p) { Field f[1] = { FT(p) }; return cell(FST, 0, NULL, 1, f); }
static int bSnd(int p) { Field f[1] = { FT(p) }; return cell(SND, 0, NULL, 1, f); }
static int bPair(int a, int b) { Field f[2] = { FT(a), FT(b) }; return cell(PAIR, 0, NULL, 2, f); }
static int bLam(int x, int A, int body) { Binder b = { S_TERM, x, A }; Field f[2] = { FT(A), FB(K_TERM_BODY, body, 0, 0) }; return cell(LAM, 1, &b, 2, f); }
static int bPlam(int i, int body) { Binder b = { S_DIM, i, -1 }; Field f[1] = { FB(K_DIM_BODY, body, 0, 0) }; return cell(PLAM, 1, &b, 1, f); }
static int bPapp(int i, int B, int l, int r, int p, int s) {
  Binder b = { S_DIM, i, -1 }; Field f[5] = { FB(K_DIM_BODY, B, 0, 0), FT(l), FT(r), FT(p), FI(s) };
  return cell(PAPP, 1, &b, 5, f);
}
static int bComp(int i, int A, int phi, int u, int a0) {
  Binder b = { S_DIM, i, -1 };
  Field f[4] = { FB(K_DIM_BODY, A, 0, 0), FF(phi), FB(K_PARTIAL_DIM_BODY, u, 0, phi), FT(a0) };
  return cell(COMP, 1, &b, 4, f);
}
/* a system of n branches; a single branch on a face equal to its guard is
 * the term itself, as the composition tube field allows */
static int bSys(int n, int *faces, int *terms) {
  Field *f = xalloc(sizeof(Field) * (2 * n + 1)); int k = 0;
  for (int i = 0; i < n; i++) { if (faces[i] == F0) continue; f[k++] = FF(faces[i]); f[k++] = FP(terms[i], faces[i]); }
  int r = cell(SYSTEM, 0, NULL, k, f); free(f); return r;
}
static int bGlueIntro(int A, int phi, int T, int e, int t, int a) {
  Field f[6] = { FT(A), FF(phi), FP(T, phi), FP(e, phi), FP(t, phi), FT(a) }; return cell(GLUE_INTRO, 0, NULL, 6, f);
}
static int bUnglue(int A, int phi, int T, int e, int v) {
  Field f[5] = { FT(A), FF(phi), FP(T, phi), FP(e, phi), FT(v) }; return cell(UNGLUE, 0, NULL, 5, f);
}
static int bGlueType(int A, int phi, int T, int e) {
  Field f[4] = { FT(A), FF(phi), FP(T, phi), FP(e, phi) }; return cell(GLUE_TYPE, 0, NULL, 4, f);
}

/* globals (section 19) */
typedef struct { char *name; IV params; int body, type; int origin; } Def;
static Def *defs; static int ndefs, capdefs;
static int globalView(int d, int *args) {
  int np = defs[d].params.n; KV *t = xalloc(sizeof(KV) * (np + 1)), *dd = xalloc(sizeof(KV) * (np + 1)); int nt = 0, nd = 0;
  for (int i = 0; i < np; i++) {
    int x = defs[d].params.a[i];
    if (vars[x].sort == S_TERM) { t[nt].k = x; t[nt].v = args[i]; nt++; }
    else { dd[nd].k = x; dd[nd].v = args[i]; nd++; }
  }
  int m = mapMake(t, nt, dd, nd); free(t); free(dd);
  return makeView(defs[d].origin, m);
}
static int findDef(const char *n) { for (int i = 0; i < ndefs; i++) if (!strcmp(defs[i].name, n)) return i; return -1; }

/* ------------------------------------------------------------------------
 * Evaluation (the owner's cache rule): one entry per (reference,
 * ambient face projected to the reference's dimension support).
 * ---------------------------------------------------------------------- */
enum { UNEVALUATED, RUNNING, READY };
typedef struct { int ref, face, state, res, neutral; int *wo, *wi, nw, capw; } Entry;
static Entry *etab; static int capetab, netab;
typedef struct { int ref, neutral, empty; } Val;
static Entry *entry(int ref, int face) {
  if (netab * 2 >= capetab) {
    Entry *old = etab; int oc = capetab; capetab = capetab ? capetab * 2 : 4096;
    etab = xalloc(sizeof(Entry) * capetab); for (int i = 0; i < capetab; i++) etab[i].ref = -1;
    for (int i = 0; i < oc; i++) if (old[i].ref >= 0) { unsigned k = ((unsigned)old[i].ref * 2654435761u ^ (unsigned)old[i].face * 40503u) % capetab; while (etab[k].ref >= 0) k = (k + 1) % capetab; etab[k] = old[i]; }
    free(old);
  }
  unsigned k = ((unsigned)ref * 2654435761u ^ (unsigned)face * 40503u) % capetab;
  while (etab[k].ref >= 0) { if (etab[k].ref == ref && etab[k].face == face) return &etab[k]; k = (k + 1) % capetab; }
  etab[k].ref = ref; etab[k].face = face; etab[k].state = UNEVALUATED; netab++;
  return &etab[k];
}
/* ------------------------------------------------------------------------
 * Composition clauses (MACHINE_SPEC sections 10, 11, 12, 17-21).
 * j is the instantiated dimension of the composition, shared by family and
 * tube (section 12 of the scope document).  Components are references with
 * j free; at(X, r) instantiates them by reindexing.
 * ---------------------------------------------------------------------- */
static int CJ, CSLOT, COWNER, CFACE;             /* current comp: its j, a slot counter, its owner, its face */
static int at(int X, int r) { return reindex(X, map1Dim(CJ, r)); }
static int atF(int phi, int r) { return substFace(phi, map1Dim(CJ, r)); }
/* the formal identities of the cells a clause builds: fresh, and the same
 * for the same composition, face and position, so that the same clause
 * builds the same (interned) cells */
static Tab ftabFormal; static int *formalVar; static int capformal;
static int formal(int sort, const char *n, int ty) {
  int v[4] = { COWNER, CFACE, CSLOT++, sort }; int before = ftabFormal.n, id = tabIntern(&ftabFormal, v, 4);
  if (id >= capformal) { int nc = id * 2 + 64; formalVar = xgrow(formalVar, sizeof(int) * nc); capformal = nc; }
  if (id >= before) formalVar[id] = newVar(sort, n, ty);
  return formalVar[id];
}
static int freshDim(const char *n) { return formal(S_DIM, n, -1); }
static int freshTerm(const char *n, int ty) { return formal(S_TERM, n, ty); }
/* fill^d X [phi -> U] a0 (r) = comp^n X(d := r/\n) [phi -> U(d := r/\n), (r=0) -> a0] a0
 * (section 9; X and U have the dimension d free) */
static int fill(int d, int X, int phi, int U, int a0, int r) {
  int n = freshDim("n"), s = imeet(r, ivar(n)), sm = map1Dim(d, s);
  int fam = reindex(X, sm), z = endpoint(r, 0);
  int faces[2], terms[2], k = 0;
  if (phi != F0) { faces[k] = phi; terms[k] = reindex(U, sm); k++; }
  if (z != F0) { faces[k] = z; terms[k] = a0; k++; }
  int guard = forr(phi, z);
  int tube = k == 0 ? a0 : bSys(k, faces, terms);
  return bComp(n, fam, guard, tube, a0);
}
static int DEF_fib = -1, DEF_lineEquiv = -1;

/* c: the composition reference; hv: the head of its family at its j,
 * already evaluated under eta.  Returns the clause's result, or 0 when the
 * head is neutral (the composition is retained). */
static int compClause(int c, int eta, Data hd, int *ok) {
  Head hc = openRef(c), *ch = &hc;
  Resolved fam = resolve(c, 0), tube = resolve(c, 2);
  if (fam.var != tube.var) die("internal: family and tube instantiated apart");
  int j = fam.var, phi = ch->f[1].face, a0 = ch->f[3].ref, uj = tube.body;
  if (hd.empty) return 0;
  struct { int ref; } hv = { hd.a };
  Head hA = openRef(hv.ref);
  int saveJ = CJ, saveS = CSLOT, saveO = COWNER, saveF = CFACE;
  CJ = j; CSLOT = 0; COWNER = c; CFACE = eta;
  int res = -1;
  switch (hA.tag) {
  case PI: {                                         /* section 10 */
    int Dj = hA.f[0].ref; Resolved C = resolve(hv.ref, 1);
    int x1 = freshTerm("x", at(Dj, I1));
    int Dneg = reindex(Dj, map1Dim(j, ineg(ivar(j))));
    int k = freshDim("k");
    int vk = fill(j, Dneg, F0, a0, refVar(x1), ineg(ivar(k)));
    int v0 = fill(j, Dneg, F0, a0, refVar(x1), ineg(I0));
    KV tt = { C.var, vk }, dd = { j, ivar(k) };
    int famk = reindex(C.body, mapMake(&tt, 1, &dd, 1));
    int body = bComp(k, famk, phi, bApp(at(uj, ivar(k)), vk), bApp(a0, v0));
    res = bLam(x1, at(Dj, I1), body);
    break;
  }
  case SIGMA: {                                      /* section 11 */
    int Dj = hA.f[0].ref; Resolved C = resolve(hv.ref, 1);
    int k = freshDim("k");
    int ak = fill(j, Dj, phi, bFst(uj), bFst(a0), ivar(k));
    int a1 = fill(j, Dj, phi, bFst(uj), bFst(a0), I1);
    KV tt = { C.var, ak }, dd = { j, ivar(k) };
    int famk = reindex(C.body, mapMake(&tt, 1, &dd, 1));
    int b1 = bComp(k, famk, phi, bSnd(at(uj, ivar(k))), bSnd(a0));
    res = bPair(a1, b1);
    break;
  }
  case PATH: {                                       /* section 12 */
    Resolved B = resolve(hv.ref, 0);
    int lj = hA.f[1].ref, rj = hA.f[2].ref;
    int m = freshDim("m"), k = freshDim("k");
    KV dk[2] = { { j, ivar(k) }, { B.var, ivar(m) } };
    int famk = reindex(B.body, mapMake(NULL, 0, dk, 2));
    int Bk = at(B.body, ivar(k)), B0 = at(B.body, I0);
    int faces[3] = { phi, endpoint(ivar(m), 0), endpoint(ivar(m), 1) };
    int terms[3] = { bPapp(B.var, Bk, at(lj, ivar(k)), at(rj, ivar(k)), at(uj, ivar(k)), ivar(m)), at(lj, ivar(k)), at(rj, ivar(k)) };
    int guard = forr(phi, forr(faces[1], faces[2]));
    int body = bComp(k, famk, guard, bSys(3, faces, terms), bPapp(B.var, B0, at(lj, I0), at(rj, I0), a0, ivar(m)));
    res = bPlam(m, body);
    break;
  }
  case UNIV: {                                       /* section 21 */
    int m = freshDim("m");
    int u1 = at(uj, I1), u0 = at(uj, I0);
    int args[3] = { u1, u0, bPlam(m, at(uj, ineg(ivar(m)))) };
    if (DEF_lineEquiv < 0) die("core: lineEquiv is not defined");
    int e = globalView(DEF_lineEquiv, args);
    res = bGlueType(a0, phi, u1, e);
    break;
  }
  case GLUE_TYPE: {                                  /* sections 17-20 */
    int Aj = hA.f[0].ref, al = hA.f[1].face, Tj = hA.f[2].ref, ej = hA.f[3].ref;
    int psi = phi, u0 = a0;
    /* a0' = unglue u0, at 0 */
    int ug0 = bUnglue(at(Aj, I0), atF(al, I0), at(Tj, I0), at(ej, I0), u0);
    /* a(r) = fill^j A(j) [psi -> unglue u(j)] a0' (r) */
    int Ugj = bUnglue(Aj, al, Tj, ej, uj);
    int a1 = fill(j, Aj, psi, Ugj, ug0, I1);
    int delta = forallDim(j, al);
    /* t(r) = fill^j T(j) [psi -> u(j)] u0 (r), under delta */
    int t1 = fill(j, Tj, psi, uj, u0, I1);
    /* omega(m) = comp^k A(k) [psi -> a(k), (m=0) -> f_k(t(k)), (m=1) -> a(k)] a0' */
    int m = freshDim("m"), k = freshDim("k");
    int ak = fill(j, Aj, psi, Ugj, ug0, ivar(k));
    int tk = fill(j, Tj, psi, uj, u0, ivar(k));
    int fk = bApp(bFst(at(ej, ivar(k))), tk);
    int of[3] = { psi, endpoint(ivar(m), 0), endpoint(ivar(m), 1) }, ot[3] = { ak, fk, ak };
    int omega = bPlam(m, bComp(k, at(Aj, ivar(k)), forr(psi, forr(of[1], of[2])), bSys(3, of, ot), ug0));
    /* w = [delta -> (t1, omega), psi -> (u 1, refl a1)] */
    int rr = freshDim("r");
    int wf[2] = { delta, psi }, wt[2] = { bPair(t1, omega), bPair(at(uj, I1), bPlam(rr, a1)) };
    int w = bSys(2, wf, wt);
    /* (t1, p) = extendEquiv e(1) a1 (delta \/ psi) w  (section 15) */
    int A1 = at(Aj, I1), al1 = atF(al, I1), T1 = at(Tj, I1), e1 = at(ej, I1);
    int f1 = bFst(e1);
    if (DEF_fib < 0) die("core: fib is not defined");
    int fargs[4] = { T1, A1, f1, a1 };
    int X = globalView(DEF_fib, fargs);
    int contr = bApp(bSnd(e1), a1), cen = bFst(contr), kw = bApp(bSnd(contr), w);
    int theta = forr(delta, psi), n = freshDim("n"), q = freshDim("q");
    int ext = bComp(n, X, theta, bPapp(q, X, cen, w, kw, ivar(n)), cen);
    int tt1 = bFst(ext), p = bSnd(ext);
    /* a1' = hcomp^n_{A(1)} [alpha(1) -> p (~n), psi -> a1] a1 */
    int n2 = freshDim("n"), q2 = freshDim("q");
    int hf[2] = { al1, psi }, ht[2] = { bPapp(q2, A1, bApp(f1, tt1), a1, p, ineg(ivar(n2))), a1 };
    int a1p = bComp(n2, A1, forr(al1, psi), bSys(2, hf, ht), a1);
    res = bGlueIntro(A1, al1, T1, e1, tt1, a1p);
    break;
  }
  default: break;                                    /* neutral family head: composition retained */
  }
  CJ = saveJ; CSLOT = saveS; COWNER = saveO; CFACE = saveF;
  if (res < 0) return 0;
  *ok = 1; return res;
}


/* ------------------------------------------------------------------------
 * Contexts, typed maps and occurrences (scope sections 1, 2, 9)
 * A context: its declarations (variable identities, in order) and its face
 * assumption.  A typed map: source and target contexts and a raw map.  An
 * occurrence: a reference and the context it is used in; the context is
 * not part of the reference's identity.
 * ---------------------------------------------------------------------- */
static Tab ctab, tmtab;
static int ctxMake(const IV *decls, int face) {
  IV e = { 0 }; ivp(&e, face); for (int i = 0; i < decls->n; i++) ivp(&e, decls->a[i]);
  int id = tabIntern(&ctab, e.a, e.n); free(e.a); return id;
}
static int ctxFace(int ctx) { return ctab.items[ctx].a[0]; }
static int ctxRestrict(int ctx, int phi) {               /* the same declarations, a stronger face */
  IV d = { 0 }; IV *e = &ctab.items[ctx];
  for (int i = 1; i < e->n; i++) ivp(&d, e->a[i]);
  int r = ctxMake(&d, fand(e->a[0], phi)); free(d.a); return r;
}
typedef struct { int ref, ctx; } Occurrence;
static Occurrence weakenOccurrence(Occurrence o, int delta) { Occurrence r = { o.ref, delta }; return r; }
static int typedMap(int source, int target, int raw) { int v[3] = { source, target, raw }; return tabIntern(&tmtab, v, 3); }
static int tmSource(int tm) { return tmtab.items[tm].a[0]; }
static int tmTarget(int tm) { return tmtab.items[tm].a[1]; }
static int tmRaw(int tm) { return tmtab.items[tm].a[2]; }
/* sigma|_phi : (Delta, phi[sigma]) -> (Gamma, phi); the raw map unchanged */
static int restrictTypedMap(int tm, int phi) {
  int mapped = substFace(phi, tmRaw(tm));
  return typedMap(ctxRestrict(tmSource(tm), mapped), ctxRestrict(tmTarget(tm), phi), tmRaw(tm));
}
/* sigma ; tau (section 6): apply sigma, then tau */
static int composeMaps(int sigma, int tau) {
  KV *st, *sd, *tt, *td; int nst, nsd, ntt, ntd;
  mapRead(sigma, &st, &nst, &sd, &nsd); mapRead(tau, &tt, &ntt, &td, &ntd);
  IV tk = { 0 }, dk = { 0 };
  for (int i = 0; i < nst; i++) ivadd(&tk, st[i].k);
  for (int i = 0; i < ntt; i++) ivadd(&tk, tt[i].k);
  for (int i = 0; i < nsd; i++) ivadd(&dk, sd[i].k);
  for (int i = 0; i < ntd; i++) ivadd(&dk, td[i].k);
  KV *t = xalloc(sizeof(KV) * (tk.n + 1)), *d = xalloc(sizeof(KV) * (dk.n + 1));
  for (int i = 0; i < tk.n; i++) { t[i].k = tk.a[i]; t[i].v = reindex(termImage(sigma, tk.a[i]), tau); }
  for (int i = 0; i < dk.n; i++) { d[i].k = dk.a[i]; d[i].v = substInterval(dimImage(sigma, dk.a[i]), tau); }
  int r = mapMake(t, tk.n, d, dk.n);
  free(t); free(d); free(st); free(sd); free(tt); free(td); free(tk.a); free(dk.a);
  return r;
}
static int composeTyped(int s1, int s2) {               /* s1 : Delta -> Gamma, s2 : Theta -> Delta */
  if (tmSource(s1) != tmTarget(s2)) die("typed maps do not compose");
  return typedMap(tmSource(s2), tmTarget(s1), composeMaps(tmRaw(s1), tmRaw(s2)));
}
/* binder handles (section 13): reindexing acts on the owner */
typedef struct { int owner, field; } BinderHandle;
static BinderHandle reindexBinder(BinderHandle h, int sigma) { BinderHandle r = { reindex(h.owner, sigma), h.field }; return r; }
/* the lifted map under a binder (sections 11, 12, 23) */
static int liftBinder(int owner, int fi) {
  Origin *O = &origins[refOrigin(owner)]; Field fl = O->f[fi]; Binder bd = O->b[fl.slot]; int sigma = refMap(owner);
  Resolved r = resolve(owner, fi);
  KV *t, *d; int nt, nd; mapRead(sigma, &t, &nt, &d, &nd);
  t = xgrow(t, sizeof(KV) * (nt + 2)); d = xgrow(d, sizeof(KV) * (nd + 2));
  int ot = 0, od = 0;
  for (int i = 0; i < nt; i++) if (!(bd.sort == S_TERM && t[i].k == bd.formal)) t[ot++] = t[i];
  for (int i = 0; i < nd; i++) if (!(bd.sort == S_DIM && d[i].k == bd.formal)) d[od++] = d[i];
  if (bd.sort == S_TERM) { t[ot].k = bd.formal; t[ot].v = refVar(r.var); ot++; } else { d[od].k = bd.formal; d[od].v = ivar(r.var); od++; }
  int m = mapMake(t, ot, d, od); free(t); free(d); return m;
}

/* ------------------------------------------------------------------------
 * Evaluation as interactions.
 *
 * Data agents (scope section 21): REF(t), HEAD_RECIPE(owner), FACE(phi),
 * PARTIAL(phi, t), TERM_BINDER(h), DIM_BINDER(h), PARTIAL_DIM_BINDER(h),
 * and the protocol results COVERED, NOT_COVERED.  A binder handle h is the
 * owner reference with its body field.
 *
 * Operation agents have a principal input and a result output; one meeting
 * a data agent is an active pair, and firing it is one finite payload
 * computation (section 22).  The scope table's own pairs:
 *   OPEN >< REF(t)                          HEAD_RECIPE(open t)
 *   UNFOLD_GLOBAL >< REF(g sigma)           REF(unfold)
 *   APPLY_TERM_BINDER(a) >< TERM_BINDER(h)  REF(apply_term_binder(h, a))
 *   APPLY_DIM_BINDER(r) >< DIM_BINDER(h)    REF(apply_dimension_binder(h, r))
 *   APPLY_PARTIAL_DIM_BINDER(r) >< PARTIAL_DIM_BINDER(h)
 *                                           PARTIAL(apply_partial_dimension_binder(h, r))
 *   FACE_COVERAGE(chi) >< FACE(phi)         COVERED or NOT_COVERED
 *   USE_PARTIAL(chi) >< PARTIAL(phi, t)     REF(t) if chi => phi, else NOT_COVERED
 * The evaluator's own (the owner's cache rule):
 *   EVAL(chi) >< REF(t): the entry (t, pi_S(chi)) -- READY: its result;
 *     RUNNING: this demand joins its waiters; otherwise RUNNING, and t is
 *     opened and inspected, the result going to PUBLISH.  A disjunctive
 *     face sends one EVAL per clause to a JOIN.
 *   PUBLISH >< REF(v): the entry READY; v to the demand and every waiter.
 *   JOIN: one input per clause, in any order (NET_SPEC 6).
 *   INSPECT(eta) >< HEAD_RECIPE: the constructor's rule.
 *   continuations: the eliminator waiting on its scrutinee's head, or on a
 *   coverage answer.
 * The length is the number of interactions.
 * ---------------------------------------------------------------------- */
enum { D_REF, D_HEAD, D_FACE, D_PARTIAL, D_TBIND, D_DBIND, D_PDBIND, D_COVERED, D_NOT_COVERED };
typedef struct { int kind, a, b, neutral, empty; } Data;
enum { OP_ROOT, OP_EVAL, OP_PUBLISH, OP_JOIN, OP_OPEN, OP_INSPECT, OP_UNFOLD, OP_APPLY_TERM, OP_APPLY_DIM, OP_APPLY_PDIM,
       OP_FACE_COVERAGE, OP_USE_PARTIAL,
       OP_KAPP, OP_KFST, OP_KSND, OP_KPEND0, OP_KPEND1, OP_KPAPP, OP_KGLUE, OP_KUNGLUE0, OP_KUNGLUE, OP_KSYS, OP_KCOMP0, OP_KCOMP };
typedef struct { int kind, p[4], outA, outI, n, got; Data *ins; int *faces; Data rootv; int rootset; } Op;
static Op *ops; static int nops, capops;
typedef struct { int op, idx; Data d; } Pair;
static Pair *queue; static int nqueue, capqueue;
static long interactions;
static int newOp(int kind, int outA, int outI, int p0, int p1, int p2, int p3) {
  Op o; memset(&o, 0, sizeof o); o.kind = kind; o.outA = outA; o.outI = outI;
  o.p[0] = p0; o.p[1] = p1; o.p[2] = p2; o.p[3] = p3;
  PUSH(ops, nops, capops, o); return nops - 1;
}
static void deliver(Data d, int op, int idx) {
  if (ops[op].kind == OP_ROOT) { ops[op].rootv = d; ops[op].rootset = 1; return; }
  Pair pr = { op, idx, d }; PUSH(queue, nqueue, capqueue, pr);
}
static Data DR(int ref, int neu) { Data d = { D_REF, ref, 0, neu, 0 }; return d; }
static Data DK(int kind, int a, int b) { Data d = { kind, a, b, 0, 0 }; return d; }
static Data DEMPTY(int ref) { Data d = { D_REF, ref, 0, 0, 1 }; return d; }
/* a data agent sent to a new operation agent */
static void to(Data d, int kind, int oA, int oI, int p0, int p1, int p2, int p3) { deliver(d, newOp(kind, oA, oI, p0, p1, p2, p3), 0); }
static void evalTo(int ref, int eta, int oA, int oI) { to(DR(ref, 0), OP_EVAL, oA, oI, eta, 0, 0, 0); }
/* evaluate, open, then the continuation k (created by the caller) */
static void evalOpenTo(int ref, int eta, int k) { int op = newOp(OP_OPEN, k, 0, 0, 0, 0, 0); evalTo(ref, eta, op, 0); }

/* an elimination of a system that does not cover the context distributes
 * over its branches (section 6); a path application keeps the family and
 * endpoints it carries */
static int distribute(Head *sy, int orig) {
  Head ho = openRef(orig); int *ts = xalloc(sizeof(int) * (sy->sysN + 1));
  for (int k = 0; k < sy->sysN; k++) {
    int t = sy->sysTerm[k];
    switch (ho.tag) {
    case APP: ts[k] = bApp(t, ho.f[1].ref); break;
    case FST: ts[k] = bFst(t); break;
    case SND: ts[k] = bSnd(t); break;
    case PAPP: { Resolved B = resolve(orig, 0); ts[k] = bPapp(B.var, B.body, ho.f[1].ref, ho.f[2].ref, t, ho.f[4].itv); break; }
    case UNGLUE: ts[k] = bUnglue(ho.f[0].ref, ho.f[1].face, ho.f[2].ref, ho.f[3].ref, t); break;
    default: die("internal: distribute");
    }
  }
  int r = bSys(sy->sysN, sy->sysFace, ts); free(ts); return r;
}

static int compClause(int c, int eta, Data hv, int *ok);

static void fire(Pair pr) {
  Op o = ops[pr.op]; Data d = pr.d; int oA = o.outA, oI = o.outI, eta = o.p[0];
  interactions++;
  /* an empty-face result passes through every continuation unopened */
  if (d.kind == D_REF && d.empty && o.kind != OP_JOIN && o.kind != OP_PUBLISH) { deliver(d, oA, oI); return; }
  switch (o.kind) {
  case OP_EVAL: {
    int chi = eta, ref = d.a;
    if (chi == F0) { deliver(DEMPTY(ref), oA, oI); return; }
    int e2 = projectFace(chi, &fvOf(ref)->d);
    Form fx = formGet(e2, 1);
    if (fx.n > 1) {
      int n = fx.n, j = newOp(OP_JOIN, oA, oI, 0, 0, 0, 0);
      ops[j].n = n; ops[j].ins = xalloc(sizeof(Data) * n); ops[j].faces = xalloc(sizeof(int) * n);
      for (int k = 0; k < n; k++) { Form one = { 0 }; formAdd(&one, ivcopy(&fx.c[k])); ops[j].faces[k] = formIntern(&one, 1); }
      formFree(&fx);
      for (int k = 0; k < n; k++) evalTo(ref, ops[j].faces[k], j, k);
      return;
    }
    formFree(&fx);
    Entry *en = entry(ref, e2);
    if (en->state == READY) { deliver(DR(en->res, en->neutral), oA, oI); return; }
    if (en->state == RUNNING) {
      if (en->nw == en->capw) { en->capw = en->capw ? 2 * en->capw : 4; en->wo = xgrow(en->wo, sizeof(int) * en->capw); en->wi = xgrow(en->wi, sizeof(int) * en->capw); }
      en->wo[en->nw] = oA; en->wi[en->nw] = oI; en->nw++;
      return;
    }
    en->state = RUNNING;
    int pub = newOp(OP_PUBLISH, oA, oI, ref, e2, 0, 0);
    int ins = newOp(OP_INSPECT, pub, 0, e2, 0, 0, 0);
    to(DR(ref, 0), OP_OPEN, ins, 0, 0, 0, 0, 0);
    return;
  }
  case OP_PUBLISH: {
    Entry *en = entry(o.p[0], o.p[1]);
    en->state = READY; en->res = d.a; en->neutral = d.neutral;
    int nw = en->nw, *wo = en->wo, *wi = en->wi;
    en->wo = en->wi = NULL; en->nw = en->capw = 0;
    deliver(d, oA, oI);
    for (int k = 0; k < nw; k++) deliver(d, wo[k], wi[k]);
    free(wo); free(wi);
    return;
  }
  case OP_JOIN: {
    Op *j = &ops[pr.op];
    j->ins[pr.idx] = d; j->got++;
    if (j->got < j->n) return;
    int same = 1, neu = 1;
    for (int k = 0; k < j->n; k++) { if (j->ins[k].a != j->ins[0].a) same = 0; neu = neu && j->ins[k].neutral; }
    if (same) { deliver(DR(j->ins[0].a, neu), oA, oI); return; }
    int n = j->n, *rs = xalloc(sizeof(int) * n), *fs = j->faces;
    for (int k = 0; k < n; k++) rs[k] = j->ins[k].a;
    int sy = bSys(n, fs, rs); free(rs);
    deliver(DR(sy, 0), oA, oI);
    return;
  }
  /* --- the scope table's pairs --- */
  case OP_OPEN: deliver(DK(D_HEAD, d.a, 0), oA, oI); return;   /* the recipe is open(t), read by its consumer */
  case OP_UNFOLD: {
    Head h = openRef(d.a); if (h.tag != GLOBAL) die("UNFOLD_GLOBAL meets a non-global reference");
    deliver(DR(reindex(defs[h.scal].body, refMap(d.a)), 0), oA, oI); return;
  }
  case OP_APPLY_TERM: deliver(DR(applyTerm(d.a, d.b, o.p[1]), 0), oA, oI); return;
  case OP_APPLY_DIM: deliver(DR(applyDim(d.a, d.b, o.p[1]), 0), oA, oI); return;
  case OP_APPLY_PDIM: {
    Resolved r = resolve(d.a, d.b); int m = map1Dim(r.var, o.p[1]);
    deliver(DK(D_PARTIAL, substFace(r.guard, m), reindex(r.body, m)), oA, oI); return;
  }
  case OP_FACE_COVERAGE: deliver(DK(entails(eta, d.a) ? D_COVERED : D_NOT_COVERED, 0, 0), oA, oI); return;
  case OP_USE_PARTIAL:
    if (entails(eta, d.a)) deliver(DR(d.b, 0), oA, oI); else deliver(DK(D_NOT_COVERED, 0, 0), oA, oI);
    return;
  /* --- inspection of the opened constructor --- */
  case OP_INSPECT: {
    int ref = d.a;
    if (isVar(ref)) { deliver(DR(ref, 1), oA, oI); return; }
    Head h = openRef(ref);
    switch (h.tag) {
    case UNIV: case PI: case SIGMA: case LAM: case PAIR: case PATH: case PLAM: deliver(DR(ref, 0), oA, oI); return;
    case GLOBAL: { int ev = newOp(OP_EVAL, oA, oI, eta, 0, 0, 0); to(DR(ref, 0), OP_UNFOLD, ev, 0, eta, 0, 0, 0); return; }
    case APP: evalOpenTo(h.f[0].ref, eta, newOp(OP_KAPP, oA, oI, eta, ref, h.f[1].ref, 0)); return;
    case FST: case SND: evalOpenTo(h.f[0].ref, eta, newOp(h.tag == FST ? OP_KFST : OP_KSND, oA, oI, eta, ref, 0, 0)); return;
    case PAPP: to(DK(D_FACE, endpoint(h.f[4].itv, 0), 0), OP_FACE_COVERAGE, newOp(OP_KPEND0, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); return;
    case GLUE_TYPE: to(DK(D_PARTIAL, h.f[2].guard, h.f[2].ref), OP_USE_PARTIAL, newOp(OP_KGLUE, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); return;
    case GLUE_INTRO: to(DK(D_PARTIAL, h.f[4].guard, h.f[4].ref), OP_USE_PARTIAL, newOp(OP_KGLUE, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); return;
    case UNGLUE: to(DK(D_PARTIAL, h.f[3].guard, h.f[3].ref), OP_USE_PARTIAL, newOp(OP_KUNGLUE0, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); return;
    case SYSTEM:
      if (h.sysN == 0) { deliver(DR(ref, 0), oA, oI); return; }
      to(DK(D_PARTIAL, h.sysFace[0], h.sysTerm[0]), OP_USE_PARTIAL, newOp(OP_KSYS, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0);
      return;
    case COMP: {
      int k = newOp(OP_KCOMP0, oA, oI, eta, ref, 0, 0);
      int use = newOp(OP_USE_PARTIAL, k, 0, eta, 0, 0, 0);
      to(DK(D_PDBIND, ref, 2), OP_APPLY_PDIM, use, 0, eta, I1, 0, 0);
      return;
    }
    }
    die("internal: unknown tag");
  }
  /* --- continuations --- */
  case OP_KAPP: {
    int orig = o.p[1], arg = o.p[2]; Head hf = openRef(d.a);
    if (hf.tag == LAM) { int ev = newOp(OP_EVAL, oA, oI, eta, 0, 0, 0); to(DK(D_TBIND, d.a, 1), OP_APPLY_TERM, ev, 0, eta, arg, 0, 0); }
    else if (hf.tag == SYSTEM) evalTo(distribute(&hf, orig), eta, oA, oI);
    else deliver(DR(orig, 1), oA, oI);
    return;
  }
  case OP_KFST: case OP_KSND: {
    int orig = o.p[1]; Head hp = openRef(d.a);
    if (hp.tag == PAIR) evalTo(hp.f[o.kind == OP_KFST ? 0 : 1].ref, eta, oA, oI);
    else if (hp.tag == SYSTEM) evalTo(distribute(&hp, orig), eta, oA, oI);
    else deliver(DR(orig, 1), oA, oI);
    return;
  }
  case OP_KPEND0: case OP_KPEND1: {
    int orig = o.p[1]; Head h = openRef(orig);
    if (d.kind == D_COVERED) { evalTo(h.f[o.kind == OP_KPEND0 ? 1 : 2].ref, eta, oA, oI); return; }
    if (o.kind == OP_KPEND0) { to(DK(D_FACE, endpoint(h.f[4].itv, 1), 0), OP_FACE_COVERAGE, newOp(OP_KPEND1, oA, oI, eta, orig, 0, 0), 0, eta, 0, 0, 0); return; }
    evalOpenTo(h.f[3].ref, eta, newOp(OP_KPAPP, oA, oI, eta, orig, 0, 0));
    return;
  }
  case OP_KPAPP: {
    int orig = o.p[1]; Head hp = openRef(d.a), ho = openRef(orig);
    if (hp.tag == PLAM) { int ev = newOp(OP_EVAL, oA, oI, eta, 0, 0, 0); to(DK(D_DBIND, d.a, 0), OP_APPLY_DIM, ev, 0, eta, ho.f[4].itv, 0, 0); }
    else if (hp.tag == SYSTEM) evalTo(distribute(&hp, orig), eta, oA, oI);
    else deliver(DR(orig, 1), oA, oI);                 /* its endpoints were not entailed */
    return;
  }
  case OP_KGLUE: {                                        /* Glue type or glue: collapse only on the entailed face */
    int orig = o.p[1];
    if (d.kind == D_REF) evalTo(d.a, eta, oA, oI); else deliver(DR(orig, 0), oA, oI);
    return;
  }
  case OP_KUNGLUE0: {
    int orig = o.p[1]; Head h = openRef(orig);
    if (d.kind == D_REF) evalTo(bApp(bFst(d.a), h.f[4].ref), eta, oA, oI);
    else evalOpenTo(h.f[4].ref, eta, newOp(OP_KUNGLUE, oA, oI, eta, orig, 0, 0));
    return;
  }
  case OP_KUNGLUE: {
    int orig = o.p[1]; Head hv = openRef(d.a);
    if (hv.tag == GLUE_INTRO) evalTo(hv.f[5].ref, eta, oA, oI);
    else if (hv.tag == SYSTEM) evalTo(distribute(&hv, orig), eta, oA, oI);
    else deliver(DR(orig, 1), oA, oI);
    return;
  }
  case OP_KSYS: {
    int orig = o.p[1], k = o.p[2]; Head h = openRef(orig);
    if (d.kind == D_REF) { evalTo(d.a, eta, oA, oI); return; }
    if (k + 1 < h.sysN) { to(DK(D_PARTIAL, h.sysFace[k + 1], h.sysTerm[k + 1]), OP_USE_PARTIAL, newOp(OP_KSYS, oA, oI, eta, orig, k + 1, 0), 0, eta, 0, 0, 0); return; }
    deliver(DR(orig, 0), oA, oI);                       /* no branch covers: retained */
    return;
  }
  case OP_KCOMP0: {                                       /* tube at 1 if the face is entailed, else the family's head at j */
    int c = o.p[1];
    if (d.kind == D_REF) { evalTo(d.a, eta, oA, oI); return; }
    Resolved fam = resolve(c, 0);
    int k = newOp(OP_KCOMP, oA, oI, eta, c, 0, 0);
    int op = newOp(OP_OPEN, k, 0, 0, 0, 0, 0);
    int ev = newOp(OP_EVAL, op, 0, eta, 0, 0, 0);
    to(DK(D_DBIND, c, 0), OP_APPLY_DIM, ev, 0, eta, ivar(fam.var), 0, 0);
    return;
  }
  case OP_KCOMP: {
    int c = o.p[1], ok = 0, r = compClause(c, eta, d, &ok);
    if (ok) evalTo(r, eta, oA, oI); else deliver(DR(c, 1), oA, oI);
    return;
  }
  }
  die("internal: an operation agent without a rule");
}
/* demand from outside the net (read-back, elaboration): run to quiescence */
static Data demand(int ref, int chi) {
  int root = newOp(OP_ROOT, -1, -1, 0, 0, 0, 0);
  evalTo(ref, chi, root, 0);
  while (nqueue) { Pair pr = queue[--nqueue]; fire(pr); }
  if (!ops[root].rootset) die("evaluation demands itself (a cycle)");
  return ops[root].rootv;
}

/* ------------------------------------------------------------------------
 * Source: a small CCHM syntax
 * ---------------------------------------------------------------------- */
enum { A_ID, A_U, A_LAM, A_PI, A_SIGMA, A_APP, A_PAIR, A_FST, A_SND, A_PLAM, A_PAPP, A_PATHP, A_PATH,
       A_COMP, A_COE, A_ANN, A_FILL, A_GLUE, A_GLUEI, A_UNGLUE, A_SYS, A_I0, A_I1, A_INEG, A_IAND, A_IOR, A_EQ };
typedef struct Ast { int k; char *name; struct Ast **c; int n; int eps; } Ast;
static Ast *amk(int k, const char *name, int n) { Ast *a = xalloc(sizeof *a); a->k = k; a->name = name ? xdup(name) : NULL; a->n = n; a->c = xalloc(sizeof(Ast *) * (n + 1)); return a; }

static char **tok; static int ntok, captok, pos; static const char *where;
static void lex(const char *s) {
  while (*s) {
    if (isspace((unsigned char)*s)) { s++; continue; }
    if (s[0] == '-' && s[1] == '-') { while (*s && *s != '\n') s++; continue; }
    const char *b = s;
    if (isalpha((unsigned char)*s) || *s == '_') { while (isalnum((unsigned char)*s) || *s == '_' || *s == '\'') s++; }
    else if (!strncmp(s, "->", 2) || !strncmp(s, "/\\", 2) || !strncmp(s, "\\/", 2) || !strncmp(s, ".1", 2) || !strncmp(s, ".2", 2)) s += 2;
    else if (strchr("01()[],:*\\<>@~=", *s)) s++;
    else die("unexpected character '%c'", *s);
    char *t = xalloc(s - b + 1); memcpy(t, b, s - b); PUSH(tok, ntok, captok, t);
  }
}
static const char *pk(int k) { return pos + k < ntok ? tok[pos + k] : ""; }
static int is(const char *s) { return !strcmp(pk(0), s); }
static const char *nx(void) { if (pos >= ntok) die("unexpected end of input"); return tok[pos++]; }
static void want(const char *s) { if (!is(s)) die("expected '%s' at '%s'", s, pk(0)); pos++; }
static int isIdent(const char *s) { return isalpha((unsigned char)s[0]) || s[0] == '_'; }
static int kw(const char *s) {
  static const char *k[] = { "U", "comp", "hcomp", "coe", "fill", "Glue", "glue", "unglue", "PathP", "Path", "postulate", "def", "eval", NULL };
  for (int i = 0; k[i]; i++) if (!strcmp(s, k[i])) return 1;
  return 0;
}

static Ast *pTerm(void);
static Ast *pAtom(void);
static Ast *pItv(void);
static Ast *pIatom(void) {
  if (is("0")) { pos++; return amk(A_I0, NULL, 0); }
  if (is("1")) { pos++; return amk(A_I1, NULL, 0); }
  if (is("~")) { pos++; Ast *a = amk(A_INEG, NULL, 1); a->c[0] = pIatom(); return a; }
  if (is("(")) { pos++; Ast *a = pItv(); want(")"); return a; }
  if (isIdent(pk(0)) && !kw(pk(0))) return amk(A_ID, nx(), 0);
  die("expected an interval at '%s'", pk(0)); return NULL;
}
static Ast *pImeet(void) { Ast *l = pIatom(); while (is("/\\")) { pos++; Ast *a = amk(A_IAND, NULL, 2); a->c[0] = l; a->c[1] = pIatom(); l = a; } return l; }
static Ast *pItv(void) { Ast *l = pImeet(); while (is("\\/")) { pos++; Ast *a = amk(A_IOR, NULL, 2); a->c[0] = l; a->c[1] = pImeet(); l = a; } return l; }
/* faces: (r = 0), (r = 1), /\ and \/ */
static Ast *pFlit(void) {
  want("("); Ast *r = pItv(); want("=");
  Ast *a = amk(A_EQ, NULL, 1); a->c[0] = r;
  if (is("0")) a->eps = 0; else if (is("1")) a->eps = 1; else die("expected 0 or 1");
  pos++; want(")"); return a;
}
static Ast *pFconj(void) { Ast *l = pFlit(); while (is("/\\")) { pos++; Ast *a = amk(A_IAND, NULL, 2); a->c[0] = l; a->c[1] = pFlit(); l = a; } return l; }
static Ast *pFace(void) { Ast *l = pFconj(); while (is("\\/")) { pos++; Ast *a = amk(A_IOR, NULL, 2); a->c[0] = l; a->c[1] = pFconj(); l = a; } return l; }
/* [ face -> t , ... ]; with tuple > 1, each branch is face -> (t1 , .. , tn) */
static Ast *pSys(int tuple) {
  want("["); Ast *s = amk(A_SYS, NULL, 0);
  Ast **items = NULL; int n = 0, cap = 0;
  while (!is("]")) {
    Ast *f = pFace(); want("->");
    PUSH(items, n, cap, f);
    if (tuple == 1) PUSH(items, n, cap, pTerm());
    else { want("("); for (int i = 0; i < tuple; i++) { if (i) want(","); PUSH(items, n, cap, pTerm()); } want(")"); }
    if (is(",")) pos++; else break;
  }
  want("]");
  s->c = items; s->n = n; s->eps = tuple;
  return s;
}
static char *pDimBinder(void) { want("<"); char *i = xdup(nx()); want(">"); return i; }
static Ast *pPost(Ast *a) {
  for (;;) {
    if (is(".1")) { pos++; Ast *b = amk(A_FST, NULL, 1); b->c[0] = a; a = b; continue; }
    if (is(".2")) { pos++; Ast *b = amk(A_SND, NULL, 1); b->c[0] = a; a = b; continue; }
    return a;
  }
}
static Ast *pAtom(void) {
  Ast *a;
  if (is("(")) {
    pos++; a = pTerm();
    if (is(",")) { pos++; Ast *p = amk(A_PAIR, NULL, 2); p->c[0] = a; p->c[1] = pTerm(); want(")"); return pPost(p); }
    if (is(":")) { pos++; Ast *n = amk(A_ANN, NULL, 2); n->c[0] = a; n->c[1] = pTerm(); want(")"); return pPost(n); }
    want(")"); return pPost(a);
  }
  if (is("U")) { pos++; return amk(A_U, NULL, 0); }
  if (is("0")) { pos++; return amk(A_I0, NULL, 0); }
  if (is("1")) { pos++; return amk(A_I1, NULL, 0); }
  if (is("~")) { pos++; a = amk(A_INEG, NULL, 1); a->c[0] = pIatom(); return a; }
  if (isIdent(pk(0)) && !kw(pk(0))) return pPost(amk(A_ID, nx(), 0));
  die("unexpected '%s'", pk(0)); return NULL;
}
static int atomStart(void) { return is("(") || is("U") || is("0") || is("1") || is("~") || (isIdent(pk(0)) && !kw(pk(0))); }
static Ast *pApp(void) {
  Ast *a;
  if (is("comp") || is("hcomp") || is("fill") || is("coe")) {
    int k = (is("comp") || is("hcomp")) ? A_COMP : is("fill") ? A_FILL : A_COE; pos++;
    char *i = pDimBinder();
    a = amk(k, i, k == A_COE ? 2 : k == A_COMP ? 3 : 4);
    a->c[0] = pAtom();
    if (k == A_COE) a->c[1] = pAtom();
    else { a->c[1] = pSys(1); a->c[2] = pAtom(); if (k == A_FILL) a->c[3] = pIatom(); }
  } else if (is("Glue")) {
    pos++; a = amk(A_GLUE, NULL, 2); a->c[0] = pAtom(); a->c[1] = pSys(2);
  } else if (is("glue")) {
    pos++; a = amk(A_GLUEI, NULL, 3); a->c[0] = pAtom(); a->c[1] = pSys(3); a->c[2] = pAtom();
  } else if (is("unglue")) {
    pos++; a = amk(A_UNGLUE, NULL, 3); a->c[0] = pAtom(); a->c[1] = pSys(2); a->c[2] = pAtom();
  } else if (is("PathP")) {
    pos++; want("("); char *i = pDimBinder(); a = amk(A_PATHP, i, 3); a->c[0] = pTerm(); want(")"); a->c[1] = pAtom(); a->c[2] = pAtom();
  } else if (is("Path")) {
    pos++; a = amk(A_PATH, NULL, 3); a->c[0] = pAtom(); a->c[1] = pAtom(); a->c[2] = pAtom();
  } else {
    a = pAtom();
    while (atomStart()) { Ast *b = amk(A_APP, NULL, 2); b->c[0] = a; b->c[1] = pAtom(); a = b; }
  }
  while (is("@")) { pos++; Ast *b = amk(A_PAPP, NULL, 2); b->c[0] = a; b->c[1] = pIatom(); a = b; }
  return a;
}
static int binderGroup(void) {      /* ( x y : */
  if (!is("(")) return 0;
  int k = 1; while (isIdent(pk(k)) && !kw(pk(k))) k++;
  return k > 1 && !strcmp(pk(k), ":");
}
static Ast *pTerm(void) {
  if (is("\\")) {
    pos++; want("("); char *x = xdup(nx()); want(":"); Ast *A = pTerm(); want(")"); want("->");
    Ast *a = amk(A_LAM, x, 2); a->c[0] = A; a->c[1] = pTerm(); return a;
  }
  if (is("<")) { char *i = pDimBinder(); Ast *a = amk(A_PLAM, i, 1); a->c[0] = pTerm(); return a; }
  if (binderGroup()) {
    int save = pos; pos++;
    char *xs[16]; int nx_ = 0; while (!is(":")) { if (nx_ == 16) die("too many binders"); xs[nx_++] = xdup(nx()); }
    pos++; Ast *A = pTerm(); want(")");
    if (is("->") || is("*")) {
      int k = is("->") ? A_PI : A_SIGMA; pos++;
      Ast *B = pTerm();
      for (int i = nx_ - 1; i >= 0; i--) { Ast *a = amk(k, xs[i], 2); a->c[0] = A; a->c[1] = B; B = a; }
      return B;
    }
    pos = save;
  }
  Ast *l = pApp();
  if (is("->") || is("*")) {
    int k = is("->") ? A_PI : A_SIGMA; pos++;
    Ast *a = amk(k, "_", 2); a->c[0] = l; a->c[1] = pTerm(); return a;
  }
  return l;
}

/* ------------------------------------------------------------------------
 * Elaboration: names to identities, source to cells
 * ---------------------------------------------------------------------- */
typedef struct Scope { const char *name; int var; struct Scope *up; } Scope;
typedef struct { char *name; int var; } Post;
static Post *posts; static int nposts, capposts;
static int lookup(Scope *s, const char *n) {
  for (; s; s = s->up) if (!strcmp(s->name, n)) return s->var;
  for (int i = 0; i < nposts; i++) if (!strcmp(posts[i].name, n)) return posts[i].var;
  return -1;
}
static int elab(Ast *a, Scope *s);
static int elabItv(Ast *a, Scope *s) {
  switch (a->k) {
  case A_I0: return I0;
  case A_I1: return I1;
  case A_INEG: return ineg(elabItv(a->c[0], s));
  case A_IAND: return imeet(elabItv(a->c[0], s), elabItv(a->c[1], s));
  case A_IOR: return ijoin(elabItv(a->c[0], s), elabItv(a->c[1], s));
  case A_ID: { int v = lookup(s, a->name); if (v < 0 || vars[v].sort != S_DIM) die("%s is not a dimension", a->name); return ivar(v); }
  default: die("expected an interval"); return -1;
  }
}
static int elabFace(Ast *a, Scope *s) {
  if (a->k == A_EQ) return endpoint(elabItv(a->c[0], s), a->eps);
  if (a->k == A_IAND) return fand(elabFace(a->c[0], s), elabFace(a->c[1], s));
  if (a->k == A_IOR) return forr(elabFace(a->c[0], s), elabFace(a->c[1], s));
  die("expected a face"); return -1;
}
/* the type of a reference, where it can be read off (for the family and
 * endpoints a path application carries) */
static int *annot; static int capannot;
static void annotate(int ref, int ty) {
  if (ref >= capannot) { int nc = ref * 2 + 64; annot = xgrow(annot, sizeof(int) * nc); for (int i = capannot; i < nc; i++) annot[i] = -1; capannot = nc; }
  annot[ref] = ty;
}
static int synth(int ref) {
  if (ref < capannot && annot[ref] >= 0) return annot[ref];
  if (isVar(ref)) return vars[refVarId(ref)].type;
  Head h = openRef(ref);
  switch (h.tag) {
  case PLAM: {                                   /* <i> t : PathP (<i> type of t) t(0) t(1) */
    Resolved b = resolve(ref, 0); int B = synth(b.body); if (B < 0) return -1;
    Binder bd = { S_DIM, b.var, -1 };
    Field f[3] = { FB(K_DIM_BODY, B, 0, 0), FT(reindex(b.body, map1Dim(b.var, I0))), FT(reindex(b.body, map1Dim(b.var, I1))) };
    return cell(PATH, 1, &bd, 3, f);
  }
  case GLOBAL: { int ty = defs[h.scal].type; return ty < 0 ? -1 : reindex(ty, refMap(ref)); }
  case APP: { int t = synth(h.f[0].ref); if (t < 0) return -1; Data w = demand(t, F1); Head ht = openRef(w.a); if (ht.tag != PI) return -1; return applyTerm(w.a, 1, h.f[1].ref); }
  case FST: case SND: {
    int t = synth(h.f[0].ref); if (t < 0) return -1; Data w = demand(t, F1); Head ht = openRef(w.a); if (ht.tag != SIGMA) return -1;
    return h.tag == FST ? ht.f[0].ref : applyTerm(w.a, 1, bFst(h.f[0].ref));
  }
  case PAPP: return applyDim(ref, 0, h.f[4].itv);
  case COMP: return applyDim(ref, 0, I1);
  case UNGLUE: return h.f[0].ref;
  default: return -1;
  }
}
static int sysFace(Ast *sys, Scope *s, int tuple, int **faces) {
  int n = sys->n / (tuple + 1); *faces = xalloc(sizeof(int) * (n + 1)); int phi = F0;
  for (int k = 0; k < n; k++) { (*faces)[k] = elabFace(sys->c[k * (tuple + 1)], s); phi = forr(phi, (*faces)[k]); }
  return phi;
}
static int sysPart(Ast *sys, Scope *s, int tuple, int which, int *faces) {
  int n = sys->n / (tuple + 1); int *ts = xalloc(sizeof(int) * (n + 1));
  for (int k = 0; k < n; k++) ts[k] = elab(sys->c[k * (tuple + 1) + 1 + which], s);
  int r = n == 1 ? ts[0] : bSys(n, faces, ts);
  free(ts); return r;
}
static int binderLam(int tag, Ast *a, Scope *s) {
  int A = elab(a->c[0], s);
  int x = newVar(S_TERM, a->name, A);
  Scope s2 = { a->name, x, s };
  int B = elab(a->c[1], &s2);
  Binder b = { S_TERM, x, A }; Field f[2] = { FT(A), FB(K_TERM_BODY, B, 0, 0) };
  return cell(tag, 1, &b, 2, f);
}
static int elab(Ast *a, Scope *s) {
  switch (a->k) {
  case A_U: return cell(UNIV, 0, NULL, 0, NULL);
  case A_ID: {
    int v = lookup(s, a->name);
    if (v >= 0) { if (vars[v].sort != S_TERM) die("%s is a dimension, used as a term", a->name); return refVar(v); }
    int d = findDef(a->name);
    if (d >= 0) {
      if (defs[d].params.n) die("%s takes %d arguments", a->name, defs[d].params.n);
      return globalView(d, NULL);
    }
    die("unknown name %s", a->name); return -1;
  }
  case A_APP: {
    Ast *spine[64]; int n = 0; Ast *h = a;
    while (h->k == A_APP) { if (n == 64) die("application too long"); spine[n++] = h->c[1]; h = h->c[0]; }
    if (h->k == A_ID && lookup(s, h->name) < 0 && findDef(h->name) >= 0) {
      int d = findDef(h->name), np = defs[d].params.n;
      if (n < np) die("%s takes %d arguments", h->name, np);
      int *args = xalloc(sizeof(int) * (np + 1));
      for (int i = 0; i < np; i++) {
        Ast *arg = spine[n - 1 - i];
        args[i] = vars[defs[d].params.a[i]].sort == S_DIM ? elabItv(arg, s) : elab(arg, s);
      }
      int r = globalView(d, args); free(args);
      for (int i = np; i < n; i++) r = bApp(r, elab(spine[n - 1 - i], s));
      return r;
    }
    return bApp(elab(a->c[0], s), elab(a->c[1], s));
  }
  case A_LAM: return binderLam(LAM, a, s);
  case A_PI: return binderLam(PI, a, s);
  case A_SIGMA: return binderLam(SIGMA, a, s);
  case A_PAIR: return bPair(elab(a->c[0], s), elab(a->c[1], s));
  case A_ANN: { int t = elab(a->c[0], s), T = elab(a->c[1], s); annotate(t, T); return t; }
  case A_FST: return bFst(elab(a->c[0], s));
  case A_SND: return bSnd(elab(a->c[0], s));
  case A_PLAM: {
    int i = newVar(S_DIM, a->name, -1); Scope s2 = { a->name, i, s };
    return bPlam(i, elab(a->c[0], &s2));
  }
  case A_PATHP: case A_PATH: {
    int i = newVar(S_DIM, a->k == A_PATHP ? a->name : "_", -1); Scope s2 = { a->name ? a->name : "_", i, s };
    int B = elab(a->c[0], a->k == A_PATHP ? &s2 : s);
    Binder b = { S_DIM, i, -1 }; Field f[3] = { FB(K_DIM_BODY, B, 0, 0), FT(elab(a->c[1], s)), FT(elab(a->c[2], s)) };
    return cell(PATH, 1, &b, 3, f);
  }
  case A_PAPP: {
    int p = elab(a->c[0], s), r = elabItv(a->c[1], s);
    int ty = synth(p);
    if (ty >= 0) {
      Data w = demand(ty, F1); Head ht = openRef(w.a);
      if (ht.tag == PATH) { Resolved B = resolve(w.a, 0); return bPapp(B.var, B.body, ht.f[1].ref, ht.f[2].ref, p, r); }
    }
    die("%s: the type of the path in `p @ r` cannot be read off; annotate it, (p : PathP (<i> A) a b) @ r", where);
    return -1;
  }
  case A_COMP: case A_FILL: case A_COE: {
    const char *iname = a->name;
    int i = newVar(S_DIM, iname, -1); Scope s2 = { iname, i, s };
    int A = elab(a->c[0], &s2);
    if (a->k == A_COE) { int x = elab(a->c[1], s); return bComp(i, A, F0, x, x); }
    int *faces; int phi = sysFace(a->c[1], s, 1, &faces);
    { IV d = { 0 }; formDims(phi, 1, &d); if (ivhas(&d, i)) die("a composition's face mentions its own dimension"); free(d.a); }
    int u = a->c[1]->n ? sysPart(a->c[1], &s2, 1, 0, faces) : -1;
    int a0 = elab(a->c[2], s);
    if (u < 0) u = a0;
    if (a->k != A_FILL) return bComp(i, A, phi, u, a0);
    /* fill (section 9): comp^j A(r/\j) [phi -> u(r/\j), (r=0) -> a0] a0 */
    int r = elabItv(a->c[3], s), jj = newVar(S_DIM, "j", -1), sm = map1Dim(i, imeet(r, ivar(jj)));
    int z = endpoint(r, 0);
    int fs[2] = { phi, z }, ts[2] = { reindex(u, sm), a0 };
    return bComp(jj, reindex(A, sm), forr(phi, z), bSys(2, fs, ts), a0);
  }
  case A_GLUE: {
    int A = elab(a->c[0], s); int *faces; int phi = sysFace(a->c[1], s, 2, &faces);
    return bGlueType(A, phi, sysPart(a->c[1], s, 2, 0, faces), sysPart(a->c[1], s, 2, 1, faces));
  }
  case A_GLUEI: {
    int A = elab(a->c[0], s); int *faces; int phi = sysFace(a->c[1], s, 3, &faces);
    return bGlueIntro(A, phi, sysPart(a->c[1], s, 3, 0, faces), sysPart(a->c[1], s, 3, 1, faces), sysPart(a->c[1], s, 3, 2, faces), elab(a->c[2], s));
  }
  case A_UNGLUE: {
    int A = elab(a->c[0], s); int *faces; int phi = sysFace(a->c[1], s, 2, &faces);
    return bUnglue(A, phi, sysPart(a->c[1], s, 2, 0, faces), sysPart(a->c[1], s, 2, 1, faces), elab(a->c[2], s));
  }
  default: die("this is not a term"); return -1;
  }
}

/* ------------------------------------------------------------------------
 * Read-back: the normal form under an ambient face
 * ---------------------------------------------------------------------- */
static void pVar(int v) { printf("%s", vars[v].name); if (!vars[v].plain) printf("_%d", v); }
static void pItv(int r) {
  Form x = formGet(r, 0);
  if (x.n == 0) printf("0");
  else if (x.n == 1 && x.c[0].n == 0) printf("1");
  else for (int i = 0; i < x.n; i++) {
    if (i) printf(" \\/ ");
    if (x.c[i].n > 1 && x.n > 1) printf("(");
    for (int k = 0; k < x.c[i].n; k++) { if (k) printf(" /\\ "); if (x.c[i].a[k] & 1) printf("~"); pVar(x.c[i].a[k] >> 1); }
    if (x.c[i].n > 1 && x.n > 1) printf(")");
  }
  formFree(&x);
}
static void pFace(int phi) {
  Form x = formGet(phi, 1);
  if (x.n == 0) printf("false");
  else if (x.n == 1 && x.c[0].n == 0) printf("true");
  else for (int i = 0; i < x.n; i++) {
    if (i) printf(" \\/ ");
    for (int k = 0; k < x.c[i].n; k++) { if (k) printf(" /\\ "); printf("("); pVar(x.c[i].a[k] >> 1); printf(" = %d)", x.c[i].a[k] & 1); }
  }
  formFree(&x);
}
/* read-back is a fold over occurrences: a field under a face is read in the
 * restricted context (section 9); it adds no interaction of its own */
static int TOPCTX;
static void nfo(Occurrence o);
static void nf(int ref, int chi) { Occurrence o = { ref, ctxRestrict(TOPCTX, chi) }; nfo(o); }
static void nfPartial(int ref, int chi, int guard) { int c = fand(chi, guard); if (c == F0) printf("_"); else nf(ref, c); }
static void nfo(Occurrence occ) {
  int chi = ctxFace(occ.ctx), ref = occ.ref;
  if (chi == F0) { printf("_"); return; }
  Data w = demand(ref, chi);
  int r = w.a;
  if (isVar(r)) { pVar(refVarId(r)); return; }
  Head h = openRef(r);
  switch (h.tag) {
  case UNIV: printf("U"); return;
  case PI: case SIGMA: case LAM: {
    Resolved b = resolve(r, 1);
    if (h.tag == LAM) { printf("(\\("); pVar(b.var); printf(" : "); nf(h.f[0].ref, chi); printf(") -> "); }
    else { printf("(("); pVar(b.var); printf(" : "); nf(h.f[0].ref, chi); printf(") %s ", h.tag == PI ? "->" : "*"); }
    nf(b.body, chi); printf(")"); return;
  }
  case PAIR: printf("("); nf(h.f[0].ref, chi); printf(" , "); nf(h.f[1].ref, chi); printf(")"); return;
  case APP: printf("("); nf(h.f[0].ref, chi); printf(" "); nf(h.f[1].ref, chi); printf(")"); return;
  case FST: case SND: nf(h.f[0].ref, chi); printf(h.tag == FST ? ".1" : ".2"); return;
  case PATH: { Resolved b = resolve(r, 0); printf("(PathP (<"); pVar(b.var); printf("> "); nf(b.body, chi); printf(") "); nf(h.f[1].ref, chi); printf(" "); nf(h.f[2].ref, chi); printf(")"); return; }
  case PLAM: { Resolved b = resolve(r, 0); printf("(<"); pVar(b.var); printf("> "); nf(b.body, chi); printf(")"); return; }
  case PAPP: printf("("); nf(h.f[3].ref, chi); printf(" @ "); pItv(h.f[4].itv); printf(")"); return;
  case GLUE_TYPE: printf("(Glue "); nf(h.f[0].ref, chi); printf(" ["); pFace(h.f[1].face); printf(" -> ("); nfPartial(h.f[2].ref, chi, h.f[1].face); printf(" , "); nfPartial(h.f[3].ref, chi, h.f[1].face); printf(")])"); return;
  case GLUE_INTRO: printf("(glue ["); pFace(h.f[1].face); printf(" -> "); nfPartial(h.f[4].ref, chi, h.f[1].face); printf("] "); nf(h.f[5].ref, chi); printf(")"); return;
  case UNGLUE: printf("(unglue "); nf(h.f[4].ref, chi); printf(")"); return;
  case SYSTEM:
    printf("[");
    for (int k = 0, first = 1; k < h.sysN; k++) { int c = fand(chi, h.sysFace[k]); if (c == F0) continue; if (!first) printf(", "); first = 0; pFace(h.sysFace[k]); printf(" -> "); nf(h.sysTerm[k], c); }
    printf("]"); return;
  case COMP: {
    Resolved fam = resolve(r, 0), tb = resolve(r, 2);
    printf("(comp <"); pVar(fam.var); printf("> "); nf(fam.body, chi); printf(" ["); pFace(h.f[1].face); printf(" -> ");
    nfPartial(tb.body, chi, h.f[1].face); printf("] "); nf(h.f[3].ref, chi); printf(")"); return;
  }
  default: printf("?");
  }
}

/* ------------------------------------------------------------------------
 * Declarations
 * ---------------------------------------------------------------------- */
static void decl(void) {
  if (is("postulate")) {
    pos++; char *x = xdup(nx()); want(":");
    int ty = elab(pTerm(), NULL);
    Post p = { x, newVar(S_TERM, x, ty) }; vars[p.var].plain = 1; PUSH(posts, nposts, capposts, p);
    return;
  }
  if (is("def")) {
    pos++; Def d; memset(&d, 0, sizeof d); d.name = xdup(nx()); d.type = -1;
    Scope *s = NULL;
    while (is("(")) {
      pos++; char *xs[16]; int n = 0;
      while (!is(":")) { if (n == 16) die("too many parameters"); xs[n++] = xdup(nx()); }
      pos++;
      int dim = is("I") && !strcmp(pk(1), ")");
      int ty = -1;
      if (dim) pos++; else ty = elab(pTerm(), s);
      want(")");
      for (int i = 0; i < n; i++) {
        int v = newVar(dim ? S_DIM : S_TERM, xs[i], ty);
        Scope *s2 = xalloc(sizeof *s2); s2->name = xs[i]; s2->var = v; s2->up = s; s = s2;
        ivp(&d.params, v);
      }
    }
    if (is(":")) { pos++; d.type = elab(pTerm(), s); }
    want("=");
    IV gT = { 0 }, gD = { 0 };
    for (int i = 0; i < d.params.n; i++) ivp(vars[d.params.a[i]].sort == S_TERM ? &gT : &gD, d.params.a[i]);
    int idx = ndefs;
    Field none[1];
    d.origin = mkOrigin(GLOBAL, idx, 0, NULL, 0, none, &gT, &gD);
    PUSH(defs, ndefs, capdefs, d);
    defs[idx].body = elab(pTerm(), s);
    if (!strcmp(d.name, "fib")) DEF_fib = idx;
    if (!strcmp(d.name, "lineEquiv")) DEF_lineEquiv = idx;
    return;
  }
  if (is("eval")) {
    pos++; int t = elab(pTerm(), NULL);
    long before = interactions;
    nf(t, F1);
    printf("\n  [%ld interactions]\n", interactions - before);
    return;
  }
  die("expected postulate, def or eval at '%s'", pk(0));
}

static char *slurp(const char *fn) {
  FILE *f = fopen(fn, "rb"); if (!f) die("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *b = xalloc(n + 2); if (fread(b, 1, n, f) != (size_t)n) die("cannot read %s", fn); fclose(f);
  b[n] = '\n'; return b;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: cell file ...\n"); return 2; }
  I0 = formConst(0, 0); I1 = formConst(1, 0); F0 = formConst(0, 1); F1 = formConst(1, 1);
  MID = mapMake(NULL, 0, NULL, 0);
  { IV none = { 0 }; TOPCTX = ctxMake(&none, F1); }
  for (int i = 1; i < argc; i++) { where = argv[i]; lex(slurp(argv[i])); }
  while (pos < ntok) decl();
  return 0;
}

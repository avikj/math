/* cell/cell.c -- scoped references and face sensitive cubical evaluation
 * with interaction optimality: the owner's handoff, cell/HANDOFF.md.
 *
 *   section 2-9    signature, intervals, faces, maps, support, binders, open
 *   section 10-11  the evaluation cache keyed by (reference, projected face)
 *   section 12-18  dispatch and the composition clauses
 *   section 19-20  scope agents, graph replacement
 *   section 26     the event protocol: REQUEST, EVALUATE, PUBLISH, DELIVER
 *   section 33-34  checking the annotated core, definitional conversion
 *   section 35     the worker pool and quiescence
 *   section 36     ownership and teardown
 *   section 37     the comparison dump (compared by cell/cellcmp.c)
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include <setjmp.h>
#include <pthread.h>
#include <stdatomic.h>

/* An internal failure ends the machine.  A user error in the source (an
 * unknown name, a malformed term) is reported by fail(); while an `assert
 * invalid` declaration is admitted, the main thread recovers from it. */
static pthread_t mainThread;
static jmp_buf *recoverJmp;
static char lastError[512];
static void die(const char *fmt, ...) {
  char buf[512]; va_list ap; va_start(ap, fmt); vsnprintf(buf, sizeof buf, fmt, ap); va_end(ap);
  fflush(stdout); fprintf(stderr, "cell: internal: %s\n", buf); exit(2);
}
static void fail(const char *fmt, ...) {
  va_list ap; va_start(ap, fmt); vsnprintf(lastError, sizeof lastError, fmt, ap); va_end(ap);
  if (recoverJmp && pthread_equal(pthread_self(), mainThread)) longjmp(*recoverJmp, 1);
  fflush(stdout); fprintf(stderr, "cell: %s\n", lastError); exit(1);
}
static void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xgrow(void *p, size_t n) { p = realloc(p, n ? n : 1); if (!p) die("out of memory"); return p; }
static char *xdup(const char *s) { char *d = xalloc(strlen(s) + 1); strcpy(d, s); return d; }
#define PUSH(arr, n, cap, v) do { if ((n) == (cap)) { (cap) = (cap) ? 2 * (cap) : 8; \
    (arr) = xgrow((arr), sizeof(*(arr)) * (cap)); } (arr)[(n)++] = (v); } while (0)
#define LOCK(m) pthread_mutex_lock(m)
#define UNLOCK(m) pthread_mutex_unlock(m)

typedef struct { int *a; int n, cap; } IV;
static void ivp(IV *v, int x) { PUSH(v->a, v->n, v->cap, x); }
static IV ivcopy(const IV *v) { IV r = { 0 }; for (int i = 0; i < v->n; i++) ivp(&r, v->a[i]); return r; }
static int ivhas(const IV *v, int x) { for (int i = 0; i < v->n; i++) if (v->a[i] == x) return 1; return 0; }
static void ivadd(IV *v, int x) { if (!ivhas(v, x)) ivp(v, x); }
static void ivfree(IV *v) { free(v->a); v->a = NULL; v->n = v->cap = 0; }
static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return x < y ? -1 : x > y; }
static void ivsortu(IV *v) {
  if (v->n) qsort(v->a, v->n, sizeof(int), cmpint);
  int o = 0; for (int i = 0; i < v->n; i++) if (!o || v->a[o - 1] != v->a[i]) v->a[o++] = v->a[i];
  v->n = o;
}

/* ------------------------------------------------------------------------
 * Stable stores (sections 20, 35): records never move once published, so a
 * worker holding an identity reads its record without a lock.  Appends are
 * serialized by the store's mutex or by the lock of the table owning it.
 * ---------------------------------------------------------------------- */
#define CHB 12
#define CHN (1 << CHB)
#define MAXCH (1 << 15)
typedef struct { char *ch[MAXCH]; size_t esz; atomic_int n; pthread_mutex_t m; } Store;
#define STORE_INIT(T) { .esz = sizeof(T), .m = PTHREAD_MUTEX_INITIALIZER }
static void *sat(Store *s, int i) { return s->ch[i >> CHB] + (size_t)(i & (CHN - 1)) * s->esz; }
static int scount(Store *s) { return atomic_load_explicit(&s->n, memory_order_acquire); }
static int spushLocked(Store *s, const void *e) {
  int i = atomic_load_explicit(&s->n, memory_order_relaxed);
  if ((i >> CHB) >= MAXCH) die("store exhausted");
  if (!s->ch[i >> CHB]) s->ch[i >> CHB] = xalloc((size_t)CHN * s->esz);
  memcpy(sat(s, i), e, s->esz);
  atomic_store_explicit(&s->n, i + 1, memory_order_release);
  return i;
}
static int spush(Store *s, const void *e) { LOCK(&s->m); int i = spushLocked(s, e); UNLOCK(&s->m); return i; }
static void sfree(Store *s) { for (int k = 0; k < MAXCH && s->ch[k]; k++) { free(s->ch[k]); s->ch[k] = NULL; } atomic_store(&s->n, 0); }

/* Interning (section 2): equality of interned records is structural; a
 * hash match is confirmed by comparing the records. */
typedef struct { int *a; int n; } Rec;
typedef struct { Store items; int *h; int hcap; pthread_mutex_t m; } Tab;
#define TAB_INIT { .items = STORE_INIT(Rec), .m = PTHREAD_MUTEX_INITIALIZER }
static unsigned hashv(const int *v, int n) { unsigned h = 2166136261u; for (int i = 0; i < n; i++) { h ^= (unsigned)v[i]; h *= 16777619u; } return h ^ (unsigned)n; }
static const Rec *trec(Tab *t, int id) { return sat(&t->items, id); }
static int tabInternLocked(Tab *t, const int *v, int n, int *isnew) {
  int cnt = atomic_load_explicit(&t->items.n, memory_order_relaxed);
  if (cnt * 2 + 2 >= t->hcap) {
    int nc = t->hcap ? t->hcap * 2 : 1024; int *nh = xalloc(sizeof(int) * nc);
    for (int i = 0; i < nc; i++) nh[i] = -1;
    for (int i = 0; i < cnt; i++) { const Rec *e = trec(t, i); unsigned k = hashv(e->a, e->n) % nc; while (nh[k] >= 0) k = (k + 1) % nc; nh[k] = i; }
    free(t->h); t->h = nh; t->hcap = nc;
  }
  unsigned k = hashv(v, n) % t->hcap;
  while (t->h[k] >= 0) {
    const Rec *e = trec(t, t->h[k]);
    if (e->n == n && (n == 0 || !memcmp(e->a, v, sizeof(int) * n))) { if (isnew) *isnew = 0; return t->h[k]; }
    k = (k + 1) % t->hcap;
  }
  Rec r = { xalloc(sizeof(int) * (n + 1)), n }; if (n) memcpy(r.a, v, sizeof(int) * n);
  int id = spushLocked(&t->items, &r);
  t->h[k] = id; if (isnew) *isnew = 1;
  return id;
}
static int tabIntern(Tab *t, const int *v, int n) { LOCK(&t->m); int id = tabInternLocked(t, v, n, NULL); UNLOCK(&t->m); return id; }
static void tabFree(Tab *t) {
  int n = scount(&t->items); for (int i = 0; i < n; i++) free(((Rec *)sat(&t->items, i))->a);
  sfree(&t->items); free(t->h); t->h = NULL; t->hcap = 0;
}

/* A memo of a pure function of two identities (reindex): a missing entry is
 * computed outside the lock; two workers computing it obtain the same
 * canonical result. */
typedef struct { int a, b, r; } M3;
typedef struct { M3 *t; int cap, n; pthread_mutex_t m; } Memo;
#define MEMO_INIT { .m = PTHREAD_MUTEX_INITIALIZER }
static unsigned mh(int a, int b, int cap) { return ((unsigned)a * 2654435761u ^ (unsigned)b * 40503u) % (unsigned)cap; }
static int memoGet(Memo *mt, int a, int b) {
  int r = -1; LOCK(&mt->m);
  if (mt->cap) { unsigned k = mh(a, b, mt->cap); while (mt->t[k].a >= 0) { if (mt->t[k].a == a && mt->t[k].b == b) { r = mt->t[k].r; break; } k = (k + 1) % mt->cap; } }
  UNLOCK(&mt->m); return r;
}
static void memoPut(Memo *mt, int a, int b, int r) {
  LOCK(&mt->m);
  if (mt->n * 2 + 2 >= mt->cap) {
    M3 *old = mt->t; int oc = mt->cap; mt->cap = oc ? oc * 2 : 4096;
    mt->t = xalloc(sizeof(M3) * mt->cap); for (int i = 0; i < mt->cap; i++) mt->t[i].a = -1;
    for (int i = 0; i < oc; i++) if (old[i].a >= 0) { unsigned k = mh(old[i].a, old[i].b, mt->cap); while (mt->t[k].a >= 0) k = (k + 1) % mt->cap; mt->t[k] = old[i]; }
    free(old);
  }
  unsigned k = mh(a, b, mt->cap);
  while (mt->t[k].a >= 0) { if (mt->t[k].a == a && mt->t[k].b == b) { UNLOCK(&mt->m); return; } k = (k + 1) % mt->cap; }
  mt->t[k].a = a; mt->t[k].b = b; mt->t[k].r = r; mt->n++;
  UNLOCK(&mt->m);
}
static void memoFree(Memo *mt) { free(mt->t); mt->t = NULL; mt->cap = mt->n = 0; }

/* ------------------------------------------------------------------------
 * Variables (section 2): identities, with their provenance.  Printed names
 * are presentation data.  A generated identity's provenance is its owner,
 * slot and sort (sections 8, 34, 37).
 * ---------------------------------------------------------------------- */
enum { S_TERM, S_DIM, S_LEVEL };
enum { P_SOURCE, P_POSTULATE, P_BINDER, P_FORMAL, P_COMPARE };
typedef struct { int sort; char *name; int type, plain, prov, pa, pb, pc, pd; } Var;
static Store varsS = STORE_INIT(Var);
static Var *V(int x) { return sat(&varsS, x); }
static int newVar(int sort, const char *name, int type, int prov, int pa, int pb, int pc, int pd) {
  Var v = { sort, xdup(name), type, 0, prov, pa, pb, pc, pd };
  return spush(&varsS, &v);
}

/* ------------------------------------------------------------------------
 * Intervals (section 3): antichains of clauses of signed atoms, 2*i for i
 * and 2*i+1 for ~i; a clause with both i and ~i is retained.
 * Faces (section 4): antichains of clauses of endpoint literals, 2*i for
 * (i=0) and 2*i+1 for (i=1); a clause with both is discarded.
 * Encoded for interning as [nclauses, len, lits.., len, lits..].
 * ---------------------------------------------------------------------- */
typedef struct { IV *c; int n, cap; } Form;
static Tab itab = TAB_INIT, ftab = TAB_INIT;
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
static int contradictory(const IV *c) { for (int k = 0; k + 1 < c->n; k++) if ((c->a[k] >> 1) == (c->a[k + 1] >> 1)) return 1; return 0; }
/* normalize (sort, deduplicate, discard contradictions for faces, absorb)
 * and intern; consumes f */
static int formIntern(Form *f, int face) {
  for (int i = 0; i < f->n; i++) ivsortu(&f->c[i]);
  Form g = { 0 };
  for (int i = 0; i < f->n; i++) {
    IV *c = &f->c[i];
    if (face && contradictory(c)) continue;
    int drop = 0;
    for (int j = 0; j < f->n && !drop; j++) {
      if (j == i) continue;
      IV *d = &f->c[j];
      if (face && contradictory(d)) continue;
      if (subsetv(d, c) && (d->n < c->n || j < i)) drop = 1;
    }
    if (!drop) formAdd(&g, ivcopy(c));
  }
  if (g.n) qsort(g.c, g.n, sizeof(IV), clauseCmp);
  IV enc = { 0 }; ivp(&enc, g.n);
  for (int i = 0; i < g.n; i++) { ivp(&enc, g.c[i].n); for (int k = 0; k < g.c[i].n; k++) ivp(&enc, g.c[i].a[k]); }
  int id = tabIntern(face ? &ftab : &itab, enc.a, enc.n);
  free(enc.a); formFree(&g); formFree(f);
  return id;
}
static Form formGet(int id, int face) {
  const Rec *e = trec(face ? &ftab : &itab, id);
  Form f = { 0 }; int p = 1;
  for (int i = 0; i < e->a[0]; i++) { IV c = { 0 }; int len = e->a[p++]; for (int k = 0; k < len; k++) ivp(&c, e->a[p++]); formAdd(&f, c); }
  return f;
}
static int formClauses(int id, int face) { return trec(face ? &ftab : &itab, id)->a[0]; }
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
  if (a == F1) return b;
  if (b == F1) return a;
  Form f = { 0 }, x = formGet(a, 1), y = formGet(b, 1);
  for (int i = 0; i < x.n; i++) for (int j = 0; j < y.n; j++) {
    IV c = ivcopy(&x.c[i]); for (int k = 0; k < y.c[j].n; k++) ivp(&c, y.c[j].a[k]); formAdd(&f, c);
  }
  formFree(&x); formFree(&y); return formIntern(&f, 1);
}
static int forr(int a, int b) {
  if (a == F0) return b;
  if (b == F0) return a;
  Form f = { 0 }, x = formGet(a, 1), y = formGet(b, 1);
  for (int i = 0; i < x.n; i++) formAdd(&f, ivcopy(&x.c[i]));
  for (int i = 0; i < y.n; i++) formAdd(&f, ivcopy(&y.c[i]));
  formFree(&x); formFree(&y); return formIntern(&f, 1);
}
static int flit(int i, int eps) { Form f = { 0 }; IV c = { 0 }; ivp(&c, 2 * i + eps); formAdd(&f, c); return formIntern(&f, 1); }
/* (r=1) = OR_C AND_{a in C} (a=1);  (r=0) = AND_C OR_{a in C} (a=0);
 * (~i=eps) = (i=1-eps) */
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
  if (phi == F1 || chi == F0 || chi == phi) return 1;
  Form x = formGet(chi, 1), y = formGet(phi, 1); int ok = 1;
  for (int i = 0; i < x.n && ok; i++) { int f = 0; for (int j = 0; j < y.n && !f; j++) if (subsetv(&y.c[j], &x.c[i])) f = 1; if (!f) ok = 0; }
  formFree(&x); formFree(&y); return ok;
}
/* section 5: forall i keeps the clauses without a literal on i */
static int forallDim(int i, int phi) {
  Form x = formGet(phi, 1), r = { 0 };
  for (int k = 0; k < x.n; k++) { int m = 0; for (int l = 0; l < x.c[k].n; l++) if ((x.c[k].a[l] >> 1) == i) m = 1; if (!m) formAdd(&r, ivcopy(&x.c[k])); }
  formFree(&x); return formIntern(&r, 1);
}
/* section 5: projection deletes the literals outside S in each clause; the
 * input is already normalized (contradictions discarded) */
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
/* the clauses of a face, each as a face */
static int *faceClauses(int phi, int *n) {
  Form x = formGet(phi, 1); int *r = xalloc(sizeof(int) * (x.n + 1));
  for (int k = 0; k < x.n; k++) { Form one = { 0 }; formAdd(&one, ivcopy(&x.c[k])); r[k] = formIntern(&one, 1); }
  *n = x.n; formFree(&x); return r;
}

/* ------------------------------------------------------------------------
 * Universe levels (section 33): explicit predicative levels.  A level is
 * the max of a constant and terms (variable + offset); its normal form keeps
 * one offset per variable and the constant only when it exceeds every
 * offset (levels are naturals).  Equal levels have equal normal forms.
 * Encoded [n, var, off, ..] sorted by var; var -1 is the constant.
 * ---------------------------------------------------------------------- */
static Tab ltab = TAB_INIT;
typedef struct { int v, o; } LT;
static int ltcmp(const void *a, const void *b) { const LT *x = a, *y = b; return x->v < y->v ? -1 : x->v > y->v ? 1 : 0; }
static int levelMake(LT *t, int n) {
  LT *u = xalloc(sizeof(LT) * (n + 1)); int m = 0, maxoff = -1, cst = 0, hasvar = 0;
  for (int i = 0; i < n; i++) {
    if (t[i].v < 0) { if (t[i].o > cst) cst = t[i].o; continue; }
    int f = -1; for (int k = 0; k < m; k++) if (u[k].v == t[i].v) f = k;
    if (f < 0) u[m++] = t[i]; else if (t[i].o > u[f].o) u[f].o = t[i].o;
  }
  for (int k = 0; k < m; k++) { hasvar = 1; if (u[k].o > maxoff) maxoff = u[k].o; }
  if (!hasvar || cst > maxoff) { u[m].v = -1; u[m].o = cst; m++; }
  if (m) qsort(u, m, sizeof(LT), ltcmp);
  IV e = { 0 }; ivp(&e, m); for (int k = 0; k < m; k++) { ivp(&e, u[k].v); ivp(&e, u[k].o); }
  int id = tabIntern(&ltab, e.a, e.n); free(e.a); free(u); return id;
}
static int lconst(int k) { LT t = { -1, k }; return levelMake(&t, 1); }
static int lvar(int v) { LT t = { v, 0 }; return levelMake(&t, 1); }
static LT *levelTerms(int l, int *n) {
  const Rec *e = trec(&ltab, l); *n = e->a[0]; LT *t = xalloc(sizeof(LT) * (*n + 1));
  for (int i = 0; i < *n; i++) { t[i].v = e->a[1 + 2 * i]; t[i].o = e->a[2 + 2 * i]; }
  return t;
}
static int lshift(int l, int by) { int n; LT *t = levelTerms(l, &n); for (int i = 0; i < n; i++) t[i].o += by; int r = levelMake(t, n); free(t); return r; }
static int lsuc(int l) { return lshift(l, 1); }
static int lmax(int a, int b) {
  int na, nb; LT *x = levelTerms(a, &na), *y = levelTerms(b, &nb);
  LT *t = xalloc(sizeof(LT) * (na + nb + 1)); memcpy(t, x, sizeof(LT) * na); memcpy(t + na, y, sizeof(LT) * nb);
  int r = levelMake(t, na + nb); free(x); free(y); free(t); return r;
}
static void levelVars(int l, IV *out) { int n; LT *t = levelTerms(l, &n); for (int i = 0; i < n; i++) if (t[i].v >= 0) ivadd(out, t[i].v); free(t); }

/* ------------------------------------------------------------------------
 * Raw maps (section 6): sorted term, dimension and level images, with no
 * identity entries.  Encoding [nt, x, ref, .., nd, i, itv, .., nl, l, lev, ..].
 * ---------------------------------------------------------------------- */
static Tab mtab = TAB_INIT, rtab = TAB_INIT;
static int MID;
typedef struct { int k, v; } KV;
static int kvcmp(const void *a, const void *b) { return cmpint(&((const KV *)a)->k, &((const KV *)b)->k); }
static int refVar(int x);
static int mapMake(KV *t, int nt, KV *d, int nd, KV *l, int nl) {
  if (nt) qsort(t, nt, sizeof(KV), kvcmp);
  if (nd) qsort(d, nd, sizeof(KV), kvcmp);
  if (nl) qsort(l, nl, sizeof(KV), kvcmp);
  IV e = { 0 }; int c = 0;
  for (int i = 0; i < nt; i++) if (t[i].v != refVar(t[i].k)) c++;
  ivp(&e, c); for (int i = 0; i < nt; i++) if (t[i].v != refVar(t[i].k)) { ivp(&e, t[i].k); ivp(&e, t[i].v); }
  c = 0; for (int i = 0; i < nd; i++) if (d[i].v != ivar(d[i].k)) c++;
  ivp(&e, c); for (int i = 0; i < nd; i++) if (d[i].v != ivar(d[i].k)) { ivp(&e, d[i].k); ivp(&e, d[i].v); }
  c = 0; for (int i = 0; i < nl; i++) if (l[i].v != lvar(l[i].k)) c++;
  ivp(&e, c); for (int i = 0; i < nl; i++) if (l[i].v != lvar(l[i].k)) { ivp(&e, l[i].k); ivp(&e, l[i].v); }
  int id = tabIntern(&mtab, e.a, e.n); free(e.a); return id;
}
typedef struct { KV *t, *d, *l; int nt, nd, nl; } MapR;
static MapR mapRead(int m, int extra) {
  const Rec *e = trec(&mtab, m); int p = 0; MapR r;
  r.nt = e->a[p++]; r.t = xalloc(sizeof(KV) * (r.nt + extra + 1));
  for (int i = 0; i < r.nt; i++) { r.t[i].k = e->a[p++]; r.t[i].v = e->a[p++]; }
  r.nd = e->a[p++]; r.d = xalloc(sizeof(KV) * (r.nd + extra + 1));
  for (int i = 0; i < r.nd; i++) { r.d[i].k = e->a[p++]; r.d[i].v = e->a[p++]; }
  r.nl = e->a[p++]; r.l = xalloc(sizeof(KV) * (r.nl + extra + 1));
  for (int i = 0; i < r.nl; i++) { r.l[i].k = e->a[p++]; r.l[i].v = e->a[p++]; }
  return r;
}
static void mapRFree(MapR *r) { free(r->t); free(r->d); free(r->l); }
static int mapFromR(MapR *r) { int m = mapMake(r->t, r->nt, r->d, r->nd, r->l, r->nl); mapRFree(r); return m; }
static int termImage(int m, int x) {
  const Rec *e = trec(&mtab, m); int nt = e->a[0];
  for (int i = 0; i < nt; i++) if (e->a[1 + 2 * i] == x) return e->a[2 + 2 * i];
  return refVar(x);
}
static int dimImage(int m, int i) {
  const Rec *e = trec(&mtab, m); int p = 1 + 2 * e->a[0], nd = e->a[p++];
  for (int k = 0; k < nd; k++) if (e->a[p + 2 * k] == i) return e->a[p + 2 * k + 1];
  return ivar(i);
}
static int levelImage(int m, int v) {
  const Rec *e = trec(&mtab, m); int p = 1 + 2 * e->a[0]; p += 1 + 2 * e->a[p]; int nl = e->a[p++];
  for (int k = 0; k < nl; k++) if (e->a[p + 2 * k] == v) return e->a[p + 2 * k + 1];
  return lvar(v);
}
static int map1Dim(int i, int r) { KV d = { i, r }; return mapMake(NULL, 0, &d, 1, NULL, 0); }
static int map1Term(int x, int t) { KV k = { x, t }; return mapMake(&k, 1, NULL, 0, NULL, 0); }
/* the map fixing the endpoints of a clause (i=eps) |-> i := eps */
static int clauseMap(int C) {
  Form x = formGet(C, 1); if (x.n != 1) die("clauseMap: not a single clause");
  KV *d = xalloc(sizeof(KV) * (x.c[0].n + 1));
  for (int k = 0; k < x.c[0].n; k++) { d[k].k = x.c[0].a[k] >> 1; d[k].v = (x.c[0].a[k] & 1) ? I1 : I0; }
  int m = mapMake(NULL, 0, d, x.c[0].n, NULL, 0); free(d); formFree(&x); return m;
}

/* ------------------------------------------------------------------------
 * Origins (section 2) and the open table (section 9)
 * ---------------------------------------------------------------------- */
enum { UNIV, PI, SIGMA, LAM, APP, PAIR, FST, SND, PATH, PLAM, PAPP, GLUE_TYPE, GLUE_INTRO, UNGLUE, COMP, SYSTEM, GLOBAL, NTAG };
static const char *tagName[NTAG] = { "U", "Pi", "Sigma", "lam", "app", "pair", "fst", "snd", "PathP", "plam", "papp", "Glue", "glue", "unglue", "comp", "system", "global" };
enum { K_TERM, K_INTERVAL, K_FACE, K_LEVEL, K_TERM_BODY, K_DIM_BODY, K_PARTIAL, K_PARTIAL_DIM_BODY };
typedef struct { int kind, val, slot, guard; } Field;
typedef struct { int sort, formal, domain; } Binder;
/* req: the required face; ann: the typing annotation (a type reference) or
 * -1; fvt, fvd, fvl: the dependency-closed free term, dimension and level
 * boundary */
typedef struct { int tag, scal, req, ann, nb, nf; Binder *b; Field *f; IV fvt, fvd, fvl; } Origin;
static Tab otab = TAB_INIT;
static Store originsS = STORE_INIT(Origin);
static Origin *O_(int o) { return sat(&originsS, o); }

/* references: [0, x] is VAR(x); [1, origin, map] is VIEW(origin, map) */
static int refVar(int x) { int v[2] = { 0, x }; return tabIntern(&rtab, v, 2); }
static int isVar(int r) { return trec(&rtab, r)->a[0] == 0; }
static int refVarId(int r) { return trec(&rtab, r)->a[1]; }
static int refOrigin(int r) { return trec(&rtab, r)->a[1]; }
static int refMap(int r) { return trec(&rtab, r)->a[2]; }
static int refTag(int r) { return isVar(r) ? -1 : O_(refOrigin(r))->tag; }

/* Support (section 7): the free term, dimension and level identities of a
 * reference's instantiated typed boundary, and its required face; computed
 * from immutable records and memoized per reference. */
typedef struct { IV t, d, l; int req; } FV;
static Store fvS = STORE_INIT(FV);
static pthread_mutex_t fvM = PTHREAD_MUTEX_INITIALIZER;
static int *fvIdx; static int fvCap;
static int substFace(int phi, int m);
static const FV *fvOf(int ref);
static void addRefFV(int ref, IV *t, IV *d, IV *l) {
  const FV *f = fvOf(ref);
  for (int i = 0; i < f->t.n; i++) ivadd(t, f->t.a[i]);
  for (int i = 0; i < f->d.n; i++) ivadd(d, f->d.a[i]);
  for (int i = 0; i < f->l.n; i++) ivadd(l, f->l.a[i]);
}
static int reqOf(int ref) { return fvOf(ref)->req; }
static const FV *fvOf(int ref) {
  LOCK(&fvM); int ix = ref < fvCap ? fvIdx[ref] : 0; UNLOCK(&fvM);
  if (ix) return sat(&fvS, ix - 1);
  FV f; memset(&f, 0, sizeof f);
  if (isVar(ref)) {
    int x = refVarId(ref);
    if (V(x)->sort != S_TERM) die("a dimension or level identity used as a term");
    ivp(&f.t, x);
    if (V(x)->type >= 0) addRefFV(V(x)->type, &f.t, &f.d, &f.l);
    f.req = F1;
  } else {
    Origin *O = O_(refOrigin(ref)); int m = refMap(ref);
    for (int k = 0; k < O->fvt.n; k++) addRefFV(termImage(m, O->fvt.a[k]), &f.t, &f.d, &f.l);
    for (int k = 0; k < O->fvd.n; k++) formDims(dimImage(m, O->fvd.a[k]), 0, &f.d);
    for (int k = 0; k < O->fvl.n; k++) levelVars(levelImage(m, O->fvl.a[k]), &f.l);
    f.req = substFace(O->req, m);
  }
  ivsortu(&f.t); ivsortu(&f.d); ivsortu(&f.l);
  LOCK(&fvM);
  if (ref >= fvCap) { int nc = ref * 2 + 64; fvIdx = xgrow(fvIdx, sizeof(int) * nc); memset(fvIdx + fvCap, 0, sizeof(int) * (nc - fvCap)); fvCap = nc; }
  if (fvIdx[ref]) { int i = fvIdx[ref] - 1; UNLOCK(&fvM); ivfree(&f.t); ivfree(&f.d); ivfree(&f.l); return sat(&fvS, i); }
  int i = spushLocked(&fvS, &f); fvIdx[ref] = i + 1;
  UNLOCK(&fvM);
  return sat(&fvS, i);
}

/* Create (or find) an origin.  A GLOBAL origin's boundary is its declared
 * parameters.  Otherwise the boundary is collected from the fields, the
 * binder domains, the required face and the annotation, with each binder's
 * formal removed at its body, and closed under the types of free term
 * variables (section 2). */
static int mkOrigin(int tag, int scal, int req, int ann, int nb, Binder *b, int nf, Field *f, IV *gT, IV *gD, IV *gL) {
  IV t = { 0 }, d = { 0 }, l = { 0 };
  if (tag == GLOBAL) { t = ivcopy(gT); d = ivcopy(gD); l = ivcopy(gL); }
  else {
    for (int i = 0; i < nf; i++) {
      Field *g = &f[i]; IV ft = { 0 }, fd = { 0 }, fl = { 0 };
      switch (g->kind) {
      case K_TERM: addRefFV(g->val, &ft, &fd, &fl); break;
      case K_INTERVAL: formDims(g->val, 0, &fd); break;
      case K_FACE: formDims(g->val, 1, &fd); break;
      case K_LEVEL: levelVars(g->val, &fl); break;
      case K_PARTIAL: addRefFV(g->val, &ft, &fd, &fl); formDims(g->guard, 1, &fd); break;
      case K_TERM_BODY: case K_DIM_BODY: case K_PARTIAL_DIM_BODY: {
        Binder *bb = &b[g->slot];
        addRefFV(g->val, &ft, &fd, &fl);
        if (g->kind == K_PARTIAL_DIM_BODY) formDims(g->guard, 1, &fd);
        IV t2 = { 0 }, d2 = { 0 };
        for (int k = 0; k < ft.n; k++) if (!(bb->sort == S_TERM && ft.a[k] == bb->formal)) ivp(&t2, ft.a[k]);
        for (int k = 0; k < fd.n; k++) if (!(bb->sort == S_DIM && fd.a[k] == bb->formal)) ivp(&d2, fd.a[k]);
        ivfree(&ft); ivfree(&fd); ft = t2; fd = d2;
        if (bb->sort == S_TERM && bb->domain >= 0) addRefFV(bb->domain, &ft, &fd, &fl);
        break;
      }
      }
      for (int k = 0; k < ft.n; k++) ivadd(&t, ft.a[k]);
      for (int k = 0; k < fd.n; k++) ivadd(&d, fd.a[k]);
      for (int k = 0; k < fl.n; k++) ivadd(&l, fl.a[k]);
      ivfree(&ft); ivfree(&fd); ivfree(&fl);
    }
    formDims(req, 1, &d);
    if (ann >= 0) addRefFV(ann, &t, &d, &l);
    for (int k = 0; k < t.n; k++) { int ty = V(t.a[k])->type; if (ty >= 0) addRefFV(ty, &t, &d, &l); }
  }
  ivsortu(&t); ivsortu(&d); ivsortu(&l);
  IV e = { 0 };
  ivp(&e, tag); ivp(&e, scal); ivp(&e, req); ivp(&e, ann); ivp(&e, nb);
  for (int i = 0; i < nb; i++) { ivp(&e, b[i].sort); ivp(&e, b[i].formal); ivp(&e, b[i].domain); }
  ivp(&e, nf);
  for (int i = 0; i < nf; i++) { ivp(&e, f[i].kind); ivp(&e, f[i].val); ivp(&e, f[i].slot); ivp(&e, f[i].guard); }
  LOCK(&otab.m);
  int isnew, id = tabInternLocked(&otab, e.a, e.n, &isnew);
  if (isnew) {
    Origin o; memset(&o, 0, sizeof o);
    o.tag = tag; o.scal = scal; o.req = req; o.ann = ann; o.nb = nb; o.nf = nf;
    o.b = xalloc(sizeof(Binder) * (nb + 1)); if (nb) memcpy(o.b, b, sizeof(Binder) * nb);
    o.f = xalloc(sizeof(Field) * (nf + 1)); if (nf) memcpy(o.f, f, sizeof(Field) * nf);
    o.fvt = t; o.fvd = d; o.fvl = l;
    if (spushLocked(&originsS, &o) != id) die("origin table out of step");
  } else { ivfree(&t); ivfree(&d); ivfree(&l); }
  UNLOCK(&otab.m);
  free(e.a);
  return id;
}
/* section 6: restrict to the origin's typed boundary, drop identities, intern */
static int makeView(int o, int m) {
  Origin *O = O_(o); MapR r = mapRead(m, 0); int ot = 0, od = 0, ol = 0;
  for (int i = 0; i < r.nt; i++) if (ivhas(&O->fvt, r.t[i].k)) r.t[ot++] = r.t[i];
  for (int i = 0; i < r.nd; i++) if (ivhas(&O->fvd, r.d[i].k)) r.d[od++] = r.d[i];
  for (int i = 0; i < r.nl; i++) if (ivhas(&O->fvl, r.l[i].k)) r.l[ol++] = r.l[i];
  r.nt = ot; r.nd = od; r.nl = ol;
  int mm = mapFromR(&r);
  int v[3] = { 1, o, mm }; return tabIntern(&rtab, v, 3);
}

/* ------------------------------------------------------------------------
 * Substitution (sections 3, 4, 6): simultaneous, one lookup per variable.
 * ---------------------------------------------------------------------- */
static int substInterval(int r, int m) {
  if (m == MID) return r;
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
  if (m == MID) return phi;
  Form x = formGet(phi, 1); int res = F0;
  for (int i = 0; i < x.n; i++) {
    int c = F1;
    for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; c = fand(c, endpoint(dimImage(m, a >> 1), a & 1)); }
    res = forr(res, c);
  }
  formFree(&x); return res;
}
static int substLevel(int l, int m) {
  if (m == MID) return l;
  int n; LT *t = levelTerms(l, &n); int acc = lconst(0);
  for (int i = 0; i < n; i++) acc = lmax(acc, t[i].v < 0 ? lconst(t[i].o) : lshift(levelImage(m, t[i].v), t[i].o));
  free(t); return acc;
}
static Memo reidx = MEMO_INIT;
/* reindex (section 6): traverses the finite image records of the view, not
 * the body of its origin; no evaluation */
static int reindex(int ref, int m) {
  if (m == MID) return ref;
  if (isVar(ref)) return termImage(m, refVarId(ref));
  int got = memoGet(&reidx, ref, m); if (got >= 0) return got;
  int o = refOrigin(ref), tau = refMap(ref); Origin *O = O_(o);
  KV *t = xalloc(sizeof(KV) * (O->fvt.n + 1)), *d = xalloc(sizeof(KV) * (O->fvd.n + 1)), *l = xalloc(sizeof(KV) * (O->fvl.n + 1));
  for (int i = 0; i < O->fvt.n; i++) { int x = O->fvt.a[i]; t[i].k = x; t[i].v = reindex(termImage(tau, x), m); }
  for (int i = 0; i < O->fvd.n; i++) { int x = O->fvd.a[i]; d[i].k = x; d[i].v = substInterval(dimImage(tau, x), m); }
  for (int i = 0; i < O->fvl.n; i++) { int x = O->fvl.a[i]; l[i].k = x; l[i].v = substLevel(levelImage(tau, x), m); }
  int rho = mapMake(t, O->fvt.n, d, O->fvd.n, l, O->fvl.n); free(t); free(d); free(l);
  int res = makeView(o, rho);
  memoPut(&reidx, ref, m, res);
  return res;
}
/* sigma ; tau: apply sigma, then tau; keys present only in tau included */
static int composeMaps(int sigma, int tau) {
  MapR s = mapRead(sigma, 0), u = mapRead(tau, 0);
  IV tk = { 0 }, dk = { 0 }, lk = { 0 };
  for (int i = 0; i < s.nt; i++) ivadd(&tk, s.t[i].k);
  for (int i = 0; i < u.nt; i++) ivadd(&tk, u.t[i].k);
  for (int i = 0; i < s.nd; i++) ivadd(&dk, s.d[i].k);
  for (int i = 0; i < u.nd; i++) ivadd(&dk, u.d[i].k);
  for (int i = 0; i < s.nl; i++) ivadd(&lk, s.l[i].k);
  for (int i = 0; i < u.nl; i++) ivadd(&lk, u.l[i].k);
  KV *t = xalloc(sizeof(KV) * (tk.n + 1)), *d = xalloc(sizeof(KV) * (dk.n + 1)), *l = xalloc(sizeof(KV) * (lk.n + 1));
  for (int i = 0; i < tk.n; i++) { t[i].k = tk.a[i]; t[i].v = reindex(termImage(sigma, tk.a[i]), tau); }
  for (int i = 0; i < dk.n; i++) { d[i].k = dk.a[i]; d[i].v = substInterval(dimImage(sigma, dk.a[i]), tau); }
  for (int i = 0; i < lk.n; i++) { l[i].k = lk.a[i]; l[i].v = substLevel(levelImage(sigma, lk.a[i]), tau); }
  int r = mapMake(t, tk.n, d, dk.n, l, lk.n);
  free(t); free(d); free(l); ivfree(&tk); ivfree(&dk); ivfree(&lk); mapRFree(&s); mapRFree(&u);
  return r;
}

/* ------------------------------------------------------------------------
 * Binders (section 8): the instantiated identity is interned from (owner,
 * slot, sort); every field governed by the slot uses the same lift.
 * ---------------------------------------------------------------------- */
static Tab btab = TAB_INIT; static Store binstS = STORE_INIT(int);
static int instBinder(int owner, int slot, int sort, const char *name, int type) {
  int v[3] = { owner, slot, sort }, var;
  LOCK(&btab.m);
  int isnew, id = tabInternLocked(&btab, v, 3, &isnew);
  if (isnew) { var = newVar(sort, name, type, P_BINDER, owner, slot, sort, 0); if (spushLocked(&binstS, &var) != id) die("binder table out of step"); }
  else var = *(int *)sat(&binstS, id);
  UNLOCK(&btab.m);
  return var;
}
typedef struct { int var, domain, body, guard, lifted; } Resolved;
/* resolve the binder governing field fi of the owner (a VIEW) */
static Resolved resolve(int owner, int fi) {
  if (isVar(owner)) die("resolve: a variable has no binder");
  Origin *O = O_(refOrigin(owner)); int sigma = refMap(owner);
  Field fl = O->f[fi]; Binder bd = O->b[fl.slot];
  Resolved r; r.domain = -1; r.guard = -1;
  if (bd.sort == S_TERM) r.domain = reindex(bd.domain, sigma);
  r.var = instBinder(owner, fl.slot, bd.sort, V(bd.formal)->name, r.domain);
  MapR m = mapRead(sigma, 1); int ot = 0, od = 0;
  for (int i = 0; i < m.nt; i++) if (!(bd.sort == S_TERM && m.t[i].k == bd.formal)) m.t[ot++] = m.t[i];
  for (int i = 0; i < m.nd; i++) if (!(bd.sort == S_DIM && m.d[i].k == bd.formal)) m.d[od++] = m.d[i];
  if (bd.sort == S_TERM) { m.t[ot].k = bd.formal; m.t[ot].v = refVar(r.var); ot++; }
  else { m.d[od].k = bd.formal; m.d[od].v = ivar(r.var); od++; }
  m.nt = ot; m.nd = od;
  r.lifted = mapFromR(&m);
  r.body = reindex(fl.val, r.lifted);
  if (fl.kind == K_PARTIAL_DIM_BODY) r.guard = substFace(fl.guard, r.lifted);
  return r;
}
static int applyTerm(int owner, int fi, int arg) { Resolved r = resolve(owner, fi); return reindex(r.body, map1Term(r.var, arg)); }
static int applyDim(int owner, int fi, int itv) { Resolved r = resolve(owner, fi); return reindex(r.body, map1Dim(r.var, itv)); }

/* open (section 9): one constructor, its immediate fields specialized by
 * the owner's map; binder fields stay handles (resolved on demand) */
typedef struct { int kind, ref, itv, face, guard, lev; } OField;
typedef struct { int tag, owner, scal, nf; OField f[8]; int sysN; int *sysFace, *sysTerm; } Head;
static Head openRef(int ref) {
  Head h; memset(&h, 0, sizeof h); h.owner = ref; h.tag = -1;
  if (isVar(ref)) return h;
  Origin *O = O_(refOrigin(ref)); int s = refMap(ref);
  h.tag = O->tag; h.scal = O->scal; h.nf = O->nf;
  if (O->tag == SYSTEM) {
    h.sysN = O->nf / 2; h.sysFace = xalloc(sizeof(int) * (h.sysN + 1)); h.sysTerm = xalloc(sizeof(int) * (h.sysN + 1));
    for (int k = 0; k < h.sysN; k++) { h.sysFace[k] = substFace(O->f[2 * k].val, s); h.sysTerm[k] = reindex(O->f[2 * k + 1].val, s); }
    h.nf = 0; return h;
  }
  if (O->nf > 8) die("too many fields");
  for (int i = 0; i < O->nf; i++) {
    Field fl = O->f[i];
    h.f[i].kind = fl.kind;
    switch (fl.kind) {
    case K_TERM: h.f[i].ref = reindex(fl.val, s); break;
    case K_INTERVAL: h.f[i].itv = substInterval(fl.val, s); break;
    case K_FACE: h.f[i].face = substFace(fl.val, s); break;
    case K_LEVEL: h.f[i].lev = substLevel(fl.val, s); break;
    case K_PARTIAL: h.f[i].guard = substFace(fl.guard, s); h.f[i].ref = reindex(fl.val, s); break;
    default: break;
    }
  }
  return h;
}
static void headFree(Head *h) { free(h->sysFace); free(h->sysTerm); h->sysFace = h->sysTerm = NULL; }

/* ------------------------------------------------------------------------
 * Building cells.  A cell's required face is the meet of the required
 * faces of the subterms it uses totally (a dimension body's for every value
 * of its dimension), the annotation's, and any stated extra; a system
 * requires the join of its guards (section 12).  Partial fields are used
 * only under their guards.
 * ---------------------------------------------------------------------- */
static Field FT(int r) { Field f = { K_TERM, r, 0, -1 }; return f; }
static Field FI(int i) { Field f = { K_INTERVAL, i, 0, -1 }; return f; }
static Field FF(int i) { Field f = { K_FACE, i, 0, -1 }; return f; }
static Field FL(int l) { Field f = { K_LEVEL, l, 0, -1 }; return f; }
static Field FP(int r, int g) { Field f = { K_PARTIAL, r, 0, g }; return f; }
static Field FB(int kind, int r, int slot, int g) { Field f = { kind, r, slot, g }; return f; }
static int cellA(int tag, int ann, int extra, int nb, Binder *b, int nf, Field *f) {
  int req = extra;
  for (int i = 0; i < nf; i++) {
    switch (f[i].kind) {
    case K_TERM: case K_TERM_BODY: req = fand(req, reqOf(f[i].val)); break;
    case K_DIM_BODY: req = fand(req, forallDim(b[f[i].slot].formal, reqOf(f[i].val))); break;
    default: break;
    }
  }
  if (ann >= 0) req = fand(req, reqOf(ann));
  return makeView(mkOrigin(tag, 0, req, ann, nb, b, nf, f, NULL, NULL, NULL), MID);
}
static int cell(int tag, int nb, Binder *b, int nf, Field *f) { return cellA(tag, -1, F1, nb, b, nf, f); }
static int bUniv(int lev) { Field f[1] = { FL(lev) }; return cell(UNIV, 0, NULL, 1, f); }
static int bBind(int tag, int x, int A, int B) { Binder b = { S_TERM, x, A }; Field f[2] = { FT(A), FB(K_TERM_BODY, B, 0, -1) }; return cell(tag, 1, &b, 2, f); }
static int bLam(int x, int A, int body) { return bBind(LAM, x, A, body); }
static int bApp(int fn, int a) { Field f[2] = { FT(fn), FT(a) }; return cell(APP, 0, NULL, 2, f); }
static int bFst(int p) { Field f[1] = { FT(p) }; return cell(FST, 0, NULL, 1, f); }
static int bSnd(int p) { Field f[1] = { FT(p) }; return cell(SND, 0, NULL, 1, f); }
static int bPair(int a, int b) { Field f[2] = { FT(a), FT(b) }; return cell(PAIR, 0, NULL, 2, f); }
static int bPath(int i, int B, int l, int r) { Binder b = { S_DIM, i, -1 }; Field f[3] = { FB(K_DIM_BODY, B, 0, -1), FT(l), FT(r) }; return cell(PATH, 1, &b, 3, f); }
static int bPlam(int i, int body) { Binder b = { S_DIM, i, -1 }; Field f[1] = { FB(K_DIM_BODY, body, 0, -1) }; return cell(PLAM, 1, &b, 1, f); }
static int bPapp(int i, int B, int l, int r, int p, int s) {
  Binder b = { S_DIM, i, -1 }; Field f[5] = { FB(K_DIM_BODY, B, 0, -1), FT(l), FT(r), FT(p), FI(s) };
  return cell(PAPP, 1, &b, 5, f);
}
static int bComp(int i, int A, int phi, int u, int a0) {
  Binder b = { S_DIM, i, -1 };
  Field f[4] = { FB(K_DIM_BODY, A, 0, -1), FF(phi), FB(K_PARTIAL_DIM_BODY, u, 0, phi), FT(a0) };
  return cell(COMP, 1, &b, 4, f);
}
static int bSys(int n, const int *faces, const int *terms) {
  Field *f = xalloc(sizeof(Field) * (2 * n + 1)); int k = 0, cover = F0;
  for (int i = 0; i < n; i++) { if (faces[i] == F0) continue; f[k++] = FF(faces[i]); f[k++] = FP(terms[i], faces[i]); cover = forr(cover, faces[i]); }
  int r = cellA(SYSTEM, -1, cover, 0, NULL, k, f); free(f); return r;
}
static int bGlueType(int lev, int A, int phi, int T, int e) {
  Field f[5] = { FL(lev), FT(A), FF(phi), FP(T, phi), FP(e, phi) }; return cell(GLUE_TYPE, 0, NULL, 5, f);
}
static int bGlueIntro(int lev, int A, int phi, int T, int e, int t, int a) {
  Field f[7] = { FL(lev), FT(A), FF(phi), FP(T, phi), FP(e, phi), FP(t, phi), FT(a) }; return cell(GLUE_INTRO, 0, NULL, 7, f);
}
static int bUnglue(int lev, int A, int phi, int T, int e, int v) {
  Field f[6] = { FL(lev), FT(A), FF(phi), FP(T, phi), FP(e, phi), FT(v) }; return cell(UNGLUE, 0, NULL, 6, f);
}
/* the same construction with an annotation (section 2) */
static int annotateCell(int ref, int ann) {
  if (isVar(ref) || refMap(ref) != MID) return ref;
  Origin *O = O_(refOrigin(ref));
  if (O->tag == GLOBAL) return ref;
  int extra = O->tag == SYSTEM ? O->req : F1;
  return cellA(O->tag, ann, extra, O->nb, O->b, O->nf, O->f);
}

/* Global definitions (section 9): a GLOBAL origin per definition, its
 * boundary the declared parameters; a use is a view of it. */
typedef struct { char *name; IV params; int body, type, origin; } Def;
static Store defsS = STORE_INIT(Def);
static Def *DEF(int d) { return sat(&defsS, d); }
static int globalView(int d, const int *args) {
  Def *D = DEF(d); int np = D->params.n;
  KV *t = xalloc(sizeof(KV) * (np + 1)), *dd = xalloc(sizeof(KV) * (np + 1)), *ll = xalloc(sizeof(KV) * (np + 1)); int nt = 0, nd = 0, nl = 0;
  for (int i = 0; i < np; i++) {
    int x = D->params.a[i];
    if (V(x)->sort == S_TERM) { t[nt].k = x; t[nt].v = args[i]; nt++; }
    else if (V(x)->sort == S_DIM) { dd[nd].k = x; dd[nd].v = args[i]; nd++; }
    else { ll[nl].k = x; ll[nl].v = args[i]; nl++; }
  }
  int m = mapMake(t, nt, dd, nd, ll, nl); free(t); free(dd); free(ll);
  return makeView(D->origin, m);
}
static int findDef(const char *n) { int nd = scount(&defsS); for (int i = 0; i < nd; i++) if (!strcmp(DEF(i)->name, n)) return i; return -1; }
static int DEF_fib = -1, DEF_lineEquiv = -1, DEF_Equiv = -1;

/* ------------------------------------------------------------------------
 * Contexts, typed maps and occurrences (sections 2, 6).  A context: its
 * declarations (identities, in order) and its face assumption.  An
 * occurrence is a reference with the context it is used in; the context is
 * not part of the reference's identity.
 * ---------------------------------------------------------------------- */
static Tab ctab = TAB_INIT, tmtab = TAB_INIT;
static int ctxMake(const IV *decls, int face) {
  IV e = { 0 }; ivp(&e, face); for (int i = 0; i < decls->n; i++) ivp(&e, decls->a[i]);
  int id = tabIntern(&ctab, e.a, e.n); ivfree(&e); return id;
}
static int ctxFace(int ctx) { return trec(&ctab, ctx)->a[0]; }
static int ctxRestrict(int ctx, int phi) {
  IV d = { 0 }; const Rec *e = trec(&ctab, ctx);
  for (int i = 1; i < e->n; i++) ivp(&d, e->a[i]);
  int r = ctxMake(&d, fand(e->a[0], phi)); ivfree(&d); return r;
}
static int typedMap(int source, int target, int raw) { int v[3] = { source, target, raw }; return tabIntern(&tmtab, v, 3); }
static int tmSource(int tm) { return trec(&tmtab, tm)->a[0]; }
static int tmTarget(int tm) { return trec(&tmtab, tm)->a[1]; }
static int tmRaw(int tm) { return trec(&tmtab, tm)->a[2]; }
/* sigma|_phi : (Delta, phi[sigma]) -> (Gamma, phi), the same raw map */
static int restrictTypedMap(int tm, int phi) {
  return typedMap(ctxRestrict(tmSource(tm), substFace(phi, tmRaw(tm))), ctxRestrict(tmTarget(tm), phi), tmRaw(tm));
}
static int composeTyped(int s1, int s2) {               /* s1 : Delta -> Gamma, s2 : Theta -> Delta */
  if (tmSource(s1) != tmTarget(s2)) die("typed maps do not compose");
  return typedMap(tmSource(s2), tmTarget(s1), composeMaps(tmRaw(s1), tmRaw(s2)));
}

/* ------------------------------------------------------------------------
 * Composition clauses (sections 13-17).  j is the composition's
 * instantiated dimension, shared by family and tube.  Components are
 * references with j free; at(X, r) specializes them by reindexing, which
 * evaluates nothing.  Each shared intermediate (v, a, t) is built once, as a
 * line in a fresh dimension, and its endpoints are specializations of it.
 * The formal identities a clause introduces are keyed by the composition,
 * the family head it read and a slot, so the same clause on the same head
 * builds the same interned cells.
 * ---------------------------------------------------------------------- */
typedef struct { int j, owner, key, slot; } Cx;
static Tab formalTab = TAB_INIT; static Store formalS = STORE_INIT(int);
static int formal(Cx *cx, int sort, const char *n, int ty) {
  int v[4] = { cx->owner, cx->key, cx->slot++, sort }, var;
  LOCK(&formalTab.m);
  int isnew, id = tabInternLocked(&formalTab, v, 4, &isnew);
  if (isnew) { var = newVar(sort, n, ty, P_FORMAL, v[0], v[1], v[2], sort); if (spushLocked(&formalS, &var) != id) die("formal table out of step"); }
  else var = *(int *)sat(&formalS, id);
  UNLOCK(&formalTab.m);
  return var;
}
static int at(Cx *cx, int X, int r) { return reindex(X, map1Dim(cx->j, r)); }
static int atF(Cx *cx, int phi, int r) { return substFace(phi, map1Dim(cx->j, r)); }
/* fill^d X [phi -> U] a0 (r) = comp^n X(d := r/\n) [phi -> U(d := r/\n), (r=0) -> a0] a0 */
static int fill(Cx *cx, int d, int X, int phi, int U, int a0, int r) {
  int n = formal(cx, S_DIM, "n", -1), sm = map1Dim(d, imeet(r, ivar(n)));
  int z = endpoint(r, 0), faces[2], terms[2], k = 0;
  if (phi != F0) { faces[k] = phi; terms[k] = reindex(U, sm); k++; }
  if (z != F0) { faces[k] = z; terms[k] = a0; k++; }
  return bComp(n, reindex(X, sm), forr(phi, z), bSys(k, faces, terms), a0);
}

enum { C_REF, C_INTRO, C_NEUTRAL, C_SYSTEM, C_EMPTY };

/* c: the composition; hv, cls: the head of its family at j observed under
 * eta.  Returns the clause's result, or -1 for a neutral family (the
 * composition is retained with all its operands). */
static int compClause(int c, int eta, int hv, int cls) {
  Head hc = openRef(c);
  Resolved fam = resolve(c, 0), tube = resolve(c, 2);
  if (fam.var != tube.var) die("family and tube instantiated apart");
  int j = fam.var, phi = hc.f[1].face, a0 = hc.f[3].ref, uj = tube.body;
  headFree(&hc);
  if (cls == C_NEUTRAL) return -1;
  Head hA = openRef(hv);
  Cx cx = { j, c, hv, 0 };
  int res = -1;
  switch (hA.tag) {
  case PI: {                                         /* dependent function clause */
    int Dj = hA.f[0].ref; Resolved Cb = resolve(hv, 1);
    int D1 = at(&cx, Dj, I1);
    int x1 = formal(&cx, S_TERM, "x", D1);
    int Dneg = reindex(Dj, map1Dim(j, ineg(ivar(j))));
    int k = formal(&cx, S_DIM, "k", -1);
    int vk = fill(&cx, j, Dneg, F0, -1, refVar(x1), ineg(ivar(k)));     /* v(k) */
    int v0 = reindex(vk, map1Dim(k, I0));                               /* v(0) */
    KV tt = { Cb.var, vk }, dd = { j, ivar(k) };
    int famk = reindex(Cb.body, mapMake(&tt, 1, &dd, 1, NULL, 0));
    res = bLam(x1, D1, bComp(k, famk, phi, bApp(at(&cx, uj, ivar(k)), vk), bApp(a0, v0)));
    break;
  }
  case SIGMA: {                                      /* dependent pair clause */
    int Dj = hA.f[0].ref; Resolved Cb = resolve(hv, 1);
    int k = formal(&cx, S_DIM, "k", -1);
    int ak = fill(&cx, j, Dj, phi, bFst(uj), bFst(a0), ivar(k));       /* a(k) */
    int a1 = reindex(ak, map1Dim(k, I1));                               /* a(1) */
    KV tt = { Cb.var, ak }, dd = { j, ivar(k) };
    int famk = reindex(Cb.body, mapMake(&tt, 1, &dd, 1, NULL, 0));
    res = bPair(a1, bComp(k, famk, phi, bSnd(at(&cx, uj, ivar(k))), bSnd(a0)));
    break;
  }
  case PATH: {                                       /* dependent path clause */
    Resolved B = resolve(hv, 0);
    int lj = hA.f[1].ref, rj = hA.f[2].ref;
    int m = formal(&cx, S_DIM, "m", -1), k = formal(&cx, S_DIM, "k", -1);
    KV dk[2] = { { j, ivar(k) }, { B.var, ivar(m) } };
    int famk = reindex(B.body, mapMake(NULL, 0, dk, 2, NULL, 0));
    int Bk = at(&cx, B.body, ivar(k)), B0 = at(&cx, B.body, I0);
    int lk = at(&cx, lj, ivar(k)), rk = at(&cx, rj, ivar(k));
    int faces[3] = { phi, flit(m, 0), flit(m, 1) };
    int terms[3] = { bPapp(B.var, Bk, lk, rk, at(&cx, uj, ivar(k)), ivar(m)), lk, rk };
    int cap = bPapp(B.var, B0, at(&cx, lj, I0), at(&cx, rj, I0), a0, ivar(m));
    res = bPlam(m, bComp(k, famk, forr(phi, forr(faces[1], faces[2])), bSys(3, faces, terms), cap));
    break;
  }
  case UNIV: {                                       /* universe clause (section 17) */
    if (DEF_lineEquiv < 0) die("core: lineEquiv is not defined");
    int l = hA.f[0].lev, m = formal(&cx, S_DIM, "m", -1);
    int u1 = at(&cx, uj, I1), u0 = at(&cx, uj, I0);
    int args[4] = { l, u1, u0, bPlam(m, at(&cx, uj, ineg(ivar(m)))) };
    res = bGlueType(l, a0, phi, u1, globalView(DEF_lineEquiv, args));
    break;
  }
  case GLUE_TYPE: {                                  /* Glue clause (section 16) */
    if (DEF_fib < 0) die("core: fib is not defined");
    int l = hA.f[0].lev, Aj = hA.f[1].ref, al = hA.f[2].face, Tj = hA.f[3].ref, ej = hA.f[4].ref;
    int psi = phi, u0 = a0;
    int ug0 = bUnglue(l, at(&cx, Aj, I0), atF(&cx, al, I0), at(&cx, Tj, I0), at(&cx, ej, I0), u0);  /* a0 = unglue u0 */
    int Ugj = bUnglue(l, Aj, al, Tj, ej, uj);                                                   /* unglue u(j) on psi */
    int k = formal(&cx, S_DIM, "k", -1);
    int ak = fill(&cx, j, Aj, psi, Ugj, ug0, ivar(k));             /* a(k) */
    int a1 = reindex(ak, map1Dim(k, I1));                           /* a(1) */
    int delta = forallDim(j, al);
    int tk = fill(&cx, j, Tj, psi, uj, u0, ivar(k));               /* t(k), on delta */
    int t1 = reindex(tk, map1Dim(k, I1));                           /* t'(1) */
    /* omega(m) = comp^k A(k) [psi -> a(k), (m=0) -> f_k(t(k)), (m=1) -> a(k)] a0 */
    int m = formal(&cx, S_DIM, "m", -1);
    int fk = bApp(bFst(at(&cx, ej, ivar(k))), tk);
    int of[3] = { psi, flit(m, 0), flit(m, 1) }, ot[3] = { ak, fk, ak };
    int omega = bPlam(m, bComp(k, at(&cx, Aj, ivar(k)), forr(psi, forr(of[1], of[2])), bSys(3, of, ot), ug0));
    /* the partial fibre element [delta -> (t'(1), omega), psi -> (u(1), refl a(1))] */
    int r = formal(&cx, S_DIM, "r", -1);
    int wf[2] = { delta, psi }, wt[2] = { bPair(t1, omega), bPair(at(&cx, uj, I1), bPlam(r, a1)) };
    int w = bSys(2, wf, wt);
    /* its extension in fib(f1, a1) under alpha(1), by the contraction of e(1) (section 15) */
    int A1 = at(&cx, Aj, I1), al1 = atF(&cx, al, I1), T1 = at(&cx, Tj, I1), e1 = at(&cx, ej, I1);
    int f1 = bFst(e1);
    int fargs[5] = { l, T1, A1, f1, a1 };
    int X = globalView(DEF_fib, fargs);
    int contr = bApp(bSnd(e1), a1), cen = bFst(contr), kw = bApp(bSnd(contr), w);
    int theta = forr(delta, psi), n = formal(&cx, S_DIM, "n", -1), q = formal(&cx, S_DIM, "q", -1);
    int ext = bComp(n, X, theta, bPapp(q, X, cen, w, kw, ivar(n)), cen);
    int tt1 = bFst(ext), p = bSnd(ext);
    /* a'(1) = hcomp^n A(1) [alpha(1) -> p(~n), psi -> a(1)] a(1) */
    int n2 = formal(&cx, S_DIM, "n", -1), q2 = formal(&cx, S_DIM, "q", -1);
    int hf[2] = { al1, psi }, ht[2] = { bPapp(q2, A1, bApp(f1, tt1), a1, p, ineg(ivar(n2))), a1 };
    int a1p = bComp(n2, A1, forr(al1, psi), bSys(2, hf, ht), a1);
    res = bGlueIntro(l, A1, al1, T1, e1, tt1, a1p);
    break;
  }
  case SYSTEM: {                                     /* a system of type families (section 12) */
    int n = hA.sysN, *g = xalloc(sizeof(int) * (n + 1)), *t = xalloc(sizeof(int) * (n + 1)), cover = F0;
    for (int k = 0; k < n; k++) {
      g[k] = forallDim(j, hA.sysFace[k]);
      t[k] = bComp(j, hA.sysTerm[k], phi, uj, a0);
      cover = forr(cover, g[k]);
    }
    if (!entails(eta, cover)) die("a type-family system does not cover its composition line");
    res = bSys(n, g, t);
    free(g); free(t);
    break;
  }
  default: die("a composition family whose head is %s is not a type", hA.tag >= 0 ? tagName[hA.tag] : "a variable");
  }
  headFree(&hA);
  return res;
}

/* ------------------------------------------------------------------------
 * The machine's agents (section 19) and the event protocol (section 26).
 *
 * Data descriptors: REF, HEAD_RECIPE, FACE, INTERVAL, MAP, typed MAP,
 * LEVEL, PARTIAL, TERM_BINDER, DIM_BINDER, PARTIAL_DIM_BINDER, DIMSET, and
 * the coverage statuses.  An evaluation result is a REF descriptor carrying
 * its classification (introduction, neutral, system, or the empty face).
 * An operation agent has its principal input, a result endpoint and
 * immutable parameters; one meeting a descriptor is an active pair.
 *
 * Counted events: REQUEST (EVAL meeting REF, whatever its entry's state),
 * EVALUATE (the one evaluator task of a key), PUBLISH, DELIVER (both when
 * the entry was ready and when the requester waited), JOIN (a clause
 * result filling its slot), RULE (every other active pair).
 * ---------------------------------------------------------------------- */
enum { D_REF, D_HEAD, D_FACE, D_INTERVAL, D_MAP, D_TMAP, D_LEVEL, D_PARTIAL, D_TBIND, D_DBIND, D_PDBIND, D_DIMSET, D_COVERED, D_NOT_COVERED };
typedef struct { int kind, a, b, cls; } Data;
static Data DR(int ref, int cls) { Data d = { D_REF, ref, 0, cls }; return d; }
static Data DK(int kind, int a, int b) { Data d = { kind, a, b, C_REF }; return d; }
enum { E_REQUEST, E_EVALUATE, E_PUBLISH, E_DELIVER, E_RULE, E_JOIN, NEV };
static const char *evName[NEV] = { "request", "evaluate", "publish", "deliver", "rule", "join" };
static atomic_long evc[NEV];
static void ev(int k) { atomic_fetch_add_explicit(&evc[k], 1, memory_order_relaxed); }

enum { OP_ROOT, OP_EVAL, OP_EVALUATE, OP_PUBLISH, OP_JOIN, OP_INSPECT,
       OP_REINDEX_TERM, OP_REINDEX_INTERVAL, OP_REINDEX_FACE, OP_REINDEX_LEVEL, OP_COMPOSE_MAP, OP_RESTRICT_MAP, OP_LIFT,
       OP_OPEN, OP_UNFOLD, OP_REINDEX_TBIND, OP_REINDEX_DBIND, OP_REINDEX_PDBIND, OP_REINDEX_PARTIAL,
       OP_APPLY_TERM, OP_APPLY_DIM, OP_APPLY_PDIM, OP_FORALL, OP_PROJECT_FACE, OP_FACE_COVERAGE, OP_USE_PARTIAL,
       OP_GET_SUPPORT, OP_REINDEX_HEAD, OP_DUP, OP_ERA,
       OP_KAPP, OP_KFST, OP_KSND, OP_KPEND0, OP_KPEND1, OP_KPAPP, OP_KGLUE, OP_KUNGLUE0, OP_KUNGLUE, OP_KSYS, OP_KCOMP0, OP_KCOMP };
typedef struct { int kind, p[4], outA, outI, n, got; Data *ins; int *faces; Data rootv; int rootset; } Op;
static Store opsS = STORE_INIT(Op);
static Op *OPP(int i) { return sat(&opsS, i); }
static int newOp(int kind, int outA, int outI, int p0, int p1, int p2, int p3) {
  Op o; memset(&o, 0, sizeof o); o.kind = kind; o.outA = outA; o.outI = outI;
  o.p[0] = p0; o.p[1] = p1; o.p[2] = p2; o.p[3] = p3;
  return spush(&opsS, &o);
}
#define NJOINLK 64
static pthread_mutex_t joinLk[NJOINLK];
static Tab dstab = TAB_INIT;                         /* dimension sets */

/* The evaluation cache (sections 10, 26): one entry per (reference,
 * projected face), U / R(waiters) / D(result). */
enum { UNEVALUATED, RUNNING, READY };
typedef struct { int ref, face, state; Data res; int *wo, *wi, nw, capw; pthread_mutex_t m; } Entry;
typedef struct { Store es; int *h; int hcap; pthread_mutex_t m; atomic_int running; } Cache;
static Cache *newCache(void) {
  Cache *c = xalloc(sizeof *c); c->es.esz = sizeof(Entry);
  pthread_mutex_init(&c->es.m, NULL); pthread_mutex_init(&c->m, NULL); atomic_init(&c->running, 0);
  return c;
}
static Entry *EN(Cache *c, int i) { return sat(&c->es, i); }
static unsigned ekey(int ref, int face, int cap) { return ((unsigned)ref * 2654435761u ^ (unsigned)face * 40503u) % (unsigned)cap; }
static int entryGet(Cache *c, int ref, int face) {
  LOCK(&c->m);
  int n = scount(&c->es);
  if (n * 2 + 2 >= c->hcap) {
    int nc = c->hcap ? c->hcap * 2 : 4096; int *nh = xalloc(sizeof(int) * nc);
    for (int i = 0; i < nc; i++) nh[i] = -1;
    for (int i = 0; i < n; i++) { Entry *e = EN(c, i); unsigned k = ekey(e->ref, e->face, nc); while (nh[k] >= 0) k = (k + 1) % nc; nh[k] = i; }
    free(c->h); c->h = nh; c->hcap = nc;
  }
  unsigned k = ekey(ref, face, c->hcap);
  while (c->h[k] >= 0) { Entry *e = EN(c, c->h[k]); if (e->ref == ref && e->face == face) { int i = c->h[k]; UNLOCK(&c->m); return i; } k = (k + 1) % c->hcap; }
  Entry z; memset(&z, 0, sizeof z);
  int i = spushLocked(&c->es, &z); Entry *e = EN(c, i);
  e->ref = ref; e->face = face; e->state = UNEVALUATED; pthread_mutex_init(&e->m, NULL);
  c->h[k] = i;
  UNLOCK(&c->m);
  return i;
}
static int entryFind(Cache *c, int ref, int face) {       /* -1 when the key was never requested */
  int r = -1; LOCK(&c->m);
  if (c->hcap) { unsigned k = ekey(ref, face, c->hcap); while (c->h[k] >= 0) { Entry *e = EN(c, c->h[k]); if (e->ref == ref && e->face == face) { r = c->h[k]; break; } k = (k + 1) % c->hcap; } }
  UNLOCK(&c->m); return r;
}
static void addWaiter(Entry *en, int op, int idx) {
  if (en->nw == en->capw) { en->capw = en->capw ? 2 * en->capw : 4; en->wo = xgrow(en->wo, sizeof(int) * en->capw); en->wi = xgrow(en->wi, sizeof(int) * en->capw); }
  en->wo[en->nw] = op; en->wi[en->nw] = idx; en->nw++;
}
/* teardown of an abandoned (stuck) workload: its suspended waiters are
 * released and its running keys return to unevaluated; nothing was
 * published for them (section 36) */
static void cacheAbandonRunning(Cache *c) {
  int n = scount(&c->es);
  for (int i = 0; i < n; i++) {
    Entry *e = EN(c, i);
    if (e->state == RUNNING) { free(e->wo); free(e->wi); e->wo = e->wi = NULL; e->nw = e->capw = 0; e->state = UNEVALUATED; }
  }
  atomic_store(&c->running, 0);
}
static void cacheFree(Cache *c) {
  int n = scount(&c->es);
  for (int i = 0; i < n; i++) { Entry *e = EN(c, i); free(e->wo); free(e->wi); pthread_mutex_destroy(&e->m); }
  sfree(&c->es); free(c->h); pthread_mutex_destroy(&c->m); pthread_mutex_destroy(&c->es.m); free(c);
}
static Cache *CUR;                                   /* the cache of the current workload */

/* ------------------------------------------------------------------------
 * The worker pool (section 35).  outstanding = queued + executing jobs; a
 * job enqueues its children before it finishes; outstanding == 0 is
 * quiescence of the closed workload.
 * ---------------------------------------------------------------------- */
enum { J_PAIR, J_DELIVER };
typedef struct { int kind, op, idx; Data d; } Job;
enum { POL_LIFO, POL_FIFO, POL_RANDOM, POL_MIXED };
static int NWORKERS = 1, POLICY = POL_LIFO;
static unsigned long long rngState = 88172645463325252ull;
static Job *jq; static int jhead, jcount, jcap;
static pthread_mutex_t qM = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t qWork = PTHREAD_COND_INITIALIZER, qIdle = PTHREAD_COND_INITIALIZER;
static long outstanding; static int stopping; static pthread_t *workers;
static unsigned long long rnd(void) { rngState ^= rngState << 13; rngState ^= rngState >> 7; rngState ^= rngState << 17; return rngState; }
static void enqueue(Job j) {
  LOCK(&qM);
  if (jcount == jcap) {
    int nc = jcap ? 2 * jcap : 1024; Job *n = xalloc(sizeof(Job) * nc);
    for (int i = 0; i < jcount; i++) n[i] = jq[(jhead + i) % jcap];
    free(jq); jq = n; jhead = 0; jcap = nc;
  }
  jq[(jhead + jcount) % jcap] = j; jcount++; outstanding++;
  pthread_cond_signal(&qWork);
  UNLOCK(&qM);
}
static Job takeLocked(void) {
  int pol = POLICY;
  if (pol == POL_MIXED) pol = (rnd() & 1) ? POL_LIFO : POL_FIFO;
  int pos = pol == POL_FIFO ? 0 : pol == POL_LIFO ? jcount - 1 : (int)(rnd() % (unsigned long long)jcount);
  Job j = jq[(jhead + pos) % jcap];
  if (pos == 0) jhead = (jhead + 1) % jcap;
  else jq[(jhead + pos) % jcap] = jq[(jhead + jcount - 1) % jcap];
  jcount--;
  return j;
}
static void runJob(Job j);
static void *workerMain(void *arg) {
  (void)arg;
  for (;;) {
    LOCK(&qM);
    while (!jcount && !stopping) pthread_cond_wait(&qWork, &qM);
    if (!jcount) { UNLOCK(&qM); return NULL; }
    Job j = takeLocked();
    UNLOCK(&qM);
    runJob(j);
    LOCK(&qM);
    if (--outstanding == 0) pthread_cond_broadcast(&qIdle);
    UNLOCK(&qM);
  }
}
static void waitQuiescent(void) { LOCK(&qM); while (outstanding) pthread_cond_wait(&qIdle, &qM); UNLOCK(&qM); }
static void startWorkers(void) {
  workers = xalloc(sizeof(pthread_t) * NWORKERS);
  for (int i = 0; i < NWORKERS; i++) if (pthread_create(&workers[i], NULL, workerMain, NULL)) die("cannot start a worker");
}
static void stopWorkers(void) {
  LOCK(&qM); stopping = 1; pthread_cond_broadcast(&qWork); UNLOCK(&qM);
  for (int i = 0; i < NWORKERS; i++) pthread_join(workers[i], NULL);
  free(workers); workers = NULL; free(jq); jq = NULL; jcap = jcount = 0;
}

static void connect(Data d, int op, int idx) { Job j = { J_PAIR, op, idx, d }; enqueue(j); }
static void deliverTo(Data d, int op, int idx) { Job j = { J_DELIVER, op, idx, d }; enqueue(j); }
static void to(Data d, int kind, int oA, int oI, int p0, int p1, int p2, int p3) { connect(d, newOp(kind, oA, oI, p0, p1, p2, p3), 0); }
static void evalTo(int ref, int eta, int oA, int oI) { to(DR(ref, C_REF), OP_EVAL, oA, oI, eta, 0, 0, 0); }
static void evalOpenTo(int ref, int eta, int k) { evalTo(ref, eta, newOp(OP_OPEN, k, 0, 0, 0, 0, 0), 0); }

/* an eliminator of a system that no branch alone covers acts branchwise,
 * with the same other operands (section 12) */
static int distribute(int sys, int orig) {
  Head sy = openRef(sys), ho = openRef(orig); int *ts = xalloc(sizeof(int) * (sy.sysN + 1));
  Resolved B; memset(&B, 0, sizeof B);
  if (ho.tag == PAPP) B = resolve(orig, 0);
  for (int k = 0; k < sy.sysN; k++) {
    int t = sy.sysTerm[k];
    switch (ho.tag) {
    case APP: ts[k] = bApp(t, ho.f[1].ref); break;
    case FST: ts[k] = bFst(t); break;
    case SND: ts[k] = bSnd(t); break;
    case PAPP: ts[k] = bPapp(B.var, B.body, ho.f[1].ref, ho.f[2].ref, t, ho.f[4].itv); break;
    case UNGLUE: ts[k] = bUnglue(ho.f[0].lev, ho.f[1].ref, ho.f[2].face, ho.f[3].ref, ho.f[4].ref, t); break;
    default: die("distribute: not an eliminator");
    }
  }
  int r = bSys(sy.sysN, sy.sysFace, ts); free(ts); headFree(&sy); headFree(&ho); return r;
}
static int dimsetOf(const IV *d) { IV s = ivcopy(d); ivsortu(&s); int id = tabIntern(&dstab, s.a, s.n); ivfree(&s); return id; }
static IV dimsetGet(int id) { const Rec *r = trec(&dstab, id); IV s = { 0 }; for (int i = 0; i < r->n; i++) ivp(&s, r->a[i]); return s; }

static void fire(int opi, int idx, Data d) {
  /* the agent's immutable parameters (a join's slots are read under its lock) */
  struct { int kind, p[4]; } o; Op *op = OPP(opi);
  o.kind = op->kind; memcpy(o.p, op->p, sizeof o.p);
  int oA = op->outA, oI = op->outI, eta = o.p[0];
  if (o.kind != OP_EVAL) ev(o.kind == OP_PUBLISH ? E_PUBLISH : o.kind == OP_JOIN ? E_JOIN : o.kind == OP_EVALUATE ? E_EVALUATE : E_RULE);
  /* an empty-face result passes through a continuation unopened */
  if (d.cls == C_EMPTY && (o.kind >= OP_KAPP || o.kind == OP_OPEN)) { connect(d, oA, oI); return; }
  switch (o.kind) {
  case OP_ROOT: { Op *r = OPP(opi); r->rootv = d; r->rootset = 1; return; }
  case OP_EVAL: {
    int chi = eta, ref = d.a;
    if (!entails(chi, reqOf(ref))) die("invalid occurrence: the ambient face does not entail the required face");
    if (chi == F0) { ev(E_REQUEST); Data e = DR(ref, C_EMPTY); deliverTo(e, oA, oI); return; }
    int e2 = projectFace(chi, &fvOf(ref)->d);
    if (formClauses(e2, 1) > 1) {                  /* a disjunctive face: one request per clause */
      ev(E_RULE);
      int n, *cl = faceClauses(e2, &n);
      int jn = newOp(OP_JOIN, oA, oI, 0, 0, 0, 0); Op *J = OPP(jn);
      J->n = n; J->ins = xalloc(sizeof(Data) * n); J->faces = cl;
      for (int k = 0; k < n; k++) evalTo(ref, cl[k], jn, k);
      return;
    }
    ev(E_REQUEST);
    Cache *c = CUR; int ei = entryGet(c, ref, e2); Entry *en = EN(c, ei);
    LOCK(&en->m);
    if (en->state == READY) { Data v = en->res; UNLOCK(&en->m); deliverTo(v, oA, oI); return; }
    addWaiter(en, oA, oI);
    if (en->state == RUNNING) { UNLOCK(&en->m); return; }
    en->state = RUNNING; atomic_fetch_add(&c->running, 1);
    UNLOCK(&en->m);
    int pub = newOp(OP_PUBLISH, -1, -1, 0, ei, 0, 0);
    to(DR(ref, C_REF), OP_EVALUATE, newOp(OP_INSPECT, pub, 0, e2, 0, 0, 0), 0, 0, 0, 0, 0);
    return;
  }
  case OP_EVALUATE: connect(DK(D_HEAD, d.a, 0), oA, oI); return;   /* the evaluator task opens its reference */
  case OP_PUBLISH: {
    Cache *c = CUR; Entry *en = EN(c, o.p[1]);
    LOCK(&en->m);
    if (en->state != RUNNING) die("publication to an entry that is not running");
    en->res = d; en->state = READY;
    int nw = en->nw, *wo = en->wo, *wi = en->wi;
    en->wo = en->wi = NULL; en->nw = en->capw = 0;
    atomic_fetch_sub(&c->running, 1);
    UNLOCK(&en->m);
    for (int k = 0; k < nw; k++) deliverTo(d, wo[k], wi[k]);
    free(wo); free(wi);
    return;
  }
  case OP_JOIN: {
    pthread_mutex_t *lk = &joinLk[opi % NJOINLK];
    LOCK(lk); Op *J = OPP(opi); J->ins[idx] = d; int full = ++J->got == J->n; UNLOCK(lk);
    if (!full) return;
    int same = 1;
    for (int k = 1; k < J->n; k++) if (J->ins[k].a != J->ins[0].a || J->ins[k].cls != J->ins[0].cls) same = 0;
    if (same) { connect(J->ins[0], oA, oI); return; }
    int *rs = xalloc(sizeof(int) * J->n);
    for (int k = 0; k < J->n; k++) rs[k] = J->ins[k].a;
    int sy = bSys(J->n, J->faces, rs); free(rs);
    connect(DR(sy, C_SYSTEM), oA, oI);
    return;
  }
  /* --- the scope agents (section 19) --- */
  case OP_REINDEX_TERM: connect(DK(D_REF, reindex(d.a, o.p[1]), 0), oA, oI); return;
  case OP_REINDEX_INTERVAL: connect(DK(D_INTERVAL, substInterval(d.a, o.p[1]), 0), oA, oI); return;
  case OP_REINDEX_FACE: connect(DK(D_FACE, substFace(d.a, o.p[1]), 0), oA, oI); return;
  case OP_REINDEX_LEVEL: connect(DK(D_LEVEL, substLevel(d.a, o.p[1]), 0), oA, oI); return;
  case OP_COMPOSE_MAP: connect(DK(D_MAP, composeMaps(o.p[1], d.a), 0), oA, oI); return;
  case OP_RESTRICT_MAP: connect(DK(D_TMAP, restrictTypedMap(d.a, o.p[1]), 0), oA, oI); return;
  case OP_LIFT:
    if (d.a != refMap(o.p[1])) die("a lift with a map that is not its owner's");
    connect(DK(D_MAP, resolve(o.p[1], o.p[2]).lifted, 0), oA, oI); return;
  case OP_OPEN: { Data h = DK(D_HEAD, d.a, 0); h.cls = d.cls; connect(h, oA, oI); return; }
  case OP_UNFOLD: {
    if (refTag(d.a) != GLOBAL) die("UNFOLD_GLOBAL meets a reference that is not global");
    int body = DEF(O_(refOrigin(d.a))->scal)->body;
    if (body < 0) die("a definition unfolded before its body was elaborated");
    connect(DK(D_REF, reindex(body, refMap(d.a)), 0), oA, oI); return;
  }
  case OP_REINDEX_TBIND: case OP_REINDEX_DBIND: case OP_REINDEX_PDBIND:
    connect(DK(d.kind, reindex(d.a, o.p[1]), d.b), oA, oI); return;
  case OP_REINDEX_PARTIAL: connect(DK(D_PARTIAL, substFace(d.a, o.p[1]), reindex(d.b, o.p[1])), oA, oI); return;
  case OP_APPLY_TERM: connect(DK(D_REF, applyTerm(d.a, d.b, o.p[1]), 0), oA, oI); return;
  case OP_APPLY_DIM: connect(DK(D_REF, applyDim(d.a, d.b, o.p[1]), 0), oA, oI); return;
  case OP_APPLY_PDIM: {
    Resolved r = resolve(d.a, d.b); int m = map1Dim(r.var, o.p[1]);
    connect(DK(D_PARTIAL, substFace(r.guard, m), reindex(r.body, m)), oA, oI); return;
  }
  case OP_FORALL: connect(DK(D_FACE, forallDim(o.p[1], d.a), 0), oA, oI); return;
  case OP_PROJECT_FACE: { IV s = dimsetGet(o.p[1]); int f = projectFace(d.a, &s); ivfree(&s); connect(DK(D_FACE, f, 0), oA, oI); return; }
  case OP_FACE_COVERAGE: connect(DK(entails(eta, d.a) ? D_COVERED : D_NOT_COVERED, 0, 0), oA, oI); return;
  case OP_USE_PARTIAL:
    if (entails(eta, d.a)) connect(DK(D_REF, d.b, 0), oA, oI); else connect(DK(D_NOT_COVERED, d.a, d.b), oA, oI);
    return;
  case OP_GET_SUPPORT: connect(DK(D_DIMSET, dimsetOf(&fvOf(d.a)->d), 0), oA, oI); return;
  case OP_REINDEX_HEAD: connect(DK(D_HEAD, reindex(d.a, o.p[1]), 0), oA, oI); return;
  case OP_DUP: connect(d, oA, oI); connect(d, o.p[1], o.p[2]); return;
  case OP_ERA: return;
  /* --- the evaluator task: inspection of the opened constructor (section 12) --- */
  case OP_INSPECT: {
    int ref = d.a;
    if (isVar(ref)) { connect(DR(ref, C_NEUTRAL), oA, oI); return; }
    Head h = openRef(ref);
    switch (h.tag) {
    case UNIV: case PI: case SIGMA: case LAM: case PAIR: case PATH: case PLAM: connect(DR(ref, C_INTRO), oA, oI); break;
    case GLOBAL: to(DR(ref, C_REF), OP_UNFOLD, newOp(OP_EVAL, oA, oI, eta, 0, 0, 0), 0, eta, 0, 0, 0); break;
    case APP: evalOpenTo(h.f[0].ref, eta, newOp(OP_KAPP, oA, oI, eta, ref, h.f[1].ref, 0)); break;
    case FST: case SND: evalOpenTo(h.f[0].ref, eta, newOp(h.tag == FST ? OP_KFST : OP_KSND, oA, oI, eta, ref, 0, 0)); break;
    case PAPP: to(DK(D_FACE, endpoint(h.f[4].itv, 0), 0), OP_FACE_COVERAGE, newOp(OP_KPEND0, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); break;
    case GLUE_TYPE: to(DK(D_PARTIAL, h.f[3].guard, h.f[3].ref), OP_USE_PARTIAL, newOp(OP_KGLUE, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); break;
    case GLUE_INTRO: to(DK(D_PARTIAL, h.f[5].guard, h.f[5].ref), OP_USE_PARTIAL, newOp(OP_KGLUE, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); break;
    case UNGLUE: to(DK(D_PARTIAL, h.f[4].guard, h.f[4].ref), OP_USE_PARTIAL, newOp(OP_KUNGLUE0, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0); break;
    case SYSTEM:
      if (h.sysN == 0) die("an empty system observed under a consistent face");
      to(DK(D_PARTIAL, h.sysFace[0], h.sysTerm[0]), OP_USE_PARTIAL, newOp(OP_KSYS, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0);
      break;
    case COMP: {                                     /* the tube first */
      int use = newOp(OP_USE_PARTIAL, newOp(OP_KCOMP0, oA, oI, eta, ref, 0, 0), 0, eta, 0, 0, 0);
      to(DK(D_PDBIND, ref, 2), OP_APPLY_PDIM, use, 0, eta, I1, 0, 0);
      break;
    }
    default: die("inspect: unknown tag");
    }
    headFree(&h);
    return;
  }
  /* --- continuations (section 19): each holds its retained operands --- */
  case OP_KAPP: {
    int orig = o.p[1], arg = o.p[2], tag = refTag(d.a);
    if (tag == LAM) to(DK(D_TBIND, d.a, 1), OP_APPLY_TERM, newOp(OP_EVAL, oA, oI, eta, 0, 0, 0), 0, eta, arg, 0, 0);
    else if (tag == SYSTEM) evalTo(distribute(d.a, orig), eta, oA, oI);
    else connect(DR(orig, C_NEUTRAL), oA, oI);
    return;
  }
  case OP_KFST: case OP_KSND: {
    int orig = o.p[1], tag = refTag(d.a);
    if (tag == PAIR) { Head hp = openRef(d.a); evalTo(hp.f[o.kind == OP_KFST ? 0 : 1].ref, eta, oA, oI); headFree(&hp); }
    else if (tag == SYSTEM) evalTo(distribute(d.a, orig), eta, oA, oI);
    else connect(DR(orig, C_NEUTRAL), oA, oI);
    return;
  }
  case OP_KPEND0: case OP_KPEND1: {                  /* path endpoints before the path */
    int orig = o.p[1]; Head h = openRef(orig);
    if (d.kind == D_COVERED) evalTo(h.f[o.kind == OP_KPEND0 ? 1 : 2].ref, eta, oA, oI);
    else if (o.kind == OP_KPEND0) to(DK(D_FACE, endpoint(h.f[4].itv, 1), 0), OP_FACE_COVERAGE, newOp(OP_KPEND1, oA, oI, eta, orig, 0, 0), 0, eta, 0, 0, 0);
    else evalOpenTo(h.f[3].ref, eta, newOp(OP_KPAPP, oA, oI, eta, orig, 0, 0));
    headFree(&h);
    return;
  }
  case OP_KPAPP: {
    int orig = o.p[1], tag = refTag(d.a);
    if (tag == PLAM) { Head ho = openRef(orig); to(DK(D_DBIND, d.a, 0), OP_APPLY_DIM, newOp(OP_EVAL, oA, oI, eta, 0, 0, 0), 0, eta, ho.f[4].itv, 0, 0); headFree(&ho); }
    else if (tag == SYSTEM) evalTo(distribute(d.a, orig), eta, oA, oI);
    else connect(DR(orig, C_NEUTRAL), oA, oI);
    return;
  }
  case OP_KGLUE:                                     /* Glue type or glue: collapse only on the entailed face */
    if (d.kind == D_REF) evalTo(d.a, eta, oA, oI); else connect(DR(o.p[1], C_INTRO), oA, oI);
    return;
  case OP_KUNGLUE0: {
    int orig = o.p[1]; Head h = openRef(orig);
    if (d.kind == D_REF) evalTo(bApp(bFst(d.a), h.f[5].ref), eta, oA, oI);   /* on alpha: e.map(v) */
    else evalOpenTo(h.f[5].ref, eta, newOp(OP_KUNGLUE, oA, oI, eta, orig, 0, 0));
    headFree(&h);
    return;
  }
  case OP_KUNGLUE: {
    int orig = o.p[1], tag = refTag(d.a);
    if (tag == GLUE_INTRO) { Head hv = openRef(d.a); evalTo(hv.f[6].ref, eta, oA, oI); headFree(&hv); }
    else if (tag == SYSTEM) evalTo(distribute(d.a, orig), eta, oA, oI);
    else connect(DR(orig, C_NEUTRAL), oA, oI);
    return;
  }
  case OP_KSYS: {
    int orig = o.p[1], k = o.p[2];
    if (d.kind == D_REF) { evalTo(d.a, eta, oA, oI); return; }
    Head h = openRef(orig);
    if (k + 1 < h.sysN) to(DK(D_PARTIAL, h.sysFace[k + 1], h.sysTerm[k + 1]), OP_USE_PARTIAL, newOp(OP_KSYS, oA, oI, eta, orig, k + 1, 0), 0, eta, 0, 0, 0);
    else connect(DR(orig, C_SYSTEM), oA, oI);       /* no single branch covers: the covered system is retained */
    headFree(&h);
    return;
  }
  case OP_KCOMP0: {
    int c = o.p[1];
    if (d.kind == D_REF) { evalTo(d.a, eta, oA, oI); return; }
    Resolved fam = resolve(c, 0);
    int ev_ = newOp(OP_EVAL, newOp(OP_OPEN, newOp(OP_KCOMP, oA, oI, eta, c, 0, 0), 0, 0, 0, 0, 0), 0, eta, 0, 0, 0);
    to(DK(D_DBIND, c, 0), OP_APPLY_DIM, ev_, 0, eta, ivar(fam.var), 0, 0);
    return;
  }
  case OP_KCOMP: {
    int c = o.p[1], r = compClause(c, eta, d.a, d.cls);
    if (r >= 0) evalTo(r, eta, oA, oI); else connect(DR(c, C_NEUTRAL), oA, oI);
    return;
  }
  }
  die("an operation agent without a rule");
}
static void runJob(Job j) {
  if (j.kind == J_DELIVER) { ev(E_DELIVER); Job p = { J_PAIR, j.op, j.idx, j.d }; enqueue(p); return; }
  fire(j.op, j.idx, j.d);
}

/* ------------------------------------------------------------------------
 * Workloads (sections 30, 36).  A workload is closed once its roots are
 * installed; at quiescence a root either has its result (W_OK) or is stuck
 * on a demand cycle (W_STUCK), never a fabricated result.  The workload's
 * continuations are then released; a stuck workload's suspended waiters are
 * released and its running keys reset.
 * ---------------------------------------------------------------------- */
typedef struct { int ok; Data v; } Obs;
static void workloadEnd(int ok) {
  if (ok && atomic_load(&CUR->running)) die("a completed root left live demands");
  if (!ok) cacheAbandonRunning(CUR);
  int n = scount(&opsS);
  for (int i = 0; i < n; i++) { Op *o = OPP(i); free(o->ins); free(o->faces); }
  atomic_store(&opsS.n, 0);
}
static void demandMany(int n, const int *refs, const int *faces, Obs *out) {
  int *roots = xalloc(sizeof(int) * (n + 1));
  for (int i = 0; i < n; i++) roots[i] = newOp(OP_ROOT, -1, -1, 0, 0, 0, 0);
  for (int i = 0; i < n; i++) evalTo(refs[i], faces[i], roots[i], 0);
  waitQuiescent();
  int ok = 1;
  for (int i = 0; i < n; i++) { Op *r = OPP(roots[i]); out[i].ok = r->rootset; out[i].v = r->rootv; ok = ok && r->rootset; }
  workloadEnd(ok);
  free(roots);
}
static Obs demand(int ref, int chi) { Obs o; demandMany(1, &ref, &chi, &o); return o; }

/* ------------------------------------------------------------------------
 * Read-back (section 30): the normal form of a requested observation is a
 * fold of weak-head demands over the fields of each observed head.  It is
 * built once as a graph, one node per (reference, face projected to its
 * support), so shared subterms stay shared; a disjunctive face is read
 * clause by clause.  The text and the comparison dump are printed from it.
 * ---------------------------------------------------------------------- */
enum { N_EMPTY, N_STUCK, N_VAR, N_U, N_PI, N_SIGMA, N_LAM, N_PAIR, N_APP, N_FST, N_SND, N_PATH, N_PLAM, N_PAPP,
       N_GLUE, N_GLUEI, N_UNGLUE, N_SYS, N_COMP, N_SPLIT, NNK };
static const char *nkName[NNK] = { "empty", "stuck", "var", "U", "Pi", "Sigma", "lam", "pair", "app", "fst", "snd",
                                   "PathP", "plam", "papp", "Glue", "glue", "unglue", "system", "comp", "split" };
typedef struct { int kind, ref, var, lev, itv, face, n, cap; int *ch, *chf; } NF;
static NF *nfs; static int nnfs, capnfs;
static Memo nfMemo = MEMO_INIT;
static int nfStuck;
static int nfNew(int kind, int ref) {
  NF x; memset(&x, 0, sizeof x); x.kind = kind; x.ref = ref; x.var = x.lev = x.itv = x.face = -1;
  PUSH(nfs, nnfs, capnfs, x); return nnfs - 1;
}
static void nfAdd(int node, int child, int face) {
  NF *x = &nfs[node];
  if (x->n == x->cap) { x->cap = x->cap ? 2 * x->cap : 4; x->ch = xgrow(x->ch, sizeof(int) * x->cap); x->chf = xgrow(x->chf, sizeof(int) * x->cap); }
  x->ch[x->n] = child; x->chf[x->n] = face; x->n++;
}
static void nfReset(void) {
  for (int i = 0; i < nnfs; i++) { free(nfs[i].ch); free(nfs[i].chf); }
  free(nfs); nfs = NULL; nnfs = capnfs = 0; memoFree(&nfMemo); nfStuck = 0;
}
static int nfBuild(int ref, int chi);
static int nfPartial(int ref, int chi, int guard) { int c = fand(chi, guard); return c == F0 ? nfNew(N_EMPTY, ref) : nfBuild(ref, c); }
static int nfHead(int ref, int C) {
  Obs w = demand(ref, C);
  if (!w.ok) { nfStuck = 1; return nfNew(N_STUCK, ref); }
  int r = w.v.a, node;
  if (w.v.cls == C_EMPTY) return nfNew(N_EMPTY, r);
  if (isVar(r)) { node = nfNew(N_VAR, r); nfs[node].var = refVarId(r); return node; }
  Head h = openRef(r);
  switch (h.tag) {
  case UNIV: node = nfNew(N_U, r); nfs[node].lev = h.f[0].lev; break;
  case PI: case SIGMA: case LAM: {
    Resolved b = resolve(r, 1);
    node = nfNew(h.tag == PI ? N_PI : h.tag == SIGMA ? N_SIGMA : N_LAM, r); nfs[node].var = b.var;
    int c0 = nfBuild(h.f[0].ref, C); nfAdd(node, c0, F1);
    int c1 = nfBuild(b.body, C); nfAdd(node, c1, F1);
    break;
  }
  case PAIR: case APP: {
    node = nfNew(h.tag == PAIR ? N_PAIR : N_APP, r);
    int c0 = nfBuild(h.f[0].ref, C); nfAdd(node, c0, F1);
    int c1 = nfBuild(h.f[1].ref, C); nfAdd(node, c1, F1);
    break;
  }
  case FST: case SND: { node = nfNew(h.tag == FST ? N_FST : N_SND, r); int c = nfBuild(h.f[0].ref, C); nfAdd(node, c, F1); break; }
  case PATH: {
    Resolved b = resolve(r, 0); node = nfNew(N_PATH, r); nfs[node].var = b.var;
    int c0 = nfBuild(b.body, C); nfAdd(node, c0, F1);
    int c1 = nfBuild(h.f[1].ref, C); nfAdd(node, c1, F1);
    int c2 = nfBuild(h.f[2].ref, C); nfAdd(node, c2, F1);
    break;
  }
  case PLAM: { Resolved b = resolve(r, 0); node = nfNew(N_PLAM, r); nfs[node].var = b.var; int c = nfBuild(b.body, C); nfAdd(node, c, F1); break; }
  case PAPP: { node = nfNew(N_PAPP, r); nfs[node].itv = h.f[4].itv; int c = nfBuild(h.f[3].ref, C); nfAdd(node, c, F1); break; }
  case GLUE_TYPE: {
    node = nfNew(N_GLUE, r); nfs[node].lev = h.f[0].lev; nfs[node].face = h.f[2].face;
    int c0 = nfBuild(h.f[1].ref, C); nfAdd(node, c0, F1);
    int c1 = nfPartial(h.f[3].ref, C, h.f[2].face); nfAdd(node, c1, h.f[2].face);
    int c2 = nfPartial(h.f[4].ref, C, h.f[2].face); nfAdd(node, c2, h.f[2].face);
    break;
  }
  case GLUE_INTRO: {
    node = nfNew(N_GLUEI, r); nfs[node].face = h.f[2].face;
    int c0 = nfPartial(h.f[5].ref, C, h.f[2].face); nfAdd(node, c0, h.f[2].face);
    int c1 = nfBuild(h.f[6].ref, C); nfAdd(node, c1, F1);
    break;
  }
  case UNGLUE: { node = nfNew(N_UNGLUE, r); int c = nfBuild(h.f[5].ref, C); nfAdd(node, c, F1); break; }
  case SYSTEM:
    node = nfNew(N_SYS, r);
    for (int k = 0; k < h.sysN; k++) { int c = nfPartial(h.sysTerm[k], C, h.sysFace[k]); nfAdd(node, c, h.sysFace[k]); }
    break;
  case COMP: {
    Resolved fam = resolve(r, 0), tb = resolve(r, 2);
    node = nfNew(N_COMP, r); nfs[node].var = fam.var; nfs[node].face = h.f[1].face;
    int c0 = nfBuild(fam.body, C); nfAdd(node, c0, F1);
    int c1 = nfPartial(tb.body, C, h.f[1].face); nfAdd(node, c1, h.f[1].face);
    int c2 = nfBuild(h.f[3].ref, C); nfAdd(node, c2, F1);
    break;
  }
  default: die("read-back of an unknown head");
  }
  headFree(&h);
  return node;
}
static int nfBuild(int ref, int chi) {
  if (chi == F0) return nfNew(N_EMPTY, ref);
  int pc = projectFace(chi, &fvOf(ref)->d);
  int m = memoGet(&nfMemo, ref, pc); if (m >= 0) return m;
  int node;
  if (formClauses(pc, 1) > 1) {
    int n, *cl = faceClauses(pc, &n);
    node = nfNew(N_SPLIT, ref);
    for (int k = 0; k < n; k++) { int c = nfBuild(ref, cl[k]); nfAdd(node, c, cl[k]); }
    free(cl);
  } else node = nfHead(ref, pc);
  memoPut(&nfMemo, ref, pc, node);
  return node;
}

/* text */
static void pVar(int v) { printf("%s", V(v)->name); if (!V(v)->plain) printf("_%d", v); }
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
static void pLevel(int l) {
  int n; LT *t = levelTerms(l, &n);
  if (n > 1) printf("max(");
  for (int i = 0; i < n; i++) { if (i) printf(", "); if (t[i].v < 0) printf("%d", t[i].o); else { pVar(t[i].v); if (t[i].o) printf("+%d", t[i].o); } }
  if (n > 1) printf(")");
  free(t);
}
static void pNF(int n) {
  NF *x = &nfs[n];
  switch (x->kind) {
  case N_EMPTY: printf("_"); return;
  case N_STUCK: printf("<unresolved: a demand cycle>"); return;
  case N_VAR: pVar(x->var); return;
  case N_U: if (x->lev == lconst(0)) printf("U"); else { printf("(U "); pLevel(x->lev); printf(")"); } return;
  case N_PI: case N_SIGMA: case N_LAM:
    printf(x->kind == N_LAM ? "(\\(" : "(("); pVar(x->var); printf(" : "); pNF(x->ch[0]);
    printf(x->kind == N_LAM ? ") -> " : x->kind == N_PI ? ") -> " : ") * "); pNF(x->ch[1]); printf(")"); return;
  case N_PAIR: printf("("); pNF(x->ch[0]); printf(" , "); pNF(x->ch[1]); printf(")"); return;
  case N_APP: printf("("); pNF(x->ch[0]); printf(" "); pNF(x->ch[1]); printf(")"); return;
  case N_FST: case N_SND: pNF(x->ch[0]); printf(x->kind == N_FST ? ".1" : ".2"); return;
  case N_PATH: printf("(PathP (<"); pVar(x->var); printf("> "); pNF(x->ch[0]); printf(") "); pNF(x->ch[1]); printf(" "); pNF(x->ch[2]); printf(")"); return;
  case N_PLAM: printf("(<"); pVar(x->var); printf("> "); pNF(x->ch[0]); printf(")"); return;
  case N_PAPP: printf("("); pNF(x->ch[0]); printf(" @ "); pItv(x->itv); printf(")"); return;
  case N_GLUE: printf("(Glue "); pNF(x->ch[0]); printf(" ["); pFace(x->face); printf(" -> ("); pNF(x->ch[1]); printf(" , "); pNF(x->ch[2]); printf(")])"); return;
  case N_GLUEI: printf("(glue ["); pFace(x->face); printf(" -> "); pNF(x->ch[0]); printf("] "); pNF(x->ch[1]); printf(")"); return;
  case N_UNGLUE: printf("(unglue "); pNF(x->ch[0]); printf(")"); return;
  case N_SYS: case N_SPLIT:
    printf(x->kind == N_SYS ? "[" : "{");
    for (int k = 0, first = 1; k < x->n; k++) {
      if (nfs[x->ch[k]].kind == N_EMPTY) continue;
      if (!first) printf(x->kind == N_SYS ? ", " : " | ");
      first = 0; pFace(x->chf[k]); printf(" -> "); pNF(x->ch[k]);
    }
    printf(x->kind == N_SYS ? "]" : "}"); return;
  case N_COMP: printf("(comp <"); pVar(x->var); printf("> "); pNF(x->ch[0]); printf(" ["); pFace(x->face); printf(" -> "); pNF(x->ch[1]); printf("] "); pNF(x->ch[2]); printf(")"); return;
  }
}

/* the comparison dump (section 37): reachable nodes with their sharing,
 * variables with their provenance, references as renamable labels */
static FILE *dumpF; static int dumpIndex;
static IV dumpVars, dumpRefs;
static char *dumpSeen; static int dumpSeenCap;
static void dVar(int v) { ivadd(&dumpVars, v); fprintf(dumpF, " v%d", v); }
static void dItv(int r) {
  Form x = formGet(r, 0); fprintf(dumpF, " I[");
  for (int i = 0; i < x.n; i++) { fprintf(dumpF, "("); for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; ivadd(&dumpVars, a >> 1); fprintf(dumpF, "%s%c%d", k ? "," : "", (a & 1) ? '-' : '+', a >> 1); } fprintf(dumpF, ")"); }
  fprintf(dumpF, "]"); formFree(&x);
}
static void dFace(int phi) {
  Form x = formGet(phi, 1); fprintf(dumpF, " F[");
  for (int i = 0; i < x.n; i++) { fprintf(dumpF, "("); for (int k = 0; k < x.c[i].n; k++) { int a = x.c[i].a[k]; ivadd(&dumpVars, a >> 1); fprintf(dumpF, "%s%d=%d", k ? "," : "", a >> 1, a & 1); } fprintf(dumpF, ")"); }
  fprintf(dumpF, "]"); formFree(&x);
}
static void dLevel(int l) {
  int n; LT *t = levelTerms(l, &n); fprintf(dumpF, " L[");
  for (int i = 0; i < n; i++) { if (i) fprintf(dumpF, ","); if (t[i].v < 0) fprintf(dumpF, "c%d", t[i].o); else { ivadd(&dumpVars, t[i].v); fprintf(dumpF, "%d+%d", t[i].v, t[i].o); } }
  fprintf(dumpF, "]"); free(t);
}
static void dumpNode(int n) {
  if (n >= dumpSeenCap) { int nc = n * 2 + 64; dumpSeen = xgrow(dumpSeen, nc); memset(dumpSeen + dumpSeenCap, 0, nc - dumpSeenCap); dumpSeenCap = nc; }
  if (dumpSeen[n]) return;
  dumpSeen[n] = 1;
  NF *x = &nfs[n];
  for (int k = 0; k < x->n; k++) dumpNode(x->ch[k]);
  x = &nfs[n];
  ivadd(&dumpRefs, x->ref);
  fprintf(dumpF, "node %d %s r%d", n, nkName[x->kind], x->ref);
  switch (x->kind) {
  case N_VAR: dVar(x->var); break;
  case N_U: dLevel(x->lev); break;
  case N_PI: case N_SIGMA: case N_LAM: case N_PATH: case N_PLAM: dVar(x->var); break;
  case N_PAPP: dItv(x->itv); break;
  case N_GLUE: dLevel(x->lev); dFace(x->face); break;
  case N_GLUEI: dFace(x->face); break;
  case N_COMP: dVar(x->var); dFace(x->face); break;
  default: break;
  }
  for (int k = 0; k < x->n; k++) {
    if (x->kind == N_SYS || x->kind == N_SPLIT) dFace(x->chf[k]);
    fprintf(dumpF, " n%d", x->ch[k]);
  }
  fprintf(dumpF, "\n");
}
static void dumpEval(int root, const long *vec) {
  if (!dumpF) return;
  fprintf(dumpF, "eval %d\n", dumpIndex++);
  if (dumpSeenCap) memset(dumpSeen, 0, dumpSeenCap);
  dumpVars.n = dumpRefs.n = 0;
  dumpNode(root);
  for (int i = 0; i < dumpVars.n; i++) {
    int v = dumpVars.a[i]; Var *x = V(v);
    if (x->prov == P_POSTULATE) fprintf(dumpF, "var %d anchor %s\n", v, x->name);
    else if (x->prov == P_SOURCE) fprintf(dumpF, "var %d anchor src:%s@%d\n", v, x->name, x->pa);
    else if (x->prov == P_BINDER) { ivadd(&dumpRefs, x->pa); fprintf(dumpF, "var %d gen r%d %d %d\n", v, x->pa, x->pb, x->pc); }
    else fprintf(dumpF, "var %d free\n", v);
  }
  for (int i = 0; i < dumpRefs.n; i++) fprintf(dumpF, "ref r%d\n", dumpRefs.a[i]);
  fprintf(dumpF, "root %d\nevents", root);
  for (int k = 0; k < NEV; k++) fprintf(dumpF, " %ld", vec[k]);
  fprintf(dumpF, "\nend\n");
}

/* ------------------------------------------------------------------------
 * Checking the annotated core (section 33) and definitional conversion
 * (section 34).  Outcomes: VALID / INVALID / UNRESOLVED (for conversion
 * EQUAL / UNEQUAL / UNRESOLVED).  A judgment under a face holds when it
 * holds under each clause of the face; every judgment below is made under
 * one consistent clause C, after projecting C to the support of its inputs.
 * A judgment is memoized by its request record; a judgment met again while
 * it runs is a circular demand and is UNRESOLVED, never assumed.  An
 * UNRESOLVED outcome is not cached.  Fresh comparison identities are keyed
 * by the request record and a slot.
 * ---------------------------------------------------------------------- */
enum { V_OK, V_BAD, V_UNRES };
static char why[1024];
static int bad(const char *fmt, ...) { va_list ap; va_start(ap, fmt); vsnprintf(why, sizeof why, fmt, ap); va_end(ap); return V_BAD; }
static int unres(const char *fmt, ...) { va_list ap; va_start(ap, fmt); vsnprintf(why, sizeof why, fmt, ap); va_end(ap); return V_UNRES; }
static const char *vName(int s, int conv) { return s == V_OK ? (conv ? "EQUAL" : "VALID") : s == V_BAD ? (conv ? "UNEQUAL" : "INVALID") : "UNRESOLVED"; }

enum { J_CHK, J_INF, J_CONVT, J_CONVE, J_NEU };
static Tab jtab = TAB_INIT;                         /* request records [mode, a, b, c, face] */
static int *jstate, *jres; static int jrcap;          /* 0 none, 1 running, 2 VALID/EQUAL, 3 INVALID/UNEQUAL */
static Tab cvtab = TAB_INIT; static Store cvS = STORE_INIT(int);
static int jReq(int mode, int a, int b, int c, int face) {
  int v[5] = { mode, a, b, c, face }; int id = tabIntern(&jtab, v, 5);
  if (id >= jrcap) { int nc = id * 2 + 64; jstate = xgrow(jstate, sizeof(int) * nc); jres = xgrow(jres, sizeof(int) * nc); memset(jstate + jrcap, 0, sizeof(int) * (nc - jrcap)); memset(jres + jrcap, 0, sizeof(int) * (nc - jrcap)); jrcap = nc; }
  return id;
}
static int cvar(int req, int slot, int sort, int type) {
  int v[3] = { req, slot, sort }, var;
  LOCK(&cvtab.m);
  int isnew, id = tabInternLocked(&cvtab, v, 3, &isnew);
  if (isnew) { var = newVar(sort, sort == S_DIM ? "c" : "y", type, P_COMPARE, req, slot, sort, 0); if (spushLocked(&cvS, &var) != id) die("comparison table out of step"); }
  else var = *(int *)sat(&cvS, id);
  UNLOCK(&cvtab.m);
  return var;
}
static int suppFace(int C, int n, const int *refs) {
  IV s = { 0 };
  for (int i = 0; i < n; i++) if (refs[i] >= 0) { const FV *f = fvOf(refs[i]); for (int k = 0; k < f->d.n; k++) ivadd(&s, f->d.a[k]); }
  int r = projectFace(C, &s); ivfree(&s); return r;
}
/* weak-head observation for the checker, in the admission cache */
static int whnfC(int ref, int C, Data *out) {
  Obs o = demand(ref, C);
  if (!o.ok) return unres("observing a reference demands itself (a demand cycle)");
  *out = o.v; return V_OK;
}
static int clauseMap(int C);
static int chk(int t, int A, int C);
static int inf(int t, int C, int *A);
static int convT(int A, int B, int C);
static int convE(int t, int u, int A, int C);
static int neu(int a, int b, int C);
/* the face-general forms: every clause, in order; a witnessed failure wins,
 * then an unresolved one */
static int chkF(int t, int A, int chi) {
  if (chi == F0) return V_OK;
  int n, *cl = faceClauses(chi, &n), r = V_OK;
  for (int k = 0; k < n; k++) { int s = chk(t, A, cl[k]); if (s == V_BAD) { r = s; break; } if (s == V_UNRES) r = s; }
  free(cl); return r;
}
static int convTF(int A, int B, int chi) {
  if (chi == F0) return V_OK;
  int n, *cl = faceClauses(chi, &n), r = V_OK;
  for (int k = 0; k < n; k++) { int s = convT(A, B, cl[k]); if (s == V_BAD) { r = s; break; } if (s == V_UNRES) r = s; }
  free(cl); return r;
}
static int convEF(int t, int u, int A, int chi) {
  if (chi == F0) return V_OK;
  int n, *cl = faceClauses(chi, &n), r = V_OK;
  for (int k = 0; k < n; k++) { int s = convE(t, u, A, cl[k]); if (s == V_BAD) { r = s; break; } if (s == V_UNRES) r = s; }
  free(cl); return r;
}
/* A : U_lev under C */
static int chkTy(int A, int C, int *lev) {
  int T, s = inf(A, C, &T); if (s != V_OK) return s;
  Data w; s = whnfC(T, C, &w); if (s != V_OK) return s;
  if (refTag(w.a) != UNIV) return bad("a type was expected; its type is not a universe");
  Head h = openRef(w.a); *lev = h.f[0].lev; headFree(&h);
  return V_OK;
}
static int chkTyAt(int A, int chi, int lev) {        /* A : U_lev exactly, under every clause */
  if (chi == F0) return V_OK;
  int n, *cl = faceClauses(chi, &n), r = V_OK;
  for (int k = 0; k < n; k++) {
    int l, s = chkTy(A, cl[k], &l);
    if (s == V_OK && l != lev) s = bad("universe levels differ (levels are compared exactly)");
    if (s == V_BAD) { r = s; break; } if (s == V_UNRES) r = s;
  }
  free(cl); return r;
}
#define TRY(e) do { int s_ = (e); if (s_ != V_OK) return s_; } while (0)
static int equivType(int lev, int T, int A) {
  if (DEF_Equiv < 0) die("core: Equiv is not defined");
  int args[3] = { lev, T, A }; return globalView(DEF_Equiv, args);
}
/* the Glue type data: A : U_l; under C /\ alpha, T : U_l and e : Equiv T A */
static int chkGlueData(int lev, int A, int alpha, int T, int e, int C) {
  TRY(chkTyAt(A, C, lev));
  int c = fand(C, alpha);
  TRY(chkTyAt(T, c, lev));
  return chkF(e, equivType(lev, T, A), c);
}
static int expectHead(int A, int C, int tag, Data *w, const char *what) {
  TRY(whnfC(A, C, w));
  if (refTag(w->a) != tag || w->cls != C_INTRO) return bad("%s was expected", what);
  return V_OK;
}
/* the rules of the checking forms against an expected type */
static int chkRule(int t, int A, int C) {
  Head h = openRef(t); int tag = h.tag; Data w; int s = V_OK;
  switch (tag) {
  case LAM: {
    if ((s = expectHead(A, C, PI, &w, "a function type")) != V_OK) break;
    Head hp = openRef(w.a); int dom = hp.f[0].ref; headFree(&hp);
    s = convT(h.f[0].ref, dom, C);
    if (s == V_BAD) { s = bad("the lambda's domain differs from the function type's"); break; }
    if (s != V_OK) break;
    Resolved b = resolve(t, 1);
    s = chk(b.body, applyTerm(w.a, 1, refVar(b.var)), C);
    break;
  }
  case PAIR: {
    if ((s = expectHead(A, C, SIGMA, &w, "a pair type")) != V_OK) break;
    Head hs = openRef(w.a); int dom = hs.f[0].ref; headFree(&hs);
    if ((s = chk(h.f[0].ref, dom, C)) != V_OK) break;
    s = chk(h.f[1].ref, applyTerm(w.a, 1, h.f[0].ref), C);
    break;
  }
  case PLAM: {
    if ((s = expectHead(A, C, PATH, &w, "a path type")) != V_OK) break;
    Head hp = openRef(w.a); int l = hp.f[1].ref, r = hp.f[2].ref; headFree(&hp);
    Resolved b = resolve(t, 0);
    if ((s = chk(b.body, applyDim(w.a, 0, ivar(b.var)), C)) != V_OK) break;
    s = convE(applyDim(t, 0, I0), l, applyDim(w.a, 0, I0), C);
    if (s == V_BAD) { s = bad("the path's left endpoint differs from the type's"); break; }
    if (s != V_OK) break;
    s = convE(applyDim(t, 0, I1), r, applyDim(w.a, 0, I1), C);
    if (s == V_BAD) s = bad("the path's right endpoint differs from the type's");
    break;
  }
  case SYSTEM: {
    int cover = F0;
    for (int k = 0; k < h.sysN; k++) cover = forr(cover, h.sysFace[k]);
    if (!entails(C, cover)) { s = bad("the system does not cover its face"); break; }
    for (int k = 0; k < h.sysN && s != V_BAD; k++) { int r = chkF(h.sysTerm[k], A, fand(C, h.sysFace[k])); if (r != V_OK) s = r; }
    for (int k = 0; k < h.sysN && s != V_BAD; k++) for (int m = k + 1; m < h.sysN && s != V_BAD; m++) {
      int r = convEF(h.sysTerm[k], h.sysTerm[m], A, fand(C, fand(h.sysFace[k], h.sysFace[m])));
      if (r == V_BAD) r = bad("two branches of the system differ on their overlap");
      if (r != V_OK) s = r;
    }
    break;
  }
  default: s = bad("not a checking form");
  }
  headFree(&h);
  return s;
}
static int chk(int t, int A, int C) {
  int c = suppFace(C, 2, (int[]){ t, A });
  int id = jReq(J_CHK, t, A, -1, c);
  if (jstate[id] == 1) return unres("a circular typing judgment");
  if (jstate[id] >= 2) return jres[id];
  if (!entails(c, reqOf(t))) return bad("the required face of the term is not entailed");
  jstate[id] = 1;
  int tag = refTag(t), s;
  if (tag == LAM || tag == PAIR || tag == PLAM || tag == SYSTEM) {
    s = chkRule(t, A, c);
    int ann = O_(refOrigin(t))->ann;
    if (s == V_OK && ann >= 0) { int T; s = inf(t, c, &T); if (s == V_OK) { s = convT(T, A, c); if (s == V_BAD) s = bad("the annotation differs from the expected type"); } }
  } else {
    int T; s = inf(t, c, &T);
    if (s == V_OK) { s = convT(T, A, c); if (s == V_BAD) s = bad("the type of the term differs from the expected type"); }
  }
  if (s == V_UNRES) jstate[id] = 0; else { jstate[id] = 2; jres[id] = s; }
  return s;
}
static int infGlobal(int t, int C, int *A) {
  Def *D = DEF(O_(refOrigin(t))->scal); int m = refMap(t);
  for (int i = 0; i < D->params.n; i++) {
    int x = D->params.a[i];
    if (V(x)->sort != S_TERM) continue;
    int s = chk(termImage(m, x), reindex(V(x)->type, m), C);
    if (s == V_BAD) return bad("argument %d of %s does not have its parameter's type", i + 1, D->name);
    if (s != V_OK) return s;
  }
  if (D->type < 0) return bad("%s is used before its type is known (a recursive use needs a declared type)", D->name);
  *A = reindex(D->type, m);
  return V_OK;
}
static int infRule(int t, int C, int *A) {
  Head h = openRef(t); int s = V_OK; Data w;
  switch (h.tag) {
  case UNIV: *A = bUniv(lsuc(h.f[0].lev)); break;
  case PI: case SIGMA: {
    int i, j; if ((s = chkTy(h.f[0].ref, C, &i)) != V_OK) break;
    Resolved b = resolve(t, 1);
    if ((s = chkTy(b.body, C, &j)) != V_OK) break;
    *A = bUniv(lmax(i, j));
    break;
  }
  case LAM: case PAIR: case PLAM: s = bad("a %s synthesizes its type only from an annotation", tagName[h.tag]); break;
  case APP: {
    int T; if ((s = inf(h.f[0].ref, C, &T)) != V_OK) break;
    if ((s = expectHead(T, C, PI, &w, "a function")) != V_OK) break;
    Head hp = openRef(w.a); int dom = hp.f[0].ref; headFree(&hp);
    if ((s = chk(h.f[1].ref, dom, C)) != V_OK) break;
    *A = applyTerm(w.a, 1, h.f[1].ref);
    break;
  }
  case FST: case SND: {
    int T; if ((s = inf(h.f[0].ref, C, &T)) != V_OK) break;
    if ((s = expectHead(T, C, SIGMA, &w, "a pair")) != V_OK) break;
    Head hs = openRef(w.a); int dom = hs.f[0].ref; headFree(&hs);
    *A = h.tag == FST ? dom : applyTerm(w.a, 1, bFst(h.f[0].ref));
    break;
  }
  case PATH: {
    Resolved b = resolve(t, 0); int l;
    if ((s = chkTy(b.body, C, &l)) != V_OK) break;
    if ((s = chk(h.f[1].ref, applyDim(t, 0, I0), C)) != V_OK) break;
    if ((s = chk(h.f[2].ref, applyDim(t, 0, I1), C)) != V_OK) break;
    *A = bUniv(l);
    break;
  }
  case PAPP: {                                       /* the retained path type data, then the path */
    Resolved B = resolve(t, 0); int l;
    if ((s = chkTy(B.body, C, &l)) != V_OK) break;
    int B0 = reindex(B.body, map1Dim(B.var, I0)), B1 = reindex(B.body, map1Dim(B.var, I1));
    if ((s = chk(h.f[1].ref, B0, C)) != V_OK) break;
    if ((s = chk(h.f[2].ref, B1, C)) != V_OK) break;
    if ((s = chk(h.f[3].ref, bPath(B.var, B.body, h.f[1].ref, h.f[2].ref), C)) != V_OK) break;
    *A = applyDim(t, 0, h.f[4].itv);
    break;
  }
  case GLUE_TYPE:
    if ((s = chkGlueData(h.f[0].lev, h.f[1].ref, h.f[2].face, h.f[3].ref, h.f[4].ref, C)) != V_OK) break;
    *A = bUniv(h.f[0].lev);
    break;
  case GLUE_INTRO: {
    int lev = h.f[0].lev, Ab = h.f[1].ref, al = h.f[2].face, T = h.f[3].ref, e = h.f[4].ref, tt = h.f[5].ref, a = h.f[6].ref;
    if ((s = chkGlueData(lev, Ab, al, T, e, C)) != V_OK) break;
    if ((s = chk(a, Ab, C)) != V_OK) break;
    int c = fand(C, al);
    if ((s = chkF(tt, T, c)) != V_OK) break;
    s = convEF(bApp(bFst(e), tt), a, Ab, c);
    if (s == V_BAD) { s = bad("the equivalence's map of the fibre element differs from the base element"); break; }
    if (s != V_OK) break;
    *A = bGlueType(lev, Ab, al, T, e);
    break;
  }
  case UNGLUE: {
    int lev = h.f[0].lev;
    if ((s = chkGlueData(lev, h.f[1].ref, h.f[2].face, h.f[3].ref, h.f[4].ref, C)) != V_OK) break;
    if ((s = chk(h.f[5].ref, bGlueType(lev, h.f[1].ref, h.f[2].face, h.f[3].ref, h.f[4].ref), C)) != V_OK) break;
    *A = h.f[1].ref;
    break;
  }
  case COMP: {
    Resolved fam = resolve(t, 0), tb = resolve(t, 2); int l, phi = h.f[1].face, a0 = h.f[3].ref;
    if ((s = chkTy(fam.body, C, &l)) != V_OK) break;
    IV d = { 0 }; formDims(phi, 1, &d); int dep = ivhas(&d, fam.var); ivfree(&d);
    if (dep) { s = bad("the composition's face depends on its dimension"); break; }
    int A0 = applyDim(t, 0, I0);
    if ((s = chk(a0, A0, C)) != V_OK) break;
    int c = fand(C, phi);
    if ((s = chkF(tb.body, fam.body, c)) != V_OK) break;
    s = convEF(reindex(tb.body, map1Dim(tb.var, I0)), a0, A0, c);
    if (s == V_BAD) { s = bad("the tube at 0 differs from the cap"); break; }
    if (s != V_OK) break;
    *A = applyDim(t, 0, I1);
    break;
  }
  case SYSTEM: {                                     /* under one clause a covered system reduces to a branch */
    int cover = F0, k0 = -1;
    for (int k = 0; k < h.sysN; k++) { cover = forr(cover, h.sysFace[k]); if (k0 < 0 && entails(C, h.sysFace[k])) k0 = k; }
    if (!entails(C, cover) || k0 < 0) { s = bad("the system does not cover its face"); break; }
    int T; if ((s = inf(h.sysTerm[k0], C, &T)) != V_OK) break;
    for (int m = 0; m < h.sysN && s == V_OK; m++) {
      if (m == k0) continue;
      int c = fand(C, h.sysFace[m]);
      if ((s = chkF(h.sysTerm[m], T, c)) != V_OK) break;
      s = convEF(h.sysTerm[m], h.sysTerm[k0], T, c);
      if (s == V_BAD) s = bad("two branches of the system differ on their overlap");
    }
    if (s == V_OK) *A = T;
    break;
  }
  case GLOBAL: s = infGlobal(t, C, A); break;
  default: s = bad("unknown constructor");
  }
  headFree(&h);
  return s;
}
/* the substitution lemma on the representation (section 33): a view
 * VIEW(C, sigma) is typed by typing the origin's own view in its declared
 * context (under its required face, when that is one clause), checking each
 * term image against its declaration's type reindexed by sigma, and
 * reindexing the type; the copied body is not rechecked */
static int infView(int t, int C, int *A, int *done) {
  *done = 0;
  int o = refOrigin(t), m = refMap(t); Origin *O = O_(o);
  if (m == MID || O->tag == GLOBAL || O->ann >= 0 || formClauses(O->req, 1) != 1) return V_OK;
  int base = makeView(o, MID), Tb, s = inf(base, O->req, &Tb);
  if (s != V_OK) { *done = 1; return s; }
  for (int i = 0; i < O->fvt.n; i++) {
    int x = O->fvt.a[i], img = termImage(m, x);
    if (img == refVar(x)) continue;
    if (V(x)->type < 0) { *done = 1; return bad("a substituted variable without a declared type"); }
    s = chk(img, reindex(V(x)->type, m), C);
    if (s != V_OK) { *done = 1; if (s == V_BAD) return bad("a substitution image does not have its variable's type"); return s; }
  }
  *done = 1; *A = reindex(Tb, m);
  return V_OK;
}
static int inf(int t, int C, int *A) {
  int c = suppFace(C, 1, &t);
  int id = jReq(J_INF, t, -1, -1, c);
  if (jstate[id] == 1) return unres("a circular typing judgment");
  if (jstate[id] == 2) { *A = jres[id]; return V_OK; }
  if (jstate[id] == 3) return bad("%s", "the term was found ill-typed before");
  if (!entails(c, reqOf(t))) return bad("the required face of the term is not entailed");
  jstate[id] = 1;
  int s, T = -1;
  if (isVar(t)) {
    T = V(refVarId(t))->type;
    s = T < 0 ? bad("a variable without a declared type") : V_OK;
  } else {
    int ann = O_(refOrigin(t))->ann;
    if (ann >= 0) {                                  /* the annotation is validated, then used */
      int l; s = chkTy(ann, c, &l);
      if (s == V_OK) {
        int tag = refTag(t);
        if (tag == LAM || tag == PAIR || tag == PLAM || tag == SYSTEM) s = chkRule(t, ann, c);
        else { s = infRule(t, c, &T); if (s == V_OK) { s = convT(T, ann, c); if (s == V_BAD) s = bad("the term's type differs from its annotation"); } }
      }
      T = ann;
    } else { int done; s = infView(t, c, &T, &done); if (!done) s = infRule(t, c, &T); }
  }
  if (s == V_UNRES) jstate[id] = 0;
  else if (s == V_OK) { jstate[id] = 2; jres[id] = T; *A = T; }
  else jstate[id] = 3;
  return s;
}

/* type conversion (section 34) */
static int convT(int A, int B, int C) {
  if (A == B) return V_OK;
  int c = suppFace(C, 2, (int[]){ A, B });
  int id = jReq(J_CONVT, A, B, -1, c);
  if (jstate[id] == 1) return unres("a circular conversion");
  if (jstate[id] >= 2) return jres[id];
  jstate[id] = 1;
  Data a, b; int s = whnfC(A, c, &a);
  if (s == V_OK) s = whnfC(B, c, &b);
  if (s == V_OK && a.a != b.a) {
    int ta = refTag(a.a), tb = refTag(b.a);
    if (a.cls == C_SYSTEM || b.cls == C_SYSTEM) s = unres("a system type observed under one clause");
    else if (a.cls == C_NEUTRAL && b.cls == C_NEUTRAL) s = neu(a.a, b.a, c);
    else if (a.cls != b.cls || ta != tb) s = bad("different type constructors");
    else {
      Head ha = openRef(a.a), hb = openRef(b.a);
      switch (ta) {
      case UNIV: s = ha.f[0].lev == hb.f[0].lev ? V_OK : bad("different universe levels"); break;
      case PI: case SIGMA:
        if ((s = convT(ha.f[0].ref, hb.f[0].ref, c)) != V_OK) break;
        { int x = refVar(cvar(id, 0, S_TERM, ha.f[0].ref)); s = convT(applyTerm(a.a, 1, x), applyTerm(b.a, 1, x), c); }
        break;
      case PATH: {
        int j = ivar(cvar(id, 0, S_DIM, -1));
        if ((s = convT(applyDim(a.a, 0, j), applyDim(b.a, 0, j), c)) != V_OK) break;
        if ((s = convE(ha.f[1].ref, hb.f[1].ref, applyDim(a.a, 0, I0), c)) != V_OK) break;
        s = convE(ha.f[2].ref, hb.f[2].ref, applyDim(a.a, 0, I1), c);
        break;
      }
      case GLUE_TYPE: {
        if (ha.f[0].lev != hb.f[0].lev) { s = bad("different universe levels"); break; }
        if (fand(c, ha.f[2].face) != fand(c, hb.f[2].face)) { s = bad("different Glue faces"); break; }
        if ((s = convT(ha.f[1].ref, hb.f[1].ref, c)) != V_OK) break;
        int g = fand(c, ha.f[2].face);
        if ((s = convTF(ha.f[3].ref, hb.f[3].ref, g)) != V_OK) break;
        s = convEF(ha.f[4].ref, hb.f[4].ref, equivType(ha.f[0].lev, ha.f[3].ref, ha.f[1].ref), g);
        break;
      }
      default: s = bad("%s is not a type", tagName[ta]);
      }
      headFree(&ha); headFree(&hb);
    }
  }
  if (s == V_UNRES) jstate[id] = 0; else { jstate[id] = 2; jres[id] = s; }
  return s;
}
/* term conversion at an expected type (section 34): eta for functions,
 * pairs, paths and Glue; neutral spines structurally */
static int convE(int t, int u, int A, int C) {
  if (t == u) return V_OK;
  int c = suppFace(C, 3, (int[]){ t, u, A });
  int id = jReq(J_CONVE, t, u, A, c);
  if (jstate[id] == 1) return unres("a circular conversion");
  if (jstate[id] >= 2) return jres[id];
  jstate[id] = 1;
  Data w; int s = whnfC(A, c, &w);
  if (s == V_OK) {
    int tag = w.cls == C_INTRO ? refTag(w.a) : -1;
    Head h = openRef(w.a);
    switch (tag) {
    case PI: { int x = refVar(cvar(id, 0, S_TERM, h.f[0].ref)); s = convE(bApp(t, x), bApp(u, x), applyTerm(w.a, 1, x), c); break; }
    case SIGMA:
      if ((s = convE(bFst(t), bFst(u), h.f[0].ref, c)) != V_OK) break;
      s = convE(bSnd(t), bSnd(u), applyTerm(w.a, 1, bFst(t)), c);
      break;
    case PATH: {
      Resolved B = resolve(w.a, 0); int j = ivar(cvar(id, 0, S_DIM, -1));
      s = convE(bPapp(B.var, B.body, h.f[1].ref, h.f[2].ref, t, j), bPapp(B.var, B.body, h.f[1].ref, h.f[2].ref, u, j), applyDim(w.a, 0, j), c);
      break;
    }
    case GLUE_TYPE: {                                /* not collapsed under c */
      int lev = h.f[0].lev, Ab = h.f[1].ref, al = h.f[2].face, T = h.f[3].ref, e = h.f[4].ref;
      if ((s = convE(bUnglue(lev, Ab, al, T, e, t), bUnglue(lev, Ab, al, T, e, u), Ab, c)) != V_OK) break;
      s = convEF(t, u, T, fand(c, al));
      break;
    }
    case UNIV: s = convT(t, u, c); break;
    default: {                                       /* a neutral expected type: compare the terms' heads */
      Data a, b;
      if ((s = whnfC(t, c, &a)) != V_OK) break;
      if ((s = whnfC(u, c, &b)) != V_OK) break;
      if (a.a == b.a) s = V_OK;
      else if (a.cls == C_NEUTRAL && b.cls == C_NEUTRAL) s = neu(a.a, b.a, c);
      else if (a.cls == C_SYSTEM || b.cls == C_SYSTEM) s = unres("a system observed under one clause");
      else s = bad("different values at a neutral type");
    }
    }
    headFree(&h);
  }
  if (s == V_UNRES) jstate[id] = 0; else { jstate[id] = 2; jres[id] = s; }
  return s;
}
static int itvModClause(int r, int C) { return substInterval(r, clauseMap(C)); }
/* neutral comparison: the head and elimination spine structurally, argument
 * data by typed conversion; no eta on the spine head */
static int neuSpine(int x, int y, int C) {
  Data a, b; TRY(whnfC(x, C, &a)); TRY(whnfC(y, C, &b));
  if (a.a == b.a) return V_OK;
  if (a.cls != C_NEUTRAL || b.cls != C_NEUTRAL) return bad("a spine head is not neutral");
  return neu(a.a, b.a, C);
}
static int neu(int a, int b, int C) {
  if (a == b) return V_OK;
  int c = suppFace(C, 2, (int[]){ a, b });
  int id = jReq(J_NEU, a, b, -1, c);
  if (jstate[id] == 1) return unres("a circular conversion");
  if (jstate[id] >= 2) return jres[id];
  jstate[id] = 1;
  int ta = refTag(a), tb = refTag(b), s;
  if (ta != tb) s = bad("different neutral heads");
  else if (ta < 0) s = bad("different variables");
  else {
    Head ha = openRef(a), hb = openRef(b);
    switch (ta) {
    case APP: {
      if ((s = neuSpine(ha.f[0].ref, hb.f[0].ref, c)) != V_OK) break;
      int T; Data w;
      if ((s = inf(ha.f[0].ref, c, &T)) != V_OK) break;
      if ((s = expectHead(T, c, PI, &w, "a function")) != V_OK) break;
      Head hp = openRef(w.a); int dom = hp.f[0].ref; headFree(&hp);
      s = convE(ha.f[1].ref, hb.f[1].ref, dom, c);
      break;
    }
    case FST: case SND: s = neuSpine(ha.f[0].ref, hb.f[0].ref, c); break;
    case PAPP:
      if ((s = neuSpine(ha.f[3].ref, hb.f[3].ref, c)) != V_OK) break;
      s = itvModClause(ha.f[4].itv, c) == itvModClause(hb.f[4].itv, c) ? V_OK : bad("different path application intervals");
      break;
    case UNGLUE: {
      int lev = ha.f[0].lev;
      if (lev != hb.f[0].lev) { s = bad("different universe levels"); break; }
      if (fand(c, ha.f[2].face) != fand(c, hb.f[2].face)) { s = bad("different Glue faces"); break; }
      if ((s = convT(ha.f[1].ref, hb.f[1].ref, c)) != V_OK) break;
      int g = fand(c, ha.f[2].face);
      if ((s = convTF(ha.f[3].ref, hb.f[3].ref, g)) != V_OK) break;
      if ((s = convEF(ha.f[4].ref, hb.f[4].ref, equivType(lev, ha.f[3].ref, ha.f[1].ref), g)) != V_OK) break;
      s = neuSpine(ha.f[5].ref, hb.f[5].ref, c);
      break;
    }
    case COMP: {
      Resolved fa = resolve(a, 0), fb = resolve(b, 0), ua = resolve(a, 2), ub = resolve(b, 2);
      int j = ivar(cvar(id, 0, S_DIM, -1));
      int Aj = reindex(fa.body, map1Dim(fa.var, j)), Bj = reindex(fb.body, map1Dim(fb.var, j));
      if ((s = convT(Aj, Bj, c)) != V_OK) break;
      if (fand(c, ha.f[1].face) != fand(c, hb.f[1].face)) { s = bad("different composition faces"); break; }
      if ((s = convE(ha.f[3].ref, hb.f[3].ref, applyDim(a, 0, I0), c)) != V_OK) break;
      s = convEF(reindex(ua.body, map1Dim(ua.var, j)), reindex(ub.body, map1Dim(ub.var, j)), Aj, fand(c, ha.f[1].face));
      break;
    }
    default: s = bad("%s is not a neutral form", tagName[ta]);
    }
    headFree(&ha); headFree(&hb);
  }
  if (s == V_UNRES) jstate[id] = 0; else { jstate[id] = 2; jres[id] = s; }
  return s;
}

/* ------------------------------------------------------------------------
 * Source: a small CCHM syntax.  Its syntax trees, tokens and scopes live in
 * one arena released at teardown.
 * ---------------------------------------------------------------------- */
static void **arena; static int narena, caparena;
static void *aalloc(size_t n) { void *p = xalloc(n); PUSH(arena, narena, caparena, p); return p; }
static char *adup(const char *s) { char *d = aalloc(strlen(s) + 1); strcpy(d, s); return d; }
static void arenaFree(void) { for (int i = 0; i < narena; i++) free(arena[i]); free(arena); arena = NULL; narena = caparena = 0; }

enum { A_ID, A_NUM, A_U, A_LAM, A_PI, A_SIGMA, A_APP, A_PAIR, A_FST, A_SND, A_PLAM, A_PAPP, A_PATHP, A_PATH,
       A_COMP, A_COE, A_ANN, A_FILL, A_GLUE, A_GLUEI, A_UNGLUE, A_SYS, A_I0, A_I1, A_INEG, A_IAND, A_IOR, A_EQ };
typedef struct Ast { int k; char *name; struct Ast **c; int n; int eps; int pos; } Ast;
static char **tok; static int ntok, captok, pos;
static Ast *amk(int k, const char *name, int n) {
  Ast *a = aalloc(sizeof *a); a->k = k; a->name = name ? adup(name) : NULL; a->n = n; a->c = aalloc(sizeof(Ast *) * (n + 1)); a->pos = pos; return a;
}
static void lex(const char *s) {
  while (*s) {
    if (isspace((unsigned char)*s)) { s++; continue; }
    if (s[0] == '-' && s[1] == '-') { while (*s && *s != '\n') s++; continue; }
    const char *b = s;
    if (isalpha((unsigned char)*s) || *s == '_') { while (isalnum((unsigned char)*s) || *s == '_' || *s == '\'') s++; }
    else if (isdigit((unsigned char)*s)) { while (isdigit((unsigned char)*s)) s++; }
    else if (!strncmp(s, "->", 2) || !strncmp(s, "/\\", 2) || !strncmp(s, "\\/", 2) || !strncmp(s, ".1", 2) || !strncmp(s, ".2", 2)) s += 2;
    else if (strchr("()[],:*\\<>@~=", *s)) s++;
    else fail("unexpected character '%c'", *s);
    char *t = aalloc(s - b + 1); memcpy(t, b, s - b); PUSH(tok, ntok, captok, t);
  }
}
static const char *pk(int k) { return pos + k < ntok ? tok[pos + k] : ""; }
static int is(const char *s) { return !strcmp(pk(0), s); }
static const char *nx(void) { if (pos >= ntok) fail("unexpected end of input"); return tok[pos++]; }
static void want(const char *s) { if (!is(s)) fail("expected '%s' at '%s' (token %d)", s, pk(0), pos); pos++; }
static int isIdent(const char *s) { return isalpha((unsigned char)s[0]) || s[0] == '_'; }
static int isNum(const char *s) { if (!*s) return 0; for (; *s; s++) if (!isdigit((unsigned char)*s)) return 0; return 1; }
static int kw(const char *s) {
  static const char *k[] = { "U", "comp", "hcomp", "coe", "fill", "Glue", "glue", "unglue", "PathP", "Path", "postulate", "def", "eval", "assert", NULL };
  for (int i = 0; k[i]; i++) if (!strcmp(s, k[i])) return 1;
  return 0;
}
static Ast *pTerm(void);
static Ast *pAtom(void);
static Ast *parseItv(void);
static Ast *pIatom(void) {
  if (is("0")) { pos++; return amk(A_I0, NULL, 0); }
  if (is("1")) { pos++; return amk(A_I1, NULL, 0); }
  if (is("~")) { pos++; Ast *a = amk(A_INEG, NULL, 1); a->c[0] = pIatom(); return a; }
  if (is("(")) { pos++; Ast *a = parseItv(); want(")"); return a; }
  if (isIdent(pk(0)) && !kw(pk(0))) return amk(A_ID, nx(), 0);
  fail("expected an interval at '%s'", pk(0)); return NULL;
}
static Ast *pImeet(void) { Ast *l = pIatom(); while (is("/\\")) { pos++; Ast *a = amk(A_IAND, NULL, 2); a->c[0] = l; a->c[1] = pIatom(); l = a; } return l; }
static Ast *parseItv(void) { Ast *l = pImeet(); while (is("\\/")) { pos++; Ast *a = amk(A_IOR, NULL, 2); a->c[0] = l; a->c[1] = pImeet(); l = a; } return l; }
static Ast *pFlit(void) {
  want("("); Ast *r = parseItv(); want("=");
  Ast *a = amk(A_EQ, NULL, 1); a->c[0] = r;
  if (is("0")) a->eps = 0; else if (is("1")) a->eps = 1; else fail("expected 0 or 1");
  pos++; want(")"); return a;
}
static Ast *pFconj(void) { Ast *l = pFlit(); while (is("/\\")) { pos++; Ast *a = amk(A_IAND, NULL, 2); a->c[0] = l; a->c[1] = pFlit(); l = a; } return l; }
static Ast *parseFace(void) { Ast *l = pFconj(); while (is("\\/")) { pos++; Ast *a = amk(A_IOR, NULL, 2); a->c[0] = l; a->c[1] = pFconj(); l = a; } return l; }
/* [ face -> t , ... ]; with tuple > 1 each branch is face -> (t1 , .. , tn) */
static Ast *pSys(int tuple) {
  want("["); Ast *s = amk(A_SYS, NULL, 0);
  Ast **items = NULL; int n = 0, cap = 0;
  while (!is("]")) {
    Ast *f = parseFace(); want("->");
    PUSH(items, n, cap, f);
    if (tuple == 1) PUSH(items, n, cap, pTerm());
    else { want("("); for (int i = 0; i < tuple; i++) { if (i) want(","); PUSH(items, n, cap, pTerm()); } want(")"); }
    if (is(",")) pos++; else break;
  }
  want("]");
  s->c = aalloc(sizeof(Ast *) * (n + 1)); if (n) memcpy(s->c, items, sizeof(Ast *) * n); free(items);
  s->n = n; s->eps = tuple;
  return s;
}
static char *pDimBinder(void) { want("<"); char *i = adup(nx()); want(">"); return i; }
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
  if (is("[")) return pSys(1);
  if (is("0")) { pos++; return amk(A_I0, NULL, 0); }
  if (is("1")) { pos++; return amk(A_I1, NULL, 0); }
  if (isNum(pk(0))) return amk(A_NUM, nx(), 0);
  if (is("~")) { pos++; a = amk(A_INEG, NULL, 1); a->c[0] = pIatom(); return a; }
  if (isIdent(pk(0)) && !kw(pk(0))) return pPost(amk(A_ID, nx(), 0));
  fail("unexpected '%s' (token %d)", pk(0), pos); return NULL;
}
static int atomStart(void) { return is("(") || is("[") || is("U") || isNum(pk(0)) || is("~") || (isIdent(pk(0)) && !kw(pk(0))); }
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
    pos++; want("("); char *x = adup(nx()); want(":"); Ast *A = pTerm(); want(")"); want("->");
    Ast *a = amk(A_LAM, x, 2); a->c[0] = A; a->c[1] = pTerm(); return a;
  }
  if (is("<")) { char *i = pDimBinder(); Ast *a = amk(A_PLAM, i, 1); a->c[0] = pTerm(); return a; }
  if (binderGroup()) {
    int save = pos; pos++;
    char *xs[16]; int nx_ = 0; while (!is(":")) { if (nx_ == 16) fail("too many binders"); xs[nx_++] = adup(nx()); }
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
 * Elaboration: names to identities, source to cells.  The face under which
 * a subterm is elaborated (a system branch, a tube, a Glue partial) is
 * carried, for the inference a path application or a Glue level needs.
 * ---------------------------------------------------------------------- */
typedef struct Scope { const char *name; int var; struct Scope *up; } Scope;
typedef struct { char *name; int var; } Post;
static Post *posts; static int nposts, capposts;
static int lookup(Scope *s, const char *n) {
  for (; s; s = s->up) if (!strcmp(s->name, n)) return s->var;
  for (int i = 0; i < nposts; i++) if (!strcmp(posts[i].name, n)) return posts[i].var;
  return -1;
}
static int elab(Ast *a, Scope *s, int face);
static int elabItv(Ast *a, Scope *s) {
  switch (a->k) {
  case A_I0: return I0;
  case A_I1: return I1;
  case A_INEG: return ineg(elabItv(a->c[0], s));
  case A_IAND: return imeet(elabItv(a->c[0], s), elabItv(a->c[1], s));
  case A_IOR: return ijoin(elabItv(a->c[0], s), elabItv(a->c[1], s));
  case A_ID: { int v = lookup(s, a->name); if (v < 0 || V(v)->sort != S_DIM) fail("%s is not a dimension", a->name); return ivar(v); }
  default: fail("expected an interval"); return -1;
  }
}
static int elabLevel(Ast *a, Scope *s) {
  switch (a->k) {
  case A_I0: return lconst(0);
  case A_I1: return lconst(1);
  case A_NUM: return lconst(atoi(a->name));
  case A_ID: { int v = lookup(s, a->name); if (v < 0 || V(v)->sort != S_LEVEL) fail("%s is not a level", a->name); return lvar(v); }
  case A_APP:
    if (a->c[0]->k == A_ID && !strcmp(a->c[0]->name, "suc")) return lsuc(elabLevel(a->c[1], s));
    if (a->c[0]->k == A_APP && a->c[0]->c[0]->k == A_ID && !strcmp(a->c[0]->c[0]->name, "max")) return lmax(elabLevel(a->c[0]->c[1], s), elabLevel(a->c[1], s));
    break;
  default: break;
  }
  fail("expected a level"); return -1;
}
static int elabFace(Ast *a, Scope *s) {
  if (a->k == A_EQ) return endpoint(elabItv(a->c[0], s), a->eps);
  if (a->k == A_IAND) return fand(elabFace(a->c[0], s), elabFace(a->c[1], s));
  if (a->k == A_IOR) return forr(elabFace(a->c[0], s), elabFace(a->c[1], s));
  fail("expected a face"); return -1;
}
/* the weak-head type of t under every clause of the elaboration face */
static int typeHeadOf(int t, int face, int tag, const char *what) {
  int n, *cl = faceClauses(face == F0 ? F1 : face, &n), res = -1;
  for (int k = 0; k < n; k++) {
    int T, s = inf(t, cl[k], &T);
    if (s != V_OK) { free(cl); fail("the %s does not check (%s: %s)", what, vName(s, 0), why); }
    Data w; s = whnfC(T, cl[k], &w);
    if (s != V_OK) { free(cl); fail("the type of the %s is unresolved (%s)", what, why); }
    if (refTag(w.a) != tag) { free(cl); fail("the type of the %s is not a %s", what, tagName[tag]); }
    if (res >= 0 && res != w.a) { free(cl); fail("the type of the %s differs between the clauses of its face; annotate it", what); }
    res = w.a;
  }
  free(cl); return res;
}
static int levelOfType(int A, int face) {
  int n, *cl = faceClauses(face == F0 ? F1 : face, &n), res = -1;
  for (int k = 0; k < n; k++) {
    int l, s = chkTy(A, cl[k], &l);
    if (s != V_OK) { free(cl); fail("the base of a Glue is not a type (%s: %s)", vName(s, 0), why); }
    if (res >= 0 && res != l) { free(cl); fail("the level of the Glue base differs between clauses"); }
    res = l;
  }
  free(cl); return res;
}
static int sysFaces(Ast *sys, Scope *s, int tuple, int **faces) {
  int n = sys->n / (tuple + 1); *faces = xalloc(sizeof(int) * (n + 1)); int phi = F0;
  for (int k = 0; k < n; k++) { (*faces)[k] = elabFace(sys->c[k * (tuple + 1)], s); phi = forr(phi, (*faces)[k]); }
  return phi;
}
static int sysPart(Ast *sys, Scope *s, int tuple, int which, int *faces, int face) {
  int n = sys->n / (tuple + 1); int *ts = xalloc(sizeof(int) * (n + 1));
  for (int k = 0; k < n; k++) ts[k] = elab(sys->c[k * (tuple + 1) + 1 + which], s, fand(face, faces[k]));
  int r = n == 1 ? ts[0] : bSys(n, faces, ts);
  free(ts); return r;
}
static int binderCell(int tag, Ast *a, Scope *s, int face) {
  int A = elab(a->c[0], s, face);
  int x = newVar(S_TERM, a->name, A, P_SOURCE, a->pos, 0, 0, 0);
  Scope s2 = { a->name, x, s };
  return bBind(tag, x, A, elab(a->c[1], &s2, face));
}
static int elab(Ast *a, Scope *s, int face) {
  switch (a->k) {
  case A_U: return bUniv(lconst(0));
  case A_ID: {
    int v = lookup(s, a->name);
    if (v >= 0) { if (V(v)->sort != S_TERM) fail("%s is not a term", a->name); return refVar(v); }
    int d = findDef(a->name);
    if (d >= 0) { if (DEF(d)->params.n) fail("%s takes %d arguments", a->name, DEF(d)->params.n); return globalView(d, NULL); }
    fail("unknown name %s", a->name); return -1;
  }
  case A_APP: {
    Ast *spine[64]; int n = 0; Ast *h = a;
    while (h->k == A_APP) { if (n == 64) fail("application too long"); spine[n++] = h->c[1]; h = h->c[0]; }
    if (h->k == A_U) { if (n != 1) fail("U takes one level"); return bUniv(elabLevel(spine[0], s)); }
    if (h->k == A_ID && lookup(s, h->name) < 0 && findDef(h->name) >= 0) {
      int d = findDef(h->name), np = DEF(d)->params.n;
      if (n < np) fail("%s takes %d arguments", h->name, np);
      int *args = xalloc(sizeof(int) * (np + 1));
      for (int i = 0; i < np; i++) {
        Ast *arg = spine[n - 1 - i]; int sort = V(DEF(d)->params.a[i])->sort;
        args[i] = sort == S_DIM ? elabItv(arg, s) : sort == S_LEVEL ? elabLevel(arg, s) : elab(arg, s, face);
      }
      int r = globalView(d, args); free(args);
      for (int i = np; i < n; i++) r = bApp(r, elab(spine[n - 1 - i], s, face));
      return r;
    }
    return bApp(elab(a->c[0], s, face), elab(a->c[1], s, face));
  }
  case A_LAM: return binderCell(LAM, a, s, face);
  case A_PI: return binderCell(PI, a, s, face);
  case A_SIGMA: return binderCell(SIGMA, a, s, face);
  case A_PAIR: return bPair(elab(a->c[0], s, face), elab(a->c[1], s, face));
  case A_ANN: {
    int t = elab(a->c[0], s, face), T = elab(a->c[1], s, face);
    int n, *cl = faceClauses(face == F0 ? F1 : face, &n);
    for (int k = 0; k < n; k++) {
      int l, st = chkTy(T, cl[k], &l);
      if (st == V_OK) st = chk(t, T, cl[k]);
      if (st != V_OK) { free(cl); fail("the annotation does not check (%s: %s)", vName(st, 0), why); }
    }
    free(cl);
    return annotateCell(t, T);
  }
  case A_FST: return bFst(elab(a->c[0], s, face));
  case A_SND: return bSnd(elab(a->c[0], s, face));
  case A_PLAM: {
    int i = newVar(S_DIM, a->name, -1, P_SOURCE, a->pos, 0, 0, 0); Scope s2 = { a->name, i, s };
    return bPlam(i, elab(a->c[0], &s2, face));
  }
  case A_PATHP: case A_PATH: {
    const char *nm = a->k == A_PATHP ? a->name : "_";
    int i = newVar(S_DIM, nm, -1, P_SOURCE, a->pos, 0, 0, 0); Scope s2 = { nm, i, s };
    int B = elab(a->c[0], a->k == A_PATHP ? &s2 : s, face);
    return bPath(i, B, elab(a->c[1], s, face), elab(a->c[2], s, face));
  }
  case A_PAPP: {
    int p = elab(a->c[0], s, face), r = elabItv(a->c[1], s);
    int P = typeHeadOf(p, face, PATH, "path in `p @ r`");
    Head ht = openRef(P); Resolved B = resolve(P, 0);
    int res = bPapp(B.var, B.body, ht.f[1].ref, ht.f[2].ref, p, r);
    headFree(&ht); return res;
  }
  case A_COMP: case A_FILL: case A_COE: {
    int i = newVar(S_DIM, a->name, -1, P_SOURCE, a->pos, 0, 0, 0); Scope s2 = { a->name, i, s };
    int A = elab(a->c[0], &s2, face);
    if (a->k == A_COE) { int x = elab(a->c[1], s, face); return bComp(i, A, F0, bSys(0, NULL, NULL), x); }
    int *faces; int phi = sysFaces(a->c[1], s, 1, &faces);
    { IV d = { 0 }; formDims(phi, 1, &d); int dep = ivhas(&d, i); ivfree(&d); if (dep) { free(faces); fail("a composition's face mentions its own dimension"); } }
    int u = a->c[1]->n ? sysPart(a->c[1], &s2, 1, 0, faces, face) : bSys(0, NULL, NULL);
    free(faces);
    int a0 = elab(a->c[2], s, face);
    if (a->k != A_FILL) return bComp(i, A, phi, u, a0);
    /* fill^i A [phi -> u] a0 (r) = comp^j A(r/\j) [phi -> u(r/\j), (r=0) -> a0] a0 */
    int r = elabItv(a->c[3], s), jj = newVar(S_DIM, "j", -1, P_SOURCE, a->pos, 1, 0, 0), sm = map1Dim(i, imeet(r, ivar(jj)));
    int z = endpoint(r, 0);
    int fs[2] = { phi, z }, ts[2] = { reindex(u, sm), a0 };
    return bComp(jj, reindex(A, sm), forr(phi, z), bSys(2, fs, ts), a0);
  }
  case A_GLUE: case A_GLUEI: case A_UNGLUE: {
    int A = elab(a->c[0], s, face), lev = levelOfType(A, face);
    int tuple = a->k == A_GLUEI ? 3 : 2, *faces;
    int phi = sysFaces(a->c[1], s, tuple, &faces);
    int T = sysPart(a->c[1], s, tuple, 0, faces, face), e = sysPart(a->c[1], s, tuple, 1, faces, face), r;
    if (a->k == A_GLUE) r = bGlueType(lev, A, phi, T, e);
    else if (a->k == A_GLUEI) r = bGlueIntro(lev, A, phi, T, e, sysPart(a->c[1], s, tuple, 2, faces, face), elab(a->c[2], s, face));
    else r = bUnglue(lev, A, phi, T, e, elab(a->c[2], s, face));
    free(faces); return r;
  }
  case A_SYS: {                                      /* a system [phi_k -> t_k] */
    int *faces, n = a->n / 2; sysFaces(a, s, 1, &faces);
    int *ts = xalloc(sizeof(int) * (n + 1));
    for (int k = 0; k < n; k++) ts[k] = elab(a->c[2 * k + 1], s, fand(face, faces[k]));
    int r = bSys(n, faces, ts); free(ts); free(faces); return r;
  }
  default: fail("this is not a term"); return -1;
  }
}

/* ------------------------------------------------------------------------
 * Declarations.  Admission (elaboration and checking) uses one persistent
 * cache; each `eval` is a separate counted workload on a fresh evaluation
 * cache, so its event vector is that of its own demand network from an
 * empty cache.  Both vectors are reported.
 * ---------------------------------------------------------------------- */
static int failures;
static Cache *ADMIT;
static void evSnap(long *v) { for (int k = 0; k < NEV; k++) v[k] = atomic_load(&evc[k]); }
static void evPrint(const char *label, const long *a, const long *b) {
  long tot = 0; for (int k = 0; k < NEV; k++) tot += b[k] - a[k];
  printf("  [%s: %ld interactions:", label, tot);
  for (int k = 0; k < NEV; k++) printf(" %s %ld%s", evName[k], b[k] - a[k], k + 1 < NEV ? "," : "");
  printf("]\n");
}
static int scopeOK(int ref, const IV *allowedT, const IV *allowedD, const IV *allowedL) {
  const FV *f = fvOf(ref);
  for (int i = 0; i < f->t.n; i++) if (!ivhas(allowedT, f->t.a[i]) && V(f->t.a[i])->prov != P_POSTULATE) return 0;
  for (int i = 0; i < f->d.n; i++) if (!ivhas(allowedD, f->d.a[i])) return 0;
  for (int i = 0; i < f->l.n; i++) if (!ivhas(allowedL, f->l.a[i])) return 0;
  return 1;
}
static void requireSorts(const char *name, int d, const int *sorts, int n) {
  Def *D = DEF(d); int ok = D->params.n == n;
  for (int i = 0; ok && i < n; i++) if (V(D->params.a[i])->sort != sorts[i]) ok = 0;
  if (!ok) fail("core: %s must take its parameters in the kernel's order", name);
}
static void skipToDecl(void) {
  while (pos < ntok && !is("postulate") && !is("def") && !is("eval") && !is("assert")) pos++;
}
static void decl(void) {
  if (is("postulate")) {
    pos++; const char *x = nx(); want(":");
    int ty = elab(pTerm(), NULL, F1), l, s = chkTy(ty, F1, &l);
    if (s != V_OK) fail("postulate %s: its type does not check (%s: %s)", x, vName(s, 0), why);
    Post p = { xdup(x), newVar(S_TERM, x, ty, P_POSTULATE, nposts, 0, 0, 0) }; V(p.var)->plain = 1;
    PUSH(posts, nposts, capposts, p);
    return;
  }
  if (is("def")) {
    pos++; Def d; memset(&d, 0, sizeof d); d.name = xdup(nx()); d.type = -1; d.body = -1;
    Scope *s = NULL; IV gT = { 0 }, gD = { 0 }, gL = { 0 };
    while (is("(")) {
      int at0 = pos; pos++; const char *xs[16]; int n = 0;
      while (!is(":")) { if (n == 16) fail("too many parameters"); xs[n++] = nx(); }
      pos++;
      int sort = S_TERM, ty = -1;
      if (is("I") && !strcmp(pk(1), ")")) { sort = S_DIM; pos++; }
      else if (is("Level") && !strcmp(pk(1), ")")) { sort = S_LEVEL; pos++; }
      else {
        ty = elab(pTerm(), s, F1); int l, st = chkTy(ty, F1, &l);
        if (st != V_OK) fail("def %s: a parameter type does not check (%s: %s)", d.name, vName(st, 0), why);
      }
      want(")");
      for (int i = 0; i < n; i++) {
        int v = newVar(sort, xs[i], ty, P_SOURCE, at0, i, 0, 0);
        Scope *s2 = aalloc(sizeof *s2); s2->name = xs[i]; s2->var = v; s2->up = s; s = s2;
        ivp(&d.params, v); ivp(sort == S_TERM ? &gT : sort == S_DIM ? &gD : &gL, v);
      }
    }
    if (is(":")) {
      pos++; d.type = elab(pTerm(), s, F1); int l, st = chkTy(d.type, F1, &l);
      if (st != V_OK) fail("def %s: its type does not check (%s: %s)", d.name, vName(st, 0), why);
    }
    want("=");
    int idx = scount(&defsS);
    d.origin = mkOrigin(GLOBAL, idx, F1, -1, 0, NULL, 0, NULL, &gT, &gD, &gL);
    spush(&defsS, &d);
    int body = elab(pTerm(), s, F1);
    DEF(idx)->body = body;
    int st;
    if (DEF(idx)->type >= 0) st = chk(body, DEF(idx)->type, F1);
    else { int T; st = inf(body, F1, &T); if (st == V_OK) DEF(idx)->type = T; }
    if (st != V_OK) fail("def %s: %s: %s", d.name, vName(st, 0), why);
    if (!scopeOK(body, &gT, &gD, &gL) || !scopeOK(DEF(idx)->type, &gT, &gD, &gL)) fail("def %s: an unbound dependency", d.name);
    ivfree(&gT); ivfree(&gD); ivfree(&gL);
    if (!strcmp(d.name, "fib")) { int so[5] = { S_LEVEL, S_TERM, S_TERM, S_TERM, S_TERM }; requireSorts("fib", idx, so, 5); DEF_fib = idx; }
    if (!strcmp(d.name, "lineEquiv")) { int so[4] = { S_LEVEL, S_TERM, S_TERM, S_TERM }; requireSorts("lineEquiv", idx, so, 4); DEF_lineEquiv = idx; }
    if (!strcmp(d.name, "Equiv")) { int so[3] = { S_LEVEL, S_TERM, S_TERM }; requireSorts("Equiv", idx, so, 3); DEF_Equiv = idx; }
    return;
  }
  if (is("eval")) {
    pos++;
    long a0[NEV], a1[NEV], e0[NEV], e1[NEV];
    evSnap(a0);
    int t = elab(pTerm(), NULL, F1), T, st = inf(t, F1, &T);
    evSnap(a1);
    if (st != V_OK) { printf("eval: %s: %s\n", vName(st, 0), why); failures++; return; }
    Cache *ec = newCache(); CUR = ec;
    evSnap(e0);
    int root = nfBuild(t, F1);
    evSnap(e1);
    printf("eval "); pNF(root); printf("\n");
    evPrint("evaluation, from an empty cache", e0, e1);
    evPrint("admission", a0, a1);
    long vec[NEV]; for (int k = 0; k < NEV; k++) vec[k] = e1[k] - e0[k];
    dumpEval(root, vec);
    if (nfStuck) failures++;
    nfReset(); CUR = ADMIT; cacheFree(ec);
    return;
  }
  if (is("assert")) {
    pos++; const char *kind = nx();
    int conv = !strcmp(kind, "equal") || !strcmp(kind, "unequal") || !strcmp(kind, "undecided");
    int want_ = !strcmp(kind, "valid") || !strcmp(kind, "equal") ? V_OK : !strcmp(kind, "invalid") || !strcmp(kind, "unequal") ? V_BAD : V_UNRES;
    if (!conv && strcmp(kind, "valid") && strcmp(kind, "invalid") && strcmp(kind, "unresolved")) fail("unknown assertion %s", kind);
    int start = pos, got, typingFailed = 0;
    jmp_buf jb; recoverJmp = &jb;
    if (!setjmp(jb)) {
      if (!conv) {
        Ast *ta = pTerm(); want(":"); Ast *Ta = pTerm();
        int T = elab(Ta, NULL, F1), l; got = chkTy(T, F1, &l);
        if (got == V_OK) { int t = elab(ta, NULL, F1); got = chk(t, T, F1); }
      } else {
        Ast *Ta = pAtom(), *ta = pAtom(), *ua = pAtom();
        int T = elab(Ta, NULL, F1), t = elab(ta, NULL, F1), u = elab(ua, NULL, F1), l;
        got = chkTy(T, F1, &l);
        if (got == V_OK) got = chk(t, T, F1);
        if (got == V_OK) got = chk(u, T, F1);
        if (got != V_OK) typingFailed = 1; else got = convE(t, u, T, F1);
      }
    } else { got = V_BAD; snprintf(why, sizeof why, "%s", lastError); typingFailed = conv; if (pos == start) pos++; skipToDecl(); }
    recoverJmp = NULL;
    int pass = got == want_ && !typingFailed;
    printf("assert %s (tokens %d-%d): %s (%s%s: %s)\n", kind, start, pos - 1, pass ? "PASS" : "FAIL",
           typingFailed ? "typing " : "", vName(got, conv && !typingFailed), got == V_OK ? "-" : why);
    if (!pass) failures++;
    return;
  }
  fail("expected postulate, def, eval or assert at '%s' (token %d)", pk(0), pos);
}

/* ------------------------------------------------------------------------
 * Self-test: the acceptance cases of section 23 and every scope agent's
 * rule run through the queue against its finite operation.
 * ---------------------------------------------------------------------- */
static int stFail;
static void stCheck(const char *name, int ok) { printf("selftest %-72s %s\n", name, ok ? "PASS" : "FAIL"); if (!ok) stFail++; }
static Data runAgent(Data in, int kind, int p1, int p2, int eta, int *got) {
  int root = newOp(OP_ROOT, -1, -1, 0, 0, 0, 0);
  connect(in, newOp(kind, root, 0, eta, p1, p2, 0), 0);
  waitQuiescent();
  Op *r = OPP(root); Data d = r->rootv; *got = r->rootset;
  workloadEnd(1);
  return d;
}
static void selftest(void) {
  int i = newVar(S_DIM, "i", -1, P_SOURCE, -1, 0, 0, 0), j = newVar(S_DIM, "j", -1, P_SOURCE, -2, 0, 0, 0), k = newVar(S_DIM, "k", -1, P_SOURCE, -3, 0, 0, 0);
  stCheck("interval i /\\ i is i", imeet(ivar(i), ivar(i)) == ivar(i));
  { int r = imeet(ivar(i), ineg(ivar(i))); Form x = formGet(r, 0); stCheck("interval i /\\ ~i is retained", r != I0 && x.n == 1 && x.c[0].n == 2); formFree(&x); }
  stCheck("face (i=0) /\\ (i=1) is false", fand(flit(i, 0), flit(i, 1)) == F0);
  stCheck("face (i=0) \\/ (i=1) is not true", forr(flit(i, 0), flit(i, 1)) != F1);
  stCheck("endpoint (~i = 0) is (i = 1)", endpoint(ineg(ivar(i)), 0) == flit(i, 1));
  stCheck("endpoint (~i = 1) is (i = 0)", endpoint(ineg(ivar(i)), 1) == flit(i, 0));
  int U0 = bUniv(lconst(0));
  int A = newVar(S_TERM, "A", U0, P_POSTULATE, -1, 0, 0, 0), Z = newVar(S_TERM, "Z", U0, P_POSTULATE, -2, 0, 0, 0);
  int T = newVar(S_TERM, "T", U0, P_POSTULATE, -3, 0, 0, 0), A2 = newVar(S_TERM, "A2", U0, P_POSTULATE, -4, 0, 0, 0);
  int x = newVar(S_TERM, "x", refVar(A), P_POSTULATE, -5, 0, 0, 0), y = newVar(S_TERM, "y", refVar(A), P_POSTULATE, -6, 0, 0, 0), z = newVar(S_TERM, "z", refVar(A), P_POSTULATE, -7, 0, 0, 0);
  int a = newVar(S_TERM, "a", refVar(A), P_POSTULATE, -8, 0, 0, 0), b = newVar(S_TERM, "b", refVar(A), P_POSTULATE, -9, 0, 0, 0);
  int w = newVar(S_TERM, "w", refVar(A), P_SOURCE, -10, 0, 0, 0), dd = newVar(S_DIM, "d", -1, P_SOURCE, -11, 0, 0, 0);
  int f = newVar(S_TERM, "f", bBind(PI, w, refVar(A), refVar(A)), P_POSTULATE, -12, 0, 0, 0);
  int p = newVar(S_TERM, "p", bPath(dd, refVar(A), refVar(a), refVar(b)), P_POSTULATE, -13, 0, 0, 0);
  int q = newVar(S_TERM, "q", bPath(dd, U0, refVar(A), refVar(A2)), P_POSTULATE, -14, 0, 0, 0);
  int e = newVar(S_TERM, "e", -1, P_POSTULATE, -15, 0, 0, 0);
  { KV t[2] = { { x, refVar(y) }, { y, refVar(z) } }; int m = mapMake(t, 2, NULL, 0, NULL, 0);
    stCheck("x[x->y, y->z] is y", reindex(refVar(x), m) == refVar(y));
    stCheck("(x[x->y])[y->z] is z", reindex(reindex(refVar(x), map1Term(x, refVar(y))), map1Term(y, refVar(z))) == refVar(z)); }
  int R = bApp(refVar(f), refVar(y));
  stCheck("R[x->a], R[x->b] are one reference when x is outside R's boundary",
          reindex(R, map1Term(x, refVar(a))) == reindex(R, map1Term(x, refVar(b))) && reindex(R, map1Term(x, refVar(a))) == R);
  int pj = bPapp(dd, refVar(A), refVar(a), refVar(b), refVar(p), ivar(j));
  stCheck("the support of R[x -> p@j] includes j", ivhas(&fvOf(reindex(bApp(refVar(f), refVar(x)), map1Term(x, pj)))->d, j));
  { IV S = { 0 }, E = { 0 }; ivp(&S, j); int chi = fand(flit(i, 0), flit(j, 0));
    stCheck("project (i=0) /\\ (j=0) onto {j} is (j=0)", projectFace(chi, &S) == flit(j, 0));
    stCheck("forall i of (i=0) /\\ (j=0) is false", forallDim(i, chi) == F0);
    stCheck("forall i of (i=0) \\/ (j=0) is (j=0)", forallDim(i, forr(flit(i, 0), flit(j, 0))) == flit(j, 0));
    stCheck("project false onto {} is false", projectFace(F0, &E) == F0);
    ivfree(&S); }
  Cache *c1 = newCache(); CUR = c1;
  { long e0 = evc[E_EVALUATE]; demand(R, flit(i, 0)); long e1 = evc[E_EVALUATE]; demand(R, flit(i, 1)); long e2 = evc[E_EVALUATE];
    stCheck("a closed reference projects every consistent face to true", projectFace(flit(i, 0), &fvOf(R)->d) == F1);
    stCheck("a closed reference under two faces is evaluated once", e1 > e0 && e2 == e1); }
  { int t = bPapp(dd, refVar(A), refVar(a), refVar(b), refVar(p), ivar(i));
    Obs o1 = demand(t, F1), o2 = demand(t, flit(i, 0)), o3 = demand(t, flit(i, 1));
    stCheck("neutral p@i under true is neutral", o1.ok && o1.v.cls == C_NEUTRAL && o1.v.a == t);
    stCheck("p@i under (i=0) is the left endpoint", o2.ok && o2.v.a == refVar(a));
    stCheck("p@i under (i=1) is the right endpoint", o3.ok && o3.v.a == refVar(b));
    int t2 = reindex(t, map1Dim(i, ivar(k)));
    stCheck("p@i's old projected key under (k=0) is true", projectFace(flit(k, 0), &fvOf(t)->d) == F1);
    Obs o4 = demand(t2, flit(k, 0));
    stCheck("p@i reindexed to p@k observes the endpoint under (k=0)", o4.ok && o4.v.a == refVar(a)); }
  { int Bi = bPapp(dd, U0, refVar(A), refVar(A2), refVar(q), ivar(i));
    int G = bGlueType(lconst(0), Bi, flit(i, 0), refVar(T), refVar(e));
    Head h = openRef(G); int base = h.f[1].ref; headFree(&h);
    Obs o = demand(reindex(G, map1Dim(i, I0)), F1), ob = demand(reindex(base, map1Dim(i, I0)), F1);
    stCheck("Glue [(i=0) -> T] B(i) at i=0 collapses to T", o.ok && o.v.a == refVar(T));
    stCheck("its retained base B(i) specialized at 0 survives and is B(0)", reindex(base, map1Dim(i, I0)) != refVar(T) && ob.ok && ob.v.a == refVar(A)); }
  { int kk = newVar(S_DIM, "k", -1, P_SOURCE, -16, 0, 0, 0);
    int c = bComp(kk, refVar(Z), flit(i, 0), refVar(a), refVar(a));
    Obs o = demand(c, flit(i, 0));
    stCheck("a covered composition returns its tube at 1", o.ok && o.v.a == refVar(a));
    stCheck("... without demanding its family head", entryFind(CUR, refVar(Z), F1) < 0); }
  cacheFree(c1);
  { long r0 = evc[E_REQUEST], v0 = evc[E_EVALUATE], d0 = evc[E_DELIVER];
    Cache *c2 = newCache(); CUR = c2; Obs o1 = demand(R, F1); cacheFree(c2);
    long r1 = evc[E_REQUEST], v1 = evc[E_EVALUATE], d1 = evc[E_DELIVER];
    Cache *c3 = newCache(); CUR = c3; int refs[2] = { R, R }, fs[2] = { F1, F1 }; Obs o[2]; demandMany(2, refs, fs, o); cacheFree(c3);
    long r2 = evc[E_REQUEST], v2 = evc[E_EVALUATE], d2 = evc[E_DELIVER];
    stCheck("two requests for one key: one evaluation task", v2 - v1 == v1 - v0);
    stCheck("... both receive its result", o[0].ok && o[1].ok && o[0].v.a == o1.v.a && o[1].v.a == o1.v.a);
    stCheck("... each request is one request and one delivery", r2 - r1 == r1 - r0 + 1 && d2 - d1 == d1 - d0 + 1); }
  Cache *c4 = newCache(); CUR = c4;
  { Def d; memset(&d, 0, sizeof d); d.name = xdup("loop"); d.body = -1; d.type = refVar(A);
    int x0 = newVar(S_TERM, "x", refVar(A), P_SOURCE, -17, 0, 0, 0); ivp(&d.params, x0);
    IV gT = { 0 }, none = { 0 }; ivp(&gT, x0);
    int idx = scount(&defsS); d.origin = mkOrigin(GLOBAL, idx, F1, -1, 0, NULL, 0, NULL, &gT, &none, &none); ivfree(&gT);
    spush(&defsS, &d);
    int self = refVar(x0); DEF(idx)->body = globalView(idx, &self);
    int t = globalView(idx, (int[]){ refVar(a) });
    Obs o = demand(t, F1);
    stCheck("a running self-demand is stuck, not a fabricated result", !o.ok);
    int ei = entryFind(CUR, t, F1);
    stCheck("... nothing is published, and teardown released its waiters", ei >= 0 && EN(CUR, ei)->state == UNEVALUATED && EN(CUR, ei)->nw == 0);
    int got; Data u = runAgent(DK(D_REF, t, 0), OP_UNFOLD, 0, 0, F1, &got);
    stCheck("UNFOLD_GLOBAL is the body reindexed by the view's map", got && u.a == t); }
  { int got, m = map1Dim(i, ivar(k)), sig = map1Term(x, refVar(y)), tau = map1Term(y, refVar(z)), Rx = bApp(refVar(f), refVar(x));
    Data r;
    r = runAgent(DK(D_REF, Rx, 0), OP_REINDEX_TERM, sig, 0, F1, &got); stCheck("REINDEX_TERM", got && r.a == reindex(Rx, sig));
    r = runAgent(DK(D_INTERVAL, ivar(i), 0), OP_REINDEX_INTERVAL, m, 0, F1, &got); stCheck("REINDEX_INTERVAL", got && r.a == ivar(k));
    r = runAgent(DK(D_FACE, flit(i, 0), 0), OP_REINDEX_FACE, map1Dim(i, ineg(ivar(k))), 0, F1, &got); stCheck("REINDEX_FACE", got && r.a == flit(k, 1));
    r = runAgent(DK(D_MAP, tau, 0), OP_COMPOSE_MAP, sig, 0, F1, &got);
    stCheck("COMPOSE_MAP, and t[sigma;tau] = (t[sigma])[tau]", got && r.a == composeMaps(sig, tau) && reindex(Rx, r.a) == reindex(reindex(Rx, sig), tau));
    int lam = bLam(w, refVar(A), bApp(refVar(f), refVar(w)));
    r = runAgent(DK(D_TBIND, lam, 1), OP_APPLY_TERM, refVar(a), 0, F1, &got); stCheck("APPLY_TERM_BINDER", got && r.a == applyTerm(lam, 1, refVar(a)) && demand(r.a, F1).v.a == r.a);
    int pl = bPlam(dd, bPapp(dd, refVar(A), refVar(a), refVar(b), refVar(p), ivar(dd)));
    r = runAgent(DK(D_DBIND, pl, 0), OP_APPLY_DIM, ivar(j), 0, F1, &got); stCheck("APPLY_DIM_BINDER", got && r.a == applyDim(pl, 0, ivar(j)));
    r = runAgent(DK(D_REF, pl, 0), OP_OPEN, 0, 0, F1, &got); stCheck("OPEN", got && r.kind == D_HEAD && r.a == pl);
    r = runAgent(DK(D_HEAD, Rx, 0), OP_REINDEX_HEAD, sig, 0, F1, &got); stCheck("REINDEX_HEAD", got && r.a == reindex(Rx, sig));
    r = runAgent(DK(D_TBIND, lam, 1), OP_REINDEX_TBIND, sig, 0, F1, &got); stCheck("REINDEX_TERM_BINDER", got && r.a == reindex(lam, sig) && r.b == 1);
    r = runAgent(DK(D_PARTIAL, flit(i, 0), pj), OP_REINDEX_PARTIAL, map1Dim(j, ivar(i)), 0, F1, &got);
    stCheck("REINDEX_PARTIAL", got && r.a == flit(i, 0) && r.b == reindex(pj, map1Dim(j, ivar(i))));
    int chi = forr(flit(i, 0), flit(j, 0));
    r = runAgent(DK(D_FACE, chi, 0), OP_FORALL, i, 0, F1, &got); stCheck("FORALL_DIMENSION", got && r.a == flit(j, 0));
    IV S = { 0 }; ivp(&S, j); int ds = dimsetOf(&S);
    r = runAgent(DK(D_FACE, fand(flit(i, 0), flit(j, 0)), 0), OP_PROJECT_FACE, ds, 0, F1, &got); stCheck("PROJECT_FACE", got && r.a == flit(j, 0));
    r = runAgent(DK(D_REF, pj, 0), OP_GET_SUPPORT, 0, 0, F1, &got); stCheck("GET_SUPPORT", got && r.a == dimsetOf(&fvOf(pj)->d));
    ivfree(&S);
    r = runAgent(DK(D_FACE, flit(i, 0), 0), OP_FACE_COVERAGE, 0, 0, fand(flit(i, 0), flit(j, 1)), &got); stCheck("FACE_COVERAGE covered", got && r.kind == D_COVERED);
    r = runAgent(DK(D_FACE, flit(i, 0), 0), OP_FACE_COVERAGE, 0, 0, flit(j, 1), &got); stCheck("FACE_COVERAGE not covered", got && r.kind == D_NOT_COVERED);
    r = runAgent(DK(D_PARTIAL, flit(i, 0), refVar(a)), OP_USE_PARTIAL, 0, 0, flit(i, 0), &got); stCheck("USE_PARTIAL covered", got && r.kind == D_REF && r.a == refVar(a));
    r = runAgent(DK(D_PARTIAL, flit(i, 0), refVar(a)), OP_USE_PARTIAL, 0, 0, F1, &got);
    stCheck("USE_PARTIAL not covered retains its payload", got && r.kind == D_NOT_COVERED && r.a == flit(i, 0) && r.b == refVar(a));
    int cmp = bComp(dd, refVar(A), flit(i, 0), refVar(a), refVar(a));
    r = runAgent(DK(D_PDBIND, cmp, 2), OP_APPLY_PDIM, I1, 0, F1, &got); stCheck("APPLY_PARTIAL_DIM_BINDER", got && r.kind == D_PARTIAL && r.a == flit(i, 0) && r.b == refVar(a));
    r = runAgent(DK(D_MAP, refMap(lam), 0), OP_LIFT, lam, 1, F1, &got); stCheck("LIFT", got && r.a == resolve(lam, 1).lifted);
    IV decl = { 0 }; int ctx = ctxMake(&decl, F1), tm = typedMap(ctx, ctx, m);
    r = runAgent(DK(D_TMAP, tm, 0), OP_RESTRICT_MAP, flit(k, 0), 0, F1, &got);
    stCheck("RESTRICT_MAP strengthens source by phi[sigma] and target by phi", got && r.a == restrictTypedMap(tm, flit(k, 0)) && ctxFace(tmSource(r.a)) == flit(k, 0) && ctxFace(tmTarget(r.a)) == flit(k, 0) && composeTyped(tm, tm) == typedMap(ctx, ctx, composeMaps(m, m)));
    int r1 = newOp(OP_ROOT, -1, -1, 0, 0, 0, 0), r2 = newOp(OP_ROOT, -1, -1, 0, 0, 0, 0);
    connect(DK(D_REF, Rx, 0), newOp(OP_DUP, r1, 0, 0, r2, 0, 0), 0); waitQuiescent();
    stCheck("DUP copies the handle, not the construction", OPP(r1)->rootset && OPP(r2)->rootset && OPP(r1)->rootv.a == Rx && OPP(r2)->rootv.a == Rx);
    workloadEnd(1);
    long q0 = outstanding; connect(DK(D_REF, Rx, 0), newOp(OP_ERA, -1, -1, 0, 0, 0, 0), 0); waitQuiescent(); workloadEnd(1);
    stCheck("ERA retires the descriptor; the workload is quiescent", outstanding == 0 && q0 == 0); }
  cacheFree(c4); CUR = ADMIT;
}

/* ------------------------------------------------------------------------
 * Teardown (section 36): workers stopped and joined first, then the caches,
 * then the immutable arenas.
 * ---------------------------------------------------------------------- */
static void teardown(void) {
  stopWorkers();
  cacheFree(ADMIT); CUR = ADMIT = NULL;
  int n = scount(&originsS);
  for (int i = 0; i < n; i++) { Origin *o = O_(i); free(o->b); free(o->f); ivfree(&o->fvt); ivfree(&o->fvd); ivfree(&o->fvl); }
  sfree(&originsS);
  n = scount(&varsS); for (int i = 0; i < n; i++) free(V(i)->name); sfree(&varsS);
  n = scount(&fvS); for (int i = 0; i < n; i++) { FV *f = sat(&fvS, i); ivfree(&f->t); ivfree(&f->d); ivfree(&f->l); } sfree(&fvS); free(fvIdx);
  n = scount(&defsS); for (int i = 0; i < n; i++) { free(DEF(i)->name); ivfree(&DEF(i)->params); } sfree(&defsS);
  Tab *tabs[] = { &itab, &ftab, &ltab, &mtab, &rtab, &otab, &btab, &formalTab, &ctab, &tmtab, &dstab, &jtab, &cvtab };
  for (size_t t = 0; t < sizeof tabs / sizeof *tabs; t++) tabFree(tabs[t]);
  sfree(&binstS); sfree(&formalS); sfree(&cvS); sfree(&opsS);
  memoFree(&reidx); free(jstate); free(jres);
  for (int i = 0; i < nposts; i++) free(posts[i].name);
  free(posts); free(tok); arenaFree();
  nfReset(); ivfree(&dumpVars); ivfree(&dumpRefs); free(dumpSeen);
  if (dumpF) fclose(dumpF);
}
static char *slurp(const char *fn) {
  FILE *f = fopen(fn, "rb"); if (!f) fail("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *b = xalloc(n + 2); if (fread(b, 1, n, f) != (size_t)n) fail("cannot read %s", fn); fclose(f);
  b[n] = '\n'; return b;
}
int main(int argc, char **argv) {
  mainThread = pthread_self();
  for (int i = 0; i < NJOINLK; i++) pthread_mutex_init(&joinLk[i], NULL);
  int self = 0, nfiles = 0; char **files = xalloc(sizeof(char *) * (argc + 1));
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-w") && i + 1 < argc) { NWORKERS = atoi(argv[++i]); if (NWORKERS < 1) fail("-w needs a positive worker count"); }
    else if (!strcmp(argv[i], "-p") && i + 1 < argc) {
      const char *p = argv[++i];
      POLICY = !strcmp(p, "lifo") ? POL_LIFO : !strcmp(p, "fifo") ? POL_FIFO : !strcmp(p, "random") ? POL_RANDOM : !strcmp(p, "mixed") ? POL_MIXED : -1;
      if (POLICY < 0) fail("-p lifo|fifo|random|mixed");
    }
    else if (!strcmp(argv[i], "-s") && i + 1 < argc) { rngState = strtoull(argv[++i], NULL, 10) * 2654435761ull + 1; }
    else if (!strcmp(argv[i], "-d") && i + 1 < argc) { dumpF = fopen(argv[++i], "w"); if (!dumpF) fail("cannot write %s", argv[i]); }
    else if (!strcmp(argv[i], "--selftest")) self = 1;
    else files[nfiles++] = argv[i];
  }
  if (!self && !nfiles) { fprintf(stderr, "usage: cell [-w workers] [-p lifo|fifo|random|mixed] [-s seed] [-d dump] [--selftest] file ...\n"); return 2; }
  I0 = formConst(0, 0); I1 = formConst(1, 0); F0 = formConst(0, 1); F1 = formConst(1, 1);
  MID = mapMake(NULL, 0, NULL, 0, NULL, 0);
  ADMIT = CUR = newCache();
  startWorkers();
  if (self) selftest();
  for (int i = 0; i < nfiles; i++) { char *b = slurp(files[i]); lex(b); free(b); }
  free(files);
  while (pos < ntok) decl();
  teardown();
  if (self) printf("selftest: %d failed\n", stFail);
  return failures || stFail ? 1 : 0;
}

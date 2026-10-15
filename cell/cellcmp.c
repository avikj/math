/* cell/cellcmp.c -- exact comparison of two result dumps modulo renaming of
 * generated identities (cell/HANDOFF.md section 37).
 *
 * A dump (cell -d FILE) holds, per eval, the reachable read-back graph:
 * nodes with their kind, their reference label, and ordered items (child
 * nodes, variables, intervals, faces, levels); variables with provenance
 * (anchored by name, or generated with owner reference, slot and sort);
 * and the balanced event vector.  Two dumps are equal when every eval's
 * root admits one bijection of nodes, references and variables preserving
 * every kind, payload, ordered item, provenance, interval and face clause
 * set, level and sharing relation -- and the event vectors are equal.
 * Unordered collections (clause sets, the literals of a clause, the clause
 * branches of a split read-back) are matched by exact backtracking over
 * candidates of the same shape; nothing is decided by colours or hashes.
 *
 *   cellcmp A B      exit 0 when equal, 1 with the first mismatch otherwise
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

static void *xalloc(size_t n) { void *p = calloc(1, n ? n : 1); if (!p) { fprintf(stderr, "out of memory\n"); exit(2); } return p; }
static void **pool; static int npool, cappool;
static void *palloc(size_t n) { void *p = xalloc(n); if (npool == cappool) { cappool = cappool ? 2 * cappool : 1024; pool = realloc(pool, sizeof(void *) * cappool); } pool[npool++] = p; return p; }
static void poolFree(int mark) { while (npool > mark) free(pool[--npool]); }

typedef struct { int var, tag; } Lit;                 /* I: tag 0 (+) / 1 (-); F: tag eps; L: var -1 const, tag offset */
typedef struct { Lit *l; int n; } Clause;
typedef struct { Clause *c; int n; } Set;
typedef struct { char kind; int id; Set s; } Item;      /* kind: n v I F L */
typedef struct { char kind[16]; int ref, ni; Item *it; int present; } Node;
typedef struct { int kind; char name[128]; int owner, slot, sort, present; } VarR;   /* kind 0 anchor, 1 gen, 2 free */
typedef struct { Node *nodes; int nn; VarR *vars; int nv; int maxref; int root; long ev[16]; int nev; } Eval;
typedef struct { Eval *e; int n; } Dump;

static Set parseSet(const char *s, char kind) {   /* s points after the kind letter, at '[' */
  Set r = { 0 }; int cap = 0;
  if (*s != '[') { fprintf(stderr, "malformed set\n"); exit(2); }
  s++;
  if (kind == 'L') {
    Clause c = { 0 }; int lc = 0;
    while (*s && *s != ']') {
      Lit l;
      if (*s == 'c') { l.var = -1; l.tag = (int)strtol(s + 1, (char **)&s, 10); }
      else { l.var = (int)strtol(s, (char **)&s, 10); if (*s == '+') s++; l.tag = (int)strtol(s, (char **)&s, 10); }
      if (c.n == lc) { lc = lc ? 2 * lc : 4; c.l = realloc(c.l, sizeof(Lit) * lc); }
      c.l[c.n++] = l;
      if (*s == ',') s++;
    }
    r.c = xalloc(sizeof(Clause)); r.c[0] = c; r.n = 1;     /* a level is one set of terms */
    return r;
  }
  while (*s == '(') {
    s++; Clause c = { 0 }; int lc = 0;
    while (*s && *s != ')') {
      Lit l;
      if (kind == 'I') { l.tag = *s == '-'; s++; l.var = (int)strtol(s, (char **)&s, 10); }
      else { l.var = (int)strtol(s, (char **)&s, 10); if (*s == '=') s++; l.tag = (int)strtol(s, (char **)&s, 10); }
      if (c.n == lc) { lc = lc ? 2 * lc : 4; c.l = realloc(c.l, sizeof(Lit) * lc); }
      c.l[c.n++] = l;
      if (*s == ',') s++;
    }
    if (*s == ')') s++;
    if (r.n == cap) { cap = cap ? 2 * cap : 4; r.c = realloc(r.c, sizeof(Clause) * cap); }
    r.c[r.n++] = c;
  }
  return r;
}
static void grow(void **a, int *cap, int need, size_t esz) {
  if (need < *cap) return;
  int nc = need * 2 + 16; *a = realloc(*a, esz * nc); memset((char *)*a + esz * *cap, 0, esz * (nc - *cap)); *cap = nc;
}
static Dump readDump(const char *fn) {
  FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
  Dump d = { 0 }; int cap = 0; char line[1 << 16]; Eval *e = NULL; int ncap = 0, vcap = 0;
  while (fgets(line, sizeof line, f)) {
    char *tok = strtok(line, " \n");
    if (!tok) continue;
    if (!strcmp(tok, "eval")) {
      if (d.n == cap) { cap = cap ? 2 * cap : 8; d.e = realloc(d.e, sizeof(Eval) * cap); }
      e = &d.e[d.n++]; memset(e, 0, sizeof *e); ncap = vcap = 0; e->root = -1;
    } else if (!strcmp(tok, "node")) {
      int id = atoi(strtok(NULL, " \n"));
      grow((void **)&e->nodes, &ncap, id, sizeof(Node)); if (id >= e->nn) e->nn = id + 1;
      Node *n = &e->nodes[id]; n->present = 1;
      snprintf(n->kind, sizeof n->kind, "%s", strtok(NULL, " \n"));
      n->ref = atoi(strtok(NULL, " \n") + 1); if (n->ref > e->maxref) e->maxref = n->ref;
      int ic = 0; char *t;
      while ((t = strtok(NULL, " \n"))) {
        Item it; memset(&it, 0, sizeof it); it.kind = t[0];
        if (t[0] == 'n' || t[0] == 'v') it.id = atoi(t + 1); else it.s = parseSet(t + 1, t[0]);
        if (n->ni == ic) { ic = ic ? 2 * ic : 4; n->it = realloc(n->it, sizeof(Item) * ic); }
        n->it[n->ni++] = it;
      }
    } else if (!strcmp(tok, "var")) {
      int id = atoi(strtok(NULL, " \n"));
      grow((void **)&e->vars, &vcap, id, sizeof(VarR)); if (id >= e->nv) e->nv = id + 1;
      VarR *v = &e->vars[id]; v->present = 1;
      char *k = strtok(NULL, " \n");
      if (!strcmp(k, "anchor")) { v->kind = 0; snprintf(v->name, sizeof v->name, "%s", strtok(NULL, " \n")); }
      else if (!strcmp(k, "gen")) { v->kind = 1; v->owner = atoi(strtok(NULL, " \n") + 1); v->slot = atoi(strtok(NULL, " \n")); v->sort = atoi(strtok(NULL, " \n")); if (v->owner > e->maxref) e->maxref = v->owner; }
      else v->kind = 2;
    } else if (!strcmp(tok, "root")) e->root = atoi(strtok(NULL, " \n"));
    else if (!strcmp(tok, "events")) { char *t; while ((t = strtok(NULL, " \n")) && e->nev < 16) e->ev[e->nev++] = atol(t); }
  }
  fclose(f);
  return d;
}

/* the bijections and their trail */
static Eval *L, *R;
static int *nL2R, *nR2L, *vL2R, *vR2L, *rL2R, *rR2L;
typedef struct { int *fw, *bw, a; } Tr;
static Tr *trail; static int ntrail, captrail;
static int bind(int *fw, int *bw, int a, int b) {
  if (fw[a] >= 0) return fw[a] == b;
  if (bw[b] >= 0) return 0;
  fw[a] = b; bw[b] = a;
  if (ntrail == captrail) { captrail = captrail ? 2 * captrail : 1024; trail = realloc(trail, sizeof(Tr) * captrail); }
  trail[ntrail].fw = fw; trail[ntrail].bw = bw; trail[ntrail].a = a; ntrail++;
  return 1;
}
static void undo(int mark) { while (ntrail > mark) { Tr t = trail[--ntrail]; t.bw[t.fw[t.a]] = -1; t.fw[t.a] = -1; } }

/* obligations: an immutable list; a choice point retries the rest of the list */
enum { OB_NODE, OB_VAR, OB_REF, OB_SET, OB_CLAUSE, OB_SPLIT };
typedef struct Ob { int kind, a, b; Clause *ca, *cb; int *ra, *rb, nr; const Node *na, *nb; char sk; struct Ob *next; } Ob;
static Ob *ob(int kind, int a, int b, Ob *next) { Ob *o = palloc(sizeof *o); o->kind = kind; o->a = a; o->b = b; o->next = next; return o; }
static char why[512];
static int bestDepth = -1;
/* the reported mismatch is the one reached by the deepest partial bijection */
static int failf(const char *m) { if (ntrail >= bestDepth) { bestDepth = ntrail; snprintf(why, sizeof why, "%s (after %d matched identities)", m, ntrail); } return 0; }
static int solve(Ob *o);
/* remaining-index arrays without element k */
static int *without(const int *r, int n, int k) { int *x = palloc(sizeof(int) * (n + 1)); int m = 0; for (int i = 0; i < n; i++) if (i != k) x[m++] = r[i]; return x; }
static int solveSet(Ob *o) {                         /* clauses ra of ca against clauses rb of cb */
  if (o->nr == 0) return solve(o->next);
  Clause *x = &o->ca[o->ra[0]];
  for (int k = 0; k < o->nr; k++) {
    Clause *y = &o->cb[o->rb[k]];
    if (x->n != y->n) continue;
    int mark = ntrail, pm = npool;
    Ob *rest = ob(OB_SET, 0, 0, o->next); rest->ca = o->ca; rest->cb = o->cb; rest->nr = o->nr - 1; rest->sk = o->sk;
    rest->ra = without(o->ra, o->nr, 0); rest->rb = without(o->rb, o->nr, k);
    Ob *cl = ob(OB_CLAUSE, 0, 0, rest); cl->ca = x; cl->cb = y; cl->nr = x->n; cl->sk = o->sk;
    cl->ra = palloc(sizeof(int) * (x->n + 1)); cl->rb = palloc(sizeof(int) * (x->n + 1));
    for (int i = 0; i < x->n; i++) { cl->ra[i] = i; cl->rb[i] = i; }
    if (solve(cl)) return 1;
    undo(mark); poolFree(pm);
  }
  return failf("a clause set has no matching clause");
}
static int solveClause(Ob *o) {                      /* literals ra of ca against literals rb of cb */
  if (o->nr == 0) return solve(o->next);
  Lit *x = &o->ca->l[o->ra[0]];
  for (int k = 0; k < o->nr; k++) {
    Lit *y = &o->cb->l[o->rb[k]];
    if (x->tag != y->tag || (x->var < 0) != (y->var < 0)) continue;
    int mark = ntrail, pm = npool;
    Ob *rest = ob(OB_CLAUSE, 0, 0, o->next); rest->ca = o->ca; rest->cb = o->cb; rest->nr = o->nr - 1; rest->sk = o->sk;
    rest->ra = without(o->ra, o->nr, 0); rest->rb = without(o->rb, o->nr, k);
    Ob *v = x->var < 0 ? rest : ob(OB_VAR, x->var, y->var, rest);
    if (solve(v)) return 1;
    undo(mark); poolFree(pm);
  }
  return failf("a clause has no matching literal");
}
static int solveSplit(Ob *o) {                       /* (face, node) pairs, unordered */
  if (o->nr == 0) return solve(o->next);
  int a = o->ra[0];
  for (int k = 0; k < o->nr; k++) {
    int b = o->rb[k];
    int mark = ntrail, pm = npool;
    Ob *rest = ob(OB_SPLIT, 0, 0, o->next); rest->na = o->na; rest->nb = o->nb; rest->nr = o->nr - 1;
    rest->ra = without(o->ra, o->nr, 0); rest->rb = without(o->rb, o->nr, k);
    Ob *nd = ob(OB_NODE, o->na->it[2 * a + 1].id, o->nb->it[2 * b + 1].id, rest);
    Ob *st = ob(OB_SET, 0, 0, nd);
    Set *sa = &((Node *)o->na)->it[2 * a].s, *sb = &((Node *)o->nb)->it[2 * b].s;
    if (sa->n != sb->n) { undo(mark); poolFree(pm); continue; }
    st->ca = sa->c; st->cb = sb->c; st->nr = sa->n; st->sk = 'F';
    st->ra = palloc(sizeof(int) * (sa->n + 1)); st->rb = palloc(sizeof(int) * (sa->n + 1));
    for (int i = 0; i < sa->n; i++) { st->ra[i] = i; st->rb[i] = i; }
    if (solve(st)) return 1;
    undo(mark); poolFree(pm);
  }
  return failf("a split read-back has no matching clause branch");
}
static int solve(Ob *o) {
  while (o) {
    switch (o->kind) {
    case OB_SET: return solveSet(o);
    case OB_CLAUSE: return solveClause(o);
    case OB_SPLIT: return solveSplit(o);
    case OB_REF: if (!bind(rL2R, rR2L, o->a, o->b)) return failf("references alias differently"); o = o->next; break;
    case OB_VAR: {
      if (o->a >= L->nv || o->b >= R->nv || !L->vars[o->a].present || !R->vars[o->b].present) return failf("an undeclared variable");
      if (vL2R[o->a] >= 0) { if (vL2R[o->a] != o->b) return failf("variables map inconsistently"); o = o->next; break; }
      VarR *x = &L->vars[o->a], *y = &R->vars[o->b];
      if (x->kind != y->kind) return failf("variables of different provenance");
      if (x->kind == 0 && strcmp(x->name, y->name)) return failf("anchored variables differ");
      if (x->kind == 1 && (x->slot != y->slot || x->sort != y->sort)) return failf("generated variables differ in slot or sort");
      if (!bind(vL2R, vR2L, o->a, o->b)) return failf("variables map inconsistently");
      if (x->kind == 1) o = ob(OB_REF, x->owner, y->owner, o->next); else o = o->next;
      break;
    }
    case OB_NODE: {
      if (o->a >= L->nn || o->b >= R->nn || !L->nodes[o->a].present || !R->nodes[o->b].present) return failf("a missing node");
      if (nL2R[o->a] >= 0) { if (nL2R[o->a] != o->b) return failf("sharing differs"); o = o->next; break; }
      Node *x = &L->nodes[o->a], *y = &R->nodes[o->b];
      if (strcmp(x->kind, y->kind)) return failf("node kinds differ");
      if (x->ni != y->ni) return failf("item counts differ");
      if (!bind(nL2R, nR2L, o->a, o->b)) return failf("sharing differs");
      Ob *next = o->next;
      if (!strcmp(x->kind, "split")) {
        Ob *sp = ob(OB_SPLIT, 0, 0, next); sp->na = x; sp->nb = y; sp->nr = x->ni / 2;
        sp->ra = palloc(sizeof(int) * (sp->nr + 1)); sp->rb = palloc(sizeof(int) * (sp->nr + 1));
        for (int i = 0; i < sp->nr; i++) { sp->ra[i] = i; sp->rb[i] = i; }
        next = sp;
      } else for (int i = x->ni - 1; i >= 0; i--) {
        Item *p = &x->it[i], *q = &y->it[i];
        if (p->kind != q->kind) return failf("item kinds differ");
        if (p->kind == 'n') next = ob(OB_NODE, p->id, q->id, next);
        else if (p->kind == 'v') next = ob(OB_VAR, p->id, q->id, next);
        else {
          if (p->s.n != q->s.n) return failf("interval, face or level shapes differ");
          Ob *st = ob(OB_SET, 0, 0, next); st->ca = p->s.c; st->cb = q->s.c; st->nr = p->s.n; st->sk = p->kind;
          st->ra = palloc(sizeof(int) * (p->s.n + 1)); st->rb = palloc(sizeof(int) * (p->s.n + 1));
          for (int k = 0; k < p->s.n; k++) { st->ra[k] = k; st->rb[k] = k; }
          next = st;
        }
      }
      next = ob(OB_REF, x->ref, y->ref, next);
      o = next;
      break;
    }
    }
  }
  return 1;
}
static int *negs(int n) { int *a = malloc(sizeof(int) * (n + 1)); for (int i = 0; i <= n; i++) a[i] = -1; return a; }
int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: cellcmp A B\n"); return 2; }
  Dump a = readDump(argv[1]), b = readDump(argv[2]);
  if (a.n != b.n) { printf("cellcmp: %d evals against %d\n", a.n, b.n); return 1; }
  for (int k = 0; k < a.n; k++) {
    L = &a.e[k]; R = &b.e[k];
    if (L->nev != R->nev || memcmp(L->ev, R->ev, sizeof(long) * L->nev)) { printf("cellcmp: eval %d: the event vectors differ\n", k); return 1; }
    nL2R = negs(L->nn); nR2L = negs(R->nn); vL2R = negs(L->nv); vR2L = negs(R->nv); rL2R = negs(L->maxref); rR2L = negs(R->maxref);
    ntrail = 0; why[0] = 0; bestDepth = -1;
    int ok = solve(ob(OB_NODE, L->root, R->root, NULL));
    poolFree(0);
    free(nL2R); free(nR2L); free(vL2R); free(vR2L); free(rL2R); free(rR2L);
    if (!ok) { printf("cellcmp: eval %d: no bijection (%s)\n", k, why); return 1; }
  }
  printf("cellcmp: %d evals equal modulo renaming\n", a.n);
  return 0;
}

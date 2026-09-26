#include <execinfo.h>
#define _GNU_SOURCE
#include <math.h>
#include <sys/mman.h>
/* hyper — cell.c: the heap, frames, and the one loop: the substrate, a cubical type theory whose reduction
 * is demanded (weak head, at the active pair) and in which ua's β-rule reduces.
 * Every rule fires only at an active pair, only when demanded, and appends its receipt to the ledger
 * (research/sat_fibre/InteractionLedger.agda: a Trace of events, interactionTotal its length).  Definitional
 * unfolding (REF) is not counted.  Nothing is erased inside a run; a forgotten port is counted where it is forgotten. */
#include "cell.h"
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Term    *HEAP;  Loc HEAP_LEN = 1;          /* loc 0 is reserved (= "none") */
static Loc HEAP_CAP;
SNode   *CODE;  uint32_t CODE_LEN = 1;
uint32_t *KIDS; uint32_t KIDS_LEN = 0;
int RULE_TRP[256], RULE_HCM[256];
Def     *BOOK;  uint32_t BOOK_LEN = 0;
uint64_t ITRS = 0;
uint32_t *TRACE; uint64_t TRACE_LEN = 0; static uint64_t TRACE_CAP;

/* ---- heap ------------------------------------------------------------- */
Loc alloc(uint32_t n) {
  /* the heap is one reservation, committed lazily by the kernel's paging, so a cell's address never
     changes: every Loc and every pointer into HEAP stays valid for the whole run */
  if (!HEAP) {
    uint64_t want = (uint64_t)1 << 35;                                 /* 2^32 words: every 32-bit Loc */
    for (; want >= ((uint64_t)1 << 28); want >>= 1) {
      void *m = mmap(NULL, want, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
      if (m != MAP_FAILED) { HEAP = m; HEAP_CAP = (Loc)(want / sizeof(Term) > 0xFFFFFFFFu ? 0xFFFFFFFFu : want / sizeof(Term)); break; }
    }
    if (!HEAP) { fprintf(stderr, "hyper: cannot reserve the heap\n"); exit(2); }
    HEAP_LEN = 1;                                                      /* address 0 is never a cell */
  }
  if ((uint64_t)HEAP_LEN + n >= HEAP_CAP) { fprintf(stderr, "hyper: heap exhausted\n"); exit(2); }
  Loc l = HEAP_LEN; HEAP_LEN += n; return l;
}
Term node1(unsigned t, uint32_t e, Term a)                 { Loc l = alloc(2); HEAP[l]=a; HEAP[l+1]=0; return mk(t,e,l); }   /* two words: room for the result once reduced */
Term node2(unsigned t, uint32_t e, Term a, Term b)         { Loc l = alloc(2); HEAP[l]=a; HEAP[l+1]=b; return mk(t,e,l); }
Term node3(unsigned t, uint32_t e, Term a, Term b, Term c) { Loc l = alloc(3); HEAP[l]=a; HEAP[l+1]=b; HEAP[l+2]=c; return mk(t,e,l); }
Term node4(unsigned t, uint32_t e, Term a, Term b, Term c, Term d) { Loc l = alloc(4); HEAP[l]=a; HEAP[l+1]=b; HEAP[l+2]=c; HEAP[l+3]=d; return mk(t,e,l); }
/* a face map (side 0/1) or a substitution (side 2, by the interval `by`) applied to `target` */
Term fce_raw(unsigned side, Term name, Term target, Term by) { return node3(T_FCE, side, name, target, by); }
Term fce3(unsigned side, Loc name, Term target, Term by) { return fce_raw(side, mk(T_IVAR, 0, name), target, by); }

static void print_rec(Term t, int depth);
Loc *TRACE_NODE, *TRACE_HEAP; static Loc CUR_NODE;
uint32_t *TRACE_WORLD; static uint32_t WORLD;         /* the world (side of a superposition) each receipt fired in; 0 the root */
static uint32_t *WPARENT, NWORLD = 1, WCAP;            /* the tree of worlds */                 /* the node under reduction: each receipt names it (a Step's source) */
static void receipt(unsigned rule) {
  ITRS++;
  if (!TRACE) { TRACE_CAP = 1u << 16; TRACE = malloc(TRACE_CAP * sizeof(uint32_t)); TRACE_NODE = malloc(TRACE_CAP * sizeof(Loc)); TRACE_HEAP = malloc(TRACE_CAP * sizeof(Loc)); TRACE_WORLD = malloc(TRACE_CAP * sizeof(uint32_t)); }
  if (TRACE_LEN >= TRACE_CAP) { TRACE_CAP *= 2; TRACE = realloc(TRACE, TRACE_CAP * sizeof(uint32_t)); TRACE_NODE = realloc(TRACE_NODE, TRACE_CAP * sizeof(Loc)); TRACE_HEAP = realloc(TRACE_HEAP, TRACE_CAP * sizeof(Loc)); TRACE_WORLD = realloc(TRACE_WORLD, TRACE_CAP * sizeof(uint32_t)); }
  TRACE[TRACE_LEN] = rule; TRACE_NODE[TRACE_LEN] = CUR_NODE; TRACE_HEAP[TRACE_LEN] = HEAP_LEN; TRACE_WORLD[TRACE_LEN] = WORLD; TRACE_LEN++;
}

/* ---- constructor names --------------------------------------------- */
static const char **CTORS; static uint32_t NCTORS;
CtorInfo CINFO[1 << 16];
static Term LABELS[4096];
Term label_name(uint32_t k) { if (k >= 4096) { fprintf(stderr, "hyper: label too large\n"); exit(2); }
  if (!LABELS[k]) LABELS[k] = node2(T_DIM, 0, 0, 0); return LABELS[k]; }
static int label_of(Loc name) { for (uint32_t k = 0; k < 4096; k++) if (LABELS[k] && loc(LABELS[k]) == name) return (int)k; return -1; }
uint32_t ctor_intern(const char *name, uint32_t arity) {
  (void)arity;
  static const char *builtin[] = { "", "Set","Pi","Sig","Path","Eql","Nat","Bool","Unit","Empty","List","Enum","Num","Glue","Pair","Refl","Cons","Nil","Face","Zer","Suc","True","False","Tt","GFace" };
  for (uint32_t i = 1; i < sizeof builtin / sizeof *builtin; i++) if (!strcmp(builtin[i], name)) return i;
  for (uint32_t i = 0; i < NCTORS; i++) if (!strcmp(CTORS[i], name)) return C_USER_BASE + i;
  CTORS = realloc(CTORS, (NCTORS + 1) * sizeof *CTORS);
  CTORS[NCTORS] = strdup(name);
  return C_USER_BASE + NCTORS++;
}
const char *ctor_name(uint32_t id) {
  static const char *builtin[] = { "", "Set","Pi","Sig","Path","Eql","Nat","Bool","Unit","Empty","List","Enum","Num","Glue","Pair","Refl","Cons","Nil","Face","Zer","Suc","True","False","Tt","GFace" };
  if (id < sizeof builtin / sizeof *builtin) return builtin[id];
  if (id - C_USER_BASE < NCTORS) return CTORS[id - C_USER_BASE];
  return "?";
}
int book_find(const char *name) {
  for (uint32_t i = 0; i < BOOK_LEN; i++) if (!strcmp(BOOK[i].name, name)) return (int)i;
  return -1;
}

/* ---- frames (§2) ------------------------------------------------------ */
/* A frame binds one slot; frames chain by parent; ext holds the depth.     */
/* T_DIM binds a dimension: its loc IS the name.                             */
/* T_RESTRICT records a face taken on everything the closure reads.          */
uint32_t next_depth(Term parent) {
  while (tag(parent) == T_RESTRICT) parent = HEAP[loc(parent)];
  return tag(parent) ? ext(parent) + 1 : 0;
}
Term frame_push(Term parent, Term slot) { return node2(T_FRAME, next_depth(parent), parent, slot); }
Term dim_push(Term parent)              { uint32_t d = next_depth(parent); return node2(T_DIM, d, parent, (Term)d + 1); }
/* a face (side 0/1) or, with side 2, a general substitution of the dimension by the interval `by` */
Term restrict_push(Term parent, Term name, unsigned side, Term by) {
  return node3(T_RESTRICT, side, parent, name, by);
}
static uint32_t frame_depth(Term f) {
  while (tag(f) == T_RESTRICT) f = HEAP[loc(f)];
  return tag(f) ? ext(f) + 1 : 0;   /* number of bindings in scope */
}
/* Look up level `lvl`, wrapping the value in every face taken between here and it. */
bool frame_is_dim(Term f, uint32_t lvl) {
  for (;;) { if (!tag(f)) return false; if (tag(f) == T_RESTRICT) { f = HEAP[loc(f)]; continue; } if (ext(f) == lvl) return tag(f) == T_DIM; f = HEAP[loc(f)]; }
}
Term frame_lookup(Term f, uint32_t lvl, bool *is_dim) {
  Term faces[64]; unsigned nf = 0;
  for (;;) {
    if (!tag(f)) { fprintf(stderr, "hyper: unbound level %u\n", lvl); exit(2); }
    if (tag(f) == T_RESTRICT) { if (nf < 64) faces[nf++] = f; f = HEAP[loc(f)]; continue; }
    if (ext(f) == lvl) break;
    f = HEAP[loc(f)];
  }
  Term v;
  if (tag(f) == T_DIM) { *is_dim = true; v = mk(T_IVAR, 0, loc(f)); }
  else { *is_dim = false; v = mk(T_VAR, lvl, loc(f)); }   /* a VAR reads the slot lazily (§2: forced once, written back) */
  for (unsigned i = nf; i-- > 0;) v = fce_raw(ext(faces[i]), HEAP[loc(faces[i]) + 1], v, HEAP[loc(faces[i]) + 2]);
  return v;
}

/* ---- instantiation: static code → cells over a frame (δ, uncounted) ---- */
Term inst(uint32_t c, Term fr) {
  SNode *n = &CODE[c];
  switch (n->tag) {
    case S_VAR: { bool d; return frame_lookup(fr, n->ext, &d); }
    case S_LAM: return node2(T_LAM, 0, mk(0, 0, c), fr);
    case S_PLM: return node2(T_PLM, 0, mk(0, 0, c), fr);
    case S_DIM: return inst(n->a, dim_push(fr));
    case S_LET: { Term v = inst(n->a, fr); return inst(n->b, frame_push(fr, v)); }
    case S_APP: return node2(T_APP, 0, inst(n->a, fr), inst(n->b, fr));
    case S_REF: { Term r = mk(T_REF, 0, n->ext);
      if (BOOK[n->ext].unknown) { Term faces[64]; unsigned nf = 0;      /* a coordinate is global; a branch's faces must reach it */
        for (Term f = fr; tag(f); f = HEAP[loc(f)]) if (tag(f) == T_RESTRICT && nf < 64) faces[nf++] = f;
        for (unsigned i = nf; i-- > 0;) r = fce_raw(ext(faces[i]), HEAP[loc(faces[i]) + 1], r, HEAP[loc(faces[i]) + 2]); }
      return r; }
    case S_ERA: return mk(T_ERA, 0, 0);
    case S_SUP: { bool d; Term nm = n->d ? inst(n->d, fr) : frame_lookup(fr, n->ext, &d);
                  return node3(T_SUP, 0, nm, inst(n->a, fr), inst(n->b, fr)); }
    case S_FCE: { bool d; Term nm = n->d ? inst(n->d, fr) : frame_lookup(fr, n->a, &d);
                  return fce_raw(n->ext, nm, inst(n->b, fr), 0); }
    case S_ISUB:{ bool d; Term nm = n->d ? inst(n->d, fr) : frame_lookup(fr, n->a, &d);   /* (isub k by T): T[k := by] */
                  return fce_raw(2, nm, inst(n->c, fr), inst(n->b, fr)); }
    case S_LABEL: return mk(T_IVAR, 0, loc(label_name(n->ext)));
    case S_FIX: { Term f = frame_push(fr, 0); HEAP[loc(f)+1] = inst(n->a, f); return HEAP[loc(f)+1]; }   /* μx. body: a knot in the heap */
    case S_OP1: return node1(T_OP1, n->ext, inst(n->a, fr));
    case S_POUT: return node1(T_POUT, 0, inst(n->a, fr));
    case S_REFLECT: return node2(T_REFLECT, 0, inst(n->a, fr), inst(n->b, fr));
    case S_PAP: return node4(T_PAP, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr), inst(n->d, fr));
    case S_ETYPE: return node4(T_ETYPE, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr), inst(n->d, fr));
    case S_ETERM: return node3(T_ETERM, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr));
    case S_I0:  return mk(T_I0, 0, 0);
    case S_I1:  return mk(T_I1, 0, 0);
    case S_IVAR:{ bool d; return frame_lookup(fr, n->ext, &d); }
    case S_INOT: return node1(T_INOT, 0, inst(n->a, fr));
    case S_IAND: return node2(T_IAND, 0, inst(n->a, fr), inst(n->b, fr));
    case S_IOR:  return node2(T_IOR, 0, inst(n->a, fr), inst(n->b, fr));
    case S_CTR: { uint32_t ar = n->ext & 0xFF; Loc l = alloc(ar ? ar : 1);
                  if (ar <= 4) { uint32_t kids[4] = { n->a, n->b, n->c, n->d };
                    for (uint32_t i = 0; i < ar; i++) HEAP[l + i] = inst(kids[i], fr); }
                  else for (uint32_t i = 0; i < ar; i++) HEAP[l + i] = inst(KIDS[n->kids + i], fr);
                  return mk(T_CTR, n->ext, l); }
    case S_HCM: return node3(T_HCM, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr));   /* [type, base, faces] */
    case S_NUM: return node1(T_NUM, n->ext, (Term)n->num);
    case S_OP2: return node2(T_OP2, n->ext, inst(n->a, fr), inst(n->b, fr));
    case S_TRP: return node4(T_TRP, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr), inst(n->d, fr));
    case S_CASE: return node3(T_CASE, 0, inst(n->a, fr), mk(0, 0, c), fr);
    case S_CHK: return node2(T_CHK, 0, inst(n->a, fr), inst(n->b, fr));
    case S_PROJ: return node2(T_PROJ, 0, inst(n->a, fr), inst(n->b, fr));   /* (proj i x): i evaluates to a NUM */
    case S_GLU:  return node2(T_GLU, 0, inst(n->a, fr), inst(n->b, fr));
    case S_GLUE: return node2(T_GLUE, 0, inst(n->a, fr), inst(n->b, fr));
    case S_UNGLUE: return node1(T_UNGLUE, 0, inst(n->a, fr));
    case S_FCASE: return node4(T_FCASE, 0, inst(n->a, fr), inst(n->b, fr), inst(n->c, fr), inst(n->d, fr));
    case S_GBASE: return node1(T_GBASE, 0, inst(n->a, fr));
    case S_GFACES: return node1(T_GFACES, 0, inst(n->a, fr));
    case S_ASK: return node2(T_ASK, 0, inst(n->a, fr), inst(n->b, fr));
    case S_TRACE: return node1(T_TRACE, 0, inst(n->a, fr));
    case S_LEAVES: return node1(T_LEAVES, 0, inst(n->a, fr));
    case S_HELIM: return node4(T_HELIM, 0, n->a ? inst(n->a, fr) : 0, mk(0, 0, c), fr, n->c ? inst(n->c, fr) : mk(T_ERA, 0, 0));
    case S_CFIELDS: return node1(T_CFIELDS, 0, inst(n->a, fr));
    case S_CWITH:   return node2(T_CWITH, 0, inst(n->a, fr), inst(n->b, fr));
    default: fprintf(stderr, "hyper: inst: bad static tag %u\n", n->tag); exit(2);
  }
}

/* ---- the interval (§3.4): the free De Morgan algebra in canonical form ---- */
/* A canonical interval is T_IDNF: ext = number of cubes, block = cubes in order,
 * each cube = [nlits, lits…] with lit = name<<1 | polarity (1 = i, 0 = ~i), lits sorted.
 * I0 = no cubes; I1 = one empty cube.  The antichain is kept by absorption. */
typedef struct { uint32_t n; uint64_t lit[32]; } Cube;
typedef struct { uint32_t n; Cube c[64]; } Dnf;

static int cube_cmp(const void *a, const void *b) {
  const Cube *x = a, *y = b; if (x->n != y->n) return (int)x->n - (int)y->n;
  for (uint32_t i = 0; i < x->n; i++) if (x->lit[i] != y->lit[i]) return x->lit[i] < y->lit[i] ? -1 : 1;
  return 0;
}
static bool cube_subset(const Cube *a, const Cube *b) {   /* a ⊆ b as literal sets ⇒ b absorbed by a */
  uint32_t j = 0;
  for (uint32_t i = 0; i < a->n; i++) { while (j < b->n && b->lit[j] < a->lit[i]) j++; if (j >= b->n || b->lit[j] != a->lit[i]) return false; j++; }
  return true;
}
static bool cube_add_lit(Cube *c, uint64_t l) {          /* false if the cube becomes 0 (i ∧ ~i is NOT 0 on the De Morgan site; only a literal and its negation are kept both) */
  uint32_t i = 0; while (i < c->n && c->lit[i] < l) i++;
  if (i < c->n && c->lit[i] == l) return true;
  if (c->n >= 32) return true;
  for (uint32_t k = c->n; k > i; k--) c->lit[k] = c->lit[k-1];
  c->lit[i] = l; c->n++; return true;
}
static void dnf_norm(Dnf *d) {                            /* sort, dedupe, absorb */
  qsort(d->c, d->n, sizeof(Cube), cube_cmp);
  uint32_t w = 0;
  for (uint32_t i = 0; i < d->n; i++) {
    bool absorbed = false;
    for (uint32_t k = 0; k < w; k++) if (cube_subset(&d->c[k], &d->c[i])) { absorbed = true; break; }
    if (!absorbed) d->c[w++] = d->c[i];
  }
  d->n = w;
}
static Term dnf_term(const Dnf *d) {
  uint32_t words = 0; for (uint32_t i = 0; i < d->n; i++) words += 1 + d->c[i].n;
  Loc l = alloc(words ? words : 1); Loc p = l;
  for (uint32_t i = 0; i < d->n; i++) { HEAP[p++] = d->c[i].n; for (uint32_t k = 0; k < d->c[i].n; k++) HEAP[p++] = d->c[i].lit[k]; }
  return mk(T_IDNF, d->n, l);
}
static void dnf_read(Term t, Dnf *d) {
  d->n = ext(t); Loc p = loc(t);
  for (uint32_t i = 0; i < d->n; i++) { d->c[i].n = (uint32_t)HEAP[p++]; for (uint32_t k = 0; k < d->c[i].n; k++) d->c[i].lit[k] = HEAP[p++]; }
}
static void dnf_or(const Dnf *a, const Dnf *b, Dnf *r) {
  r->n = 0; for (uint32_t i = 0; i < a->n && r->n < 64; i++) r->c[r->n++] = a->c[i];
  for (uint32_t i = 0; i < b->n && r->n < 64; i++) r->c[r->n++] = b->c[i]; dnf_norm(r);
}
static void dnf_and(const Dnf *a, const Dnf *b, Dnf *r) {
  r->n = 0;
  for (uint32_t i = 0; i < a->n; i++) for (uint32_t j = 0; j < b->n && r->n < 64; j++) {
    Cube c = a->c[i]; for (uint32_t k = 0; k < b->c[j].n; k++) cube_add_lit(&c, b->c[j].lit[k]); r->c[r->n++] = c; }
  dnf_norm(r);
}
static void dnf_not(const Dnf *a, Dnf *r) {              /* ~(∨ cubes) = ∧ (∨ ~lit) : product of sums, then DNF */
  r->n = 1; r->c[0].n = 0;                               /* start at I1 */
  for (uint32_t i = 0; i < a->n; i++) {
    Dnf sum; sum.n = 0;
    for (uint32_t k = 0; k < a->c[i].n; k++) { sum.c[sum.n].n = 1; sum.c[sum.n].lit[0] = a->c[i].lit[k] ^ 1; sum.n++; }
    Dnf tmp; dnf_and(r, &sum, &tmp); *r = tmp;
  }
}
static void dnf_subst(const Dnf *a, Loc name, unsigned side, Dnf *r) {   /* i := side */
  r->n = 0;
  for (uint32_t i = 0; i < a->n; i++) {
    Cube c; c.n = 0; bool dead = false;
    for (uint32_t k = 0; k < a->c[i].n; k++) { uint64_t l = a->c[i].lit[k];
      if ((Loc)(l >> 1) == name) { if ((l & 1) != side) { dead = true; break; } continue; }
      c.lit[c.n++] = l; }
    if (!dead && r->n < 64) r->c[r->n++] = c;
  }
  dnf_norm(r);
}
static Term dnf_of(Term t, Dnf *d) {                     /* any interval term → canonical */
  t = whnf(t);
  switch (tag(t)) {
    case T_I0: d->n = 0; return t;
    case T_I1: d->n = 1; d->c[0].n = 0; return t;
    case T_IVAR: d->n = 1; d->c[0].n = 1; d->c[0].lit[0] = ((uint64_t)loc(t) << 1) | 1; return t;
    case T_IDNF: dnf_read(t, d); return t;
    default: d->n = 0; return t;                          /* a neutral interval (a generic): callers treat as undecided */
  }
}
Term iwhnf(Term t) {
  Dnf a, b, r;
  switch (tag(t)) {
    case T_INOT: { Term x = dnf_of(HEAP[loc(t)], &a); if (tag(x) != T_I0 && tag(x) != T_I1 && tag(x) != T_IVAR && tag(x) != T_IDNF) return t;
                   dnf_not(&a, &r); return dnf_term(&r); }
    case T_IAND: { Term x = dnf_of(HEAP[loc(t)], &a), y = dnf_of(HEAP[loc(t)+1], &b);
                   if (!(tag(x) == T_I0 || tag(x) == T_I1 || tag(x) == T_IVAR || tag(x) == T_IDNF)) return t;
                   if (!(tag(y) == T_I0 || tag(y) == T_I1 || tag(y) == T_IVAR || tag(y) == T_IDNF)) return t;
                   dnf_and(&a, &b, &r); return dnf_term(&r); }
    case T_IOR:  { Term x = dnf_of(HEAP[loc(t)], &a), y = dnf_of(HEAP[loc(t)+1], &b);
                   if (!(tag(x) == T_I0 || tag(x) == T_I1 || tag(x) == T_IVAR || tag(x) == T_IDNF)) return t;
                   if (!(tag(y) == T_I0 || tag(y) == T_I1 || tag(y) == T_IVAR || tag(y) == T_IDNF)) return t;
                   dnf_or(&a, &b, &r); return dnf_term(&r); }
    case T_FCE: case T_VAR: case T_APP: case T_CASE: return whnf(t);
    default: return t;
  }
}
/* canonical readback: {} → I0, {{}} → I1, {{i}} → IVAR i */
Term ican(Term t) {
  t = iwhnf(t);
  if (tag(t) != T_IDNF) return t;
  if (ext(t) == 0) return mk(T_I0,0,0);
  if (ext(t) == 1 && HEAP[loc(t)] == 0) return mk(T_I1,0,0);
  if (ext(t) == 1 && HEAP[loc(t)] == 1 && (HEAP[loc(t)+1] & 1)) return mk(T_IVAR, 0, (Loc)(HEAP[loc(t)+1] >> 1));
  return t;
}
bool ieq(Term a, Term b) {                        /* equal canonical intervals */
  a = ican(a); b = ican(b);
  if (tag(a) != tag(b)) return false;
  if (tag(a) == T_IVAR) return loc(a) == loc(b);
  if (tag(a) != T_IDNF) return tag(a) == T_I0 || tag(a) == T_I1;
  Dnf x, y; dnf_read(a, &x); dnf_read(b, &y);
  if (x.n != y.n) return false;
  for (uint32_t i = 0; i < x.n; i++) if (cube_cmp(&x.c[i], &y.c[i])) return false;
  return true;
}
static Term isub_interval(Term t, Loc name, Term by) {
  Dnf a, b, nb, acc, tmp; Term x = dnf_of(t, &a); Term y = dnf_of(by, &b);
  if (!(tag(y) == T_I0 || tag(y) == T_I1 || tag(y) == T_IVAR || tag(y) == T_IDNF)) return fce3(2, name, x, by);
  dnf_not(&b, &nb); acc.n = 0;
  for (uint32_t i = 0; i < a.n; i++) {
    Dnf cube; cube.n = 1; cube.c[0].n = 0; bool pos = false, neg = false;
    for (uint32_t k = 0; k < a.c[i].n; k++) { uint64_t l = a.c[i].lit[k];
      if ((Loc)(l >> 1) == name) { if (l & 1) pos = true; else neg = true; } else cube.c[0].lit[cube.c[0].n++] = l; }
    if (pos) { dnf_and(&cube, &b, &tmp); cube = tmp; }
    if (neg) { dnf_and(&cube, &nb, &tmp); cube = tmp; }
    dnf_or(&acc, &cube, &tmp); acc = tmp;
  }
  return ican(dnf_term(&acc));
}
static Term face_subst_interval(Term t, Loc name, unsigned side) {
  Dnf a, r; Term x = dnf_of(t, &a);
  if (!(tag(x) == T_I0 || tag(x) == T_I1 || tag(x) == T_IVAR || tag(x) == T_IDNF)) return fce3(side, name, x, 0);
  dnf_subst(&a, name, side, &r); return ican(dnf_term(&r));
}

/* the DNF cells of a face formula (Check.faceDNF): I0 → none, I1 → one empty cell; a cube naming both
   endpoints of one dimension is inconsistent and dropped */
int face_cells(Term phi, FaceCell *out, int max) {
  Term c = ican(phi); int n = 0;
  if (tag(c) == T_I0) return 0;
  if (tag(c) == T_I1) { if (max > 0) out[0].n = 0; return 1; }
  if (tag(c) == T_IVAR) { if (max > 0) { out[0].n = 1; out[0].name[0] = loc(c); out[0].side[0] = 1; } return 1; }
  if (tag(c) != T_IDNF) return -1;
  Loc p = loc(c);
  for (uint32_t i = 0; i < ext(c) && n < max; i++) {
    uint32_t nl = (uint32_t)HEAP[p++]; FaceCell *f = &out[n]; f->n = 0; bool ok = true;
    for (uint32_t k = 0; k < nl; k++) { uint64_t l = HEAP[p++]; Loc nm = (Loc)(l >> 1); unsigned sd = (unsigned)(l & 1);
      for (uint32_t j = 0; j < f->n; j++) if (f->name[j] == nm && f->side[j] != sd) ok = false;
      if (f->n < 32) { f->name[f->n] = nm; f->side[f->n] = sd; f->n++; } }
    if (ok) n++;
  }
  return n;
}

/* ---- the face map (§3.1) ------------------------------------------------ */
static bool is_value(Term t) {
  switch (tag(t)) {
    case T_LAM: case T_PLM: case T_SUP: case T_CTR: case T_NUM: case T_ERA: case T_REF: case T_GLU: case T_GLUE:
    case T_I0: case T_I1: case T_IVAR: case T_IDNF: return true;
    default: return false;
  }
}
static Term fce_apply(Term nm, unsigned side, Term by, Term v);
static bool lam_drops(Term f);
static bool is_coordinate(Term v);
static bool blocked(Term s);
static Term case_restrict(Term cs, Term name, unsigned side, Term by, Term scrut);
static Term case_select(Term cs, Term scrut);
static Term helim_restrict(Term he, Term name, unsigned side, Term by, Term scrut, Term motive);
bool CHECK_MODE; bool (*REWRITE_HOOK)(Term old, Term v);

/* push a face map into a closure: record the restriction on its frame */
static Term fce_closure(unsigned ctag, Term name, unsigned side, Term by, Term clo) {
  Term code = HEAP[loc(clo)], fr = HEAP[loc(clo) + 1];
  return node2(ctag, 0, code, restrict_push(fr, name, side, by));
}
/* the face map / substitution at a name: an interval name (faces and interval substitution), a choice
   name (endpoints and renaming), a coordinate (a VAR atom: substitution by a term), or, under the
   checker's hook, any cell (a semantic rewrite: what equals `nm` becomes `by`) */
static Term FCE_SELF;                                   /* the face node being reduced: a face that waits is that node again, not a copy */
static Term fce_apply(Term nm, unsigned side, Term by, Term v) {
  bool ivar = tag(nm) == T_IVAR; Loc name = loc(nm); Term self = FCE_SELF; FCE_SELF = 0;
  #define FCE_(x) fce_raw(side, nm, (x), by)
  #define WAIT_(x) (self && HEAP[loc(self)+1] == (x) && HEAP[loc(self)] == nm && ext(self) == side ? self : FCE_(x))
  if (CHECK_MODE) { Term args[64]; uint32_t n; Term h = spine(v, args, &n);   /* the checker's substitution passes through a neutral spine headed by a definition */
    if (tag(h) == T_REF && n > 0 && (ivar || tag(nm) == T_VAR)) { receipt(R_DUP_NODE); for (uint32_t i = 0; i < n; i++) args[i] = FCE_(args[i]); return whnf(apps(h, args, n)); } }
  v = whnf(v);                                                        /* the runtime's face meets a value: every rule below is at an active pair */
  if (!ivar && tag(nm) != T_VAR && REWRITE_HOOK && REWRITE_HOOK(nm, v)) { receipt(R_DUP_SUP_EQUAL); return whnf(by); }
  switch (tag(v)) {
    case T_SUP: {
      Term sn = whnf(HEAP[loc(v)]);
      if (ivar && tag(sn) == T_IVAR && loc(sn) == name) {
        receipt(R_DUP_SUP_EQUAL);
        if (side < 2) { Term r = whnf(HEAP[loc(v) + 1 + side]);
          while (tag(r) == T_SUP && tag(whnf(HEAP[loc(r)])) == T_IVAR && loc(whnf(HEAP[loc(r)])) == name) r = whnf(HEAP[loc(r) + 1 + side]);   /* the same name again inside: already decided */
          return r; }
        Term b = ican(by);                           /* a choice name admits endpoints and renaming only */
        if (tag(b) == T_I0) return whnf(HEAP[loc(v) + 1]);
        if (tag(b) == T_I1) return whnf(HEAP[loc(v) + 2]);
        if (tag(b) == T_IVAR) return node3(T_SUP, 0, b, HEAP[loc(v) + 1], HEAP[loc(v) + 2]);
        fprintf(stderr, "hyper: connection on a choice name\n"); exit(2);
      }
      receipt(R_DUP_SUP_DIFFERENT);                       /* δᵢδⱼ = δⱼδᵢ */
      return node3(T_SUP, 0, sn, FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]));
    }
    case T_LAM: receipt(lam_drops(v) ? R_DUP_LAM_ERASED : R_DUP_LAM_USED); return fce_closure(T_LAM, nm, side, by, v);
    case T_PLM: receipt(R_DUP_LAM_USED); return fce_closure(T_PLM, nm, side, by, v);
    case T_IVAR: if (ivar && loc(v) == name) { receipt(R_DUP_SUP_EQUAL); return side < 2 ? mk(side ? T_I1 : T_I0, 0, 0) : iwhnf(by); }
                 receipt(R_FCE_SHARE); return v;
    case T_IDNF: if (!ivar) { receipt(R_FCE_SHARE); return v; }
                 receipt(R_DUP_SUP_EQUAL); return side < 2 ? face_subst_interval(v, name, side) : isub_interval(v, name, by);
    case T_INOT: case T_IAND: case T_IOR: {           /* a neutral interval formula: canonicalise if possible, else pass inside */
      Term w = iwhnf(v);
      if (tag(w) != tag(v)) return fce_apply(nm, side, by, w);
      receipt(R_DUP_NODE);
      if (tag(v) == T_INOT) return whnf(node1(T_INOT, 0, FCE_(HEAP[loc(v)])));
      return whnf(node2(tag(v), 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]))); }
    case T_VAR: if (tag(nm) == T_VAR && loc(v) == loc(nm)) { receipt(R_DUP_SUP_EQUAL); return side < 2 ? mk(side ? T_I1 : T_I0, 0, 0) : whnf(by); }   /* the coordinate itself */
                if (is_coordinate(v)) return WAIT_(v);                                                 /* a coordinate with no value yet: the face waits for it */
                receipt(R_FCE_SHARE); return v;                                                        /* another atom */
    case T_CTR: {
      uint32_t ar = ctr_arity(v);
      if (ar == 0) { receipt(R_FCE_SHARE); return v; }
      receipt(R_DUP_NODE);
      Loc l = alloc(ar);
      for (uint32_t i = 0; i < ar; i++) HEAP[l+i] = FCE_(HEAP[loc(v)+i]);
      return mk(T_CTR, ext(v), l);
    }
    case T_GLU: case T_GLUE: { receipt(R_DUP_NODE);   /* a face may decide the Glue: reduce again */
      return whnf(node2(tag(v), 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]))); }
    case T_NUM: case T_ERA: case T_REF: case T_I0: case T_I1: receipt(R_FCE_SHARE); return v;
    /* a substitution commutes with everything: it passes into a stuck spine or a canonical composite */
    case T_APP:  receipt(R_DUP_NODE); return whnf(node2(T_APP, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
    case T_CASE: if (!CHECK_MODE && blocked(v)) return WAIT_(v);    /* blocked on a coordinate: the face waits on the one shared cell */
                 receipt(R_DUP_NODE); return whnf(case_restrict(v, nm, side, by, FCE_(HEAP[loc(v)])));
    case T_HELIM: receipt(R_DUP_NODE);
      return whnf(helim_restrict(v, nm, side, by, HEAP[loc(v)] ? FCE_(HEAP[loc(v)]) : 0, FCE_(HEAP[loc(v)+3])));
    case T_TRP:  receipt(R_DUP_NODE); return whnf(node4(T_TRP, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_PAP:  receipt(R_DUP_NODE); return whnf(node4(T_PAP, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_FCASE: receipt(R_DUP_NODE); return whnf(node4(T_FCASE, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_REFLECT: receipt(R_DUP_NODE); return whnf(node2(T_REFLECT, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
    case T_HCM:  receipt(R_DUP_NODE); return whnf(node3(T_HCM, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2])));
    case T_OP2:  receipt(R_DUP_NODE); return whnf(node2(T_OP2, ext(v), FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
    case T_UNIFY: receipt(R_DUP_NODE); return whnf(node3(T_UNIFY, ext(v), FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), side < 2 ? restrict_push(HEAP[loc(v)+2], nm, side, 0) : HEAP[loc(v)+2]));
    case T_BOTH:  receipt(R_DUP_NODE); return whnf(node4(T_BOTH, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), HEAP[loc(v)+2], side < 2 ? restrict_push(HEAP[loc(v)+3], nm, side, 0) : HEAP[loc(v)+3]));
    case T_OP1:  receipt(R_DUP_NODE); return whnf(node1(T_OP1, ext(v), FCE_(HEAP[loc(v)])));
    case T_POUT: receipt(R_DUP_NODE); return whnf(node1(T_POUT, 0, FCE_(HEAP[loc(v)])));
    case T_PROJ: receipt(R_DUP_NODE); return whnf(node2(T_PROJ, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
    case T_UNGLUE: receipt(R_DUP_NODE); return whnf(node1(T_UNGLUE, 0, FCE_(HEAP[loc(v)])));
    case T_FCE: {                                    /* a face already waiting on a stuck term: at the same name the earlier face has spent it; at another, both wait */
      Term inner = whnf(HEAP[loc(v)]);
      if (ivar && tag(inner) == T_IVAR && loc(inner) == name && ext(v) < 2) { receipt(R_DUP_SUP_EQUAL); return v; }
      return WAIT_(v); }
    default: /* stuck: the face map waits */ return WAIT_(v);
  }
  #undef FCE_
  #undef WAIT_
}

/* ---- opening a closure (β, path application) --------------------------- */
Term open_closure(Term clo, Term arg) {
  uint32_t code = loc(HEAP[loc(clo)]);
  Term fr = HEAP[loc(clo) + 1];
  SNode *n = &CODE[code];                 /* S_LAM / S_PLM: body is n->a */
  return inst(n->a, frame_push(fr, arg));
}

/* ---- §3.3 erase at the projection ------------------------------------------------------------ */
/* Nothing is erased inside a run: a datum that falls out of reach stays in the arena, retained free.
   What is counted is a forgotten PORT, one row each: the other fields of a projected constructor, the
   fields a branch does not carry into its body, the free variables of the branches a match drops, the
   argument of a lambda whose body ignores its binder, the ports a printer cuts.  Which ports a binder
   drops is a property of its code, so it is computed once and kept on the node (num: key+1 << 32 | count). */
static void erase_ports(uint64_t k) { while (k--) receipt(R_ERASE); }
static bool memo_get(SNode *n, uint32_t key, uint64_t *out) { if ((n->num >> 32) != (uint64_t)key + 1) return false; *out = n->num & 0xFFFFFFFFu; return true; }
static void memo_put(SNode *n, uint32_t key, uint64_t v) { n->num = ((uint64_t)key + 1) << 32 | (v & 0xFFFFFFFFu); }
static bool lam_drops(Term clo) {                     /* the argument's port, when the body never reads the binder */
  SNode *n = &CODE[loc(HEAP[loc(clo)])]; uint32_t lvl = next_depth(HEAP[loc(clo) + 1]); uint64_t v;
  if (!memo_get(n, lvl, &v)) { v = !code_uses(n->a, lvl); memo_put(n, lvl, v); }
  return v;
}
/* the ports a selected branch drops: its own fields (levels base.. for the constructor's fields from `first`)
   that its body never reads, and every term level below base some other branch reads and this one does not */
static uint64_t branch_drops(uint32_t first_br, uint32_t br, Term fr, uint32_t first, uint32_t ar) {
  SNode *b = &CODE[br]; uint32_t base = next_depth(fr); uint64_t v;
  if (memo_get(b, base, &v)) return v;
  v = 0;
  for (uint32_t i = first; i < ar; i++) if (!code_uses(b->b, base + i - first)) v++;
  for (uint32_t l = 0; l < base; l++) {
    if (frame_is_dim(fr, l) || code_uses(b->b, l)) continue;
    for (uint32_t o = first_br; o; o = CODE[o].c) if (o != br && code_uses(CODE[o].b, l)) { v++; break; }
  }
  memo_put(b, base, v); return v;
}

/* ---- a coordinate asked by a match ---------------------------------------------------------------------
   A coordinate is a generic element: a slot that points to itself.  When an eliminator asks it which
   constructor it is, it becomes the superposition of the constructors the eliminator lists, each with fresh
   coordinates for its fields, written into its own slot so that every holder of the coordinate sees the same
   correlated superposition; the match then commutes over it by the ordinary rule and each side carries the
   face that decided it.  Nothing here names a type: the constructors are the eliminator's own branches. */
/* a run-time coordinate: a declared unknown or a field of one.  Its frame is marked (level 0xFFFFFF) and carries its
   type in a third word; the presentation's and the checker's generic elements are not marked and are never split. */
/* a coordinate: a slot pointing at itself, its type, and the world (faces) it lives in, so that a binding made under
   faces of that world is written plainly and a binding under the opposite side of one of them is an empty world */
static Term coordinate_in(Term type, Term world) { Loc l = alloc(4); HEAP[l] = 0; HEAP[l+1] = mk(T_VAR, 0xFFFFFF, l); HEAP[l+2] = type; HEAP[l+3] = world; return HEAP[l+1]; }
Term coordinate(Term type) { return coordinate_in(type, 0); }
static int world_side(Term world, Loc name) { for (Term f = world; tag(f); f = HEAP[loc(f)]) if (loc(whnf(HEAP[loc(f)+1])) == name) return (int)ext(f); return -1; }
static bool is_coordinate(Term v) { return tag(v) == T_VAR && ext(v) == 0xFFFFFF && tag(HEAP[loc(v)+1]) == T_VAR && loc(HEAP[loc(v)+1]) == loc(v); }
Term coordinate_type(Term v) { return HEAP[loc(v)+2]; }
/* the constructors of a data type, from its declaration alone: every constructor whose declared type ends in T, each
   with fresh coordinates for its fields, typed by that declaration at T's parameters, living in `world`.  Nothing is
   per type.  A type with a path constructor has no such list (0). */
/* a point of a constructor: its fields fresh coordinates of `world`, typed by the constructor's declaration at the
   parameters of T (fresh coordinates of their own types when no T is given, carried as leading fields when the type
   carries them); a constructor of no declared type has `ar` untyped fields */
static Term ctor_point(uint32_t cid, uint32_t ar, Term T, Term world) {
  uint32_t hid = CINFO[cid].hit;
  if (!hid || CINFO[cid].dim) { Loc l = alloc(ar ? ar : 1); for (uint32_t i = 0; i < ar; i++) HEAP[l+i] = coordinate_in(0, world); return mk(T_CTR, ctr_ext(cid, ar), l); }
  uint32_t np = CINFO[hid].nparams, carried = CINFO[hid].carries ? np : 0, nf = CINFO[cid].nfields;
  Term ty = inst(BOOK[CINFO[cid].type_def].code, 0); Loc l = alloc(carried + nf ? carried + nf : 1);
  for (uint32_t i = 0; i < np; i++) { ty = whnf(ty); if (tag(ty) != T_CTR || ctr_id(ty) != C_PI) return 0;
    Term par = T ? HEAP[loc(T)+i] : coordinate_in(HEAP[loc(ty)], world); if (i < carried) HEAP[l+i] = par; ty = app2(HEAP[loc(ty)+1], par); }
  for (uint32_t i = 0; i < nf; i++) { ty = whnf(ty); if (tag(ty) != T_CTR || ctr_id(ty) != C_PI) return 0;
    HEAP[l+carried+i] = coordinate_in(HEAP[loc(ty)], world); ty = app2(HEAP[loc(ty)+1], HEAP[l+carried+i]); }
  return mk(T_CTR, ctr_ext(cid, carried + nf), l);
}
uint32_t type_constructors(Term T, Term *alts, uint32_t max, Term world) {
  T = whnf(T); if (tag(T) != T_CTR) return 0; uint32_t id = ctr_id(T); if (!CINFO[id].is_hit) return 0; uint32_t k = 0;
  for (uint32_t c = 1; c < C_USER_BASE + NCTORS && k < max; c++) {
    if (c == id || CINFO[c].hit != id) continue; if (CINFO[c].dim) return 0;
    Term a = ctor_point(c, 0, T, world); if (!a) return 0; alts[k++] = a; }
  return k;
}
/* the constructors a match lists, as points of `world`: the type of a point no declaration types */
static uint32_t case_points(Term cs, Term *alts, Term world) {
  uint32_t code = loc(HEAP[loc(cs)+1]); uint32_t k = 0;
  for (uint32_t br = CODE[code].b; br && k < 64; br = CODE[br].c) { SNode *b = &CODE[br]; if (b->ext == 0xFFFFFF) continue; alts[k++] = ctor_point(b->ext, b->a, 0, world); }
  if (k == 0) { fprintf(stderr, "hyper: a match with no constructor asked a point\n"); exit(3); }
  return k;
}
/* a coordinate of a Σ type asked for its value is a pair of coordinates, the second typed at the first */
static Term sigma_split(Term T, Term world) {
  Term a = coordinate_in(HEAP[loc(T)], world); Term b = coordinate_in(app2(HEAP[loc(T)+1], a), world);
  return node2(T_CTR, ctr_ext(C_PAIR, 2), a, b);
}
/* unification: the identity type between two data terms, decided.  REFL when the terms can be made equal by binding
   coordinates, ERA when constructors or numerals disagree, a superposition of these when a side is superposed (each
   side face-mapped into its branch), 0 when a side is neutral and nothing decides.  A binding made inside a branch is
   written as a superposition correlated with that branch, the other side a fresh coordinate, so every holder of the
   coordinate sees the binding exactly where it holds. */
static Term refl_cell(void) { return mk(T_CTR, ctr_ext(C_REFL, 0), alloc(1)); }
static bool refers(Term from, Loc target, int depth); static void cycle_trap(const char *where, Term cell, Term newv);
/* inspection (the fibre law at a match).  The scrutinee of a match and the sides of an identity are INSPECTED, not
   forced: evaluation runs through β and constructor selection and stops at a match facing a point whose head is not
   yet a constructor.  Binding that point's output is the act of what faces it, never of the inspection. */
static int INSPECT;
static Term inspect(Term t) { INSPECT++; Term r = whnf(t); INSPECT--; return r; }
/* a small map from pairs of words to a term, for the questions the machine asks once */
typedef struct { uint64_t k1, k2; Term v; } MemoCell; static MemoCell *MEMO; static uint32_t MEMO_N;
static Term *memo_slot(uint64_t k1, uint64_t k2) {
  if (!MEMO) MEMO = calloc(1u << 20, sizeof *MEMO);
  uint32_t h = (uint32_t)((k1 * 0x9E3779B97F4A7C15ull ^ k2 * 0xC2B2AE3D27D4EB4Full) >> 44);
  for (;;) { MemoCell *c = &MEMO[h & ((1u << 20) - 1)];
    if (!c->v) { c->k1 = k1; c->k2 = k2; MEMO_N++; return &c->v; }
    if (c->k1 == k1 && c->k2 == k2) return &c->v;
    h++; }
}
/* the identity of a term as a question's part: a coordinate by its cell, a constant by its value, a function by its
   code and the identities of what its frame holds (its own fixed point counted as itself), a stuck match by its
   question; anything else has none */
static Term peel(Term v, Term *faces); static Term frame_faces(Term fr); static int frame_side(Term fr, Loc name);
static bool question_key_d(Term s, int depth, uint64_t *k1, uint64_t *k2); static bool known_split(Term s, Term faces); static Term split_stuck(Term s, Term cs);
static Term KEY_FACES, KEY_FRAME;                        /* the faces (and the frame's restrictions) an identity is read under: a superposed slot is its side there */
static Term frame_slot_raw(Term f, uint32_t lvl) { for (;;) { if (tag(f) == T_RESTRICT) { f = HEAP[loc(f)]; continue; } if (ext(f) == lvl) return HEAP[loc(f)+1]; f = HEAP[loc(f)]; } }
static bool term_identity(Term v, int depth, uint64_t *id) {
  if (depth < 0) return false;
  v = inspect(v);
  for (;;) { Term q = 0; v = peel(v, &q);                            /* a port under waiting faces is the port */
    if (tag(v) != T_SUP) break; Term nm = whnf(HEAP[loc(v)]); if (tag(nm) != T_IVAR) break;
    int w = world_side(KEY_FACES, loc(nm)); if (w < 0) w = frame_side(KEY_FRAME, loc(nm));
    if (w < 0) break; v = inspect(HEAP[loc(v) + 1 + w]); }
  if (is_coordinate(v)) { *id = (uint64_t)loc(v) << 8 | 1; return true; }
  if (tag(v) == T_CTR && ctr_arity(v) == 0) { *id = (uint64_t)ctr_id(v) << 8 | 2; return true; }
  if (tag(v) == T_NUM) { *id = HEAP[loc(v)] << 8 | 3; return true; }
  if (tag(v) == T_REF) { *id = (uint64_t)loc(v) << 8 | 4; return true; }
  if (tag(v) == T_LAM || tag(v) == T_PLM) { uint32_t code = loc(HEAP[loc(v)]); uint64_t h = (uint64_t)code << 8 | 6; if (depth <= 0) { *id = h; return true; }
    for (Term f = HEAP[loc(v)+1]; tag(f); f = HEAP[loc(f)]) { if (tag(f) == T_RESTRICT || !code_uses(code, ext(f))) continue;   /* only what the body reads */
      if (tag(f) == T_DIM) return false;
      Term w = HEAP[loc(f)+1]; uint64_t sub;
      if (tag(w) == T_LAM && loc(HEAP[loc(w)]) == code) sub = 7; else if (!term_identity(w, depth - 1, &sub)) return false;
      h = (h ^ sub) * 0xC2B2AE3D27D4EB4Full; }
    *id = h; return true; }
  if (tag(v) == T_CASE) { uint64_t a, b; if (!question_key_d(v, depth - 1, &a, &b)) return false; *id = a ^ (b << 1); return true; }
  *id = (uint64_t)loc(v) << 8 | 5; return true;                        /* anything else: by its cell */
}
static uint64_t arg_identity(Term x) { uint64_t id; if (term_identity(x, 3, &id)) return id; return (uint64_t)loc(inspect(x)) << 8 | 5; }
/* an unknown function applied: the coordinate of its codomain at the argument.  The same argument asks the same
   question, so the coordinate is one per (function, argument): a free port fires once. */
static Term pi_apply(Term f, Term x) {
  Term T = coordinate_type(f); if (!T) return 0; T = whnf(T);
  if (tag(T) != T_CTR || ctr_id(T) != C_PI) return 0;
  Term *slot = memo_slot(loc(f), arg_identity(x));
  if (!*slot) *slot = coordinate_in(app2(HEAP[loc(T)+1], x), 0);
  return *slot;
}
/* the coordinate under a chain of waiting faces, the faces collected onto `faces` */
static Term peel(Term v, Term *faces) {
  Term w = v; while (tag(w) == T_FCE && ext(w) < 2 && tag(HEAP[loc(w)]) == T_IVAR) w = inspect(HEAP[loc(w)+1]);
  if (!is_coordinate(w)) return v;                                    /* only a coordinate's faces are collected; anything else keeps them */
  while (tag(v) == T_FCE) { *faces = restrict_push(*faces, HEAP[loc(v)], ext(v), 0); v = inspect(HEAP[loc(v)+1]); }
  return v;
}
static bool proof_cell(Term t) { return tag(t) == T_UNIFY || tag(t) == T_BOTH; }
static bool proof_case(Term s) { return tag(s) == T_CASE && proof_cell(inspect(HEAP[loc(s)])); }   /* a match on an undecided identity: its one branch is Refl */
static Term refl_body(Term cs);
/* a match on an identity, possibly under waiting faces: the identity and the branch, each under the same faces */
static bool under_faces(Term s, Term *p, Term *v) {
  Term chain[64]; unsigned n = 0; Term w = s;
  while (tag(w) == T_FCE && n < 64) { chain[n++] = w; w = inspect(HEAP[loc(w)+1]); }
  if (!proof_case(w)) return false;
  *p = HEAP[loc(w)]; *v = refl_body(w);
  for (unsigned i = n; i-- > 0;) { *p = fce_raw(ext(chain[i]), HEAP[loc(chain[i])], *p, HEAP[loc(chain[i])+2]); *v = fce_raw(ext(chain[i]), HEAP[loc(chain[i])], *v, HEAP[loc(chain[i])+2]); }
  return true;
}
static bool blocked(Term s) {                                          /* stuck on a coordinate along its spine */
  for (int i = 0; i < 64; i++) switch (tag(s)) {
    case T_VAR: return is_coordinate(s);
    case T_CASE: case T_APP: case T_OP1: case T_POUT: case T_UNGLUE: s = HEAP[loc(s)]; break;
    case T_FCE: case T_PROJ: s = HEAP[loc(s)+1]; break;
    case T_OP2: s = is_value(HEAP[loc(s)]) ? HEAP[loc(s)+1] : HEAP[loc(s)]; break;
    case T_UNIFY: case T_BOTH: return true;
    default: return false;
  }
  return false;
}
/* a point whose head is not yet a constructor, forced: bound at its output by the match facing it (below); a bare
   coordinate is not forced here, the match facing it splits it */
static Term force(Term v) {
  Term w = v; while (tag(w) == T_FCE) w = whnf(HEAP[loc(w)+1]);
  if (is_coordinate(w) || !blocked(w)) return v;
  Term r = whnf(w); return r == w ? v : whnf(v);
}
/* a binding made under the faces of a branch is written as a superposition correlated with that branch, the other
   side of each face a fresh coordinate, so every holder of the coordinate sees the binding exactly where it holds */
static Term BIND_FS[64]; static unsigned BIND_N; static Term BIND_T;
static Term bind_wrap(Term v, unsigned i, Term world) {   /* outermost face first, each other side a coordinate of its world */
  if (i == BIND_N) return v;
  Term f = BIND_FS[i], nm = HEAP[loc(f)+1]; unsigned side = ext(f);
  Term in = bind_wrap(v, i + 1, restrict_push(world, nm, side, 0)), out = coordinate_in(BIND_T, restrict_push(world, nm, !side, 0));
  return node3(T_SUP, 0, nm, side ? out : in, side ? in : out);
}
static Term bind_under(Term c, Term v, Term faces) {
  Term world = HEAP[loc(c)+3]; BIND_N = 0; BIND_T = coordinate_type(c);
  for (Term f = faces; tag(f) && BIND_N < 64; f = HEAP[loc(f)]) {   /* a face of the coordinate's own world is already in force; one face per name */
    Loc name = loc(whnf(HEAP[loc(f)+1])); int w = world_side(world, name);
    if (w >= 0) { if ((unsigned)w != ext(f)) return mk(T_ERA, 0, 0); continue; }
    unsigned i = 0; for (; i < BIND_N; i++) if (loc(whnf(HEAP[loc(BIND_FS[i])+1])) == name) break;
    if (i < BIND_N) { if (ext(BIND_FS[i]) != ext(f)) return mk(T_ERA, 0, 0); continue; }
    BIND_FS[BIND_N++] = f; }
  { Term w = bind_wrap(v, 0, world); if (getenv("HYPER_BT") && refers(w, loc(c), 8)) { fprintf(stderr, "[cycle at bind]\n"); void *bt[40]; int n = backtrace(bt, 40); backtrace_symbols_fd(bt, n, 2); exit(7); } HEAP[loc(c) + 1] = w; } return refl_cell();
}
static bool mentions(Term t, Loc c, int depth) {
  if (depth <= 0) return false; t = inspect(t);
  if (tag(t) == T_VAR) return loc(t) == c;
  if (tag(t) == T_CTR) { for (uint32_t i = 0; i < ctr_arity(t); i++) if (mentions(HEAP[loc(t)+i], c, depth-1)) return true; return false; }
  if (tag(t) == T_SUP) return mentions(HEAP[loc(t)+1], c, depth-1) || mentions(HEAP[loc(t)+2], c, depth-1);
  return false;
}
static Term faces_cat(Term a, Term b) { for (Term f = b; tag(f); f = HEAP[loc(f)]) if (world_side(a, loc(whnf(HEAP[loc(f)+1]))) < 0) a = restrict_push(a, HEAP[loc(f)+1], ext(f), 0); return a; }
/* an identity read in a world: its faces extended, its sides under them (thin, they wait on what is stuck) */
static Term restrict_proof(Term p, Term W) {
  if (!tag(W)) return p;
  if (tag(p) == T_UNIFY) { Term x = HEAP[loc(p)], y = HEAP[loc(p)+1], own = HEAP[loc(p)+2]; bool any = false;
    for (Term f = W; tag(f); f = HEAP[loc(f)]) { if (world_side(own, loc(whnf(HEAP[loc(f)+1]))) >= 0) continue;   /* only faces it does not already have */
      any = true; x = fce_raw(ext(f), HEAP[loc(f)+1], x, 0); y = fce_raw(ext(f), HEAP[loc(f)+1], y, 0); }
    return any ? node3(T_UNIFY, ext(p), x, y, faces_cat(own, W)) : p; }
  if (tag(p) == T_BOTH) return node4(T_BOTH, 0, restrict_proof(HEAP[loc(p)], W), restrict_proof(HEAP[loc(p)+1], W), HEAP[loc(p)+2], faces_cat(HEAP[loc(p)+3], W));
  return p;
}
static bool refers(Term from, Loc target, int depth) {   /* does `from` reach the cell `target` through sides, scrutinees, applications, variables and conjunctions */
  if (depth <= 0) return false;
  if (loc(from) == target && (tag(from) == T_UNIFY || tag(from) == T_CASE || tag(from) == T_BOTH)) return true;
  switch (tag(from)) {
    case T_UNIFY: case T_CASE: case T_APP: if (tag(HEAP[loc(from)]) == T_IND) return refers(HEAP[loc(from)+1], target, depth - 1); return refers(HEAP[loc(from)], target, depth - 1) || (tag(from) != T_CASE && refers(HEAP[loc(from)+1], target, depth - 1));
    case T_BOTH: return refers(HEAP[loc(from)], target, depth - 1) || refers(HEAP[loc(from)+1], target, depth - 1);
    case T_FCE: return refers(HEAP[loc(from)+1], target, depth - 1);
    case T_VAR: { Term v = HEAP[loc(from)+1]; if (tag(v) == T_VAR && loc(v) == loc(from)) return false; return refers(v, target, depth - 1); }
    default: return false;
  }
}
static void cycle_trap(const char *where, Term cell, Term newv) {
  if (!getenv("HYPER_BT")) return;
  if (refers(newv, loc(cell), 6)) { fprintf(stderr, "[cycle at %s]\n", where); void *bt[40]; int n = backtrace(bt, 40); backtrace_symbols_fd(bt, n, 2); exit(7); }
}
static void cycle_trap(const char *where, Term cell, Term newv);
static Term unify_cell(Term x, Term y, Term faces) { return node3(T_UNIFY, 0, x, y, faces); }
static Term both_cell(Term p, Term q, Term faces) { return node4(T_BOTH, 0, p, q, 0, faces); }   /* [p, q, which side was forced last, the faces it lives under] */
/* v under the identity p: the language's own J, `under` in the prelude */
static int under_id(void) { static int id = -1; if (id < 0) id = book_find("under"); return id; }
static Term under(Term p, Term v) { return app2(app2(ref_of(under_id()), p), v); }
static uint32_t under_case(void) {                       /* the code of under's own match, to know it when met */
  static uint32_t c = 0; if (!c) { uint32_t k = BOOK[under_id()].code; while (CODE[k].tag == S_LAM || CODE[k].tag == S_DIM) k = CODE[k].a; c = k; } return c;
}
static Term refl_body(Term cs) { return case_select(cs, refl_cell()); }
/* unification: the identity type between two data terms, decided.  REFL when the terms can be made equal by binding
   coordinates, ERA when constructors or numerals disagree, a superposition of these when a side is superposed (each
   side face-mapped into its branch), a match on an identity commuted to a conjunction, and otherwise a wait; a
   side stuck on a coordinate is the term's: the match facing the coordinate splits it. */
static Term unify_step(Term t) {
  for (;;) {
    Term faces = HEAP[loc(t)+2], fx = faces, fy = faces;
    Term x0 = inspect(HEAP[loc(t)]), y0 = inspect(HEAP[loc(t)+1]);
    Term x = peel(x0, &fx), y = peel(y0, &fy);
    if (tag(x) == T_ERA || tag(y) == T_ERA) return mk(T_ERA, 0, 0);
    if (tag(x0) == T_SUP || tag(y0) == T_SUP) { bool xs = tag(x0) == T_SUP; Term sp = xs ? x0 : y0, ot = xs ? y0 : x0; Term nm = whnf(HEAP[loc(sp)]);
      receipt(R_UNIFY);
      int w = tag(nm) == T_IVAR ? world_side(faces, loc(nm)) : -1;    /* the name already fixed by this identity's faces: that side alone */
      if (w >= 0) { HEAP[loc(t) + (xs ? 0 : 1)] = HEAP[loc(sp) + 1 + w]; HEAP[loc(t) + (xs ? 1 : 0)] = fce_raw((unsigned)w, nm, ot, 0); continue; }
      Term a = xs ? unify_cell(HEAP[loc(sp)+1], fce_raw(0, nm, ot, 0), restrict_push(faces, nm, 0, 0)) : unify_cell(fce_raw(0, nm, ot, 0), HEAP[loc(sp)+1], restrict_push(faces, nm, 0, 0));
      Term b = xs ? unify_cell(HEAP[loc(sp)+2], fce_raw(1, nm, ot, 0), restrict_push(faces, nm, 1, 0)) : unify_cell(fce_raw(1, nm, ot, 0), HEAP[loc(sp)+2], restrict_push(faces, nm, 1, 0));
      return node3(T_SUP, 0, nm, a, b); }
    { Term p, v;                                                       /* (v under p) ≡ y  is  p ∧ v ≡ y */
      if (under_faces(x0, &p, &v)) { receipt(R_UNIFY); return both_cell(restrict_proof(p, faces), unify_cell(v, y0, faces), faces); }
      if (under_faces(y0, &p, &v)) { receipt(R_UNIFY); return both_cell(restrict_proof(p, faces), unify_cell(x0, v, faces), faces); } }
    bool cx = is_coordinate(x), cy = is_coordinate(y);
    if (cx && cy && loc(x) == loc(y)) return refl_cell();
    if (cx) { receipt(R_UNIFY); if (mentions(y, loc(x), 64)) return mk(T_ERA, 0, 0); return bind_under(x, y0, fx); }
    if (cy) { receipt(R_UNIFY); if (mentions(x, loc(y), 64)) return mk(T_ERA, 0, 0); return bind_under(y, x0, fy); }
    if (tag(x) == T_CTR && tag(y) == T_CTR) { receipt(R_UNIFY);
      if (ctr_id(x) != ctr_id(y) || ctr_arity(x) != ctr_arity(y)) return mk(T_ERA, 0, 0);
      uint32_t ar = ctr_arity(x); if (ar == 0) return refl_cell();
      Term r = unify_cell(HEAP[loc(x)+ar-1], HEAP[loc(y)+ar-1], faces);
      for (uint32_t i = ar - 1; i-- > 0;) r = both_cell(unify_cell(HEAP[loc(x)+i], HEAP[loc(y)+i], faces), r, faces);
      return r; }
    if (tag(x) == T_NUM && tag(y) == T_NUM) { receipt(R_UNIFY); return (ext(x) == ext(y) && HEAP[loc(x)] == HEAP[loc(y)]) ? refl_cell() : mk(T_ERA, 0, 0); }
    if (INSPECT == 0) {                                                /* forced: a side whose head is not yet a constructor is bound at its output */
      if (blocked(x0) && known_split(x, faces)) continue;              /* the point is split already: its worlds */
      if (blocked(y0) && known_split(y, faces)) continue;
      Term x2 = force(x0), y2 = x2 == x0 ? force(y0) : y0;             /* the term's order: an identity's sides are not two independent demands, a dead one ends the other */
      if (x2 != x0) { HEAP[loc(t)] = x2; continue; }
      if (y2 != y0) { HEAP[loc(t)+1] = y2; continue; } }
    cycle_trap("unify x", t, x0); cycle_trap("unify y", t, y0);
    HEAP[loc(t)] = x0; HEAP[loc(t)+1] = y0; return 0;                 /* neutral: nothing decides yet */
  }
}
/* both identities hold.  Each side is inspected to its head before either is forced, so a dead side kills the branch
   whatever the other is doing and a binding the other side makes is met before a port is asked; a superposed side
   distributes. */
static Term both_step(Term t) {
  for (;;) {
    Term p = inspect(HEAP[loc(t)]); if (tag(p) == T_ERA) return p;
    Term q = inspect(HEAP[loc(t)+1]); if (tag(q) == T_ERA) return q;
    if (tag(p) == T_CTR && ctr_id(p) == C_REFL) return q;
    if (tag(q) == T_CTR && ctr_id(q) == C_REFL) return p;
    if (tag(p) == T_SUP || tag(q) == T_SUP) {                        /* a superposed side distributes; a name this conjunction's faces fix is projected */
      bool ps = tag(p) == T_SUP; Term sp = ps ? p : q, ot = ps ? q : p; Term nm = whnf(HEAP[loc(sp)]), faces = HEAP[loc(t)+3];
      int w = tag(nm) == T_IVAR ? world_side(faces, loc(nm)) : -1;
      if (w >= 0) { HEAP[loc(t) + (ps ? 0 : 1)] = HEAP[loc(sp) + 1 + w]; HEAP[loc(t) + (ps ? 1 : 0)] = fce_raw((unsigned)w, nm, ot, 0); continue; }
      Term f0 = restrict_push(faces, nm, 0, 0), f1 = restrict_push(faces, nm, 1, 0);
      return node3(T_SUP, 0, nm, ps ? both_cell(HEAP[loc(sp)+1], fce_raw(0, nm, ot, 0), f0) : both_cell(fce_raw(0, nm, ot, 0), HEAP[loc(sp)+1], f0),
                                 ps ? both_cell(HEAP[loc(sp)+2], fce_raw(1, nm, ot, 0), f1) : both_cell(fce_raw(1, nm, ot, 0), HEAP[loc(sp)+2], f1)); }
    cycle_trap("both p", t, p); cycle_trap("both q", t, q);
    HEAP[loc(t)] = p; HEAP[loc(t)+1] = q;
    if (INSPECT == 0) {                                                /* forced: each side in turn; a side that moves is met again by both */
      Term a = whnf(p); if (a != p) { HEAP[loc(t)] = a; continue; }
      Term b = whnf(q); if (b != q) { HEAP[loc(t)+1] = b; continue; } }
    return 0;
  }
}
/* a coordinate asked for its value: an identity type is decided, a Σ is a pair, a one-constructor type is that constructor; other types wait for a match */
static Term coordinate_asked(Term c) {
  Term T = coordinate_type(c); if (!T) return c; T = whnf(T);
  if (tag(T) != T_CTR) return c;
  if (ctr_id(T) == C_EQL || ctr_id(T) == C_PATH) { Term r = unify_cell(HEAP[loc(T)+1], HEAP[loc(T)+2], 0); HEAP[loc(c)+1] = r; return r; }
  if (ctr_id(T) == C_SIG) { receipt(R_SPLIT); Term p = sigma_split(T, HEAP[loc(c)+3]); HEAP[loc(c)+1] = p; return p; }
  { Term alts[2]; if (type_constructors(T, alts, 2, HEAP[loc(c)+3]) == 1) { HEAP[loc(c)+1] = alts[0]; return alts[0]; } }   /* one constructor: the point is it, its fields fresh */
  return c;
}
/* a coordinate asked by a match: the superposition of its type's constructors, one line at a fresh bound name per
   choice, each constructor's fields fresh coordinates of the world that choice makes; written into the coordinate's
   own slot so every holder meets the same correlated superposition.  0 when the type has no constructor list. */
static uint32_t points_of(Term cs, Term T, Term *alts, Term world) { uint32_t k = T ? type_constructors(T, alts, 64, world) : 0; return k ? k : case_points(cs, alts, world); }
static Term constructor_superposition(Term cs, Term coord) {
  Term T = coordinate_type(coord), world = HEAP[loc(coord)+3]; Term alts[64]; uint32_t k = points_of(cs, T, alts, world);
  Term names[64]; for (uint32_t i = 0; i + 1 < k; i++) names[i] = mk(T_IVAR, 0, loc(dim_push(0)));
  Term r = 0;
  for (uint32_t i = k; i-- > 0;) {
    Term w = world; for (uint32_t j = 0; j < i && j + 1 < k; j++) w = restrict_push(w, names[j], 1, 0);
    if (i + 1 < k) w = restrict_push(w, names[i], 0, 0);
    Term side[64]; points_of(cs, T, side, w);
    r = r ? node3(T_SUP, 0, names[i], side[i], r) : side[i]; }
  return r;
}
/* the faces in force on a frame: the world its bodies live in */
static int frame_side(Term fr, Loc name) { for (Term f = fr; tag(f); f = HEAP[loc(f)]) if (tag(f) == T_RESTRICT && ext(f) < 2 && loc(whnf(HEAP[loc(f)+1])) == name) return (int)ext(f); return -1; }
static Term frame_faces(Term fr) { Term w = 0; for (Term f = fr; tag(f); f = HEAP[loc(f)]) if (tag(f) == T_RESTRICT && ext(f) < 2) w = restrict_push(w, HEAP[loc(f)+1], ext(f), 0); return w; }
static unsigned cell_words(unsigned g) {
  switch (g) { case T_CASE: case T_FCE: case T_HCM: case T_UNIFY: return 3; case T_BOTH: case T_HELIM: case T_TRP: case T_PAP: case T_FCASE: return 4; default: return 2; }
}
/* the identity of a stuck match as a point: its code and the identities of the slots the code reads.  Two matches
   with one identity are one point, and one point is split once (the coordinate principle: a port fires once). */
static bool question_key_d(Term s, int depth, uint64_t *k1, uint64_t *k2) {
  if (tag(s) != T_CASE || depth < 0) return false;
  uint32_t code = loc(HEAP[loc(s)+1]); Term fr = HEAP[loc(s)+2]; uint64_t h1 = code * 0x9E3779B97F4A7C15ull, h2 = code;
  for (uint32_t lvl = 0; lvl < frame_depth(fr); lvl++) if (code_uses(code, lvl)) {
    if (frame_is_dim(fr, lvl)) return false;
    Term kf = KEY_FRAME; KEY_FRAME = fr; uint64_t id; bool ok = term_identity(frame_slot_raw(fr, lvl), depth - 1, &id); KEY_FRAME = kf;   /* the slot itself, read in this frame's world */
    if (!ok) return false;
    h1 = (h1 ^ id) * 0xC2B2AE3D27D4EB4Full; h2 = h2 * 31 + lvl + id; }
  *k1 = h1; *k2 = h2; return true;
}
static bool question_key(Term s, uint64_t *k1, uint64_t *k2) { return question_key_d(s, 6, k1, k2); }
/* a stuck match that is a point already split: it is that split (its worlds), so a copy of the point meets no new one */
static bool known_split(Term s, Term faces) {
  while (tag(s) == T_FCE && ext(s) < 2 && tag(HEAP[loc(s)]) == T_IVAR) { faces = restrict_push(faces, HEAP[loc(s)], ext(s), 0); s = inspect(HEAP[loc(s)+1]); }   /* the faces waiting on it are its world too */
  uint64_t k1, k2; KEY_FACES = faces; bool ok = tag(s) == T_CASE && !proof_case(s) && question_key(s, &k1, &k2); KEY_FACES = 0;
  if (!ok) return false;
  Term *slot = memo_slot(k1, k2 ^ 0x51); Term own = *memo_slot((uint64_t)loc(s) << 8 | 0xC0, 0xC0);
  if (!*slot) { if (own) *slot = own; return false; }                  /* the point as now understood is this computation's own split: registered under this identity */
  if (own == *slot) return false;                                      /* its own split: nothing new */
  HEAP[loc(s)] = mk(T_IND, 0, 0); HEAP[loc(s)+1] = *slot; return true;
}
/* a computation whose head is not yet a constructor, asked by a match for its head: the fibre law read at its
   output.  It becomes the superposition, over the constructors the match lists, of each constructor (fields fresh
   coordinates of that side's world) under the identity of the computation with it.  The computation moves to a
   fresh cell shared by every residual; the stuck cell is marked with the superposition, so every holder meets the
   same split and the same worlds; and the split is registered under the point's identity. */
static Term split_stuck(Term s, Term cs) {
  if (tag(HEAP[loc(s)]) == T_IND) return HEAP[loc(s)+1];               /* split already: its superposition */
  uint64_t k1, k2; Term *slot = 0;
  if (question_key(s, &k1, &k2)) { slot = memo_slot(k1, k2 ^ 0x51); if (*slot) { HEAP[loc(s)] = mk(T_IND, 0, 0); HEAP[loc(s)+1] = *slot; return *slot; } }
  unsigned n = cell_words(tag(s)); Loc l = alloc(n); for (unsigned i = 0; i < n; i++) HEAP[l+i] = HEAP[loc(s)+i];
  Term s1 = mk(tag(s), ext(s), l); Term *own = memo_slot((uint64_t)l << 8 | 0xC0, 0xC0);
  Term world = tag(s) == T_CASE ? frame_faces(HEAP[loc(s)+2]) : 0;
  Term alts[64]; uint32_t k = case_points(cs, alts, world);
  Term names[64]; for (uint32_t i = 0; i + 1 < k; i++) names[i] = mk(T_IVAR, 0, loc(dim_push(0)));
  Term r = 0;
  for (uint32_t i = k; i-- > 0;) {
    Term w = world; for (uint32_t j = 0; j < i && j + 1 < k; j++) w = restrict_push(w, names[j], 1, 0);
    if (i + 1 < k) w = restrict_push(w, names[i], 0, 0);
    Term side[64]; case_points(cs, side, w); Term a = side[i];
    r = r ? node3(T_SUP, 0, names[i], under(unify_cell(s1, a, w), a), r) : under(unify_cell(s1, a, w), a); }
  if (k == 1) r = node3(T_SUP, 0, mk(T_IVAR, 0, loc(dim_push(0))), r, mk(T_ERA, 0, 0));   /* one constructor is still a world */
  *own = r; if (slot) *slot = r; HEAP[loc(s)] = mk(T_IND, 0, 0); HEAP[loc(s)+1] = r;
  return r;
}

/* ---- case trees (§4): the eliminator instantiated on the heap ---------- */
static Term case_select(Term cs, Term scrut) {
  uint32_t code = loc(HEAP[loc(cs) + 1]); Term fr = HEAP[loc(cs) + 2];
  SNode *n = &CODE[code];                 /* S_CASE: a = scrut, b = first S_BRANCH */
  uint32_t br = n->b;
  while (br) {
    SNode *b = &CODE[br];                 /* S_BRANCH: ext = ctor id, a = arity, b = body, c = next */
    if (b->ext == ctr_id(scrut) || b->ext == 0xFFFFFF) {
      Term f = fr;
      uint32_t ar = b->ext == 0xFFFFFF ? 0 : ctr_arity(scrut);
      erase_ports(branch_drops(n->b, br, fr, 0, ar) + (ar ? 0 : ctr_arity(scrut)));   /* §3.3: the default branch drops every field */
      for (uint32_t i = 0; i < ar; i++) f = frame_push(f, HEAP[loc(scrut) + i]);
      return inst(b->b, f);
    }
    br = b->c;
  }
  fprintf(stderr, "hyper: no branch for %s in a case with branches", ctor_name(ctr_id(scrut)));
  for (uint32_t b2 = n->b; b2; b2 = CODE[b2].c) fprintf(stderr, " %s", CODE[b2].ext == 0xFFFFFF ? "_" : ctor_name(CODE[b2].ext));
  fprintf(stderr, "; scrutinee "); print_rec(scrut, 4); fprintf(stderr, "\n"); exit(3);
}
static Term case_restrict(Term cs, Term name, unsigned side, Term by, Term scrut) {
  Term code = HEAP[loc(cs) + 1], fr = HEAP[loc(cs) + 2];
  return node3(T_CASE, 0, scrut, code, restrict_push(fr, name, side, by));
}
static Term helim_restrict(Term he, Term name, unsigned side, Term by, Term scrut, Term motive) {
  Term code = HEAP[loc(he) + 1], fr = HEAP[loc(he) + 2];
  return node4(T_HELIM, 0, scrut, code, restrict_push(fr, name, side, by), motive);
}

/* ---- the HIT schema (§4): a path constructor applied to intervals is an APP spine over a CTR ---- */
Term nil_cell(void) { return mk(T_CTR, ctr_ext(C_NIL, 0), alloc(1)); }
Term cons_cell(Term h, Term t) { return node2(T_CTR, ctr_ext(C_CONS, 2), h, t); }
Term fields_list(Term ctr) {            /* the fields of a constructor cell as a list */
  Term l = nil_cell();
  for (uint32_t i = ctr_arity(ctr); i-- > 0;) l = cons_cell(HEAP[loc(ctr) + i], l);
  return l;
}
static Term ctr_with(uint32_t id, Term list) { /* a constructor with the fields of a (forced) list */
  Term xs[256]; uint32_t n = 0;
  for (Term l = whnf(list); tag(l) == T_CTR && ctr_id(l) == C_CONS && n < 256; l = whnf(HEAP[loc(l)+1])) xs[n++] = HEAP[loc(l)];
  Loc a = alloc(n ? n : 1); for (uint32_t i = 0; i < n; i++) HEAP[a+i] = xs[i];
  return mk(T_CTR, ctr_ext(id, n), a);
}
/* peel an application spine: returns the head, fills args outermost-last */
Term spine(Term t, Term *args, uint32_t *n) {
  *n = 0; Term a[64]; uint32_t k = 0;
  while (tag(t) == T_APP && k < 64) { if (tag(HEAP[loc(t)]) == T_IND) { t = HEAP[loc(t)+1]; continue; } a[k++] = HEAP[loc(t)+1]; t = HEAP[loc(t)]; }
  for (uint32_t i = 0; i < k; i++) args[i] = a[k-1-i];
  *n = k; return t;
}
Term apps(Term f, Term *args, uint32_t n) { for (uint32_t i = 0; i < n; i++) f = node2(T_APP, 0, f, args[i]); return f; }
/* a path constructor's cell at the intervals applied so far: its type, stepped through params, fields, intervals */
static uint32_t hit_nparams_carried(Term head) { CtorInfo *ci = &CINFO[ctr_id(head)]; return CINFO[ci->hit].carries ? CINFO[ci->hit].nparams : 0; }
static Term hit_ctor_type(Term head, Term *ivs, uint32_t nivs) {
  CtorInfo *ci = &CINFO[ctr_id(head)];
  Term ty = inst(BOOK[ci->type_def].code, 0);
  if (!CINFO[ci->hit].carries)
    for (uint32_t i = 0; i < CINFO[ci->hit].nparams; i++) { ty = whnf(ty); if (tag(ty) != T_CTR || ctr_id(ty) != C_PI) return 0; ty = node2(T_APP, 0, HEAP[loc(ty)+1], mk(T_ERA,0,0)); }
  for (uint32_t i = 0; i < ctr_arity(head); i++)          { ty = whnf(ty); if (tag(ty) != T_CTR || ctr_id(ty) != C_PI) return 0; ty = node2(T_APP, 0, HEAP[loc(ty)+1], HEAP[loc(head)+i]); }
  for (uint32_t i = 0; i < nivs; i++)                     { ty = whnf(ty); if (tag(ty) != T_CTR || ctr_id(ty) != C_PATH) return 0; ty = node2(T_APP, 0, HEAP[loc(ty)], ivs[i]); }
  return whnf(ty);
}
/* whnfHCon: the first literal interval selects the declared endpoint; the later intervals apply to it.
   Returns 0 when nothing fires (the spine is canonical). */
static Term hcon_step(Term t) {
  Term args[64]; uint32_t n; Term head = spine(t, args, &n);
  head = whnf(head);
  if (tag(head) != T_CTR || CINFO[ctr_id(head)].dim == 0) return 0;
  for (uint32_t i = 0; i < n; i++) {
    Term iv = ican(args[i]);
    if (tag(iv) == T_I0 || tag(iv) == T_I1) {
      Term ty = hit_ctor_type(head, args, i);
      if (!ty || tag(ty) != T_CTR || ctr_id(ty) != C_PATH) return 0;
      receipt(R_HCON);
      return apps(HEAP[loc(ty) + (tag(iv) == T_I0 ? 1 : 2)], args + i + 1, n - i - 1);
    }
    args[i] = iv;
  }
  return 0;
}
static Term helim_select(Term he, Term head, Term *ivs, uint32_t nivs) {
  uint32_t code = loc(HEAP[loc(he) + 1]); Term fr = HEAP[loc(he) + 2];
  SNode *n = &CODE[code];                 /* S_HELIM: b = first S_BRANCH */
  for (uint32_t br = n->b; br; br = CODE[br].c) {
    SNode *b = &CODE[br];
    if (b->ext == ctr_id(head)) {
      uint32_t first = hit_nparams_carried(head);
      erase_ports(branch_drops(n->b, br, fr, first, ctr_arity(head)));
      Term f = fr; for (uint32_t i = first; i < ctr_arity(head); i++) f = frame_push(f, HEAP[loc(head) + i]);
      return apps(inst(b->b, f), ivs, nivs);
    }
  }
  fprintf(stderr, "hyper: helim: no branch for %s\n", ctor_name(ctr_id(head))); exit(3);
}

/* ---- numbers ---------------------------------------------------------- */
static Term boolc(bool b) { return mk(T_CTR, ctr_ext(b ? C_TRUE : C_FALSE, 0), alloc(1)); }
static Term op2_num(unsigned op, unsigned kind, uint64_t a, uint64_t b) {
  uint64_t r = 0;
  if (kind == N_F64) { double x, y, z = 0; memcpy(&x, &a, 8); memcpy(&y, &b, 8);
    switch (op) {
      case OP_ADD: z = x + y; break; case OP_SUB: z = x - y; break; case OP_MUL: z = x * y; break;
      case OP_DIV: z = x / y; break; case OP_MOD: z = fmod(x, y); break; case OP_POW: z = pow(x, y); break;
      case OP_EQ: return boolc(x == y); case OP_NE: return boolc(x != y); case OP_LT: return boolc(x < y);
      case OP_LE: return boolc(x <= y); case OP_GT: return boolc(x > y); case OP_GE: return boolc(x >= y);
      default: return 0;
    }
    memcpy(&r, &z, 8); return node1(T_NUM, N_F64, (Term)r);
  }
  if (kind == N_I64) { int64_t x = (int64_t)a, y = (int64_t)b, z = 0;
    switch (op) {
      case OP_ADD: z = x + y; break; case OP_SUB: z = x - y; break; case OP_MUL: z = x * y; break;
      case OP_DIV: if (!y) return 0; z = x / y; break; case OP_MOD: if (!y) return 0; z = x % y; break;
      case OP_POW: { z = 1; for (int64_t i = 0; i < y; i++) z *= x; break; }
      case OP_EQ: return boolc(x == y); case OP_NE: return boolc(x != y); case OP_LT: return boolc(x < y);
      case OP_LE: return boolc(x <= y); case OP_GT: return boolc(x > y); case OP_GE: return boolc(x >= y);
      case OP_AND: z = x & y; break; case OP_OR: z = x | y; break; case OP_XOR: z = x ^ y; break;
      case OP_LSH: z = (int64_t)((uint64_t)x << y); break; case OP_RSH: z = x >> y; break;
    }
    return node1(T_NUM, N_I64, (Term)(uint64_t)z);
  }
  switch (op) {
    case OP_ADD: r = a + b; break; case OP_SUB: r = a - b; break; case OP_MUL: r = a * b; break;
    case OP_DIV: if (!b) return 0; r = a / b; break; case OP_MOD: if (!b) return 0; r = a % b; break;
    case OP_POW: { r = 1; for (uint64_t i = 0; i < b; i++) r *= a; break; }
    case OP_EQ: return boolc(a == b); case OP_NE: return boolc(a != b); case OP_LT: return boolc(a < b);
    case OP_LE: return boolc(a <= b); case OP_GT: return boolc(a > b); case OP_GE: return boolc(a >= b);
    case OP_AND: r = a & b; break; case OP_OR: r = a | b; break; case OP_XOR: r = a ^ b; break;
    case OP_LSH: r = a << b; break; case OP_RSH: r = a >> b; break;
  }
  return node1(T_NUM, kind, (Term)r);
}
static Term op2_bool(unsigned op, bool a, bool b) {
  switch (op) {
    case OP_AND: return boolc(a && b); case OP_OR: return boolc(a || b); case OP_XOR: return boolc(a != b);
    case OP_EQ: return boolc(a == b); case OP_NE: return boolc(a != b); default: return 0;
  }
}
static Term op1_num(unsigned op, unsigned kind, uint64_t a) {
  switch (op) {
    case OP1_NOT: return node1(T_NUM, N_U64, (Term)~a);
    case OP1_NEG: if (kind == N_I64) return node1(T_NUM, N_I64, (Term)(uint64_t)(-(int64_t)a));
                  if (kind == N_F64) { double x; memcpy(&x, &a, 8); x = -x; uint64_t r; memcpy(&r, &x, 8); return node1(T_NUM, N_F64, (Term)r); }
                  return 0;
    case OP1_TOCHAR: return node1(T_NUM, N_CHR, (Term)a);
  }
  return 0;
}


/* ---- occurs: does dimension `name` appear in t?  Over-approximates on depth (safe: no regularity fired) ---- */
static bool code_mentions(uint32_t c, uint32_t lvl) {
  if (!c) return false; SNode *n = &CODE[c];
  switch (n->tag) {
    case S_IVAR: return n->ext == lvl;
    case S_SUP: return (!n->d && n->ext == lvl) || code_mentions(n->a, lvl) || code_mentions(n->b, lvl);
    case S_FCE: return (!n->d && n->a == lvl) || code_mentions(n->b, lvl);
    case S_ISUB: return (!n->d && n->a == lvl) || code_mentions(n->b, lvl) || code_mentions(n->c, lvl);
    case S_LABEL: return false;
    case S_FIX: case S_OP1: case S_POUT: return code_mentions(n->a, lvl);
    case S_REFLECT: return code_mentions(n->a, lvl) || code_mentions(n->b, lvl);
    case S_PAP: return code_mentions(n->a, lvl) || code_mentions(n->b, lvl) || code_mentions(n->c, lvl) || code_mentions(n->d, lvl);
    case S_ETYPE: return code_mentions(n->a, lvl) || code_mentions(n->b, lvl) || code_mentions(n->c, lvl) || code_mentions(n->d, lvl);
    case S_ETERM: return code_mentions(n->a, lvl) || code_mentions(n->b, lvl) || code_mentions(n->c, lvl);
    case S_VAR: case S_REF: case S_ERA: case S_I0: case S_I1: case S_NUM: return false;
    case S_CTR: { uint32_t ar = n->ext & 0xFF; if (ar <= 4) { uint32_t k[4]={n->a,n->b,n->c,n->d}; for (uint32_t i=0;i<ar;i++) if (code_mentions(k[i],lvl)) return true; return false; }
                  for (uint32_t i=0;i<ar;i++) if (code_mentions(KIDS[n->kids+i],lvl)) return true; return false; }
    case S_BRANCH: return code_mentions(n->b, lvl) || code_mentions(n->c, lvl);
    default: return code_mentions(n->a, lvl) || code_mentions(n->b, lvl) || code_mentions(n->c, lvl) || code_mentions(n->d, lvl);
  }
}
bool code_uses(uint32_t c, uint32_t lvl) {          /* does the static code read level lvl (a term or a dimension)? */
  if (!c) return false; SNode *n = &CODE[c];
  switch (n->tag) {
    case S_VAR: case S_IVAR: return n->ext == lvl;
    case S_SUP: return (!n->d && n->ext == lvl) || code_uses(n->a, lvl) || code_uses(n->b, lvl) || code_uses(n->d, lvl);
    case S_FCE: return (!n->d && n->a == lvl) || code_uses(n->b, lvl) || code_uses(n->d, lvl);
    case S_ISUB: return (!n->d && n->a == lvl) || code_uses(n->b, lvl) || code_uses(n->c, lvl) || code_uses(n->d, lvl);
    case S_LABEL: case S_REF: case S_ERA: case S_I0: case S_I1: case S_NUM: return false;
    case S_CTR: { uint32_t ar = n->ext & 0xFF; if (ar <= 4) { uint32_t k[4]={n->a,n->b,n->c,n->d}; for (uint32_t i=0;i<ar;i++) if (code_uses(k[i],lvl)) return true; return false; }
                  for (uint32_t i=0;i<ar;i++) if (code_uses(KIDS[n->kids+i],lvl)) return true; return false; }
    case S_BRANCH: return code_uses(n->b, lvl) || code_uses(n->c, lvl);
    default: return code_uses(n->a, lvl) || code_uses(n->b, lvl) || code_uses(n->c, lvl) || code_uses(n->d, lvl);
  }
}
static bool occurs(Loc name, Term t, int depth);
/* does a closure over frame `fr` running `code` mention dimension `name`?  Through a DIM binder whose
 * level the code uses, or through any slot value that mentions it (over-approximate: the code may not read it). */
static bool frame_mentions(Term fr, uint32_t code, Loc name, int depth) {
  for (int guard = 0; tag(fr) && guard < 4096; guard++) {
    if (tag(fr) == T_DIM) { if (loc(fr) == name && code_mentions(code, ext(fr))) return true; }
    else if (tag(fr) == T_FRAME) { if (occurs(name, HEAP[loc(fr)+1], depth-1)) return true; }
    fr = HEAP[loc(fr)];
  }
  return false;
}
/* a visited set for the traversals of cyclic cells (a knot revisits the same cell) */
typedef struct { Term k[1 << 14]; uint32_t n; } Visited;
static bool visited(Visited *vs, Term key) {
  if (vs->n > (1u << 13)) return false;                                /* full: stop pruning, stay correct */
  uint32_t h = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 50) & ((1 << 14) - 1);
  for (;;) { if (!vs->k[h]) { vs->k[h] = key; vs->n++; return false; } if (vs->k[h] == key) return true; h = (h + 1) & ((1 << 14) - 1); }
}
static bool occurs_v(Loc name, Term t, int depth, Visited *vs);
static bool occurs(Loc name, Term t, int depth) { Visited *vs = calloc(1, sizeof *vs); bool r = occurs_v(name, t, depth, vs); free(vs); return r; }
static bool occurs_v(Loc name, Term t, int depth, Visited *vs) {   /* regularity by normalisation: the cell is reduced as it is inspected */
  if (depth <= 0) return true;
  if (tag(t) == T_REFLECT) return occurs_v(name, HEAP[loc(t)], depth-1, vs) || occurs_v(name, HEAP[loc(t)+1], depth-1, vs);   /* η-long x at T mentions what x and T mention */
  { Term args[64]; uint32_t n; Term h = spine(t, args, &n);
    if (tag(h) == T_REF) { for (uint32_t i = 0; i < n; i++) if (occurs_v(name, args[i], depth-1, vs)) return true; return false; } }
  t = whnf(t);
  if (tag(t) != T_IVAR && tag(t) != T_I0 && tag(t) != T_I1 && tag(t) != T_VAR && visited(vs, t)) return false;
  #define OCC(x) occurs_v(name, (x), depth-1, vs)
  switch (tag(t)) {
    case T_IVAR: return loc(t) == name;
    case T_I0: case T_I1: case T_NUM: case T_ERA: case T_REF: return false;
    case T_IDNF: { Loc p = loc(t); for (uint32_t i = 0; i < ext(t); i++) { uint32_t n = (uint32_t)HEAP[p++]; for (uint32_t k = 0; k < n; k++) if ((Loc)(HEAP[p++] >> 1) == name) return true; } return false; }
    case T_LAM: { Term g = generic(HEAP[loc(t)+1]); return OCC(inst(CODE[loc(HEAP[loc(t)])].a, g)); }
    case T_PLM: { Term g = dim_push(HEAP[loc(t)+1]); return OCC(inst(CODE[loc(HEAP[loc(t)])].a, g)); }
    case T_CASE: return OCC(HEAP[loc(t)]) || frame_mentions(HEAP[loc(t)+2], loc(HEAP[loc(t)+1]), name, depth);
    case T_HELIM: return (HEAP[loc(t)] && OCC(HEAP[loc(t)])) || OCC(HEAP[loc(t)+3]) || frame_mentions(HEAP[loc(t)+2], loc(HEAP[loc(t)+1]), name, depth);
    case T_CTR: for (uint32_t i = 0; i < ctr_arity(t); i++) if (OCC(HEAP[loc(t)+i])) return true; return false;
    case T_SUP: return OCC(HEAP[loc(t)]) || OCC(HEAP[loc(t)+1]) || OCC(HEAP[loc(t)+2]);
    case T_APP: case T_OP2: case T_IAND: case T_IOR: case T_CHK: case T_ASK: case T_PROJ: case T_CWITH: case T_GLU: case T_GLUE: case T_REFLECT:
      return OCC(HEAP[loc(t)]) || OCC(HEAP[loc(t)+1]);
    case T_FCE: return OCC(HEAP[loc(t)]) || OCC(HEAP[loc(t)+1]) || (ext(t) == 2 && OCC(HEAP[loc(t)+2]));
    case T_INOT: case T_UNGLUE: case T_GBASE: case T_GFACES: case T_OP1: case T_POUT: case T_CFIELDS: return OCC(HEAP[loc(t)]);
    case T_TRP: case T_FCASE: case T_ETYPE: case T_PAP: for (int i = 0; i < 4; i++) if (OCC(HEAP[loc(t)+i])) return true; return false;
    case T_HCM: case T_ETERM: for (int i = 0; i < 3; i++) if (OCC(HEAP[loc(t)+i])) return true; return false;
    case T_VAR: return false;                          /* a generic element (its own slot) */
    default: return true;
  }
  #undef OCC
}
bool occurs_cell(Loc name, Term t) { return occurs(name, t, 24); }
static bool is_rigid_type(uint32_t id) {
  return id == C_NAT || id == C_BOOL || id == C_UNIT || id == C_EMPTY || id == C_ENUM || id == C_NUMTY || id == C_SET;
}
static Term glu_collapse(Term t);
static uint32_t C_UAU;                                 /* the constructor id of Bend2's 6-ary ua, if declared */
static uint32_t C_ITV_ID;                              /* the constructor id of the interval type */
Term app2(Term f, Term a) { return node2(T_APP, 0, f, a); }
Term ref_of(int id) { return mk(T_REF, 0, (uint32_t)id); }

/* TRP L r s x  (§3.5 left column) */
static Term trp_step(Term t) {
  Term L = HEAP[loc(t)], r = ican(HEAP[loc(t)+1]), s = ican(HEAP[loc(t)+2]), x = HEAP[loc(t)+3];
  HEAP[loc(t)+1] = r; HEAP[loc(t)+2] = s;
  if (ieq(r, s)) { receipt(R_TRP); return whnf(x); }
  Term k = dim_push(0);                                   /* a fresh bound name */
  Term T = whnf(app2(L, mk(T_IVAR, 0, loc(k))));
  if (!occurs(loc(k), T, 24)) { receipt(R_TRP); return whnf(x); }          /* regularity: an occurs check */
  if (tag(T) == T_GLU) T = glu_collapse(T);
  switch (tag(T)) {
    case T_CTR: {
      uint32_t id = ctr_id(T);
      if (is_rigid_type(id)) { receipt(R_TRP); return whnf(x); }
      if (id < 256 && RULE_TRP[id] >= 0) { receipt(R_TRP); return whnf(app2(app2(app2(app2(ref_of(RULE_TRP[id]), L), r), s), x)); }
      if (CINFO[id].is_hit) {                       /* a HIT whose parameters move: push into the constructor, field by field */
        Term xw = whnf(x); Term ivs[64]; uint32_t n; Term h = whnf(spine(xw, ivs, &n));
        if (tag(h) == T_CTR && CINFO[ctr_id(h)].hit == id) {
          int d = book_find("trp/hit"); if (d < 0) return t;
          receipt(R_TRP);
          uint32_t np = hit_nparams_carried(h);
          Term rest = nil_cell(); for (uint32_t i = ctr_arity(h); i-- > np;) rest = cons_cell(HEAP[loc(h) + i], rest);
          Term fs = app2(app2(app2(app2(app2(ref_of(d), L), r), s), ref_of(CINFO[ctr_id(h)].type_def)), rest);
          if (np) {                                     /* the parameters at s are those of the line's cell there */
            Term Ts = whnf(app2(L, s)); Term ps = tag(Ts) == T_CTR ? fields_list(Ts) : nil_cell();
            int ap = book_find("append"); fs = ap >= 0 ? app2(app2(ref_of(ap), ps), fs) : fs;
          }
          return whnf(apps(ctr_with(ctr_id(h), fs), ivs, n));
        }
        if (tag(h) == T_HCM && n == 0) {              /* transport commutes with a composite of the HIT */
          int d = book_find("trp/hcm"); if (d < 0) return t;
          receipt(R_TRP);
          return whnf(app2(app2(app2(app2(app2(ref_of(d), L), r), s), HEAP[loc(h)+2]), HEAP[loc(h)+1]));
        }
        HEAP[loc(t)+3] = xw; return t;
      }
      return t;
    }
    case T_SUP: { receipt(R_TRP); Term nm = whnf(HEAP[loc(T)]);
      return whnf(app2(app2(app2(app2(app2(ref_of(RULE_TRP[0]), L), r), s), x), nm)); }
    case T_APP: case T_PAP: {                          /* a universe path applied at the marker: Bend2's 6-ary ua */
      Term ivs[64]; uint32_t n; Term h;
      if (tag(T) == T_PAP) { h = whnf(HEAP[loc(T)]); ivs[0] = HEAP[loc(T)+1]; n = 1; } else h = whnf(spine(T, ivs, &n));
      if (tag(h) == T_CTR && n == 1 && C_UAU && ctr_id(h) == C_UAU && ctr_arity(h) == 6) {
        Term iv = ican(ivs[0]); int fwd = -1;                         /* direction of the literal endpoints */
        if (tag(r) == T_I0 && tag(s) == T_I1) fwd = 1; else if (tag(r) == T_I1 && tag(s) == T_I0) fwd = 0;
        bool at_k = tag(iv) == T_IVAR && loc(iv) == loc(k);
        bool at_nk = false;
        if (tag(iv) == T_IDNF && ext(iv) == 1 && HEAP[loc(iv)] == 1 && (Loc)(HEAP[loc(iv)+1] >> 1) == loc(k) && !(HEAP[loc(iv)+1] & 1)) at_nk = true;
        if (fwd >= 0 && (at_k || at_nk)) { receipt(R_TRP); bool f = (fwd == 1) == at_k;
          return whnf(app2(HEAP[loc(h) + (f ? 2 : 3)], x)); }
      }
      return t; }
    case T_GLU: { int d = book_find("trp/Glue"); if (d < 0) return t; receipt(R_TRP);
      return whnf(app2(app2(app2(app2(app2(app2(ref_of(d), L), r), s), x), T), mk(T_IVAR, 0, loc(k)))); }
    default: return t;                                                       /* a neutral line: stuck */
  }
}
/* HCM A base faces  (§3.5 right column) */
static Term hcm_step(Term t) {
  Term A = HEAP[loc(t)], base = HEAP[loc(t)+1], faces = HEAP[loc(t)+2];
  /* walk the face list: a true face wins; false faces drop */
  Term live_head = mk(T_CTR, ctr_ext(C_NIL, 0), alloc(1)), *tail = &live_head; uint32_t nlive = 0;
  for (Term fs = whnf(faces); tag(fs) == T_CTR && ctr_id(fs) == C_CONS; fs = whnf(HEAP[loc(fs)+1])) {
    Term face = whnf(HEAP[loc(fs)]); Term phi = ican(HEAP[loc(face)]), u = HEAP[loc(face)+1];
    if (tag(phi) == T_I1) { receipt(R_HCM); return whnf(app2(u, mk(T_I1,0,0))); }
    if (tag(phi) == T_I0) continue;
    Term f2 = node2(T_CTR, ctr_ext(C_FACE, 2), phi, u);
    Term cell = node2(T_CTR, ctr_ext(C_CONS, 2), f2, live_head); *tail = cell; tail = &HEAP[loc(cell)+1]; nlive++;
  }
  if (nlive == 0) { receipt(R_HCM); return whnf(base); }
  *tail = mk(T_CTR, ctr_ext(C_NIL, 0), alloc(1));
  Term live = live_head;
  Term Aw = whnf(A);
  if (tag(Aw) == T_GLU) Aw = glu_collapse(Aw);
  switch (tag(Aw)) {
    case T_CTR: {
      uint32_t id = ctr_id(Aw);
      if (id == C_NAT || id == C_BOOL || id == C_UNIT || id == C_LIST || id == C_ENUM) {
        /* constructor-headed: the cap and every tube at a fresh dimension carry one constructor */
        Term b = whnf(base); if (tag(b) != T_CTR) { HEAP[loc(t)+1] = b; HEAP[loc(t)+2] = live; return t; }
        Term k = dim_push(0); bool same = true;
        for (Term fs = live; tag(fs) == T_CTR && ctr_id(fs) == C_CONS; fs = HEAP[loc(fs)+1]) {
          Term u = HEAP[loc(HEAP[loc(fs)])+1]; Term uk = whnf(app2(u, mk(T_IVAR,0,loc(k))));
          if (tag(uk) != T_CTR || ctr_id(uk) != ctr_id(b)) { same = false; break; }
        }
        if (!same) { HEAP[loc(t)+1] = b; HEAP[loc(t)+2] = live; return t; }
        receipt(R_HCM);
        uint32_t ar = ctr_arity(b); if (ar == 0) return b;
        Loc l = alloc(ar);
        for (uint32_t i = 0; i < ar; i++) {
          /* field i: hcomp of the fields, tubes projected by a case on the constructor */
          Term fl = mk(T_CTR, ctr_ext(C_NIL,0), alloc(1)), *ft = &fl;
          for (Term fs = live; tag(fs) == T_CTR && ctr_id(fs) == C_CONS; fs = HEAP[loc(fs)+1]) {
            Term face = HEAP[loc(fs)]; Term phi = HEAP[loc(face)], u = HEAP[loc(face)+1];
            Term sel = node2(T_APP, 0, app2(ref_of(book_find("tube-field")), node1(T_NUM, 0, (Term)i)), u);
            Term cell = node2(T_CTR, ctr_ext(C_CONS,2), node2(T_CTR, ctr_ext(C_FACE,2), phi, sel), fl); *ft = cell; ft = &HEAP[loc(cell)+1];
          }
          *ft = mk(T_CTR, ctr_ext(C_NIL,0), alloc(1));
          Term fieldTy = (id == C_LIST && i == 0) ? HEAP[loc(Aw)] : Aw;   /* List: head at the element type, tail at the list */
          if (id == C_NAT) fieldTy = Aw;
          HEAP[l+i] = node3(T_HCM, 0, fieldTy, HEAP[loc(b)+i], fl);
        }
        return mk(T_CTR, ext(b), l);
      }
      if (id < 256 && RULE_HCM[id] >= 0) { receipt(R_HCM); return whnf(app2(app2(app2(ref_of(RULE_HCM[id]), Aw), base), live)); }
      HEAP[loc(t)] = Aw; HEAP[loc(t)+2] = live; return t;                    /* HIT: canonical */
    }
    case T_GLU: { int d = book_find("hcm/Glue"); if (d < 0) { HEAP[loc(t)] = Aw; HEAP[loc(t)+2] = live; return t; }
      receipt(R_HCM); return whnf(app2(app2(app2(ref_of(d), Aw), base), live)); }
    case T_SUP: { receipt(R_HCM); Term nm = whnf(HEAP[loc(Aw)]);
      return whnf(app2(app2(app2(app2(ref_of(RULE_HCM[0]), Aw), base), live), nm)); }
    default: HEAP[loc(t)] = Aw; HEAP[loc(t)+2] = live; return t;
  }
}


/* ---- Glue (GLUE.md): the boundary rules; the Kan rules are prelude rows ------------------ */
/* walk a face list; returns the tube/type of a true face in *hit, and the live list */
static Term faces_live(Term faces, unsigned kind, Term *hit) {
  /* kind 2: Face(phi,u) ; kind 3: GFace(phi,T,e) */
  Term head = mk(T_CTR, ctr_ext(C_NIL,0), alloc(1)), *tail = &head; uint32_t n = 0; *hit = 0;
  for (Term fs = whnf(faces); tag(fs) == T_CTR && ctr_id(fs) == C_CONS; fs = whnf(HEAP[loc(fs)+1])) {
    Term f = whnf(HEAP[loc(fs)]); Term phi = ican(HEAP[loc(f)]);
    if (tag(phi) == T_I1) { *hit = f; return head; }
    if (tag(phi) == T_I0) continue;
    Loc l = alloc(kind); HEAP[l] = phi; for (unsigned i = 1; i < kind; i++) HEAP[l+i] = HEAP[loc(f)+i];
    Term cell = node2(T_CTR, ctr_ext(C_CONS,2), mk(T_CTR, ext(f), l), head); *tail = cell; tail = &HEAP[loc(cell)+1]; n++;
  }
  *tail = mk(T_CTR, ctr_ext(C_NIL,0), alloc(1));
  return n ? head : 0;
}
static Term glu_collapse(Term t) {        /* dispatching on a Glue type: a true face IS the partial type; no live face IS A */
  Term hit; Term live = faces_live(HEAP[loc(t)+1], 3, &hit);
  if (hit) { receipt(R_TRP); return whnf(HEAP[loc(hit)+1]); }
  if (!live) { receipt(R_TRP); return whnf(HEAP[loc(t)]); }
  HEAP[loc(t)+1] = live; return t;
}
static Term glue_step(Term t) {           /* glue faces a: a true face IS the section; no face IS a */
  Term hit; Term live = faces_live(HEAP[loc(t)], 2, &hit);
  if (hit) { receipt(R_TRP); return whnf(HEAP[loc(hit)+1]); }
  if (!live) { receipt(R_TRP); return whnf(HEAP[loc(t)+1]); }
  HEAP[loc(t)] = live; return t;
}

/* prelude rule table: trp/<Ctor>, hcm/<Ctor>; slot 0 holds the superposed-line rules */
void load_prelude(void) {
  for (int i = 0; i < 256; i++) RULE_TRP[i] = RULE_HCM[i] = -1;
  const char *names[] = { "Pi", "Sig", "Path", "Glue", "Set", 0 };
  for (int i = 0; names[i]; i++) {
    char buf[64]; uint32_t id = ctor_intern(names[i], 0);
    snprintf(buf, sizeof buf, "trp/%s", names[i]); int d = book_find(buf); if (d >= 0 && id < 256) RULE_TRP[id] = d;
    snprintf(buf, sizeof buf, "hcm/%s", names[i]); d = book_find(buf); if (d >= 0 && id < 256) RULE_HCM[id] = d;
  }
  RULE_TRP[0] = book_find("trp/sup"); RULE_HCM[0] = book_find("hcm/sup");
  C_UAU = ctor_intern("UaU", 6); C_ITV_ID = ctor_intern("Itv", 0);
}


/* ---- the loop (§3): weak head, demanded interaction ---------------------- */
static uint64_t WHNF_STEPS;
/* a node that a rule may fire on, and whose first word is a term (so the mark T_IND cannot be mistaken).
   REFLECT is not one: it is the checker's view of a typed point (§7), read by its cell, never marked. */
static Term prune(Term t); static Term trace_over(Term v, uint64_t from); static Term lift(Term t, int depth); static uint32_t side_world(Term sup, unsigned side); static bool world_within(uint32_t w, uint32_t of);
static bool node_redex(unsigned g) {
  switch (g) { case T_APP: case T_FCE: case T_PROJ: case T_CASE: case T_OP2: case T_OP1: case T_TRP: case T_HCM: case T_HELIM: case T_CHK:
    case T_UNGLUE: case T_GBASE: case T_GFACES: case T_FCASE: case T_CFIELDS: case T_CWITH: case T_PAP: case T_ETYPE: case T_ETERM: case T_POUT: case T_UNIFY: case T_BOTH: case T_TRACE: case T_LEAVES: return true;
    default: return false; }
}
static Term whnf_(Term t);
/* a demanded port fires once: the node a holder points at is marked with its result, and every other holder
   of the same node meets the value (the sharing of §3 is at every port, not only at a coordinate's slot) */
Term whnf(Term t) {
  Loc outer = CUR_NODE; Term r = whnf_(t); CUR_NODE = outer;   /* a nested reduction names its own nodes; the outer resumes naming its own */
  if (r != t && node_redex(tag(t))) { cycle_trap("ind", t, r); HEAP[loc(t)] = mk(T_IND, 0, 0); HEAP[loc(t)+1] = r; }
  return r;
}
static Term whnf_(Term t) {
  for (;;) {
    CUR_NODE = loc(t);
    if (node_redex(tag(t)) && tag(HEAP[loc(t)]) == T_IND) { t = HEAP[loc(t)+1]; continue; }   /* already fired: its result */
    if (CHECK_MODE && ++WHNF_STEPS > 30000000 && getenv("HYPER_DEBUG")) { fprintf(stderr, "whnf: runaway at tag %u: ", tag(t)); print_rec(t, 5); fprintf(stderr, "\n"); fflush(stdout); exit(9); }
    switch (tag(t)) {
      case T_VAR: {                                   /* a coordinate: force once, write back */
        Loc slot = loc(t) + 1; Term v = HEAP[slot];
        if (tag(v) == T_VAR && loc(v) == loc(t)) {            /* a generic element: its own slot */
          if (!CHECK_MODE && is_coordinate(t)) { Term r = coordinate_asked(t); if (r != t) { t = r; continue; } }
          return t; }
        v = whnf(v); HEAP[slot] = v; return v;
      }
      case T_REF: {                                   /* δ: the definition's own fresh dimensions */
        Def *d = &BOOK[loc(t)]; Term fr = 0;
        if (d->unknown) { if (!d->coord) d->coord = coordinate(d->type ? inst(d->type, 0) : 0); t = d->coord; continue; }   /* a declared unknown: one coordinate, shared by every reference */
        for (uint32_t i = 0; i < d->ndims; i++) fr = dim_push(fr);
        if (CHECK_MODE && d->type) { t = node2(T_REFLECT, 0, inst(d->code, fr), inst(d->type, 0)); continue; }   /* §7: a typed point is η-long at its type */
        t = inst(d->code, fr); continue;
      }
      case T_REFLECT: {                               /* x made η-long at T: Π → λ, Σ → pair, Path → a line whose faces are the endpoints,
                                                         Interval → a dimension name (an interval coordinate IS a name) */
        Term x = HEAP[loc(t)], T = whnf(HEAP[loc(t)+1]);
        if (tag(T) == T_CTR && C_ITV_ID && ctr_id(T) == C_ITV_ID && tag(whnf(x)) == T_VAR) return mk(T_IVAR, 0, loc(dim_push(0)));
        if (tag(T) == T_CTR) switch (ctr_id(T)) {
          case C_PI:  { int d = book_find("eta-pi"); if (d >= 0) { t = app2(app2(ref_of(d), x), HEAP[loc(T)+1]); continue; } break; }
          case C_SIG: { Term a = node2(T_PROJ, 0, node1(T_NUM, N_U64, 0), x), b = node2(T_PROJ, 0, node1(T_NUM, N_U64, 1), x);
                        return node2(T_CTR, ctr_ext(C_PAIR, 2), node2(T_REFLECT, 0, a, HEAP[loc(T)]), node2(T_REFLECT, 0, b, app2(HEAP[loc(T)+1], a))); }
          case C_PATH: { int d = book_find("eta-path"); if (d >= 0) { t = app2(app2(app2(app2(ref_of(d), x), HEAP[loc(T)]), HEAP[loc(T)+1]), HEAP[loc(T)+2]); continue; } break; }
          default: break;
        }
        t = x; continue;
      }
      case T_PAP: {                                   /* p @ i with the boundary kept */
        Term i = ican(HEAP[loc(t)+1]); HEAP[loc(t)+1] = i;
        if (tag(i) == T_I0) { receipt(R_APP_PLM); t = HEAP[loc(t)+2]; continue; }
        if (tag(i) == T_I1) { receipt(R_APP_PLM); t = HEAP[loc(t)+3]; continue; }
        Term p = whnf(HEAP[loc(t)]); HEAP[loc(t)] = p;
        if (tag(p) == T_PLM) { receipt(R_APP_PLM); t = open_closure(p, i); continue; }
        if (tag(p) == T_SUP) { receipt(R_APP_SUP); Term nm = HEAP[loc(p)]; Loc name = loc(whnf(nm));
          return node3(T_SUP, 0, nm, node4(T_PAP, 0, HEAP[loc(p)+1], fce3(0, name, i, 0), fce3(0, name, HEAP[loc(t)+2], 0), fce3(0, name, HEAP[loc(t)+3], 0)),
                                     node4(T_PAP, 0, HEAP[loc(p)+2], fce3(1, name, i, 0), fce3(1, name, HEAP[loc(t)+2], 0), fce3(1, name, HEAP[loc(t)+3], 0))); }
        return t;
      }
      case T_ETYPE: {                                 /* checkBranches.etype: Path ty → PathP (λi. etype (L i) (u @ i)) (eterm a) (eterm b); else P u */
        Term P = HEAP[loc(t)], elim = HEAP[loc(t)+1], ty = whnf(HEAP[loc(t)+2]), u = HEAP[loc(t)+3];
        if (tag(ty) == T_CTR && ctr_id(ty) == C_PATH) {
          int d = book_find("eline"); if (d < 0) return t;
          Term L = HEAP[loc(ty)], a = HEAP[loc(ty)+1], b = HEAP[loc(ty)+2];
          return node3(T_CTR, ctr_ext(C_PATH, 3), app2(app2(app2(app2(ref_of(d), P), elim), L), u),
                       node3(T_ETERM, 0, elim, app2(L, mk(T_I0,0,0)), a), node3(T_ETERM, 0, elim, app2(L, mk(T_I1,0,0)), b));
        }
        t = app2(P, u); continue;
      }
      case T_ETERM: {                                 /* checkBranches.eterm: Path ty → <j> eterm (L j) (u @ j); else elim u */
        Term elim = HEAP[loc(t)], ty = whnf(HEAP[loc(t)+1]), u = HEAP[loc(t)+2];
        if (tag(ty) == T_CTR && ctr_id(ty) == C_PATH) { int d = book_find("eterm-line"); if (d < 0) return t;
          t = app2(app2(app2(ref_of(d), elim), HEAP[loc(ty)]), u); continue; }
        t = app2(elim, u); continue;
      }
      case T_APP: {
        Term f = whnf(HEAP[loc(t)]), x = HEAP[loc(t) + 1];
        switch (tag(f)) {
          case T_ERA: return f;
          case T_LAM: receipt(R_BETA); if (lam_drops(f)) receipt(R_ERASE); t = open_closure(f, x); continue;
          case T_PLM: receipt(R_APP_PLM); t = open_closure(f, x); continue;
          case T_SUP: {                               /* distribute; the argument face-mapped at the name */
            receipt(R_APP_SUP);
            Term nm = HEAP[loc(f)]; Loc name = loc(whnf(nm));
            Term x0 = fce3(0, name, x, 0), x1 = fce3(1, name, x, 0);
            return node3(T_SUP, 0, nm, node2(T_APP, 0, HEAP[loc(f)+1], x0), node2(T_APP, 0, HEAP[loc(f)+2], x1));
          }
          case T_HELIM:                               /* an eliminator awaiting its point */
            if (HEAP[loc(f)] == 0) { t = node4(T_HELIM, 0, x, HEAP[loc(f)+1], HEAP[loc(f)+2], HEAP[loc(f)+3]); continue; }
            HEAP[loc(t)] = f; return t;
          case T_CTR: case T_APP: {                   /* a path constructor at intervals (whnfHCon) */
            HEAP[loc(t)] = f;
            Term r = hcon_step(t); if (r) { t = r; continue; }
            return t;
          }
          case T_VAR: if (!CHECK_MODE && is_coordinate(f)) { Term r = pi_apply(f, x); if (r) { t = r; continue; } }   /* an unknown function: its value there is a coordinate */
                      HEAP[loc(t)] = f; return t;
          case T_CASE: if (!CHECK_MODE && proof_case(f)) { receipt(R_CASE); t = under(inspect(HEAP[loc(f)]), node2(T_APP, 0, refl_body(f), x)); continue; }   /* J commutes out of an application */
                       HEAP[loc(t)] = f; return t;
          default: HEAP[loc(t)] = f; return t;        /* stuck spine */
        }
      }
      case T_HELIM: {                                 /* whnfHEl / whnfHRec */
        if (HEAP[loc(t)] == 0) return t;              /* a function cell */
        Term s = whnf(HEAP[loc(t)]); Term ivs[64]; uint32_t n; Term h = spine(s, ivs, &n);
        h = whnf(h);
        switch (tag(h)) {
          case T_CTR: if (n == 0 || CINFO[ctr_id(h)].dim) { receipt(R_HELIM); t = helim_select(t, h, ivs, n); continue; }
                      HEAP[loc(t)] = s; return t;
          case T_SUP: { if (n) { HEAP[loc(t)] = s; return t; }
            receipt(R_HELIM_SUP); Term nm = whnf(HEAP[loc(h)]); Term P = HEAP[loc(t)+3];
            return node3(T_SUP, 0, nm, helim_restrict(t, nm, 0, 0, HEAP[loc(h)+1], fce_raw(0, nm, P, 0)),
                                       helim_restrict(t, nm, 1, 0, HEAP[loc(h)+2], fce_raw(1, nm, P, 0))); }
          case T_HCM: {                               /* helim of a composite in the HIT: comp along the motive over the filler */
            Term P = HEAP[loc(t)+3]; Term A = whnf(HEAP[loc(h)]);
            if (n || tag(P) == T_ERA || tag(A) != T_CTR || !CINFO[ctr_id(A)].is_hit) { HEAP[loc(t)] = s; return t; }
            int d = book_find("helim/hcm"); if (d < 0) { HEAP[loc(t)] = s; return t; }
            receipt(R_HELIM_HCM);
            Term elim = node4(T_HELIM, 0, 0, HEAP[loc(t)+1], HEAP[loc(t)+2], P);
            t = app2(app2(app2(app2(app2(ref_of(d), P), elim), A), HEAP[loc(h)+2]), HEAP[loc(h)+1]); continue; }
          default: HEAP[loc(t)] = s; return t;
        }
      }
      case T_CFIELDS: { Term x = whnf(HEAP[loc(t)]);
        if (tag(x) == T_CTR) { receipt(R_CASE); t = fields_list(x); continue; }
        if (tag(x) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP, 0, HEAP[loc(x)], node1(T_CFIELDS,0,HEAP[loc(x)+1]), node1(T_CFIELDS,0,HEAP[loc(x)+2])); }
        HEAP[loc(t)] = x; return t; }
      case T_CWITH: { Term x = whnf(HEAP[loc(t)]);
        if (tag(x) == T_CTR) { receipt(R_CASE); erase_ports(ctr_arity(x)); t = ctr_with(ctr_id(x), HEAP[loc(t)+1]); continue; }
        HEAP[loc(t)] = x; return t; }
      case T_FCE: {
        Term nm = whnf(HEAP[loc(t)]);
        HEAP[loc(t)] = nm; FCE_SELF = t;
        return fce_apply(nm, ext(t), HEAP[loc(t) + 2], HEAP[loc(t) + 1]);
      }
      case T_CASE: {
        Term s0 = inspect(HEAP[loc(t)]);
        if (tag(s0) == T_ERA) return s0;                     /* a dead scrutinee: the match is dead */
        switch (tag(s0)) {
          case T_CTR: receipt(R_CASE); t = case_select(t, s0); continue;
          case T_SUP: {                                /* a match commutes over a superposition; a name its frame fixes is projected */
            Term nm = whnf(HEAP[loc(s0)]);
            { int w = tag(nm) == T_IVAR ? frame_side(HEAP[loc(t)+2], loc(nm)) : -1; if (w >= 0) { HEAP[loc(t)] = HEAP[loc(s0) + 1 + w]; continue; } }
            receipt(R_CASE_SUP);
            return node3(T_SUP, 0, nm, case_restrict(t, nm, 0, 0, HEAP[loc(s0)+1]),
                                       case_restrict(t, nm, 1, 0, HEAP[loc(s0)+2]));
          }
          default: {
            if (CHECK_MODE) { if (!proof_cell(s0)) HEAP[loc(t)] = s0; return t; }   /* the checker keeps its coordinates neutral and restricts frames per branch */
            Term pf = 0; Term s = peel(s0, &pf);
            if (is_coordinate(s)) {                    /* a coordinate asked by a match: the superposition of its type's constructors */
              if (INSPECT) { if (!proof_cell(s0)) HEAP[loc(t)] = s0; return t; }
              receipt(R_SPLIT); HEAP[loc(s) + 1] = constructor_superposition(t, s); continue; }
            { Term p, v; if (under_faces(s0, &p, &v)) { receipt(R_CASE); t = under(restrict_proof(p, frame_faces(HEAP[loc(t)+2])), node3(T_CASE, 0, v, HEAP[loc(t)+1], HEAP[loc(t)+2])); continue; } }   /* J commutes out, the identity read in this match's world */
            if (proof_cell(s)) {                       /* a match on an identity: the identity is decided when the match is asked */
              if (INSPECT) { if (!proof_cell(s0)) HEAP[loc(t)] = s0; return t; }
              Term s2 = whnf(s0); if (s2 != s0) { if (!proof_cell(s2)) HEAP[loc(t)] = s2; continue; }   /* a reduct that is still an identity is reached through the memo, not written: it may be a child of this match's own body */
              /* undecided: the one branch is what it is under the identity; its superposition is the match's, a side
                 under the identity at that face; a dead branch is dead */
              Term b = whnf(refl_body(t));
              if (tag(b) == T_ERA) return b;
              if (tag(b) == T_SUP) { Term nm = whnf(HEAP[loc(b)]); receipt(R_CASE_SUP);
                return node3(T_SUP, 0, nm, under(fce_raw(0, nm, s0, 0), HEAP[loc(b)+1]), under(fce_raw(1, nm, s0, 0), HEAP[loc(b)+2])); }
              if (loc(HEAP[loc(t)+1]) != under_case()) { t = under(s0, b); continue; }
              if (!proof_cell(s0)) HEAP[loc(t)] = s0; return t; }
            if (INSPECT == 0 && blocked(s)) {          /* a match on a computation whose head is not yet a constructor: its output is bound */
              /* at the innermost computation not facing a bare port: a match on a match on a comparison asks the comparison, not the constructor of its result */
              Term q = 0; Term in = peel(s, &q); Term deeper = tag(in) == T_CASE ? HEAP[loc(in)] : 0; Term dq = 0;
              if (deeper && tag(peel(deeper, &dq)) == T_CASE) { Term s2 = whnf(s0); if (s2 != s0) { HEAP[loc(t)] = s2; continue; } }
              if (known_split(s0, 0)) continue;          /* the point is split already: its worlds, no new split */
              receipt(R_SPLIT); HEAP[loc(t)] = split_stuck(s0, t); continue; }
            if (!proof_cell(s0)) HEAP[loc(t)] = s0; return t;
          }
        }
      }
      case T_TRACE: {                                 /* the run of e as a term: (value, events), each event the rule and the words it allocated
                                                         (research/sat_fibre/InteractionLedger.agda: Trace, Charge; the trace lives over the result) */
        uint64_t from = TRACE_LEN; int in = INSPECT; INSPECT = 0; Term v = nf(HEAP[loc(t)], 256); Term r = trace_over(v, from); INSPECT = in;   /* a demand of its own */
        return r;
      }
      case T_LEAVES: {                                /* the leaves of a superposition as a list, dead sides dropped */
        static Term out[1 << 14]; int in = INSPECT; INSPECT = 0; int n = collapse_leaves(HEAP[loc(t)], out, 1 << 14); INSPECT = in;
        Term l = nil_cell(); for (int i = n; i-- > 0;) l = cons_cell(out[i], l);
        return l;
      }
      case T_UNIFY: { Term r = unify_step(t); if (!r) return t; t = r; continue; }
      case T_BOTH:  { Term r = both_step(t);  if (!r) return t; t = r; continue; }
      case T_OP2: {
        Term a = whnf(HEAP[loc(t)]);
        if (tag(a) == T_SUP) { receipt(R_OP2_SUP); Loc name = loc(whnf(HEAP[loc(a)])); Term b = HEAP[loc(t)+1];
          return node3(T_SUP, 0, HEAP[loc(a)],
            node2(T_OP2, ext(t), HEAP[loc(a)+1], fce3(0, name, b, 0)),
            node2(T_OP2, ext(t), HEAP[loc(a)+2], fce3(1, name, b, 0))); }
        Term b = whnf(HEAP[loc(t) + 1]);
        if (tag(b) == T_SUP) { receipt(R_OP2_SUP); Loc name = loc(whnf(HEAP[loc(b)]));
          return node3(T_SUP, 0, HEAP[loc(b)],
            node2(T_OP2, ext(t), fce3(0, name, a, 0), HEAP[loc(b)+1]),
            node2(T_OP2, ext(t), fce3(1, name, a, 0), HEAP[loc(b)+2])); }
        if (tag(a) == T_NUM && tag(b) == T_NUM) { Term r = op2_num(ext(t), ext(a), HEAP[loc(a)], HEAP[loc(b)]); if (r) { receipt(R_OP2); return r; } }
        if (tag(a) == T_CTR && tag(b) == T_CTR && (ctr_id(a) == C_TRUE || ctr_id(a) == C_FALSE) && (ctr_id(b) == C_TRUE || ctr_id(b) == C_FALSE)) {
          Term r = op2_bool(ext(t), ctr_id(a) == C_TRUE, ctr_id(b) == C_TRUE); if (r) { receipt(R_OP2); return r; } }
        HEAP[loc(t)] = a; HEAP[loc(t)+1] = b; return t;
      }
      case T_OP1: {
        Term a = whnf(HEAP[loc(t)]);
        if (tag(a) == T_SUP) { receipt(R_OP2_SUP); return node3(T_SUP, 0, HEAP[loc(a)], node1(T_OP1, ext(t), HEAP[loc(a)+1]), node1(T_OP1, ext(t), HEAP[loc(a)+2])); }
        if (tag(a) == T_NUM) { Term r = op1_num(ext(t), ext(a), HEAP[loc(a)]); if (r) { receipt(R_OP1); return r; } }
        if (tag(a) == T_CTR && ext(t) == OP1_NOT && (ctr_id(a) == C_TRUE || ctr_id(a) == C_FALSE)) { receipt(R_OP1); return boolc(ctr_id(a) == C_FALSE); }
        HEAP[loc(t)] = a; return t;
      }
      case T_POUT: {                                  /* whnfPOut: a system on a true face is that branch */
        Term u = whnf(HEAP[loc(t)]);
        if (tag(u) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP, 0, HEAP[loc(u)], node1(T_POUT, 0, HEAP[loc(u)+1]), node1(T_POUT, 0, HEAP[loc(u)+2])); }
        if (tag(u) == T_CTR && ctr_arity(u) == 1 && !strcmp(ctor_name(ctr_id(u)), "Sys")) {
          for (Term fs = whnf(HEAP[loc(u)]); tag(fs) == T_CTR && ctr_id(fs) == C_CONS; fs = whnf(HEAP[loc(fs)+1])) {
            Term face = whnf(HEAP[loc(fs)]); Term phi = ican(HEAP[loc(face)]);
            if (tag(phi) == T_I1) { receipt(R_POUT); t = HEAP[loc(face)+1]; goto next; }
          }
        }
        HEAP[loc(t)] = u; return t;
        next: continue;
      }
      case T_INOT: case T_IAND: case T_IOR: return ican(t);
      case T_CHK: t = HEAP[loc(t) + 1]; continue;    /* a judgment projects to its term at run */
      case T_PROJ: {
        Term i = whnf(HEAP[loc(t)]), x = whnf(HEAP[loc(t)+1]);
        if (tag(x) == T_ERA) return x;
        if (tag(x) == T_GLU && tag(i) == T_NUM && HEAP[loc(i)] < 2) { receipt(R_CASE); erase_ports(1); return whnf(HEAP[loc(x) + HEAP[loc(i)]]); }
        if (tag(i) == T_NUM && tag(x) == T_CTR && HEAP[loc(i)] < ctr_arity(x)) { receipt(R_CASE); erase_ports(ctr_arity(x) - 1); return whnf(HEAP[loc(x) + HEAP[loc(i)]]); }   /* the field is a held port: it fires once */
        if (tag(x) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP, 0, HEAP[loc(x)], node2(T_PROJ,0,i,HEAP[loc(x)+1]), node2(T_PROJ,0,i,HEAP[loc(x)+2])); }
        if (!CHECK_MODE && proof_case(x)) { receipt(R_CASE); t = under(inspect(HEAP[loc(x)]), node2(T_PROJ, 0, i, refl_body(x))); continue; }   /* J commutes out of a projection */
        HEAP[loc(t)] = i; HEAP[loc(t)+1] = x; return t;
      }
      case T_GBASE: { Term g = whnf(HEAP[loc(t)]);
        if (tag(g) == T_GLU) { receipt(R_CASE); t = HEAP[loc(g)]; continue; }
        if (tag(g) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP,0,HEAP[loc(g)], node1(T_GBASE,0,HEAP[loc(g)+1]), node1(T_GBASE,0,HEAP[loc(g)+2])); }
        if (is_value(g)) return g;                          /* a non-Glue type is its own base */
        HEAP[loc(t)] = g; return t; }
      case T_GFACES: { Term g = whnf(HEAP[loc(t)]);
        if (tag(g) == T_GLU) { receipt(R_CASE); t = HEAP[loc(g)+1]; continue; }
        if (tag(g) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP,0,HEAP[loc(g)], node1(T_GFACES,0,HEAP[loc(g)+1]), node1(T_GFACES,0,HEAP[loc(g)+2])); }
        if (is_value(g)) return mk(T_CTR, ctr_ext(C_NIL,0), alloc(1));   /* no faces */
        HEAP[loc(t)] = g; return t; }
      case T_FCASE: { Term phi = ican(HEAP[loc(t)]);              /* [phi, a, b, c]: I1 → a, I0 → b, symbolic → c */
        receipt(R_CASE);
        if (tag(phi) == T_I1) { t = HEAP[loc(t)+1]; continue; }
        if (tag(phi) == T_I0) { t = HEAP[loc(t)+2]; continue; }
        t = HEAP[loc(t)+3]; continue; }
      case T_GLUE: return glue_step(t);
      case T_GLU: return glu_collapse(t);           /* a Glue type with a true face IS that partial type */
      case T_UNGLUE: { Term g = HEAP[loc(t)];
        if (tag(g) == T_GLUE) { receipt(R_TRP); t = HEAP[loc(g)+1]; continue; }   /* a syntactic glue is eliminated before it reduces to its base (whnfUnG) */
        g = whnf(g);
        if (tag(g) == T_GLUE) { receipt(R_TRP); t = HEAP[loc(g)+1]; continue; }
        if (tag(g) == T_SUP) { receipt(R_CASE_SUP); return node3(T_SUP, 0, HEAP[loc(g)], node1(T_UNGLUE,0,HEAP[loc(g)+1]), node1(T_UNGLUE,0,HEAP[loc(g)+2])); }
        HEAP[loc(t)] = g; return t; }
      case T_TRP: return trp_step(t);
      case T_HCM: return hcm_step(t);
      default: return t;
    }
  }
}

/* ---- normal forms and printing ------------------------------------------ */
Term generic(Term fr) {              /* a fresh generic element: a slot that points to itself */
  Term f = frame_push(fr, 0);
  HEAP[loc(f) + 1] = mk(T_VAR, ext(f), loc(f));
  return f;
}
/* the normal form as the top demands it: rounds of splits, dead sides pruned, into every field */
Term nf(Term t, int depth) {
  if (depth <= 0) return t;
  t = whnf(t); if (tag(t) == T_SUP) t = prune(t);
  if (proof_case(t)) {                                  /* a value under an undecided identity: its body is normalised, its superpositions are the leaf's */
    Term p = inspect(HEAP[loc(t)]), b = lift(nf(refl_body(t), depth-1), depth-1);
    if (tag(b) == T_ERA) return b;
    if (tag(b) == T_SUP) { Term nm = whnf(HEAP[loc(b)]); return nf(node3(T_SUP, 0, nm, under(fce_raw(0, nm, p, 0), HEAP[loc(b)+1]), under(fce_raw(1, nm, p, 0), HEAP[loc(b)+2])), depth); }
    return whnf(under(p, b)); }
  switch (tag(t)) {
    case T_CTR: for (uint32_t i = 0; i < ctr_arity(t); i++) { Term f = nf(HEAP[loc(t)+i], depth-1); HEAP[loc(t)+i] = f;
        if (proof_case(f)) { HEAP[loc(t)+i] = refl_body(f); return nf(under(inspect(HEAP[loc(f)]), t), depth); } }   /* a field under an identity: the value is */
      return t;
    case T_SUP: { uint32_t w = WORLD;
      WORLD = side_world(t, 0); HEAP[loc(t)+1] = nf(HEAP[loc(t)+1], depth-1); WORLD = side_world(t, 1); HEAP[loc(t)+2] = nf(HEAP[loc(t)+2], depth-1); WORLD = w;
      return t; }
    default: return t;
  }
}
/* the trace over a value: at each leaf of the superposition (the value lifted), the events that fired in that leaf's
   world or any world above it, so a shared prefix is every leaf's and a side's own work is its own */
static Term trace_over(Term v, uint64_t from) {
  v = lift(v, 256);
  if (tag(v) == T_SUP) { uint32_t w = WORLD; Term nm = HEAP[loc(v)];
    WORLD = side_world(v, 0); Term a = trace_over(HEAP[loc(v)+1], from); WORLD = side_world(v, 1); Term b = trace_over(HEAP[loc(v)+2], from); WORLD = w;
    return node3(T_SUP, 0, nm, a, b); }
  if (tag(v) == T_ERA) return v;
  Term l = nil_cell();
  for (uint64_t i = TRACE_LEN; i-- > from;) if (world_within(WORLD, TRACE_WORLD[i])) {
    Loc next = i + 1 < TRACE_LEN ? TRACE_HEAP[i+1] : HEAP_LEN;
    l = cons_cell(node1(T_CTR, ctr_ext(ctor_intern(RULE_NAME[TRACE[i]], 1), 1), node1(T_NUM, N_U64, next - TRACE_HEAP[i])), l); }
  return node2(T_CTR, ctr_ext(C_PAIR, 2), v, l);
}
Term normalize(Term t, int depth) {
  if (depth <= 0) return t;
  t = whnf(t);
  switch (tag(t)) {
    case T_CTR: for (uint32_t i = 0; i < ctr_arity(t); i++) HEAP[loc(t)+i] = normalize(HEAP[loc(t)+i], depth-1); return t;
    case T_SUP: HEAP[loc(t)+1] = normalize(HEAP[loc(t)+1], depth-1); HEAP[loc(t)+2] = normalize(HEAP[loc(t)+2], depth-1); return t;
    case T_APP: HEAP[loc(t)+1] = normalize(HEAP[loc(t)+1], depth-1); return t;
    default: return t;
  }
}
static void print_num(Term t) {
  uint64_t v = HEAP[loc(t)];
  switch (ext(t)) {
    case N_I64: printf("%s%lld", (int64_t)v >= 0 ? "+" : "", (long long)(int64_t)v); break;
    case N_F64: { double x; memcpy(&x, &v, 8); printf("%g", x); break; }
    case N_CHR: printf("'%c'", (int)v); break;
    default: printf("%llu", (unsigned long long)v);
  }
}
/* the world of side i of a superposition at a name, under the current world: one per (world, name, side) */
static uint32_t side_world(Term sup, unsigned side) {
  Term nm = whnf(HEAP[loc(sup)]); if (tag(nm) != T_IVAR) return WORLD;
  Term *slot = memo_slot((uint64_t)WORLD << 32 | loc(nm), 0x77 | (uint64_t)side << 8);
  if (!*slot) { if (NWORLD >= WCAP) { WCAP = WCAP ? WCAP * 2 : 1024; WPARENT = realloc(WPARENT, WCAP * sizeof *WPARENT); WPARENT[0] = 0; }
    WPARENT[NWORLD] = WORLD; *slot = (Term)NWORLD++; }
  return (uint32_t)*slot;
}
static bool world_within(uint32_t w, uint32_t of) { for (;;) { if (w == of) return true; if (!w) return false; w = WPARENT[w]; } }
/* a superposition with a dead side is its other side; with both dead it is dead (an empty fibre) */
static Term prune(Term t) {
  t = whnf(t); if (tag(t) != T_SUP) return t;
  uint32_t w = WORLD;
  WORLD = side_world(t, 0); Term a = prune(HEAP[loc(t)+1]); WORLD = side_world(t, 1); Term b = prune(HEAP[loc(t)+2]); WORLD = w;
  HEAP[loc(t)+1] = a; HEAP[loc(t)+2] = b;
  if (tag(a) == T_ERA) { receipt(R_ERASE); return b; }
  if (tag(b) == T_ERA) { receipt(R_ERASE); return a; }
  return t;
}
static void print_rec(Term t, int depth) {
  if (depth <= 0) { receipt(R_ERASE); printf("…"); return; }   /* §3.3: the printer cuts a port */
  t = whnf(t); if (tag(t) == T_SUP) t = prune(t);
  switch (tag(t)) {
    case T_NUM: print_num(t); break;
    case T_OP1: printf("(op%u ", ext(t)); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_POUT: printf("pout("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_CTR: { uint32_t ar = ctr_arity(t); printf("#%s", ctor_name(ctr_id(t)));
      if (ar) { printf("{"); for (uint32_t i = 0; i < ar; i++) { if (i) printf(","); print_rec(HEAP[loc(t)+i], depth-1); } printf("}"); }
      else printf("{}"); break; }
    case T_SUP: { Term nm = whnf(HEAP[loc(t)]); int k = tag(nm)==T_IVAR ? label_of(loc(nm)) : -1;   /* a label by its number, a bound name by its address */
      printf("&%u{", k >= 0 ? (unsigned)k : tag(nm)==T_IVAR ? loc(nm) : 0);
      print_rec(HEAP[loc(t)+1], depth-1); printf(","); print_rec(HEAP[loc(t)+2], depth-1); printf("}"); break; }
    case T_LAM: { Term fr = HEAP[loc(t)+1]; Term g = generic(fr); uint32_t code = loc(HEAP[loc(t)]);
      printf("λx%u.", ext(g)); print_rec(inst(CODE[code].a, g), depth-1); break; }
    case T_PLM: { Term fr = HEAP[loc(t)+1]; Term g = dim_push(fr); uint32_t code = loc(HEAP[loc(t)]);
      printf("<i%u>", loc(g)); print_rec(inst(CODE[code].a, g), depth-1); break; }
    case T_VAR: if (is_coordinate(t)) printf("_%u", loc(t)); else printf("x%u", ext(t)); break;   /* a coordinate with no value yet, by its cell */
    case T_IVAR: printf("i%u", loc(t)); break;
    case T_I0: printf("i0"); break; case T_I1: printf("i1"); break;
    case T_IDNF: { Loc p = loc(t); for (uint32_t i = 0; i < ext(t); i++) { if (i) printf("∨"); uint32_t n = (uint32_t)HEAP[p++];
        if (!n) printf("i1"); for (uint32_t k = 0; k < n; k++) { uint64_t l = HEAP[p++]; if (k) printf("∧"); printf("%si%u", (l&1)?"":"~", (unsigned)(l>>1)); } }
        if (!ext(t)) printf("i0"); break; }
    case T_INOT: printf("~"); print_rec(HEAP[loc(t)], depth-1); break;
    case T_IAND: printf("("); print_rec(HEAP[loc(t)], depth-1); printf("∧"); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_IOR:  printf("("); print_rec(HEAP[loc(t)], depth-1); printf("∨"); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_ERA: printf("*"); break;
    case T_REF: printf("@%s", BOOK[loc(t)].name); break;
    case T_APP: printf("("); print_rec(HEAP[loc(t)], depth-1); printf(" "); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_FCE: printf("[i%u:=", loc(whnf(HEAP[loc(t)]))); if (ext(t) < 2) printf("%u", ext(t)); else print_rec(HEAP[loc(t)+2], depth-1); printf("]"); print_rec(HEAP[loc(t)+1], depth-1); break;
    case T_CASE: if (proof_case(t)) { printf("("); print_rec(refl_body(t), depth-1); printf(" under "); print_rec(inspect(HEAP[loc(t)]), depth-1); printf(")"); break; }   /* a value under an undecided identity */
                 { uint32_t code = loc(HEAP[loc(t)+1]); Term fr = HEAP[loc(t)+2]; printf("case%u(", code); print_rec(HEAP[loc(t)], depth-1);   /* a stuck match: its scrutinee and what its code reads */
                   INSPECT++; for (uint32_t lvl = 0; lvl < frame_depth(fr); lvl++) if (code_uses(code, lvl)) { bool dim; Term v = frame_lookup(fr, lvl, &dim); if (dim) continue; v = whnf(v); if (tag(v) == T_LAM || tag(v) == T_PLM) continue; printf(";"); print_rec(v, depth-1); }
                   INSPECT--; printf(")"); break; }
    case T_UNIFY: INSPECT++; printf("("); print_rec(HEAP[loc(t)], depth-1); printf(" ≡ "); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); INSPECT--;   /* an undecided identity: its sides as they stand, not asked */
      break;
    case T_BOTH: INSPECT++; printf("("); print_rec(HEAP[loc(t)], depth-1); printf(" ∧ "); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); INSPECT--; break;
    case T_HELIM: printf("helim("); if (HEAP[loc(t)]) print_rec(HEAP[loc(t)], depth-1); else printf("_"); printf(")"); break;
    case T_CFIELDS: printf("fields("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_REFLECT: printf("reflect("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_PAP: printf("("); print_rec(HEAP[loc(t)], depth-1); printf(" @ "); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_ETYPE: printf("etype(…)"); break; case T_ETERM: printf("eterm(…)"); break;
    case T_CWITH: printf("with("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_PROJ: printf("proj("); print_rec(HEAP[loc(t)], depth-1); printf(","); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_OP2: printf("("); print_rec(HEAP[loc(t)], depth-1); printf(" op%u ", ext(t)); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_GLU: printf("Glue("); print_rec(HEAP[loc(t)], depth-1); printf(","); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_GLUE: printf("glue("); print_rec(HEAP[loc(t)], depth-1); printf(","); print_rec(HEAP[loc(t)+1], depth-1); printf(")"); break;
    case T_GBASE: printf("glue-base("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_GFACES: printf("glue-faces("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_FCASE: printf("face-case("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_UNGLUE: printf("unglue("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_TRACE: printf("trace("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_LEAVES: printf("leaves("); print_rec(HEAP[loc(t)], depth-1); printf(")"); break;
    case T_TRP: printf("trp("); print_rec(HEAP[loc(t)], depth-1); printf(","); print_rec(HEAP[loc(t)+1], depth-1); printf(","); print_rec(HEAP[loc(t)+2], depth-1); printf(","); print_rec(HEAP[loc(t)+3], depth-1); printf(")"); break;
    case T_HCM: printf("hcomp("); print_rec(HEAP[loc(t)], depth-1); printf(","); print_rec(HEAP[loc(t)+1], depth-1); printf(","); print_rec(HEAP[loc(t)+2], depth-1); printf(")"); break;
    default: printf("?%u", tag(t));
  }
}
void print_term(Term t, int depth) { print_rec(t, depth); }

/* §6: the census of receipts. Every interaction left one receipt in the trace; the census is its fold
   by rule (AdiBija: every analyzer is a fold over the trace). Definitional unfolding and the face map's
   sharing are shown apart, as the receipts name them. */
const char *RULE_NAME[R_COUNT] = { "", "beta", "appSup", "app-plm", "dupSupEqual", "dupSupDifferent", "dupLamUsed", "dupLamErased", "dupNode",
    "fce-share", "case", "appMatSup", "op2", "op2-sup", "erase", "trp", "hcm", "hcon", "helim", "helim-sup", "helim-hcm", "op1", "pout", "split", "unify" };
void print_trace(uint64_t from) {           /* the derivation as data: each step a rule at a node */
  for (uint64_t i = from; i < TRACE_LEN; i++) printf("%s%s@%u", i > from ? " " : "", RULE_NAME[TRACE[i]], TRACE_NODE[i]);
  printf("\n");
}
void print_census(void) {
  const char **names = RULE_NAME;
  uint64_t count[R_COUNT] = {0}, words[R_COUNT] = {0};   /* by event: the interactions and the heap words they allocated (the two receivers of Charge) */
  for (uint64_t i = 0; i < TRACE_LEN; i++) if (TRACE[i] < R_COUNT) { count[TRACE[i]]++; words[TRACE[i]] += (i + 1 < TRACE_LEN ? TRACE_HEAP[i+1] : HEAP_LEN) - TRACE_HEAP[i]; }
  fprintf(stderr, "- Census:");
  for (unsigned r = 1; r < R_COUNT; r++) if (count[r]) fprintf(stderr, " %s=%llu/%lluw", names[r], (unsigned long long)count[r], (unsigned long long)words[r]);
  fprintf(stderr, "\n");
}

static bool is_chr_string(Term t);
/* ---- Bend2's presentation (Core.Type's Show), for the dialect's oracle comparison ---- */
static bool is_chr_string(Term t) {          /* a list of characters prints as a string */
  t = whnf(t);
  while (tag(t) == T_CTR && ctr_id(t) == C_CONS) { Term h = whnf(HEAP[loc(t)]); if (tag(h) != T_NUM || ext(h) != N_CHR) return false; t = whnf(HEAP[loc(t)+1]); }
  return tag(t) == T_CTR && ctr_id(t) == C_NIL;
}
static void print_bend_num(Term t) {
  uint64_t v = HEAP[loc(t)];
  switch (ext(t)) {
    case N_I64: printf("%s%lld", (int64_t)v >= 0 ? "+" : "", (long long)(int64_t)v); break;
    case N_F64: { double x; memcpy(&x, &v, 8); if (x == (double)(long long)x && fabs(x) < 1e15) printf("%.1f", x); else printf("%g", x); break; }
    case N_CHR: printf("'%c'", (int)v); break;
    default: printf("%llu", (unsigned long long)v);
  }
}
static void pb(Term t, int depth);
static const char *PNAMES[4096];              /* binder names by level, while presenting an open term */
static const char *bname(uint32_t code) { uint32_t i = (uint32_t)CODE[code].num; return (BNAMES && i) ? BNAMES[i] : 0; }
static void pb_list(Term l, const char *open, const char *sep, const char *close, int depth) {
  printf("%s", open); bool first = true;
  for (l = whnf(l); tag(l) == T_CTR && ctr_id(l) == C_CONS; l = whnf(HEAP[loc(l)+1])) { if (!first) printf("%s", sep); first = false; pb(HEAP[loc(l)], depth-1); }
  printf("%s", close);
}
static void pb(Term t, int depth) {
  if (depth <= 0) { printf("…"); return; }
  t = whnf(t);
  switch (tag(t)) {
    case T_NUM: print_bend_num(t); break;
    case T_CTR: {
      uint32_t id = ctr_id(t), ar = ctr_arity(t); const char *nm = ctor_name(id);
      switch (id) {
        case C_ZER: printf("0n"); return;
        case C_SUC: printf("1n+"); pb(HEAP[loc(t)], depth-1); return;
        case C_TRUE: printf("True"); return; case C_FALSE: printf("False"); return;
        case C_TT: printf("()"); return; case C_REFL: printf("{==}"); return;
        case C_NIL: printf("[]"); return;
        case C_CONS:
          if (is_chr_string(t)) { printf("\""); for (Term l = whnf(t); tag(l) == T_CTR && ctr_id(l) == C_CONS; l = whnf(HEAP[loc(l)+1])) printf("%c", (int)HEAP[loc(whnf(HEAP[loc(l)]))]); printf("\""); return; }
          pb(HEAP[loc(t)], depth-1); printf("<>"); pb(HEAP[loc(t)+1], depth-1); return;
        case C_PAIR: {                                  /* a tuple; (&Ctor, fields…, ()) is a user constructor */
          Term xs[256]; uint32_t n = 0; Term p = t;
          while (tag(p) == T_CTR && ctr_id(p) == C_PAIR && n < 255) { xs[n++] = HEAP[loc(p)]; p = whnf(HEAP[loc(p)+1]); }
          xs[n++] = p;
          Term h = whnf(xs[0]);
          if (tag(h) == T_CTR && ctr_arity(h) == 0 && ctor_name(ctr_id(h))[0] == '&' && tag(p) == T_CTR && ctr_id(p) == C_TT) {
            printf("@%s{", ctor_name(ctr_id(h)) + 1);
            for (uint32_t i = 1; i + 1 < n; i++) { if (i > 1) printf(","); pb(xs[i], depth-1); }
            printf("}"); return; }
          printf("("); for (uint32_t i = 0; i < n; i++) { if (i) printf(","); pb(xs[i], depth-1); } printf(")"); return; }
        case C_SET: printf("Set"); return; case C_NAT: printf("Nat"); return; case C_BOOL: printf("Bool"); return;
        case C_UNIT: printf("Unit"); return; case C_EMPTY: printf("Empty"); return;
        case C_LIST: pb(HEAP[loc(t)], depth-1); printf("[]"); return;
        case C_ENUM: pb_list(HEAP[loc(t)], "&{", ",", "}", depth); return;
        case C_PI: printf("∀"); pb(HEAP[loc(t)], depth-1); printf(". "); pb(HEAP[loc(t)+1], depth-1); return;
        case C_SIG: printf("Σ"); pb(HEAP[loc(t)], depth-1); printf(". "); pb(HEAP[loc(t)+1], depth-1); return;
        case C_PATH: printf("PathP("); pb(HEAP[loc(t)], depth-1); printf(","); pb(HEAP[loc(t)+1], depth-1); printf(","); pb(HEAP[loc(t)+2], depth-1); printf(")"); return;
        case C_EQL: pb(HEAP[loc(t)], depth-1); printf("{"); pb(HEAP[loc(t)+1], depth-1); printf("=="); pb(HEAP[loc(t)+2], depth-1); printf("}"); return;
        default: break;
      }
      if (nm[0] == '&' && ar == 0) { printf("%s", nm); return; }                          /* an enum symbol */
      if (nm[0] == '@') {
        uint32_t np = CINFO[id].hit ? hit_nparams_carried(t) : 0;
        if (!strcmp(nm, "@Trunc/tin"))     { printf("tin("); pb(HEAP[loc(t)], depth-1); printf(")"); return; }
        if (!strcmp(nm, "@Trunc/tsquash")) { printf("tsquash("); pb(HEAP[loc(t)], depth-1); printf(","); pb(HEAP[loc(t)+1], depth-1); printf(")"); return; }
        if (!strcmp(nm, "@S1/base")) { printf("s1base"); return; }
        if (!strcmp(nm, "@S1/loop")) { printf("s1loop"); return; }
        if (!strcmp(nm, "@Quot/cl")) { printf("["); pb(HEAP[loc(t)], depth-1); printf("]"); return; }
        if (!strcmp(nm, "@Quot/eq")) { printf("eq/("); pb(HEAP[loc(t)], depth-1); printf(","); pb(HEAP[loc(t)+1], depth-1); printf(","); pb(HEAP[loc(t)+2], depth-1); printf(")"); return; }
        if (!strcmp(nm, "@Quot/sq")) { printf("squash/"); return; }
        printf("%s{", nm); for (uint32_t i = np; i < ar; i++) { if (i > np) printf(","); pb(HEAP[loc(t)+i], depth-1); } printf("}"); return; }
      if (!strcmp(nm, "h/Quot") && ar == 2) { printf("("); pb(HEAP[loc(t)], depth-1); printf(" / "); pb(HEAP[loc(t)+1], depth-1); printf(")"); return; }
      if (!strcmp(nm, "h/Trunc") && ar == 1) { printf("Trunc("); pb(HEAP[loc(t)], depth-1); printf(")"); return; }
      if (nm[0] == 'h' && nm[1] == '/') { printf("%s", nm + 2); if (ar) { printf("("); for (uint32_t i = 0; i < ar; i++) { if (i) printf(","); pb(HEAP[loc(t)+i], depth-1); } printf(")"); } return; }
      printf("%s", nm); if (ar) { printf("("); for (uint32_t i = 0; i < ar; i++) { if (i) printf(","); pb(HEAP[loc(t)+i], depth-1); } printf(")"); }
      return; }
    case T_SUP: { Term nm = whnf(HEAP[loc(t)]); int k = tag(nm) == T_IVAR ? label_of(loc(nm)) : -1;
      if (k >= 0) printf("&%d{", k); else printf("&{"); pb(HEAP[loc(t)+1], depth-1); printf(","); pb(HEAP[loc(t)+2], depth-1); printf("}"); return; }
    case T_LAM: { Term fr = HEAP[loc(t)+1]; Term g = generic(fr); uint32_t code = loc(HEAP[loc(t)]);
      const char *nm = bname(code); if (ext(g) < 4096) PNAMES[ext(g)] = nm;
      if (nm) printf("λ%s. ", nm); else printf("λx%u. ", ext(g)); pb(inst(CODE[code].a, g), depth-1); return; }
    case T_PLM: { Term fr = HEAP[loc(t)+1]; Term g = dim_push(fr); uint32_t code = loc(HEAP[loc(t)]);
      const char *nm = bname(code); if (ext(g) < 4096) PNAMES[ext(g)] = nm;
      if (nm) printf("<%s> ", nm); else printf("<i%u> ", loc(g)); pb(inst(CODE[code].a, g), depth-1); return; }
    case T_APP: { Term ivs[64]; uint32_t n; Term h = spine(t, ivs, &n);
      h = whnf(h); if (tag(h) == T_CTR && ctor_name(ctr_id(h))[0] == '@') { pb(h, depth-1); for (uint32_t i = 0; i < n; i++) { printf(" @ "); pb(ivs[i], depth-1); } return; }
      pb(h, depth-1); printf("("); for (uint32_t i = 0; i < n; i++) { if (i) printf(","); pb(ivs[i], depth-1); } printf(")"); return; }
    case T_I0: printf("i0"); return; case T_I1: printf("i1"); return;
    case T_IDNF: case T_INOT: case T_IAND: case T_IOR: print_rec(t, depth); return;
    case T_ERA: printf("*"); return;
    case T_REF: printf("%s", BOOK[loc(t)].name + (strncmp(BOOK[loc(t)].name, "b/", 2) ? 0 : 2)); return;
    case T_TRP: printf("coe("); pb(HEAP[loc(t)], depth-1); printf(","); pb(HEAP[loc(t)+1], depth-1); printf(","); pb(HEAP[loc(t)+2], depth-1); printf(","); pb(HEAP[loc(t)+3], depth-1); printf(")"); return;
    case T_HCM: printf("hcomp("); pb(HEAP[loc(t)], depth-1); printf(","); pb(HEAP[loc(t)+1], depth-1); printf(",{");
      for (Term l = whnf(HEAP[loc(t)+2]); tag(l) == T_CTR && ctr_id(l) == C_CONS; l = whnf(HEAP[loc(l)+1])) { Term f = whnf(HEAP[loc(l)]); pb(HEAP[loc(f)], depth-1); printf(" => "); pb(HEAP[loc(f)+1], depth-1); printf("; "); }
      printf("})"); return;
    case T_GLU: printf("Glue("); pb(HEAP[loc(t)], depth-1); printf(",{");
      for (Term l = whnf(HEAP[loc(t)+1]); tag(l) == T_CTR && ctr_id(l) == C_CONS; l = whnf(HEAP[loc(l)+1])) { Term f = whnf(HEAP[loc(l)]); pb(HEAP[loc(f)], depth-1); printf("=>("); pb(HEAP[loc(f)+1], depth-1); printf(","); pb(HEAP[loc(f)+2], depth-1); printf("); "); }
      printf("})"); return;
    case T_GLUE: printf("glue(_,"); pb(HEAP[loc(t)+1], depth-1); printf(",{");
      for (Term l = whnf(HEAP[loc(t)]); tag(l) == T_CTR && ctr_id(l) == C_CONS; l = whnf(HEAP[loc(l)+1])) { Term f = whnf(HEAP[loc(l)]); pb(HEAP[loc(f)], depth-1); printf("=>"); pb(HEAP[loc(f)+1], depth-1); printf("; "); }
      printf("})"); return;
    case T_UNGLUE: printf("unglue("); pb(HEAP[loc(t)], depth-1); printf(")"); return;
    case T_POUT: printf("pout("); pb(HEAP[loc(t)], depth-1); printf(")"); return;
    case T_VAR: if (ext(t) < 4096 && PNAMES[ext(t)]) printf("%s", PNAMES[ext(t)]); else printf("x%u", ext(t)); return;
    case T_IVAR: {                                 /* a bound dimension prints by its binder's name (the DIM frame records its level + 1) */
      uint64_t lv = HEAP[loc(t)+1];
      if (lv && lv - 1 < 4096 && PNAMES[lv - 1]) printf("%s", PNAMES[lv - 1]); else printf("i%u", loc(t)); return; }
    case T_CASE: {                                  /* Core.Type's Show of the eliminators */
      uint32_t code = loc(HEAP[loc(t)+1]); Term fr = HEAP[loc(t)+2]; SNode *n = &CODE[code];
      uint32_t first = n->b; uint32_t id0 = first ? CODE[first].ext : 0;
      const char *open = "~ ", *close = " }"; bool spaced = true;
      if (!first) { printf("~"); pb(HEAP[loc(t)], depth-1); printf("{}"); return; }
      if (id0 == C_NIL || id0 == C_CONS) spaced = false;
      printf("%s", open); pb(HEAP[loc(t)], depth-1); printf(" {%s", spaced ? " " : " ");
      bool firstb = true;
      for (uint32_t br = first; br; br = CODE[br].c) {
        SNode *b = &CODE[br]; if (!firstb) printf(spaced ? " ; " : " ; "); firstb = false;
        const char *cn = b->ext == 0xFFFFFF ? "" : ctor_name(b->ext);
        switch (b->ext) {
          case C_ZER: printf("0n: "); break; case C_SUC: printf("1n+: "); break;
          case C_NIL: printf("[]:"); break; case C_CONS: printf("<>:"); break;
          case C_TT: printf("(): "); break; case C_PAIR: printf("(,):"); break; case C_REFL: printf("{==}:"); break;
          case C_FALSE: printf("False: "); break; case C_TRUE: printf("True: "); break;
          case 0xFFFFFF: break;
          default: printf("%s: ", cn);
        }
        Term f = fr; uint32_t names = (uint32_t)b->num;
        for (uint32_t i = 0; i < b->a; i++) { f = generic(f); printf("λ%s. ", BNAMES ? BNAMES[names + i] : "x"); }
        pb(inst(b->b, f), depth-1);
      }
      printf("%s", close); return; }
    default: print_rec(t, depth);
  }
}
void print_bend(Term t, int depth) { pb(t, depth); }

/* Bend2's collapse: a superposition anywhere in a value is lifted to the top by the face map
   (the same choice name inside a branch is decided by the branch: fce annihilates it), and the
   branches are printed breadth-first, left before right (Core.Collapse.flatten). */
static Term lift(Term t, int depth) {
  if (depth <= 0) return t;
  t = whnf(t); if (tag(t) == T_SUP) t = prune(t);
  switch (tag(t)) {
    case T_SUP: return t;
    case T_CTR: {
      for (uint32_t i = 0; i < ctr_arity(t); i++) {
        Term f = lift(HEAP[loc(t)+i], depth-1); HEAP[loc(t)+i] = f;
        if (tag(f) == T_SUP) { Term nm = whnf(HEAP[loc(f)]); if (tag(nm) != T_IVAR) continue;
          Loc name = loc(nm);
          return node3(T_SUP, 0, nm, fce3(0, name, t, 0), fce3(1, name, t, 0)); }
      }
      return t; }
    case T_APP: { Term x = lift(HEAP[loc(t)+1], depth-1); HEAP[loc(t)+1] = x;
      if (tag(x) == T_SUP) { Term nm = whnf(HEAP[loc(x)]); if (tag(nm) == T_IVAR) return node3(T_SUP, 0, nm, fce3(0, loc(nm), t, 0), fce3(1, loc(nm), t, 0)); }
      return t; }
    default: return t;
  }
}
/* the leaves of a superposition tree, in collapse order; a value that is not superposed is one leaf */
int collapse_leaves(Term t, Term *out, int max) {
  Term q[1 << 12]; uint32_t head = 0, tail = 0; int n = 0; q[tail++] = t;
  while (head < tail && n < max) {
    Term v = lift(q[head++], 256);
    if (tag(v) == T_SUP) { if (tail + 2 < (1u << 12)) { q[tail++] = HEAP[loc(v)+1]; q[tail++] = HEAP[loc(v)+2]; } continue; }
    if (tag(v) == T_ERA) continue;
    out[n++] = v;
  }
  return n;
}
/* a value as its printed text, for comparison by identity of normal forms */
char *term_string(Term t, int depth) {
  char *buf = 0; size_t n = 0; FILE *m = open_memstream(&buf, &n); FILE *old = stdout;
  stdout = m; print_rec(t, depth); fflush(m); stdout = old; fclose(m);
  return buf;
}
void collapse_print(Term t) {
  Term q[1 << 16]; uint32_t head = 0, tail = 0; q[tail++] = t;
  while (head < tail) {
    Term v = lift(q[head++], 256);
    if (tag(v) == T_SUP) { if (tail + 2 < (1u << 16)) { q[tail++] = HEAP[loc(v)+1]; q[tail++] = HEAP[loc(v)+2]; } continue; }
    if (tag(v) == T_ERA) continue;
    pb(v, 256); printf("\n");
  }
}

Term run_def(uint32_t id) { return whnf(mk(T_REF, 0, id)); }

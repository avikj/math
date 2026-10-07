#include <execinfo.h>
#define _GNU_SOURCE
#include <math.h>
#include <sys/mman.h>
#include <pthread.h>
#include <sched.h>
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
/* ---- §9 parallel demand over the one arena (MAP §0.3 step 6) ----------------------------------------
   HYPER_PARALLEL=N serves independent demands on N workers over the one heap.  A demanded node fires once:
   CLAIM[loc] is its claim (0 free, 1 firing, 2 fired), taken by compare-and-swap in whnf, and a second
   demand of the same node waits for the result instead of firing it again.  Allocation is an atomic bump
   on the one reservation (a cell's address never changes), a receipt is an atomic slot in the trace, and
   the state a reduction carries (the node under reduction, the world, the waiting face) is per thread.
   The diamond fixes what the schedule may change: nothing.  The normal form, the interaction count and
   the words allocated are those of the sequential run; only the order of the receipts differs. */
int NPAR = 0; static uint8_t *CLAIM; __thread bool NO_COUNT; static bool node_redex(unsigned g);
static pthread_mutex_t KMUT = PTHREAD_MUTEX_INITIALIZER;          /* the rare shared tables: worlds, constructor names */
static pthread_mutex_t GMUT = PTHREAD_MUTEX_INITIALIZER;          /* the tables of closed cells and erasing matches, shared by the workers */
uint32_t *TRACE; uint64_t TRACE_LEN = 0; static uint64_t TRACE_CAP;

/* ---- heap ------------------------------------------------------------- */
static void heap_init(void) {
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
    void *cm = mmap(NULL, (size_t)HEAP_CAP, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (cm == MAP_FAILED) { fprintf(stderr, "hyper: cannot reserve the claims\n"); exit(2); }
    CLAIM = cm;
  }
}
Loc alloc(uint32_t n) {
  if (!HEAP) heap_init();
  Loc l = __atomic_fetch_add(&HEAP_LEN, n, __ATOMIC_RELAXED);
  if ((uint64_t)l + n >= HEAP_CAP) { fprintf(stderr, "hyper: heap exhausted\n"); exit(2); }
  return l;
}
Term node1(unsigned t, uint32_t e, Term a)                 { Loc l = alloc(2); HEAP[l]=a; HEAP[l+1]=0; return mk(t,e,l); }   /* two words: room for the result once reduced */
Term node2(unsigned t, uint32_t e, Term a, Term b)         { Loc l = alloc(2); HEAP[l]=a; HEAP[l+1]=b; return mk(t,e,l); }
Term node3(unsigned t, uint32_t e, Term a, Term b, Term c) { Loc l = alloc(3); HEAP[l]=a; HEAP[l+1]=b; HEAP[l+2]=c; return mk(t,e,l); }
Term node4(unsigned t, uint32_t e, Term a, Term b, Term c, Term d) { Loc l = alloc(4); HEAP[l]=a; HEAP[l+1]=b; HEAP[l+2]=c; HEAP[l+3]=d; return mk(t,e,l); }
/* a face map (side 0/1) or a substitution (side 2, by the interval `by`) applied to `target` */
Term fce_raw(unsigned side, Term name, Term target, Term by) { return node3(T_FCE, side, name, target, by); }
Term fce3(unsigned side, Loc name, Term target, Term by) { return fce_raw(side, mk(T_IVAR, 0, name), target, by); }

static void print_rec(Term t, int depth);
Loc *TRACE_NODE, *TRACE_HEAP; static __thread Loc CUR_NODE;
uint32_t *TRACE_WORLD; static __thread uint32_t WORLD;         /* the world (side of a superposition) each receipt fired in; 0 the root */
static uint32_t *WPARENT, NWORLD = 1, WCAP;            /* the tree of worlds */                 /* the node under reduction: each receipt names it (a Step's source) */
static void *reserve(size_t bytes) { void *m = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (m == MAP_FAILED) { fprintf(stderr, "hyper: cannot reserve the trace\n"); exit(2); } return m; }
static void receipt(unsigned rule) {
  if (NO_COUNT) return;                                                /* a definitional comparison is not an event */
  __atomic_fetch_add(&ITRS, 1, __ATOMIC_RELAXED);
  if (!TRACE) { pthread_mutex_lock(&KMUT); if (!TRACE) { TRACE_CAP = (uint64_t)1 << 28;    /* one reservation each, committed as written */
      TRACE_NODE = reserve(TRACE_CAP * sizeof(Loc)); TRACE_HEAP = reserve(TRACE_CAP * sizeof(Loc)); TRACE_WORLD = reserve(TRACE_CAP * sizeof(uint32_t));
      uint32_t *tr = reserve(TRACE_CAP * sizeof(uint32_t)); __atomic_store_n(&TRACE, tr, __ATOMIC_RELEASE); } pthread_mutex_unlock(&KMUT); }
  uint64_t i = __atomic_fetch_add(&TRACE_LEN, 1, __ATOMIC_RELAXED);
  if (i >= TRACE_CAP) { fprintf(stderr, "hyper: trace exhausted\n"); exit(2); }
  TRACE[i] = rule; TRACE_NODE[i] = CUR_NODE; TRACE_HEAP[i] = HEAP_LEN; TRACE_WORLD[i] = WORLD;
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
  pthread_mutex_lock(&KMUT);
  for (uint32_t i = 0; i < NCTORS; i++) if (!strcmp(CTORS[i], name)) { pthread_mutex_unlock(&KMUT); return C_USER_BASE + i; }
  CTORS = realloc(CTORS, (NCTORS + 1) * sizeof *CTORS);
  CTORS[NCTORS] = strdup(name);
  uint32_t id = C_USER_BASE + NCTORS++; pthread_mutex_unlock(&KMUT); return id;
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
  if (nf > 1 && !CHECK_MODE) {                       /* every face at a choice: one face carrying the set, taken in one pass */
    bool all = true; for (unsigned i = 0; i < nf; i++) if (ext(faces[i]) > 1 || tag(HEAP[loc(faces[i]) + 1]) != T_IVAR) all = false;
    if (all) { Term chain = 0; for (unsigned i = nf; i-- > 0;) chain = node3(T_RESTRICT, ext(faces[i]), chain, HEAP[loc(faces[i]) + 1], 0);   /* nearest first */
      return node3(T_FCE, 3, chain, v, 0); }
  }
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
    case S_REF: return mk(T_REF, 0, n->ext);
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
static bool ground(Term t, int depth); static bool ground_at(Term t, Loc name, int depth); static Term fce_set_apply(Term chain, Term v); static Term live_side(Term sup); static Term peek(Term t); static bool erasing_case(uint32_t code); static Term resolve_erasing(Term cs, Term sup); static int frame_side(Term fr, Loc name);
static bool frame_mentions(Term fr, uint32_t code, Loc name, int depth);
static bool lam_drops(Term f);
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
   name (endpoints and renaming), a variable (a VAR atom: substitution by a term), or, under the
   checker's hook, any cell (a semantic rewrite: what equals `nm` becomes `by`) */
static __thread Term FCE_SELF;                                   /* the face node being reduced: a face that waits is that node again, not a copy */
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
      { Term ls = live_side(v); if (ls) { receipt(R_ERASE); return fce_apply(nm, side, by, ls); } }
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
      if (ivar && ground_at(v, name, 1 << 16)) { receipt(R_FCE_SHARE); return v; }   /* nothing of this name below: the face is the identity on it */
      receipt(R_DUP_SUP_DIFFERENT);                       /* δᵢδⱼ = δⱼδᵢ */
      return node3(T_SUP, 0, sn, FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]));
    }
    case T_LAM: if (ivar && ground_at(v, name, 1 << 16)) { receipt(R_FCE_SHARE); return v; }
                receipt(lam_drops(v) ? R_DUP_LAM_ERASED : R_DUP_LAM_USED); return fce_closure(T_LAM, nm, side, by, v);
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
                receipt(R_FCE_SHARE); return v;                                                        /* another atom */
    case T_CTR: {
      uint32_t ar = ctr_arity(v);
      if (ar == 0) { receipt(R_FCE_SHARE); return v; }
      if (ivar ? ground_at(v, name, 1 << 16) : ground(v, 1 << 16)) { receipt(R_FCE_SHARE); return v; }   /* nothing in it for a face to meet: the face is the identity on it */
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
    case T_CASE: receipt(R_DUP_NODE); return whnf(case_restrict(v, nm, side, by, FCE_(HEAP[loc(v)])));
    case T_HELIM: receipt(R_DUP_NODE);
      return whnf(helim_restrict(v, nm, side, by, HEAP[loc(v)] ? FCE_(HEAP[loc(v)]) : 0, FCE_(HEAP[loc(v)+3])));
    case T_TRP:  receipt(R_DUP_NODE); return whnf(node4(T_TRP, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_PAP:  receipt(R_DUP_NODE); return whnf(node4(T_PAP, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_FCASE: receipt(R_DUP_NODE); return whnf(node4(T_FCASE, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2]), FCE_(HEAP[loc(v)+3])));
    case T_REFLECT: receipt(R_DUP_NODE); return whnf(node2(T_REFLECT, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
    case T_HCM:  receipt(R_DUP_NODE); return whnf(node3(T_HCM, 0, FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1]), FCE_(HEAP[loc(v)+2])));
    case T_OP2:  receipt(R_DUP_NODE); return whnf(node2(T_OP2, ext(v), FCE_(HEAP[loc(v)]), FCE_(HEAP[loc(v)+1])));
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



/* a side already erased: the superposition is its other side (peeked, nothing is evaluated here) */
static Term peek(Term t) { for (int g = 0; g < 1 << 12; g++) { if (node_redex(tag(t)) && tag(__atomic_load_n(&HEAP[loc(t)], __ATOMIC_ACQUIRE)) == T_IND) { t = HEAP[loc(t)+1]; continue; } return t; } return t; }
static bool peek_dead(Term t, int depth) { t = peek(t); if (tag(t) == T_ERA) return true;
  if (tag(t) == T_SUP && depth > 0) return peek_dead(HEAP[loc(t)+1], depth-1) && peek_dead(HEAP[loc(t)+2], depth-1); return false; }
static Term live_side(Term sup) {
  bool d0 = peek_dead(HEAP[loc(sup)+1], 64), d1 = peek_dead(HEAP[loc(sup)+2], 64);
  if (d0 && d1) return mk(T_ERA, 0, 0);
  if (d0) return HEAP[loc(sup)+2]; if (d1) return HEAP[loc(sup)+1]; return 0;
}

/* ---- an erasing match decides the worlds it meets ------------------------
   A match with `era` in a branch can kill a world.  Meeting a superposition, instead of commuting over it
   (which leaves every world standing, dead or not, for every later match to commute over again), it reads
   the chain of alternatives whole, runs on each in bisection order (the middle first, so what one
   alternative's comparisons kept decides its neighbours by recall), drops the worlds it erased, and is the
   superposition of the worlds that survive — one value when one survives. */
static uint8_t *ERASING; static uint32_t ERASING_LEN;
static bool code_has_era(uint32_t c, int depth) {
  if (!c || depth <= 0) return false; SNode *n = &CODE[c];
  if (n->tag == S_ERA) return true;
  if (n->tag == S_CTR) { uint32_t ar = n->ext & 0xFF; if (ar <= 4) { uint32_t k[4] = {n->a, n->b, n->c, n->d}; for (uint32_t i = 0; i < ar; i++) if (code_has_era(k[i], depth-1)) return true; return false; }
    for (uint32_t i = 0; i < ar; i++) if (code_has_era(KIDS[n->kids + i], depth-1)) return true; return false; }
  if (n->tag == S_NUM || n->tag == S_VAR || n->tag == S_REF || n->tag == S_IVAR || n->tag == S_LABEL) return false;
  return code_has_era(n->a, depth-1) || code_has_era(n->b, depth-1) || code_has_era(n->c, depth-1) || code_has_era(n->d, depth-1);
}
static bool erasing_case(uint32_t code) {
  pthread_mutex_lock(&GMUT);
  if (ERASING_LEN < CODE_LEN) { ERASING = realloc(ERASING, CODE_LEN); memset(ERASING + ERASING_LEN, 0, CODE_LEN - ERASING_LEN); ERASING_LEN = CODE_LEN; }
  if (!ERASING[code]) { SNode *n = &CODE[code]; bool e = false; for (uint32_t br = n->b; br; br = CODE[br].c) if (code_has_era(CODE[br].b, 64)) e = true; ERASING[code] = e ? 2 : 1; }
  bool r = ERASING[code] == 2; pthread_mutex_unlock(&GMUT); return r;
}
static Term resolve_erasing(Term cs, Term sup) {
  Term *alts = malloc((1 << 12) * sizeof(Term)), *nms = malloc((1 << 12) * sizeof(Term)), *res = malloc((1 << 12) * sizeof(Term));
  int k = 0; Term v = sup;
  for (;;) {                                                     /* the chain: left sides, then the last right side */
    Term nm = whnf(HEAP[loc(v)]); if (tag(nm) != T_IVAR) { free(alts); free(nms); free(res); return 0; }
    alts[k] = HEAP[loc(v)+1]; nms[k] = nm; k++;
    Term r = whnf(HEAP[loc(v)+2]);
    if (tag(r) == T_SUP && k < (1 << 12) - 1) { v = r; continue; }
    alts[k] = r; nms[k] = 0; k++; break;
  }
  Term fr0 = HEAP[loc(cs)+2], code = HEAP[loc(cs)+1];
  /* bisection order over the alternatives */
  int *order = malloc(k * sizeof(int)), on = 0; { int lo[64], hi[64], sp = 0; lo[sp] = 0; hi[sp] = k - 1; sp++;
    while (sp) { sp--; int l = lo[sp], h = hi[sp]; if (l > h) continue; int m = (l + h) / 2; order[on++] = m;
      if (sp + 2 < 64) { lo[sp] = m + 1; hi[sp] = h; sp++; lo[sp] = l; hi[sp] = m - 1; sp++; } } }
  int live = 0;
  for (int oi = 0; oi < on; oi++) { int i = order[oi];
    Term fr = fr0; for (int j = 0; j < i; j++) fr = restrict_push(fr, nms[j], 1, 0); if (i < k - 1) fr = restrict_push(fr, nms[i], 0, 0);   /* this world */
    Term r = whnf(node3(T_CASE, 0, alts[i], code, fr));
    if (tag(r) == T_ERA) receipt(R_ERASE); else live++;
    res[i] = r; }
  Term out;
  if (live == 0) out = mk(T_ERA, 0, 0);
  else { out = 0; for (int i = k; i-- > 0;) { if (tag(res[i]) == T_ERA) continue; out = out ? node3(T_SUP, 0, nms[i], res[i], out) : res[i]; } }
  free(alts); free(nms); free(res); free(order); return out;
}
/* ---- a face carrying a set of choices ----------------------------------
   A variable read through several world restrictions is one face carrying them all (frame_lookup), and the
   face passes through a value in one walk: a superposition at a name in the set is its side, a cell holding
   nothing of the set is shared, any other cell is copied once with the set on its parts. */
static Term chain_side(Term chain, Loc name) { for (Term ch = chain; ch; ch = HEAP[loc(ch)]) if (loc(HEAP[loc(ch)+1]) == name) return (Term)(ext(ch) + 1); return 0; }
static Term fset(Term chain, Term x) { return node3(T_FCE, 3, chain, x, 0); }
static bool ground_chain(Term v, Term chain) { for (Term ch = chain; ch; ch = HEAP[loc(ch)]) if (!ground_at(v, loc(HEAP[loc(ch)+1]), 1 << 16)) return false; return true; }
static Term chain_push(Term fr, Term chain) {                  /* the set onto a frame, farthest first so the nearest is on top */
  Term cs[64]; unsigned n = 0; for (Term ch = chain; ch && n < 64; ch = HEAP[loc(ch)]) cs[n++] = ch;
  for (unsigned i = n; i-- > 0;) fr = restrict_push(fr, HEAP[loc(cs[i])+1], ext(cs[i]), 0);
  return fr;
}
static Term fce_set_apply(Term chain, Term v) {
  v = whnf(v);
  switch (tag(v)) {
    case T_SUP: { { Term ls = live_side(v); if (ls) { receipt(R_ERASE); return fce_set_apply(chain, ls); } }
      Term sn = whnf(HEAP[loc(v)]);
      if (tag(sn) == T_IVAR) { Term s = chain_side(chain, loc(sn));
        if (s) { receipt(R_DUP_SUP_EQUAL); return fce_set_apply(chain, HEAP[loc(v) + s]); }
        if (ground_chain(v, chain)) { receipt(R_FCE_SHARE); return v; }
        receipt(R_DUP_SUP_DIFFERENT); return node3(T_SUP, 0, sn, fset(chain, HEAP[loc(v)+1]), fset(chain, HEAP[loc(v)+2])); }
      break; }
    case T_CTR: { uint32_t ar = ctr_arity(v);
      if (ar == 0 || ground_chain(v, chain)) { receipt(R_FCE_SHARE); return v; }
      receipt(R_DUP_NODE); Loc l = alloc(ar); for (uint32_t i = 0; i < ar; i++) HEAP[l+i] = fset(chain, HEAP[loc(v)+i]);
      return mk(T_CTR, ext(v), l); }
    case T_LAM: case T_PLM:
      if (ground_chain(v, chain)) { receipt(R_FCE_SHARE); return v; }
      receipt(tag(v) == T_LAM && lam_drops(v) ? R_DUP_LAM_ERASED : R_DUP_LAM_USED);
      return node2(tag(v), 0, HEAP[loc(v)], chain_push(HEAP[loc(v)+1], chain));
    case T_CASE: receipt(R_DUP_NODE); return whnf(node3(T_CASE, 0, fset(chain, HEAP[loc(v)]), HEAP[loc(v)+1], chain_push(HEAP[loc(v)+2], chain)));
    case T_IVAR: { Term s = chain_side(chain, loc(v)); if (s) { receipt(R_DUP_SUP_EQUAL); return mk(s == 2 ? T_I1 : T_I0, 0, 0); } receipt(R_FCE_SHARE); return v; }
    case T_NUM: case T_ERA: case T_REF: case T_I0: case T_I1: case T_VAR: receipt(R_FCE_SHARE); return v;
    case T_OP2: receipt(R_DUP_NODE); return whnf(node2(T_OP2, ext(v), fset(chain, HEAP[loc(v)]), fset(chain, HEAP[loc(v)+1])));
    case T_OP1: receipt(R_DUP_NODE); return whnf(node1(T_OP1, ext(v), fset(chain, HEAP[loc(v)])));
    default: break;
  }
  Term cs[64]; unsigned n = 0; for (Term ch = chain; ch && n < 64; ch = HEAP[loc(ch)]) cs[n++] = ch;   /* any other form: the faces one by one, farthest innermost */
  for (unsigned i = n; i-- > 0;) v = fce_raw(ext(cs[i]), HEAP[loc(cs[i])+1], v, 0);
  return whnf(v);
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
/* the faces in force on a frame: the world its bodies live in */
static int frame_side(Term fr, Loc name) { for (Term f = fr; tag(f); f = HEAP[loc(f)]) if (tag(f) == T_RESTRICT && ext(f) < 2 && loc(whnf(HEAP[loc(f)+1])) == name) return (int)ext(f); return -1; }

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


/* ---- ground cells and retained applications ---------------------------------
   A ground cell is a constructor tree of literals already built: no name occurs in it, so a face maps it to
   itself (shared, not copied), and an application of one closure cell to one ground cell is one derivation —
   the result is kept and a second demand of the same application is answered from it (a "recall").  Nothing the
   machine derived about a value is derived again in another world of a superposition. */
#define GR_N (1u << 22)
static uint64_t *GR_SET;                                           /* open addressing over cell addresses known ground */
static uint64_t gr_hash(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; return k; }
static bool gr_has(Loc l) { if (!GR_SET) return false; uint64_t h = gr_hash(l) & (GR_N - 1); while (GR_SET[h]) { if (GR_SET[h] == (uint64_t)l + 1) return true; h = (h + 1) & (GR_N - 1); } return false; }
static void gr_add(Loc l) { if (!GR_SET) GR_SET = calloc(GR_N, sizeof(uint64_t)); uint64_t h = gr_hash(l) & (GR_N - 1); while (GR_SET[h]) { if (GR_SET[h] == (uint64_t)l + 1) return; h = (h + 1) & (GR_N - 1); } GR_SET[h] = (uint64_t)l + 1; }
static Loc *GR_BUSY; static uint32_t GR_NBUSY; static Loc GR_NAME; static bool GR_REL;                     /* cells under inspection: a knot that meets itself is closed */
static uint64_t *GR_SET_AT;                                        /* (cell, name) pairs known to hold nothing of that name */
static uint64_t gr_key_at(Loc l, Loc name) { return ((uint64_t)l << 32 | name) + 1; }
static bool gr_has_at(Loc l, Loc name) { if (!GR_SET_AT) return false; uint64_t k = gr_key_at(l, name), h = gr_hash(k) & (GR_N - 1); while (GR_SET_AT[h]) { if (GR_SET_AT[h] == k) return true; h = (h + 1) & (GR_N - 1); } return false; }
static void gr_add_at(Loc l, Loc name) { if (!GR_SET_AT) GR_SET_AT = calloc(GR_N, sizeof(uint64_t)); uint64_t k = gr_key_at(l, name), h = gr_hash(k) & (GR_N - 1); uint32_t n = 0; while (GR_SET_AT[h]) { if (GR_SET_AT[h] == k) return; h = (h + 1) & (GR_N - 1); if (++n > GR_N / 2) return; } GR_SET_AT[h] = k; }
static bool node_redex(unsigned g);

/* a definition whose body holds a superposition (or a label, a dimension, a face) anywhere: a reference to it is not closed */
static uint8_t *DEF_SUPS; static uint32_t DEF_SUPS_LEN;
static bool code_has_sup(uint32_t c, int depth) {
  if (!c || depth <= 0) return depth <= 0; SNode *n = &CODE[c];
  switch (n->tag) {
    case S_SUP: case S_LABEL: case S_DIM: case S_FCE: case S_ISUB: case S_IVAR: return true;
    case S_NUM: case S_VAR: case S_ERA: case S_I0: case S_I1: return false;
    case S_REF: return false;                                  /* read through its own entry when met */
    case S_CTR: { uint32_t ar = n->ext & 0xFF; if (ar <= 4) { uint32_t k[4] = {n->a, n->b, n->c, n->d}; for (uint32_t i = 0; i < ar; i++) if (code_has_sup(k[i], depth-1)) return true; return false; }
      for (uint32_t i = 0; i < ar; i++) if (code_has_sup(KIDS[n->kids + i], depth-1)) return true; return false; }
    default: return code_has_sup(n->a, depth-1) || code_has_sup(n->b, depth-1) || code_has_sup(n->c, depth-1) || code_has_sup(n->d, depth-1);
  }
}
static bool def_has_sup(uint32_t id) {                           /* under GMUT: called from ground_ */
  if (DEF_SUPS_LEN < BOOK_LEN) { DEF_SUPS = realloc(DEF_SUPS, BOOK_LEN); memset(DEF_SUPS + DEF_SUPS_LEN, 0, BOOK_LEN - DEF_SUPS_LEN); DEF_SUPS_LEN = BOOK_LEN; }
  if (!DEF_SUPS[id]) DEF_SUPS[id] = (BOOK[id].unknown || code_has_sup(BOOK[id].code, 256)) ? 2 : 1;
  return DEF_SUPS[id] == 2;
}
static bool ground_(Term t, int depth) {
  if (depth <= 0) return false;
  for (;;) {
    switch (tag(t)) {
      case T_NUM: case T_I0: case T_I1: case T_ERA: return true;
      case T_REF: if (!def_has_sup(loc(t))) return true;                           /* its body holds no superposition */
        GR_REL = true; return GR_NAME && label_of(GR_NAME) < 0;                    /* a fresh name (dim) cannot be in a body; a static label can */
      case T_CTR: case T_LAM: break;
      case T_APP: case T_OP2: case T_OP1: case T_CASE: case T_PROJ:                 /* a fired node: its result (the mark in word 0) */
        if (tag(__atomic_load_n(&HEAP[loc(t)], __ATOMIC_ACQUIRE)) == T_IND) { t = HEAP[loc(t)+1]; continue; }
        break;
      case T_IVAR: GR_REL = true; return GR_NAME && loc(t) != GR_NAME;                 /* another name */
      case T_VAR: GR_REL = true; return GR_NAME != 0;                                   /* an atom, not a name */
      case T_SUP: if (!GR_NAME) return false; GR_REL = true; break;                 /* read relative to a name only */
      case T_FCE: if (!GR_NAME) return false; GR_REL = true;
        if (tag(__atomic_load_n(&HEAP[loc(t)], __ATOMIC_ACQUIRE)) == T_IND) { t = HEAP[loc(t)+1]; continue; }
        break;
      default: return false;                                   /* a form not read here */
    }
    Loc l = loc(t);
    if (gr_has(l)) return true;
    if (GR_NAME && gr_has_at(l, GR_NAME)) return true;
    for (uint32_t i = 0; i < GR_NBUSY; i++) if (GR_BUSY[i] == l) return true;
    if (!GR_BUSY) GR_BUSY = malloc((1 << 16) * sizeof(Loc));
    if (GR_NBUSY >= (1 << 16)) return false;
    GR_BUSY[GR_NBUSY++] = l; bool ok = true;
    switch (tag(t)) {
      case T_CTR: for (uint32_t i = 0; ok && i < ctr_arity(t); i++) ok = ground_(HEAP[l+i], depth-1); break;
      case T_LAM: { Term fr = HEAP[l+1];                        /* the closure's frame: every slot closed, no binder of a dimension, no face taken */
        for (int g = 0; ok && tag(fr) && g < 4096; g++) {
          if (tag(fr) == T_FRAME) ok = ground_(HEAP[loc(fr)+1], depth-1);
          else if (tag(fr) == T_DIM) { GR_REL = true; ok = loc(fr) != GR_NAME; }                 /* a binder of another dimension */
          else if (tag(fr) == T_RESTRICT) { GR_REL = true; if (GR_NAME && loc(HEAP[loc(fr)+1]) == GR_NAME && ext(fr) < 2) break; } /* a face at the name already taken here: spent */
          else ok = false;
          fr = HEAP[loc(fr)]; }
        break; }
      case T_CASE: { Term fr = HEAP[l+2]; bool shielded = false;
        for (int g = 0; ok && tag(fr) && g < 4096; g++) {
          if (tag(fr) == T_FRAME) ok = ground_(HEAP[loc(fr)+1], depth-1);
          else if (tag(fr) == T_DIM) { GR_REL = true; ok = loc(fr) != GR_NAME; }
          else if (tag(fr) == T_RESTRICT) { GR_REL = true; if (GR_NAME && loc(HEAP[loc(fr)+1]) == GR_NAME && ext(fr) < 2) { shielded = true; break; } }   /* a face at the name already taken here */
          else ok = false;
          fr = HEAP[loc(fr)]; }
        if (ok && !shielded) ok = ground_(HEAP[l], depth-1);
        break; }
      case T_OP1: ok = ground_(HEAP[l], depth-1); break;
      case T_SUP: { Term nm = HEAP[l]; if (tag(nm) == T_IND) nm = HEAP[loc(nm)];
        ok = tag(nm) == T_IVAR && loc(nm) != GR_NAME && ground_(HEAP[l+1], depth-1) && ground_(HEAP[l+2], depth-1); break; }
      case T_FCE: { Term nm = HEAP[l]; if (tag(nm) == T_IND) nm = HEAP[loc(nm)];
        if (ext(t) == 3) { bool in = false; for (Term ch = nm; ch; ch = HEAP[loc(ch)]) if (loc(HEAP[loc(ch)+1]) == GR_NAME) in = true;
          ok = in || ground_(HEAP[l+1], depth-1); break; }                 /* a set face: the name spent if in the set */
        if (tag(nm) != T_IVAR) { ok = false; break; }
        if (loc(nm) == GR_NAME && ext(t) < 2) { ok = true; break; }       /* a face at this name already taken below: the name is spent there */
        ok = loc(nm) != GR_NAME && ground_(HEAP[l+1], depth-1) && (ext(t) != 2 || ground_(HEAP[l+2], depth-1)); break; }
      default: ok = ground_(HEAP[l], depth-1) && ground_(HEAP[l+1], depth-1); break;   /* APP, OP2, PROJ */
    }
    GR_NBUSY--;
    if (ok && !GR_REL) gr_add(l); else if (ok && GR_NAME) gr_add_at(l, GR_NAME);
    return ok;
  }
}

static bool ground(Term t, int depth) { pthread_mutex_lock(&GMUT); GR_NBUSY = 0; GR_REL = false; GR_NAME = 0; bool r = ground_(t, depth); r = r && !GR_REL; pthread_mutex_unlock(&GMUT); return r; }   /* closed outright */
static bool ground_at(Term t, Loc name, int depth) { pthread_mutex_lock(&GMUT); GR_NBUSY = 0; GR_REL = false; GR_NAME = name; bool r = ground_(t, depth); pthread_mutex_unlock(&GMUT); return r; }    /* nothing of this name in it */
#define AM_N (1u << 22)
typedef struct { uint64_t key; Term val; } AMem;
static AMem *AMEM;
static AMem *am_slot(uint64_t key) {
  if (!AMEM) AMEM = calloc(AM_N, sizeof(AMem));
  uint64_t h = gr_hash(key) & (AM_N - 1); uint32_t tries = 0;
  while (AMEM[h].key && AMEM[h].key != key) { h = (h + 1) & (AM_N - 1); if (++tries > 64) return 0; }
  return &AMEM[h];
}
/* ---- numbers ---------------------------------------------------------- */
static Term boolc(bool b) { return mk(T_CTR, ctr_ext(b ? C_TRUE : C_FALSE, 0), alloc(1)); }

/* ---- retained comparisons ----------------------------------------------
   A comparison of two literals is an interaction that yields an order fact; the fact is kept, with its
   transitive closure, and a later comparison the kept facts already decide is answered from them (a
   "recall" receipt, not a comparison).  Nothing a comparison told the machine is ever asked again:
   across the worlds of a superposition the same pair is compared once, and a pair two kept facts
   order is never compared at all. */
#define RT_N 4096
#define RT_W (RT_N / 64)
static uint32_t RT_CNT; static uint64_t RT_VAL[RT_N]; static unsigned RT_KIND[RT_N];
static uint64_t (*RT_LE)[RT_W], (*RT_LT)[RT_W];                 /* LE[u] ∋ v: u ≤ v is kept; LT[u] ∋ v: u < v is kept */
#define RTB(S, i, j) (((S)[i][(j) >> 6] >> ((j) & 63)) & 1)
#define RTS(S, i, j) ((S)[i][(j) >> 6] |= (uint64_t)1 << ((j) & 63))
static int rt_node(unsigned kind, uint64_t v) {
  for (uint32_t i = 0; i < RT_CNT; i++) if (RT_VAL[i] == v && RT_KIND[i] == kind) return (int)i;
  if (RT_CNT >= RT_N) return -1;
  if (!RT_LE) { RT_LE = calloc(RT_N, sizeof *RT_LE); RT_LT = calloc(RT_N, sizeof *RT_LT); }
  RT_VAL[RT_CNT] = v; RT_KIND[RT_CNT] = kind; return (int)RT_CNT++;
}
static void rt_keep(int a, int b) {                               /* the fact a < b, closed transitively */
  for (uint32_t u = 0; u < RT_CNT; u++) {
    if (!((int)u == a || RTB(RT_LE, u, a))) continue;
    for (int w = 0; w < RT_W; w++) { RT_LE[u][w] |= RT_LE[b][w]; RT_LT[u][w] |= RT_LE[b][w] | RT_LT[b][w]; }
    RTS(RT_LE, u, b); RTS(RT_LT, u, b);
  }
}
/* 1: the comparison is decided by kept facts (*out set); 0: it is not, compare and keep */
static int rt_decide(unsigned op, int a, int b, bool *out) {
  if (a < 0 || b < 0) return 0;
  bool lt = RTB(RT_LT, a, b), gt = RTB(RT_LT, b, a), le = a == b || RTB(RT_LE, a, b), ge = a == b || RTB(RT_LE, b, a);
  switch (op) {
    case OP_LT: if (lt) { *out = true; return 1; } if (ge) { *out = false; return 1; } return 0;
    case OP_LE: if (le) { *out = true; return 1; } if (gt) { *out = false; return 1; } return 0;
    case OP_GT: if (gt) { *out = true; return 1; } if (le) { *out = false; return 1; } return 0;
    case OP_GE: if (ge) { *out = true; return 1; } if (lt) { *out = false; return 1; } return 0;
    case OP_EQ: if (a == b) { *out = true; return 1; } if (lt || gt) { *out = false; return 1; } return 0;
    case OP_NE: if (a == b) { *out = false; return 1; } if (lt || gt) { *out = true; return 1; } return 0;
  }
  return 0;
}
static bool is_cmp(unsigned op) { return op == OP_LT || op == OP_LE || op == OP_GT || op == OP_GE || op == OP_EQ || op == OP_NE; }
/* the comparison of two integer literals: recalled if kept facts decide it, else compared once and kept */
static Term op2_retained(unsigned op, unsigned kind, uint64_t a, uint64_t b) {
  pthread_mutex_lock(&KMUT);
  int na = rt_node(kind, a), nb = rt_node(kind, b); bool r;
  if (rt_decide(op, na, nb, &r)) { pthread_mutex_unlock(&KMUT); receipt(R_RECALL); return boolc(r); }
  if (getenv("HYPER_CMP")) fprintf(stderr, "cmp %llu %llu\n", (unsigned long long)a, (unsigned long long)b);
  bool less = kind == N_I64 ? (int64_t)a < (int64_t)b : a < b;    /* one comparison of the two literals: the order between them */
  if (na >= 0 && nb >= 0 && a != b) { if (less) rt_keep(na, nb); else rt_keep(nb, na); }
  pthread_mutex_unlock(&KMUT); receipt(R_OP2);
  switch (op) {
    case OP_LT: return boolc(a != b && less); case OP_LE: return boolc(a == b || less);
    case OP_GT: return boolc(a != b && !less); case OP_GE: return boolc(a == b || !less);
    case OP_EQ: return boolc(a == b); default: return boolc(a != b);
  }
}

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

/* ---- §9 the schedule: which of two independent demands is served first ----------------------------- */
/* HYPER_SCHEDULE=right serves the right one, a number seeds a coin per choice, the default is left.  The
   redex bag is the only scheduler, so the normal form and the count must not depend on it (Krama, §10.7). */
static unsigned SCHED; static __thread uint64_t SCHED_RNG; static uint64_t SCHED_SEED;
void sched_init(void) { const char *s = getenv("HYPER_SCHEDULE"); if (!s || !*s) return;
  if (!strcmp(s, "right")) SCHED = 1; else { SCHED = 2; SCHED_SEED = strtoull(s, 0, 10) * 2654435761ull + 88172645463325252ull; SCHED_RNG = SCHED_SEED; } }
static bool right_first(void) {
  if (SCHED < 2) return SCHED;
  SCHED_RNG ^= SCHED_RNG << 13; SCHED_RNG ^= SCHED_RNG >> 7; SCHED_RNG ^= SCHED_RNG << 17; return SCHED_RNG & 1;
}
/* ---- §9 the pool: the workers that serve spawned demands ------------------------------------------- */
static pthread_mutex_t QM = PTHREAD_MUTEX_INITIALIZER; static pthread_cond_t QC = PTHREAD_COND_INITIALIZER;
static Term *Q; static unsigned QCAP = 1u << 14, QH, QT; static int BUSY; static bool QUIT; static unsigned NSPAWN;
void par_spawn(Term t) {                                /* a hint: a demand that will be served anyway, offered to a worker */
  if (!NPAR || !node_redex(tag(t)) || __atomic_load_n(&CLAIM[loc(t)], __ATOMIC_RELAXED)) return;
  pthread_mutex_lock(&QM);
  if (QT - QH < QCAP) { Q[QT++ % QCAP] = t; NSPAWN++; pthread_cond_signal(&QC); }
  pthread_mutex_unlock(&QM);
}
static void *worker(void *arg) {
  SCHED_RNG = SCHED_SEED ^ ((uint64_t)(uintptr_t)arg * 0x9E3779B97F4A7C15ull);
  for (;;) {
    pthread_mutex_lock(&QM);
    while (QH == QT && !QUIT) pthread_cond_wait(&QC, &QM);
    if (QH == QT) { pthread_mutex_unlock(&QM); return 0; }
    Term t = Q[QH++ % QCAP]; BUSY++; pthread_mutex_unlock(&QM);
    whnf(t);
    pthread_mutex_lock(&QM); BUSY--; pthread_mutex_unlock(&QM);
  }
}
void par_init(void) {
  const char *s = getenv("HYPER_PARALLEL"); NPAR = s && *s ? atoi(s) : 0; if (NPAR <= 0) { NPAR = 0; return; }
  for (uint32_t i = 1; i < CODE_LEN; i++) if (CODE[i].tag == S_TRACE) {   /* a run traced as a term is its own events alone: one thread */
    if (getenv("HYPER_DEBUG")) fprintf(stderr, "hyper: parallel demand off: the book traces a run\n"); NPAR = 0; return; }
  heap_init(); Q = malloc(QCAP * sizeof(Term));
  pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);   /* deep terms recurse deep */
  for (int i = 0; i < NPAR; i++) { pthread_t th; if (pthread_create(&th, &at, worker, (void *)(uintptr_t)(i + 1))) { fprintf(stderr, "hyper: cannot start a worker\n"); exit(2); } pthread_detach(th); }
}
void par_drain(void) {                                  /* every spawned demand served: the arena is quiet */
  if (!NPAR) return;
  for (;;) { pthread_mutex_lock(&QM); bool idle = QH == QT && BUSY == 0; pthread_mutex_unlock(&QM); if (idle) return; sched_yield(); }
}
unsigned par_spawned(void) { return NSPAWN; }

/* a projection demands every field: under a schedule other than the default they are forced in its order
   first, each written back into its field, and the printer then meets values */
void force_fields(Term t, int depth) {
  if (depth <= 0 || (!SCHED && !NPAR)) return; t = whnf(t);
  if (tag(t) == T_CTR) { uint32_t ar = ctr_arity(t); bool rev = right_first();
    if (NPAR) for (uint32_t i = 0; i < ar; i++) par_spawn(HEAP[loc(t)+i]);
    for (uint32_t k = 0; k < ar; k++) { uint32_t i = rev ? ar - 1 - k : k; HEAP[loc(t)+i] = whnf(HEAP[loc(t)+i]); force_fields(HEAP[loc(t)+i], depth-1); } }
  else if (tag(t) == T_SUP) { bool rev = right_first(); uint32_t f = rev ? 2 : 1, g = rev ? 1 : 2;
    if (NPAR) { par_spawn(HEAP[loc(t)+1]); par_spawn(HEAP[loc(t)+2]); }
    HEAP[loc(t)+f] = whnf(HEAP[loc(t)+f]); force_fields(HEAP[loc(t)+f], depth-1); HEAP[loc(t)+g] = whnf(HEAP[loc(t)+g]); force_fields(HEAP[loc(t)+g], depth-1); }
}

/* ---- the loop (§3): weak head, demanded interaction ---------------------- */
static __thread uint64_t WHNF_STEPS;
/* a node that a rule may fire on, and whose first word is a term (so the mark T_IND cannot be mistaken).
   REFLECT is not one: it is the checker's view of a typed point (§7), read by its cell, never marked. */
static Term prune(Term t); static Term trace_over(Term v, uint64_t from); static Term lift(Term t, int depth); static uint32_t side_world(Term sup, unsigned side); static bool world_within(uint32_t w, uint32_t of);
static bool node_redex(unsigned g) {
  switch (g) { case T_APP: case T_FCE: case T_PROJ: case T_CASE: case T_OP2: case T_OP1: case T_TRP: case T_HCM: case T_HELIM: case T_CHK:
    case T_UNGLUE: case T_GBASE: case T_GFACES: case T_FCASE: case T_CFIELDS: case T_CWITH: case T_PAP: case T_ETYPE: case T_ETERM: case T_POUT: case T_TRACE: case T_LEAVES: return true;
    default: return false; }
}
static Term whnf_(Term t);
/* a demanded port fires once: the node a holder points at is marked with its result, and every other holder
   of the same node meets the value (the sharing of §3 is at every port) */
Term whnf(Term t) {
  if (NPAR && node_redex(tag(t))) {                     /* the claim: fire once across the workers, or wait for the result */
    Loc l = loc(t);
    for (;;) {
      uint8_t st = __atomic_load_n(&CLAIM[l], __ATOMIC_ACQUIRE);
      if (st == 2) return HEAP[l+1];
      uint8_t z = 0; if (st == 0 && __atomic_compare_exchange_n(&CLAIM[l], &z, 1, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) break;
      sched_yield();
    }
    Loc outer = CUR_NODE; Term r = whnf_(t); CUR_NODE = outer;
    if (r != t) { HEAP[l+1] = r; __atomic_store_n(&HEAP[l], mk(T_IND, 0, 0), __ATOMIC_RELEASE); __atomic_store_n(&CLAIM[l], 2, __ATOMIC_RELEASE); }
    else __atomic_store_n(&CLAIM[l], 0, __ATOMIC_RELEASE);          /* stuck: nothing fired, the claim is returned */
    return r;
  }
  Loc outer = CUR_NODE; Term r = whnf_(t); CUR_NODE = outer;   /* a nested reduction names its own nodes; the outer resumes naming its own */
  if (r != t && node_redex(tag(t))) { HEAP[loc(t)] = mk(T_IND, 0, 0); HEAP[loc(t)+1] = r; }
  return r;
}
static Term whnf_(Term t) {
  for (;;) {
    CUR_NODE = loc(t);
    if (node_redex(tag(t)) && tag(__atomic_load_n(&HEAP[loc(t)], __ATOMIC_ACQUIRE)) == T_IND) { t = HEAP[loc(t)+1]; continue; }   /* already fired: its result */
    if (CHECK_MODE && ++WHNF_STEPS > 30000000 && getenv("HYPER_DEBUG")) { fprintf(stderr, "whnf: runaway at tag %u: ", tag(t)); print_rec(t, 5); fprintf(stderr, "\n"); fflush(stdout); exit(9); }
    switch (tag(t)) {
      case T_VAR: {                                   /* a variable: its slot, forced once and written back */
        Loc slot = loc(t) + 1; Term v = HEAP[slot];
        if (tag(v) == T_VAR && loc(v) == loc(t)) {            /* a generic element: its own slot */
          return t; }
        v = whnf(v); HEAP[slot] = v; return v;
      }
      case T_REF: {                                   /* δ: the definition's own fresh dimensions */
        Def *d = &BOOK[loc(t)]; Term fr = 0;
        if (d->unknown) {                            /* a declaration with no body: the census of the book at its type (MAP §0.3 step 5) */
          Term ty = whnf(inst(d->type, 0)); bool map = tag(ty) == T_CTR && ctr_id(ty) == C_PI;
          int e = map ? resolve_declaration_q(loc(t), true) : resolve_declaration(loc(t));
          if (e < 0) { if (map) return t; exit(2); }               /* a map with no entry of its type resolves at its arguments (the application below) */
          d->code = BOOK[e].code; d->ndims = BOOK[e].ndims; d->unknown = false; receipt(R_DECLARE); }
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
        if (tag(f) == T_REF || tag(f) == T_APP) {           /* a declaration with no body at its arguments: the census at the point of demand */
          Term args[64]; uint32_t n; Term h = spine(node2(T_APP, 0, f, x), args, &n);
          if (tag(h) == T_REF && BOOK[loc(h)].unknown) {
            int st; Term p = resolve_applied(h, args, n, &st);
            if (st == 1) { receipt(R_DECLARE); t = p; continue; }
            if (st == 0) return t;                            /* more arguments wanted: the partial application stands */
            exit(2); } }
        switch (tag(f)) {
          case T_ERA: return f;
          case T_LAM: {
            if (!NPAR && !CHECK_MODE) {            /* the application of this closure cell to this ground cell: derived once */
              Term xv = peek(x);                   /* an argument already a value; nothing is forced here (§3.3: a port not demanded costs nothing) */
              if (tag(xv) == T_NUM || (tag(xv) == T_CTR && ground(xv, 1 << 16))) {
                uint64_t key = ((uint64_t)loc(f) << 32) ^ (uint64_t)loc(xv) ^ ((uint64_t)tag(xv) << 60) ^ ((uint64_t)ext(xv) << 40);
                if (tag(xv) == T_NUM) key ^= HEAP[loc(xv)] * 0x9E3779B97F4A7C15ULL;
                AMem *s = am_slot(key);
                if (s && s->key == key) { receipt(R_RECALL); return s->val; }
                receipt(R_BETA); if (lam_drops(f)) receipt(R_ERASE);
                Term r = whnf(open_closure(f, xv));
                if (s && !s->key) { s->key = key; s->val = r; }
                return r;
              }
            }
            receipt(R_BETA); if (lam_drops(f)) receipt(R_ERASE); t = open_closure(f, x); continue; }
          case T_PLM: receipt(R_APP_PLM); t = open_closure(f, x); continue;
          case T_SUP: {                               /* distribute; the argument face-mapped at the name */
            { Term ls = live_side(f); if (ls) { receipt(R_ERASE); HEAP[loc(t)] = ls; continue; } }
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
        if (ext(t) == 3) return fce_set_apply(HEAP[loc(t)], HEAP[loc(t) + 1]);
        Term nm = whnf(HEAP[loc(t)]);
        HEAP[loc(t)] = nm; FCE_SELF = t;
        return fce_apply(nm, ext(t), HEAP[loc(t) + 2], HEAP[loc(t) + 1]);
      }
      case T_CASE: {
        Term s0 = whnf(HEAP[loc(t)]);
        if (tag(s0) == T_ERA) return s0;                     /* a dead scrutinee: the match is dead */
        switch (tag(s0)) {
          case T_CTR: receipt(R_CASE); t = case_select(t, s0); continue;
          case T_SUP: {                                /* a match commutes over a superposition; a name its frame fixes is projected */
            { Term ls = live_side(s0); if (ls) { receipt(R_ERASE); HEAP[loc(t)] = ls; continue; } }   /* a dead side: the match is on the live one */
            Term nm = whnf(HEAP[loc(s0)]);
            if (!CHECK_MODE && tag(nm) == T_IVAR && frame_side(HEAP[loc(t)+2], loc(nm)) < 0 && erasing_case(loc(HEAP[loc(t)+1]))) {
              Term r = resolve_erasing(t, s0); if (r) return r; }   /* an erasing match decides the worlds it meets */
            { int w = tag(nm) == T_IVAR ? frame_side(HEAP[loc(t)+2], loc(nm)) : -1; if (w >= 0) { HEAP[loc(t)] = HEAP[loc(s0) + 1 + w]; continue; } }
            receipt(R_CASE_SUP);
            return node3(T_SUP, 0, nm, case_restrict(t, nm, 0, 0, HEAP[loc(s0)+1]),
                                       case_restrict(t, nm, 1, 0, HEAP[loc(s0)+2]));
          }
          default: HEAP[loc(t)] = s0; return t;        /* stuck */
        }
      }
      case T_TRACE: {                                 /* the run of e as a term: (value, events), each event the rule and the words it allocated
                                                         (research/sat_fibre/InteractionLedger.agda: Trace, Charge; the trace lives over the result) */
        uint64_t from = TRACE_LEN; Term v = nf(HEAP[loc(t)], 256);
        return trace_over(v, from);
      }
      case T_LEAVES: {                                /* the leaves of a superposition as a list, dead sides dropped */
        Term *out = malloc((1 << 14) * sizeof(Term)); int n = collapse_leaves(HEAP[loc(t)], out, 1 << 14);
        Term l = nil_cell(); for (int i = n; i-- > 0;) l = cons_cell(out[i], l);
        free(out); return l;
      }
      case T_OP2: {
        bool rf = right_first();
        if (NPAR) par_spawn(rf ? HEAP[loc(t)] : HEAP[loc(t)+1]);     /* §9: the other operand is an independent demand */
        if (rf) HEAP[loc(t)+1] = whnf(HEAP[loc(t)+1]);               /* §9: the other schedule serves the right operand first */
        Term a = whnf(HEAP[loc(t)]);
        if (tag(a) == T_SUP) { Term ls = live_side(a); if (ls) { receipt(R_ERASE); HEAP[loc(t)] = ls; continue; } }
        if (tag(a) == T_SUP) { receipt(R_OP2_SUP); Loc name = loc(whnf(HEAP[loc(a)])); Term b = HEAP[loc(t)+1];
          return node3(T_SUP, 0, HEAP[loc(a)],
            node2(T_OP2, ext(t), HEAP[loc(a)+1], fce3(0, name, b, 0)),
            node2(T_OP2, ext(t), HEAP[loc(a)+2], fce3(1, name, b, 0))); }
        Term b = whnf(HEAP[loc(t) + 1]);
        if (tag(b) == T_SUP) { Term ls = live_side(b); if (ls) { receipt(R_ERASE); HEAP[loc(t)] = a; HEAP[loc(t)+1] = ls; continue; } }
        if (tag(b) == T_SUP) { receipt(R_OP2_SUP); Loc name = loc(whnf(HEAP[loc(b)]));
          return node3(T_SUP, 0, HEAP[loc(b)],
            node2(T_OP2, ext(t), fce3(0, name, a, 0), HEAP[loc(b)+1]),
            node2(T_OP2, ext(t), fce3(1, name, a, 0), HEAP[loc(b)+2])); }
        if (tag(a) == T_NUM && tag(b) == T_NUM && ext(a) == ext(b) && ext(a) != N_F64 && is_cmp(ext(t))) return op2_retained(ext(t), ext(a), HEAP[loc(a)], HEAP[loc(b)]);
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
/* the normal form: dead sides pruned, into every field */
Term nf(Term t, int depth) {
  if (depth <= 0) return t;
  t = whnf(t); if (tag(t) == T_SUP) t = prune(t);
  switch (tag(t)) {
    case T_CTR: for (uint32_t i = 0; i < ctr_arity(t); i++) HEAP[loc(t)+i] = nf(HEAP[loc(t)+i], depth-1);
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
  if (!*slot) { pthread_mutex_lock(&KMUT); if (!*slot) { if (NWORLD >= WCAP) { WCAP = WCAP ? WCAP * 2 : 1024; WPARENT = realloc(WPARENT, WCAP * sizeof *WPARENT); WPARENT[0] = 0; }
    WPARENT[NWORLD] = WORLD; *slot = (Term)NWORLD++; } pthread_mutex_unlock(&KMUT); }
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
    case T_VAR: printf("x%u", ext(t)); break;
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
    case T_CASE: { uint32_t code = loc(HEAP[loc(t)+1]); Term fr = HEAP[loc(t)+2]; printf("case%u(", code); print_rec(HEAP[loc(t)], depth-1);   /* a stuck match: its scrutinee and what its code reads */
                   for (uint32_t lvl = 0; lvl < frame_depth(fr); lvl++) if (code_uses(code, lvl)) { bool dim; Term v = frame_lookup(fr, lvl, &dim); if (dim) continue; v = whnf(v); if (tag(v) == T_LAM || tag(v) == T_PLM) continue; printf(";"); print_rec(v, depth-1); }
                   printf(")"); break; }
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
void print_term(Term t, int depth) { force_fields(t, depth); par_drain(); print_rec(t, depth); }

/* §6: the census of receipts. Every interaction left one receipt in the trace; the census is its fold
   by rule (AdiBija: every analyzer is a fold over the trace). Definitional unfolding and the face map's
   sharing are shown apart, as the receipts name them. */
const char *RULE_NAME[R_COUNT] = { "", "beta", "appSup", "app-plm", "dupSupEqual", "dupSupDifferent", "dupLamUsed", "dupLamErased", "dupNode",
    "fce-share", "case", "appMatSup", "op2", "op2-sup", "erase", "trp", "hcm", "hcon", "helim", "helim-sup", "helim-hcm", "op1", "pout", "declare", "recall" };
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
/* the leaves of a superposition tree; a value that is not superposed is one leaf.  A superposition's
   right side that is itself a superposition continues a chain of alternatives; the chain is read whole
   first (no alternative is entered), then entered by bisection — the middle alternative first, then the
   middle of each half — so that what one alternative's comparisons kept decides its neighbours. */
static Term *CL_OUT; static int CL_N, CL_MAX; static uint64_t *CL_KEY; static int CL_DEPTH; static int CL_PATH[64];
/* lift without pruning: a dead side is dropped where it is met (an erase receipt, as prune leaves), so no
   alternative is entered before its turn */
static Term cl_lift(Term t, int depth) {
  if (depth <= 0) return t;
  t = whnf(t);
  switch (tag(t)) {
    case T_SUP: return t;
    case T_CTR: {
      for (uint32_t i = 0; i < ctr_arity(t); i++) {
        Term f = cl_lift(HEAP[loc(t)+i], depth-1); HEAP[loc(t)+i] = f;
        if (tag(f) == T_ERA) return f;
        if (tag(f) == T_SUP) { Term nm = whnf(HEAP[loc(f)]); if (tag(nm) != T_IVAR) continue;
          Loc name = loc(nm);
          return node3(T_SUP, 0, nm, fce3(0, name, t, 0), fce3(1, name, t, 0)); }
      }
      return t; }
    case T_APP: { Term x = cl_lift(HEAP[loc(t)+1], depth-1); HEAP[loc(t)+1] = x;
      if (tag(x) == T_SUP) { Term nm = whnf(HEAP[loc(x)]); if (tag(nm) == T_IVAR) return node3(T_SUP, 0, nm, fce3(0, loc(nm), t, 0), fce3(1, loc(nm), t, 0)); }
      return t; }
    default: return t;
  }
}
static void cl_collect(Term t);
static void cl_bisect(Term *alts, int lo, int hi) {
  if (lo > hi) return; int m = (lo + hi) / 2;
  if (CL_DEPTH < 64) CL_PATH[CL_DEPTH] = m;
  CL_DEPTH++; cl_collect(alts[m]); CL_DEPTH--;
  cl_bisect(alts, lo, m - 1); cl_bisect(alts, m + 1, hi);
}
static void cl_collect(Term t) {
  Term v = cl_lift(t, 256);
  if (tag(v) == T_ERA) { receipt(R_ERASE); return; }
  if (tag(v) != T_SUP) {
    if (CL_N < CL_MAX) { CL_OUT[CL_N] = v;                      /* the leaf's place in the tree, for the collapse order */
      uint64_t *k = CL_KEY + (size_t)CL_N * 8; for (int i = 0; i < 8; i++) k[i] = 0;
      for (int i = 0; i < CL_DEPTH && i < 64; i++) k[i / 4] |= (uint64_t)((CL_PATH[i] + 1) & 0xFFFF) << (48 - 16 * (i % 4));
      CL_N++; }
    return; }
  Term *alts = malloc((1 << 12) * sizeof(Term)); int k = 0;
  for (;;) { alts[k++] = HEAP[loc(v)+1]; Term r = cl_lift(HEAP[loc(v)+2], 256);
    if (tag(r) == T_SUP && k < (1 << 12) - 1) { v = r; continue; }
    alts[k++] = r; break; }
  cl_bisect(alts, 0, k - 1); free(alts);
}
static int cl_cmp(const void *x, const void *y) {
  const uint64_t *a = CL_KEY + (size_t)*(const int *)x * 8, *b = CL_KEY + (size_t)*(const int *)y * 8;
  for (int i = 0; i < 8; i++) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
  return 0;
}
int collapse_leaves(Term t, Term *out, int max) {
  Term *so = CL_OUT; int sn = CL_N, sm = CL_MAX; uint64_t *sk = CL_KEY; int sd = CL_DEPTH; int path[64]; memcpy(path, CL_PATH, sizeof path);
  CL_OUT = out; CL_N = 0; CL_MAX = max; CL_KEY = calloc((size_t)max * 8, sizeof(uint64_t)); CL_DEPTH = 0;
  cl_collect(t);
  int n = CL_N; int *ix = malloc(n * sizeof(int)); Term *tmp = malloc(n * sizeof(Term));
  for (int i = 0; i < n; i++) ix[i] = i;
  qsort(ix, n, sizeof(int), cl_cmp);                             /* the leaves in their left-to-right place, whatever order entered them */
  for (int i = 0; i < n; i++) tmp[i] = out[ix[i]];
  memcpy(out, tmp, n * sizeof(Term)); free(tmp); free(ix); free(CL_KEY);
  CL_OUT = so; CL_N = sn; CL_MAX = sm; CL_KEY = sk; CL_DEPTH = sd; memcpy(CL_PATH, path, sizeof path); return n;
}
/* a value as its printed text, for comparison by identity of normal forms */
char *term_string(Term t, int depth) {
  char *buf = 0; size_t n = 0; FILE *m = open_memstream(&buf, &n); FILE *old = stdout;
  stdout = m; print_rec(t, depth); fflush(m); stdout = old; fclose(m);
  return buf;
}
void collapse_print(Term t) {
  force_fields(t, 256);
  Term q[1 << 16]; uint32_t head = 0, tail = 0; q[tail++] = t;
  while (head < tail) {
    Term v = lift(q[head++], 256);
    if (tag(v) == T_SUP) { if (tail + 2 < (1u << 16)) { q[tail++] = HEAP[loc(v)+1]; q[tail++] = HEAP[loc(v)+2]; } continue; }
    if (tag(v) == T_ERA) continue;
    pb(v, 256); printf("\n");
  }
}

Term run_def(uint32_t id) { Term r = whnf(mk(T_REF, 0, id)); par_drain(); return r; }

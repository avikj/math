/* hyper.c: Hyperactive.
 *
 * The net that Bend2's --to-hvm4-full emits into, and the one thing a declaration adds: a declaration with no
 * body is a coordinate of its type.  Everything cubical (coe, hcomp, ua, Glue), the fibre law (descend/ascend),
 * the whole process (react), and every domain (order, lists, formulas) are programs in the book.
 *
 *   TERM  = VAR | LAM | APP | SUP L | DP0 L | DP1 L | ERA | CTR c | MAT T | REF d | NUM | OP2 | CRD | TYP T | EQL
 *
 *   whnf, one interaction per rule:
 *     DUP meets LAM             dupLam            both copies are lambdas; the binder becomes &L{x0,x1}
 *     DUP meets SUP, same L     dupSupEqual       route: the two sides are the two copies (one bit)
 *     DUP meets SUP, other L    dupSupDifferent   cross: both copies superposed at the other label
 *     DUP meets CTR/MAT/…       dupNode           both copies are the node, its parts duplicated
 *     APP of LAM                beta
 *     APP of SUP                appSup
 *     APP of MAT to CTR         match
 *     APP of MAT to SUP         appMatSup
 *   the coordinate (a slot and its type; its copies are it):
 *     asked by a match, an application, or the leaves     expand: by its type, in place
 *       T  its constructors superposed, fields fresh coordinates   Σ A F  (a, b : F a)
 *       Π A F  λx. the coordinate of F x                           x ≡ y  unification of x and y
 *     x ≡ y                     unify / bind      a coordinate is bound on the choice labels it was reached
 *                                                 through; two constructors, field by field; a SUP distributes
 *   collapse: the leaves of the result's superposition, the empty ones (&{}) gone.
 *
 * Surface: `type T { C, D(f: U, …) }`;  `@d = term`;  `@d : type` (no body: a coordinate of it);
 *   λx t  |  λ{#C: t; #D: t}  |  (f a …)  |  (op a b)  |  &L{a, b}  |  &{}  |  #C{a, …}  |  @d  |  ?T  |  n
 *   |  !x = t; u  (let)  |  T  |  Σ x: A. B  |  Π x: A. B  |  (≡ a b)  |  (× A B).
 *   A variable used k > 1 times is duplicated k − 1 times, each at a fresh label.
 *
 * usage: hyper FILE…   (prints each leaf of @main, then the receipt) */
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

typedef uint64_t Term; typedef uint32_t u32; typedef uint64_t u64;
enum { VAR = 1, LAM, APP, SUP, DP0, DP1, ERA, CTR, MAT, REF, NUM, OP2, CRD, TYP, EQL };
#define SUBB (1ull << 63)
static inline Term mk(u32 tag, u32 lab, u32 loc) { return (Term)tag << 56 | (Term)(lab & 0xFFFFFF) << 32 | loc; }
static inline u32 TAG(Term t) { return (u32)(t >> 56) & 0x7F; }
static inline u32 LAB(Term t) { return (u32)(t >> 32) & 0xFFFFFF; }
static inline u32 LOC(Term t) { return (u32)t; }

/* ---- heap ------------------------------------------------------------------------------------------------ */
static u64 *H; static u64 HLEN, HCAP;
static u32 alloc(u32 n) {
  if (HLEN + n > HCAP) { HCAP = HCAP ? HCAP * 2 : 1 << 20; while (HLEN + n > HCAP) HCAP *= 2; H = realloc(H, HCAP * 8); }
  u32 l = (u32)HLEN; HLEN += n; memset(H + l, 0, n * 8); return l;
}
/* A label is a copy label (two consumers of one value: a variable's duplications) or a choice label (the two
   sides of a superposition: the file's own, and a coordinate's constructors).  A binding made in a branch is
   made on the choice labels it was reached through; a copy label is one value, bound on both copies. */
static u32 LABELS = 1u << 16, CHOICES = 1u << 23;
static u32 fresh_label(void) { return LABELS++; }
static u32 fresh_choice(void) { return CHOICES++ & 0xFFFFFF; }
static int is_choice(u32 L) { return L < (1u << 16) || L >= (1u << 23); }

/* ---- the receipt ------------------------------------------------------------------------------------------ */
enum { R_BETA, R_APPSUP, R_APPERA, R_MATCH, R_APPMATSUP, R_DUPLAM, R_DUPSUPEQ, R_DUPSUPDIFF, R_DUPNODE,
       R_DUPATOM, R_OP, R_OPSUP, R_EXPAND, R_REF, R_UNIFY, R_BIND, R_N };
static const char *RNAME[R_N] = { "beta", "appSup", "appEra", "match", "appMatSup", "dupLam", "dupSupEqual",
  "dupSupDifferent", "dupNode", "dupAtom", "op", "opSup", "expand", "ref", "unify", "bind" };
static u64 RC[R_N], ITRS;
static inline void itr(int r) { RC[r]++; ITRS++; }

/* ---- the book: types, constructors, definitions ------------------------------------------------------------ */
typedef struct { char *name; int type, idx, arity; int ftype[16]; } Ctor;
typedef struct { char *name; int nctor; int ctor[32]; } Type;
static Ctor CT[4096]; static int NCT; static u64 DUPCT[4096]; static Type TY[512]; static int NTY;
static int find_type(const char *s) { for (int i = 0; i < NTY; i++) if (!strcmp(TY[i].name, s)) return i; return -1; }
static int find_ctor(const char *s) { for (int i = 0; i < NCT; i++) if (!strcmp(CT[i].name, s)) return i; return -1; }

enum { K_VAR, K_LAM, K_APP, K_SUP, K_ERA, K_CTR, K_MAT, K_REF, K_NUM, K_OP2, K_CRD, K_TYP };
typedef struct Ast { int k; u32 x; struct Ast *a, *b, **kids; int n; } Ast;
static Ast *node(int k) { Ast *t = calloc(1, sizeof *t); t->k = k; return t; }
typedef struct { char *name; Ast *body; } Def;
static Def DF[4096]; static int NDF; static u64 REFS[4096];
static int def_id(const char *s) {
  for (int i = 0; i < NDF; i++) if (!strcmp(DF[i].name, s)) return i;
  DF[NDF].name = strdup(s); DF[NDF].body = 0; return NDF++;
}
static int *BUSES; static int NB, CB;                              /* each binder's number of uses */
static int new_binder(void) { if (NB == CB) { CB = CB ? CB * 2 : 1024; BUSES = realloc(BUSES, CB * sizeof *BUSES); } BUSES[NB] = 0; return NB++; }

/* ---- instantiating a definition: its variables' duplications at fresh labels --------------------------------- */
static Term **USE; static int *NEXTUSE; static int UCAP;
static Term dup_of(Term v, u32 L, Term *r1) { u32 e = alloc(2); H[e] = v; *r1 = mk(DP1, L, e); return mk(DP0, L, e); }
static void bind(int b, Term v) {
  int k = BUSES[b]; NEXTUSE[b] = 0;
  USE[b] = realloc(USE[b], (k > 0 ? k : 1) * sizeof(Term));
  if (k <= 1) { USE[b][0] = v; return; }
  Term cur = v;
  for (int j = 0; j < k - 1; j++) { Term r1; USE[b][j] = dup_of(cur, fresh_label(), &r1); cur = r1; }
  USE[b][k - 1] = cur;
}
static Term inst(Ast *t) {
  switch (t->k) {
    case K_VAR: return USE[t->x][NEXTUSE[t->x]++];
    case K_LAM: { u32 l = alloc(1); bind((int)t->x, mk(VAR, 0, l)); Term b = inst(t->a); H[l] = b; return mk(LAM, 0, l); }
    case K_APP: { u32 l = alloc(2); Term f = inst(t->a), a = inst(t->b); H[l] = f; H[l + 1] = a; return mk(APP, 0, l); }
    case K_SUP: { u32 l = alloc(2); Term a = inst(t->a), b = inst(t->b); H[l] = a; H[l + 1] = b; return mk(SUP, t->x, l); }
    case K_ERA: return mk(ERA, 0, 0);
    case K_CTR: { int ar = CT[t->x].arity; u32 l = alloc(ar ? ar : 1); for (int i = 0; i < ar; i++) { Term f = inst(t->kids[i]); H[l + i] = f; } return mk(CTR, t->x, l); }
    case K_MAT: { int n = TY[t->x].nctor; u32 l = alloc(n); for (int i = 0; i < n; i++) { Term f = t->kids[i] ? inst(t->kids[i]) : mk(ERA, 0, 0); H[l + i] = f; } return mk(MAT, t->x, l); }
    case K_REF: return mk(REF, t->x, 0);
    case K_NUM: return mk(NUM, 0, t->x);
    case K_OP2: { u32 l = alloc(2); Term a = inst(t->a), b = inst(t->b); H[l] = a; H[l + 1] = b; return mk(OP2, t->x, l); }
    case K_CRD: { Term ty = inst(t->a); u32 l = alloc(2); H[l + 1] = ty; return mk(CRD, 0, l); }   /* [slot, type] */
    case K_TYP: return mk(TYP, t->x, 0);
  }
  return mk(ERA, 0, 0);
}

/* ---- the coordinate --------------------------------------------------------------------------------------------
   A declaration with no body is a coordinate: a slot and its type.  Its type is a term: a data type T, Σ A F,
   Π A F, or x ≡ y.  Asked for its value (a match, an application, the leaves), the slot is written in place:
     T      the superposition of T's constructors, each field a fresh coordinate of its declared type
     Σ A F  the pair (a, b) with a : A and b : F a
     Π A F  λx. the coordinate of F x
     x ≡ y  the identity decided: unification of x and y (below)
   and a superposed type is the superposition of its sides' coordinates; the empty type has no point.        */
static int C_PAIR, C_REFL, C_SIG, C_PI, C_EQL, T_EQ;
static Term whnf(Term t);
static Term coord(Term type) { u32 l = alloc(2); H[l + 1] = type; return mk(CRD, 0, l); }
static Term ctor_with_fresh_fields(int c) {
  int ar = CT[c].arity; u32 l = alloc(ar ? ar : 1);
  for (int i = 0; i < ar; i++) H[l + i] = coord(CT[c].ftype[i] >= 0 ? mk(TYP, (u32)CT[c].ftype[i], 0) : 0);
  return mk(CTR, (u32)c, l);
}
static Term pair(Term a, Term b) { u32 l = alloc(2); H[l] = a; H[l + 1] = b; return mk(CTR, (u32)C_PAIR, l); }
static Term app(Term f, Term a) { u32 l = alloc(2); H[l] = f; H[l + 1] = a; return mk(APP, 0, l); }
static Term eql(Term x, Term y) { u32 l = alloc(2); H[l] = x; H[l + 1] = y; return mk(EQL, 0, l); }
static int expand(Term crd) {                                     /* 1 when the slot was written */
  u32 c = LOC(crd); Term ty = H[c + 1] ? whnf(H[c + 1]) : 0; H[c + 1] = ty; Term v;
  switch (TAG(ty)) {
    case TYP: {
      Type *T = &TY[LAB(ty)];
      if (T->nctor == 0) { v = mk(ERA, 0, 0); break; }
      v = ctor_with_fresh_fields(T->ctor[T->nctor - 1]);
      for (int i = T->nctor - 2; i >= 0; i--) { Term k = ctor_with_fresh_fields(T->ctor[i]); u32 l = alloc(2); H[l] = k; H[l + 1] = v; v = mk(SUP, fresh_choice(), l); }
      break;
    }
    case CTR:
      if ((int)LAB(ty) == C_SIG) { Term a1, a0 = dup_of(coord(H[LOC(ty)]), fresh_label(), &a1); v = pair(a0, coord(app(H[LOC(ty) + 1], a1))); break; }
      if ((int)LAB(ty) == C_PI) { u32 l = alloc(1); H[l] = coord(app(H[LOC(ty) + 1], mk(VAR, 0, l))); v = mk(LAM, 0, l); break; }
      if ((int)LAB(ty) == C_EQL) { v = eql(H[LOC(ty)], H[LOC(ty) + 1]); break; }
      return 0;
    case SUP: {
      Term t1, t0 = H[LOC(ty)]; t1 = H[LOC(ty) + 1];
      u32 l = alloc(2); H[l] = coord(t0); H[l + 1] = coord(t1); v = mk(SUP, LAB(ty), l); break;
    }
    case ERA: v = ty; break;
    default: return 0;                                             /* a type not yet known: it waits */
  }
  H[c] = v | SUBB; itr(R_EXPAND); return 1;
}
/* the coordinate a value is a copy of, through its chain of duplications; 0 if it is not one */
static Term root_of(Term v) {
  while (TAG(v) == DP0 || TAG(v) == DP1) { u32 e = LOC(v); if (H[e + (TAG(v) == DP1)] & SUBB) return 0; v = H[e] = whnf(H[e]); }
  return TAG(v) == CRD && !(H[LOC(v)] & SUBB) ? v : 0;
}

/* ---- reduction ------------------------------------------------------------------------------------------------- */
static Term node_copy(Term v, u32 L, Term *r1) {                  /* a node's two copies, its parts duplicated */
  u32 tg = TAG(v), n = 0;
  if (tg == CTR) n = (u32)CT[LAB(v)].arity; else if (tg == MAT) n = (u32)TY[LAB(v)].nctor; else if (tg == APP || tg == OP2) n = 2;
  u32 a = alloc(n ? n : 1), b = alloc(n ? n : 1);
  for (u32 i = 0; i < n; i++) { Term x1, x0 = dup_of(H[LOC(v) + i], L, &x1); H[a + i] = x0; H[b + i] = x1; }
  *r1 = mk(tg, LAB(v), b); return mk(tg, LAB(v), a);
}
static Term apply_fields(Term f, Term ctr) {
  int ar = CT[LAB(ctr)].arity;
  for (int i = 0; i < ar; i++) { u32 l = alloc(2); H[l] = f; H[l + 1] = H[LOC(ctr) + i]; f = mk(APP, 0, l); }
  return f;
}
static u32 opcalc(u32 op, u32 a, u32 b) {
  switch (op) {
    case '+': return a + b; case '-': return a - b; case '*': return a * b; case '/': return b ? a / b : 0; case '%': return b ? a % b : 0;
    case '=': return a == b; case '!': return a != b; case '<': return a < b; case '>': return a > b; case 'l': return a <= b; case 'g': return a >= b;
  }
  return 0;
}

/* ---- unification: x ≡ y decided -------------------------------------------------------------------------------
   Refl when x and y are made one by binding coordinates, &{} when two constructors or numbers differ, a
   superposition when a side is superposed (the other side copied at its label).  Two constructors: the identity
   of each field, in order.  A coordinate reached through copies is bound in the branch it was reached in: its
   slot becomes, for each choice label on the way, that label's superposition with the value on the side taken
   and a fresh coordinate of the same type on the other. */
static Term refl(void) { return mk(CTR, (u32)C_REFL, alloc(1)); }
static int mentions(Term t, u32 c, int d) {
  for (; d > 0; d--) {
    u32 tg = TAG(t);
    if ((tg == VAR || tg == CRD) && (H[LOC(t)] & SUBB)) { t = H[LOC(t)] & ~SUBB; continue; }
    if (tg == DP0 || tg == DP1) { u64 x = H[LOC(t) + (tg == DP1)]; t = x & SUBB ? x & ~SUBB : H[LOC(t)]; continue; }
    if (tg == CRD) return LOC(t) == c;
    if (tg == CTR) { for (int i = 0; i < CT[LAB(t)].arity; i++) if (mentions(H[LOC(t) + i], c, d - 1)) return 1; return 0; }
    if (tg == SUP) return mentions(H[LOC(t)], c, d - 1) || mentions(H[LOC(t) + 1], c, d - 1);
    return 0;
  }
  return 0;
}
static Term bind_at(Term x, Term c, Term v) {
  if (mentions(v, LOC(c), 4096)) return mk(ERA, 0, 0);
  Term w = v, ty = H[LOC(c) + 1];
  for (Term p = x; TAG(p) == DP0 || TAG(p) == DP1; p = H[LOC(p)]) {        /* the chain root_of read */
    u32 L = LAB(p); int side = TAG(p) == DP1;
    if (!is_choice(L)) continue;
    Term t1, t0 = dup_of(ty, fresh_label(), &t1); ty = t1;
    u32 l = alloc(2); H[l + side] = w; H[l + !side] = coord(t0); w = mk(SUP, L, l);
  }
  H[LOC(c) + 1] = ty; H[LOC(c)] = w | SUBB; itr(R_BIND);
  return refl();
}
static Term unify(Term t) {
  u32 l = LOC(t);
  for (int k = 0; k < 2; k++) {
    Term x = whnf(H[l + k]); H[l + k] = x;
    if (TAG(x) == ERA) return x;
    if (TAG(x) == SUP) {
      itr(R_UNIFY); Term o1, o0 = dup_of(H[l + !k], LAB(x), &o1);
      Term a = k ? eql(o0, H[LOC(x)]) : eql(H[LOC(x)], o0), b = k ? eql(o1, H[LOC(x) + 1]) : eql(H[LOC(x) + 1], o1);
      u32 s = alloc(2); H[s] = a; H[s + 1] = b; return mk(SUP, LAB(x), s);
    }
  }
  Term x = H[l], y = H[l + 1], rx = root_of(x), ry = root_of(y);
  if (rx && ry && LOC(rx) == LOC(ry)) { itr(R_UNIFY); return refl(); }
  if (rx) return bind_at(x, rx, y);
  if (ry) return bind_at(y, ry, x);
  if (TAG(x) == CTR && TAG(y) == CTR) {
    itr(R_UNIFY);
    if (LAB(x) != LAB(y)) return mk(ERA, 0, 0);
    int ar = CT[LAB(x)].arity; if (!ar) return refl();
    Term acc = eql(H[LOC(x) + ar - 1], H[LOC(y) + ar - 1]);
    for (int i = ar - 2; i >= 0; i--) { u32 m = alloc(1); H[m] = acc; acc = app(mk(MAT, (u32)T_EQ, m), eql(H[LOC(x) + i], H[LOC(y) + i])); }
    return acc;
  }
  if (TAG(x) == NUM && TAG(y) == NUM) { itr(R_UNIFY); return LOC(x) == LOC(y) ? refl() : mk(ERA, 0, 0); }
  if (TAG(x) == TYP && TAG(y) == TYP) { itr(R_UNIFY); return LAB(x) == LAB(y) ? refl() : mk(ERA, 0, 0); }
  return t;                                                        /* a side not yet known: it waits */
}

static Term whnf(Term t) {
  for (;;) {
    switch (TAG(t)) {
      case VAR: { u64 s = H[LOC(t)]; if (s & SUBB) { t = s & ~SUBB; continue; } return t; }
      case CRD: { u64 s = H[LOC(t)]; if (s & SUBB) { t = s & ~SUBB; continue; } return t; }
      case REF: { itr(R_REF); REFS[LAB(t)]++; t = inst(DF[LAB(t)].body); continue; }
      case DP0: case DP1: {
        u32 e = LOC(t), L = LAB(t); int side = TAG(t) == DP1;
        u64 s = H[e + side]; if (s & SUBB) { t = s & ~SUBB; continue; }
        Term v = whnf(H[e]), r0, r1; H[e] = v;
        switch (TAG(v)) {
          case CRD: return t;                                        /* a copy of a coordinate is a coordinate */
          case LAM: {
            itr(R_DUPLAM);
            u32 m = LOC(v), l0 = alloc(1), l1 = alloc(1); Term body = H[m], b1;
            u32 sl = alloc(2); H[sl] = mk(VAR, 0, l0); H[sl + 1] = mk(VAR, 0, l1);
            H[m] = mk(SUP, L, sl) | SUBB;
            { Term b0 = dup_of(body, L, &b1); H[l0] = b0; H[l1] = b1; }
            r0 = mk(LAM, 0, l0); r1 = mk(LAM, 0, l1); break;
          }
          case SUP: {
            if (LAB(v) == L) { itr(R_DUPSUPEQ); r0 = H[LOC(v)]; r1 = H[LOC(v) + 1]; break; }
            itr(R_DUPSUPDIFF);
            Term a1, b1, a0 = dup_of(H[LOC(v)], L, &a1), b0 = dup_of(H[LOC(v) + 1], L, &b1);
            u32 s0 = alloc(2), s1 = alloc(2); H[s0] = a0; H[s0 + 1] = b0; H[s1] = a1; H[s1 + 1] = b1;
            r0 = mk(SUP, LAB(v), s0); r1 = mk(SUP, LAB(v), s1); break;
          }
          case CTR: case MAT: itr(R_DUPNODE); if (TAG(v) == CTR) DUPCT[LAB(v)]++; r0 = node_copy(v, L, &r1); break;
          case NUM: case ERA: case TYP: itr(R_DUPATOM); r0 = r1 = v; break;
          default: return t;                                        /* a duplication of something stuck */
        }
        H[e] = r0 | SUBB; H[e + 1] = r1 | SUBB;
        t = side ? r1 : r0; continue;
      }
      case APP: {
        u32 l = LOC(t); Term f = whnf(H[l]), a = H[l + 1];
        switch (TAG(f)) {
          case LAM: { itr(R_BETA); u32 m = LOC(f); Term body = H[m]; H[m] = a | SUBB; t = body; continue; }
          case SUP: {
            itr(R_APPSUP); Term a1, a0 = dup_of(a, LAB(f), &a1);
            Term f0 = H[LOC(f)], f1 = H[LOC(f) + 1], x0 = app(f0, a0), x1 = app(f1, a1); u32 s = alloc(2); H[s] = x0; H[s + 1] = x1; return mk(SUP, LAB(f), s);
          }
          case ERA: itr(R_APPERA); return f;
          case MAT: {
            H[l] = f; Term v = whnf(a);
            switch (TAG(v)) {
              case CTR: { itr(R_MATCH); t = apply_fields(H[LOC(f) + CT[LAB(v)].idx], v); continue; }
              case SUP: {
                itr(R_APPMATSUP); Term m1, m0 = dup_of(f, LAB(v), &m1);
                Term v0 = H[LOC(v)], v1 = H[LOC(v) + 1], x0 = app(m0, v0), x1 = app(m1, v1); u32 s = alloc(2); H[s] = x0; H[s + 1] = x1; return mk(SUP, LAB(v), s);
              }
              case ERA: itr(R_APPERA); return v;
              default: { Term r = root_of(v); H[l] = f; H[l + 1] = v; if (r && expand(r)) continue; return t; }
            }
          }
          default: { Term r = root_of(f); H[l] = f; if (r && expand(r)) continue; return t; }
        }
      }
      case EQL: { Term r = unify(t); if (r == t) return t; t = r; continue; }
      case OP2: {
        u32 l = LOC(t); Term a = whnf(H[l]), b = whnf(H[l + 1]);
        if (TAG(a) == ERA || TAG(b) == ERA) return mk(ERA, 0, 0);
        if (TAG(a) == SUP || TAG(b) == SUP) {
          itr(R_OPSUP); int onA = TAG(a) == SUP; Term s = onA ? a : b, o = onA ? b : a, o1, o0 = dup_of(o, LAB(s), &o1);
          u32 x = alloc(2), y = alloc(2), z = alloc(2);
          if (onA) { H[x] = H[LOC(s)]; H[x + 1] = o0; H[y] = H[LOC(s) + 1]; H[y + 1] = o1; }
          else { H[x] = o0; H[x + 1] = H[LOC(s)]; H[y] = o1; H[y + 1] = H[LOC(s) + 1]; }
          H[z] = mk(OP2, LAB(t), x); H[z + 1] = mk(OP2, LAB(t), y); return mk(SUP, LAB(s), z);
        }
        if (TAG(a) == NUM && TAG(b) == NUM) { itr(R_OP); return mk(NUM, 0, opcalc(LAB(t), LOC(a), LOC(b))); }
        H[l] = a; H[l + 1] = b; return t;
      }
      default: return t;
    }
  }
}

/* ---- collapse: a superposition's leaves, the empty ones gone ----------------------------------------------------- */
static Term lift(Term t);
static int ORDER;                                                 /* HYPER_ORDER=1: another schedule */
static Term lift_ctr(Term v) {                                    /* a field's superposition taken to the node's top */
  int ar = CT[LAB(v)].arity;
  for (int k = 0; k < ar; k++) {
    int i = ORDER ? ar - 1 - k : k;                               /* the order fields are demanded: a schedule */
    Term f = lift(H[LOC(v) + i]); H[LOC(v) + i] = f;
    if (TAG(f) == ERA) return f;
    if (TAG(f) == SUP) {
      u32 L = LAB(f), a = alloc(ar), b = alloc(ar);
      for (int j = 0; j < ar; j++) {
        if (j == i) { H[a + j] = H[LOC(f)]; H[b + j] = H[LOC(f) + 1]; continue; }
        Term x1, x0 = dup_of(H[LOC(v) + j], L, &x1); H[a + j] = x0; H[b + j] = x1;
      }
      u32 s = alloc(2); H[s] = mk(CTR, LAB(v), a); H[s + 1] = mk(CTR, LAB(v), b); return mk(SUP, L, s);
    }
  }
  return v;
}
/* a point asked for its value: an identity is decided, a Σ is a pair, a type of one constructor is it, the empty
   type has none; a coordinate of a data type of several constructors is left open (a match splits it) */
static int asked(Term r) {
  Term ty = H[LOC(r) + 1] ? whnf(H[LOC(r) + 1]) : 0; H[LOC(r) + 1] = ty;
  switch (TAG(ty)) {
    case TYP: return TY[LAB(ty)].nctor <= 1;
    case CTR: return (int)LAB(ty) == C_SIG || (int)LAB(ty) == C_EQL;
    case SUP: case ERA: return 1;
  }
  return 0;
}
static Term lift(Term t) {
  for (;;) { t = whnf(t); Term r = root_of(t); if (!(r && asked(r) && expand(r))) break; }
  return TAG(t) == CTR ? lift_ctr(t) : t;
}
static Term *LEAVES; static u32 NLEAF, CLEAF;
static void collapse(Term t) {
  for (u64 n = ~0ull; n != RC[R_EXPAND] + RC[R_BIND] && TAG(t) != SUP && TAG(t) != ERA; ) { n = RC[R_EXPAND] + RC[R_BIND]; t = lift(t); }
  if (TAG(t) == ERA) return;
  if (TAG(t) == SUP) { Term x = H[LOC(t)], y = H[LOC(t) + 1]; if (ORDER) { collapse(y); collapse(x); } else { collapse(x); collapse(y); } return; }
  if (NLEAF == CLEAF) { CLEAF = CLEAF ? CLEAF * 2 : 64; LEAVES = realloc(LEAVES, CLEAF * sizeof *LEAVES); }
  LEAVES[NLEAF++] = t;
}
static void show(FILE *o, Term t, int d) {
  t = whnf(t);
  if (d > 100000) { fputs("…", o); return; }
  switch (TAG(t)) {
    case NUM: fprintf(o, "%u", LOC(t)); return;
    case ERA: fputs("&{}", o); return;
    case LAM: fputs("λ", o); return;
    case SUP: fprintf(o, "&%u{", LAB(t)); show(o, H[LOC(t)], d + 1); fputs(",", o); show(o, H[LOC(t) + 1], d + 1); fputs("}", o); return;
    case CTR: {
      Ctor *c = &CT[LAB(t)]; fprintf(o, "#%s", c->name);
      if (c->arity) { fputs("{", o); for (int i = 0; i < c->arity; i++) { if (i) fputs(",", o); show(o, H[LOC(t) + i], d + 1); } fputs("}", o); }
      return;
    }
    case TYP: fputs(TY[LAB(t)].name, o); return;
    case CRD: case DP0: case DP1: {
      Term r = root_of(t); if (!r) { fputs("<stuck>", o); return; }
      Term ty = H[LOC(r) + 1]; fputs("?", o); if (TAG(ty) == TYP) fputs(TY[LAB(ty)].name, o); return;
    }
    case EQL: fputs("<≡ waiting>", o); return;
    default: fputs("<stuck>", o); return;
  }
}

/* ---- reading ------------------------------------------------------------------------------------------------------ */
static const char *S; static size_t P; static int LINE;
static void die(const char *m) { fprintf(stderr, "hyper: %s at line %d\n", m, LINE); exit(2); }
static void ws(void) {
  for (;;) {
    while (isspace((unsigned char)S[P])) { if (S[P] == '\n') LINE++; P++; }
    if (S[P] == '/' && S[P + 1] == '/') { while (S[P] && S[P] != '\n') P++; continue; }
    return;
  }
}
static int peek(const char *s) { ws(); return !strncmp(S + P, s, strlen(s)); }
static int eat(const char *s) { if (peek(s)) { P += strlen(s); return 1; } return 0; }
static void need(const char *s) { if (!eat(s)) { char m[64]; snprintf(m, sizeof m, "expected '%s'", s); die(m); } }
static char *name(void) {
  ws(); size_t s = P; while (isalnum((unsigned char)S[P]) || S[P] == '_' || S[P] == '\'') P++;
  if (s == P) die("expected a name");
  char *w = malloc(P - s + 1); memcpy(w, S + s, P - s); w[P - s] = 0; return w;
}
typedef struct { char *name; int b; } Scope;
static Scope SC[4096]; static int NSC;
static Ast *term(void);
static Ast *lam_after_binder(void) {
  char *x = name(); int b = new_binder();
  SC[NSC++] = (Scope){ x, b };
  Ast *body = term(); NSC--;
  Ast *t = node(K_LAM); t->x = (u32)b; t->a = body; return t;
}
static Ast *term(void) {
  ws();
  if (eat("λ{") || eat("\\{")) {                                   /* a match on the constructors of one type */
    Ast *arms[32] = { 0 }; int T = -1;
    while (!eat("}")) {
      need("#"); char *c = name(); int ci = find_ctor(c); if (ci < 0) die("unknown constructor");
      if (T < 0) T = CT[ci].type; else if (CT[ci].type != T) die("constructors of two types in one match");
      need(":"); arms[CT[ci].idx] = term(); eat(";");
    }
    if (T < 0) die("empty match");
    Ast *t = node(K_MAT); t->x = (u32)T; t->n = TY[T].nctor; t->kids = calloc(t->n, sizeof *t->kids);
    for (int i = 0; i < t->n; i++) t->kids[i] = arms[i];
    return t;
  }
  if (eat("λ") || eat("\\")) return lam_after_binder();
  if (eat("&{}")) return node(K_ERA);
  if (eat("&")) {
    u32 L; ws(); if (isdigit((unsigned char)S[P])) L = (u32)strtoul(S + P, 0, 10), P += strspn(S + P, "0123456789"); else { char *n = name(); L = 0; for (char *q = n; *q; q++) L = L * 131 + (unsigned char)*q; L %= 60000; }
    need("{"); Ast *a = term(); eat(","); Ast *b = term(); need("}");
    Ast *t = node(K_SUP); t->x = L; t->a = a; t->b = b; return t;
  }
  if (eat("#")) {
    char *c = name(); int ci = find_ctor(c); if (ci < 0) die("unknown constructor");
    Ast *t = node(K_CTR); t->x = (u32)ci; t->n = CT[ci].arity; t->kids = calloc(t->n ? t->n : 1, sizeof *t->kids);
    if (eat("{")) { for (int i = 0; i < t->n; i++) { t->kids[i] = term(); eat(","); } need("}"); }
    else if (t->n) die("constructor needs its fields");
    return t;
  }
  if (eat("@")) { char *n = name(); Ast *t = node(K_REF); t->x = (u32)def_id(n); return t; }
  if (eat("?")) { char *n = name(); int T = find_type(n); if (T < 0) die("unknown type"); Ast *t = node(K_CRD); t->a = node(K_TYP); t->a->x = (u32)T; return t; }
  if (eat("Σ") || eat("Π")) {                                      /* Σ x: A. B  |  Π x: A. B */
    int sig = S[P - 1] == (char)0xA3; char *x = name(); need(":"); Ast *A = term(); need(".");
    int b = new_binder(); SC[NSC++] = (Scope){ x, b }; Ast *B = term(); NSC--;
    Ast *F = node(K_LAM); F->x = (u32)b; F->a = B;
    Ast *t = node(K_CTR); t->x = (u32)(sig ? C_SIG : C_PI); t->n = 2; t->kids = calloc(2, sizeof *t->kids); t->kids[0] = A; t->kids[1] = F; return t;
  }
  if (eat("!")) {                                                  /* !x = v; body */
    char *x = name(); need("="); Ast *v = term(); need(";");
    int b = new_binder(); SC[NSC++] = (Scope){ x, b }; Ast *body = term(); NSC--;
    Ast *l = node(K_LAM); l->x = (u32)b; l->a = body;
    Ast *t = node(K_APP); t->a = l; t->b = v; return t;
  }
  if (eat("(")) {
    if (eat("≡")) { Ast *t = node(K_CTR); t->x = (u32)C_EQL; t->n = 2; t->kids = calloc(2, sizeof *t->kids); t->kids[0] = term(); t->kids[1] = term(); need(")"); return t; }
    if (eat("×")) {                                                /* A × B: Σ _: A. B */
      Ast *A = term(), *B = term(); need(")"); Ast *F = node(K_LAM); F->x = (u32)new_binder(); F->a = B;
      Ast *t = node(K_CTR); t->x = (u32)C_SIG; t->n = 2; t->kids = calloc(2, sizeof *t->kids); t->kids[0] = A; t->kids[1] = F; return t;
    }
    static const char *ops[] = { "<=", ">=", "==", "!=", "+", "-", "*", "/", "%", "<", ">" };
    static const char opc[] = { 'l', 'g', '=', '!', '+', '-', '*', '/', '%', '<', '>' };
    for (int i = 0; i < 11; i++) if (peek(ops[i]) && isspace((unsigned char)S[P + strlen(ops[i])])) {
      P += strlen(ops[i]); Ast *a = term(), *b = term(); need(")");
      Ast *t = node(K_OP2); t->x = (u32)opc[i]; t->a = a; t->b = b; return t;
    }
    Ast *f = term();
    while (!eat(")")) { Ast *a = term(); Ast *t = node(K_APP); t->a = f; t->b = a; f = t; }
    return f;
  }
  if (isdigit((unsigned char)S[P])) { Ast *t = node(K_NUM); t->x = (u32)strtoul(S + P, 0, 10); P += strspn(S + P, "0123456789"); return t; }
  char *x = name();
  for (int i = NSC - 1; i >= 0; i--) if (!strcmp(SC[i].name, x)) { BUSES[SC[i].b]++; Ast *t = node(K_VAR); t->x = (u32)SC[i].b; return t; }
  { int T = find_type(x); if (T >= 0) { Ast *t = node(K_TYP); t->x = (u32)T; return t; } }
  die("unbound variable"); return 0;
}
static void read_src(const char *src) {
  S = src; P = 0; LINE = 1;
  for (ws(); S[P]; ws()) {
    if (eat("type")) {
      char *n = name(); int T = NTY++; TY[T].name = n; TY[T].nctor = 0; need("{");
      /* constructors first, field types after: a type may mention itself */
      size_t save = P; int sl = LINE;
      while (!eat("}")) {
        char *c = name(); int ci = NCT++; CT[ci].name = c; CT[ci].type = T; CT[ci].idx = TY[T].nctor; CT[ci].arity = 0;
        TY[T].ctor[TY[T].nctor++] = ci;
        if (eat("(")) { while (!eat(")")) { name(); need(":"); name(); CT[ci].arity++; eat(","); } }
        eat(",");
      }
      P = save; LINE = sl;
      for (int k = 0; !eat("}"); k++) {
        int ci = TY[T].ctor[k]; name();
        if (eat("(")) {                                            /* a field of type _ or U32 is never split */
          for (int j = 0; !eat(")"); j++) {
            name(); need(":"); char *ft = name(); CT[ci].ftype[j] = find_type(ft);
            if (CT[ci].ftype[j] < 0 && strcmp(ft, "_") && strcmp(ft, "U32")) die("unknown field type");
            eat(",");
          }
        }
        eat(",");
      }
      continue;
    }
    need("@"); char *n = name(); int d = def_id(n);
    if (eat(":")) {                                                /* no body: a coordinate of its type */
      NSC = 0; Ast *t = node(K_CRD); t->a = term(); DF[d].body = t; eat(";"); continue;
    }
    need("="); NSC = 0; DF[d].body = term(); eat(";");
  }
}
static void read_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(1); }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = malloc((size_t)len + 1); if (fread(src, 1, (size_t)len, f) != (size_t)len) { perror(path); exit(1); }
  src[len] = 0; fclose(f); read_src(src);
}
/* the types a declaration's type is written with */
static const char *CORE = "type Pair { Pair(fst: _, snd: _) } type Eq { Refl } type Type { Sig(a: _, f: _), Pi(a: _, f: _), Eql(x: _, y: _) }";

int main(int argc, char **argv) {
  { struct rlimit rl; if (!getrlimit(RLIMIT_STACK, &rl)) { rl.rlim_cur = rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }
  if (argc < 2) { fprintf(stderr, "usage: hyper FILE…\n"); return 1; }
  ORDER = getenv("HYPER_ORDER") != 0;
  read_src(CORE);
  C_PAIR = find_ctor("Pair"); C_REFL = find_ctor("Refl"); C_SIG = find_ctor("Sig"); C_PI = find_ctor("Pi"); C_EQL = find_ctor("Eql"); T_EQ = find_type("Eq");
  for (int i = 1; i < argc; i++) read_file(argv[i]);
  for (int d = 0; d < NDF; d++) if (!DF[d].body) { fprintf(stderr, "hyper: @%s is used but not declared\n", DF[d].name); return 2; }
  USE = calloc(NB + 1, sizeof *USE); NEXTUSE = calloc(NB + 1, sizeof *NEXTUSE); UCAP = NB;
  int m = -1; for (int d = 0; d < NDF; d++) if (!strcmp(DF[d].name, "main")) m = d;
  if (m < 0) { fprintf(stderr, "hyper: no @main\n"); return 2; }
  collapse(mk(REF, (u32)m, 0));
  for (u32 i = 0; i < NLEAF; i++) { show(stdout, LEAVES[i], 0); putchar('\n'); }
  printf("- leaves: %u\n- interactions: %llu\n- heap words: %llu\n-", NLEAF, (unsigned long long)ITRS, (unsigned long long)HLEN);
  for (int r = 0; r < R_N; r++) if (RC[r]) printf(" %s %llu", RNAME[r], (unsigned long long)RC[r]);
  printf("\n");
  if (getenv("HYPER_REFS")) { printf("- copies by constructor:"); for (int c = 0; c < NCT; c++) if (DUPCT[c]) printf(" #%s %llu", CT[c].name, (unsigned long long)DUPCT[c]); printf("\n"); }
  if (getenv("HYPER_REFS")) { printf("- unfoldings:"); for (int d = 0; d < NDF; d++) if (REFS[d]) printf(" @%s %llu", DF[d].name, (unsigned long long)REFS[d]); printf("\n"); }
  return 0;
}

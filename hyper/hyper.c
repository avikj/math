/* hyper.c: Hyperactive.
 *
 * The net that Bend2's --to-hvm4-full emits into, and the one thing a declaration adds: a declaration with no
 * body is a coordinate of its type.  Nothing else is here.  Everything cubical (coe, hcomp, ua, Glue), the fibre
 * law (descend/ascend), the whole process (react), and every domain (order, lists, formulas) are programs in the
 * book, reduced by these rules.
 *
 *   TERM  = VAR loc | LAM loc | APP loc | SUP L loc | DP0 L loc | DP1 L loc | ERA
 *         | CTR c loc | MAT T loc | REF d | NUM n | OP2 op loc | CRD T loc
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
 *     APP of MAT to CRD / DUP meets CRD   expand: the coordinate becomes, in place, the superposition of its
 *                                         type's constructors with fresh coordinates for their fields
 *   collapse: the leaves of the result's superposition, the empty ones (&{}) gone.
 *
 * Surface: `type T { C, D(f: U, …) }`;  `@d = term`;  `@d : T` (no body: a coordinate of T);
 *   λx t  |  λ{#C: t; #D: t}  |  (f a …)  |  (op a b)  |  &L{a, b}  |  &{}  |  #C{a, …}  |  @d  |  ?T  |  n
 *   |  !x = t; u  (let).  A variable used k > 1 times is duplicated k − 1 times, each at a fresh label.
 *
 * usage: hyper FILE…   (prints each leaf of @main, then the receipt) */
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

typedef uint64_t Term; typedef uint32_t u32; typedef uint64_t u64;
enum { VAR = 1, LAM, APP, SUP, DP0, DP1, ERA, CTR, MAT, REF, NUM, OP2, CRD };
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
static u32 LABELS = 1u << 16;                                     /* fresh labels; the file's own are below */
static u32 fresh_label(void) { return LABELS++ & 0xFFFFFF; }

/* ---- the receipt ------------------------------------------------------------------------------------------ */
enum { R_BETA, R_APPSUP, R_APPERA, R_MATCH, R_APPMATSUP, R_DUPLAM, R_DUPSUPEQ, R_DUPSUPDIFF, R_DUPNODE,
       R_DUPATOM, R_OP, R_OPSUP, R_EXPAND, R_REF, R_N };
static const char *RNAME[R_N] = { "beta", "appSup", "appEra", "match", "appMatSup", "dupLam", "dupSupEqual",
  "dupSupDifferent", "dupNode", "dupAtom", "op", "opSup", "expand", "ref" };
static u64 RC[R_N], ITRS;
static inline void itr(int r) { RC[r]++; ITRS++; }

/* ---- the book: types, constructors, definitions ------------------------------------------------------------ */
typedef struct { char *name; int type, idx, arity; int ftype[16]; } Ctor;
typedef struct { char *name; int nctor; int ctor[32]; } Type;
static Ctor CT[4096]; static int NCT; static Type TY[512]; static int NTY;
static int find_type(const char *s) { for (int i = 0; i < NTY; i++) if (!strcmp(TY[i].name, s)) return i; return -1; }
static int find_ctor(const char *s) { for (int i = 0; i < NCT; i++) if (!strcmp(CT[i].name, s)) return i; return -1; }

enum { K_VAR, K_LAM, K_APP, K_SUP, K_ERA, K_CTR, K_MAT, K_REF, K_NUM, K_OP2, K_CRD };
typedef struct Ast { int k; u32 x; struct Ast *a, *b, **kids; int n; } Ast;
static Ast *node(int k) { Ast *t = calloc(1, sizeof *t); t->k = k; return t; }
typedef struct { char *name; Ast *body; } Def;
static Def DF[4096]; static int NDF;
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
    case K_CRD: { u32 l = alloc(1); return mk(CRD, t->x, l); }
  }
  return mk(ERA, 0, 0);
}

/* ---- the coordinate: the superposition of its type's constructors ------------------------------------------- */
static Term ctor_with_fresh_fields(int c) {
  int ar = CT[c].arity; u32 l = alloc(ar ? ar : 1);
  for (int i = 0; i < ar; i++) { u32 s = alloc(1); H[l + i] = mk(CRD, (u32)CT[c].ftype[i], s); }
  return mk(CTR, (u32)c, l);
}
static void expand(Term crd) {
  Type *T = &TY[LAB(crd)];
  Term acc = ctor_with_fresh_fields(T->ctor[T->nctor - 1]);
  for (int i = T->nctor - 2; i >= 0; i--) {
    Term c = ctor_with_fresh_fields(T->ctor[i]); u32 l = alloc(2); H[l] = c; H[l + 1] = acc; acc = mk(SUP, fresh_label(), l);
  }
  if (T->nctor == 0) acc = mk(ERA, 0, 0);
  H[LOC(crd)] = acc | SUBB;
  itr(R_EXPAND);
}

/* ---- reduction ------------------------------------------------------------------------------------------------- */
static Term whnf(Term t);
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
static Term app(Term f, Term a) { u32 l = alloc(2); H[l] = f; H[l + 1] = a; return mk(APP, 0, l); }
static u32 opcalc(u32 op, u32 a, u32 b) {
  switch (op) {
    case '+': return a + b; case '-': return a - b; case '*': return a * b; case '/': return b ? a / b : 0; case '%': return b ? a % b : 0;
    case '=': return a == b; case '!': return a != b; case '<': return a < b; case '>': return a > b; case 'l': return a <= b; case 'g': return a >= b;
  }
  return 0;
}

static Term whnf(Term t) {
  for (;;) {
    switch (TAG(t)) {
      case VAR: { u64 s = H[LOC(t)]; if (s & SUBB) { t = s & ~SUBB; continue; } return t; }
      case CRD: { u64 s = H[LOC(t)]; if (s & SUBB) { t = s & ~SUBB; continue; } return t; }
      case REF: { itr(R_REF); t = inst(DF[LAB(t)].body); continue; }
      case DP0: case DP1: {
        u32 e = LOC(t), L = LAB(t); int side = TAG(t) == DP1;
        u64 s = H[e + side]; if (s & SUBB) { t = s & ~SUBB; continue; }
        Term v = whnf(H[e]), r0, r1;
        switch (TAG(v)) {
          case CRD: expand(v); H[e] = v; continue;                  /* the one coordinate, then its copies */
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
          case CTR: case MAT: itr(R_DUPNODE); r0 = node_copy(v, L, &r1); break;
          case NUM: case ERA: itr(R_DUPATOM); r0 = r1 = v; break;
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
              case CRD: expand(v); H[l + 1] = v; continue;
              default: H[l] = f; H[l + 1] = v; return t;
            }
          }
          default: H[l] = f; return t;
        }
      }
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
static Term lift_ctr(Term v) {                                    /* a field's superposition taken to the node's top */
  int ar = CT[LAB(v)].arity;
  for (int i = 0; i < ar; i++) {
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
static Term lift(Term t) { t = whnf(t); return TAG(t) == CTR ? lift_ctr(t) : t; }
static Term *LEAVES; static u32 NLEAF, CLEAF;
static void collapse(Term t) {
  t = lift(t);
  if (TAG(t) == ERA) return;
  if (TAG(t) == SUP) { collapse(H[LOC(t)]); collapse(H[LOC(t) + 1]); return; }
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
    case CRD: fprintf(o, "?%s", TY[LAB(t)].name); return;
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
  if (eat("?")) { char *n = name(); int T = find_type(n); if (T < 0) die("unknown type"); Ast *t = node(K_CRD); t->x = (u32)T; return t; }
  if (eat("!")) {                                                  /* !x = v; body */
    char *x = name(); need("="); Ast *v = term(); need(";");
    int b = new_binder(); SC[NSC++] = (Scope){ x, b }; Ast *body = term(); NSC--;
    Ast *l = node(K_LAM); l->x = (u32)b; l->a = body;
    Ast *t = node(K_APP); t->a = l; t->b = v; return t;
  }
  if (eat("(")) {
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
  die("unbound variable"); return 0;
}
static void read_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(1); }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = malloc((size_t)len + 1); if (fread(src, 1, (size_t)len, f) != (size_t)len) { perror(path); exit(1); }
  src[len] = 0; fclose(f); S = src; P = 0; LINE = 1;
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
        if (eat("(")) { int j = 0; while (!eat(")")) { name(); need(":"); char *ft = name(); CT[ci].ftype[j] = find_type(ft); if (CT[ci].ftype[j] < 0) die("unknown field type"); j++; eat(","); } }
        eat(",");
      }
      continue;
    }
    need("@"); char *n = name(); int d = def_id(n);
    if (eat(":")) {                                                /* no body: a coordinate of its type */
      char *tn = name(); int T = find_type(tn); if (T < 0) die("unknown type");
      Ast *t = node(K_CRD); t->x = (u32)T; DF[d].body = t; eat(";"); continue;
    }
    need("="); NSC = 0; DF[d].body = term(); eat(";");
  }
}

int main(int argc, char **argv) {
  { struct rlimit rl; if (!getrlimit(RLIMIT_STACK, &rl)) { rl.rlim_cur = rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }
  if (argc < 2) { fprintf(stderr, "usage: hyper FILE…\n"); return 1; }
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
  return 0;
}

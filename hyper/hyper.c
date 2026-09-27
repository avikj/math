/* hyper.c: Hyperactive.  One element and one interaction (hyper/HYPERACTIVE.md).
 *
 * The element is an identification.  A wire is refl: two ports that are one value.  A node is an
 * identification not yet folded: a principal port, two auxiliary ports (its faces), and a label (a name).
 * When two nodes meet principal to principal:
 *   same label       fold:     the faces are identified pairwise and both nodes are gone   (J, transport)
 *   different labels commute:  each passes through the other                               (f x = f y is f ∘ p)
 * The node with no faces is erasure; it is the only place information is destroyed.
 * A step is one interaction.  Any order gives the same normal form and the same count (the diamond). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

typedef uint32_t Port;                          /* node << 2 | slot: slot 0 principal, 1 and 2 the faces */
#define NODE(p) ((uint32_t)(p) >> 2)
#define SLOT(p) ((uint32_t)(p) & 3u)
#define PORT(n, s) ((Port)((uint32_t)(n) << 2 | (uint32_t)(s)))

enum { ERA = 0xFFFFFFF0u, ROOT = 0xFFFFFFF1u, FREE = 0xFFFFFFF2u, DEAD = 0xFFFFFFF3u };
#define INERT(l) ((l) == ROOT || (l) == FREE)   /* the ends where the net meets the world: never interact */
#define FRESH0 (1u << 24)                        /* labels at or above this name the sharing of a variable */

static uint32_t *LABEL;                          /* per node: its name, or ERA / ROOT / FREE / DEAD */
static Port *PEER;                               /* per port: the port at the other end of its wire */
static uint32_t NODES, CAP, *FREELIST, NFREE;
static Port *REDEX; static uint32_t NREDEX, RCAP;
static uint64_t STEPS, ERASED;

static uint32_t node(uint32_t label) {
  uint32_t n;
  if (NFREE) n = FREELIST[--NFREE];
  else {
    if (NODES == CAP) {
      CAP = CAP ? CAP * 2 : 1024;
      LABEL = realloc(LABEL, CAP * sizeof *LABEL); PEER = realloc(PEER, (size_t)CAP * 4 * sizeof *PEER);
      FREELIST = realloc(FREELIST, CAP * sizeof *FREELIST);
      if (!LABEL || !PEER || !FREELIST) { fprintf(stderr, "hyper: out of memory\n"); exit(2); }
    }
    n = NODES++;
  }
  LABEL[n] = label;
  PEER[4*n] = PEER[4*n+1] = PEER[4*n+2] = PORT(n, 3);                         /* slot 3: not yet wired */
  return n;
}
static void drop(uint32_t n) { LABEL[n] = DEAD; FREELIST[NFREE++] = n; }

/* a wire: each end names the other; two principal ports facing each other are an active pair */
static void link(Port a, Port b) {
  PEER[a] = b; PEER[b] = a;
  if (SLOT(a) == 0 && SLOT(b) == 0 && !INERT(LABEL[NODE(a)]) && !INERT(LABEL[NODE(b)])) {
    if (NREDEX == RCAP) { RCAP = RCAP ? RCAP * 2 : 1024; REDEX = realloc(REDEX, RCAP * sizeof *REDEX); }
    REDEX[NREDEX++] = a;
  }
}

/* fold: face i of x is face i of y.  A face may be wired to another face of the pair; the live end of each
   outside wire is found by walking through the dying faces.  0 when the walk closes (a loop). */
static uint32_t FX, FY;
static int dying(Port p) { return NODE(p) == FX || NODE(p) == FY; }
static Port partner(Port p) { return PORT(NODE(p) == FX ? FY : FX, SLOT(p)); }
static Port live_end(Port face) {
  Port p = face;
  for (int i = 0; i < 8; i++) {
    Port r = PEER[partner(p)];
    if (!dying(r)) return r;
    p = r;
  }
  return 0;
}

static void interact(Port a, Port b) {
  uint32_t x = NODE(a), y = NODE(b), lx = LABEL[x], ly = LABEL[y];
  STEPS++;
  if (lx == ERA && ly == ERA) { drop(x); drop(y); return; }
  if (lx == ERA || ly == ERA) {                                  /* erasure: the other node's faces are erased */
    uint32_t n = lx == ERA ? y : x, e = lx == ERA ? x : y;
    Port f1 = PEER[PORT(n,1)], f2 = PEER[PORT(n,2)];
    uint32_t e1 = node(ERA), e2 = node(ERA);
    ERASED++;
    drop(n); drop(e);
    if (f1 == PORT(n,2)) { link(PORT(e1,0), PORT(e2,0)); return; }   /* its two faces were wired to each other */
    link(PORT(e1,0), f1); link(PORT(e2,0), f2);
    return;
  }
  if (lx == ly) {                                                 /* fold */
    FX = x; FY = y;
    Port face[4] = { PORT(x,1), PORT(x,2), PORT(y,1), PORT(y,2) }, out[4], end[4];
    for (int i = 0; i < 4; i++) { out[i] = PEER[face[i]]; end[i] = dying(out[i]) ? 0 : live_end(face[i]); }
    drop(x); drop(y);
    for (int i = 0; i < 4; i++) {
      if (!end[i] || dying(out[i])) continue;
      int again = 0;                                              /* each outside wire is joined once */
      for (int k = 0; k < i; k++) if (end[k] && out[k] == end[i] && end[k] == out[i]) again = 1;
      if (!again) link(out[i], end[i]);
    }
    return;
  }
  /* commute: copies of y go to x's faces, copies of x to y's faces, and the copies are cross-wired */
  Port ox[2] = { PEER[PORT(x,1)], PEER[PORT(x,2)] }, oy[2] = { PEER[PORT(y,1)], PEER[PORT(y,2)] };
  uint32_t xc[2] = { node(lx), node(lx) }, yc[2] = { node(ly), node(ly) };
  drop(x); drop(y);
  for (uint32_t i = 0; i < 2; i++) for (uint32_t j = 0; j < 2; j++) link(PORT(yc[i], 1 + j), PORT(xc[j], 1 + i));
  for (uint32_t i = 0; i < 2; i++) {                              /* x's face i is now yc[i]'s principal */
    Port o = ox[i];
    if (NODE(o) == y) { link(PORT(yc[i],0), PORT(xc[SLOT(o)-1],0)); continue; }
    if (NODE(o) == x) { if (SLOT(o) > 1 + i) link(PORT(yc[i],0), PORT(yc[SLOT(o)-1],0)); continue; }
    link(PORT(yc[i],0), o);
  }
  for (uint32_t j = 0; j < 2; j++) {                              /* y's face j is now xc[j]'s principal */
    Port o = oy[j];
    if (NODE(o) == x) continue;                                   /* joined from x's side */
    if (NODE(o) == y) { if (SLOT(o) > 1 + j) link(PORT(xc[j],0), PORT(xc[SLOT(o)-1],0)); continue; }
    link(PORT(xc[j],0), o);
  }
}

static void run(void) {
  while (NREDEX) {
    Port a = REDEX[--NREDEX], b = PEER[a];
    if (LABEL[NODE(a)] == DEAD || SLOT(b) != 0 || LABEL[NODE(b)] == DEAD) continue;
    interact(a, b);
  }
}

/* ---- reading in: a term becomes wiring of the element, with no evaluation -------------------------------
 *   \x t                 a node at label 0: principal is the value, face 1 the variable, face 2 the body
 *   (f a b ...)          a node at label 0 per argument: principal meets f, face 1 takes a, face 2 the result
 *   {a b}#L              a node at label L: principal is the value, faces a and b
 *   let {x y}#L = t; u   a node at label L: principal meets t, the faces are x and y
 *   let x = t; u         x names t
 *   *                    erasure
 *   name                 a bound variable, else the definition `name = term;` in place, else a free port
 * A variable used k times is shared by k-1 nodes at fresh labels; used zero times it is erased. */
typedef struct Tm { int kind; char *name, *name2; struct Tm *a, *b; uint32_t label; } Tm;
enum { VAR, LAM, APP, SUP, DUP, LET, ERASE };
static const char *SRC; static size_t POS;
static void skip(void) {
  for (;;) {
    while (isspace((unsigned char)SRC[POS])) POS++;
    if (SRC[POS] == '/' && SRC[POS+1] == '/') { while (SRC[POS] && SRC[POS] != '\n') POS++; continue; }
    return;
  }
}
static int peek(char c) { skip(); return SRC[POS] == c; }
static void expect(char c) { skip(); if (SRC[POS] != c) { fprintf(stderr, "hyper: expected '%c' at offset %zu\n", c, POS); exit(2); } POS++; }
static int namechar(char c) { return isalnum((unsigned char)c) || c == '_' || c == '\'' || c == '-' || c == '.'; }
static char *ident(void) {
  skip(); size_t s = POS; while (namechar(SRC[POS])) POS++;
  if (s == POS) { fprintf(stderr, "hyper: expected a name at offset %zu\n", POS); exit(2); }
  char *r = malloc(POS - s + 1); memcpy(r, SRC + s, POS - s); r[POS - s] = 0; return r;
}
static char **LNAMES; static uint32_t NLABELS;
static uint32_t label_of(const char *nm) {                        /* user labels 1..; label 0 is the function's */
  for (uint32_t i = 0; i < NLABELS; i++) if (!strcmp(LNAMES[i], nm)) return i + 1;
  LNAMES = realloc(LNAMES, (NLABELS + 1) * sizeof *LNAMES); LNAMES[NLABELS] = strdup(nm); return ++NLABELS;
}
static Tm *mk(int k) { Tm *t = calloc(1, sizeof *t); t->kind = k; return t; }
static Tm *term(void) {
  skip();
  if (SRC[POS] == '\\') { POS++; Tm *t = mk(LAM); t->name = ident(); t->a = term(); return t; }
  if (SRC[POS] == '*') { POS++; return mk(ERASE); }
  if (SRC[POS] == '(') {
    POS++; Tm *f = term();
    while (!peek(')')) { Tm *t = mk(APP); t->a = f; t->b = term(); f = t; }
    POS++; return f;
  }
  if (SRC[POS] == '{') {
    POS++; Tm *t = mk(SUP); t->a = term(); t->b = term(); expect('}'); expect('#'); t->label = label_of(ident()); return t;
  }
  char *w = ident();
  if (!strcmp(w, "let")) {
    if (peek('{')) {
      POS++; Tm *t = mk(DUP); t->name = ident(); t->name2 = ident(); expect('}'); expect('#'); t->label = label_of(ident());
      expect('='); t->a = term(); expect(';'); t->b = term(); return t;
    }
    Tm *t = mk(LET); t->name = ident(); expect('='); t->a = term(); expect(';'); t->b = term(); return t;
  }
  Tm *t = mk(VAR); t->name = w; return t;
}
typedef struct { char *name; Tm *body; } Def;
static Def *DEFS; static int NDEFS;
static Tm *def_of(const char *nm) { for (int i = 0; i < NDEFS; i++) if (!strcmp(DEFS[i].name, nm)) return DEFS[i].body; return 0; }

static int uses(Tm *t, const char *x) {                           /* free occurrences of x in t */
  switch (t->kind) {
    case VAR: return !strcmp(t->name, x);
    case LAM: return strcmp(t->name, x) ? uses(t->a, x) : 0;
    case APP: case SUP: return uses(t->a, x) + uses(t->b, x);
    case DUP: return uses(t->a, x) + (strcmp(t->name, x) && strcmp(t->name2, x) ? uses(t->b, x) : 0);
    case LET: return uses(t->a, x) + (strcmp(t->name, x) ? uses(t->b, x) : 0);
    default: return 0;
  }
}
typedef struct Bind { const char *name; Port *use; int n, k; struct Bind *up; } Bind;
static uint32_t FRESH = FRESH0;
static Bind *bind(Bind *up, const char *name, Port source, int k) {
  Bind *b = calloc(1, sizeof *b); b->name = name; b->up = up; b->n = k; b->use = calloc(k ? k : 1, sizeof(Port));
  if (k == 0) { link(PORT(node(ERA),0), source); return b; }
  for (int i = 0; i < k - 1; i++) {                               /* one node at a fresh label per extra use */
    uint32_t d = node(FRESH++); link(PORT(d,0), source); b->use[i] = PORT(d,1); source = PORT(d,2);
  }
  b->use[k-1] = source; return b;
}
static int DEPTH;
static Port compile(Tm *t, Bind *env) {
  if (++DEPTH > 1000000) { fprintf(stderr, "hyper: definitions unfold without end\n"); exit(2); }
  Port r = 0;
  switch (t->kind) {
    case VAR: {
      for (Bind *b = env; b; b = b->up) if (!strcmp(b->name, t->name)) { r = b->use[b->k++]; goto done; }
      Tm *d = def_of(t->name);
      r = d ? compile(d, 0) : PORT(node(FREE),0);                 /* a free name is an open port: the world's */
      break;
    }
    case ERASE: r = PORT(node(ERA),0); break;
    case LAM: {
      uint32_t n = node(0);
      Bind *b = bind(env, t->name, PORT(n,1), uses(t->a, t->name));
      link(compile(t->a, b), PORT(n,2));
      r = PORT(n,0); break;
    }
    case APP: {
      uint32_t n = node(0);
      link(compile(t->a, env), PORT(n,0));
      link(compile(t->b, env), PORT(n,1));
      r = PORT(n,2); break;
    }
    case SUP: {
      uint32_t n = node(t->label);
      link(compile(t->a, env), PORT(n,1));
      link(compile(t->b, env), PORT(n,2));
      r = PORT(n,0); break;
    }
    case DUP: {
      uint32_t n = node(t->label);
      link(compile(t->a, env), PORT(n,0));
      Bind *b1 = bind(env, t->name, PORT(n,1), uses(t->b, t->name));
      Bind *b2 = bind(b1, t->name2, PORT(n,2), strcmp(t->name, t->name2) ? uses(t->b, t->name2) : 0);
      r = compile(t->b, b2); break;
    }
    case LET: {
      Port v = compile(t->a, env);
      r = compile(t->b, bind(env, t->name, v, uses(t->b, t->name))); break;
    }
  }
done:
  DEPTH--; return r;
}

/* ---- reading out: walk the net from the root; a fold that copies it, no interaction -------------------- */
static char *OUT; static size_t OLEN, OCAP;
static void emit(const char *s) {
  size_t n = strlen(s);
  if (OLEN + n + 1 > OCAP) { OCAP = (OLEN + n + 1) * 2; OUT = realloc(OUT, OCAP); }
  memcpy(OUT + OLEN, s, n + 1); OLEN += n;
}
static const char *label_name(uint32_t l, char *buf) { if (l >= 1 && l <= NLABELS) return LNAMES[l-1]; sprintf(buf, "%u", l); return buf; }
/* A path through the net enters a node at one label through a face and, when it later meets a node of the same
   label at its principal port, leaves through the same face: the two are one identification.  The faces entered
   so far are kept as a stack; a principal port with no entered face of its label is a superposition. */
typedef struct { uint32_t label, face; int used; } Entered;
static Entered ENTERED[1 << 16]; static int NENTERED;
static void readback(Port p, int depth) {                         /* the value the port p offers */
  char buf[64];
  if (depth > 100000 || NENTERED >= (1 << 16) - 1) { emit("..."); return; }
  uint32_t n = NODE(p), s = SLOT(p), l = LABEL[n];
  if (l == ERA) { emit("*"); return; }
  if (l == FREE) { emit("?"); return; }
  if (l == 0) {
    if (s == 0) { sprintf(buf, "\\x%u ", n); emit(buf); readback(PEER[PORT(n,2)], depth + 1); return; }  /* a function */
    if (s == 1) { sprintf(buf, "x%u", n); emit(buf); return; }                                            /* its variable */
    emit("("); readback(PEER[PORT(n,0)], depth + 1); emit(" "); readback(PEER[PORT(n,1)], depth + 1); emit(")");
    return;                                                                                                /* a stuck application */
  }
  if (s != 0) {                                                   /* entering through a face: remember it */
    ENTERED[NENTERED++] = (Entered){ l, s, 0 };
    readback(PEER[PORT(n,0)], depth + 1);
    NENTERED--; return;
  }
  for (int k = NENTERED - 1; k >= 0; k--) if (!ENTERED[k].used && ENTERED[k].label == l) {   /* leave by that face */
    ENTERED[k].used = 1; readback(PEER[PORT(n, ENTERED[k].face)], depth + 1); ENTERED[k].used = 0; return;
  }
  emit("{"); readback(PEER[PORT(n,1)], depth + 1); emit(" "); readback(PEER[PORT(n,2)], depth + 1);
  emit("}#"); emit(label_name(l, buf));                                                                    /* a superposition */
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: hyper FILE [NAME]\n"); return 1; }
  FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
  fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
  char *buf = malloc((size_t)len + 1);
  if (fread(buf, 1, (size_t)len, f) != (size_t)len) { perror(argv[1]); return 1; }
  buf[len] = 0; fclose(f);
  SRC = buf; POS = 0;
  for (skip(); SRC[POS]; skip()) {                                /* name = term ; */
    DEFS = realloc(DEFS, (NDEFS + 1) * sizeof *DEFS);
    DEFS[NDEFS].name = ident(); expect('='); DEFS[NDEFS].body = term(); expect(';'); NDEFS++;
  }
  const char *entry = argc > 2 ? argv[2] : "main";
  Tm *m = def_of(entry); if (!m) { fprintf(stderr, "hyper: no %s\n", entry); return 1; }
  uint32_t root = node(ROOT);
  link(PORT(root,0), compile(m, 0));
  run();
  readback(PEER[PORT(root,0)], 0);
  printf("%s\n- steps: %llu\n- erased: %llu\n", OUT ? OUT : "", (unsigned long long)STEPS, (unsigned long long)ERASED);
  return 0;
}

/* hyper/inet.c — the machine of index.html §5.2, as written and nothing else.
 *
 * 5.4  A cell has one principal port and finitely many auxiliary ports. A net is a finite set of cells with a
 *      partial matching of their ports by wires. A port not matched is free.
 * 5.5  An active pair is two cells whose principal ports are wired to each other. A rule gives, for a pair of
 *      cell kinds, a net on exactly the auxiliary wires of the two cells; the step replaces the pair by it and
 *      touches nothing else. The two cells of the pair are consumed by the step: that is the whole of memory.
 * 5.1  The cell kinds are the type theory's constructors: abstraction and application (→), constructors and case
 *      (× ⊎ ⊥ Σ), the duplicator (5.24), the erasure, and the complex's own: a coordinate (a path &L{a,b}, a
 *      superposition), its faces, a fresh coordinate, the collapse.
 * 5.7  Two costs: the length (steps) and the effect-cost (bits merged). A step that discards a side or a branch
 *      is a merge; a reversible step costs nothing on that axis.
 *
 * No global substitution, no heap of terms, no evaluator: variables are wires, sharing is a duplicator cell,
 * reduction is the active pairs in any order (5.11: the result and the length do not depend on it). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

typedef uint32_t u32; typedef uint64_t u64; typedef uint8_t u8;

/* ---------- cells and wires ---------- */
enum { K_ERA, K_LAM, K_APP, K_SUP, K_DUP, K_CTR, K_MATV, K_MAT, K_REF, K_NUM, K_FRS, K_FRI, K_DSU, K_DDU,
       K_FAD, K_FDL, K_FA, K_COL, K_APPEND, K_LIFT, K_LIFTC, K_EQL, K_EQLC, K_EQLN, K_AND, K_NF, K_LAMV, K_LABELS, K_ROOT, K_FREE };
static const char *KIND_NAME[] = { "ERA","LAM","APP","SUP","DUP","CTR","MATV","MAT","REF","NUM","FRS","FRI","DSU","DDU",
       "FAD","FDL","FA","COL","APPEND","LIFT","LIFTC","EQL","EQLC","EQLN","AND","NF","LAMV","LABELS","ROOT","FREE" };
#define MAXP 18                        /* principal + up to 17 auxiliary ports */
#define NIL 0xFFFFFFFFu                /* a free port */
typedef u32 Port;                      /* cell << 5 | slot */
#define P(c,s) (((u32)(c) << 5) | (u32)(s))
#define PC(p) ((p) >> 5)
#define PS(p) ((p) & 31)
typedef struct { u8 kind; u8 ari; u32 ext; u32 ext2; Port p[MAXP]; } Cell;
static Cell *CELLS; static u32 NCELLS = 0, CAP = 0; static u32 FREELIST = NIL; static u32 *GEN;   /* a cell index is reused; its generation tells a stale port */
static u64 LIVE = 0, PEAK = 0;
static u32 *ACTIVE; static u32 NACTIVE = 0, ACAP = 0;   /* one cell of each active pair */
static u64 STEPS = 0, MERGES = 0, UNFOLDS = 0;
static u64 RULES[64][64];

static u32 cell_new(u8 kind, u8 ari, u32 ext) {
  u32 c;
  if (FREELIST != NIL) { c = FREELIST; FREELIST = CELLS[c].ext; }
  else { if (NCELLS == CAP) { CAP = CAP ? CAP * 2 : 1 << 16; CELLS = realloc(CELLS, CAP * sizeof(Cell)); GEN = realloc(GEN, CAP * sizeof(u32)); memset(GEN + NCELLS, 0, (CAP - NCELLS) * sizeof(u32)); } c = NCELLS++; }
  CELLS[c].kind = kind; CELLS[c].ari = ari; CELLS[c].ext = ext; CELLS[c].ext2 = 0;
  for (u32 i = 0; i <= ari; i++) CELLS[c].p[i] = NIL;
  LIVE++; if (LIVE > PEAK) PEAK = LIVE;
  return c;
}
static void cell_free(u32 c) { CELLS[c].kind = K_FREE; CELLS[c].ext = FREELIST; FREELIST = c; LIVE--; GEN[c]++; }
static void active_push(u32 c) { if (NACTIVE == ACAP) { ACAP = ACAP ? ACAP * 2 : 1 << 12; ACTIVE = realloc(ACTIVE, ACAP * sizeof(u32)); } ACTIVE[NACTIVE++] = c; }
/* wire two ports: the matching is partial, a port is wired at most once */
static void wire(Port a, Port b) {
  if (a == NIL || b == NIL) { if (a != NIL) CELLS[PC(a)].p[PS(a)] = NIL; if (b != NIL) CELLS[PC(b)].p[PS(b)] = NIL; return; }
  CELLS[PC(a)].p[PS(a)] = b; CELLS[PC(b)].p[PS(b)] = a;
  /* an erasure meeting a principal port is taken as soon as the rule that made it is done: its steps commute with
     every other and end (nothing unfolds under an erasure), and a sub-net erased is memory returned */
  if (PS(a) == 0 && PS(b) == 0 && (CELLS[PC(a)].kind == K_ERA || CELLS[PC(b)].kind == K_ERA)) active_push(PC(a));
}
/* the port wired to p (NIL when free) */
static Port peer(Port p) { return CELLS[PC(p)].p[PS(p)]; }
static u32 LAB_CHOICE = 1u << 20, LAB_INDEX = 1u << 18;    /* fresh coordinates: choices above, index coordinates below */
/* a choice coordinate: a static label or a fresh ? ; an index coordinate (??) is a node of the value, not a choice */
static int is_choice(u32 lab) { return !(lab >= (1u << 18) && lab < (1u << 20)); }

/* ---------- names ---------- */
#define MAXNAMES 65536
static char *NAMES[MAXNAMES]; static u32 NNAMES = 0;
static u32 name_id(const char *s, size_t n) {
  for (u32 i = 0; i < NNAMES; i++) if (strlen(NAMES[i]) == n && !memcmp(NAMES[i], s, n)) return i;
  NAMES[NNAMES] = strndup(s, n); return NNAMES++;
}

/* ---------- terms (the source, kept only to instantiate definitions) ---------- */
enum { T_VAR, T_LAM, T_APP, T_SUP, T_DSU, T_ERA, T_CTR, T_MATV, T_REF, T_LET, T_LETD, T_FRS, T_FRI, T_FAD, T_FAC, T_COL, T_COLQ, T_EQL, T_NUM, T_FAN };
typedef struct Term { u8 tag; u8 affine; u32 name; u32 n; struct Term **a; u32 *names; u8 has_default; u32 matv_id; u32 nfv; u32 *fv; u8 fv_done; } Term;
static Term *tm(u8 tag) { Term *t = calloc(1, sizeof(Term)); t->tag = tag; return t; }
static void tm_push(Term *t, Term *x) { t->a = realloc(t->a, (t->n + 1) * sizeof(Term *)); t->a[t->n++] = x; }
#define MAXDEFS 65536
static Term *DEFS[MAXDEFS];

/* ---------- parser ---------- */
static const char *SRC; static const char *CUR; static const char *FILE_NAME;
static void perr(const char *msg) { fprintf(stderr, "PARSE_ERROR (%s): %s at: %.40s\n", FILE_NAME, msg, CUR); exit(1); }
static void skip(void) {
  for (;;) {
    while (*CUR && isspace((unsigned char)*CUR)) CUR++;
    if (CUR[0] == '/' && CUR[1] == '/') { while (*CUR && *CUR != '\n') CUR++; continue; }
    return;
  }
}
static int is_name_char(char c) { return isalnum((unsigned char)c) || c == '_' || c == '\''; }
static u32 read_name(void) {
  skip(); const char *s = CUR;
  while (is_name_char(*CUR)) CUR++;
  if (CUR == s) perr("expected a name");
  return name_id(s, (size_t)(CUR - s));
}
static int peek(const char *s) { skip(); return strncmp(CUR, s, strlen(s)) == 0; }
static void expect(const char *s) { if (!peek(s)) { char b[64]; snprintf(b, 64, "expected '%s'", s); perr(b); } CUR += strlen(s); }
static int peek_lambda(void) { skip(); return (unsigned char)CUR[0] == 0xCE && (unsigned char)CUR[1] == 0xBB; }   /* λ */
static Term *parse_term(void);
static Term *parse_args(Term *f) {
  while (peek("(")) {
    CUR++;
    for (;;) { Term *x = parse_term(); Term *ap = tm(T_APP); tm_push(ap, f); tm_push(ap, x); f = ap; if (peek(",")) { CUR++; continue; } expect(")"); break; }
  }
  return f;
}
static Term *parse_atom(void) {
  skip();
  if (peek_lambda()) {
    CUR += 2; skip();
    if (*CUR == '{') {                                   /* λ{#C: t; ...; λx. t} */
      CUR++; Term *m = tm(T_MATV);
      for (;;) {
        skip();
        if (*CUR == '}') { CUR++; break; }
        if (*CUR == '#') {
          CUR++; u32 nm = read_name(); expect(":"); Term *b = parse_term();
          m->names = realloc(m->names, (m->n + 1) * sizeof(u32)); m->names[m->n] = nm; tm_push(m, b);
        } else { Term *d = parse_term(); m->has_default = 1; tm_push(m, d); }
        skip(); if (*CUR == ';') CUR++;
      }
      return parse_args(m);
    }
    Term *l = tm(T_LAM);
    if (*CUR == '&') { CUR++; l->affine = 0; } else l->affine = 1;
    l->name = read_name(); expect("."); tm_push(l, parse_term()); return l;
  }
  if (*CUR == '!') {                                     /* ! &x = t; body   |   ! &(c){a,b} = t; body */
    CUR++; expect("&"); skip();
    if (*CUR == '(' || is_name_char(*CUR)) {
      const char *save = CUR;
      if (*CUR == '(') {
        CUR++; u32 lab = read_name(); expect(")"); expect("{"); u32 a = read_name(); expect(","); u32 b = read_name(); expect("}"); expect("=");
        Term *v = parse_term(); expect(";"); Term *body = parse_term();
        Term *d = tm(T_LETD); d->name = lab; d->names = malloc(2 * sizeof(u32)); d->names[0] = a; d->names[1] = b; tm_push(d, v); tm_push(d, body); return d;
      }
      u32 x = read_name(); skip();
      if (*CUR == '{') { CUR = save; perr("a named dup binder is not in this machine"); }
      expect("="); Term *v = parse_term(); expect(";"); Term *body = parse_term();
      Term *l = tm(T_LET); l->name = x; tm_push(l, v); tm_push(l, body); return l;
    }
    perr("after !");
  }
  if (*CUR == '&') {                                     /* &{}  &(c){a,b}  &I{a,b} */
    CUR++; skip();
    if (*CUR == '{') { CUR++; skip(); if (*CUR == '}') { CUR++; return parse_args(tm(T_ERA)); } perr("&{ without }"); }
    if (*CUR == '(') { CUR++; Term *lab = parse_term(); expect(")"); expect("{"); Term *a = parse_term(); expect(","); Term *b = parse_term(); expect("}");
      Term *s = tm(T_DSU); tm_push(s, lab); tm_push(s, a); tm_push(s, b); return parse_args(s); }
    u32 lab = read_name(); expect("{"); Term *a = parse_term(); expect(","); Term *b = parse_term(); expect("}");
    Term *s = tm(T_SUP); s->name = lab; tm_push(s, a); tm_push(s, b); return parse_args(s);
  }
  if (*CUR == '#') {                                     /* #Name{...} */
    CUR++; u32 nm = read_name(); Term *c = tm(T_CTR); c->name = nm; skip();
    if (*CUR == '{') { CUR++; skip(); if (*CUR == '}') CUR++; else for (;;) { tm_push(c, parse_term()); if (peek(",")) { CUR++; continue; } expect("}"); break; } }
    return parse_args(c);
  }
  if (*CUR == '@') { CUR++; u32 nm = read_name(); Term *r = tm(T_REF); r->name = nm; return parse_args(r); }
  if (*CUR == '(') { CUR++; Term *t = parse_term(); expect(")"); return parse_args(t); }
  if (CUR[0] == '?' && CUR[1] == '?') { CUR += 2; return tm(T_FRI); }
  if (*CUR == '?') { CUR++; return tm(T_FRS); }
  if (*CUR == '|') {                                     /* |(side)(coord) x   |   |0I x  |1I x */
    CUR++; skip();
    if (*CUR == '(') { CUR++; Term *side = parse_term(); expect(")"); expect("("); Term *lab = parse_term(); expect(")"); Term *x = parse_atom();
      Term *f = tm(T_FAD); tm_push(f, side); tm_push(f, lab); tm_push(f, x); return f; }
    u8 side = *CUR == '1'; if (*CUR != '0' && *CUR != '1') perr("face side"); CUR++; u32 lab = read_name(); Term *x = parse_atom();
    Term *f = tm(T_FAC); f->name = lab; f->affine = side; tm_push(f, x); return f;
  }
  if (CUR[0] == '%' && CUR[1] == '%') { CUR += 2; Term *c = tm(T_COL); tm_push(c, parse_atom()); Term *r = tm(T_REF); r->name = name_id("colq", 4); Term *ap = tm(T_APP); tm_push(ap, r); tm_push(ap, c); return ap; }
  if (peek("labels(")) { CUR += 6; Term *l = tm(T_COLQ); CUR++; tm_push(l, parse_term()); expect(")"); return l; }
  if (*CUR == '%') { CUR++; Term *c = tm(T_COL); tm_push(c, parse_atom()); return c; }
  if (*CUR == '[') {                                     /* [a, b, c] is #Cons{a, #Cons{b, #Cons{c, #Nil}}} */
    CUR++; Term *items = tm(T_CTR); skip();
    if (*CUR == ']') CUR++; else for (;;) { tm_push(items, parse_term()); if (peek(",")) { CUR++; continue; } expect("]"); break; }
    Term *l = tm(T_CTR); l->name = name_id("Nil", 3);
    for (u32 i = items->n; i > 0; i--) { Term *c = tm(T_CTR); c->name = name_id("Cons", 4); tm_push(c, items->a[i - 1]); tm_push(c, l); l = c; }
    return parse_args(l);
  }
  if (isdigit((unsigned char)*CUR)) perr("a number is not primitive here");
  if (is_name_char(*CUR)) { u32 nm = read_name(); Term *v = tm(T_VAR); v->name = nm; return parse_args(v); }
  perr("unexpected");
  return NULL;
}
static Term *parse_term(void) {
  Term *t = parse_atom();
  if (peek("===")) { CUR += 3; Term *u = parse_term(); Term *e = tm(T_EQL); tm_push(e, t); tm_push(e, u); return e; }
  return t;
}
static void parse_file(const char *path);
static void parse_source(const char *path, const char *src) {
  const char *save_src = SRC, *save_cur = CUR, *save_name = FILE_NAME;
  SRC = src; CUR = src; FILE_NAME = path;
  for (;;) {
    skip(); if (!*CUR) break;
    if (peek("#include")) {
      CUR += 8; expect("\""); const char *s = CUR; while (*CUR && *CUR != '"') CUR++;
      char inc[512]; const char *slash = strrchr(path, '/'); size_t dl = slash ? (size_t)(slash - path + 1) : 0;
      snprintf(inc, sizeof inc, "%.*s%.*s", (int)dl, path, (int)(CUR - s), s); CUR++;
      parse_file(inc); continue;
    }
    expect("@"); u32 nm = read_name(); expect("="); Term *body = parse_term();
    if (nm >= MAXDEFS) perr("too many definitions");
    DEFS[nm] = body;
  }
  SRC = save_src; CUR = save_cur; FILE_NAME = save_name;
}
static void parse_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) { fprintf(stderr, "hyper: could not open %s\n", path); exit(1); }
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *src = malloc((size_t)n + 1); if (fread(src, 1, (size_t)n, f) != (size_t)n) { fprintf(stderr, "hyper: read %s\n", path); exit(1); } src[n] = 0; fclose(f);
  parse_source(path, src);
}

static Port (*LINKS)[2]; static u32 NLINKS = 0, LCAP = 0;
/* ---------- compilation: a term is a net with one free port, its root; variables are wires ---------- */
typedef struct { u32 name; Port *uses; u32 n, cap; } Bind;
static Bind *ENV; static u32 NENV = 0, ECAP = 0;
static void env_push(u32 name) { if (NENV == ECAP) { ECAP = ECAP ? ECAP * 2 : 64; ENV = realloc(ENV, ECAP * sizeof(Bind)); } ENV[NENV].name = name; ENV[NENV].uses = NULL; ENV[NENV].n = 0; ENV[NENV].cap = 0; NENV++; }
static Bind *env_find(u32 name) { for (u32 i = NENV; i > 0; i--) if (ENV[i - 1].name == name) return &ENV[i - 1]; return NULL; }
static void use_add(Bind *b, Port p) { if (b->n == b->cap) { b->cap = b->cap ? b->cap * 2 : 4; b->uses = realloc(b->uses, b->cap * sizeof(Port)); } b->uses[b->n++] = p; }
/* connect a use to the port that produces its value. A use whose placeholder was never wired is the root of a
   term a rule has already linked: that link's end is rewritten to the value. */
static void bind_use(Port placeholder, Port value, void (*conn)(Port, Port)) {
  u32 w = PC(placeholder); Port u = CELLS[w].p[1]; cell_free(w);
  if (u != NIL) { conn(u, value); return; }
  for (u32 j = 0; j < NLINKS; j++) for (u32 k = 0; k < 2; k++) if (LINKS[j][k] == placeholder) { LINKS[j][k] = value; return; }
  fprintf(stderr, "hyper: a use with no user\n"); exit(1);
}
/* a use of a variable: a placeholder cell whose slot 1 the user wires; the binder connects it later */
static Port var_use(u32 name) {
  Bind *b = env_find(name); if (!b) { fprintf(stderr, "hyper: unbound %s\n", NAMES[name]); exit(1); }
  u32 w = cell_new(K_ROOT, 1, 0); use_add(b, P(w, 1)); return P(w, 1);
}
static void link(Port a, Port b);
/* bind a variable's uses to the port that produces its value: none → erase, one → wire, many → a duplicator
   tree. Inside a rule the value port is an external wire end and the connection is a link. */
static void env_pop_wire(Port value, int external) {
  Bind *b = &ENV[--NENV];
  void (*conn)(Port, Port) = external ? link : wire;
  if (b->n == 0) { u32 e = cell_new(K_ERA, 0, 0); conn(P(e, 0), value); }
  else if (b->n == 1) bind_use(b->uses[0], value, conn);
  else {
    Port src = value;
    for (u32 i = 0; i + 1 < b->n; i++) {
      u32 d = cell_new(K_DUP, 2, LAB_CHOICE++);       /* an auto-dup is a coordinate of its own, fresh per instantiation (5.24) */
      conn(P(d, 0), src); bind_use(b->uses[i], P(d, 1), wire);
      if (i + 2 == b->n) bind_use(b->uses[i + 1], P(d, 2), wire); else src = P(d, 2);
      conn = wire;
    }
  }
  free(b->uses);
}
/* the free variables of a term: the names it uses that it does not bind */
static void fv_collect(Term *t, u32 *bound, u32 nb, u32 **out, u32 *n, u32 *cap) {
  switch (t->tag) {
    case T_VAR: {
      for (u32 i = 0; i < nb; i++) if (bound[i] == t->name) return;
      for (u32 i = 0; i < *n; i++) if ((*out)[i] == t->name) return;
      if (*n == *cap) { *cap = *cap ? *cap * 2 : 8; *out = realloc(*out, *cap * sizeof(u32)); } (*out)[(*n)++] = t->name; return; }
    case T_LAM: { u32 nb2[nb + 1]; memcpy(nb2, bound, nb * sizeof(u32)); nb2[nb] = t->name; fv_collect(t->a[0], nb2, nb + 1, out, n, cap); return; }
    case T_LET: { fv_collect(t->a[0], bound, nb, out, n, cap); u32 nb2[nb + 1]; memcpy(nb2, bound, nb * sizeof(u32)); nb2[nb] = t->name; fv_collect(t->a[1], nb2, nb + 1, out, n, cap); return; }
    case T_LETD: { Term v = { .tag = T_VAR, .name = t->name }; fv_collect(&v, bound, nb, out, n, cap); fv_collect(t->a[0], bound, nb, out, n, cap);
      u32 nb2[nb + 2]; memcpy(nb2, bound, nb * sizeof(u32)); nb2[nb] = t->names[0]; nb2[nb + 1] = t->names[1]; fv_collect(t->a[1], nb2, nb + 2, out, n, cap); return; }
    default: for (u32 i = 0; i < t->n; i++) fv_collect(t->a[i], bound, nb, out, n, cap); return;
  }
}
static void term_fv(Term *t) {
  if (t->fv_done) return;
  u32 cap = 0; t->fv = NULL; t->nfv = 0;
  if (t->tag == T_LAM) { u32 b[1] = { t->name }; fv_collect(t->a[0], b, 1, &t->fv, &t->nfv, &cap); }
  else for (u32 i = 0; i < t->n; i++) fv_collect(t->a[i], NULL, 0, &t->fv, &t->nfv, &cap);
  t->fv_done = 1;
}
Term **CLOS_TERMS; u32 NCLOS = 0;
static u32 clos_id(Term *t) {
  if (!t->matv_id) { if (NCLOS >= (1u << 22)) { fprintf(stderr, "hyper: closure table\n"); exit(1); } CLOS_TERMS[NCLOS] = t; t->matv_id = ++NCLOS; }
  return t->matv_id - 1;
}
/* a closure: the term is instantiated when the cell meets its argument (no reduction under a binder: a
   branch not taken or a function never applied builds nothing) */
static u32 closure(u8 kind, Term *t) {
  term_fv(t);
  if (t->nfv > 16) { fprintf(stderr, "hyper: more than 16 free variables in a closure\n"); exit(1); }
  u32 c = cell_new(kind, (u8)t->nfv, clos_id(t));
  for (u32 i = 0; i < t->nfv; i++) wire(P(c, i + 1), var_use(t->fv[i]));
  return c;
}
static Port compile(Term *t);
static Port compile(Term *t) {
  switch (t->tag) {
    case T_VAR: return var_use(t->name);
    case T_LAM: { u32 l = closure(K_LAM, t); return P(l, 0); }
    case T_APP: { Port f = compile(t->a[0]); Port x = compile(t->a[1]); u32 a = cell_new(K_APP, 2, 0); wire(P(a, 0), f); wire(P(a, 1), x); return P(a, 2); }
    case T_SUP: { u32 s = cell_new(K_SUP, 2, 1 + t->name); Port a = compile(t->a[0]); Port b = compile(t->a[1]); wire(P(s, 1), a); wire(P(s, 2), b); return P(s, 0); }
    case T_DSU: { u32 s = cell_new(K_DSU, 3, 0); Port lab = compile(t->a[0]); wire(P(s, 0), lab);
      Port a = compile(t->a[1]); Port b = compile(t->a[2]); wire(P(s, 2), a); wire(P(s, 3), b); return P(s, 1); }
    case T_ERA: { u32 e = cell_new(K_ERA, 0, 0); return P(e, 0); }
    case T_CTR: { if (t->n > 16) { fprintf(stderr, "hyper: constructor arity > 16\n"); exit(1); }
      u32 c = cell_new(K_CTR, (u8)t->n, t->name); for (u32 i = 0; i < t->n; i++) { Port f = compile(t->a[i]); wire(P(c, i + 1), f); } return P(c, 0); }
    case T_MATV: { u32 m = closure(K_MATV, t); return P(m, 0); }
    case T_REF: { u32 r = cell_new(K_REF, 0, t->name); return P(r, 0); }
    case T_LET: { Port v = compile(t->a[0]); env_push(t->name); Port body = compile(t->a[1]); env_pop_wire(v, 0); return body; }
    case T_LETD: { Port v = compile(t->a[0]); u32 d = cell_new(K_DDU, 3, 0); wire(P(d, 1), v); wire(P(d, 0), var_use(t->name));
      env_push(t->names[0]); env_push(t->names[1]); Port body = compile(t->a[1]); env_pop_wire(P(d, 3), 0); env_pop_wire(P(d, 2), 0); return body; }
    case T_FRS: { u32 f = cell_new(K_FRS, 0, 0); return P(f, 0); }
    case T_FRI: { u32 f = cell_new(K_FRI, 0, 0); return P(f, 0); }
    case T_FAD: { u32 f = cell_new(K_FAD, 3, 0); Port side = compile(t->a[0]); Port lab = compile(t->a[1]); Port x = compile(t->a[2]);
      wire(P(f, 0), side); wire(P(f, 1), lab); wire(P(f, 2), x); return P(f, 3); }
    case T_FAC: { u32 f = cell_new(K_FA, 1, 1 + t->name); CELLS[f].ext2 = t->affine; Port x = compile(t->a[0]); wire(P(f, 0), x); return P(f, 1); }
    case T_FAN: { u32 f = cell_new(K_FA, 1, t->name); CELLS[f].ext2 = t->affine; Port x = compile(t->a[0]); wire(P(f, 0), x); return P(f, 1); }
    case T_COL: { u32 l = cell_new(K_LIFT, 1, 0); u32 c = cell_new(K_COL, 1, 0); Port x = compile(t->a[0]); wire(P(l, 0), x); wire(P(l, 1), P(c, 0)); return P(c, 1); }
    case T_COLQ: { u32 l = cell_new(K_LABELS, 1, 0); Port x = compile(t->a[0]); wire(P(l, 0), x); return P(l, 1); }
    case T_EQL: { u32 e = cell_new(K_EQL, 2, 0); Port a = compile(t->a[0]); Port b = compile(t->a[1]); wire(P(e, 0), a); wire(P(e, 1), b); return P(e, 2); }
    default: fprintf(stderr, "hyper: compile tag %d\n", t->tag); exit(1);
  }
}

/* ---------- the rules (5.5): each takes an active pair (a, b), consumes both cells, and builds a net on their
   auxiliary wires. aux(c, i) is the port wired to c's i-th auxiliary port. ---------- */
#define aux(c, i) (CELLS[c].p[i])
static u32 CN_NIL, CN_CONS, CN_T, CN_F, CN_TUP;
static u8 LAST_A = 0, LAST_B = 0;
static void dump_cell(u32 c) {
  fprintf(stderr, "  cell %u %s ext=%u ari=%u:", c, KIND_NAME[CELLS[c].kind], CELLS[c].ext, CELLS[c].ari);
  for (u32 i = 0; i <= CELLS[c].ari; i++) { Port q = CELLS[c].p[i]; if (q == NIL) fprintf(stderr, " [%u]=free", i); else fprintf(stderr, " [%u]=%u.%u(%s)", i, PC(q), PS(q), KIND_NAME[CELLS[PC(q)].kind]); }
  fprintf(stderr, "\n");
}
static void fail_pair(u32 a, u32 b, const char *msg) {
  fprintf(stderr, "hyper: %s (after %llu steps, last rule %s - %s, %llu live cells)\n", msg, (unsigned long long)STEPS, KIND_NAME[LAST_A], KIND_NAME[LAST_B], (unsigned long long)LIVE); dump_cell(a); dump_cell(b);
  for (u32 i = 1; i <= CELLS[a].ari; i++) if (CELLS[a].p[i] != NIL) dump_cell(PC(CELLS[a].p[i]));
  for (u32 i = 1; i <= CELLS[b].ari; i++) if (CELLS[b].p[i] != NIL) dump_cell(PC(CELLS[b].p[i]));
  exit(1);
}
static int TRACE = 0;
static void check_net(const char *when) {
  for (u32 c = 0; c < NCELLS; c++) if (CELLS[c].kind != K_FREE) for (u32 i = 0; i <= CELLS[c].ari; i++) {
    Port q = CELLS[c].p[i]; if (q == NIL) continue;
    if (PC(q) >= NCELLS || CELLS[PC(q)].kind == K_FREE || CELLS[PC(q)].p[PS(q)] != P(c, i)) { fprintf(stderr, "hyper: inconsistent wire %s: ", when); dump_cell(c); if (PC(q) < NCELLS) dump_cell(PC(q)); exit(1); }
  }
}
static void tick(u32 a, u32 b) { STEPS++; RULES[CELLS[a].kind][CELLS[b].kind]++; LAST_A = CELLS[a].kind; LAST_B = CELLS[b].kind; if (TRACE) { fprintf(stderr, "step %llu: %s(%u) - %s(%u)\n", (unsigned long long)STEPS, KIND_NAME[CELLS[a].kind], a, KIND_NAME[CELLS[b].kind], b); dump_cell(a); dump_cell(b); } }
/* the two cells of the pair are consumed; the connections a rule makes are links between wire ends, resolved
   together when the rule is done (an auxiliary wire may run back into the pair: then the two links it joins are
   one wire) */
static int CHECK = 0;
static u32 CONS_A, CONS_B; static int KEEP = 0;
static void link(Port a, Port b) { if (NLINKS == LCAP) { LCAP = LCAP ? LCAP * 2 : 1024; LINKS = realloc(LINKS, LCAP * sizeof(*LINKS)); } LINKS[NLINKS][0] = a; LINKS[NLINKS][1] = b; NLINKS++; }
static int in_pair(Port p) { return p != NIL && (PC(p) == CONS_A || PC(p) == CONS_B); }
static u32 *UF; static u32 NUF, UFCAP = 0;
static u32 uf_find(u32 x) { while (UF[x] != x) x = UF[x] = UF[UF[x]]; return x; }
static Port *NODE;
static u32 node_of(Port p) {                      /* an internal wire is one node for both its ends; a free end is its own */
  if (in_pair(p)) { Port q = CELLS[PC(p)].p[PS(p)]; if (in_pair(q) && q < p) p = q; }
  if (p != NIL) for (u32 i = 0; i < NUF; i++) if (NODE[i] == p) return i;
  if (NUF == UFCAP) { UFCAP = UFCAP ? UFCAP * 2 : 2048; UF = realloc(UF, UFCAP * sizeof(u32)); NODE = realloc(NODE, UFCAP * sizeof(Port)); }
  NODE[NUF] = p; UF[NUF] = NUF; return NUF++;
}
static void commit(void) {
  NUF = 0;
  if (CHECK) {                                      /* every external end of the pair must be mentioned by a link */
    u32 cs[2] = { CONS_A, CONS_B };
    for (u32 k = 0; k < 2; k++) for (u32 i = 1; i <= CELLS[cs[k]].ari; i++) {
      Port q = CELLS[cs[k]].p[i]; if (q == NIL || in_pair(q)) continue;
      int seen = 0; for (u32 j = 0; j < NLINKS && !seen; j++) seen = (LINKS[j][0] == q || LINKS[j][1] == q);
      if (!seen) { fprintf(stderr, "hyper: an auxiliary wire dropped by %s - %s (port %u of cell %u)\n", KIND_NAME[CELLS[CONS_A].kind], KIND_NAME[CELLS[CONS_B].kind], i, cs[k]); dump_cell(CONS_A); dump_cell(CONS_B); exit(1); }
    }
  }
  for (u32 i = 0; i < NLINKS; i++) { u32 x = node_of(LINKS[i][0]), y = node_of(LINKS[i][1]); UF[uf_find(x)] = uf_find(y); }
  /* every internal wire also joins its two ends (already one node); now each component has at most two external ends */
  for (u32 r = 0; r < NUF; r++) {
    if (uf_find(r) != r) continue;
    Port ends[4]; u32 n = 0;
    for (u32 i = 0; i < NUF; i++) if (uf_find(i) == r && !in_pair(NODE[i])) { if (n < 4) ends[n] = NODE[i]; n++; }
    if (n == 2) wire(ends[0], ends[1]);
    else if (n == 1) { if (ends[0] != NIL) { fprintf(stderr, "hyper: a wire left with one end after %s - %s\n", KIND_NAME[CELLS[CONS_A].kind], KIND_NAME[CELLS[CONS_B].kind]); dump_cell(CONS_A); dump_cell(CONS_B); exit(1); } }
    else if (n > 2) { fprintf(stderr, "hyper: a wire with %u ends after %s - %s\n", n, KIND_NAME[CELLS[CONS_A].kind], KIND_NAME[CELLS[CONS_B].kind]); dump_cell(CONS_A); dump_cell(CONS_B); exit(1); }
  }
  NLINKS = 0; cell_free(CONS_A); cell_free(CONS_B);
}
static u32 mk_era(Port to) { u32 e = cell_new(K_ERA, 0, 0); link(P(e, 0), to); return e; }
static u32 mk_ctr0(u32 name, Port to) { u32 c = cell_new(K_CTR, 0, name); link(P(c, 0), to); return c; }
static u32 mk_dup(u32 lab, Port in, Port o0, Port o1) { u32 d = cell_new(K_DUP, 2, lab); link(P(d, 0), in); link(P(d, 1), o0); link(P(d, 2), o1); return d; }
static u32 mk_sup(u32 lab, Port out, Port a, Port b) { u32 s = cell_new(K_SUP, 2, lab); link(P(s, 0), out); link(P(s, 1), a); link(P(s, 2), b); return s; }
/* which auxiliary ports of a cell are its outputs (the rest are inputs): used when a superposition meets a
   cell's principal port and the cell is taken on both sides */
static u32 out_mask(u32 c) {
  switch (CELLS[c].kind) {
    case K_APP: return 1u << 2; case K_MAT: return 1u << 1; case K_EQL: return 1u << 2; case K_EQLC: return 1u << CELLS[c].ari;
    case K_EQLN: return 1u << 1; case K_AND: return 1u << 2; case K_APPEND: return 1u << 2; case K_COL: return 1u << 1;
    case K_FA: return 1u << 1; case K_FAD: return 1u << 3; case K_FDL: return 1u << 2; case K_LIFT: return 1u << 1; case K_LIFTC: return 1u << CELLS[c].ari;
    case K_DSU: return 1u << 1; case K_DDU: return (1u << 2) | (1u << 3); case K_NF: return 1u << 1; case K_LABELS: return 1u << 1;
    default: return 0;
  }
}
/* a superposition &L{x, y} on the principal port of a cell c (not a duplicator): c is taken on both sides */
static void rule_sup_commute(u32 s, u32 c) {
  tick(s, c);
  u32 lab = CELLS[s].ext; u8 kind = CELLS[c].kind, ari = CELLS[c].ari; u32 ext = CELLS[c].ext, ext2 = CELLS[c].ext2;
  Port x = aux(s, 1), y = aux(s, 2);
  u32 c0 = cell_new(kind, ari, ext), c1 = cell_new(kind, ari, ext); CELLS[c0].ext2 = ext2; CELLS[c1].ext2 = ext2;
  u32 outs = out_mask(c);
  for (u32 i = 1; i <= ari; i++) {
    Port q = aux(c, i);
    if (outs & (1u << i)) mk_sup(lab, q, P(c0, i), P(c1, i)); else mk_dup(lab, q, P(c0, i), P(c1, i));
  }
  link(P(c0, 0), x); link(P(c1, 0), y);
}
/* a duplicator on a value cell c: two copies of c, its auxiliary wires duplicated */
static void rule_dup_copy(u32 d, u32 c) {
  tick(d, c);
  u32 lab = CELLS[d].ext; u8 kind = CELLS[c].kind, ari = CELLS[c].ari; u32 ext = CELLS[c].ext, ext2 = CELLS[c].ext2;
  Port o0 = aux(d, 1), o1 = aux(d, 2);
  u32 c0 = cell_new(kind, ari, ext), c1 = cell_new(kind, ari, ext); CELLS[c0].ext2 = ext2; CELLS[c1].ext2 = ext2;
  for (u32 i = 1; i <= ari; i++) mk_dup(lab, aux(c, i), P(c0, i), P(c1, i));
  link(P(c0, 0), o0); link(P(c1, 0), o1);
}
static void rule_erase(u32 e, u32 c) {
  tick(e, c);
  u8 k = CELLS[c].kind;
  if (k == K_CTR || k == K_LAM || k == K_SUP || k == K_NUM || k == K_MATV) MERGES++;   /* a value discarded */
  for (u32 i = 1; i <= CELLS[c].ari; i++) mk_era(aux(c, i));
}
static Port instantiate(u32 name);
static void rule_unfold(u32 r, u32 c) {
  tick(r, c); UNFOLDS++;
  u32 name = CELLS[r].ext; cell_free(r); KEEP = 1;
  Port root = instantiate(name);
  wire(root, P(c, 0));
}
/* a closure cell c (LAM or MATV) applied: the term's free variables are the cell's auxiliary wires */
static void push_fv(Term *t) { for (u32 i = 0; i < t->nfv; i++) env_push(t->fv[i]); }
static void pop_fv(Term *t, u32 c, u32 first) { for (u32 i = t->nfv; i > 0; i--) env_pop_wire(aux(c, first + i - 1), 1); }
static void rule_lam_app(u32 l, u32 ap) {
  tick(l, ap);
  Term *t = CLOS_TERMS[CELLS[l].ext]; Port arg = aux(ap, 1), out = aux(ap, 2);
  push_fv(t); env_push(t->name);
  Port root = compile(t->a[0]);
  link(root, out);
  env_pop_wire(arg, 1); pop_fv(t, l, 1);
}
/* case analysis: MAT(principal = scrutinee; aux1 = ret; aux 2.. = the closure's free variables) meets a constructor */
static void rule_mat_ctr(u32 m, u32 c) {
  tick(m, c);
  Term *mt = CLOS_TERMS[CELLS[m].ext]; Port ret = aux(m, 1);
  int sel = -1; u32 ncases = mt->n - (mt->has_default ? 1 : 0);
  for (u32 i = 0; i < ncases; i++) if (mt->names[i] == CELLS[c].ext) { sel = (int)i; break; }
  if (sel < 0 && !mt->has_default) { fprintf(stderr, "hyper: no case for #%s in a match over", NAMES[CELLS[c].ext]); for (u32 i = 0; i < ncases; i++) fprintf(stderr, " #%s", NAMES[mt->names[i]]); fprintf(stderr, " (after %llu steps)\n", (unsigned long long)STEPS); dump_cell(m); dump_cell(c); exit(1); }
  MERGES += (mt->n > 1);                             /* the branches not taken are never built: the choice is the merge */
  Term *branch = mt->a[sel < 0 ? mt->n - 1 : (u32)sel];
  push_fv(mt);
  Port f = compile(branch);
  if (sel < 0) {                                    /* the default takes the constructor itself */
    u32 d = cell_new(K_CTR, CELLS[c].ari, CELLS[c].ext); for (u32 i = 1; i <= CELLS[c].ari; i++) link(P(d, i), aux(c, i));
    u32 ap = cell_new(K_APP, 2, 0); link(P(ap, 0), f); wire(P(ap, 1), P(d, 0)); link(P(ap, 2), ret);
  } else {
    for (u32 i = 1; i <= CELLS[c].ari; i++) { u32 ap = cell_new(K_APP, 2, 0); link(P(ap, 0), f); link(P(ap, 1), aux(c, i)); f = P(ap, 2); }
    link(f, ret);
  }
  pop_fv(mt, m, 2);
}
/* a copy of a cell's shell: same kind, arity and extension, its auxiliary wires linked to the given cell's */
static u32 shell(u32 c) {
  u32 d = cell_new(CELLS[c].kind, CELLS[c].ari, CELLS[c].ext); CELLS[d].ext2 = CELLS[c].ext2;
  for (u32 i = 1; i <= CELLS[c].ari; i++) link(P(d, i), aux(c, i));
  return d;
}
/* a face on a closure: the closure of the faced body */
static Term *faced_term(Term *t, u32 lab, u8 side) {
  Term *f = tm(T_FAN); f->name = lab; f->affine = side; tm_push(f, t); return f;
}
static u32 faced_closure(u32 c, u32 lab, u8 side) {
  Term *t = CLOS_TERMS[CELLS[c].ext]; Term *nt;
  if (t->tag == T_LAM) { nt = tm(T_LAM); nt->name = t->name; nt->affine = t->affine; tm_push(nt, faced_term(t->a[0], lab, side)); }
  else { nt = tm(T_MATV); nt->has_default = t->has_default; nt->names = t->names; for (u32 i = 0; i < t->n; i++) tm_push(nt, faced_term(t->a[i], lab, side)); }
  term_fv(nt);
  u32 d = cell_new(CELLS[c].kind, CELLS[c].ari, clos_id(nt));
  for (u32 i = 1; i <= CELLS[c].ari; i++) link(P(d, i), aux(c, i));   /* the free variables are the same, in the same order */
  return d;
}
static void freshen(u32 f) {       /* ? → the next choice coordinate, ?? → the next index coordinate: one step */
  u8 idx = CELLS[f].kind == K_FRI; STEPS++; RULES[CELLS[f].kind][K_NUM]++;
  CELLS[f].kind = K_NUM; CELLS[f].ext = idx ? LAB_INDEX++ : LAB_CHOICE++;
  if (CELLS[f].ext >= (idx ? (1u << 20) : 0xFFFFFFu)) { fprintf(stderr, "hyper: coordinates exhausted\n"); exit(2); }
}
/* lifting (the collapsed normal form): LIFT(principal = value; aux1 = out) brings the first choice coordinate of
   the value to its top. A coordinate inside a node rises through the node, the node's other fields taken on the
   side it names (its faces), so a label occurring twice is one coordinate (the correlation of the collapse).
   LIFTC(kind, ext, n, k; principal = field k lifted; aux 1..n = the fields, aux n+1 = out) walks the fields. */
static u32 mk_fa(u32 lab, u8 side, Port in, Port out) { u32 f = cell_new(K_FA, 1, lab); CELLS[f].ext2 = side; link(P(f, 0), in); link(P(f, 1), out); return f; }
static u32 mk_liftc(u8 kind, u32 ext, u32 n, u32 k) { u32 lc = cell_new(K_LIFTC, (u8)(n + 1), ext); CELLS[lc].ext2 = n | (k << 8) | ((u32)kind << 16); return lc; }
static void rule_lift(u32 lf, u32 c) {
  tick(lf, c);
  Port out = aux(lf, 1); u8 k = CELLS[c].kind;
  if (k == K_SUP && is_choice(CELLS[c].ext)) {   /* a choice at the top: its sides faced, lifted on */
    u32 lab = CELLS[c].ext; u32 s = cell_new(K_SUP, 2, lab); link(P(s, 0), out);
    for (u8 side = 0; side < 2; side++) { u32 l2 = cell_new(K_LIFT, 1, 0); mk_fa(lab, side, aux(c, side + 1), P(l2, 0)); link(P(l2, 1), P(s, side + 1)); }
    return;
  }
  if ((k == K_CTR && CELLS[c].ari > 0) || k == K_SUP) {   /* a node (an index coordinate is a node): its fields lifted in turn */
    u32 n = CELLS[c].ari; u32 lc = mk_liftc(k, CELLS[c].ext, n, 1);
    u32 l2 = cell_new(K_LIFT, 1, 0); link(P(l2, 0), aux(c, 1)); link(P(l2, 1), P(lc, 0));
    for (u32 i = 2; i <= n; i++) link(P(lc, i), aux(c, i));
    link(P(lc, n + 1), out);
    return;
  }
  u32 d = shell(c); link(P(d, 0), out);              /* a leaf: a nullary constructor, a number, a closure, an erasure */
}
static void rule_liftc(u32 lc, u32 c) {
  tick(lc, c);
  u32 n = CELLS[lc].ext2 & 255, k = (CELLS[lc].ext2 >> 8) & 255; u8 kind = (u8)(CELLS[lc].ext2 >> 16); u32 ext = CELLS[lc].ext;
  Port out = aux(lc, n + 1);
  if (CELLS[c].kind == K_SUP && is_choice(CELLS[c].ext)) {   /* field k is a choice: it rises, the other fields follow its side */
    u32 lab = CELLS[c].ext; u32 s = cell_new(K_SUP, 2, lab); link(P(s, 0), out);
    u32 lc0 = mk_liftc(kind, ext, n, k), lc1 = mk_liftc(kind, ext, n, k);
    u32 dl = LAB_CHOICE++;
    for (u32 i = 1; i <= n; i++) {
      if (i == k) continue;
      u32 d = cell_new(K_DUP, 2, dl); link(P(d, 0), aux(lc, i));
      if (i < k) { wire(P(d, 1), P(lc0, i)); wire(P(d, 2), P(lc1, i)); }                /* a field already a leaf */
      else { mk_fa(lab, 0, P(d, 1), P(lc0, i)); mk_fa(lab, 1, P(d, 2), P(lc1, i)); }    /* a pending field: its face */
    }
    for (u8 side = 0; side < 2; side++) { u32 l2 = cell_new(K_LIFT, 1, 0); mk_fa(lab, side, aux(c, side + 1), P(l2, 0)); wire(P(l2, 1), P(side ? lc1 : lc0, 0)); }
    link(P(lc0, n + 1), P(s, 1)); link(P(lc1, n + 1), P(s, 2));
    return;
  }
  if (CELLS[c].kind == K_ERA) { for (u32 i = 1; i <= n; i++) if (i != k) mk_era(aux(lc, i)); mk_era(out); return; }
  /* field k is a leaf */
  u32 leaf = shell(c);
  if (k < n) {
    u32 lc2 = mk_liftc(kind, ext, n, k + 1);
    for (u32 i = 1; i <= n; i++) { if (i == k) wire(P(lc2, i), P(leaf, 0)); else if (i == k + 1) continue; else link(P(lc2, i), aux(lc, i)); }
    u32 l2 = cell_new(K_LIFT, 1, 0); link(P(l2, 0), aux(lc, k + 1)); wire(P(l2, 1), P(lc2, 0));
    link(P(lc2, n + 1), out);
    return;
  }
  u32 d = cell_new(kind, (u8)n, ext); link(P(d, 0), out);
  for (u32 i = 1; i <= n; i++) { if (i == k) wire(P(d, i), P(leaf, 0)); else link(P(d, i), aux(lc, i)); }
}
static void rule_append_ctr(u32 ap, u32 c) {
  tick(ap, c);
  Port second = aux(ap, 1), out = aux(ap, 2);
  if (CELLS[c].ext == CN_NIL) { link(second, out); return; }
  Port h = aux(c, 1), t = aux(c, 2);
  u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 0), out); link(P(cons, 1), h);
  u32 ap2 = cell_new(K_APPEND, 2, 0); link(P(ap2, 0), t); link(P(ap2, 1), second); link(P(ap2, 2), P(cons, 2));
}
/* a face |s(L) on a value */
static void rule_fa(u32 fa, u32 c) {
  tick(fa, c);
  u32 lab = CELLS[fa].ext; u8 side = (u8)CELLS[fa].ext2; Port out = aux(fa, 1); u8 k = CELLS[c].kind;
  if (k == K_SUP) {
    if (CELLS[c].ext == lab) {                      /* the side at every depth: the face continues into the side it keeps */
      u32 f = cell_new(K_FA, 1, lab); CELLS[f].ext2 = side; link(P(f, 0), aux(c, side ? 2 : 1)); link(P(f, 1), out); mk_era(aux(c, side ? 1 : 2)); MERGES++; }
    else { u32 f0 = cell_new(K_FA, 1, lab), f1 = cell_new(K_FA, 1, lab); CELLS[f0].ext2 = side; CELLS[f1].ext2 = side;
      link(P(f0, 0), aux(c, 1)); link(P(f1, 0), aux(c, 2)); mk_sup(CELLS[c].ext, out, P(f0, 1), P(f1, 1)); }
  } else if (k == K_CTR) {
    u32 d = cell_new(k, CELLS[c].ari, CELLS[c].ext); CELLS[d].ext2 = CELLS[c].ext2; link(P(d, 0), out);
    for (u32 i = 1; i <= CELLS[c].ari; i++) { u32 f = cell_new(K_FA, 1, lab); CELLS[f].ext2 = side; link(P(f, 0), aux(c, i)); link(P(f, 1), P(d, i)); }
  } else if (k == K_LAM || k == K_MATV) {
    u32 d = faced_closure(c, lab, side); link(P(d, 0), out);
  } else if (k == K_NUM || k == K_REF || k == K_ERA) {
    u32 d = cell_new(k, 0, CELLS[c].ext); link(P(d, 0), out);
  } else { fprintf(stderr, "hyper: a face on %s\n", KIND_NAME[k]); exit(1); }
}
/* NF(principal = value; aux1 = out): the demand for the value's normal form, pushed through it */
static void rule_nf(u32 nf, u32 c) {
  tick(nf, c);
  Port out = aux(nf, 1); u8 k = CELLS[c].kind;
  if (k == K_NUM) { u32 d = cell_new(K_NUM, 0, CELLS[c].ext); link(P(d, 0), out); return; }
  if (k == K_MATV) { u32 d = shell(c); link(P(d, 0), out); return; }
  if (k == K_LAM) {                                 /* the body under the binder, for reading: the variable a free end */
    Term *t = CLOS_TERMS[CELLS[c].ext];
    u32 v = cell_new(K_ROOT, 1, 0), lv = cell_new(K_LAMV, 2, 0), f = cell_new(K_NF, 1, 0);
    push_fv(t); env_push(t->name); Port root = compile(t->a[0]);
    link(P(f, 0), root); env_pop_wire(P(v, 1), 0); pop_fv(t, c, 1);
    wire(P(f, 1), P(lv, 2)); wire(P(lv, 1), P(v, 0)); link(P(lv, 0), out); return;
  }
  u32 d = cell_new(k, CELLS[c].ari, CELLS[c].ext); CELLS[d].ext2 = CELLS[c].ext2; link(P(d, 0), out);
  for (u32 i = 1; i <= CELLS[c].ari; i++) { u32 f = cell_new(K_NF, 1, 0); link(P(f, 0), aux(c, i)); link(P(f, 1), P(d, i)); }
}
/* LABELS(principal = value; aux1 = out): the index coordinates occurring in a value, as a list of their numbers */
static void rule_labels(u32 lb, u32 c) {
  tick(lb, c);
  Port out = aux(lb, 1); u8 k = CELLS[c].kind;
  if (k == K_SUP && !is_choice(CELLS[c].ext)) {
    u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 0), out); u32 n = cell_new(K_NUM, 0, CELLS[c].ext); wire(P(cons, 1), P(n, 0));
    u32 ap = cell_new(K_APPEND, 2, 0); wire(P(ap, 2), P(cons, 2));
    u32 l0 = cell_new(K_LABELS, 1, 0), l1 = cell_new(K_LABELS, 1, 0);
    link(P(l0, 0), aux(c, 1)); wire(P(l0, 1), P(ap, 0)); link(P(l1, 0), aux(c, 2)); wire(P(l1, 1), P(ap, 1));
    return;
  }
  if ((k == K_CTR && CELLS[c].ari > 0) || k == K_SUP) {
    Port acc = out;
    for (u32 i = 1; i <= CELLS[c].ari; i++) {
      u32 li = cell_new(K_LABELS, 1, 0); link(P(li, 0), aux(c, i));
      if (i == CELLS[c].ari) link(P(li, 1), acc);
      else { u32 ap = cell_new(K_APPEND, 2, 0); wire(P(ap, 0), P(li, 1)); link(P(ap, 2), acc); acc = P(ap, 1); }
    }
    return;
  }
  for (u32 i = 1; i <= CELLS[c].ari; i++) mk_era(aux(c, i));   /* a leaf (a closure's free variables are not read) */
  mk_ctr0(CN_NIL, out);
}
static void rule_eqlc_ctr(u32 e, u32 c) {
  tick(e, c);
  u32 n = CELLS[e].ari - 1; Port out = aux(e, n + 1);
  if (CELLS[e].ext != CELLS[c].ext || n != CELLS[c].ari) {
    for (u32 i = 1; i <= n; i++) mk_era(aux(e, i)); for (u32 i = 1; i <= CELLS[c].ari; i++) mk_era(aux(c, i));
    MERGES++; mk_ctr0(CN_F, out); return;
  }
  Port acc = out;
  for (u32 i = 1; i <= n; i++) {
    u32 q = cell_new(K_EQL, 2, 0); link(P(q, 0), aux(e, i)); link(P(q, 1), aux(c, i));
    if (i == n) link(P(q, 2), acc);
    else { u32 an = cell_new(K_AND, 2, 0); link(P(an, 0), P(q, 2)); link(P(an, 2), acc); acc = P(an, 1); }
  }
  if (n == 0) mk_ctr0(CN_T, out);
}
static void step_(u32 a, u32 b);
static void step(u32 a, u32 b) { CONS_A = a; CONS_B = b; NLINKS = 0; KEEP = 0; step_(a, b); if (!KEEP) commit(); else NLINKS = 0; }
static void step_(u32 a, u32 b) {
  u8 ka = CELLS[a].kind, kb = CELLS[b].kind;
  if (ka > kb) { u32 t = a; a = b; b = t; ka = CELLS[a].kind; kb = CELLS[b].kind; }
  /* fresh coordinates become numbers first; a reference unfolds unless it is erased or copied */
  if (kb == K_FRS || kb == K_FRI) { if (ka == K_ERA) { tick(a, b); return; } freshen(b); KEEP = 1; active_push(a); return; }
  if (ka == K_FRS || ka == K_FRI) { freshen(a); KEEP = 1; active_push(a); return; }
  if (ka == K_REF && kb != K_ERA && kb != K_DUP) { rule_unfold(a, b); return; }
  if (kb == K_REF && ka != K_ERA && ka != K_DUP) { rule_unfold(b, a); return; }
  if (kb == K_NF && (ka == K_CTR || ka == K_SUP || ka == K_LAM || ka == K_NUM || ka == K_MATV)) { rule_nf(b, a); return; }
  if (kb == K_LIFT && (ka == K_CTR || ka == K_SUP || ka == K_LAM || ka == K_NUM || ka == K_MATV || ka == K_ERA)) { rule_lift(b, a); return; }
  if (kb == K_LIFTC && (ka == K_CTR || ka == K_SUP || ka == K_LAM || ka == K_NUM || ka == K_MATV || ka == K_ERA)) { rule_liftc(b, a); return; }
  if (kb == K_LABELS && (ka == K_CTR || ka == K_SUP || ka == K_LAM || ka == K_NUM || ka == K_MATV || ka == K_ERA)) { rule_labels(b, a); return; }
  if (ka == K_SUP && kb == K_COL) {                 /* the collapse of a lifted value: a choice at the top gives both sides, in order */
    tick(a, b); Port x = aux(a, 1), y = aux(a, 2), out = aux(b, 1);
    u32 ap = cell_new(K_APPEND, 2, 0); link(P(ap, 2), out); u32 c0 = cell_new(K_COL, 1, 0), c1 = cell_new(K_COL, 1, 0);
    link(P(c0, 0), x); wire(P(c0, 1), P(ap, 0)); link(P(c1, 0), y); wire(P(c1, 1), P(ap, 1)); return;
  }
  switch (ka) {
    case K_ERA:
      if (kb == K_COL) { tick(a, b); mk_ctr0(CN_NIL, aux(b, 1)); return; }
      if (kb == K_NF) { tick(a, b); mk_era(aux(b, 1)); return; }
      rule_erase(a, b); return;
    case K_LAM:
      if (kb == K_APP) { rule_lam_app(a, b); return; }
      if (kb == K_DUP) { rule_dup_copy(b, a); return; }
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_COL) { tick(a, b); u32 l = shell(a); u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 1), P(l, 0)); mk_ctr0(CN_NIL, P(cons, 2)); link(P(cons, 0), aux(b, 1)); return; }
      break;
    case K_APP:
      if (kb == K_SUP) { rule_sup_commute(b, a); return; }
      if (kb == K_MATV) { tick(a, b); u32 nb = CELLS[b].ari; u32 m = cell_new(K_MAT, nb + 1, CELLS[b].ext); link(P(m, 1), aux(a, 2)); for (u32 i = 1; i <= nb; i++) link(P(m, i + 1), aux(b, i)); link(P(m, 0), aux(a, 1)); return; }
      if (kb == K_CTR) fail_pair(a, b, "cannot apply a constructor");
      if (kb == K_NUM) { fprintf(stderr, "hyper: cannot apply a number\n"); exit(1); }
      break;
    case K_SUP:
      if (kb == K_DUP) {
        tick(a, b);
        if (CELLS[a].ext == CELLS[b].ext) { Port x = aux(a, 1), y = aux(a, 2), o0 = aux(b, 1), o1 = aux(b, 2); link(x, o0); link(y, o1); return; }
        u32 ls = CELLS[a].ext, ld = CELLS[b].ext; Port x = aux(a, 1), y = aux(a, 2), o0 = aux(b, 1), o1 = aux(b, 2);
        u32 s0 = cell_new(K_SUP, 2, ls), s1 = cell_new(K_SUP, 2, ls);
        mk_dup(ld, x, P(s0, 1), P(s1, 1)); mk_dup(ld, y, P(s0, 2), P(s1, 2)); link(P(s0, 0), o0); link(P(s1, 0), o1); return;
      }
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_DSU || kb == K_DDU) { fprintf(stderr, "hyper: a superposed coordinate\n"); exit(1); }
      rule_sup_commute(a, b); return;
    case K_DUP:
      if (kb == K_CTR || kb == K_MATV || kb == K_NUM || kb == K_REF) { rule_dup_copy(a, b); return; }
      break;
    case K_CTR:
      if (kb == K_MAT) { rule_mat_ctr(b, a); return; }
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_COL) { tick(a, b); u32 d = shell(a); u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 1), P(d, 0)); mk_ctr0(CN_NIL, P(cons, 2)); link(P(cons, 0), aux(b, 1)); return; }
      if (kb == K_APPEND) { rule_append_ctr(b, a); return; }
      if (kb == K_EQL) { tick(a, b); u32 n = CELLS[a].ari; u32 e = cell_new(K_EQLC, n + 1, CELLS[a].ext); for (u32 i = 1; i <= n; i++) link(P(e, i), aux(a, i)); link(P(e, n + 1), aux(b, 2)); Port o = aux(b, 1); link(P(e, 0), o); return; }
      if (kb == K_EQLC) { rule_eqlc_ctr(b, a); return; }
      if (kb == K_AND) { tick(a, b); Port y = aux(b, 1), out = aux(b, 2); u32 nm = CELLS[a].ext;
        if (nm == CN_T) link(y, out); else { mk_era(y); MERGES++; mk_ctr0(CN_F, out); } return; }
      if (kb == K_FAD) { tick(a, b); u32 nm = CELLS[a].ext; if (nm != CN_T && nm != CN_F) { fprintf(stderr, "hyper: a face's side is not a bit\n"); exit(1); }
        u32 f = cell_new(K_FDL, 2, 0); CELLS[f].ext2 = nm == CN_T; link(P(f, 1), aux(b, 2)); link(P(f, 2), aux(b, 3)); Port co = aux(b, 1); link(P(f, 0), co); return; }
      if (kb == K_EQLN) { tick(a, b); for (u32 i = 1; i <= CELLS[a].ari; i++) mk_era(aux(a, i)); MERGES++; Port o = aux(b, 1); mk_ctr0(CN_F, o); return; }
      break;
    case K_NUM:
      if (kb == K_DSU) { tick(a, b); u32 s = cell_new(K_SUP, 2, CELLS[a].ext); link(P(s, 1), aux(b, 2)); link(P(s, 2), aux(b, 3)); Port o = aux(b, 1); link(P(s, 0), o); return; }
      if (kb == K_DDU) { tick(a, b); u32 d = cell_new(K_DUP, 2, CELLS[a].ext); link(P(d, 1), aux(b, 2)); link(P(d, 2), aux(b, 3)); Port in = aux(b, 1); link(P(d, 0), in); return; }
      if (kb == K_FDL) { tick(a, b); u32 f = cell_new(K_FA, 1, CELLS[a].ext); CELLS[f].ext2 = CELLS[b].ext2; link(P(f, 1), aux(b, 2)); Port in = aux(b, 1); link(P(f, 0), in); return; }
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_COL) { tick(a, b); u32 n = cell_new(K_NUM, 0, CELLS[a].ext); u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 1), P(n, 0)); mk_ctr0(CN_NIL, P(cons, 2)); link(P(cons, 0), aux(b, 1)); return; }
      if (kb == K_EQL) { tick(a, b); u32 e = cell_new(K_EQLN, 1, CELLS[a].ext); link(P(e, 1), aux(b, 2)); Port o = aux(b, 1); link(P(e, 0), o); return; }
      if (kb == K_EQLN) { tick(a, b); u32 same = CELLS[a].ext == CELLS[b].ext; Port o = aux(b, 1); MERGES++; mk_ctr0(same ? CN_T : CN_F, o); return; }
      break;
    case K_MATV:
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_COL) { tick(a, b); u32 m = shell(a); u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 1), P(m, 0)); mk_ctr0(CN_NIL, P(cons, 2)); link(P(cons, 0), aux(b, 1)); return; }
      break;
    case K_REF:
      if (kb == K_FA) { rule_fa(b, a); return; }
      if (kb == K_COL) { tick(a, b); u32 r = cell_new(K_REF, 0, CELLS[a].ext); u32 cons = cell_new(K_CTR, 2, CN_CONS); link(P(cons, 1), P(r, 0)); mk_ctr0(CN_NIL, P(cons, 2)); link(P(cons, 0), aux(b, 1)); return; }
      break;
    default: break;
  }
  char m[128]; snprintf(m, sizeof m, "no rule for %s - %s", KIND_NAME[ka], KIND_NAME[kb]); fail_pair(a, b, m);
}

/* ---------- instantiation of a definition: its term compiled afresh (fresh coordinates per unfolding) ---------- */
static Port instantiate(u32 name) {
  if (name >= MAXDEFS || !DEFS[name]) { fprintf(stderr, "hyper: no definition @%s\n", NAMES[name]); exit(1); }
  u32 save = NENV;
  Port root = compile(DEFS[name]);
  if (NENV != save) { fprintf(stderr, "hyper: binder imbalance\n"); exit(1); }
  return root;
}

/* ---------- reduction by demand (5.25: the forced steps). A value is demanded at an input port; the cell
   producing it is driven: if it waits on its own principal port, that is demanded first; when the principal meets a
   value the pair is active and its rule fires; a reference unfolds and a fresh coordinate is named when demanded.
   A sub-net nothing demands never reduces: the branch not taken costs nothing, and a wire that is erased carries
   no work. The order among independent demands is free (5.11). ---------- */
static u64 SCHED_SEED = 0; static u64 STEP_LIMIT = 0;
static int is_value(u8 k) { return k == K_CTR || k == K_SUP || k == K_NUM || k == K_LAM || k == K_MATV || k == K_ERA; }
static void step(u32 a, u32 b);
static void erase_pending(void) {
  while (NACTIVE) {
    u32 a = ACTIVE[--NACTIVE];
    if (CELLS[a].kind == K_FREE) continue;
    Port pb = CELLS[a].p[0]; if (pb == NIL || PS(pb) != 0) continue;
    u32 b = PC(pb); if (CELLS[b].kind == K_FREE || CELLS[b].p[0] != P(a, 0)) continue;
    if (CELLS[a].kind != K_ERA && CELLS[b].kind != K_ERA) continue;
    if (CELLS[a].kind == K_ROOT || CELLS[b].kind == K_ROOT) continue;
    step(a, b);
  }
}
static void drive(Port in) {
  u32 gen_in = GEN[PC(in)];
  for (;;) {
    erase_pending();
    if (GEN[PC(in)] != gen_in) return;              /* the demanding cell was erased meanwhile: nothing to produce */
    Port q = peer(in); if (q == NIL) return;
    u32 c = PC(q); u8 k = CELLS[c].kind;
    if (PS(q) == 0) {
      if (is_value(k)) return;
      if (k == K_REF) { STEPS++; UNFOLDS++; RULES[K_REF][K_REF]++; u32 name = CELLS[c].ext; cell_free(c); Port root = instantiate(name); wire(root, in); continue; }
      if (k == K_FRS || k == K_FRI) { freshen(c); continue; }
      if (k == K_ROOT) return;
      fprintf(stderr, "hyper: a demand met the principal port of %s\n", KIND_NAME[k]); dump_cell(c); exit(1);
    }
    /* q is an output port of c, a cell waiting on its principal: demand that, then let the pair interact */
    u32 gen_c = GEN[c];
    drive(P(c, 0));
    if (GEN[c] != gen_c) continue;                  /* an erasure reached c meanwhile: in's peer has changed */
    erase_pending();
    if (GEN[c] != gen_c) continue;
    Port v = peer(P(c, 0)); if (v == NIL || PS(v) != 0) { fprintf(stderr, "hyper: a cell with no value at its principal: "); dump_cell(c); exit(1); }
    u32 vc = PC(v);
    if (CELLS[vc].kind == K_ROOT) return;
    if (STEP_LIMIT && STEPS >= STEP_LIMIT) { fprintf(stderr, "hyper: step limit; %llu live cells, %llu at the peak\n", (unsigned long long)LIVE, (unsigned long long)PEAK); exit(2); }
    step(c, vc);
    if (CHECK) check_net("after a step");
  }
}
/* the normal form: every field demanded, in any order */
static void normalize(Port in) {
  drive(in);
  Port q = peer(in); if (q == NIL || PS(q) != 0) return;
  u32 c = PC(q); u8 k = CELLS[c].kind;
  if (k == K_CTR || k == K_SUP) {
    u32 n = CELLS[c].ari; u32 order[18]; for (u32 i = 0; i < n; i++) order[i] = i + 1;
    if (SCHED_SEED) for (u32 i = n; i > 1; i--) { SCHED_SEED = SCHED_SEED * 6364136223846793005ULL + 1442695040888963407ULL; u32 j = (u32)((SCHED_SEED >> 33) % i); u32 t = order[i - 1]; order[i - 1] = order[j]; order[j] = t; }
    for (u32 i = 0; i < n; i++) normalize(P(c, order[i]));
  } else if (k == K_LAM) {                           /* the body under the binder, for reading: the variable a free end */
    Term *t = CLOS_TERMS[CELLS[c].ext];
    u32 v = cell_new(K_ROOT, 1, 0), lv = cell_new(K_LAMV, 2, 0);
    CONS_A = NIL >> 5; CONS_B = NIL >> 5; NLINKS = 0;
    push_fv(t); env_push(t->name); Port root = compile(t->a[0]);
    wire(root, P(lv, 2)); env_pop_wire(P(v, 1), 0);
    for (u32 i = t->nfv; i > 0; i--) env_pop_wire(aux(c, i), 0);
    wire(P(lv, 1), P(v, 0)); cell_free(c); wire(P(lv, 0), in);
    normalize(P(lv, 2));
  }
}
/* ---------- reading the normal form off the net: a walk, no step ---------- */
static u32 *LAMNAME; static u32 NLAMNAME = 0;
static void print_name(u32 i) { char b[8]; int n = 0; do { b[n++] = 'a' + i % 26; i /= 26; } while (i); while (n) putchar(b[--n]); }
static void print_port(Port p, u32 depth) {
  if (p == NIL) { printf("*"); return; }
  u32 c = PC(p); u32 s = PS(p);
  if (s != 0) {                                                 /* an auxiliary port: a variable or a copy of one */
    if (CELLS[c].kind == K_ROOT && s == 1) { if (!LAMNAME[c]) LAMNAME[c] = ++NLAMNAME; print_name(LAMNAME[c] - 1); return; }
    if (CELLS[c].kind == K_DUP) { if (!LAMNAME[c]) LAMNAME[c] = ++NLAMNAME; print_name(LAMNAME[c] - 1); printf(s == 1 ? "₀" : "₁"); return; }
    printf("<%s.%u>", KIND_NAME[CELLS[c].kind], s); return;
  }
  if (depth > 100000) { printf("..."); return; }
  switch (CELLS[c].kind) {
    case K_CTR: printf("#%s{", NAMES[CELLS[c].ext]); for (u32 i = 1; i <= CELLS[c].ari; i++) { if (i > 1) printf(","); print_port(CELLS[c].p[i], depth + 1); } printf("}"); return;
    case K_SUP: { u32 l = CELLS[c].ext; printf("&"); if (l >= 1u << 18) printf("%u", l); else printf("%s", NAMES[l - 1]); printf("{"); print_port(CELLS[c].p[1], depth + 1); printf(","); print_port(CELLS[c].p[2], depth + 1); printf("}"); return; }
    case K_LAMV: { u32 v = PC(CELLS[c].p[1]); if (!LAMNAME[v]) LAMNAME[v] = ++NLAMNAME; printf("λ"); print_name(LAMNAME[v] - 1); printf("."); print_port(CELLS[c].p[2], depth + 1); return; }
    case K_LAM: printf("λ{..}"); return;
    case K_NUM: printf("%u", CELLS[c].ext); return;
    case K_ERA: printf("&{}"); return;
    case K_REF: printf("@%s", NAMES[CELLS[c].ext]); return;
    case K_MATV: printf("λ{..}"); return;
    default: printf("<%s>", KIND_NAME[CELLS[c].kind]); for (u32 i = 1; i <= CELLS[c].ari; i++) { printf(i == 1 ? "(" : ","); print_port(CELLS[c].p[i], depth + 1); } if (CELLS[c].ari) printf(")"); return;
  }
}

int inet_main(int argc, char **argv) {
  const char *file = NULL; int stats = 0; int debug = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-s")) stats = 1;
    else if (!strcmp(argv[i], "-d")) debug = 1;
    else if (!strcmp(argv[i], "-t")) TRACE = 1;
    else if (!strcmp(argv[i], "-c")) CHECK = 1;
    else if (!strcmp(argv[i], "-l") && i + 1 < argc) STEP_LIMIT = strtoull(argv[++i], NULL, 10);
    else if (!strcmp(argv[i], "-R") && i + 1 < argc) SCHED_SEED = strtoull(argv[++i], NULL, 10);
    else if (!strcmp(argv[i], "net")) continue;
    else file = argv[i];
  }
  if (!file) { fprintf(stderr, "usage: hyper net file.hvm4 [-s] [-R seed] [-c] [-t] [-l steps]\n"); return 1; }
  CLOS_TERMS = malloc((1u << 22) * sizeof(Term *));
  CN_NIL = name_id("Nil", 3); CN_CONS = name_id("Cons", 4); CN_T = name_id("T", 1); CN_F = name_id("F", 1); CN_TUP = name_id("tup", 3);
  parse_file(file);
  { char pre[600]; const char *slash = strrchr(file, '/'); size_t dl = slash ? (size_t)(slash - file + 1) : 0;
    snprintf(pre, sizeof pre, "%.*sprelude.hvm4", (int)dl, file); FILE *pf = fopen(pre, "rb"); if (pf) { fclose(pf); parse_file(pre); } }
  u32 main_id = name_id("main", 4);
  u32 root = cell_new(K_ROOT, 1, 0);
  Port r = instantiate(main_id);
  wire(P(root, 1), r);
  if (CHECK) check_net("after compiling main");
  normalize(P(root, 1));
  LAMNAME = calloc(NCELLS + 1, sizeof(u32));
  print_port(CELLS[root].p[1], 0); printf("\n");
  if (debug) { fprintf(stderr, "live cells:\n"); for (u32 c = 0; c < NCELLS; c++) if (CELLS[c].kind != K_FREE) dump_cell(c); }
  if (stats) {
    fprintf(stderr, "- Steps: %llu (length)\n- Merges: %llu (effect axis, in discarded values)\n- Unfolds: %llu\n- Cells: %llu live at the end, %llu at the peak\n",
      (unsigned long long)STEPS, (unsigned long long)MERGES, (unsigned long long)UNFOLDS, (unsigned long long)LIVE, (unsigned long long)PEAK);
    fprintf(stderr, "- Rules:");
    for (u32 i = 0; i < 64; i++) for (u32 j = 0; j < 64; j++) if (RULES[i][j]) fprintf(stderr, " %s-%s:%llu", KIND_NAME[i], KIND_NAME[j], (unsigned long long)RULES[i][j]);
    fprintf(stderr, "\n");
  }
  return 0;
}

#ifdef INET_STANDALONE
int main(int argc, char **argv) { return inet_main(argc, argv); }
#endif

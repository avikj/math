#define _GNU_SOURCE
/* hyper — read.c: the reader for the kernel's own text (the identity chart, MAP.md §5.1).
 *
 *   file  := (def NAME TERM) | (def NAME : TYPE = TERM) ...
 *   term  := NAME                       a bound variable or dimension
 *          | (lam x TERM)                | (plm i TERM)            | (dim i TERM)
 *          | (app F X)                   | (sup i A B)             | (fce i 0|1 T)
 *          | (ref NAME)                  | (era)                   | (let x V BODY)
 *          | (ctr Name ARGS…)            | (num N)                 | (op2 OP A B)
 *          | i0 | i1 | (inot A) | (iand A B) | (ior A B)
 *          | (trp LINE R S X)            | (case S (Ctor (x…) BODY) … (_ () BODY)?)
 *          | (chk T X)                   | (ask Q K)
 * A dimension used by `sup`/`fce` and not bound by plm/dim is bound implicitly
 * at the definition's top: fresh per instantiation (the capture fix).
 */
#include "cell.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

static const char *src; static size_t pos, len;
static void skip(void) { for (;;) { while (pos < len && isspace((unsigned char)src[pos])) pos++;
  if (pos < len && src[pos] == ';') { while (pos < len && src[pos] != '\n') pos++; continue; } break; } }
static bool peek(char c) { skip(); return pos < len && src[pos] == c; }
static void expect(char c) { skip(); if (pos >= len || src[pos] != c) { fprintf(stderr, "hyper: expected '%c' at %zu\n", c, pos); exit(2); } pos++; }
static char *atom(void) { skip(); size_t s = pos; while (pos < len && !isspace((unsigned char)src[pos]) && src[pos] != '(' && src[pos] != ')') pos++;
  if (s == pos) { fprintf(stderr, "hyper: expected atom at %zu\n", pos); exit(2); }
  char *a = malloc(pos - s + 1); memcpy(a, src + s, pos - s); a[pos - s] = 0; return a; }

static uint32_t snode(uint8_t t, uint32_t e, uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
  static uint32_t cap; if (!CODE) { cap = 1u << 16; CODE = calloc(cap, sizeof(SNode)); }
  if (CODE_LEN >= cap) { cap *= 2; CODE = realloc(CODE, cap * sizeof(SNode)); }
  SNode *n = &CODE[CODE_LEN]; memset(n, 0, sizeof *n); n->tag = t; n->ext = e; n->a = a; n->b = b; n->c = c; n->d = d;
  return CODE_LEN++;
}

/* scope: names → levels; kind distinguishes dimensions */
typedef struct { const char *name; bool dim; } Bind;
static Bind scope[1024]; static uint32_t depth;
static const char **implicit; static uint32_t nimplicit;      /* the definition's implicit dims */

static int lookup(const char *nm, bool *dim) {
  for (int i = (int)depth - 1; i >= 0; i--) if (!strcmp(scope[i].name, nm)) { *dim = scope[i].dim; return i; }
  return -1;
}
/* a dimension name not in scope is bound implicitly at the definition top: recorded, resolved in a second pass */
static uint32_t dim_level(const char *nm) {
  bool d; int l = lookup(nm, &d);
  if (l >= 0) return (uint32_t)l;
  for (uint32_t i = 0; i < nimplicit; i++) if (!strcmp(implicit[i], nm)) return i;       /* implicit dims occupy levels 0..n-1 */
  implicit = realloc(implicit, (nimplicit + 1) * sizeof *implicit); implicit[nimplicit] = strdup(nm);
  return nimplicit++;
}

const char **BNAMES; uint32_t BNAMES_LEN;
static uint32_t bnames(char **xs, uint32_t n) {       /* record a branch's field names; returns their index */
  static uint32_t cap; if (!BNAMES) { cap = 1024; BNAMES = malloc(cap * sizeof *BNAMES); BNAMES_LEN = 1; }
  while (BNAMES_LEN + n >= cap) { cap *= 2; BNAMES = realloc(BNAMES, cap * sizeof *BNAMES); }
  uint32_t at = BNAMES_LEN; for (uint32_t i = 0; i < n; i++) BNAMES[BNAMES_LEN++] = xs[i];
  return at;
}
static uint32_t term(void);
static uint32_t bind_and_parse(const char *x, bool dim, uint8_t t) {
  scope[depth].name = x; scope[depth].dim = dim; depth++;
  uint32_t body = term(); depth--;
  uint32_t r = snode(t, 0, body, 0, 0, 0); char *xs[1] = { (char *)x }; CODE[r].num = bnames(xs, 1);   /* the written name, for presentation */
  return r;
}
static unsigned opcode(const char *s) {
  static const char *ops[]   = { "+","-","*","/","%","==","!=","<","<=",">",">=","&","|","^","<<",">>","**" };
  static const char *names[] = { "add","sub","mul","div","mod","eq","ne","lt","le","gt","ge","and","or","xor","shl","shr","pow" };
  for (unsigned i = 0; i < OP_COUNT; i++) if (!strcmp(ops[i], s) || !strcmp(names[i], s)) return i;
  fprintf(stderr, "hyper: unknown op %s\n", s); exit(2);
}
static unsigned op1code(const char *s) {
  if (!strcmp(s, "not")) return OP1_NOT; if (!strcmp(s, "neg")) return OP1_NEG; if (!strcmp(s, "tochar")) return OP1_TOCHAR;
  fprintf(stderr, "hyper: unknown op1 %s\n", s); exit(2);
}
/* a name position: a numeral is a global label (one choice name shared by every use), else a bound name */
static uint32_t label_code(const char *a) {
  for (const char *c = a; *c; c++) if (!isdigit((unsigned char)*c)) return 0;
  return snode(S_LABEL, (uint32_t)strtoul(a, 0, 10), 0, 0, 0, 0);
}
static uint32_t term(void) {
  skip();
  if (!peek('(')) {
    char *a = atom();
    if (!strcmp(a, "i0")) return snode(S_I0, 0,0,0,0,0);
    if (!strcmp(a, "i1")) return snode(S_I1, 0,0,0,0,0);
    if (isdigit((unsigned char)a[0])) { uint32_t n = snode(S_NUM, 0,0,0,0,0); CODE[n].num = strtoull(a, 0, 10); return n; }
    bool d; int l = lookup(a, &d);
    if (l < 0) { int r = book_find(a); if (r >= 0) return snode(S_REF, (uint32_t)r, 0,0,0,0);
                 fprintf(stderr, "hyper: unbound %s\n", a); exit(2); }
    return snode(d ? S_IVAR : S_VAR, (uint32_t)l, 0,0,0,0);
  }
  expect('('); char *h = atom(); uint32_t r;
  if (!strcmp(h, "lam"))  { char *x = atom(); r = bind_and_parse(x, false, S_LAM); }
  else if (!strcmp(h, "plm")) { char *x = atom(); r = bind_and_parse(x, true, S_PLM); }
  else if (!strcmp(h, "dim")) { char *x = atom(); r = bind_and_parse(x, true, S_DIM); }
  else if (!strcmp(h, "let")) { char *x = atom(); uint32_t v = term();
     scope[depth].name = x; scope[depth].dim = false; depth++; uint32_t b = term(); depth--; r = snode(S_LET, 0, v, b, 0, 0); }
  else if (!strcmp(h, "app")) { uint32_t f = term(); r = f; while (!peek(')')) { uint32_t x = term(); r = snode(S_APP, 0, r, x, 0, 0); } }
  else if (!strcmp(h, "sup")) { char *i = atom(); uint32_t lb = label_code(i); uint32_t a = term(), b = term(); r = snode(S_SUP, lb ? 0 : dim_level(i), a, b, 0, lb); }
  else if (!strcmp(h, "fce")) { char *i = atom(); uint32_t lb = label_code(i); char *s = atom(); uint32_t t = term(); r = snode(S_FCE, (uint32_t)atoi(s), lb ? 0 : dim_level(i), t, 0, lb); }
  else if (!strcmp(h, "fix")) { char *x = atom(); r = bind_and_parse(x, false, S_FIX); }
  else if (!strcmp(h, "op1")) { char *o = atom(); uint32_t a = term(); r = snode(S_OP1, op1code(o), a, 0, 0, 0); }
  else if (!strcmp(h, "pout")) { uint32_t a = term(); r = snode(S_POUT, 0, a, 0, 0, 0); }
  else if (!strcmp(h, "pap")) { uint32_t a = term(), b = term(), c2 = term(), d2 = term(); r = snode(S_PAP, 0, a, b, c2, d2); }
  else if (!strcmp(h, "reflect")) { uint32_t a = term(), b = term(); r = snode(S_REFLECT, 0, a, b, 0, 0); }
  else if (!strcmp(h, "etype")) { uint32_t a = term(), b = term(), c2 = term(), d2 = term(); r = snode(S_ETYPE, 0, a, b, c2, d2); }
  else if (!strcmp(h, "eterm")) { uint32_t a = term(), b = term(), c2 = term(); r = snode(S_ETERM, 0, a, b, c2, 0); }
  else if (!strcmp(h, "chr")) { char *n = atom(); r = snode(S_NUM, N_CHR, 0,0,0,0); CODE[r].num = strtoull(n, 0, 10); }
  else if (!strcmp(h, "i64")) { char *n = atom(); r = snode(S_NUM, N_I64, 0,0,0,0); CODE[r].num = (uint64_t)strtoll(n, 0, 10); }
  else if (!strcmp(h, "f64")) { char *n = atom(); r = snode(S_NUM, N_F64, 0,0,0,0); CODE[r].num = strtoull(n, 0, 10); }
  else if (!strcmp(h, "ref")) { char *n = atom(); int d = book_find(n); if (d < 0) { fprintf(stderr, "hyper: no def %s\n", n); exit(2); } r = snode(S_REF, (uint32_t)d, 0,0,0,0); }
  else if (!strcmp(h, "era")) r = snode(S_ERA, 0,0,0,0,0);
  else if (!strcmp(h, "num")) { char *n = atom(); r = snode(S_NUM, N_U64,0,0,0,0); CODE[r].num = strtoull(n, 0, 10); }
  else if (!strcmp(h, "op2")) { char *o = atom(); uint32_t a = term(), b = term(); r = snode(S_OP2, opcode(o), a, b, 0, 0); }
  else if (!strcmp(h, "inot")) { uint32_t a = term(); r = snode(S_INOT, 0, a, 0,0,0); }
  else if (!strcmp(h, "iand")) { uint32_t a = term(), b = term(); r = snode(S_IAND, 0, a, b, 0,0); }
  else if (!strcmp(h, "ior"))  { uint32_t a = term(), b = term(); r = snode(S_IOR, 0, a, b, 0,0); }
  else if (!strcmp(h, "ctr")) { char *n = atom(); uint32_t k[64] = {0}, ar = 0;
     while (!peek(')')) { if (ar >= 64) { fprintf(stderr, "hyper: constructor arity > 64\n"); exit(2); } k[ar++] = term(); }
     if (ar <= 4) r = snode(S_CTR, ctr_ext(ctor_intern(n, ar), ar), k[0], k[1], k[2], k[3]);
     else { static uint32_t kcap; if (!KIDS) { kcap = 4096; KIDS = malloc(kcap * sizeof(uint32_t)); }
            if (KIDS_LEN + ar >= kcap) { kcap *= 2; KIDS = realloc(KIDS, kcap * sizeof(uint32_t)); }
            r = snode(S_CTR, ctr_ext(ctor_intern(n, ar), ar), 0,0,0,0); CODE[r].kids = KIDS_LEN;
            for (uint32_t i = 0; i < ar; i++) KIDS[KIDS_LEN++] = k[i]; } }
  else if (!strcmp(h, "proj")) { uint32_t i = term(), x = term(); r = snode(S_PROJ, 0, i, x, 0, 0); }
  else if (!strcmp(h, "isub")) { char *k = atom(); uint32_t lb = label_code(k); uint32_t by = term(), T = term(); r = snode(S_ISUB, 0, lb ? 0 : dim_level(k), by, T, lb); }
  else if (!strcmp(h, "glue-base")) { uint32_t g = term(); r = snode(S_GBASE, 0, g, 0, 0, 0); }
  else if (!strcmp(h, "glue-fs"))   { uint32_t g = term(); r = snode(S_GFACES, 0, g, 0, 0, 0); }
  else if (!strcmp(h, "face-case")) { uint32_t p = term(), a = term(), b = term(), c2 = term(); r = snode(S_FCASE, 0, p, a, b, c2); }
  else if (!strcmp(h, "Glue")) { uint32_t A = term(), fs = term(); r = snode(S_GLU, 0, A, fs, 0, 0); }
  else if (!strcmp(h, "glue")) { uint32_t fs = term(), a = term(); r = snode(S_GLUE, 0, fs, a, 0, 0); }
  else if (!strcmp(h, "unglue")) { uint32_t g = term(); r = snode(S_UNGLUE, 0, g, 0, 0, 0); }
  else if (!strcmp(h, "hcm")) { uint32_t A = term(), base = term(), fs = term(); r = snode(S_HCM, 0, A, base, fs, 0); }
  else if (!strcmp(h, "trp")) { uint32_t L = term(), a = term(), b = term(), x = term(); r = snode(S_TRP, 0, L, a, b, x); }
  else if (!strcmp(h, "chk")) { uint32_t T = term(), x = term(); r = snode(S_CHK, 0, T, x, 0, 0); }
  else if (!strcmp(h, "ask")) { uint32_t q = term(), k = term(); r = snode(S_ASK, 0, q, k, 0, 0); }
  else if (!strcmp(h, "trace")) { uint32_t a = term(); r = snode(S_TRACE, 0, a, 0, 0, 0); }
  else if (!strcmp(h, "leaves")) { uint32_t a = term(); r = snode(S_LEAVES, 0, a, 0, 0, 0); }
  else if (!strcmp(h, "ctr-fields")) { uint32_t x = term(); r = snode(S_CFIELDS, 0, x, 0, 0, 0); }
  else if (!strcmp(h, "ctr-with"))   { uint32_t x = term(), l = term(); r = snode(S_CWITH, 0, x, l, 0, 0); }
  else if (!strcmp(h, "helim") || !strcmp(h, "hrec")) {       /* (helim P x (c (fs) body)…) | (hrec x (c (fs) body)…); x may be _ */
     uint32_t P = h[1] == 'e' ? term() : 0; uint32_t x = 0;
     if (peek('_')) { expect('_'); } else x = term();
     uint32_t first = 0, last = 0;
     while (!peek(')')) {
       expect('('); char *cn = atom(); uint32_t ar = 0; char *xs[32];
       if (peek('(')) { expect('('); while (!peek(')')) xs[ar++] = atom(); expect(')'); }
       uint32_t cid = ctor_intern(cn, ar);
       for (uint32_t i = 0; i < ar; i++) { scope[depth].name = xs[i]; scope[depth].dim = false; depth++; }
       uint32_t body = term(); depth -= ar; expect(')');
       uint32_t br = snode(S_BRANCH, cid, ar, body, 0, 0); CODE[br].num = bnames(xs, ar);
       if (last) CODE[last].c = br; else first = br; last = br;
     }
     r = snode(S_HELIM, 0, x, first, P, 0);
  }
  else if (!strcmp(h, "case")) {
     uint32_t s = term(); uint32_t first = 0, last = 0;
     while (!peek(')')) {
       expect('('); char *cn = atom(); uint32_t ar = 0; char *xs[32]; uint32_t cid;
       if (!strcmp(cn, "_")) { cid = 0xFFFFFF; if (peek(40)) { expect(40); expect(41); } }
       else { if (peek('(')) { expect('('); while (!peek(')')) xs[ar++] = atom(); expect(')'); } cid = ctor_intern(cn, ar); }
       for (uint32_t i = 0; i < ar; i++) { scope[depth].name = xs[i]; scope[depth].dim = false; depth++; }
       uint32_t body = term(); depth -= ar; expect(')');
       uint32_t br = snode(S_BRANCH, cid, ar, body, 0, 0); CODE[br].num = bnames(xs, ar);
       if (last) CODE[last].c = br; else first = br; last = br;
     }
     r = snode(S_CASE, 0, s, first, 0, 0);
  }
  else {   /* (f a b …) with f a bound variable or a definition: application */
    bool d; int l = lookup(h, &d); int def = l < 0 ? book_find(h) : -1;
    if (l < 0 && def < 0) { fprintf(stderr, "hyper: unknown form %s\n", h); exit(2); }
    r = l >= 0 ? snode(d ? S_IVAR : S_VAR, (uint32_t)l, 0,0,0,0) : snode(S_REF, (uint32_t)def, 0,0,0,0);
    while (!peek(')')) { uint32_t x = term(); r = snode(S_APP, 0, r, x, 0, 0); }
  }
  expect(')'); return r;
}

/* Wrap a definition body in its implicit dimension binders (levels 0..n-1). */
static void read_def(void) {
  expect('('); char *kw = atom(); if (strcmp(kw, "def")) { fprintf(stderr, "hyper: expected def\n"); exit(2); }
  char *name = atom();
  int found = book_find(name); uint32_t id = (uint32_t)found;   /* registered by the pre-scan */
  /* implicit dims are levels 0..n-1: pre-scan is avoided by parsing with a reserved gap and
     re-resolving; simpler: parse the body, then wrap in n S_DIM binders and SHIFT nothing,
     because implicit levels were allocated as 0..n-1 while explicit binders started at `depth`.
     To keep levels consistent we reserve MAX_IMPLICIT levels below explicit binders.          */
  enum { MAX_IMPLICIT = 8 };
  nimplicit = 0; depth = MAX_IMPLICIT;
  for (uint32_t i = 0; i < MAX_IMPLICIT; i++) { scope[i].name = ""; scope[i].dim = true; }
  uint32_t type = 0;
  bool unknown = false;
  if (peek(':')) { expect(':'); type = term(); if (peek(')')) unknown = true; else expect('='); }   /* a type and no body: a coordinate */
  uint32_t body = unknown ? 0 : term();
  expect(')');
  /* wrap: MAX_IMPLICIT dim binders (unused ones cost one frame each at δ); the type likewise */
  for (uint32_t i = 0; i < MAX_IMPLICIT; i++) { if (body) body = snode(S_DIM, 0, body, 0, 0, 0); if (type) type = snode(S_DIM, 0, type, 0, 0, 0); }
  BOOK[id].code = body; BOOK[id].type = type; BOOK[id].ndims = 0; BOOK[id].unknown = unknown; BOOK[id].coord = 0;
}
/* (hit T (p…) (c : TYPE)…): a higher inductive type. Each constructor's closed type, Pi over the
   parameters then its fields, ends in T or in a Path into T whose nesting is the constructor's
   dimension. The type is stored as the definition `c/type`; the endpoints are read from it. */
static uint32_t count_pis(uint32_t c, uint32_t *dim) {
  while (CODE[c].tag == S_DIM) c = CODE[c].a;
  uint32_t n = 0;
  while (CODE[c].tag == S_CTR && (CODE[c].ext >> 8) == C_PI) { n++; c = CODE[CODE[c].b].a; }
  *dim = 0;
  while (CODE[c].tag == S_CTR && (CODE[c].ext >> 8) == C_PATH) { (*dim)++; c = CODE[CODE[c].a].a; }
  return n;
}
static void read_hit(void) {
  char *T = atom(); uint32_t np = 0; bool carries = true;
  expect('('); while (!peek(')')) { char *a = atom(); if (!strcmp(a, "~")) carries = false; else np++; free(a); } expect(')');
  uint32_t hid = ctor_intern(T, np); CINFO[hid].is_hit = true; CINFO[hid].nparams = np; CINFO[hid].carries = carries;
  { char buf[256]; snprintf(buf, sizeof buf, "%s/type", T); int tid = book_find(buf);   /* the parameter telescope: Pi params. Set */
    enum { MAX_IMPLICIT = 8 };
    nimplicit = 0; depth = MAX_IMPLICIT;
    for (uint32_t i = 0; i < MAX_IMPLICIT; i++) { scope[i].name = ""; scope[i].dim = true; }
    uint32_t body;
    if (peek(':')) { expect(':'); body = term(); } else body = snode(S_CTR, ctr_ext(C_SET, 0), 0, 0, 0, 0);
    for (uint32_t i = 0; i < MAX_IMPLICIT; i++) body = snode(S_DIM, 0, body, 0, 0, 0);
    BOOK[tid].code = body; BOOK[tid].type = 0; BOOK[tid].ndims = 0; CINFO[hid].type_def = tid; }
  while (!peek(')')) {
    expect('('); char *c = atom(); expect(':');
    char buf[256]; snprintf(buf, sizeof buf, "%s/type", c); int id = book_find(buf);
    enum { MAX_IMPLICIT = 8 };
    nimplicit = 0; depth = MAX_IMPLICIT;
    for (uint32_t i = 0; i < MAX_IMPLICIT; i++) { scope[i].name = ""; scope[i].dim = true; }
    uint32_t body = term(); expect(')');
    for (uint32_t i = 0; i < MAX_IMPLICIT; i++) body = snode(S_DIM, 0, body, 0, 0, 0);
    BOOK[id].code = body; BOOK[id].type = 0; BOOK[id].ndims = 0;
    uint32_t dim, npi = count_pis(body, &dim);
    uint32_t cid = ctor_intern(c, npi - np);
    CINFO[cid].hit = hid; CINFO[cid].type_def = id; CINFO[cid].nfields = npi - np; CINFO[cid].dim = dim;
    if (getenv("HYPER_DEBUG")) fprintf(stderr, "hit %s ctor %s fields %u dim %u\n", T, c, npi - np, dim);
  }
  expect(')');
}

static void register_name(const char *name) {
  static uint32_t cap; if (!BOOK) { cap = 256; BOOK = calloc(cap, sizeof(Def)); }
  if (BOOK_LEN >= cap) { cap *= 2; BOOK = realloc(BOOK, cap * sizeof(Def)); }
  if (book_find(name) >= 0) { fprintf(stderr, "hyper: duplicate definition %s\n", name); exit(2); }
  if (getenv("HYPER_DEBUG")) fprintf(stderr, "reg %s\n", name);
  BOOK[BOOK_LEN].unknown = false; BOOK[BOOK_LEN].coord = 0;
  BOOK[BOOK_LEN++].name = name;
}
static void skip_form(void) {      /* skip one balanced form from the current '(' */
  int depth = 0;
  for (; pos < len; pos++) { if (src[pos] == ';') { while (pos < len && src[pos] != '\n') pos++; continue; }
    if (src[pos] == '(') depth++; else if (src[pos] == ')') { depth--; if (depth == 0) { pos++; return; } } }
}
static void read_source(char *buf, size_t n) {
  src = buf; len = n; pos = 0;
  /* pass 1: register every definition name, so forward references resolve */
  for (;;) { skip(); if (pos >= len) break; size_t save = pos; expect('('); char *kw = atom();
    if (!strcmp(kw, "def")) register_name(atom());
    else if (!strcmp(kw, "hit")) { char *T = atom(); expect('('); while (!peek(')')) free(atom()); expect(')');
      { char *nm = malloc(strlen(T) + 6); sprintf(nm, "%s/type", T); register_name(nm); }
      if (peek(':')) { expect(':'); skip_form(); }
      while (!peek(')')) { size_t s2 = pos; expect('('); char *c = atom(); char *nm = malloc(strlen(c) + 6); sprintf(nm, "%s/type", c);
        register_name(nm); pos = s2; skip_form(); } }
    pos = save; skip_form(); }
  /* pass 2: parse */
  pos = 0;
  for (;;) { skip(); if (pos >= len) break; size_t save = pos; expect('('); char *kw = atom();
    if (!strcmp(kw, "hit")) read_hit(); else { pos = save; read_def(); } }
}
void read_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(2); }
  fseek(f, 0, SEEK_END); size_t n = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
  char *buf = malloc(n + 1); if (fread(buf, 1, n, f) != n) { perror(path); exit(2); } buf[n] = 0; fclose(f);
  read_source(buf, n);
}
/* a question from the world (§5): one term in the kernel's text, lowered with its own bound names; returns its book id */
int read_question(const char *text) {
  static unsigned n; char name[32]; snprintf(name, sizeof name, "?%u", n++);
  size_t l = strlen(text) + strlen(name) + 16; char *buf = malloc(l);
  snprintf(buf, l, "(def %s %s)", name, text);
  read_source(buf, strlen(buf));
  return book_find(name);
}

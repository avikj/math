#define _GNU_SOURCE
/* hyper — verify.c: checking is the other projection of the same presentation (MAP.md §7).
 *
 * The term is VIEWED (static code walked with a frame of coordinates), the type is EVALUATED
 * (a cell). A coordinate is a fresh atom reflected η-long at its type (T_REFLECT); a match
 * rewrites the goal by the substitution cell at the scrutinee's atom; a face restricts by the
 * face map; conversion is on cells: weak heads agree and fields convert, η for functions,
 * lines and pairs, and two stuck eliminators with the same code convert when their frames do.
 * The rules are Bend2's Core.Check, one clause each, over the kernel's cells.                */
#include "cell.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum { V_OK = 0, V_MISMATCH, V_CANTINFER } VRes;
static VRes VERR; static Term VERR_WANT, VERR_GOT; static const char *VERR_MSG;
static uint32_t CUR_CODE;                 /* the static node under examination (for the trace) */
static int DBG_DEPTH;
static bool fail_mis(Term want, Term got) { VERR = V_MISMATCH; VERR_WANT = want; VERR_GOT = got; VERR_MSG = 0;
  if (getenv("HYPER_DEBUG")) { fprintf(stderr, "  [mismatch at static tag %u] want ", CODE[CUR_CODE].tag); print_term(want, 8); fprintf(stderr, " got "); print_term(got, 8); fprintf(stderr, "\n"); }
  return false; }
static bool fail_ci(const char *msg)     { VERR = V_CANTINFER; VERR_MSG = msg;
  if (getenv("HYPER_DEBUG")) fprintf(stderr, "  [cannot infer at static tag %u] %s\n", CODE[CUR_CODE].tag, msg ? msg : "");
  return false; }

/* ---- the context: types by level, the atom of each coordinate, active faces and rewrites ---- */
static Term CTX_TY[4096]; static Term CTX_ATOM[4096];
static uint32_t CTX_LET_CODE[4096]; static Term CTX_LET_FR[4096];   /* a substituted let: its value's code and frame (Core: the value is substituted, never inferred) */
static uint32_t C_ITV;
typedef struct { Term old, by; unsigned side; } Rewrite;   /* side 0/1: a face at a dimension; 2: old := by */
static Rewrite RW[1024]; static int NRW;
static Term apply_rw(Term T) { for (int i = 0; i < NRW; i++) T = fce_raw(RW[i].side, RW[i].old, T, RW[i].by); return T; }
static Term ctx_type(uint32_t lvl) { if (!CTX_TY[lvl]) { fail_ci("a coordinate of unknown type"); return 0; } return apply_rw(CTX_TY[lvl]); }
static Term atom(void) { Term a = generic(0); return mk(T_VAR, 0, loc(a)); }
/* bind a coordinate of type T: its slot reads the atom made η-long at T */
static Term bind_coord(Term fr, Term T) {
  Term a = atom(); Term f = frame_push(fr, node2(T_REFLECT, 0, a, T));
  CTX_TY[ext(f)] = T; CTX_ATOM[ext(f)] = a; return f;
}
static Term bind_value(Term fr, Term v, Term T) { Term f = frame_push(fr, v); CTX_TY[ext(f)] = T; CTX_ATOM[ext(f)] = 0; CTX_LET_CODE[ext(f)] = 0; return f; }
static Term bind_let(Term fr, uint32_t code, Term vfr) { Term f = frame_push(fr, inst(code, vfr)); CTX_TY[ext(f)] = 0; CTX_ATOM[ext(f)] = 0; CTX_LET_CODE[ext(f)] = code; CTX_LET_FR[ext(f)] = vfr; return f; }
static Term bind_dim(Term fr) { Term f = dim_push(fr); CTX_TY[ext(f)] = mk(T_CTR, ctr_ext(C_ITV, 0), alloc(1)); CTX_ATOM[ext(f)] = 0; return f; }
static Term var_of(Term f) { return mk(T_VAR, ext(f), loc(f)); }
static Term ivar_of(Term f) { return mk(T_IVAR, 0, loc(f)); }
static Term ctr0(uint32_t id) { return mk(T_CTR, ctr_ext(id, 0), alloc(1)); }
static Term ctr1(uint32_t id, Term a) { return node1(T_CTR, ctr_ext(id, 1), a); }
static Term ctr2(uint32_t id, Term a, Term b) { return node2(T_CTR, ctr_ext(id, 2), a, b); }
static Term ctr3(uint32_t id, Term a, Term b, Term c) { return node3(T_CTR, ctr_ext(id, 3), a, b, c); }
static Term SET, ITV, konst_ref;
static Term konst(Term b) { return app2(konst_ref, b); }                       /* λ_. b */
static Term pi(Term A, Term B) { return ctr2(C_PI, A, B); }
static Term path(Term L, Term a, Term b) { return ctr3(C_PATH, L, a, b); }
static Term I0c(void) { return mk(T_I0, 0, 0); } static Term I1c(void) { return mk(T_I1, 0, 0); }
static Term proj(unsigned i, Term x) { return node2(T_PROJ, 0, node1(T_NUM, N_U64, i), x); }
static bool is_ctr(Term t, uint32_t id) { return tag(t) == T_CTR && ctr_id(t) == id; }
static uint32_t named(const char *n, uint32_t ar) { return ctor_intern(n, ar); }

/* ---- conversion on cells ------------------------------------------------------------------ */
static bool eq(Term u, Term v, int d);
/* two closures of one code convert when every level the code reads converts; for an eliminator the
   scrutinee is compared apart, so only its branches (and motive) decide which levels matter */
static bool frames_eq(Term a, Term b, uint32_t code, uint32_t code2, int d) {
  if (a == b) return true;
  uint32_t na = next_depth(a), nb = next_depth(b);
  if (na != nb) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [frames] depth %u vs %u\n", na, nb); return false; }
  for (uint32_t l = 0; l < na; l++) {
    if ((code || code2) && !code_uses(code, l) && !code_uses(code2, l)) continue;
    bool da = frame_is_dim(a, l), db = frame_is_dim(b, l);
    if (da != db) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [frames] level %u dim %d vs %d\n", l, da, db); return false; }
    if (da) continue;                                /* a bound dimension: the same position is the same name */
    bool x, y; if (!eq(frame_lookup(a, l, &x), frame_lookup(b, l, &y), d+1)) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [frames] level %u differs\n", l); return false; }
  }
  return true;
}
/* two stuck eliminators: same code → frames convert; else branch by branch on fresh fields */
static bool elims_eq(Term u, Term v, int d, bool helim) {
  uint32_t off = helim ? 0 : 0;
  Term su = HEAP[loc(u)+off], sv = HEAP[loc(v)+off];
  if ((su == 0) != (sv == 0)) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [elims] one is a function cell\n"); return false; }
  if (su && !eq(su, sv, d+1)) { if (getenv("HYPER_EQDBG")) { fprintf(stderr, "  [elims] scrutinees differ: "); print_term(su, 4); fprintf(stderr, " vs "); print_term(sv, 4); fprintf(stderr, "\n"); } return false; }
  if (helim && !eq(HEAP[loc(u)+3], HEAP[loc(v)+3], d+1)) return false;
  Term cu = HEAP[loc(u)+1], cv = HEAP[loc(v)+1], fu = HEAP[loc(u)+2], fv = HEAP[loc(v)+2];
  if (cu == cv) return frames_eq(fu, fv, CODE[loc(cu)].b, CODE[loc(cu)].c, d);
  if (d > 48) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [elims] different code, depth exhausted\n"); return false; }
  for (uint32_t bu = CODE[loc(cu)].b; bu; bu = CODE[bu].c) {
    uint32_t bv = CODE[loc(cv)].b; while (bv && CODE[bv].ext != CODE[bu].ext) bv = CODE[bv].c;
    if (!bv || CODE[bv].a != CODE[bu].a) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [elims] branch %s missing or of another arity\n", CODE[bu].ext == 0xFFFFFF ? "_" : ctor_name(CODE[bu].ext)); return false; }
    Term f1 = fu, f2 = fv;
    for (uint32_t i = 0; i < CODE[bu].a; i++) { Term a = atom(); f1 = frame_push(f1, a); f2 = frame_push(f2, a); }
    if (!eq(inst(CODE[bu].b, f1), inst(CODE[bv].b, f2), d+1)) return false;
  }
  for (uint32_t bv = CODE[loc(cv)].b; bv; bv = CODE[bv].c) {
    uint32_t bu = CODE[loc(cu)].b; while (bu && CODE[bu].ext != CODE[bv].ext) bu = CODE[bu].c;
    if (!bu) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [elims] extra branch %s\n", CODE[bv].ext == 0xFFFFFF ? "_" : ctor_name(CODE[bv].ext)); return false; }
  }
  return true;
}
static bool is_id_fn(Term f, int d) { Term a = atom(); return eq(app2(f, a), a, d+1); }
/* Equal.isIdUa: the universe path ua(A,B,f,g,..) with A ≡ B and f, g ≡ id is the constant line at A */
static Term id_ua_base(Term p, int d) {
  p = whnf(p);
  if (tag(p) != T_CTR || ctr_arity(p) != 6 || strcmp(ctor_name(ctr_id(p)), "UaU")) return 0;
  if (!eq(HEAP[loc(p)], HEAP[loc(p)+1], d+1) || !is_id_fn(HEAP[loc(p)+2], d) || !is_id_fn(HEAP[loc(p)+3], d)) return 0;
  return HEAP[loc(p)];
}
static bool faces_eq(Term fu, Term fv, int d) {   /* the faces of a composite are a set: each face of one has an equal face in the other */
  Term a[64], b[64]; uint32_t na = 0, nb = 0;
  for (Term l = whnf(fu); is_ctr(l, C_CONS) && na < 64; l = whnf(HEAP[loc(l)+1])) a[na++] = HEAP[loc(l)];
  for (Term l = whnf(fv); is_ctr(l, C_CONS) && nb < 64; l = whnf(HEAP[loc(l)+1])) b[nb++] = HEAP[loc(l)];
  if (na != nb) return false;
  bool used[64] = {0};
  for (uint32_t i = 0; i < na; i++) { bool found = false;
    for (uint32_t j = 0; j < nb && !found; j++) if (!used[j] && eq(a[i], b[j], d+1)) { used[j] = true; found = true; }
    if (!found) return false; }
  return true;
}
static bool words_eq(Term u, Term v, unsigned n, int d) { for (unsigned i = 0; i < n; i++) if (!eq(HEAP[loc(u)+i], HEAP[loc(v)+i], d+1)) return false; return true; }
static uint64_t EQ_CALLS; static int IN_HOOK;
static bool eq_leaf(Term u, Term v, bool r) {   /* the innermost failing comparison, for the trace */
  if (!r && !IN_HOOK && getenv("HYPER_EQDBG")) { fprintf(stderr, "  [eq leaf] "); print_term(u, 5); fprintf(stderr, "  vs  "); print_term(v, 5); fprintf(stderr, "\n"); }
  return r;
}
static bool eq_(Term u, Term v, int d);
static bool eq_struct(Term u, Term v, int d);
static bool eq(Term u, Term v, int d) {
  bool r = eq_(u, v, d);
  if (!r && !IN_HOOK && d <= 14 && getenv("HYPER_EQDBG")) { fprintf(stderr, "  [eq d=%d] ", d); print_term(u, 4); fprintf(stderr, "  vs  "); print_term(v, 4); fprintf(stderr, "\n"); }
  return r;
}
/* pairs already under comparison: a revisit is the coinductive case and counts as equal (path ≃ bisimulation) */
static struct { uint64_t k[1 << 14]; uint32_t n; } EQV;
static uint64_t eq_key(Term u, Term v) { uint64_t k = ((uint64_t)loc(u) << 32) ^ (uint64_t)loc(v) ^ ((uint64_t)tag(u) << 56); return k ? k : 1; }
static bool eq_seen(Term u, Term v) {
  if (EQV.n > (1u << 13)) return false;
  uint64_t key = eq_key(u, v);
  uint32_t h = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 50) & ((1 << 14) - 1);
  for (;;) { if (!EQV.k[h]) { EQV.k[h] = key; EQV.n++; return false; } if (EQV.k[h] == key) return true; h = (h + 1) & ((1 << 14) - 1); }
}
static void eq_forget(Term u, Term v) {           /* a comparison that failed is not an assumption anyone may rely on */
  uint64_t key = eq_key(u, v);
  uint32_t h = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 50) & ((1 << 14) - 1);
  for (;;) { if (!EQV.k[h]) return; if (EQV.k[h] == key) { EQV.k[h] = ~0ull; return; } h = (h + 1) & ((1 << 14) - 1); }   /* a tombstone keeps the probe chain */
}
/* Equal.sameHead: two applications of the same definition with convertible arguments are equal without
   unfolding (a recursive definition applied to a coordinate would regenerate itself forever) */
static bool same_head(Term u, Term v, int d) {
  Term au[64], av[64]; uint32_t nu, nv;
  Term hu = spine(u, au, &nu), hv = spine(v, av, &nv);
  if (tag(hu) != T_REF || tag(hv) != T_REF || loc(hu) != loc(hv) || nu != nv) return false;
  for (uint32_t i = 0; i < nu; i++) if (!eq(au[i], av[i], d+1)) return false;
  return true;
}
static bool eq_(Term u, Term v, int d) {
  if (u == v) return true;
  if ((tag(u) == T_APP || tag(u) == T_REF) && (tag(v) == T_APP || tag(v) == T_REF) && same_head(u, v, d)) return true;
  /* η-long forms of the same thing are the same thing: compare what was reflected before expanding it */
  if (tag(u) == T_REFLECT && tag(v) == T_REFLECT) return eq(HEAP[loc(u)], HEAP[loc(v)], d+1);
  if (tag(u) == T_REFLECT && eq(HEAP[loc(u)], v, d+1)) return true;
  if (tag(v) == T_REFLECT && eq(u, HEAP[loc(v)], d+1)) return true;
  if (++EQ_CALLS > 2000000 && getenv("HYPER_DEBUG")) { fprintf(stderr, "eq: runaway at depth %d, tags %u %u\n", d, tag(u), tag(v)); print_term(u, 6); fprintf(stderr, "\n"); print_term(v, 6); fprintf(stderr, "\n"); exit(9); }
  u = whnf(u); v = whnf(v);
  if (u == v) return true;
  if (d > 65536) { if (getenv("HYPER_EQDBG")) fprintf(stderr, "  [eq] depth exceeded\n"); return false; }
  bool track = (tag(u) == T_CTR || tag(u) == T_CASE || tag(u) == T_HELIM) && tag(u) == tag(v);
  if (track) { if (eq_seen(u, v)) return true;         /* the coinductive assumption, on the current path */
    bool r = eq_struct(u, v, d); if (!r) eq_forget(u, v); return r; }
  return eq_struct(u, v, d);
}
static bool eq_struct(Term u, Term v, int d) {
  /* η: functions, lines, pairs; a body is opened uncomputed so a definition applied inside it is seen by its head */
  if (tag(u) == T_PLM || tag(v) == T_PLM) { Term k = ivar_of(dim_push(0));   /* a line: the fresh variable is a dimension (a λ over the interval too) */
    return eq(tag(u) == T_PLM || tag(u) == T_LAM ? open_closure(u, k) : app2(u, k), tag(v) == T_PLM || tag(v) == T_LAM ? open_closure(v, k) : app2(v, k), d+1); }
  if (tag(u) == T_LAM || tag(v) == T_LAM) { Term a = atom();
    return eq(tag(u) == T_LAM ? open_closure(u, a) : app2(u, a), tag(v) == T_LAM ? open_closure(v, a) : app2(v, a), d+1); }
  if (is_ctr(u, C_PAIR) || is_ctr(v, C_PAIR)) {
    if (is_ctr(u, C_PAIR) && is_ctr(v, C_PAIR)) return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1);
    if (tag(u) == T_CTR && tag(v) == T_CTR) return false;      /* a pair against another constructor */
    return eq(proj(0, u), proj(0, v), d+1) && eq(proj(1, u), proj(1, v), d+1);
  }
  /* a universe path at an identity equivalence is its constant base */
  if (d < 40) {
    if (tag(u) == T_PAP) { Term A = id_ua_base(HEAP[loc(u)], d); if (A) return eq(A, v, d+1); }
    if (tag(v) == T_PAP) { Term A = id_ua_base(HEAP[loc(v)], d); if (A) return eq(u, A, d+1); }
    if (tag(u) == T_APP) { Term A = id_ua_base(HEAP[loc(u)], d); if (A) return eq(A, v, d+1); }
    if (tag(v) == T_APP) { Term A = id_ua_base(HEAP[loc(v)], d); if (A) return eq(u, A, d+1); }
    if (tag(u) == T_CTR && !strcmp(ctor_name(ctr_id(u)), "UaU") && tag(v) != T_CTR) { Term A = id_ua_base(u, d); if (A) return eq(konst(A), v, d+1); }
    if (tag(v) == T_CTR && !strcmp(ctor_name(ctr_id(v)), "UaU") && tag(u) != T_CTR) { Term A = id_ua_base(v, d); if (A) return eq(u, konst(A), d+1); }
  }
  /* p @ i with its boundary kept is p @ i: the endpoints are determined by p */
  if (tag(u) == T_PAP && tag(v) == T_APP) return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1);
  if (tag(v) == T_PAP && tag(u) == T_APP) return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1);
  if (tag(u) == T_PAP && tag(v) == T_PAP) return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1);
  if (tag(u) != tag(v)) {
    bool iu = tag(u) == T_I0 || tag(u) == T_I1 || tag(u) == T_IVAR || tag(u) == T_IDNF;
    bool iv = tag(v) == T_I0 || tag(v) == T_I1 || tag(v) == T_IVAR || tag(v) == T_IDNF;
    if (iu && iv) return eq_leaf(u, v, ieq(ican(u), ican(v)));
    return eq_leaf(u, v, false);
  }
  switch (tag(u)) {
    case T_VAR: return eq_leaf(u, v, loc(u) == loc(v));
    case T_I0: case T_I1: return true;
    case T_IVAR: case T_IDNF: return eq_leaf(u, v, ieq(ican(u), ican(v)));
    case T_INOT: return words_eq(u, v, 1, d);         /* a neutral formula over interval atoms: structural (Equal.cmp) */
    case T_IAND: case T_IOR: return words_eq(u, v, 2, d);
    case T_NUM: return eq_leaf(u, v, ext(u) == ext(v) && HEAP[loc(u)] == HEAP[loc(v)]);
    case T_ERA: return true;
    case T_REF: return eq_leaf(u, v, loc(u) == loc(v));
    case T_CTR: if (ext(u) != ext(v)) return eq_leaf(u, v, false); return words_eq(u, v, ctr_arity(u), d);
    case T_SUP: { Term a = whnf(HEAP[loc(u)]), b = whnf(HEAP[loc(v)]); if (tag(a) != tag(b) || loc(a) != loc(b)) return false; return words_eq(u, v, 3, d); }
    case T_APP: return words_eq(u, v, 2, d);
    case T_CASE: return elims_eq(u, v, d, false);
    case T_HELIM: return elims_eq(u, v, d, true);
    case T_FCE: if (ext(u) != ext(v)) return false; return words_eq(u, v, ext(u) == 2 ? 3 : 2, d);
    case T_TRP: return words_eq(u, v, 4, d);
    case T_HCM: return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1) && faces_eq(HEAP[loc(u)+2], HEAP[loc(v)+2], d);
    case T_GLU: return eq(HEAP[loc(u)], HEAP[loc(v)], d+1) && faces_eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d);
    case T_GLUE: return faces_eq(HEAP[loc(u)], HEAP[loc(v)], d) && eq(HEAP[loc(u)+1], HEAP[loc(v)+1], d+1);
    case T_OP2: case T_PROJ: case T_CHK: case T_CWITH: case T_REFLECT: return (tag(u) != T_OP2 || ext(u) == ext(v)) && words_eq(u, v, 2, d);
    case T_OP1: return ext(u) == ext(v) && words_eq(u, v, 1, d);
    case T_UNGLUE: case T_POUT: case T_GBASE: case T_GFACES: case T_CFIELDS: return words_eq(u, v, 1, d);
    case T_FCASE: case T_ETYPE: case T_PAP: return words_eq(u, v, 4, d);
    case T_ETERM: return words_eq(u, v, 3, d);
    default: return false;
  }
}
bool equal(Term u, Term v) { memset(&EQV, 0, sizeof EQV); return eq(u, v, 0); }
static bool rewrite_hook(Term old, Term v) { IN_HOOK++; bool r = eq(old, v, 0); IN_HOOK--;
  if (getenv("HYPER_HOOKDBG") && tag(v) == T_APP) { fprintf(stderr, "  [hook %d] ", r); print_term(old, 4); fprintf(stderr, "  ~  "); print_term(v, 4); fprintf(stderr, "\n"); }
  return r; }

/* ---- faces: check under a face, restrict a cell ------------------------------------------- */
/* face-cell scratch arrays live off the stack (a check frame must stay small: numerals recurse deep) */
static FaceCell *CELLS_POOL[64]; static unsigned CELLS_TOP;
static void cells_init(void) { if (CELLS_POOL[0]) return; for (int i = 0; i < 64; i++) CELLS_POOL[i] = calloc(64, sizeof(FaceCell)); }
static Term restrict_cell(Term x, FaceCell *c) { for (uint32_t i = 0; i < c->n; i++) x = fce3(c->side[i], c->name[i], x, 0); return x; }
static Term restrict_frame(Term fr, FaceCell *c) {
  for (uint32_t i = 0; i < c->n; i++) { fr = restrict_push(fr, mk(T_IVAR, 0, c->name[i]), c->side[i], 0);
    RW[NRW].old = mk(T_IVAR, 0, c->name[i]); RW[NRW].side = c->side[i]; RW[NRW].by = 0; NRW++; }
  return fr;
}
static void unrestrict(FaceCell *c) { NRW -= (int)c->n; }
static void push_rw(Term old, Term by) { RW[NRW].old = old; RW[NRW].side = 2; RW[NRW].by = by; NRW++; }
static void pop_rw(void) { NRW--; }
static Term rewrite(Term old, Term by, Term goal) { return fce_raw(2, old, goal, by); }

bool occurs_cell(Loc name, Term t);              /* cell.c: regularity by normalisation */
/* ---- the checker over static code ---------------------------------------------------------- */
static bool check(uint32_t c, Term fr, Term goal);
static Term infer(uint32_t c, Term fr);           /* 0 on failure (VERR set) */
static Term cell(uint32_t c, Term fr) { return inst(c, fr); }
static bool check_set(uint32_t c, Term fr) { return check(c, fr, SET); }
static bool check_itv(uint32_t c, Term fr) { return check(c, fr, ITV); }
static bool verify(uint32_t c, Term fr, Term goal) {
  Term T = infer(c, fr); if (!T) return false;
  memset(&EQV, 0, sizeof EQV);
  if (eq(T, goal, 0)) return true;
  return fail_mis(goal, T);
}
static uint32_t skip_dims(uint32_t c, Term *fr) { while (CODE[c].tag == S_DIM) { *fr = bind_dim(*fr); c = CODE[c].a; } return c; }
static uint32_t strip_dims(uint32_t c) { while (CODE[c].tag == S_DIM) c = CODE[c].a; return c; }

/* the enum a symbol belongs to: a definition `T : Set = Σ (Enum syms). …` (Bend2's bookEnums) */
static Term enum_of_sym(uint32_t sid) {
  for (uint32_t i = 0; i < BOOK_LEN; i++) {
    if (!BOOK[i].type || !BOOK[i].code) continue;
    uint32_t c = strip_dims(BOOK[i].code);
    if (CODE[c].tag != S_CTR || (CODE[c].ext >> 8) != C_SIG) continue;
    uint32_t e = CODE[c].a; if (CODE[e].tag != S_CTR || (CODE[e].ext >> 8) != C_ENUM) continue;
    for (uint32_t l = CODE[e].a; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) {
      uint32_t s = CODE[l].a; if (CODE[s].tag == S_CTR && (CODE[s].ext >> 8) == sid) return inst(e, 0);
    }
  }
  return 0;
}
static bool enum_has(Term en, uint32_t sid) {     /* en = #Enum{list of symbols} */
  for (Term l = whnf(HEAP[loc(en)]); is_ctr(l, C_CONS); l = whnf(HEAP[loc(l)+1])) { Term s = whnf(HEAP[loc(l)]); if (tag(s) == T_CTR && ctr_id(s) == sid) return true; }
  return false;
}
static uint32_t num_kind_of(Term T) {             /* #Num{&U64} → kind, or 99 */
  if (!is_ctr(T, C_NUMTY)) return 99;
  Term k = whnf(HEAP[loc(T)]); if (tag(k) != T_CTR) return 99;
  const char *n = ctor_name(ctr_id(k));
  if (!strcmp(n, "&U64")) return N_U64; if (!strcmp(n, "&I64")) return N_I64; if (!strcmp(n, "&F64")) return N_F64; if (!strcmp(n, "&Char")) return N_CHR;
  return 99;
}
static Term num_type(unsigned kind) {
  const char *n = kind == N_U64 ? "&U64" : kind == N_I64 ? "&I64" : kind == N_F64 ? "&F64" : "&Char";
  return ctr1(C_NUMTY, ctr0(named(n, 0)));
}

/* applyTele over static arguments */
static Term apply_tele(Term ty, uint32_t *args, uint32_t n, Term fr) {
  for (uint32_t i = 0; i < n; i++) {
    ty = whnf(ty);
    if (!is_ctr(ty, C_PI)) { fail_mis(pi(mk(T_ERA,0,0), mk(T_ERA,0,0)), ty); return 0; }
    if (!check(args[i], fr, HEAP[loc(ty)])) return 0;
    ty = app2(HEAP[loc(ty)+1], cell(args[i], fr));
  }
  return ty;
}
static void ctr_args(uint32_t c, uint32_t *out, uint32_t *n) {
  SNode *k = &CODE[c]; uint32_t ar = k->ext & 0xFF; *n = ar;
  if (ar <= 4) { uint32_t kk[4] = { k->a, k->b, k->c, k->d }; for (uint32_t i = 0; i < ar; i++) out[i] = kk[i]; }
  else for (uint32_t i = 0; i < ar; i++) out[i] = KIDS[k->kids + i];
}

/* the eliminator's branches (checkBranches): every constructor has a branch, each checked at its type */
static bool check_branches(uint32_t hcode, Term fr, uint32_t hit, Term ps_list, Term P, Term elim) {
  uint32_t first = CODE[hcode].b;
  /* every branch names a constructor of the HIT */
  for (uint32_t br = first; br; br = CODE[br].c) if (CINFO[CODE[br].ext].hit != hit) return fail_ci("helim: a branch for a constructor of another type");
  for (uint32_t cid = 0; cid < (1u << 16); cid++) {
    if (CINFO[cid].hit != hit || cid == hit) continue;
    uint32_t br = first; while (br && CODE[br].ext != cid) br = CODE[br].c;
    if (!br) return fail_ci("helim: incomplete match");
    if (CODE[br].a != CINFO[cid].nfields) return fail_ci("helim: branch arity");
    Term ty = inst(BOOK[CINFO[cid].type_def].code, 0);
    Term fields[64]; uint32_t nf = 0;
    /* the parameters */
    for (Term l = whnf(ps_list); is_ctr(l, C_CONS); l = whnf(HEAP[loc(l)+1])) {
      ty = whnf(ty); if (!is_ctr(ty, C_PI)) return fail_ci("helim: constructor type");
      fields[nf++] = HEAP[loc(l)]; ty = app2(HEAP[loc(ty)+1], HEAP[loc(l)]);
    }
    /* the fields, bound as coordinates */
    Term f = fr;
    for (uint32_t i = 0; i < CODE[br].a; i++) {
      ty = whnf(ty); if (!is_ctr(ty, C_PI)) return fail_ci("helim: constructor type");
      f = bind_coord(f, HEAP[loc(ty)]); Term x = var_of(f);
      fields[nf++] = x;
      ty = app2(HEAP[loc(ty)+1], x);
    }
    uint32_t np = CINFO[hit].carries ? CINFO[hit].nparams : 0; (void)np;
    Loc l = alloc(nf ? nf : 1); for (uint32_t i = 0; i < nf; i++) HEAP[l+i] = fields[i];
    Term u = mk(T_CTR, ctr_ext(cid, nf), l);
    Term goal = node4(T_ETYPE, 0, P, elim, ty, u);
    if (!check(CODE[br].b, f, goal)) return false;
  }
  return true;
}

static Term infer(uint32_t c, Term fr) {
  SNode *n = &CODE[c]; CUR_CODE = c;
  if (getenv("HYPER_TRACE")) fprintf(stderr, "%*sinfer tag %u\n", DBG_DEPTH*2, "", n->tag);
  switch (n->tag) {
    case S_VAR: if (!CTX_TY[n->ext] && CTX_LET_CODE[n->ext]) return infer(CTX_LET_CODE[n->ext], CTX_LET_FR[n->ext]); return ctx_type(n->ext);
    case S_IVAR: return ITV;
    case S_REF: { Def *d = &BOOK[n->ext]; if (!d->type) { fail_ci("cannot infer: an untyped definition"); return 0; } return inst(d->type, 0); }
    case S_LET: { VRes e = VERR; Term T = infer(n->a, fr); if (T) return infer(n->b, bind_value(fr, cell(n->a, fr), T));
                  VERR = e; return infer(n->b, bind_let(fr, n->a, fr)); }
    case S_CHK: {
      if (CODE[n->b].tag == S_CTR && CINFO[CODE[n->b].ext >> 8].hit) {   /* a HIT constructor annotated with its HIT: its own type (Core.Check infer Chk/HCon) */
        Term T = whnf(cell(n->a, fr)); if (tag(T) == T_CTR && ctr_id(T) == CINFO[CODE[n->b].ext >> 8].hit) return infer(n->b, fr); }
      if (!check(n->b, fr, cell(n->a, fr))) return 0; return cell(n->a, fr); }
    case S_LAM: case S_PLM: case S_FIX: case S_ERA: case S_SUP: case S_CASE: fail_ci("cannot infer"); return 0;
    case S_FCE: { Term T = infer(n->b, fr); if (!T) return 0; Term nm = n->d ? cell(n->d, fr) : mk(T_IVAR, 0, 0); return fce_raw(n->ext, nm, T, 0); }
    case S_I0: case S_I1: return ITV;
    case S_INOT: if (!check_itv(n->a, fr)) return 0; return ITV;
    case S_IAND: case S_IOR: if (!check_itv(n->a, fr) || !check_itv(n->b, fr)) return 0; return ITV;
    case S_NUM: return num_type(n->ext);
    case S_OP2: {
      Term ta = infer(n->a, fr); if (!ta) return 0; Term tb = infer(n->b, fr); if (!tb) return 0;
      ta = whnf(ta); tb = whnf(tb); unsigned ka = num_kind_of(ta), kb = num_kind_of(tb);
      bool boolean = is_ctr(ta, C_BOOL) && is_ctr(tb, C_BOOL);
      switch (n->ext) {
        case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV: case OP_MOD: case OP_POW:
          if (ka != 99 && ka == kb) return num_type(ka); fail_mis(num_type(N_U64), ta); return 0;
        case OP_EQ: case OP_NE: case OP_LT: case OP_GT: case OP_LE: case OP_GE:
          if ((ka != 99 && ka == kb) || boolean) return ctr0(C_BOOL); fail_mis(ta, tb); return 0;
        case OP_AND: case OP_OR: case OP_XOR:
          if (boolean) return ctr0(C_BOOL); if (ka != 99 && ka == kb && ka != N_CHR) return num_type(N_U64); fail_mis(ta, tb); return 0;
        case OP_LSH: case OP_RSH:
          if (ka != 99 && ka == kb && ka != N_CHR) return num_type(N_U64); fail_mis(num_type(N_U64), ta); return 0;
      }
      return 0; }
    case S_OP1: {
      Term ta = infer(n->a, fr); if (!ta) return 0; ta = whnf(ta); unsigned ka = num_kind_of(ta);
      if (n->ext == OP1_NOT) { if (is_ctr(ta, C_BOOL)) return ctr0(C_BOOL); if (ka != 99 && ka != N_CHR) return num_type(N_U64); }
      if (n->ext == OP1_NEG) { if (ka == N_I64 || ka == N_F64) return num_type(ka); }
      if (n->ext == OP1_TOCHAR) { if (ka == N_U64) return num_type(N_CHR); }
      fail_ci("cannot infer: unary operator"); return 0; }
    case S_CTR: {
      uint32_t id = n->ext >> 8, ar = n->ext & 0xFF; uint32_t args[64]; uint32_t na; ctr_args(c, args, &na);
      switch (id) {
        case C_SET: case C_EMPTY: case C_UNIT: case C_BOOL: case C_NAT: return SET;
        case C_TT: return ctr0(C_UNIT);
        case C_TRUE: case C_FALSE: return ctr0(C_BOOL);
        case C_ZER: return ctr0(C_NAT);
        case C_SUC: { Term T = infer(args[0], fr); if (!T) return 0; T = whnf(T);
          if (is_ctr(T, C_NAT)) return T;
          if (is_ctr(T, C_EQL) && is_ctr(whnf(HEAP[loc(T)]), C_NAT)) return ctr3(C_EQL, HEAP[loc(T)], ctr1(C_SUC, HEAP[loc(T)+1]), ctr1(C_SUC, HEAP[loc(T)+2]));
          fail_mis(ctr0(C_NAT), T); return 0; }
        case C_LIST: if (!check_set(args[0], fr)) return 0; return SET;
        case C_NIL: case C_CONS: case C_REFL: fail_ci("cannot infer"); return 0;
        case C_ENUM: return SET;
        case C_NUMTY: return SET;
        case C_SIG: case C_PI: if (!check_set(args[0], fr)) return 0; if (!check(args[1], fr, pi(cell(args[0], fr), konst(SET)))) return 0; return SET;
        case C_PAIR: { Term A = infer(args[0], fr); if (!A) return 0; Term B = infer(args[1], fr); if (!B) return 0; return ctr2(C_SIG, A, konst(B)); }
        case C_EQL: if (!check_set(args[0], fr)) return 0; { Term T = cell(args[0], fr); if (!check(args[1], fr, T) || !check(args[2], fr, T)) return 0; } return SET;
        case C_PATH: { if (!check(args[0], fr, pi(ITV, konst(SET)))) return 0; Term L = cell(args[0], fr);
          if (!check(args[1], fr, app2(L, I0c())) || !check(args[2], fr, app2(L, I1c()))) return 0; return SET; }
        case C_GLU: { int eq_d = book_find("Equiv-ty");
          if (!check_set(args[0], fr)) return 0; Term A = cell(args[0], fr);
          /* the faces: a static list of (ctr GFace phi T e) */
          for (uint32_t l = args[1]; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) {
            uint32_t g = CODE[l].a; if (CODE[g].tag != S_CTR || (CODE[g].ext >> 8) != C_GFACE) { fail_ci("Glue: face"); return 0; }
            if (!check_itv(CODE[g].a, fr) || !check_set(CODE[g].b, fr)) return 0;
            Term T = cell(CODE[g].b, fr);
            if (eq_d < 0 || !check(CODE[g].c, fr, app2(app2(ref_of(eq_d), T), A))) return 0;
          }
          return SET; }
        default: break;
      }
      if (id == C_ITV) return SET;
      const char *nm = ctor_name(id);
      if (nm[0] == '&' && ar == 0) { Term en = enum_of_sym(id); if (!en) { fail_ci("cannot infer: a symbol of no declared enum"); return 0; } return en; }
      if (!strcmp(nm, "Partial")) { if (!check_itv(args[0], fr) || !check_set(args[1], fr)) return 0; return SET; }
      if (!strcmp(nm, "Sub")) { if (!check_set(args[0], fr) || !check_itv(args[1], fr)) return 0;
        Term A = cell(args[0], fr); FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(cell(args[1], fr), cells, 64);
        for (int i = 0; i < nc; i++) { Term f = restrict_frame(fr, &cells[i]); bool ok = check(args[2], f, restrict_cell(A, &cells[i])); unrestrict(&cells[i]); if (!ok) return 0; }
        return SET; }
      if (!strcmp(nm, "InS")) { Term T = infer(args[0], fr); if (!T) return 0; return ctr3(named("Sub", 3), T, I0c(), cell(args[0], fr)); }
      if (!strcmp(nm, "Sys")) {
        uint32_t l = args[0]; if (CODE[l].tag != S_CTR || (CODE[l].ext >> 8) != C_CONS) { fail_mis(ctr2(named("Partial",2), I0c(), SET), ctr1(named("Sys",1), nil_cell())); return 0; }
        uint32_t f0 = CODE[l].a; Term A = infer(CODE[f0].b, fr); if (!A) return 0;
        Term phi = 0; for (; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) { Term p = cell(CODE[CODE[l].a].a, fr); phi = phi ? node2(T_IOR, 0, phi, p) : p; }
        return ctr2(named("Partial", 2), phi, A); }
      if (!strcmp(nm, "@Trunc/tin")) { Term T = infer(args[0], fr); if (!T) return 0; return ctr1(named("h/Trunc", 1), T); }
      if (!strcmp(nm, "@Trunc/tsquash")) { Term T = infer(args[0], fr); if (!T) return 0; if (!check(args[1], fr, T)) return 0; return path(konst(T), cell(args[0], fr), cell(args[1], fr)); }
      if (!strcmp(nm, "@S1/base")) return ctr0(named("h/S1", 0));
      if (!strcmp(nm, "@S1/loop")) return path(konst(ctr0(named("h/S1", 0))), ctr0(id), ctr0(id));
      if (CINFO[id].is_hit) {                          /* a HIT type applied to its parameters */
        if (ar != CINFO[id].nparams) { fail_ci("HIT: parameter count"); return 0; }
        Term ty = apply_tele(inst(BOOK[CINFO[id].type_def].code, 0), args, na, fr); if (!ty) return 0; return SET; }
      if (CINFO[id].hit) {                             /* a HIT constructor at its parameters and fields */
        uint32_t np = CINFO[CINFO[id].hit].carries ? CINFO[CINFO[id].hit].nparams : 0;
        if (ar != np + CINFO[id].nfields) { fail_ci("HIT constructor: arity"); return 0; }
        if (!CINFO[CINFO[id].hit].carries && CINFO[CINFO[id].hit].nparams) { fail_ci("cannot infer: a built-in HIT constructor"); return 0; }
        return apply_tele(inst(BOOK[CINFO[id].type_def].code, 0), args, na, fr); }
      fail_ci("cannot infer: constructor"); return 0; }
    case S_APP: {
      /* (app (lam x body) v): the binder is the value; (app (plm i body) r): the dimension is substituted (PAp β) */
      if (CODE[n->a].tag == S_LAM) { Term T = infer(n->b, fr); if (!T) return 0; return infer(CODE[n->a].a, bind_value(fr, cell(n->b, fr), T)); }
      if (CODE[n->a].tag == S_PLM) { if (!check_itv(n->b, fr)) return 0; Term f = bind_dim(fr); return infer(CODE[n->a].a, restrict_push(f, ivar_of(f), 2, cell(n->b, fr))); }
      { uint32_t sp[64]; uint32_t ns = 0; uint32_t h = c; while (CODE[h].tag == S_APP && ns < 64) { sp[ns++] = CODE[h].b; h = CODE[h].a; }
        for (uint32_t i = 0; i < ns / 2; i++) { uint32_t t = sp[i]; sp[i] = sp[ns-1-i]; sp[ns-1-i] = t; }
        if (CODE[h].tag == S_REF) {
          const char *nm = BOOK[CODE[h].ext].name;
          if (!strcmp(nm, "trec") && ns == 3) {        /* TRec x pb f: the target is f's codomain */
            Term fT = infer(sp[2], fr); if (!fT) return 0; fT = whnf(fT);
            if (!is_ctr(fT, C_PI)) { fail_mis(pi(SET, konst(SET)), fT); return 0; }
            Term aT = HEAP[loc(fT)], bT = app2(HEAP[loc(fT)+1], atom());
            if (!check(sp[0], fr, ctr1(named("h/Trunc", 1), aT))) return 0;
            int d = book_find("isProp-ty"); if (d < 0) { fail_ci("isProp-ty"); return 0; }
            if (!check(sp[1], fr, app2(ref_of(d), bT))) return 0;
            return bT; }
          if (!strcmp(nm, "srec") && ns == 3) {        /* CRec x b l */
            if (!check(sp[0], fr, ctr0(named("h/S1", 0)))) return 0;
            Term bT = infer(sp[1], fr); if (!bT) return 0;
            if (!check(sp[2], fr, path(konst(bT), cell(sp[1], fr), cell(sp[1], fr)))) return 0;
            return bT; }
        } }
      Term fT = infer(n->a, fr); if (!fT) return 0; fT = whnf(fT);
      if (is_ctr(fT, C_PI)) { if (!check(n->b, fr, HEAP[loc(fT)])) return 0; return app2(HEAP[loc(fT)+1], cell(n->b, fr)); }
      if (is_ctr(fT, C_PATH)) { if (!check_itv(n->b, fr)) return 0; return app2(HEAP[loc(fT)], cell(n->b, fr)); }
      fail_mis(pi(mk(T_ERA,0,0), mk(T_ERA,0,0)), fT); return 0; }
    case S_TRP: {
      if (!check(n->a, fr, pi(ITV, konst(SET))) || !check_itv(n->b, fr) || !check_itv(n->c, fr)) return 0;
      Term L = cell(n->a, fr);
      if (!check(n->d, fr, app2(L, cell(n->b, fr)))) return 0;
      return app2(L, cell(n->c, fr)); }
    case S_HCM: {
      if (!check_set(n->a, fr)) return 0; Term A = cell(n->a, fr);
      if (!check(n->b, fr, A)) return 0; Term x = cell(n->b, fr);
      uint32_t faces[64]; uint32_t nf = 0;
      for (uint32_t l = n->c; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) faces[nf++] = CODE[l].a;
      for (uint32_t i = 0; i < nf; i++) {
        uint32_t pc = CODE[faces[i]].a, uc = CODE[faces[i]].b;
        if (!check_itv(pc, fr)) return 0;
        FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(cell(pc, fr), cells, 64);
        for (int k = 0; k < nc; k++) {
          Term f = restrict_frame(fr, &cells[k]);
          Term u = cell(uc, f);
          Term goal = path(konst(restrict_cell(A, &cells[k])), restrict_cell(x, &cells[k]), app2(u, I1c()));
          bool ok = check(uc, f, goal); unrestrict(&cells[k]); if (!ok) return 0;
        }
      }
      for (uint32_t i = 0; i < nf; i++) for (uint32_t j = i + 1; j < nf; j++) {
        Term pq = node2(T_IAND, 0, cell(CODE[faces[i]].a, fr), cell(CODE[faces[j]].a, fr));
        FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(pq, cells, 64);
        for (int k = 0; k < nc; k++) {
          Term u = restrict_cell(cell(CODE[faces[i]].b, fr), &cells[k]), v = restrict_cell(cell(CODE[faces[j]].b, fr), &cells[k]);
          if (!eq(u, v, 0)) { fail_mis(u, v); return 0; }
        }
      }
      return A; }
    case S_UNGLUE: { Term T = infer(n->a, fr); if (!T) return 0; T = whnf(T); if (tag(T) == T_GLU) return HEAP[loc(T)]; return T; }
    case S_GLU: {                                     /* Glue A [(φ, T, e)…] : Set */
      int eq_d = book_find("Equiv-ty");
      if (!check_set(n->a, fr)) return 0; Term A = cell(n->a, fr);
      for (uint32_t l = n->b; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) {
        uint32_t g = CODE[l].a; if (CODE[g].tag != S_CTR || (CODE[g].ext >> 8) != C_GFACE) { fail_ci("Glue: face"); return 0; }
        if (!check_itv(CODE[g].a, fr) || !check_set(CODE[g].b, fr)) return 0;
        Term T = cell(CODE[g].b, fr);
        if (eq_d < 0 || !check(CODE[g].c, fr, app2(app2(ref_of(eq_d), T), A))) return 0;
      }
      return SET; }
    case S_GLUE: {                                    /* glue [(φ, t)…] x : the base type when every face is false (GlB infer) */
      Term xT = infer(n->b, fr); if (!xT) return 0;
      bool all_false = true;
      for (uint32_t l = n->a; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) {
        uint32_t f = CODE[l].a; if (!check_itv(CODE[f].a, fr)) return 0;
        if (tag(ican(cell(CODE[f].a, fr))) != T_I0) all_false = false;
      }
      if (all_false) return xT;
      fail_ci("cannot infer: glue with a live face"); return 0; }
    case S_HELIM: {
      if (!n->c || !n->a) { fail_ci("cannot infer: hrec"); return 0; }
      Term xT = infer(n->a, fr); if (!xT) return 0; xT = whnf(xT);
      if (tag(xT) != T_CTR || !CINFO[ctr_id(xT)].is_hit) { fail_mis(ctr0(named("HIT", 0)), xT); return 0; }
      if (!check(n->c, fr, pi(xT, konst(SET)))) return 0;
      Term P = cell(n->c, fr);
      Term elim = node4(T_HELIM, 0, 0, mk(0, 0, c), fr, P);
      if (!check_branches(c, fr, ctr_id(xT), fields_list(xT), P, elim)) return 0;
      return app2(P, cell(n->a, fr)); }
    case S_POUT: { Term T = infer(n->a, fr); if (!T) return 0; T = whnf(T);
      if (is_ctr(T, named("Partial", 2))) { Term p = ican(HEAP[loc(T)]); if (tag(p) == T_I1) return HEAP[loc(T)+1]; fail_mis(I1c(), p); return 0; }
      return T; }
    case S_LABEL: return ITV;
    default: fail_ci("cannot infer"); return 0;
  }
}

/* the goal rewritten at a match: the scrutinee's atom becomes the constructor (Rwt x ctor goal) */
static Term scrut_atom(uint32_t xc, Term fr) {
  if (CODE[xc].tag == S_VAR) return CTX_ATOM[CODE[xc].ext];
  return cell(xc, fr);        /* a non-variable scrutinee: the semantic rewrite (Core deviation kept: it is Bend2's rule) */
}
static bool check_branch(uint32_t br, Term fr, Term *field_types, Term atom_x, Term ctor_of_fields /* built by caller from fields */, Term goal);

/* check a case tree against a goal (the M-forms) */
static bool check_case(uint32_t c, Term fr, Term goal) {
  SNode *n = &CODE[c]; uint32_t xc = n->a;
  Term xT = infer(xc, fr); if (!xT) return false; xT = whnf(xT);
  Term ax = scrut_atom(xc, fr);
  uint32_t first = n->b;
  #define BRANCH(cid) ({ uint32_t _b = first; while (_b && CODE[_b].ext != (cid)) _b = CODE[_b].c; _b; })
  if (is_ctr(xT, C_EMPTY)) return true;
  if (is_ctr(xT, C_EQL) && !first) {               /* an empty match on a disequality */
    Term T = HEAP[loc(xT)], a = HEAP[loc(xT)+1], b = HEAP[loc(xT)+2]; (void)T;
    if (!eq(a, b, 0)) return true; return fail_mis(a, b);
  }
  /* a constructor-indexed match: branches by constructor id, fields bound as coordinates */
  struct { uint32_t cid; uint32_t nf; Term ftypes[4]; bool dep; } shape[8]; uint32_t ns = 0;
  if (is_ctr(xT, C_UNIT)) { shape[ns++] = (typeof(shape[0])){ C_TT, 0, {0}, false }; }
  else if (is_ctr(xT, C_BOOL)) { shape[ns++] = (typeof(shape[0])){ C_FALSE, 0, {0}, false }; shape[ns++] = (typeof(shape[0])){ C_TRUE, 0, {0}, false }; }
  else if (is_ctr(xT, C_NAT)) { shape[ns++] = (typeof(shape[0])){ C_ZER, 0, {0}, false }; shape[ns++] = (typeof(shape[0])){ C_SUC, 1, { ctr0(C_NAT) }, false }; }
  else if (is_ctr(xT, C_LIST)) { Term A = HEAP[loc(xT)]; shape[ns++] = (typeof(shape[0])){ C_NIL, 0, {0}, false }; shape[ns++] = (typeof(shape[0])){ C_CONS, 2, { A, xT }, false }; }
  else if (is_ctr(xT, C_SIG)) { shape[ns++] = (typeof(shape[0])){ C_PAIR, 2, { HEAP[loc(xT)], HEAP[loc(xT)+1] }, true }; }
  else if (is_ctr(xT, C_EQL)) { shape[ns++] = (typeof(shape[0])){ C_REFL, 0, {0}, false }; }
  else if (is_ctr(xT, named("Sub", 3))) { shape[ns++] = (typeof(shape[0])){ named("InS", 1), 1, { HEAP[loc(xT)] }, false }; }
  else if (is_ctr(xT, C_ENUM)) {
    /* every listed symbol; a default branch covers the rest */
    bool uncovered = false;
    for (Term l = whnf(HEAP[loc(xT)]); is_ctr(l, C_CONS); l = whnf(HEAP[loc(l)+1])) {
      Term s = whnf(HEAP[loc(l)]); uint32_t sid = ctr_id(s);
      uint32_t br = BRANCH(sid);
      if (!br) { uncovered = true; continue; }
      Term g = rewrite(ax, ctr0(sid), goal); push_rw(ax, ctr0(sid));
      bool ok = check(CODE[br].b, CODE[xc].tag == S_VAR ? restrict_push(fr, ax, 2, ctr0(sid)) : fr, g); pop_rw(); if (!ok) return false;
    }
    if (uncovered) { uint32_t df = BRANCH(0xFFFFFF); if (!df) return fail_ci("incomplete match"); if (!check(CODE[df].b, fr, goal)) return false; }
    return true;
  }
  else return fail_mis(ctr0(C_NAT), xT);
  for (uint32_t i = 0; i < ns; i++) {
    uint32_t br = BRANCH(shape[i].cid);
    if (!br) { if (BRANCH(0xFFFFFF)) continue; return fail_ci("incomplete match"); }
    if (CODE[br].a != shape[i].nf) return fail_ci("branch arity");
    /* x := ctor for everything older (rewriteCtx); the constructor is filled in below. Only a coordinate
       restricts the frame: a non-variable scrutinee rewrites the goal alone (the semantic rewrite at every
       read of every older variable is the recorded Core deviation, not reproduced) */
    bool coord = CODE[xc].tag == S_VAR;
    Term rst = coord ? restrict_push(fr, ax, 2, 0) : fr;
    Term f = rst; Term fields[4]; Term B = shape[i].dep ? shape[i].ftypes[1] : 0;
    for (uint32_t k = 0; k < shape[i].nf; k++) {
      Term ft = shape[i].dep && k == 1 ? app2(B, fields[0]) : shape[i].ftypes[k];
      f = bind_coord(f, apply_rw(ft)); fields[k] = var_of(f);
    }
    Term ctor; if (shape[i].nf == 0) ctor = ctr0(shape[i].cid); else { Loc l = alloc(shape[i].nf); for (uint32_t k = 0; k < shape[i].nf; k++) HEAP[l+k] = fields[k]; ctor = mk(T_CTR, ctr_ext(shape[i].cid, shape[i].nf), l); }
    if (coord) HEAP[loc(rst)+2] = ctor;
    Term g = goal;
    if (shape[i].cid == C_REFL) { Term a = HEAP[loc(xT)+1], b = HEAP[loc(xT)+2]; g = rewrite(a, b, rewrite(ax, ctor, goal)); push_rw(ax, ctor); push_rw(a, b);
      if (tag(whnf(a)) == T_VAR) f = restrict_push(f, a, 2, b); }
    else if (shape[i].cid == named("InS", 1)) { g = goal; if (coord) HEAP[loc(rst)+2] = ax; }   /* no rewrite for outS */
    else { g = rewrite(ax, ctor, goal); push_rw(ax, ctor); }
    bool ok = check(CODE[br].b, f, g);
    if (shape[i].cid == C_REFL) { pop_rw(); pop_rw(); } else if (shape[i].cid != named("InS", 1)) pop_rw();
    if (!ok) return false;
  }
  uint32_t df = BRANCH(0xFFFFFF); if (df) { if (!check(CODE[df].b, fr, goal)) return false; }
  return true;
  #undef BRANCH
}

static bool check(uint32_t c, Term fr, Term goal) {
  SNode *n = &CODE[c]; CUR_CODE = c;
  if (getenv("HYPER_TRACE")) { fprintf(stderr, "%*scheck tag %u vs ", DBG_DEPTH*2, "", n->tag); print_term(goal, 6); fprintf(stderr, "\n"); }
  goal = whnf(goal);
  switch (n->tag) {
    case S_ERA: return true;
    case S_LET: { VRes e = VERR; Term T = infer(n->a, fr); if (T) return check(n->b, bind_value(fr, cell(n->a, fr), T), goal);
                  VERR = e; return check(n->b, bind_let(fr, n->a, fr), goal); }
    case S_LAM: {
      if (!is_ctr(goal, C_PI)) return fail_mis(pi(mk(T_ERA,0,0), mk(T_ERA,0,0)), goal);
      Term f = bind_coord(fr, HEAP[loc(goal)]);
      return check(n->a, f, app2(HEAP[loc(goal)+1], var_of(f))); }
    case S_PLM: {
      if (is_ctr(goal, C_PI) && is_ctr(whnf(HEAP[loc(goal)]), C_ITV)) {   /* a line of types: a λ over the interval whose binder is a name */
        Term f = bind_dim(fr); return check(n->a, f, app2(HEAP[loc(goal)+1], ivar_of(f))); }
      if (!is_ctr(goal, C_PATH)) return fail_mis(path(mk(T_ERA,0,0), mk(T_ERA,0,0), mk(T_ERA,0,0)), goal);
      Term L = HEAP[loc(goal)], a = HEAP[loc(goal)+1], b = HEAP[loc(goal)+2];
      Term f = bind_dim(fr); Term i = ivar_of(f);
      if (!check(n->a, f, app2(L, i))) return false;
      Term body = cell(n->a, f);
      Term b0 = fce3(0, loc(f), body, 0), b1 = fce3(1, loc(f), body, 0);
      if (!eq(b0, a, 0)) return fail_mis(a, b0);
      if (!eq(b1, b, 0)) return fail_mis(b, b1);
      return true; }
    case S_FIX: { Term f = bind_value(fr, 0, goal); HEAP[loc(f)+1] = inst(n->a, f); return check(n->a, f, goal); }
    case S_CASE: return check_case(c, fr, goal);
    case S_SUP: {
      Term nm = n->d ? cell(n->d, fr) : mk(T_IVAR, 0, 0);
      return check(n->a, fr, fce_raw(0, nm, goal, 0)) && check(n->b, fr, fce_raw(1, nm, goal, 0)); }
    case S_HELIM: if (!n->c) {                        /* hrec: the motive is the goal */
        Term xT = infer(n->a, fr); if (!xT) return false; xT = whnf(xT);
        if (tag(xT) != T_CTR || !CINFO[ctr_id(xT)].is_hit) return fail_mis(ctr0(named("HIT", 0)), xT);
        Term P = konst(goal); Term elim = node4(T_HELIM, 0, 0, mk(0, 0, c), fr, mk(T_ERA, 0, 0));
        return check_branches(c, fr, ctr_id(xT), fields_list(xT), P, elim); }
      return verify(c, fr, goal);
    case S_GLUE: {                                    /* glue faces x against Glue A gfaces */
      if (tag(goal) != T_GLU) return fail_mis(goal, mk(T_ERA, 0, 0));
      Term A = HEAP[loc(goal)]; Term gfs = HEAP[loc(goal)+1];
      if (!check(n->b, fr, A)) return false; Term x = cell(n->b, fr);
      int ef = book_find("equiv-fun");
      for (uint32_t l = n->a; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) {
        uint32_t fc = CODE[l].a; uint32_t pc = CODE[fc].a, tc = CODE[fc].b;
        if (!check_itv(pc, fr)) return false;
        Term p = ican(cell(pc, fr)); Term found = 0;
        for (Term g = whnf(gfs); is_ctr(g, C_CONS); g = whnf(HEAP[loc(g)+1])) { Term gf = whnf(HEAP[loc(g)]); if (ieq(ican(HEAP[loc(gf)]), p)) { found = gf; break; } }
        if (!found) return fail_mis(goal, mk(T_ERA, 0, 0));
        Term T = HEAP[loc(found)+1], e = HEAP[loc(found)+2];
        if (!check(tc, fr, T)) return false; Term t = cell(tc, fr);
        FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(p, cells, 64);
        for (int k = 0; k < nc; k++) {
          Term lhs = restrict_cell(ef >= 0 ? app2(app2(ref_of(ef), e), t) : t, &cells[k]), rhs = restrict_cell(x, &cells[k]);
          if (!eq(lhs, rhs, 0)) return fail_mis(rhs, lhs);
        }
      }
      return true; }
    case S_CTR: {
      uint32_t id = n->ext >> 8; uint32_t args[64]; uint32_t na; ctr_args(c, args, &na);
      switch (id) {
        case C_TT: if (is_ctr(goal, C_UNIT)) return true; break;
        case C_TRUE: case C_FALSE: if (is_ctr(goal, C_BOOL)) return true; break;
        case C_ZER: if (is_ctr(goal, C_NAT)) return true; break;
        case C_SUC:
          if (is_ctr(goal, C_NAT)) { uint32_t k = args[0]; while (CODE[k].tag == S_CTR && (CODE[k].ext >> 8) == C_SUC) k = CODE[k].a; return check(k, fr, goal); }
          if (is_ctr(goal, C_EQL)) { Term a = whnf(HEAP[loc(goal)+1]), b = whnf(HEAP[loc(goal)+2]);
            if (is_ctr(a, C_SUC) && is_ctr(b, C_SUC)) return check(args[0], fr, ctr3(C_EQL, HEAP[loc(goal)], HEAP[loc(a)], HEAP[loc(b)])); }
          break;
        case C_NIL: if (is_ctr(goal, C_LIST)) return true; return fail_mis(ctr1(C_LIST, mk(T_ERA,0,0)), goal);
        case C_CONS: if (is_ctr(goal, C_LIST)) return check(args[0], fr, HEAP[loc(goal)]) && check(args[1], fr, goal); break;
        case C_PAIR: if (is_ctr(goal, C_SIG)) { if (!check(args[0], fr, HEAP[loc(goal)])) return false; return check(args[1], fr, app2(HEAP[loc(goal)+1], cell(args[0], fr))); } break;
        case C_REFL: if (is_ctr(goal, C_EQL)) { Term T = HEAP[loc(goal)], a = HEAP[loc(goal)+1], b = HEAP[loc(goal)+2]; (void)T;
            if (!eq(a, b, 0)) return fail_mis(a, b); return true; } break;
        default: break;
      }
      const char *nm = ctor_name(id);
      if (nm[0] == '&' && na == 0 && is_ctr(goal, C_ENUM)) { if (enum_has(goal, id)) return true; return fail_mis(goal, ctr0(id)); }
      if (!strcmp(nm, "Sys") && is_ctr(goal, named("Partial", 2))) {
        Term p = HEAP[loc(goal)], A = HEAP[loc(goal)+1];
        uint32_t faces[64]; uint32_t nf = 0;
        for (uint32_t l = args[0]; CODE[l].tag == S_CTR && (CODE[l].ext >> 8) == C_CONS; l = CODE[l].b) faces[nf++] = CODE[l].a;
        for (uint32_t i = 0; i < nf; i++) {
          uint32_t qc = CODE[faces[i]].a, vc = CODE[faces[i]].b;
          if (!check_itv(qc, fr)) return false;
          FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(cell(qc, fr), cells, 64);
          for (int k = 0; k < nc; k++) { Term f = restrict_frame(fr, &cells[k]); bool ok = check(vc, f, restrict_cell(A, &cells[k])); unrestrict(&cells[k]); if (!ok) return false; }
        }
        for (uint32_t i = 0; i < nf; i++) for (uint32_t j = i + 1; j < nf; j++) {
          Term qr = node2(T_IAND, 0, cell(CODE[faces[i]].a, fr), cell(CODE[faces[j]].a, fr));
          FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(qr, cells, 64);
          for (int k = 0; k < nc; k++) { Term v = restrict_cell(cell(CODE[faces[i]].b, fr), &cells[k]), w = restrict_cell(cell(CODE[faces[j]].b, fr), &cells[k]);
            if (!eq(v, w, 0)) return fail_mis(v, w); }
        }
        FaceCell *pcells = CELLS_POOL[CELLS_TOP++ % 64]; int npc = face_cells(p, pcells, 64);
        for (int k = 0; k < npc; k++) { bool covered = false;
          for (uint32_t i = 0; i < nf && !covered; i++) if (tag(ican(restrict_cell(cell(CODE[faces[i]].a, fr), &pcells[k]))) == T_I1) covered = true;
          if (!covered) return fail_mis(I1c(), p); }
        return true;
      }
      if (!strcmp(nm, "InS") && is_ctr(goal, named("Sub", 3))) {
        Term A = HEAP[loc(goal)], p = HEAP[loc(goal)+1], u = HEAP[loc(goal)+2];
        if (!check(args[0], fr, A)) return false; Term x = cell(args[0], fr);
        FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(p, cells, 64);
        for (int k = 0; k < nc; k++) { Term xa = restrict_cell(x, &cells[k]), ua = restrict_cell(u, &cells[k]); if (!eq(xa, ua, 0)) return fail_mis(ua, xa); }
        return true;
      }
      if (!strcmp(nm, "@Quot/cl") && is_ctr(goal, named("h/Quot", 2))) return check(args[0], fr, HEAP[loc(goal)]);
      if (!strcmp(nm, "@Quot/sq")) { if (is_ctr(goal, C_PI) && is_ctr(whnf(HEAP[loc(goal)]), named("h/Quot", 2))) return true; return fail_mis(goal, ctr0(id)); }
      if (!strcmp(nm, "@Quot/eq") && is_ctr(goal, C_PATH)) {
        Term qt = whnf(app2(HEAP[loc(goal)], I0c()));
        if (is_ctr(qt, named("h/Quot", 2))) { Term A = HEAP[loc(qt)], R = HEAP[loc(qt)+1];
          if (!check(args[0], fr, A) || !check(args[1], fr, A)) return false;
          Term a = cell(args[0], fr), b = cell(args[1], fr);
          if (!check(args[2], fr, app2(app2(R, a), b))) return false;
          if (!eq(HEAP[loc(goal)+1], ctr1(id ? named("@Quot/cl", 1) : 0, a), 0) || !eq(HEAP[loc(goal)+2], ctr1(named("@Quot/cl", 1), b), 0)) return fail_mis(goal, mk(T_ERA,0,0));
          return true; }
      }
      return verify(c, fr, goal); }
    case S_APP: {
      /* a β-redex: the binder is the argument; a spine headed by a built-in eliminator */
      if (CODE[n->a].tag == S_LAM) { VRes e = VERR; Term T = infer(n->b, fr); if (T) return check(CODE[n->a].a, bind_value(fr, cell(n->b, fr), T), goal);
                                     VERR = e; return check(CODE[n->a].a, bind_let(fr, n->b, fr), goal); }
      if (CODE[n->a].tag == S_PLM) { if (!check_itv(n->b, fr)) return false; Term f = bind_dim(fr); return check(CODE[n->a].a, restrict_push(f, ivar_of(f), 2, cell(n->b, fr)), goal); }
      uint32_t sp[64]; uint32_t ns = 0; uint32_t h = c; while (CODE[h].tag == S_APP && ns < 64) { sp[ns++] = CODE[h].b; h = CODE[h].a; }
      for (uint32_t i = 0; i < ns / 2; i++) { uint32_t t = sp[i]; sp[i] = sp[ns-1-i]; sp[ns-1-i] = t; }
      if (CODE[h].tag == S_REF) {
        const char *nm = BOOK[CODE[h].ext].name;
        if (!strcmp(nm, "transp") && ns == 3) {        /* transp(L, φ, x): L is constant on φ */
          if (!check(sp[0], fr, pi(ITV, konst(SET))) || !check_itv(sp[1], fr)) return false;
          Term L = cell(sp[0], fr);
          if (!check(sp[2], fr, app2(L, I0c()))) return false;
          FaceCell *cells = CELLS_POOL[CELLS_TOP++ % 64]; int nc = face_cells(cell(sp[1], fr), cells, 64);
          for (int k = 0; k < nc; k++) {
            Term Lk = restrict_cell(L, &cells[k]); Term dm = dim_push(0); Term body = app2(Lk, ivar_of(dm));
            if (occurs_cell(loc(dm), body)) return fail_mis(app2(Lk, I0c()), body);
          }
          Term T = app2(L, I1c()); if (!eq(T, goal, 0)) return fail_mis(goal, T); return true; }
        if (!strcmp(nm, "trec") && ns == 3) {          /* TRec x pb f: x : Trunc A, f : A → goal, pb : isProp goal */
          Term xT = infer(sp[0], fr); if (!xT) return false; xT = whnf(xT);
          if (!is_ctr(xT, named("h/Trunc", 1))) return fail_mis(ctr1(named("h/Trunc",1), SET), xT);
          Term A = HEAP[loc(xT)];
          if (!check(sp[2], fr, pi(A, konst(goal)))) return false;
          int d = book_find("isProp-ty"); if (d < 0) return fail_ci("isProp-ty");
          return check(sp[1], fr, app2(ref_of(d), goal)); }
        if (!strcmp(nm, "srec") && ns == 3) {          /* CRec x b l */
          if (!check(sp[0], fr, ctr0(named("h/S1", 0)))) return false;
          Term bT = infer(sp[1], fr); if (!bT) return false;
          if (!check(sp[2], fr, path(konst(bT), cell(sp[1], fr), cell(sp[1], fr)))) return false;
          if (!eq(bT, goal, 0)) return fail_mis(goal, bT); return true; }
        if (!strcmp(nm, "qrec") && ns == 4) {          /* QRec x s f resp */
          Term xT = infer(sp[0], fr); if (!xT) return false; xT = whnf(xT);
          if (!is_ctr(xT, named("h/Quot", 2))) return fail_mis(ctr2(named("h/Quot",2), SET, SET), xT);
          Term A = HEAP[loc(xT)], R = HEAP[loc(xT)+1];
          if (!infer(sp[1], fr)) return false;
          if (!check(sp[2], fr, pi(A, konst(goal)))) return false;
          int d = book_find("qresp-ty"); if (d < 0) return fail_ci("qresp-ty");
          return check(sp[3], fr, app2(app2(app2(app2(ref_of(d), A), R), cell(sp[2], fr)), goal)); }
      }
      if (CODE[h].tag == S_CASE) {                     /* (app (case …) x): the case at the function type */
        Term xT = infer(sp[ns-1], fr); if (!xT) return false;
        if (ns == 1) return check(h, fr, pi(xT, konst(goal)));
      }
      return verify(c, fr, goal); }
    case S_NUM: { unsigned k = num_kind_of(goal); if (k == n->ext) return true; if (k != 99) return fail_mis(goal, num_type(n->ext)); return verify(c, fr, goal); }
    case S_VAR: if (!CTX_TY[n->ext] && CTX_LET_CODE[n->ext]) return check(CTX_LET_CODE[n->ext], CTX_LET_FR[n->ext], goal); return verify(c, fr, goal);
    default: return verify(c, fr, goal);
  }
}

/* ---- the entry: every definition, type against Set then term against type ------------------ */
static void report_err(const char *name) {
  printf("\x1b[31m✗ %s\x1b[0m\n", name);
  if (VERR == V_CANTINFER) printf("  cannot infer%s%s\n", VERR_MSG ? ": " : "", VERR_MSG ? VERR_MSG : "");
  else { printf("  mismatch: expected "); print_term(VERR_WANT, 12); printf("\n            got      "); print_term(VERR_GOT, 12); printf("\n"); }
}
int check_book(const char *prefix) {
  CHECK_MODE = true; REWRITE_HOOK = rewrite_hook; cells_init();
  if (getenv("HYPER_DEBUG") || getenv("HYPER_EQDBG") || getenv("HYPER_TRACE")) setvbuf(stdout, NULL, _IONBF, 0);
  C_ITV = ctor_intern("Itv", 0); SET = ctr0(C_SET); ITV = ctr0(C_ITV); int kd = book_find("konst"); konst_ref = kd >= 0 ? ref_of(kd) : 0;
  int bad = 0;
  for (uint32_t i = 0; i < BOOK_LEN; i++) {
    if (prefix && strncmp(BOOK[i].name, prefix, strlen(prefix))) continue;
    if (!BOOK[i].type) continue;
    if (BOOK[i].unknown) { NRW = 0; VERR = V_OK; Term fr = 0; uint32_t ty = skip_dims(BOOK[i].type, &fr);
      if (check(ty, fr, SET)) printf("\x1b[32m✓ %s : a coordinate of its type\x1b[0m\n", BOOK[i].name + (prefix ? strlen(prefix) : 0)); else { bad++; report_err(BOOK[i].name + (prefix ? strlen(prefix) : 0)); }
      continue; }
    NRW = 0; VERR = V_OK;
    Term fr = 0; uint32_t ty = skip_dims(BOOK[i].type, &fr);
    bool ok = check(ty, fr, SET);
    if (getenv("HYPER_TRACE")) fprintf(stderr, "type of %s: %s\n", BOOK[i].name, ok ? "ok" : "FAIL");
    if (ok) { Term fr2 = 0; uint32_t tm = skip_dims(BOOK[i].code, &fr2); ok = check(tm, fr2, inst(BOOK[i].type, 0)); }
    if (ok) printf("\x1b[32m✓ %s\x1b[0m\n", BOOK[i].name + (prefix ? strlen(prefix) : 0));
    else { bad++; report_err(BOOK[i].name + (prefix ? strlen(prefix) : 0)); }
  }
  return bad;
}

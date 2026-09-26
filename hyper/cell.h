/* hyper — the Parallel Univalent Superposition Computer.  cell.h: the word.
 *
 * MAP.md §1.  One data structure: a heap of cells over bound dimension names.
 * A Port is one word:  tag:8 | ext:24 | loc:32.  A node is a block at loc.
 * A Name is the heap address of the frame that bound it, so two instances of
 * one definition never share a name (the label-capture finding).
 */
#ifndef HYPER_CELL_H
#define HYPER_CELL_H
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>

typedef uint64_t Term;
typedef uint32_t Loc;

/* ---- tags ------------------------------------------------------------- */
enum Tag {
  /* points and maps */
  T_VAR = 1,   /* ext = de Bruijn level, loc = frame               */
  T_LAM,       /* loc → [code, frame]              closure          */
  T_APP,       /* loc → [fun, arg]                  ● fun            */
  T_REF,       /* loc = book index                  a NAME (value)   */
  T_ERA,       /* the one address of loss                             */
  /* lines: one notion of dimension */
  T_SUP,       /* loc → [name, a, b]                a 1-cell by faces */
  T_PLM,       /* loc → [code, frame]              a 1-cell by formula (binds a dim) */
  T_FCE,       /* ext = side (0/1) or 2, loc → [name, target, by]  the face map, or the substitution name := by */
  /* the interval */
  T_I0, T_I1,  /* no node                                              */
  T_IVAR,      /* loc = name                                           */
  T_INOT,      /* loc → [a]                                            */
  T_IAND,      /* loc → [a, b]                                         */
  T_IOR,       /* loc → [a, b]                                         */
  T_IDNF,      /* ext = ncubes, loc → cubes: [nlits, lit…]…  canonical interval (antichain of cubes) */
  /* data; a type is a CTR cell with a reserved constructor id */
  T_CTR,       /* ext = ctor id (16) | arity (8), loc → fields         */
  T_NUM,       /* ext = kind (N_U64, N_I64, N_F64, N_CHR), loc → [u64 bits] */
  T_OP2,       /* ext = op, loc → [a, b]            ● a then ● b       */
  T_OP1,       /* ext = op, loc → [a]               ● a                */
  T_POUT,      /* loc → [u]  pout of a system: the branch of a true face; stuck otherwise */
  /* Kan */
  T_TRP,       /* loc → [line, r, s, x]             ● line            */
  T_HCM,       /* loc → [type, base, faces]           ● faces          */
  T_GLU,       /* loc → [base, gfaces]  Glue A [(φ,T,e)…]  a type cell     */
  T_GLUE,      /* loc → [faces, a]      glue [(φ,t)…] a                     */
  T_UNGLUE,    /* loc → [g]             ● g                                 */
  T_FCASE,     /* loc → [phi, a, b]     a if phi ≡ I1, b if I0, else stuck   */
  T_GBASE,     /* loc → [G]  the base of a Glue type; a non-Glue type is its own base  */
  T_GFACES,    /* loc → [G]  the faces of a Glue type; a non-Glue type has none        */
  /* static-code eliminators instantiated on the heap */
  T_CASE,      /* loc → [scrut, code, frame]        ● scrut           */
  T_PROJ,      /* ext = field index, loc → [x]      ● x  (fst/snd of any constructor) */
  T_HELIM,     /* loc → [scrut, code, frame, motive]  ● scrut; scrut 0 = a function awaiting its point;
                  motive ERA = the recursor (stuck on a composite)                                    */
  T_CFIELDS,   /* loc → [x]        the fields of a constructor cell, as a list                        */
  T_CWITH,     /* loc → [x, list]  the constructor of x rebuilt with these fields                     */
  T_PAP,       /* loc → [p, i, a, b]  p @ i knowing the endpoints a, b: a literal i selects one; a symbolic i
                  stays a cell a later face decides (a reduction that forgot the boundary would not commute) */
  /* the interaction */
  T_ASK,       /* loc → [q, k]                      a free port        */
  T_UNIFY,     /* loc → [x, y, faces]   the identity x ≡ y between data terms, decided by unification under the branch's faces */
  T_BOTH,      /* loc → [p, q, last forced, faces]  both identities hold: fair, either dead side kills */
  T_TRACE,     /* loc → [e]   the run of e to its normal form, as a term: the value with the ledger's events over it */
  T_LEAVES,    /* loc → [e]   the leaves of e's superposition, as a list */
  T_IND,       /* word 0 of a reduced node: word 1 holds its result (§3: a demanded port fires once, every holder sees the value) */
  /* frames (never a value) */
  T_FRAME,     /* loc → [parent, slot]  ext = depth   one binding      */
  T_DIM,       /* loc → [parent, unused] ext = depth  a bound dimension: its loc is the NAME */
  T_RESTRICT,  /* loc → [parent, name, by] ext = side  a face (or substitution) taken on a closure's frame */
  T_TAGS
};

static inline Term  mk(unsigned tag, uint32_t ext, Loc loc) {
  return ((Term)tag << 56) | ((Term)(ext & 0xFFFFFFu) << 32) | (Term)loc;
}
static inline unsigned tag(Term t) { return (unsigned)(t >> 56); }
static inline uint32_t ext(Term t) { return (uint32_t)((t >> 32) & 0xFFFFFFu); }
static inline Loc      loc(Term t) { return (Loc)t; }

/* ---- constructor ids (a type is a point of Set) ------------------------ */
enum Ctor {
  C_USER = 0,        /* user constructors are looked up by name, ids ≥ C_USER_BASE */
  C_SET = 1, C_PI, C_SIG, C_PATH, C_EQL, C_NAT, C_BOOL, C_UNIT, C_EMPTY, C_LIST,
  C_ENUM, C_NUMTY, C_GLU, C_PAIR, C_REFL, C_CONS, C_NIL, C_FACE, C_ZER, C_SUC, C_TRUE, C_FALSE, C_TT, C_GFACE,
  C_USER_BASE = 64
};
static inline uint32_t ctr_ext(uint32_t id, uint32_t arity) { return (id << 8) | (arity & 0xFF); }
static inline uint32_t ctr_id(Term t)    { return ext(t) >> 8; }
static inline uint32_t ctr_arity(Term t) { return ext(t) & 0xFF; }

/* ---- ops ---------------------------------------------------------------- */
enum Op { OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_MOD, OP_EQ, OP_NE, OP_LT, OP_LE, OP_GT, OP_GE,
          OP_AND, OP_OR, OP_XOR, OP_LSH, OP_RSH, OP_POW, OP_COUNT };

/* ---- static code (the BOOK) ------------------------------------------- */
/* Static terms live in an immutable arena; binders are de Bruijn levels.  */
enum STag {
  S_VAR = 1, S_LAM, S_APP, S_REF, S_ERA, S_SUP, S_PLM, S_DIM, S_FCE,
  S_I0, S_I1, S_IVAR, S_INOT, S_IAND, S_IOR,
  S_CTR, S_NUM, S_OP2, S_TRP, S_HCM, S_CASE, S_BRANCH, S_ASK, S_LET, S_PROJ, S_GLU, S_GLUE, S_UNGLUE, S_FCASE, S_GBASE, S_GFACES, S_ISUB,
  S_HELIM, S_CFIELDS, S_CWITH, S_FIX, S_OP1, S_POUT, S_PAP, S_TRACE, S_LEAVES
};
enum NumKind { N_U64 = 0, N_I64, N_F64, N_CHR };
enum Op1 { OP1_NOT, OP1_NEG, OP1_TOCHAR };
typedef struct SNode {
  uint8_t  tag;
  uint32_t ext;        /* level / op / ctor ext / side / count */
  uint32_t a, b, c, d; /* child indices into the arena (0 = none) */
  uint32_t kids;       /* S_CTR with arity > 4: index into KIDS of `arity` children */
  uint64_t num;        /* S_NUM */
} SNode;

typedef struct Def {
  const char *name;
  uint32_t    code;    /* static index of the body */
  uint32_t    type;    /* static index of the type, 0 if none */
  uint32_t    ndims;   /* implicit dimension binders at the top */
  bool        unknown; /* declared with a type and no body: a coordinate of its type, created once on demand */
  Term        coord;   /* that coordinate, once created */
} Def;
/* ---- the machine ----------------------------------------------------- */
extern Term    *HEAP;   extern Loc HEAP_LEN;
extern SNode   *CODE;   extern uint32_t CODE_LEN;
extern uint32_t *KIDS;  extern uint32_t KIDS_LEN;
extern Def     *BOOK;   extern uint32_t BOOK_LEN;
extern const char **BNAMES; extern uint32_t BNAMES_LEN;   /* field names of case branches (S_BRANCH.num = index), for presentation */
extern uint64_t ITRS;
extern uint32_t *TRACE; extern uint64_t TRACE_LEN;   /* receipts: rule ids */
extern Loc      *TRACE_NODE;                          /* the node each receipt fired on */
extern Loc      *TRACE_HEAP;                          /* the heap length at each receipt: the words an event allocated are the gap to the next */
extern const char *RULE_NAME[];                       /* the census names, by rule */
void print_trace(uint64_t from);                      /* the receipts from index `from` as rule@node */

/* the events.  Those of the superposition algebra are named as research/sat_fibre/InteractionLedger.agda names them
   (Event: dupSupEqual, dupSupDifferent, dupLamUsed, dupLamErased, dupNode, appSup, appMatSup): the correspondence from
   this loop's transitions to that alphabet, which the ledger asks a runtime to supply.  The rest are this machine's own. */
enum RuleId { R_BETA = 1, R_APP_SUP, R_APP_PLM, R_DUP_SUP_EQUAL, R_DUP_SUP_DIFFERENT, R_DUP_LAM_USED, R_DUP_LAM_ERASED, R_DUP_NODE,
              R_FCE_SHARE, R_CASE, R_CASE_SUP, R_OP2, R_OP2_SUP, R_ERASE, R_TRP, R_HCM,
              R_HCON, R_HELIM, R_HELIM_SUP, R_HELIM_HCM, R_OP1, R_POUT, R_SPLIT, R_UNIFY, R_COUNT };

/* ---- the HIT schema (§4): nothing per HIT is hardcoded; a constructor's boundary IS its type ---- */
typedef struct CtorInfo {
  bool     is_hit;     /* this constructor id names a higher inductive TYPE */
  uint32_t nparams;    /* … with this many parameters */
  bool     carries;    /* its constructors carry the parameters as leading fields (the emitter's convention);
                          otherwise the parameters are not fields of its constructors */
  uint32_t hit;        /* for a constructor of a HIT: the type's id (0 otherwise) */
  int      type_def;   /* the book entry holding its closed type: Pi params. Pi fields. T ps | Path … */
  uint32_t nfields, dim;
} CtorInfo;
extern CtorInfo CINFO[1 << 16];   /* indexed by constructor id */

Loc  alloc(uint32_t n);
Term whnf(Term t);
Term normalize(Term t, int depth);
Term nf(Term t, int depth);         /* the normal form as the top demands it: rounds and pruning */
void print_term(Term t, int depth);
Term inst(uint32_t code, Term frame);
Term run_def(uint32_t id);
Term iwhnf(Term t);
void load_prelude(void);
extern int RULE_TRP[256], RULE_HCM[256];   /* prelude rule per type constructor id, -1 if none */
int  book_find(const char *name);
const char *ctor_name(uint32_t id);
uint32_t ctor_intern(const char *name, uint32_t arity);
/* the cell constructors and frame operations, shared with verify.c */
Term node1(unsigned t, uint32_t e, Term a);
Term node2(unsigned t, uint32_t e, Term a, Term b);
Term node3(unsigned t, uint32_t e, Term a, Term b, Term c);
Term node4(unsigned t, uint32_t e, Term a, Term b, Term c, Term d);
Term fce_raw(unsigned side, Term name, Term target, Term by);
Term fce3(unsigned side, Loc name, Term target, Term by);
uint32_t next_depth(Term parent);
Term frame_push(Term parent, Term slot);
Term dim_push(Term parent);
Term restrict_push(Term parent, Term name, unsigned side, Term by);
Term generic(Term fr);
Term coordinate(Term type);

Term coordinate_type(Term v);
uint32_t type_constructors(Term T, Term *alts, uint32_t max, Term world);   /* the constructors of a data type from its declaration, fields fresh coordinates */
Term frame_lookup(Term f, uint32_t lvl, bool *is_dim);
bool frame_is_dim(Term f, uint32_t lvl);
bool code_uses(uint32_t c, uint32_t lvl);
Term open_closure(Term clo, Term arg);          /* the body of a λ or <i> at an argument, uncomputed */
Term ican(Term t);
bool ieq(Term a, Term b);
Term spine(Term t, Term *args, uint32_t *n);
Term apps(Term f, Term *args, uint32_t n);
Term app2(Term f, Term a);
Term ref_of(int id);
Term nil_cell(void);
Term cons_cell(Term h, Term t);
Term fields_list(Term ctr);
/* the DNF cells of a face formula: each cell is a list of (name, side) literals; returns the count, -1 if not an interval */
typedef struct FaceCell { uint32_t n; Loc name[32]; unsigned side[32]; } FaceCell;
int face_cells(Term phi, FaceCell *out, int max);
int  collapse_leaves(Term t, Term *out, int max);   /* the leaves of a superposition, in collapse order */
char *term_string(Term t, int depth);           /* a value as its printed text */
void print_census(void);               /* §6: the receipts by rule (the trace is the retained history) */


#endif

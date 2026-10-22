/* core.h — the cubical interaction net.
 *
 * A term is a net of cells. Every cell has one principal port (port 0).
 * Values (V_*) have a positive principal port: they provide. Operations
 * (O_*) have a negative principal port: they consume one value there. An
 * active pair is an operation's principal port wired to a value's principal
 * port; its rule replaces the two cells by a net on their auxiliary wires.
 * Sharing is the duplicator O_DUP; erasure is O_ERA; substitution of
 * dimensions is O_SUBST. Intervals and faces are values carrying immutable
 * DNF payloads; a face clause is a substitution of endpoints, so being under
 * a face is reindexing and no cell consults an ambient context.
 */
#ifndef CORE_H
#define CORE_H
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

/* ---------------- dimensions, intervals, faces, substitutions ---------------- */
typedef uint32_t Dim;
/* a clause: sorted literals. Interval literal = dim<<1 | negated;
 * face literal = dim<<1 | endpoint. */
/* Payloads are immutable and reference counted; functions borrow their
 * arguments and return references their callers own; a cell owns its payload. */
typedef struct { uint32_t rc, n; uint32_t l[]; } Clause;
typedef struct { uint32_t rc, n; Clause *c[]; } Dnf;     /* join of clauses (or a system's clause list) */
typedef struct { uint32_t rc, n; Dim *d; Dnf **v; } Subst;
extern long stat_payloads;
Clause *clause_retain(Clause *c);
void clause_release(Clause *c);
Dnf *dnf_retain(Dnf *d);
void dnf_release(Dnf *d);
Subst *subst_retain(Subst *s);
void subst_release(Subst *s);
Dnf *clause_list(Clause *const *c, uint32_t n);

Dim  fresh_dim(void);
Dnf *dnf_zero(void);
Dnf *dnf_one(void);
Dnf *iv_atom(Dim i);
bool dnf_is_zero(const Dnf *x);
bool dnf_is_one(const Dnf *x);
bool dnf_mentions(const Dnf *x, Dim i);
bool clause_mentions(const Clause *c, Dim i);
Dnf *dnf_meet(const Dnf *x, const Dnf *y, bool face);
Dnf *dnf_join(const Dnf *x, const Dnf *y, bool face);
Dnf *iv_neg(const Dnf *x);
Dnf *iv_subst(const Dnf *x, const Subst *s);
Dnf *face_eq(const Dnf *r, int eps);           /* the face (r = eps) */
Dnf *face_subst(const Dnf *f, const Subst *s);
Dnf *face_of_clause(const Clause *c);
bool dnf_equal(const Dnf *x, const Dnf *y);
Dnf *face_forall(const Dnf *f, Dim i);
Dnf *face_of_clauses(const Dnf *list);
Subst *subst_single(Dim i, const Dnf *r);
Subst *subst_of_clause(const Clause *c);
Subst *subst_then_clause(const Subst *s, const Clause *d); /* x ↦ s(x)[d], then d */
bool  subst_range_mentions(const Subst *s, Dim j);
Subst *subst_without(const Subst *s, Dim j);
Subst *subst_with(const Subst *s, Dim j, const Dnf *r);
Subst *subst_compose(const Subst *s, const Subst *t); /* s, then t */
Subst *subst_id(void);
const Dnf *subst_get(const Subst *s, Dim j);
typedef const char *(*DimName)(Dim);
void dnf_print(FILE *o, const Dnf *x, bool face, DimName nm);
void clause_print(FILE *o, const Clause *c, DimName nm);

/* ---------------- cells ---------------- */
enum {
    /* values: positive principal port */
    V_LAM = 1,  /* p=Record; ports 1.. = environment */
    V_PAIR,     /* 1=a 2=b */
    V_PI,       /* 1=A 2=B (a λ) */
    V_SIGMA,    /* 1=A 2=B (a λ) */
    V_U,        /* 1=level */
    V_PATHP,    /* 1=A (a line) 2=a 3=b */
    V_PLAM,     /* a=dim; 1=body */
    V_IV,       /* p=Dnf (interval) */
    V_FACE,     /* p=Dnf (face) */
    V_SYS,      /* p=Dnf (the branches' clauses, in order; NULL when none); ports 1.. = branch values */
    V_GLUE,     /* 1=A 2=S (a SYS of (T,e)) */
    V_GLUEV,    /* 1=S (a SYS) 2=a */
    /* neutrals: the last port is the neutral's type (V_UNK when unknown);
     * ty=1 when it is known */
    V_NVAR,     /* a=name; 1=type */
    V_NAPP,     /* 1=f 2=arg 3=type */
    V_NFST, V_NSND, /* 1=p 2=type */
    V_NPAPP,    /* p=Dnf r, x=annotated; 1=p [2=a 3=b] type */
    V_NCOMP,    /* 1=A 2=u 3=a0 4=type */
    V_NUNGLUE,  /* 1=S 2=b 3=type */
    V_NCASE,    /* p=CaseTab, x=has motive; 1=scrutinee [2=motive] environment, type */
    V_NTRANS,   /* a=data type, p=Dnf ψ; 1=x 2..k+1=parameter lines, type */
    V_GLOBAL,   /* a=global id */
    V_SITEF,    /* a=L, x=arguments so far; 1..x=the arguments */
    V_DEFER,    /* a=g, x=flags, p=Subst or NULL; 1..n=arguments: g applied to them
                 * (then substituted by p), built when eliminated */
    V_UNK,      /* an unknown type */
    V_DATA,     /* a=data type; 1..k=parameters */
    V_CON,      /* a=constructor; 1..f=fields, then the dimensions (interval values) */
    V_HCOMP,    /* formal homogeneous composition in a data type: 1=tube 2=cap */
    V_CASEF,    /* p=CaseTab, x=has motive; [1=motive] environment: the elimination as a function */
    V_REF,      /* p=Box: a reference to a value held once; copying it copies the reference, an operation
                 * meeting it copies the value out (as a definition is unfolded) */
    V_WORD,     /* a=the number: a machine word, one cell */
    V_WSUSP,    /* 1=z 2=s 3=a word: the elimination of that word, computed when used (a hypothesis) */
    V_SUSP,     /* p=CaseTab, x=has motive; 1=field [2=motive] environment: an induction hypothesis, the
                 * elimination of a recursive field, computed when forced */
    V_END,
    /* operations: negative principal port; the last port is the result */
    O_APP,      /* 0=f 1=arg 2=out */
    O_FORCE,    /* 0=thunk 1=out */
    O_FST, O_SND, /* 0=p 1=out */
    O_PAPPR,    /* x=annotated; 0=r 1=p [2=a 3=b] out */
    O_PAPPP,    /* p=Dnf r, x=annotated; 0=p [1=a 2=b] out */
    O_SUBST,    /* p=Subst; 0=value 1=out */
    O_DUP,      /* 0=value 1=out 2=out */
    O_ERA,      /* 0=value */
    O_COMP,     /* 0=u 1=A 2=a0 3=out */
    O_COMPA,    /* 0=A 1=u 2=a0 3=out */
    O_COMPH,    /* a=dim; 0=H 1=u 2=a0 3=out */
    O_MKPLAM,   /* a=dim; 0=body 1=out */
    O_MKGLUE,   /* 0=S 1=A 2=out */
    O_MKGLUEV,  /* 0=S 1=a 2=out */
    O_UNGLUE,   /* 0=S 1=b 2=out */
    O_UNGLUE2,  /* 0=b 1=S 2=out */
    O_FACEOF,   /* 0=s 1=out */
    O_NEG,      /* 0=r 1=out */
    O_BIN,      /* x=B_*; 0=a 1=b 2=out */
    O_BIN2,     /* x=B_*, p=Dnf a; 0=b 1=out */
    O_FEQ,      /* a=eps; 0=r 1=out */
    O_FORALL,   /* a=dim; 0=φ 1=out */
    O_SYSCONS,  /* 0=φ 1=t (thunk) 2=rest 3=out */
    O_SYSCONS2, /* p=Dnf φ; 0=rest 1=t 2=out */
    O_SYSMAP,   /* 0=s 1=f 2=out */
    O_TPART,    /* a=k; 0=a type 1=out: the type's k-th component */
    O_CONCHK,   /* a=constructor; 0=its boundary's face 1=the boundary 2..=fields, dims; out */
    O_HCOMP,    /* 0=tube 1=cap 2=out: a formal hcomp unless the tube is total */
    O_TRANSD1,  /* a=data type; 0=ψ 1..k=parameter lines k+1=x out */
    O_TRANSD2,  /* a=data type, p=Dnf ψ; 0=x 1..k=parameter lines out */
    O_CASE,     /* p=CaseTab, x=has motive; 0=scrutinee [1=motive] environment, out. Meeting a
                 * constructor it builds the selected branch's body: one interaction */
    /* the values as data, for terms about terms (the checker): */
    O_VIEW,     /* 0=value 1=out: the value's head as a View constructor (lib/code.ctt), its parts the
                 * value's own ports */
    O_MKVAR,    /* a=count; 0=level (Num) 1=type 2=out: the variable at that level */
    O_MKDIM,    /* a=count; 0=level (Num) 1=out: the dimension at that level */
    O_IEQ,      /* 0=r 1=s 2=out */
    O_IEQB,     /* p=Dnf r; 0=s 1=out: r = s, a Bool */
    O_FEQL,     /* 0=a 1=b 2=out */
    O_FEQLB,    /* p=Dnf a; 0=b 1=out: a = b as faces, a Bool */
    O_CLAUSES,  /* 0=face 1=out: its clauses, each a face, as a list */
    O_RESTRICT, /* 0=a clause (a face) 1=value 2=out: the value under the clause */
    O_GLOB,     /* x=table, a=count; 0=index (Num) 1=out: an entry of the checker's tables, a reference */
    O_ABS,      /* a=count; 0=level (Num) 1=value 2=out: the line binding the dimension at that level */
    O_NTYPE,    /* 0=a neutral 1=out: its type, computed from its spine (only a variable stores one) */
    O_CALL,     /* 0=a definition 1..n=arguments out: a definition applied to its arguments; with all
                 * its parameters, its body is built in one interaction */
    O_WSUCC,    /* 0=w 1=out: w + 1 */
    O_WEQ, O_WLT, O_WADD, O_WMAX, O_WSUB,  /* 0=a 1=b 2=out: on words; first a, then b */
    O_WOP2,     /* x=the operation, a=a; 0=b 1=out */
    O_WELIM,    /* (%welim w z s): 0=w 1=z 2=s 3=out: #0 ↦ z, #(n+1) ↦ s #n (the elimination of #n) */
    O_PEND,     /* p=Dnf r (0 or 1); 0=the type of p 1=p 2=out: p r, an endpoint when the type is a path type */
    O_CLOS,     /* 0=f 1=g 2=out */
    O_CLOS2,    /* 0=g 1=f 2=out: (csame pairs) when f, g are λs of one record, the pairs of their
                 * environments; else (cdiff f g), both untouched */
    O_BRANCH,   /* 0=an elimination (V_CASEF) 1=constructor (Num) 2=parameters (a list) 3=out */
    O_BRANCHC,  /* p=CaseTab, a=count; 0=constructor (Num) 1=parameters, then the environment, out */
    O_BRANCHL,  /* p=CaseTab, a=constructor, x=parameters read; 0=the rest of the list, then the
                 * environment, then the parameters read, out: branch a at the parameters */
    O_ROOT,     /* 0: an observation; never interacts */
    K_END
};
enum { B_MEET, B_JOIN, B_FAND, B_FOR };

typedef uint64_t Port;            /* cell pointer << 16 | port index; 0 = none */
typedef struct Cell {
    uint16_t kind, n;             /* n = number of ports */
    uint32_t x;
    uint32_t lk, ty;              /* lk: the cell's lock (HANDOFF §20), never reset; ty: a neutral's type is known */
    uint64_t a;
    void *p;
    Port port[];
} Cell;

static inline Port P(Cell *c, int k) { return ((uint64_t)(uintptr_t)c << 16) | (uint64_t)k; }
static inline Cell *PC(Port p) { return (Cell *)(uintptr_t)(p >> 16); }
static inline int PI(Port p) { return (int)(p & 0xffff); }
static inline bool is_value(int k) { return k > 0 && k < V_END; }

Cell *cell(int kind, int n);
void cell_free(Cell *c);
void link(Port a, Port b);
void net_start(int workers);       /* worker threads besides the caller */
void net_push(Cell *op, Cell *v);  /* enqueue an active pair */
bool net_observe(Cell *root, long limit); /* reduce until root's port holds a value (root NULL: until no pair is pending); workers then pause */
void net_drain(void);
Cell *global_res(long g);          /* the cell holding a definition's value */
/* an application of a definition with declared identities: true when the
 * application was rewired (it follows an identity, or collects arguments) */
bool site_open(Cell *app, Cell *glob);
void site_apply(Cell *app, Cell *sitef);
void defer_force(Cell *op, Cell *deferred);
#define X_SITED 0x80000000u       /* an application that does not follow identities */

/* data types (higher inductive types, Coquand–Huber–Mörtberg): declared by
 * (data ...); the net's rules are generic over these tables */
typedef struct { char *name; int data, index, nfields, ndims; long bdy, trans; int nrec; uint64_t recmask; } ConInfo;
/* bdy, trans: globals or -1; recmask: the fields of type the data type itself (recursive), nrec of them */
typedef struct { char *name; int nparams, ncons; int *cons; long comp, transh; void *decl; } DataInfo;   /* decl: the (data ...) form */
extern ConInfo *CON;
extern DataInfo *DATA;
extern long case_hcomp_global;
/* an elimination's branches: one record per constructor, parameters its fields, [the induction
 * hypotheses of its recursive fields when mask has the branch,] its dimensions; environment the
 * variables the branches share, supplied once by the case cell's ports */
/* variables and dimensions at de Bruijn levels, made by %var and %dim and read by %view */
#define LVL_TAG (1ull << 62)
#define DIM_LVL 0x40000000u
int data_checked_index(int d);     /* a data type's index in the checker's signature, or -1 */
int con_index(const char *name);   /* a constructor by name, or -1 */
enum { TB_VAL, TB_TY, TB_DTAB, TB_DENT, TB_N };
long table_global(int table, long i);  /* the global holding entry i of a checker table, or -1 */
/* a definition's body as one record taking all its parameters (NULL when it is not a λ), and
 * whether applications of it follow declared identities */
struct Record *global_nary(long g);
bool global_sited(long g);
typedef struct Box { struct Cell *root; long rc; } Box;
typedef struct CaseTab { int d, nenv; uint64_t mask; struct Record **br; } CaseTab;
Port con_build(int c, const Port *fields, const Port *dims);
Port apply_gid(long g, const Port *args, int n);

/* readings */
extern long stat_steps, stat_kind[K_END];
extern long stat_cells;

/* ---------------- compiled syntax ---------------- */
enum {
    S_VAR, S_LAM, S_APP, S_PAIR, S_FST, S_SND, S_PI, S_SIGMA, S_U, S_PATHP, S_PLAM, S_PAPP,
    S_IV0, S_IV1, S_NEG, S_BIN, S_FEQ, S_FTT, S_FFF, S_FORALL, S_FACEOF, S_SYS0, S_SYSCONS,
    S_SYSMAP, S_COMP, S_GLUE, S_GLUEV, S_UNGLUE, S_GLOBAL, S_AXIOM, S_LET, S_FORCE,
    S_DATA, S_CON, S_HCOMPD, S_TRANSD, S_CASE,  /* id: the data type or constructor; S_CASE: tab */
    S_PRIM,     /* x=the operation cell, n operands */
    S_GLOBTAB,  /* x=the table; k[0]=the index */
    S_BOX,      /* k[0]: the value, held once and referred to */
    S_WORD,     /* id: a word literal #n */
    S_CALL      /* id: the definition; k: its arguments */
};
struct Record;
typedef struct Syn {
    int tag, n, slot;
    uint32_t x;
    long id;
    struct Record *rec;
    struct CaseTab *tab;
    struct Syn **k;
} Syn;   /* S_AXIOM: slot = the global holding its type, or -1 */
/* a binder level: λ (one parameter), thunk (none), or a case branch (its fields, hypotheses and
 * dimensions, in slots 0..nparam-1). Its frame has slots: the parameters, the environment (maximal subterms free of this level,
 * lifted to the enclosing level and wired to the cell's ports), and locals. */
typedef struct Record {
    int nparam, nslots, nenv;
    int *env_slot;
    int *uses;          /* occurrences of each slot in the body */
    Syn *body;
    int where;          /* the definition it was compiled in (CUBICAL_PROFILE) */
} Record;
/* profile: applications of λs and forcings of thunks, by the definition they were compiled in */
extern long *prof_count, *prof_dup; extern const char **prof_name; extern int prof_n, prof_on; extern long prof_dupk[64], prof_erak[64], prof_con[4096], prof_glob[65536];

/* build the body of r: param (or 0), env providers; returns the provider */
Port record_build(const Record *r, Port param, const Port *env);
Port record_build_n(const Record *r, const Port *params, const Port *env);
void port_split(Port prov, int m, Port *out);
/* build a top-level body with its own slots */
Port top_build(Syn *body, int nslots, const int *uses);

/* globals: each definition's net is built once; a use copies its value */
Port global_copy(long g);          /* 0 when the global is an unsupplied input */
void global_park(long g, Cell *op, Cell *glob);
long global_lookup(const char *name);
const char *name_of(long id);

#endif

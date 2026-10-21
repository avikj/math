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
typedef struct { uint32_t n; uint32_t l[]; } Clause;
typedef struct { uint32_t n; Clause *c[]; } Dnf;     /* join of clauses */
typedef struct { uint32_t n; Dim *d; Dnf **v; } Subst; /* sorted by dim */

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
Dnf *face_forall(const Dnf *f, Dim i);
Dnf *face_of_clauses(Clause *const *c, uint32_t n);
Subst *subst_single(Dim i, Dnf *r);
Subst *subst_of_clause(const Clause *c);
Subst *subst_then_clause(const Subst *s, const Clause *d); /* x ↦ s(x)[d], then d */
bool  subst_range_mentions(const Subst *s, Dim j);
Subst *subst_without(const Subst *s, Dim j);
Subst *subst_with(const Subst *s, Dim j, Dnf *r);
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
    V_U,
    V_PATHP,    /* 1=A (a line) 2=a 3=b */
    V_PLAM,     /* a=dim; 1=body */
    V_IV,       /* p=Dnf (interval) */
    V_FACE,     /* p=Dnf (face) */
    V_SYS,      /* p=Clause*[]; ports 1.. = branch values, each under its clause */
    V_GLUE,     /* 1=A 2=S (a SYS of (T,e)) */
    V_GLUEV,    /* 1=S (a SYS) 2=a */
    V_NVAR,     /* a=name */
    V_NAPP,     /* 1=f 2=arg */
    V_NFST, V_NSND, /* 1=p */
    V_NPAPP,    /* p=Dnf r, x=annotated; 1=p [2=a 3=b] */
    V_NCOMP,    /* 1=A 2=u 3=a0 */
    V_NUNGLUE,  /* 1=S 2=b */
    V_GLOBAL,   /* a=global id */
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
    O_ROOT,     /* 0: an observation; never interacts */
    K_END
};
enum { B_MEET, B_JOIN, B_FAND, B_FOR };

typedef uint64_t Port;            /* cell pointer << 16 | port index; 0 = none */
typedef struct Cell {
    uint16_t kind, n;             /* n = number of ports */
    uint32_t x;
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
long net_run(long limit);
void net_push(Cell *op, Cell *v);  /* re-enqueue an active pair */          /* reduce until no active pair (or limit); returns steps */

/* readings */
extern long stat_steps, stat_kind[K_END];
extern long stat_cells;

/* ---------------- compiled syntax ---------------- */
enum {
    S_VAR, S_LAM, S_APP, S_PAIR, S_FST, S_SND, S_PI, S_SIGMA, S_U, S_PATHP, S_PLAM, S_PAPP,
    S_IV0, S_IV1, S_NEG, S_BIN, S_FEQ, S_FTT, S_FFF, S_FORALL, S_FACEOF, S_SYS0, S_SYSCONS,
    S_SYSMAP, S_COMP, S_GLUE, S_GLUEV, S_UNGLUE, S_GLOBAL, S_AXIOM, S_LET
};
struct Record;
typedef struct Syn {
    int tag, n, slot;
    uint32_t x;
    long id;
    struct Record *rec;
    struct Syn **k;
} Syn;
/* a binder level: λ (one parameter) or thunk (none). Its frame has slots:
 * the parameter, the environment (maximal subterms free of this level,
 * lifted to the enclosing level and wired to the cell's ports), and locals. */
typedef struct Record {
    int nparam, nslots, nenv;
    int *env_slot;
    int *uses;          /* occurrences of each slot in the body */
    Syn *body;
} Record;

/* build the body of r: param (or 0), env providers; returns the provider */
Port record_build(const Record *r, Port param, const Port *env);
/* build a top-level body with its own slots */
Port top_build(Syn *body, int nslots, const int *uses);

/* globals: each definition's net is built once; a use copies its value */
Port global_copy(long g);          /* 0 when the global is an unsupplied input */
void global_park(long g, Cell *op, Cell *glob);
long global_lookup(const char *name);
const char *name_of(long id);

#endif

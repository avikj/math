# Scoped cubical machine

C11 machine for the specification `HANDOFF.md`; `INTERNING.md` specifies
stepped interning. The evaluator and the composition library are programs
of the language (`prog/core.ctt`); the machine performs the steps those
programs are made of.

    make test    # ASan/UBSan: every suite
    make tsan    # ThreadSanitizer: every suite with 4 workers

## The one protocol (`eval.c`, `eval.h`, `families.h`)

Every computation over variable data is a producer keyed by (family, a, b).
Its entry moves U → R → D by a constant number of atomic operations: a
requester joins by one exchange (the one that finds U launches the producer;
a launch alone is one CAS, never retried), publication exchanges the waiter
chain for READY, and each delivery is its own job. A
producer is a frame: a step function that does a bounded amount of work and
ends in request, call (a subroutine frame), yield or finish. Independent
demands are launched and then awaited in order. Host callers drive a root
key with a host frame (`family_run`, `family_call`, `family_run_budget`); a
budget is a host control bound on the jobs executed during the call. Every family id is
named in `families.h`.

## Records

- One record table (`state.h`, `intern.c`): every record is interned in
  `M.keys` by the stepped interner; the evaluator's entry index is its own
  table. Stable stores are radix directories of fixed-size nodes over every
  `size_t` index.
- Universe levels are exact naturals (a word below 2^63, the canonical
  exact-integer record above); successor and maximum are stepped families.
- Intervals and faces are canonical antichain DNFs (`dnf.h`); their
  operations, and set union / removal / membership, are families (`dnfam.c`).
- One substitution record (`subst.c`): `[(key, sort, value)*]` sorted by
  key, an environment (and every total record: context indexes,
  CLOSE contexts) followed by a trailing word. One stepped lookup, one set.
- Constructions (`construct.c`): one constructor schema per tag (field kinds,
  binder slots, binder sort, role, scrutinee, a code eliminator's operand
  fields) read by
  every builder. A construction is a node whose field constants are closed by
  CLOSE over (depth, slot) atoms; its reference is TVIEW(node, environment).
- Traversal (`scopefam.c`, `template.c`): CLOSE (identity ↦ slot), APPLY
  (environment slot ↦ value, lowering deeper atoms), RE (a map on free
  identities), LOWER (∀); TVIEW views of construction nodes.

## Definitions (`term.c`)

A symbol is opaque by its declaration (an axiom: a constant), or a
definition whose body is an input, supplied once. An observation before the
body is supplied is pending, not sealed: the supply publishes the input entry
and every pending computation continues from where it stopped. An external
answer that can differ between consumers is an explicit argument (a
variable) at the boundary where it matters: each answer is a substitution
into the residual.

## The machine's steps (`eval.c`)

β, pair projections, unfolding a definition, and the code eliminators;
native evaluation is keyed by the term alone (the ambient face is an
argument of the evaluator program). Every other former (paths, Glue,
systems, composition) is a value of the machine; its computation is the
evaluator program. The value of a stuck elimination is its residual: the
eliminator with its operands replaced by their values, where computation
continues when an open input is supplied (by substitution: the prefix
already established is not redone). While a computation runs, its entry
records the term it has moved to; `whnf_residual(t)` reads the computation
so far. The machine judges nothing: records carry no required faces, and a
code operation outside its domain gives the code `(cnone)`.

## Codes (`code.c`, `read.c`)

The language's own term records are values of the type `(Code)`: `(quote t)`
holds the record of `t`; `(qiv r)`, `(qfc φ)`, `(qlv l)` are codes of the
types `(ICode)`, `(FCode)`, `(LCode)`. There is no second representation of
syntax: the record a quote holds is the record the machine evaluates. Each
code eliminator is one native rule over those records, its operands
evaluated together first: `cmatch` (dispatch on the former; its argument
kinds are `code_arg_kind`, exposed to programs as `cfield`), `cinst` /
`cinsti` (open a term / dimension binder), `cset` / `csetb` / `csetbi` /
`csetlv` (rebuild with a field, a binder field or the annotation replaced),
`clevels`, `cvar` / `cvari`, `csubst`, `csyscons`, `ceq`, `cent`, `cfcend`,
interval and face operations, level successor and maximum, `cunfold`,
`ctype`, `cpayload`, `cquote`, `cstep` (the code of one rule step).

## The evaluator (`prog/core.ctt`)

`eval χ c`: the code of the term the term coded by `c` reaches under the
face coded by `χ` — an introduction, a system value, or a residual. It has a
clause for every executable former, the code operations included (operands
evaluated, then the operation's rule as one represented step, `cstep`). It
contains the composition clauses (Π, Σ, Path, Glue, U) and the library they
build (Fill, HComp, Coe, Equiv, Fib, Contr, IdEquiv, LineEquiv,
ExtendContr, ua), each a program building codes.

## The checker (`prog/check.ctt`)

`check χ c A` and `infer χ c`: bidirectional typing over codes, with
conversion (η for functions, pairs and paths; systems branchwise; universe
cumulativity). A variable's type is its declaration (`ctype`), so the
context is the variables themselves: a binder is entered at its own
variable (`cvar`, `cvari`). A partial element has the type `(Partial φ A)`:
a variable of that type is used only under faces entailing φ, and checking
against it checks under φ. Programs over codes are typed: the code types
are types, a code operation takes codes of the kinds it acts on, its
branches share one type, a `cmatch` handler has the type its former's
arguments give (computed in the program from `cfield`). The checker
checks every definition of the evaluator, the library and itself against
its declared type, the library's constructions (IdEquiv : Equiv A A,
LineEquiv, ua : Path U A A, Fill), and that the evaluator's composition
reducts have the composition's type (`tests/test_check.c`).

## Tests

`tests/test_*.c` check substitution, DNF laws, alpha identity, records,
the machine's steps, reading, and the evaluator program (`test_code`: its
values, and agreement with the machine on the machine's own steps).

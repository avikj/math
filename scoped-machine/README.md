# Cubical interaction net

A term is a net of cells. A declaration together with the identities it uses is posed as a net, and normalizing that net is the computation. Every cell has one principal port, so distinct active pairs share no cell and any two steps close up in one step each. Sharing is the duplicator cell. Information moves one wire per step.

```
make test        # the suites, with 0 and 4 workers, and under ASan/UBSan
make tsan        # the suites with 4 workers under ThreadSanitizer
```

## Cells (`src/core.h`)

**Values** have a positive principal port:
- λ: an immutable binder record, plus one port for each maximal subterm of its body that is free of the bound variable;
- pair, Π, Σ, U, PathP;
- a line `PLAM(i, body)`;
- an interval or face (an immutable DNF payload);
- a system: branches, each a face clause with the value restricted to it;
- Glue type and glue element;
- neutrals, which keep every operand: variables and stuck application, projection, path application, composition and unglue;
- a definition `GLOBAL`.

**Operations** have a negative principal port facing the value their rule inspects:
- application: on the function;
- projections: on the pair;
- path application: on the interval first, since an annotated endpoint answers without the path, then on the path;
- composition: on the tube first (coverage), then on the family, then on the family's head at its own fresh dimension;
- Glue, glue and unglue;
- the interval and face connectives, and `forall`;
- the face of a system;
- system construction;
- mapping over a system;
- the structural cells: duplicate, erase, and substitute dimensions.

## What makes it local

- **A face clause is a substitution of endpoints.** Being under a face is reindexing.
- **A system branch is built only after its clause is known.** It is a thunk forced under the clause's substitution. A system whose clause becomes true is that branch.
- **A face is ⊤ exactly when its DNF has the empty clause.** An interval is 0 or 1 exactly when its DNF is. So no rule consults an ambient context.
- **Every eliminator acts branchwise on a system.** Its other operands are restricted to each branch's clause.
- **A dimension binder is a name and a value.** Applying it puts a substitution cell on the value, which re-activates every neutral the substitution unblocks (`p@i` under `i:=0` is the left endpoint).

## Binders and sharing

`lam` compiles to a record. Its body's maximal subterms that are free of the bound variable are compiled in the enclosing level and wired to the cell's ports, so they are computed once however often the λ is applied. Duplicating a λ copies the record handle and duplicates the ports. A definition's net is built once, and each use copies its value through a duplicator.

## Composition

`comp A u a0` takes a line of types, a tube (a system of lines, or a total line) and a base.
- **A total tube is its own end.** The result is `u@1`.
- **Otherwise the family is opened at its own dimension.** Its head selects a library clause in `lib/prelude.ctt`, applied to the head's components re-abstracted as lines: `%comp-pi`, `%comp-sigma`, `%comp-path`, `%comp-u` or `%comp-glue` (HANDOFF §§14–17).
- **A system of families** composes branchwise under ∀i of each branch's clause.
- **A neutral family** gives a neutral composition.

`fill`, `transp`, `hcomp`, `Equiv`, `idequiv`, `lineequiv` and `ua` are definitions in the prelude, as are the data types: `Bool`, `Nat` and `List` are Π-types over `U` with their constructors and operations as terms. No data type is a primitive.

## Observation

Reading a value reduces the net in arrival order only until the observed port holds a value; the rest of the net stands. A divergent part the answer does not use does not block it, and a definition referring to itself unfolds only when eliminated (`(def ones (pair a ones))`).

## Codes and the evaluator

`lib/code.ctt` gives codes of terms as data (a Scott encoding: a code is a function of one handler per constructor; variables are de Bruijn indices into an environment of nested pairs) and `eval`, a term mapping a code and an environment to the value the machine gives that term. There is no `quote`: a primitive inspecting a term's syntax would distinguish path-equal functions and could not be a function respecting paths. Codes are built as data; statements about the evaluator are terms.

## Parallel rewriting

`CUBICAL_WORKERS=n` runs n threads besides the caller. One rewrite follows HANDOFF §20: it locks the active pair and every cell whose port it may rewrite (the pair's neighbours; for a definition, the cell holding its value and that value's cell) in address order, revalidates that those neighbours are unchanged, installs the replacement, releases, and only then publishes the active pairs it made, so no worker meets a cell still being built. Cells are type-stable: their memory is never returned, so a stale pointer reaches a valid lock word and revalidation fails. Wires are published with release and read with acquire.

By 5.11–5.13 the number of steps is independent of the schedule; the suite without its divergent check takes the same number of interactions with 0, 2, 8 and 16 workers.

## Readings

`show` reports the length (interactions) and the effect (erasures: every forgetting goes through an eraser cell) of reading a value.

## Identities on running computations

A subnet computing `L γ` between its input wires and its output wire is, at every cut, a run of `L` (HANDOFF §21, §41): its internal wires hold the residuals and every witness is refl, since reduction is definitional. An identity `p : L γ = R γ` acts on that run by `F_p = d_R ∘ (p⁻¹·) ∘ c_L`, which on a refl-witnessed run is the rewiring: `R`'s net on the same inputs and the same output wire, with the output's witness `p γ`.

`(identity L R p)` declares that `p` gives `L g = R g` for every argument `g`; `p` may be an input not yet supplied. An application of `L` whose identity is available applies it: `R` is applied instead, and the argument is kept to read the witness. While the identity is pending, the application is wrapped in a site that holds the argument and the output wire and forwards `L`'s value if it arrives. When `p` is supplied, every live site switches: `R` is applied to the kept argument on the same output wire, and `L`'s running subnet goes to an eraser (a strict net cannot cancel running work; its value is erased when it arrives). `(witnesses)` reads `p g` for every switched application.

Supplying an identity is an external event, like supplying an input: equal length (5.13) holds within each run, and the steps added and saved by the switch are the defect of the square comparing the two routes.

## Inputs

`(input x)` declares a definition whose value is not yet supplied. Any eliminator meeting it waits. `(supply x t)` connects the value, and the waiting pairs proceed.

## Files

- `src/dnf.c`: interval and face DNF, substitutions.
- `src/net.c`: cells, wiring, the interaction rules, building a net from compiled syntax.
- `src/lang.c`: reader, compilation to binder records with lifting, definitions, identities and sites, readback, driver (`def`, `axiom`, `input`, `supply`, `identity`, `show`, `same`, `watch`, `same-watch`, `witnesses`).
- `lib/prelude.ctt`: the library.
- `tests/cubical.ctt`, `tests/code.ctt`, `tests/identity.ctt`: the checks.
- `HANDOFF.md`: the specification.

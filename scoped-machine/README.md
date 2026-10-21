# Cubical interaction net

A term is a net of cells. A declaration together with the identities it uses is posed as a net, and normalizing that net is the computation. Every cell has one principal port, so distinct active pairs share no cell and any two steps close up in one step each. Sharing is the duplicator cell. Information moves one wire per step.

```
make test        # build/cubical lib/prelude.ctt tests/cubical.ctt, then the same under ASan/UBSan
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

`fill`, `transp`, `hcomp`, `Equiv`, `idequiv`, `lineequiv` and `ua` are definitions in the prelude.

## Inputs

`(input x)` declares a definition whose value is not yet supplied. Any eliminator meeting it waits. `(supply x t)` connects the value, and the waiting pairs proceed.

## Files

- `src/dnf.c`: interval and face DNF, substitutions.
- `src/net.c`: cells, wiring, the interaction rules, building a net from compiled syntax.
- `src/lang.c`: reader, compilation to binder records with lifting, definitions, readback, driver (`def`, `axiom`, `input`, `supply`, `show`, `same`).
- `lib/prelude.ctt`: the library.
- `tests/cubical.ctt`: the checks.
- `HANDOFF.md`: the specification.

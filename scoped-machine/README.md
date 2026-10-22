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
- neutrals, which keep every operand and carry their type: variables and stuck application, projection, path application, composition and unglue;
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
- **A neutral carries its type** on its last port. `(axiom (p T))` declares a constant of type T. Eliminating a neutral of known type computes the result's type from it (the codomain at the argument, a Σ's components, the line at r), so the endpoints of a neutral path are read from its type: `t 0 = u0` for `t : Path A u0 u1`, as in CCHM. A constant declared without a type, or a variable introduced by readback, has an unknown type.

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

## Data types

`(data T (c1 x..) (c2 y..) ..)` defines a type by its constructors as terms (a constructor is a function of one handler per constructor, applied to its arguments); `(case t ((c1 x..) b1) ..)` is that application with each branch a thunk, so only the selected branch is built. `if`, `delay` and `force` are the same sugar. `(declare f)` names a definition used before it is given (mutual recursion); the later `def` supplies it. Nothing here adds a cell kind beyond the thunk force.

## Codes and the evaluator

`lib/code.ctt` gives codes of terms as a data type `Code` (variables are de Bruijn indices `Num` into one context of term and dimension variables; globals are indices into a signature) and `eval-g g e c`, a term mapping a code to the value the machine gives that term. `(code t)` writes the code of a source term. There is no `quote`: a primitive inspecting a term's syntax would distinguish path-equal functions and could not be a function respecting paths. Codes are built as data; statements about the evaluator are terms.

## The checker as a term

`lib/check.ctt` is the type checker of CCHM, written in the language and run by the net (5.26: no outer layer). It is normalization by evaluation over data:
- **Intervals and faces are data**: DNFs of literals with meet, join, negation, the order and equality, substitution, and `forall`.
- **Values and neutrals are data**, closures are functions taking a fresh-level counter. `act` substitutes dimensions and re-dispatches neutrals the substitution unblocks; neutrals carry their types.
- **`veval`** evaluates a code; composition follows the same clauses as the machine (Π, Σ, path, U, Glue), with `fill`, `transp`, `hcomp`, `idequiv`, `lineequiv` defined in the checker.
- **`conv`** decides conversion with η for functions, pairs and lines, and compares systems under each clause.
- **`check` / `infer`** are the typing rules, including faces, systems (adjacent branches agree on their meet), composition (the tube agrees with the base) and Glue.

`(checked n T t)` translates `T` and `t` to codes, runs `chk-def` on the current signature, compares the result with `true`, and on success defines `n` and extends the signature; `(check T t)` and `(check-fail T t)` check without defining. `tests/check.ctt` checks identity, refl, sym, funext, transport, path concatenation by hcomp, contractibility, fibres, equivalences, `idequiv` and `ua`, and rejects ill-typed terms, among them a tube disagreeing with its base.

## Parallel rewriting

`CUBICAL_WORKERS=n` runs n threads besides the caller. One rewrite follows HANDOFF §20: it locks the active pair and every cell whose port it may rewrite (the pair's neighbours; for a definition, the cell holding its value and that value's cell) in address order, revalidates that those neighbours are unchanged, installs the replacement, releases, and only then publishes the active pairs it made, so no worker meets a cell still being built. Cells are type-stable: their memory is never returned, so a stale pointer reaches a valid lock word and revalidation fails. Wires are published with release and read with acquire.

By 5.11–5.13 the number of steps is independent of the schedule; the suite without its divergent check takes the same number of interactions with 0, 2, 8 and 16 workers.

## Readings

`show` reports the length (interactions) and the effect (erasures: every forgetting goes through an eraser cell) of reading a value. A reading is taken over the complete normalization of what was posed: pending pairs are reduced before and after, so the counts do not depend on the schedule (identical with 0, 4 and 8 workers). This requires the workload to normalize; a divergent part left pending makes a reading wait forever.

## Identities on running computations

An identity `p : L g = R g` acts on an application of `L` by transport along it: the application's output wire carries the line `p g @ i`, at the identity's own dimension `i` (fixed when the identity is declared), with its endpoints annotated: `L g` at 0 and `R g` at 1. The line is a neutral path application, so by the endpoint rule nothing waits on the evidence: the answer (every identity's dimension at 1) is `R g`, the 0-end is `L g`, what was posed, and only the witness, the line's interior, needs `p`. Everything downstream computes along the line, so the observed value is `ap` of the rest of the computation applied to `p g`. All three parts are deferred and built when eliminated; `L`'s run is the 0-end and is not followed again, nothing is erased.

- `(identity L R p [n])` declares that `p g1..gn` is a path `L g1..gn = R g1..gn` (`n` defaults to `L`'s leading λs); `p` may be an input not yet supplied, an ordinary input.
- An application of `L` collects its `n` arguments (a curried application is a value until saturated), then follows the identity.
- `R g` follows `R`'s own identities, so identities chain. Declaring both `L → R` and `R → L` poses a cycle, which has no normal form; the reverse direction is `p⁻¹` and is not declared.
- Readback gives the answer. `(witness t)` and `(witness-watch w)` read the value itself, the line or cube from what was posed to the answer, re-dispatching its neutrals so a witness read after its evidence arrived is in normal form; `(same-watch w u 0)` reads a watch at the 0-end.
- `(the T t)` observes `t` at its declared type: when `T` itself moved along identities' lines, the answer (at the 1-end) is transported back along `T` to `T` at the 0-end, so it inhabits the declaration.
- `(defect t)` runs `t` from the same warm state without and with its identities and reports the difference in length and in erasures, the work reading's value across the identity.

## Memory

Intervals, faces, clause lists and substitutions are immutable and reference counted; a cell owns its payload and releases it when the cell is retired, so payloads live are bounded by the cells holding them (100 nested transports, 390k interactions: 100 payloads live, those of the result). Reading a value back runs on an explicit stack: a value a million deep reads back on the default native stack. No fixed caps remain in the reader, compiler, readback or observation.

## Inputs

`(input x)` declares a definition whose value is not yet supplied. Any eliminator meeting it waits. `(supply x t)` connects the value, and the waiting pairs proceed.

## Files

- `src/dnf.c`: interval and face DNF, substitutions.
- `src/net.c`: cells, wiring, the interaction rules, building a net from compiled syntax.
- `src/lang.c`: reader, compilation to binder records with lifting, definitions, identities and sites, readback, driver (`def`, `declare`, `data`, `axiom`, `input`, `supply`, `identity`, `show`, `same`, `the`, `watch`, `same-watch`, `witness`, `witness-watch`, `defect`, `checked`, `check`, `check-fail`).
- `lib/prelude.ctt`: the library.
- `lib/code.ctt`: codes and the evaluator; `lib/check.ctt`: the checker.
- `tests/cubical.ctt`, `tests/code.ctt`, `tests/identity.ctt`, `tests/check.ctt`: the checks.
- `HANDOFF.md`: the specification.

# What the mathematics dictates, from the ground up

*The design of `--to-hvm4-full`, stated once so it is not rediscovered.
Companion to `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §41,
`RUNTIME_FULL.md` ("Typed points") and `SETTLED_BY_THE_CORPUS.md` (what the
corpus already settles about superposition, order and the price of Glue,
and the runtime those theorems dictate).*

The runtime object is `Σ A : Set. A`: a checked term together with its
checked type. Every definition is emitted as `@Dname` (the term) and
`@Tname` (its type), through the one emitter. The root is the pair,
`@main = #Pair{@Tmain, @Dmain}`. That is the whole design. Everything else
in the pull request's description is a consequence of it:

- The graph `Σ a. Σ b. Path (f a) b` needs no wrapper, because it is
  already a Bend term with a Bend type, and the ordinary emitter emits
  ordinary terms. A second runtime for it would be a second evaluator,
  which the description forbids. `port/FibreCoalgebra.bend` and
  `port/ConductiveRuntime.bend` are ordinary programs of this kind.
- Cubical cells (`ua` with both of its coherences, `coe`, `hcomp`, `Glue`,
  HIT constructors, the interval) are structure in the checked term.
  Erasing any of them is lossy. The full target keeps them all. That is
  what "full" means.
- Whole-family information is the SUP-shared object, evaluated by the HVM.
  It is not enumerated by the host and not traced by a Haskell WHNF
  recorder. `research/sat_fibre/SATProcess.bend` conducts XOR over
  `@assignment{&100{False, True}, &101{False, True}}` and the four readings
  come out of one net.
- The cost is the HVM interaction count on the typed root. It is not the
  length of a derivation list: for a closed deterministic run the
  derivation is contractible (Niyati, the fibre of a run), so the list
  carries no information, and recording it at compile time both describes
  a different evaluator (Core.WHNF, not HVM4) and breaks productivity.
- Ill-typed input is refused before emission, because a typed point with
  no type is not in `Σ A. A`. `--to-hvm4-full` runs the checker first and
  emits nothing on failure.

So the "one right result" is not ambiguous. It is a full emitter whose
output is the checked object as a typed point, with all cells preserved,
no prelude re-implementing the law, no generated companions, no receivers,
and gates that establish the acceptance items on the pinned toolchain in
a CI file that parses. The order of the non-commuting steps that reach it
is: hold the spec; read the mathematics the spec cites until the design
reads as forced; get the pinned toolchain building; apply the patch to a
real checkout; remove what the spec says to remove; add what it says is
missing; regenerate the patch from source (never edit a hunk header by
hand); run the gates locally; fix the CI file; push once.

## This goes all the way up: SupGen, and declarative Bend

The typed point is not a feature of `main`. It is what every Bend
expression is. Because the emitted object is the whole checked term with
its type and every cell, and because the HVM is the evaluator of that
object, an arbitrary Bend expression is evaluated *as the mathematical
object it denotes*, however it was declared:

- A function declared by pattern matching, by a fold, by a path, by a
  transport along `ua`, or by a corecursive record receives the same
  execution: Lévy-optimal sharing on the interaction net, with the
  cubical structure executing rather than erased. There is no privileged
  "efficient" way to write a function and no "proof-only" way to write
  one. Cost-optimal execution and the complete mathematical power of the
  theory come with the object, not with its spelling.
- A superposed candidate family (`SUPGEN_DEMO.md`) is just such an
  expression: `&L{…}` is a term, a specification is a map out of it, the
  survivors are its fibre, and collapse reads that fibre off the net. Search
  is evaluation of a typed point whose value happens to be a superposition.
  Nothing is added for it, and nothing may be: a host loop, a scheduler
  superposition, a theorem database or an external optimizer would put a
  second evaluator between the object and the net.
- Programming is therefore declarative in the strong sense: state the
  object (its type and its term), and its execution is the net's reduction
  of exactly that object. Observation of it is a map out of it; the fibre
  law says the observation loses nothing that the retained coordinate does
  not keep; the coinductive closure says the result is again such an
  object. That is the point of the pull request, and it is the point of
  the whole lane: the mathematics was already complete and executable, and
  the compiler's only job is to not stand between it and the machine.

## Regression checklist

Read this before touching the emitter, the patch, the ports or the CI, and
again before pushing. Every line is checkable on the pinned toolchain
(`mining/bootstrap.sh`), and `.github/workflows/conductive-language-entry.yml`
runs the same checks.

1. `cubical-paths.patch` applies to Bend2 `f026483` with `git apply --check`,
   and `glue-emit.patch` stacks on top. It was regenerated with `git diff`,
   not edited by hand: `python3 test_list_transport.py --check-only` verifies
   the new-file hunk length against its header.
2. The patch contains no `@cf`, `sourceMain`, `conductiveMain`,
   `NativeStep`, `nativeDerivation`, `nativeRun`, `@nativeFold`, and
   `Target.HVM4Full.compileFull` emits exactly `@D…`, `@T…` and the root.
3. `bend x.bend --to-hvm4-full` on an ill-typed file exits non-zero with
   empty stdout (`gate_mustfail.bend`); on a checked file the last line is
   `@main = #Pair{@Tmain, @Dmain}` and `hvm p.hvm4 -s` prints
   `#Pair{<type>, <value>}`.
4. Cells survive: `#UaU{A, B, f, g, gf, fg}` (six), `#Eql{A, x, y}`,
   `#Enum{…}`, `#Num{…}` (`complex_cells_smoke.bend`); `Op1`, `Met`, `F64`,
   `I64` are refused with an error, never emitted as `&{}` or the identity.
   A HIT constructor carries its parameters (`hit_param_endpoint.bend`
   computes 6 at both ends, in the checker and on HVM4; `hit_trunc.bend`'s
   value prints under `-C10`); a constructor without its parameters is
   refused at emission, and `&{}` never stands for a missing cell.
5. `port/FibreCoalgebra.bend` and `port/ConductiveRuntime.bend` run through
   the ordinary emitter to `#Pair{#Nat{},#Suc{#Suc{#Zer{}}}}`; no runtime
   definition re-implements `descend`/`observe`/`ascend`.
6. `research/sat_fibre/SATProcess.bend` emits no `@DwholeProcess` or
   `@Dinteract`, and its root value contains
   `#Pair{&L100{0,1},#Pair{&L101{0,1},#Pair{&L100{&L101{0,1},&L101{1,0}},#One{}}}}`:
   the four readings from one shared net.
7. `suite.sh` reports `bad=0`; the must-fail probes are still rejected.
8. The mining linker follows the `@D` namespace
   (`node --test mining/transport-checks.mjs`).
9. Nothing was added between the checked object and the net: no host
   enumeration, no scheduler, no trace recorder, no optimizer, no second
   type theory, no prelude copy of a port module.
10. A superposition is typed by the DUP of its goal at its label
   (`sup_dependent.bend`: `(&0{True,False}, &0{3n,()}) : Σ b:Bool. F(b)`
   checks fibrewise and collapses under `-C10` to exactly the two diagonal
   readings; `sup_dependent_mustfail.bend`'s different-label sibling is
   rejected). The checker, the normaliser and HVM4 run one DUP-SUP rule;
   no product rule on the type and no second rule for the net.

# The task, and the construction already handed that makes it elementary

The task is Lafont/Lévy-optimal reduction of cubical cell complexes:

1. **Express an arbitrary expression as a cell complex.**
2. **Fill and reduce all of its faces and identities.**

Every piece of this is already constructed and checked in this repository. The mathematics is in `fibre/` and
`formal/cubical/`. Its first dialect on a net is `collab/bend2-interactive-cubical/` ("the lane"): the Bend2 fork plus
HVM4.

## 0. Why a new language and runtime instead of the lane

`hyper/MAP.md` §0.2 says the fork is this language's first dialect and value oracle, and that the runtime has one
entry: reduce, with check on the same loop. `CORPUS_DIGEST.md`, in its "Design consequence" for the kernel lane,
states that HVM4 violates the specification in three ways.

1. **The checker is outside.** Bend2's Haskell checker runs before emission as a second evaluator.
   - The corpus says verify is decide (`VerifyIsDecide_…`; `SETTLED_BY_THE_CORPUS.md` §4 item 8). Checking is the type
     projection of the typed point, reduced by the same net.
   - This is exactly what makes a declaration with no body a program. Checking `Σ B. P` against a superposed `B` is
     the DUP-of-goal rule, and the survivors are the fibre.
   - An outside checker demands a term, so a missing body is an error.
2. **Labels are a budget.** HVM4 labels are 24 bits and static per binder, so a recursive unfolding reuses its label.
   - The corpus says a label is the name of a coordinate: same label means same coordinate
     (`SETTLED_BY_THE_CORPUS.md` §1, §4 item 3).
   - A reused label conflates distinct coordinates.
3. **Collapse is a printer.** HVM4's `-C` is a readback with a priority queue.
   - The corpus says collapse conserves multiplicity and the fibre is a value that computation continues on
     (`SETTLED_BY_THE_CORPUS.md` §4 item 6).
   - `sortCost` needs the collapse as data.

Bend2's core adds `Set : Set` and one-step untyped conversion (`STATE_OF_THE_WORK.md` I.4).

The language `hyper/` is meant to hold is the runtime `SETTLED_BY_THE_CORPUS.md` §4 specifies ("hvm5/bend3"):
- **agents:** LAM/APP, labelled DUP/SUP, and constructors for cells;
- **the checker:** folded in as net programs;
- **labels:** named by coordinates;
- **collapse:** a value.

The lane already supplies the Kan rules as net programs (`RUNTIME_FULL.md`: the prelude is Core.WHNF's cubical
reduction written for HVM4). It also supplies the checker's rules, including DUP-of-goal, in `cubical-paths.patch`.
`hyper/` spent a week building beside those instead of starting from them.

## 1. An arbitrary expression is a cell complex

**The object** is a typed point of the universal family, `Σ A : Set. A`.
- Every family `B : A → Type` is the pullback of `π : Σ X. X → Type` along its classifying map, by `refl`.
- A tower of families flattens to one family.
- Source: `fibre/src/Fibre/Universal_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda`.
- So types, values, paths and processes are all points of one object, and nothing leaves it.

**On the net:**
- Every checked definition is emitted as `@Dname` (the term) and `@Tname` (its type), and the root is `#Pair{@Tmain, @Dmain}`.
- The lowering keeps every cell as runtime data:
  - the interval: `#I0 #I1 #INot #IAnd #IOr`;
  - paths: `#PLm{λi. t}`, and `p @ r` is an application;
  - universe paths: `#UaU{A,B,f,g,gf,fg}` and `#CompU`;
  - types: `#Pi #Sig #Path #Glue …`;
  - composites: `hcomp` as `#HCm`;
  - HIT constructors with their parameters.
- Sources: `collab/bend2-interactive-cubical/TYPED_POINT.md`; `RUNTIME_FULL.md` (the table and "Typed points"); the
  emitter `Target/HVM4Full.hs` in `cubical-paths.patch`.
- Nothing is erased, and nothing is normalised at compile time.

**Every map is already its own complex.**
- For any `f : A → B`, `A ≃ Σ b. fib_f b` with first projection `f` by `refl`.
  Source: `fibre/src/Fibre/Carrier.agda`; `Trace_…` `fibre-of-run`.
- The graph `Σ a. Σ b. f a ≡ b` has two projections. The source projection is always an equivalence. The target
  projection is one exactly when every residual is contractible. Source: `Residue_…` `ग्राह`.
- The completion is unique. Source: `formal/cubical/theorems/residue/Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda`.
- So an expression's cells, its maps and their fibres, are forced by the expression and not chosen.

## 2. Filling and reducing every face is net reduction

**One Kan primitive.**
- `comp` gives `coe` (empty faces) and `hcomp` (constant line).
- Its reduction dispatches on the type former:
  - Π conjugates;
  - Σ is componentwise;
  - inductive types commute with constructors;
  - the universe goes through Glue.
- Source: `CONVERGENCE.md` II.3.
- On the net:
  - `@coe` dispatches on the runtime type cell;
  - `@hcomp` evaluates the faces, so a true face gives its tube's top, all-false gives the base, and otherwise the
    composite stays as `#HCm`, partial knowledge that resumes when the interval is decided;
  - Glue and `hcomp` in `Set` mirror the checker.
- Sources: `RUNTIME_FULL.md`; `GLUE.md`; `GENERAL_HCOMP.md`; checked runs `uaglue.bend`, `hcompset.bend`,
  `isprop_run.bend`, `fibrelaw.bend`.

**Filling is the invertibility test, and DUP-SUP runs it.**
- `comp` reduces fully exactly when the fibre is contractible. On the net, same-label DUP-SUP routes that case with
  no allocation.
- `comp` sticks exactly when the fibre is not contractible. On the net, different-label DUP-SUP crosses that case and
  allocates.
- Sources: `CONVERGENCE.md` IV.1; `SETTLED_BY_THE_CORPUS.md` §1. `supline.bend` is transport along a superposed line
  with no rule of its own.

**Order is not a choice.**
- Interaction nets have the one-step diamond by construction.
- Every complete reduction to the normal form therefore has one length. Source: `research/sat_fibre/InteractionGeodesic.agda`
  (`same-normalization-length`, `normalization-is-geodesic`).
- Schedule is a gauge. Sources: `SETTLED_BY_THE_CORPUS.md` §2; `Order_…` (Krama); `PairwiseCommutationGivesEveryOrder`.

**Sharing.**
- Transport that recomputes shared subterms is a redex family, and optimal reduction shares it. Source: `WRITEUP.md` §3.1.
- Measured: a transport consumed `k` times is paid once, 14 interactions per extra use shared against 150 unshared.
  Source: `SYNTHESIS.md` §3.

## 3. A declaration with no body is the same reduction

"Search is evaluation":
- A candidate family is a SUP.
- A specification is a map out of it.
- The survivors are its fibre.
- `&{}` is the empty fibre.
- Collapse reads what remains and never deduplicates.

Sources: `SETTLED_BY_THE_CORPUS.md` §4 item 6; `TYPED_POINT.md` "This goes all the way up"; `SUPGEN_DEMO.md`
(synthesising `not` by example as the only survivor).

**It is typed fibrewise.** A superposition is typed by the DUP of its goal at its label (`SETTLED_BY_THE_CORPUS.md`
§1; `sup_dependent.bend` and its must-fail sibling).

**Finding and checking are one equivalence.** Source: `formal/cubical/theorems/residue/VerifyIsDecide_ThereIsNoGapBetweenFindingAndCheckingBecauseBothAreProjectionsOfOneEquivalence.agda`.

## 4. Cost-optimality validates the construction; it is not the goal

**The certificate.** A potential Φ with `Φ(u) ≤ c(u,v) + Φ(v)` on every primitive edge bounds every realisation from
below. A native path that attains it is a proved geodesic. Source: lane `README.md`, "Exact cost certificate".

**A worked instance.** Bringing cell `n` to the head costs exactly `n` crossings, and `Bring(n)` attains it. Source:
`research/PNP_GEODESIC_REDUCTION_20260916.md` G3.

**Presentations.**
- A speedup is a detour through another presentation. Sources: `formal/cubical/NaturalMachine/CostGeometry.agda`;
  `formal/cubical/theorems/cost/TransportDivScale.agda`.
- Size is not a function of meaning. Source: `NaturalMachine/Laghava.agda`.
- So what runs is the cheapest presentation reachable by executable identity. Reaching it is itself reduction. Source:
  `SETTLED_BY_THE_CORPUS.md` §4 item 9.

## 5. The questions raised in this session, and where each is already answered

**Q1. "Labels alone are only correct on a restricted fragment; full Lamping bookkeeping is needed."**
- A label is not an approximation of Lamping's levels. It is the name of a base coordinate:
  - same label means the same coordinate (the source projection, which routes);
  - a different label means an independent coordinate (the product, which pays).
  Source: `SETTLED_BY_THE_CORPUS.md` §1 and §4 item 3.
- Label correctness is therefore the typing rule "a superposition is typed by the DUP of its goal": the checker, the
  normaliser and HVM4 run one rule (`sup_dependent.bend`; `TYPED_POINT.md` checklist item 10).
- `CONVERGENCE.md` XIII names the label discipline as the one thing to check on the runtime.

**Q2. "Lévy families have to be defined for the cubical rules: the interval is not linear and Kan operations need types at run time."**

- *The interval.* It is data, and path application is β. Duplicating a dimension is an ordinary DUP of a constructor.
  Source: `RUNTIME_FULL.md` table.
- *Kan operations.* The prelude is the checker's cubical reduction written as an interaction-calculus program, so its
  redex families are the calculus's own. Source: `RUNTIME_FULL.md` opening paragraph.
- *Types at run time.* They are cells of the typed point. Source: `TYPED_POINT.md`.
- *The price of Glue.* It is exactly the non-contractible fibre. Source: `SETTLED_BY_THE_CORPUS.md` §3.

Nothing cubical-specific remains to define.

**Q3. "Measure cost / Blum's speedup theorem / Asperti–Mairson."**
- Blum's theorem is about extensional functions over all programs. The corpus claims a minimum over presentations
  reachable by executable identity, not over all programs (§4 above). So Blum does not apply.
- Asperti–Mairson is already addressed in `research/sat_fibre/THEORY_READING.md`.

**Q4. The old `MAP.md` 0.1: "how a declaration with no body resolves."** Answered in §3 above.

## 6. What remains: labour, as the lane lists it

From `SETTLED_BY_THE_CORPUS.md` §5 and the caveats in `RUNTIME_FULL.md`:

1. **Fold the checker into the net** ("verify is decide"). The Haskell checker currently runs before emission as a gate.
2. **Transport to a symbolic endpoint.** Hold it as a resuming cell, as `#HCm` does, instead of the dead end `#StuckCoe`.
3. **`infer` for a superposition.** `&l{a,b}` infers `&l{A,B}`; `Frk` gets the same DUP rule.
4. **The printer.** Observe points that contain recursive functions through a map out of them.
5. **Unary operations and numeric kinds.** `Op1`, `I64` and `F64` become cells instead of refusals.
6. **Port the remaining corpus modules.** `AUDIT.md`: nothing needs a feature Bend lacks.

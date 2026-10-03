# Settled by the corpus: superposition, order, the price of Glue, and the runtime they dictate

*Companion to `TYPED_POINT.md`. Three questions were carried through this
lane as uncertain. Each is answered by a theorem already checked in the
repository, and one of them was malformed as asked. This note records the
answers with their sources, the one checker change they force, and the
design of the next runtime as those theorems state it. Nothing here is
estimated and nothing is deferred to a later stage; every claim names the
module that carries it.*

## 0. The three questions

| asked | status |
|---|---|
| How is a correlated superposition typed in a dependent family? | Malformed as a question about a new type former. It is the DUP-SUP rule applied to the type. Settled, and now implemented (§1). |
| What does the equivalence data of a Glue line cost, and how is it shared? | The non-contractible fibre and nothing else; sharing is forced by uniqueness of the completion. Settled (§3). |
| How is cost identified on hardware, and which schedule is right? | Not a question. Every schedule has the same count (confluence); the schedule is a gauge; the physical constant is Landauer's. Settled (§2). |

## 1. Superposition and duplication are the two projections of the fibre law

The corpus identifies them at length. The statements, in the order that
makes the identification forced:

- `README.md` §1. A DUP at label `L` meeting a SUP at `L` **routes**: the
  paired observations are the diagonal `Δ₂ = {(0,0),(1,1)} ≃ 2`, one bit.
  A DUP at `L` meeting a SUP at `M ≠ L` **crosses**: both coordinates
  survive, the product `2 × 2`, two bits. Shannon counts exactly this.
- `CONVERGENCE.md` IV.1. Same label = contractible fibre = unique
  preimage = no allocation. Different label = non-contractible fibre =
  the leftover made physical = allocation. The machine's one paid
  decision is the mathematics' invertibility test.
- `fibre/src/Fibre/Residue_…` §2 (`ग्राह`). One graph
  `Σ a. Σ b. (f a ≡ b)`, two projections. The source projection is always
  an equivalence (`Carrier≃-via-law`); the target projection is one
  exactly when every residual `शेष b` is contractible. Read on the net: a
  SUP at label `L` is the total space of a family over the one-bit base
  whose name is `L`. A DUP at `L` is the source projection, always free:
  it routes. A DUP at `M ≠ L` reads the same total space through an
  independent coordinate, the product, and pays.
- `theorems/physics/Bandha_…`. `cnot (a, false) ≡ (a, a)`: the
  correlated diagonal is the bond, and `entangling` proves it does not
  factor into independent single-coordinate maps. A same-label SUP inside
  a dependent family is exactly this: the index choice and the value
  choice are one choice, and no factoring into two independent labels
  exists.
- `Kernel/Avirodha_…` §5 and abstracts 16, 20. Nothing is deduplicated;
  `advance` conserves multiplicity. Collapse (`-C`) enumerates the fibre
  over an outcome, and an erased branch (`&{}`) is the empty fibre
  (नास्ति), not a merge of two.
- `HLEVEL_OF_INTERACTION` and `theorems/residue/Niyati_…`. The h-level of
  the event datum controls the contractibility of the history. A question
  is a SUP whose label is the question; the environment's answer is a DUP
  at that label; every question contractible means no SUP, one history.

### The typing rule this forces, and its implementation

Bend2 typed `&l{a, b} : G` by checking both branches against the whole
goal. That is the product rule. It is right when `G` is rigid and right
when `G` is a top-level SUP at `l` (the patch already special-cased that),
and wrong for every other shape: a goal `F(&0{True, False})`, or
`Σ n : F(&0{…}). Bool`, or `List(&0{Nat, Unit})`, made the checker demand
that `3n` inhabit `&0{Nat, Unit}`, which it rejected.

The rule the mathematics states is the runtime's own rule run on the type:

    &l{a, b} : G    iff    a : G₀  and  b : G₁    where (G₀, G₁) = dup l G

`dup` (Core.WHNF) pushes a label-`l` duplication through every former,
routes a SUP at `l` and crosses a SUP at any other label. So a value whose
label is the label of the index it depends on is typed fibrewise, and a
value at an independent label must inhabit both fibres. This is the
`(Sup l a b, goal')` case of `check` in `cubical-paths.patch`; it replaces
the two earlier cases and subsumes both.

Verified (`sup_dependent.bend`, `sup_dependent_mustfail.bend`, in
`verify_conductive_entry.sh` and the suite registry):

| term | checker | HVM4 `-s -C10` |
|---|---|---|
| `(&0{True,False}, &0{3n,()}) : Σ b:Bool. F(b)` | ✓, normaliser prints `(True,3n)` and `(False,())` | two readings: `#Pair{1, 3}` and `#Pair{0, #One{}}`, each beside its type; 11 interactions |
| `(&0{True,False}, &0{(2n,True),((),False)}) : Σ b. Σ n:F(b). Bool` | ✓ (dup pushed through Σ) | — |
| `(&0{True,False}, &1{&0{1n,()}, &0{2n,()}})` | ✓ (product outside, diagonal inside) | — |
| `(&0{True,False}, &1{3n,()})` | ✗ Mismatch (`3n` is not a point of `Unit`) | never emitted |

The cross term `(3n, False)` is admitted by no label, and it never appears
on the net. The checker, the normaliser and HVM4 agree because they now run
one rule. The typed point `#Pair{#Sig{#Bool, λb. F b}, #Pair{&L0{1,0},
&L0{3,()}}}` is the object; its collapse is the fibre.

## 2. Order is a gauge; the schedule is not a question

I once wrote that the confluence theorems say every schedule is correct and
then called the choice of schedule an open problem. The first clause refutes
the second. The corpus:

- `fibre/src/Fibre/Order_…` (Krama). A commutation certificate turns any
  interleaving into `normal (countL w) (countR w)`: the residue of a word
  is its pair of counts and its sequence is discarded with a proof. Its
  failure is retained: `suc` and `double` compute 2 and 1 from equal counts,
  so there the order is data.
- `theorems/automata/PairwiseCommutationGivesEveryOrder`. Pairwise
  commutation of the steps gives agreement of every order, compressed and
  uncompressed, and a point where two orders disagree is off the image of
  the projection: conflict names a state, not a pair.
- `Coordination/Serialization` (K2). Mazurkiewicz trace equivalence,
  `trace-sound`; and K9 as a term: ignorance is not independence.
- `Kernel/Avirodha_…` §3–§4. The merge is order-independent and
  idempotent; meaning lands in a proposition, so consensus on meaning is
  vacuous; what differs is the route, and it is kept.
- `PUSC.md`. The interchange law `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁) = (f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`:
  a sequential schedule is a traversal of the dependency structure, not
  the identity of the computation. `CONVERGENCE.md` Part I: interaction
  nets are strongly confluent, so the interaction count to normal form is
  the same on every reduction order (Lafont); order is never a choice.
- `NaturalMachine/Prastara_…`. A stream of gauges costs zero carried bits
  however long it is and however large the gauge group; the price of a
  disturbance is the image of the disturbance under the evaluation, not
  its cardinality. The scheduler's freedom is that gauge stream.

So the cost is the interaction count on the typed root (`TYPED_POINT.md`),
a `Matra` on the presented route (`theorems/grammar/Laghava_…` §1, §5),
invariant under schedule. What a schedule changes is the wall time of a
particular machine, which is a different `Matra` on a different
presentation. `research/PNP_GEODESIC_REDUCTION_20260916.md` D3 says a cost
transfers along an equivalence exactly when the equivalence respects it, so
the machine's `Matra` is the machine's to state. The floor beneath every
machine is `theorems/cost/Machine_…`: `kT ln 2` per bit forgotten, that is,
per non-contractible fibre crossed. Parallel depth is the dependency cone
(G4 of the same note), which coincides with work only for some tasks. None
of this is open. The sentence is retracted.

## 3. The price of Glue is the non-contractible fibre, and nothing else

- `theorems/CompressionIsTransport…` §1–§4. The codec `A ≃ Σ B (fiber f)`
  is an equivalence, hence priceless as a recoding; the residue collapses
  where every fibre is contractible; a bit is forced only at a `b` whose
  fibre is not a proposition. That is the whole cost.
- `theorems/grammar/Laghava_…` §4. `Bool ≃ Bool` under composition is a
  group with a non-identity element, so **no cost function exists on the
  transports of Bool**. The equivalence `e` carried by a Glue face, as a
  point of the groupoid, has no price.
- `research/PNP_GEODESIC…` D1, G3. That does not forbid positive geodesic
  length on a generator set: `Bring(n)` is an equivalence and its minimum
  word length is exactly `n`. A route that computes `fst e a`, or the
  centre of a fibre, has a `Matra`: its interactions.
- `UNIVALENCE.md`, `REF_ENDPOINTS.md`. `isEquiv` is a proposition
  (`isPropIsEquiv`, the 4-face `hcompN`). A proposition knows *that* and
  not *which* (`CONVERGENCE.md` II.4): its content is contractible and
  costs nothing until consumed. It is consumed only by `coe` to a symbolic
  endpoint (`RUNTIME_FULL.md`, caveats), where it is held as stuck data,
  which is the partial-knowledge discipline of `SYNTHESIS.md` §1, not a
  charge.
- `theorems/cost/Abhijnana_…` §१. `isContrSingl a .fst = (a, refl)`: the
  carried image and the witness that it is the image assert nothing, so
  carrying them costs nothing. This is why `#UaU{A, B, f, g, gf, fg}` may
  keep all six fields: four of them are determined by the other two.
- `theorems/residue/Ekatva_…` and `kernel-flat/AdiBija_…`. The lossless
  completion of a map is unique (`isContr (Lossless f)`), and every reading
  of a system is the unique fold of one recursor. So there is exactly one
  `transpEquiv` up to a path, and sharing it across `N` transported values
  is not an optimisation choice but the object: one line, `N` values.
  `SYNTHESIS.md` §3–§4 measured it on the net: the transport is paid once
  under sharing (marginal 14 interactions against 150), and one shared line
  over `N` values costs 38 per value against 139 separately, improving with
  `N`. `N` different lines share nothing and pay a constant factor: the
  product of §1, as it should.

## 4. The runtime the theorems dictate

Stated as the specification of the next runtime and language, in the
user's phrase hvm5/bend3, with the module that forces each line.

1. **The object** is a typed point of `Σ X : Set. X`, the universal family
   `π` of `fibre/src/Fibre/Universal_…` §1. Every family is its pullback
   (§2) and the tower flattens (§7), so types, values, paths and processes
   nest without leaving the one runtime type. This is `TYPED_POINT.md`.
2. **The agents** are LAM/APP, DUP/SUP with labels, and constructors for
   cells: the interval, `#PLm`, `#UaU`, `#HCm`, `#Glue`, HIT cells, and
   types. Nothing else. The one paid interaction is DUP meeting SUP at
   different labels; every other interaction is wiring. Types are cells,
   consumed by `coe` and by checking (`RUNTIME_FULL.md`).
3. **The type theory** is CCHM with univalence computing through Glue,
   Σ and Π, inductives and HITs by one declaration schema (`HITS.md`),
   coinductive records with productivity (`COINDUCTION.md`), and the fibre
   law as the composition principle: every map is the projection of its
   lossless completion (`theorems/residue/Vishvayantra_…`), the completion
   is unique (`Ekatva`), and `LawfulStep A ≃ (A → A)`. Hence there is no
   reversible mode and no lossless mode: the runtime keeps the fibre as
   SUP/DUP labels, where a label is the name of a base coordinate and a
   DUP at that label is the source projection.
4. **Superposition is typed by the DUP of the goal** (§1). A superposition
   of types is a type, a SUP cell in `Set`, and `coe` along it needs no
   rule (`RUNTIME_FULL.md`, `supline.bend`).
5. **Cost is the interaction count**, invariant under schedule, certified
   exactly by potential functions (`README.md` §9, Pareto in `ℕ^d`), with
   the floor `kT ln 2` per non-contractible bit (`Machine_…`). There is no
   scheduler in the semantics; strong confluence is the scheduler (§2).
6. **Search is evaluation.** A candidate family is a SUP; a specification
   is a map out of it; the survivors are its fibre; collapse conserves
   multiplicity and never deduplicates (`Avirodha` §5, abstracts 16 and
   20); `&{}` is the empty fibre. `SUPGEN_DEMO.md` is §1 applied to a SUP
   of programs, and with item 4 the survivors are typed fibrewise: a SUP of
   programs at the label of a SUP of specifications is checked branch by
   branch, so type-directed synthesis is the same rule.
7. **Interaction** is the coalgebra `ISC` of
   `fibre/src/Fibre/Interaction_…`: `react` returns the successor, the
   observation, the event datum and the continuation together. Questions
   are SUPs whose label is the question; the environment's answer is a DUP
   at that label; a history is its answer stream (`run-is-answers`,
   receipts weigh nothing); contractible questions give one history
   (`silence-is-determinism`, `Niyati`). A derived identity is installed
   where it was proved (`kernel-flat/IntrinsicRewrite`, `view-install`) and
   the library grows by concatenation with nothing to validate, because an
   operation cannot exist without its derivation (`Avirodha` §3). So the
   set of executable identities grows during reduction: `README.md` §8,
   `R_t = R_t^*`.
8. **Verify is decide.** `theorems/residue/VerifyIsDecide_…`: finding and
   checking are the two directions of the one equivalence `lossless uStep`,
   and that equivalence is unique. So the checker is not a phase before
   emission; it is the type projection of the typed point, evaluated by
   the same reducer, and conversion is a path cell reducing. Today the
   Haskell checker runs before emission and is the one second evaluator
   `TYPED_POINT.md` item 9 still tolerates, as the gate. The theorem fixes
   the direction: fold it into the net. That is labour, not a question.
9. **Declarative execution**, precisely. `README.md` §10: optimal
   interaction execution is the minimum interaction count over executable
   equivalent presentations. `NaturalMachine/Laghava` proves that the size
   of a presentation is not a function of its meaning, so two spellings of
   one function are two presentations with two costs; but the identity
   between them is itself an executable path (`README.md` §2, §8), and the
   runtime installs it (item 7). The guarantee "any function receives
   cost-optimal execution regardless of how declared" therefore reads: the
   cheapest presentation reachable by executable identity is what runs,
   reaching it is itself reduction, and the reachable class grows as
   identities are proved. Not "every spelling costs the same", which
   `Laghava` refutes.

## 5. What remains is labour, and it is listed

- Fold the checker into the net (item 8).
- Dependent transport to a symbolic endpoint: hold it as a stuck cell that
  resumes when the interval is decided, as `#HCm` does, instead of the
  `#StuckCoe` dead end (`RUNTIME_FULL.md` caveats; `SYNTHESIS.md` §1).
- `infer` for a superposition (`&l{a, b}` infers `&l{A, B}`) and the same
  DUP rule for `Frk`.
- The HVM4 printer diverges on a typed point containing a recursive
  function; observe such a point through a map out of it (`RUNTIME_FULL.md`).
- `Op1`, `I64`, `F64` as cells rather than refusals.
- The port of the remaining corpus modules (`AUDIT.md`: nothing needs a
  feature Bend lacks).

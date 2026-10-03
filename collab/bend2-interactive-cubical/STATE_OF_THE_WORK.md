# State of the work: where we are coming from, what is known, where we are going

*Everything learned in this lane so far, written once so that the next reader,
human or agent, starts from reality and not from a prior. Companion to
`TYPED_POINT.md` (the standing design note) and `SETTLED_BY_THE_CORPUS.md`
(three questions dissolved by theorems already in the repository). Every
claim names its source. Nothing here carries a time unit.*

---

## Part I. Where we are coming from

### I.1 The repository

`avikj/metacircular-interaction-prototype`, described as "pure math". The
checked core is 2319 Agda files under `--cubical --safe` (Agda 2.8.0,
agda/cubical v0.9; no postulates, no holes). They are organised in lanes:

| lane | files | what it carries |
|---|---|---|
| `formal/cubical/theorems/physics` | 277 | braids, unitarity, gauge, entanglement, oscillators, Weil positivity |
| `formal/cubical/theorems/number` | 202 | residues, moduli, Nerode congruence, cost geometry, tomography |
| `formal/cubical/theorems/residue` | 156 | the fibre lane: Vishvayantra, Ekatva, Niyati, Prasna, VerifyIsDecide, Anveshana, Avinimaya |
| `formal/cubical/theorems/historical_proofs` | 149 | Piṅgala, Āryabhaṭa, saptabhaṅgī, firm factorisation, Samkramana |
| `formal/cubical/NaturalMachine` | 140 | Laghava, Prastara, cost geometry, machine loop, cohomology |
| `formal/cubical/theorems/unplaced` | 122 | Sīmā (the frontier), stagewise composites |
| `formal/cubical/theorems/logic` | 121 | Sarvavibhāga, Koṣṭha-nyāya, standpoints, NKS univalence |
| `formal/cubical/theorems/cost` | 80 | Abhijnana, Machine, AvarohaNisedha, DvitiyaNiyama, payload morphisms |
| `formal/cubical/theorems/automata` | 68 | order independence, pairwise commutation, Asanna, Nirmāṇa |
| `formal/cubical/theorems/walks` | 57 | walks and charted caps |
| `formal/cubical/theorems/grammar` | 55 | Laghava (cost vs inverse), Antya, Pāṇinian machine loop |
| `formal/cubical/theorems/primes` | 50 | damping ladder (Sopāna), Weyl pairs |
| `formal/cubical/kernel-flat`, `Kernel` | 41, 23 | RewriteCertificate, IntrinsicRewrite, AdiBija, Avirodha, AnswerIsProjection, provenance |
| `formal/cubical/theorems/metre`, `lattices`, `order`, `homotopy`, `must_fail`, `Mula` | 34, 32, 27, 27, 11, 16 | |
| `fibre/src/Fibre` | 27 | the fibre library proper: Carrier, Trace, Residue, Universal, Order, Orbit, Nucleus, Interaction, Ekatva-adjacent |

Around the core: `abstracts/` (numbered one-page statements of results,
01 to 59, each ending "machine-checked, no postulates"), `research/` (SAT
derivations, the P versus NP geodesic note, SHA-256 decompositions,
finite-field identities, biology, superconductivity, rule 30, Rubik's cube,
Pratt/Chu), `notes/{engine,frontier,lineage}`, `interactive/` and `machine/`
(operational lanes in Haskell), `collab/` (the Bend lanes), `CLAUDE.md`
(the naming and sourcing rules).

Conventions that matter when reading it:

- A file's name is its theorem. A Sanskrit term names the object; the
  English after the underscore states the result. The term is sourced by
  `MulaVakya_SourceStatementsForTheTermsInOurFileNames.txt`; a compound
  built in the repository is declared as such and not passed off as a
  citation (Apratikaryatva's header is the model).
- Re-derivation is the named failure mode. A theorem has one locus
  (`एकाधिकरण`); a second proof of a special case is a defect even when both
  are green (Samkramana §3 records a cut for exactly this).
- Every claim is a term or is marked as prose. Documents tag `[T]`
  (checked term), `[R]` (statement about checked terms), `[open]` (a type
  posed, not inhabited).

### I.2 The Bend lane and what was built in it

`collab/bend2-interactive-cubical/` adds a CCHM cubical layer to Bend2
(DKormann fork, pin `f026483`) as one patch, `cubical-paths.patch`, and
targets HVM4 (`HigherOrderCO/HVM4` @ `6defdfc`). The layer was built in
this order, and each layer has its files and its verification:

1. **Paths and transport.** Interval with De Morgan structure, `Path`/
   `PathP`, path abstraction and application with boundary checks, `coe`
   with dispatch on the type former (Π, Σ, List, rigid inductives, `Set`),
   regularity decided up to conversion, `J` as `coe` along the connection
   square, `ua` with definitional `uaβ`. `cubical_test.bend` and siblings.
2. **General composition.** One constructor `HCm A [(φ,u)] base` with
   arbitrary DNF faces, per-cell boundary and adjacency checks; `hfill`
   sugar; `isPropIsContr` green with the 4-face system (`isprop.bend`).
   The typed endpoint law extended to `Ref`-headed spines
   (`REF_ENDPOINTS.md`) is what let `isPropIsEquiv` be definitional.
3. **Univalence, coherent.** `Equiv = Σ f. ∀y. isContr(fiber f y)`;
   `uaE`; `pathToEquiv`; both round trips (`uaequiv.bend` 17✓,
   `roundtrip.bend` 21✓). Raw-Iso reverse trip fails as it must
   (`uaroundtrip.bend`).
4. **The universe's Kan rules.** `Glue` with boundary laws and the
   coherence obligation; transport through Glue; `hcomp` in `Set` reduces to
   Glue with `transpEquiv`; `ua` derived from Glue with `uaβ` definitional
   (`GLUE.md`, `uaglue.bend` 26✓, `hcompset.bend` 10✓). Also `Partial`,
   `Sub`, `comp`, `transp` with a cofibration (`REMAINING.md` §C).
5. **The fibre law, on the net.** `fibrelaw.bend` (35✓): `lemIso`
   transcribed, `totalEquiv` for every `f`, `losslessPath = uaE(totalEquiv)`,
   `present`/`retrieve` with `refl` laws. `forcing.bend` (62✓) and
   `forcing_run.bend` (82✓): the `Fibre.Trace` core, executed on HVM4.
6. **HITs by one schema.** `type … path @c(fields): Path(…)` of any
   dimension; `hrec`/`helim`; elimination commutes with `hcomp`; `coe`
   pushes into constructors of parametric HITs; circle, suspension,
   pushout, torus, Klein bottle, set quotient with effectivity (23✓),
   truncations (`HITS.md`, 16 files). The minimal Nerode machine computes
   and behavioural equivalence is path equality both ways, with
   `isSet hProp` proved from scratch (`QUOTIENT.md`).
7. **Coinduction.** Corecursive records, corecursive bisimulation paths,
   a productivity classifier gated by `--total`; `run-is-answers` and
   `silence-is-determinism` as corecursive paths (`COINDUCTION.md`,
   `silence.bend` 25✓); the braid relations pointwise on the net
   (`INTERACTION.md`).
8. **Runtime targets.** `--to-hvm4` (normalise then erase), `--to-hvm4-raw`
   (erase, strict, universe paths as Church pairs, closed path algebra of
   `RUNTIME_ALGEBRA.md`), `--to-hvm` (HVM3), and `--to-hvm4-full`
   (`RUNTIME_FULL.md`): the interval, paths, types, `coe`, `hcomp`, Glue
   and HIT cells as runtime data, `@coe` dispatching at runtime, stuck
   `#HCm` as partial knowledge. Measured: transport paid once under sharing
   (marginal 14 interactions against 150); one shared line over N values
   38 per value against 139 separately; N different lines pay a constant
   factor (`SYNTHESIS.md` §3–§4).
9. **Ports.** `port/*.bend`: Prelude, RewriteCertificate, ControlledGrammar,
   GenerativeKernel, EveryDerivationIsInvertible, WindingCost, Carrier,
   HLevelOfInteraction, FibreElement, FibreCoalgebra, ConductiveRuntime,
   UniversalPresentation. `AUDIT.md`: nothing the corpus does needs a
   feature Bend lacks; the differences are stated (no implicit arguments,
   one-step untyped conversion, `Set : Set`, HIT parameters from the goal).
10. **The typed point** (PR 45, this lane's current head). Below.

### I.3 PR 45: the goal, the failure, the correction

**Goal** (the PR description): make `--to-hvm4-full` emit the whole checked
Cubical Bend object faithfully, without a second evaluator, compile-time
execution, erased cells, or an application-specific fibre wrapper. The
runtime object is the typed point `Σ A : Set. A`:

    @Dmain = <checked term>
    @Tmain = <its checked type>
    @main  = #Pair{@Tmain, @Dmain}

**The failure.** A prior agent spent twelve hours on this branch building
`NativeStep`/`nativeRun` (a compile-time Haskell recorder of Core.WHNF
reductions emitted as a derivation list), a handwritten `@cf*` HVM
"fibre bootstrap" prelude, and receiver lowerings. Every one of those was
the wrong layer, for reasons the PR description now states: the target
executes HVM4, not Core.WHNF, so a recorded WHNF trace describes a
different evaluator; `coe` has reduction premises, so a flat list is not a
proof object; a closed deterministic run's derivation is contractible
(Niyati; fibre-of-run), so precomputing it adds nothing; the relevant cost
is the HVM interaction count under sharing; and compile-time `nativeRun`
destroys productivity and can diverge. The transcript of that session is
the negative example: keyword pattern matching on the corpus's vocabulary
instead of reading the theorems, and building a second evaluator between
the object and the net.

**The correction, as executed on this branch.**

- Checker before emission; ill-typed input exits non-zero with empty
  stdout (`gate_mustfail.bend`).
- Every definition emitted twice (`@D`, `@T`) through one emitter; the
  root is the pair. `Target/HVM4Full.hs` `compileFull` emits exactly
  `@D…`, `@T…` and the root; no companions, no receivers, no prelude copy of
  the fibre law.
- Cells preserved: `#UaU{A,B,f,g,gf,fg}` (six fields), `#Eql{A,x,y}`,
  `#Enum{…}`, `#Num{…}`; `Op1`, `Met`, `F64`, `I64` refused rather than
  emitted as `&{}` or the identity (the old `not` lowering was the
  identity and produced a wrong SAT result).
- The derivation layer removed: `NativeDerivation`, `UniversalDerivation`,
  `UniversalElucidator`, `UniversalMachine`, `DependentFibreElement`,
  `DependentFibreCoalgebra`, the `@cf` bootstrap, and two probe files from
  the other Bend fork. `ConductiveRuntime.bend` and
  `UniversalPresentation.bend` rewritten to plain checked programs.
- HIT constructor parameters carried as cells. A bare `@seg{a}` carries no
  parameters and the checker reads them off the goal; the emitter used to
  emit `&{}` for them, which annihilated the whole value under collapse.
  Checking is now two passes: a silent pass records every bare
  constructor's parameters by source span (`recordFill`), the book is
  elaborated (`Core.Check.elabFills`, instantiating binders exactly as
  `check` does, with fresh placeholders per binder), and the reporting pass
  runs on the elaborated book. `hit_param_endpoint.bend`: the cylinder of
  `dbl` collapses its segment at 3 to 6 at both ends, in the normaliser and
  on HVM4; `hit_trunc.bend` survives `-C10`.
- A superposition typed by the DUP of its goal (`SETTLED_BY_THE_CORPUS.md`
  §1; `sup_dependent.bend`, its must-fail sibling).
- CI rewritten as one job (`.github/workflows/conductive-language-entry.yml`):
  bootstrap on the pins, `--total` on the four port modules,
  `verify_conductive_entry.sh` (TYPED-POINT, FIBRE-LAW-AND-CONTINUATION,
  CELLS, HIT-PARAMETERS, SUP-DEPENDENT, CHECK-GATE, TYPED-POINT ENTRY),
  map smokes, exact values for the canonical process and universal
  presentation, `suite.sh` (122 files, bad = 0, must-fail registry), SAT
  (XOR readings from one net; `sat_fibre` = `#Pair{#Bool{},1}`), the mining
  transport checks, the native list transport (26/26).
- Mining (`mining/mining.mjs`, `transport-checks.mjs`, README) follows the
  `@D` namespace; labels `T${n}` / `&N${i}{0,1}` (HVM4 labels are at most
  four characters); the verifier accepts `#Nil{}` and the ` #itrs`
  annotation `-C` prints.
- Docs: `TYPED_POINT.md` (design plus a ten-item regression checklist),
  `RUNTIME_FULL.md` ("Typed points"), `LANGUAGE_LEVEL…` §41,
  `SETTLED_BY_THE_CORPUS.md`, this file.

State at head `a43490c`: all three workflows green, mergeable clean, no
review threads.

### I.4 Toolchain facts and procedures (so nobody rediscovers them)

- GHC 9.12.2, cabal 3.14.2.0 via ghcup; `libgmp-dev`, `libtinfo-dev`,
  `libnuma-dev` needed; `LC_ALL=C.UTF-8` mandatory (the binary aborts on
  any UTF-8 source otherwise and prints nothing). `bend f.bend` checks and
  runs; `bend check` is not a subcommand and exits 0 silently.
- Build: `mining/bootstrap.sh NEWDIR` clones the three pins, applies the
  patch, writes `cabal.project`, builds; `env.sh` exports `BEND` and `HVM`.
  The working build is `/home/user/bend-build`.
- **Never edit a hunk by hand.** Regenerate: in the patched checkout,
  `git add -N` the untracked files, then
  `git diff -- . ':!cabal.project'` reproduces the committed patch byte for
  byte, and a change to the source is a change to the patch. Then
  `git apply --check` on a clean pinned checkout, and
  `python3 test_list_transport.py --check-only`.
- Local CI replica: `scratchpad/gates.sh` runs the workflow's steps; the
  suite alone is `bash suite.sh "$BEND"`.
- `suite.sh` has two registries: `NONTOTAL` (files allowed an `[unchecked]`
  definition) and `MUSTFAIL` (files that must contain a rejection). An
  unregistered rejection reads as a regression; a registered file that
  passes reads as a hole.
- HVM4: labels are 24-bit (at most four characters in the surface syntax);
  auto-dup labels are static per binder; `&{}` is both the eraser and the
  empty superposition and annihilates a branch under `-C`; references are
  expanded on normalisation, so `hvm -s` diverges on any value containing
  a recursive function (observe such a point through a map out of it);
  `-C` prints ` #n` after each reading; `#Nil{}` prints with braces; the
  binary is single-threaded (`hvm.c` line 6295 prints "A sequential
  Interaction Calculus runtime."; no threads, no atomics).
- Bend2 checker: HOAS terms; bidirectional `check` returning `Result ()`;
  `check` matches on `(term, force book goal)`; `dup :: Book -> Term ->
  Term -> (Term, Term)` in `Core.WHNF` pushes a labelled duplication through
  every former, routes a same-label `Sup`, crosses a different one;
  `hitify` makes a bare HIT constructor with empty parameters; the
  totality classifier treats a declared type as coinductive (a record
  field is never a descent position); Σ has η; `Set : Set`.
- `pkill -f gates.sh` kills the shell running it; use `pkill -x bend`.

### I.5 Errors made in this lane and how each was closed

| error | closure |
|---|---|
| patch corrupt at a hand-edited hunk count | recount, then the regeneration rule above |
| bootstrap failed on `-lgmp` | install the dev headers |
| CI YAML unparseable | rewritten as one job |
| suite `bad=2` | the two files were probes from the other fork; removed |
| list-transport fixtures with four-field `#UaU` | six fields |
| HIT parameters emitted as `&{}` | span-keyed fill recording plus elaboration; placeholder capture fixed with unique placeholders and an environment; elaboration made unconditional; the `Chk` annotated case accepts carried parameters; zero-arity constructors are not refused |
| mining labels longer than four characters; verifier choking on `#Nil{}` and the `-C` annotation | fixed |
| an ill-typed pushout eliminator written as a probe | replaced by the cylinder observed through its eliminator |
| `--total` refused on the derivation modules (fold under an arbitrary algebra over a declared type) | the modules were the wrong layer and were pruned |
| a superposed point of a dependent family rejected by the checker | DUP-of-goal rule |
| calling the choice of schedule an open problem after stating confluence settles it | retracted, `SETTLED_BY_THE_CORPUS.md` §2 |
| estimating in calendar units and framing the work as a contribution to be accepted upstream | dropped; the object is defined by the theorems, the substrate is whatever executes it |

---

## Part II. The mathematics, as read

This is the digest of what was read in full. The point of the digest is
that every design decision in Part III is a corollary of a line here.

### II.1 The fibre law and its family

- **Carrier** (`fibre/src/Fibre/Carrier.agda`). For `f : A → B`, a point
  of `Carrier f` is `(base, carried, witness : f base ≡ carried)`. The
  fibre over `a` is `singl (f a)`, contractible, so `A ≃ Carrier f` and by
  univalence `A ≡ Carrier f`. The spelling "fibre" (Σ over the codomain,
  the carried slot, free) is deliberately not cubical's `fiber` (Σ over
  the domain, the loss). Two implementation facts: `Cubical.Data.Sigma`
  not `Prod` (η), and `descend` must not pattern match. `carry-transport-
  descend = uaβ` is load-bearing: transport along `ua` does not reduce on a
  neutral variable.
- **Trace** (`Trace_TheTraceFamilyIsForcedToBeTheFibre…`). A
  `Conservative A B` is a family `Trace : B → Type` with
  `whole : A ≃ Σ b. Trace b`; the visible map `run` is read off it.
  Theorem: `fiber (run C) b ≃ Trace b` for any conservative factorisation.
  The fibre is the only residue up to equivalence; a factorisation cannot
  retain less. Corollaries: contractible trace ⟺ `run` is an equivalence.
  The proviso "any equivalence `A ≃ Σ b. T b` will do" is refuted:
  `Bool ≃ Σ b. Unit` factorises the identity, not `alwaysTrue`.
- **Residue** (`Residue_TheResidualIsTheOtherProjectionOfTheSameGraph`).
  The graph `Σ a. Σ b. (f a ≡ b)` is `Carrier f` by reassociation. Its
  source projection is always an equivalence; its target projection is one
  exactly when every residual `शेष b = Σ a. (f a ≡ b)` is contractible.
  The residual can fail two opposite ways, empty (नास्ति) or crowded
  (नष्टि), and the census `SakalaVikalaDesa` separates them. `Bool → Unit`
  has residual `≃ Bool`: one bit, priced.
- **Universal** (`Universal_EveryFamilyIsAPullbackOfTheUniverse…`). The
  universal family `π : Σ X:Type. X → Type`; every `B : A → Type` is its
  pullback along the classifying map, by `refl`; the classifier is
  `fibrationEquiv` (HoTT 4.8.3), whose content is `ua`. §5: a family is
  invisible over its base (projection an equivalence) iff every fibre is
  contractible, as an equivalence of propositions. §6: this is about the
  projection, not the mere existence of an equivalence (`Σ Bool Br ≃ Bool`
  with one empty and one crowded fibre). §7: a tower of families flattens
  to one family over the base, computed.
- **Vishvayantra** (`theorems/residue/…TheTuringStepIsTheVisibleProjection…`).
  `lossless f : A ≃ Σ B (fiber f)`, forward `a ↦ (f a, a, refl)`, visible
  projection `f` by `refl`. `LawfulStep` carries the commuting field
  `visible : π₁ ∘ complete ∼ step`, without which the equivalence may
  permute `A` and `step` is decorative; `trace-is-fiber` proves the field is
  exactly strong enough. An encoded universal machine (`Code = List Rule`,
  lookup answering `Maybe (m ≡ n)`, never a boolean); `turing-is-the-
  projection` is `refl`; halting is the table's silence; divergence is a
  refutation at every depth of a productive `exec`.
- **Ekatva** (`…LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleType…`).
  `Lossless f = Σ T. Σ (e : A ≃ Σ B T). π₁ ∘ e ∼ f` is contractible, by a
  chain of eight equivalences ending in a product of equivalence
  singletons (`EquivContr`). Hence `LawfulStep A ≃ (A → A)`: completion adds
  nothing and forgets nothing.
- **CompressionIsTransport** (`theorems/CompressionIsTransport…`). The codec
  is `lossless`; the residue collapses where every fibre is contractible; a
  bit is forced only at a `b` whose fibre is not a proposition. Perfect
  compression is `f` itself, by `refl`.
- **AReadingIsACollapse**. A reading is a collapse into a set with its
  kept middle (the Carrier) and owed residual; `middle ≃ Source` always;
  `middle ≃ Target` iff every residual contractible; the verdict reading
  `Bool → Unit` has residual one bit.
- **Anveshana**. Three grades of a fibre: contractible (nothing to
  search), propositional (unique if it exists; existence is the whole
  work; this is where an algorithm has content), neither. The h-level of a
  fibre does not track undoability: `Unit → S¹` has a retraction and fibre
  `ℤ`; the obstruction to undoing is two distinct sources over one target.

### II.2 Order, merge, consensus

- **Order** (`fibre/src/Fibre/Order_CommutationIsTheProof…`, Krama). For
  two steps with `Commutes = ∀a. f (g a) ≡ g (f a)`, any word `w` computes
  `normal (countL w) (countR w)`: the residue of a word is its counts; its
  sequence is discarded with a proof (the Mazurkiewicz quotient). Failure
  is retained: `suc` and `double` compute 2 and 1 from equal counts.
- **PairwiseCommutationGivesEveryOrder** (`theorems/automata`). Pairwise
  commutation gives agreement of every permutation, compressed and
  uncompressed; a disagreement at an observed state proves the state has no
  preimage. Conflict names a state, not a pair.
- **Serialization** (`Coordination/Serialization`, K2). A fixed event word
  (the data-passivity hypothesis as the type), `Indep` inhabited only by a
  commutation proof, trace equivalence generated by adjacent swaps,
  `trace-sound`; K9 as a term: `setTrue` and `flip` have no commutation
  proof and the orders differ; the combinatorial half (`LinextConnected`)
  is an interface.
- **Avirodha** (`Kernel/…TheKernelIsAReversibleGroupoidWhoseJoinIsConflictFree…`).
  `⊕` strictly associative and unital as data; `rev` total; `rev` is an
  inverse only up to meaning, and the gap is the śeṣa. The library merge is
  `++`: keeps both sides, invents nothing, order-independent, idempotent,
  total with no failure mode (an operation cannot exist without its
  derivation). Meaning lands in a proposition, so two nodes cannot disagree
  and consensus on meaning is vacuous; routes differ and are kept
  (`advance` never dedups).
- **Prastara** (`NaturalMachine/…TheGaugeStreamCostsZeroCarriedBits…`). A
  proof-carrying certificate; an arbitrary perturbation costs `evaluate d`;
  a gauge costs zero; a stream of gauges of any length costs zero and
  collapses to one gauge. The price of a disturbance is the image of the
  disturbance set under the evaluation, not its cardinality (Piṅgala over
  Ashby). Invisibility is weaker than gauge.

### II.3 Cost

- **Laghava** (`theorems/grammar/Laghava_TheCostAndTheInverseCannotCoexist…`).
  A `Matra` is an additive ℕ-grading; a `Laghava` also detects the unit.
  §2: a graded structure admits no inverse (one costly element suffices;
  unit-detection unused). §3: an invertible structure admits no cost
  (needs unit-detection). §4: `Bool ≃ Bool` has `notEquiv ≠ idEquiv`, so no
  cost function exists on the transports of Bool; cost is not a univalent
  invariant because it cannot live on the groupoid. §5: `len` is a Matra on
  derivations, so the kernel is not a group. §7: no function of any
  group-valued image recovers the cost. §8: nothing computed from the
  meaning sees the route.
- **NaturalMachine/Laghava**. Stronger and needing no univalence: no
  function of the denotation computes the size of a presentation, because
  two presentations with identical meaning have different sizes.
- **Abhijnana** (`theorems/cost/…TheReceiptAndTheElisionAgree…`). Bind `b`
  in `f a ≡ b` and the total space is `singl (f a)`, contractible with no
  hypothesis; bind `a` and it is the fibre, exhibited non-contractible for
  `Bool → Unit`. The centre `isContrSingl a .fst = (a, refl)` asserts
  nothing, which is why carrying costs zero. The codomain does not decide
  losslessness: a checker, not a reader, tells a receipt from an elision.
- **Machine** (`theorems/cost/…TheComputerIsTheGroupoidOfProofsOfTransport…`).
  Programs are equivalences; they form a groupoid with the five laws as
  library terms; running is transport and is a functor; a monoid machine
  lacks the inverse, and the missing inverse is the heat: `Q_min = kT ln 2 ×
  bits forgotten = kT × entropy of the fibre`, forced by Landauer and
  Bennett.
- **AvarohaNisedha**. An invertible element admits no nonzero additive
  cost; no receiver that inverts the generator carries an additive ℕ-cost
  back to it. **DvitiyaNiyama**: downstream, a collapse is forever (no
  later stage is a left inverse of a merging one); upstream, the ledger
  never forgets (the tape machine deepens addresses, never contents).
- **AnswerIsProjectionAtOutputSize** (`kernel-flat`). Reading the answer
  is `eval`, a projection, free; the canonical route's length equals the
  symbol size of the output, as an equation.
- **The geodesic note** (`research/PNP_GEODESIC_REDUCTION_20260916.md`).
  D1: an additive cost on a group is zero, but geodesic length on a
  generator set is subadditive and positive. G3: bringing cell `n` to the
  head of the rope costs exactly `n` crossings, lower bound over every word
  by the prefix theorem and the separating pair, attained by `Bring(n)`;
  reversible and still positive. D3: costs transfer along an equivalence
  exactly when the equivalence respects them. E: semantic factorisation
  carries no price; costed factorisation prices both directions and the
  interface.

### II.4 Interaction, process, kernel

- **Interaction / Samvada** (`fibre/src/Fibre/Interaction_TheOrbitIsTheOneQueryCase…`).
  `ISC Q O E w`: `react : (q : Q w) → Σ w'. Σ o. E w q w' o × ISC w'`. The
  orbit is the trivial-query case; under it every strategy gets the same
  answers; `counter` separates strategies at the first step. Nothing is
  globally normalised: a demand of length `n` asks `n` questions.
- **Orbit, Nucleus.** Path equality of orbits is bisimulation (`ua` of the
  iso built from four coinductive definitions); the carrier construction
  commutes with the whole trajectory, the transport version closing its
  head by `uaβ`.
- **Prasna, Niyati.** `IExec x ≃ Answers x` (receipts weigh nothing);
  contractible questions force a contractible run space; `one-execution :
  isContr (Exec mc)`, the contraction built coinductively with the
  ∨-square that collapses a receipt onto `refl`.
- **HLEVEL_OF_INTERACTION**. The h-level of the event datum controls the
  contractibility of the process; a question is a superposition, an answer
  a duplication; same label correlates, different labels are independent
  (`INTERACTION.md` measured it on HVM4).
- **IntrinsicRewrite** (`kernel-flat`). A `Run t`'s constructors are the
  executable motions; `result` and `run-sound` are two projections of one
  object; a locus reweaves a run into every rooted view; a `Delta` splices
  in front of an old run without traversing it (`view-install`).
- **AdiBija**. The kernel is initial: every receiver has a unique fold;
  soundness, length, the evaluator integral are each that fold.
- **VerifyIsDecide**. `decide` and `verify` are the two directions of
  `lossless uStep`; the witness self-certifies by `refl`; the equivalence is
  unique, so no other completion could host a gap.
- **Avinimaya.** Every table's step is unitary when completed and still
  the successor and the eraser do not exchange at a named configuration:
  reversibility is free, exchange coherence is data. **BahumargaBheda**:
  `loop ≢ refl` on the circle; the multiway does not collapse.
- **AnEquivalenceIdentifiesTheCarriers.** Three grades: satya (both
  inhabited), artha (`A ≃ B`), mūla (the sources agree). `ua` delivers
  artha; artha is strictly weaker than mūla (one identity equivalence, two
  disagreeing provenance maps). The retained object is the triple
  `(a, e, b)`; the existence of a route does not give the route
  (`Bool` has two). No third road: an answer is a transport or a written
  defect.
- **Samkramana.** Transport carries structure: operations go to their
  conjugates with `e` a homomorphism (`transportUAop₁/₂`), predicates to
  the same predicate; `∣_∣₁` is an equivalence exactly when `A` is a
  proposition, so truncation is what transport degenerates to where there
  was nothing to lose; a map lossless in both directions hands over its
  equivalence as data.
- **Bandha** (`theorems/physics`). CNOT is its own inverse (lossless) and
  does not factor into single-qubit gates; `cnot (a, false) ≡ (a, a)` is the
  correlated diagonal.
- **WitnessDichotomy.** Answerability is a gate, not an axis; past it a
  collision plus the floor is exactly 2.

### II.5 The abstracts read (14 to 25)

Patch theories from pairwise commutation; the Nerode congruence of a
modular sensor family computed as divisibility by the lcm; pruning by
observational equivalence collapses an unbounded fibre; the holonomy of a
circuit is the successor function and invisibility is invariance (the
converse free because `uaβ` is a path); two blind readings jointly
faithful; opacity is the fibre (phonology); the deduplication store is the
expensive object; a generating function does not determine a bijection
(the difference is a group action); full abstraction is the truncation;
proof logging must be online; cost and inverse cannot coexist; the
universal Turing machine is a forgetful projection.

### II.6 The lane's own identification (`README.md` §1–§10, `CONVERGENCE.md` IV, `PUSC.md`)

Sharing and independence are different Boolean spaces: the diagonal
`Δ₂ ≃ 2` (one bit) and the product `2 × 2` (two). `DUP_L ⋈ SUP_L → route`,
`DUP_L ⋈ SUP_M → cross`. Same label = contractible fibre = no allocation;
different label = non-contractible = the leftover made physical. Every map
is visible value plus fibre. Equivalent presentations are connected by
executable cubical paths, so factorisation is not restricted to the net
initially presented. Optimal interaction execution = minimum interaction
count over executable equivalent presentations. Exact cost certificates by
potential functions, Pareto in `ℕ^d`. The four words: parallel (independent
composition, the interchange law), univalent (the universe's identity
structure is computational, `Ω(𝒰, A) ≃ Aut(A)`), superposition (the
structural rules made explicit; labels are provenance), computer (closed
under construction and execution of programs).

---

## Part III. Where we are going

### III.1 The frame

There is nothing to merge and nobody to persuade. The object is fixed by
the theorems; the substrate is whatever open code executes it fastest; the
result runs or it does not. The next runtime and language are a new type
theory, runtime and execution semantics around univalence, built
independently with everything open today. No calendar units appear in this
lane's documents. The relevant history of HOC's runtimes is a sequence of
retreats forced by overheads, and every one of those overheads is a
theorem here about paying for a contractible fibre or erasing a
non-contractible one (Part III.3).

### III.2 HVM4: right where it has content, empty where the mathematics has content

Right: the one paid interaction (DUP meeting SUP at different labels) is
the invertibility test; strong confluence makes the schedule a gauge; Lévy
optimality is optimality for the corpus's cost model; lazy reduction is
corecursion; `&{}` is the empty fibre; superposition is first-class and
collapse enumerates the fibre.

Empty, each exposed by a piece of the surgery: no types at runtime (the
typed point was bolted on; the object is the total space of the universal
family); labels as a 24-bit budget with static auto-dup instead of typed
base coordinates; no interval, `comp` or Glue (added as constructors and
prelude functions; a stuck `#HCm` should resume by interaction); the checker
outside the net (VerifyIsDecide says checking is the other projection of
one equivalence); no installed identities (IntrinsicRewrite, AdiBija,
Avirodha: the library grows by concatenation at runtime); the printer
expands references; numerics as special cases; and one thread.

Why one thread: the strategy is lazy, implemented as a single demand
cursor with an explicit frame stack (`wnf`, `WNF_STACK`). HVM2 was strict
and fired every redex, which parallelised trivially and reduced branches a
later `&{}` erased. Lazy is the demand of the coalgebra; the parallel unit
in a lazy machine is the independent demand front, not the redex.

### III.3 HOC's retreats, diagnosed by the theorems

| retreat | the overhead they saw | what it is here |
|---|---|---|
| Lamping's oracle (brackets, croissants) → static labels | matching fans | the fibre's two projections; same label contractible, forced free; nested labels are the flattened tower (Universal §7) |
| strict GPU net reduction (HVM2) → lazy single cursor (HVM3/4) | work on branches that erase | reducing the empty fibre; the coalgebra demands, never normalises globally |
| garbage collection, erasure | the missing inverse | the monoid of irreversible steps paying Landauer; the groupoid pays only at the non-contractible fibre |
| Bend2 leaving nets for native primitives | interaction count of encodings | a presentation's cost is real and not semantic (Laghava); presentations are connected by executable identity; the minimum is over the class |

The theorem: the object's cost is exactly the non-contractible fibre, and
carrying determined structure is free. The claim still owed to an engine:
that a given loop attains that count edge by edge, which is the potential
certificate of `README.md` §9 and has not been written for `hvm.c`. The
measured constant factor on different-label crossings (about 1.4 to 1.8) is
the product's genuine cost.

### III.4 The specification of the next runtime and language

From `SETTLED_BY_THE_CORPUS.md` §4, with the engine added:

1. The object is a typed point of `Σ X:Set. X`, the universal family; every
   family is its pullback; the tower flattens.
2. Agents: LAM/APP, DUP/SUP with labels, constructors for cells (interval,
   `#PLm`, `#UaU`, `#HCm`, `#Glue`, HIT cells, types). One paid interaction.
   Types are cells consumed by `coe` and by checking.
3. CCHM with univalence computing through Glue; Σ, Π; inductives and HITs
   by one schema; coinductive records with productivity; the fibre law as
   the composition principle (`LawfulStep A ≃ (A → A)`); the fibre kept as
   SUP/DUP labels, a label being the name of a base coordinate.
4. Superposition typed by the DUP of the goal; a superposition of types is
   a type; `coe` along it needs no rule.
5. Cost is the interaction count, schedule-invariant, certified by
   potentials, floored by `kT ln 2` per non-contractible bit; no scheduler
   in the semantics.
6. Search is evaluation: candidates a SUP, specification a map out,
   survivors the fibre, multiplicity conserved, `&{}` the empty fibre;
   survivors typed fibrewise.
7. Interaction is the ISC coalgebra; questions are SUPs labelled by the
   question; answers are DUPs; identities proved during reduction are
   installed where proved and the library grows by concatenation
   (`R_t = R_t^*`).
8. Verify is decide: the checker is the type projection of the typed
   point, evaluated by the same reducer; conversion is a path cell
   reducing. The Haskell checker before emission is the one second
   evaluator still tolerated, as the gate.
9. Declarative execution, precisely: the cheapest presentation reachable by
   executable identity is what runs, reaching it is itself reduction, and
   the reachable class grows as identities are proved. Not "every spelling
   costs the same", which NaturalMachine/Laghava refutes.
10. The engine: lazy demand fronts as the unit of parallelism over a shared
    heap, with the independent sub-demands inside one weak-head reduction
    (both arguments of a strict binary operation, the fields a match forces,
    the two halves of a different-label commutation) as the fine grain.
    Neither HVM2's strict net-wide firing nor HVM4's single cursor.

What survives from Bend and HVM into it: the interaction rule tables
(APP-LAM, DUP-SUP, DUP-LAM, APP-SUP, the cubical cells added here), the
memory discipline and the GPU work of HVM2, Bend2's surface syntax and its
users. What does not: the erasing pipeline, the separate checker, the label
scheme, the printer, numerics as special cases.

### III.5 Labour that remains, and two ordering questions

- Fold the checker into the net (item 8).
- The lazy-parallel engine (item 10).
- Labels as typed coordinates in the surface syntax.
- Dependent transport to a symbolic endpoint held as a resuming stuck cell
  (like `#HCm`), not the `#StuckCoe` dead end.
- `infer` for a superposition; the DUP rule for `Frk`.
- The printer on recursive typed points (observe through a map out).
- `Op1`, `I64`, `F64` as cells.
- The port of the remaining corpus modules (`AUDIT.md`: labour, not gaps).
- A potential-function certificate for the engine's interaction count.

Two orderings the theorems fix in direction but not in sequence, put to
the author: checker-in-the-net before or after the engine; labels as typed
coordinates now or after the new core.

---

## Part IV. The reading that continues

The digest in Part II covers the fibre core, the cost and coordination
modules, the kernel-flat modules named above, twelve abstracts, and the
lane's documents. What is being read next, in order: the residue modules
the geodesic note cites (SamyogaSesa, Avaccheda, Varanam, NKSUnivalence,
Prasna, AnantaVeni, SthairyaSutra), Apratikaryatva and HidingAndHardness,
the Kernel modules the cost lane rests on (RewriteCertificate,
Residue_TheDerivationCarriesNoMeaning, AvrttiResidue, Vyapti,
Interaction_TheKernelIsAnInteractiveSystem), the SAT derivation series,
then the physics, number, logic, grammar, historical, automata, walks,
primes and metre lanes, the `research/` notes (biology, superconductivity,
rule 30, Rubik's cube, SHA-256, Pratt/Chu, nonhuman communication), and
`notes/{engine,frontier,lineage}`. The digest of each lane is appended to
`CORPUS_DIGEST.md` as it is read, so that what is learned survives any
one session.

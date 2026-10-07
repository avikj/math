# Hyperactive

**Read this section before anything else in this directory. It is the task. Every
regression this project has suffered came from someone building a smaller thing
than this and calling it progress.**

## 0. What this is

Hyperactive is a programming language whose runtime is the mathematics done
right, so that a declaration is the program. You write the type of a function
from lists to their sorted permutations:

    sort : Π (A : List Nat). Σ (B : List Nat). (multiset A ≡ multiset B) × Sorted B

and nothing else. The runtime produces B for any A, and the cost of producing it
is the minimum for that object. You never wrote an algorithm and never chose
one. On the next line you write

    sortCost : Π (n : Nat). Nat        -- the greatest cost of sorting any list of length n

and the same operation resolves it: over an unbounded domain, and over the
machine's own cost. If those two declarations resolve from the core, with no
organ written for lists, numbers, sorting or cost, everything else the language
is meant to be falls out. If either needs a special case, the core is wrong.

Why this is possible and not a wish, in the corpus's own checked terms:

1. **The fibre law.** For any f : A → B, A ≃ Σ_b fib_f(b), and for any lossless
   factorisation of a computation the retained trace is forced to be the fibre
   of its visible map (`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:133` `fibre-of-run`). A specification `Σ B. P A B` is a fibre. When it is
   contractible its centre is determined by A, so B is inferrable, not guessed.
   When it is empty there is no B; when it is crowded the specification
   underdetermines. The census says which, pointwise, three-valued, never a
   Boolean (`fibre/src/Fibre/SakalaVikalaDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:4` `देश`).
2. **The geodesic.** Under the one-step diamond every complete reduction of an
   object to its normal form has the same length and no first move can lengthen
   it (`research/sat_fibre/InteractionGeodesic.agda:45` `same-normalization-length`,
   `:53` `normalization-is-geodesic`). Interaction nets have the diamond because
   active pairs are disjoint. So the number of interactions from a declaration
   to its resolution is an invariant of the object, and it is the minimum,
   because every path is the minimum. Cost is not a performance figure and the
   programmer never thinks about it.
3. **Univalence computes.** A proved equivalence between two presentations is a
   path in the universe and transport along it reduces (`fibre/src/Fibre/Carrier.agda:118` `carry-transport-descend`). Meaning descends along it; cost does not. So the
   minimal count for an object is the minimum over its charts, and the only
   lever that changes cost is a proof.
4. **Cost and inverse cannot coexist.** Only forgetting costs. Nothing is erased
   inside a run; a demanded node fires once and every holder sees its value; a
   forgotten port is charged at the projection. The run's charge is interactions
   and heap words (`research/sat_fibre/InteractionLedger.agda:20` `Charge`,
   `:74` `interactionTotal-is-length`).
5. **Interaction is the operation.** A state faces a typed map and returns the
   successor, the observation, the event and the continuation
   (`fibre/src/Fibre/Samvada_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda:85` `react`). Two parts are projections of one joint
   (`formal/cubical/theorems/logic/Jiva_EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals.agda:137` `तुलना`); two peers with an overlap compose one trace
   (`formal/cubical/kernel/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:166` `interact`). What the runtime cannot infer is exactly the concrete, non-universal
   information, and it enters through a free port.

The universal part of mathematics is finite and already in the construction.
What the language accepts from outside is the specific: data, boundary
conditions, the choice at a crowded fibre. A deterministic physical law over its
boundary data is a contractible fibre and resolves like `sort`.

## 0.1 The mechanism, from the construction

The construction's whole machine is small:

- **A state** is a typed point (`fibre/src/Fibre/CorpusSamvada.agda:16` `Point ℓ = Σ[ A ∈ Type ℓ ] A`).
- **A question** is a typed map out of the state's type (`:21` `Question`).
- **A step** answers with the image of the point (`:25` `target s (B , f) = B , f (snd s)`). Its receipt and event are `refl`, and the run continues from the image (`:38` `S.react (run s) q`).
- **Presenting a point along a map** carries the image and its witness, and adds nothing: `descend a = (a , f a , refl)` (`fibre/src/Fibre/Carrier.agda:86` `descend a = carry a (f a) refl`), `ascend c = base c` (`:89` `ascend c = base c`).
  - The carried pair ranges over a contractible type (`:82` `fibre-isContr a = isContrSingl (f a)`), so presenting is an equivalence (`:105` `Carrier≃ = isoToEquiv Carrier-Iso`).
  - Transport along its `ua` computes to `descend` (`:119` `carry-transport-descend a = uaβ Carrier≃ a`).
- **The residual** a question leaves is inhabited by the point itself (`formal/cubical/theorems/residue/CorpusLosslessPresentation.agda:28` `current-residual s q = source s , refl`). It is never computed.

The core owes the language exactly the reduction of these:
- application;
- projection and match on constructors;
- superposition;
- faces;
- transport, hcomp, Glue and `ua`;
- trace and leaves as terms;
- the receipt of each rule at an active pair.

It does not solve for an unknown. An earlier core did: it made a bodyless declaration a coordinate, split coordinates at matches, unified at data types, and split the output of stuck computations. That machinery is not in the construction and has been deleted, along with the scheduler it needed.

A declaration with no body is resolved by the book, by type (step 5 below): the typed entries whose type converts to the declaration's are the fibre of the book over that type, and the declaration is the one entry when there is one. The chart move (step 4) is the construction's mechanism for reaching a specification's point; the map (`isort`) is written in the book, and the declaration reaches it through the book.

## 0.2 What regressing looks like, so you can recognise it

Today's session lost most of a day to each of these, in order. Do not repeat
them.

- **Building an interface instead of the language.** Subcommands that compute
  what a corpus module proves (a census mode, a joint mode, a meet mode) are
  organs. The constructions belong in the language as terms over the two
  primitives above, and the runtime has one entry: reduce, with check on the
  same loop. The modes this branch once had are gone; their probes are
  programs (step 3).
- **Building the runtime someone else already has.** An efficient interaction
  net exists (HVM). A cubical fork of Bend on it exists
  (`collab/bend2-interactive-cubical`). This directory is not a faster one of
  those. It is the language in §0, and the fork is its first dialect and its
  value oracle.
- **Importing the toy's frame.** `formal/cubical/Kernel/` is a first-order
  term-rewriting kernel whose own theorems show its `install` fires at exactly
  one term (`formal/cubical/Kernel/Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise.agda:118` `fires-only-at-source`) and cannot grow its reach
  (`formal/cubical/Kernel/Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateauSoTheKernelsOwnLibraryCannotGrowItsReach.agda:122` `install-chain-plateau`). Its vocabulary is not this language's design.
- **Deleting the cost.** The interaction count is a corpus quantity (item 4).
  Removing it because a toy also counted was wrong and was reverted.
- **Narrating from prior.** Every identifier in this file is cited to a file and
  line, and `cite.sh` fails the test suite when one does not resolve. A sentence
  that could have been written without reading the checked term it is about is
  not allowed here. Nineteen of twenty-one rules once cited theorems that did
  not exist; the table that exposed it is the reason this gate exists.
- **Inventing the cost model.** This file once said the proved count needed a
  face that "acts only at a superposition of its own name", never copying a
  constructor. The ledger's alphabet says the opposite: a duplicator meeting a
  node is the event `dupNode`, charged one interaction and the node's words
  (`research/sat_fibre/InteractionLedger.agda:16` `dupNode`, `:35` `localCharge`). A day was spent building a runtime around the invented
  sentence before it was checked against the cited line. The count's status is
  decided by the diamond and the schedule check, not by removing events.
- **Reading instead of building.** The object is fixed by items 1 to 5 and the
  modules they cite. A further module is read when its probe is being written,
  and the probe reproduces it by running.

## 0.3 Order of work

1. **The substrate. Written.**
   - Application, match, superposition and faces, each at an active pair.
   - Transport, hcomp, Glue, `ua`, and higher inductive types.
   - Tested by `t/basic.hyper`, `t/lazy.hyper`, `t/sup.hyper`, `t/kan.hyper`, `t/ua.hyper`, `t/setcomp.hyper`, `t/hit.hyper` and `t/erase.hyper`.
2. **The trace of a run and the leaves of a superposition as terms. Written** (`trace`, `leaves`; `t/meet.hyper`).
3. **Every rule fires at an active pair and is receipted. Written.** The value and the count are the same when the right demand is served first or a coin decides (`test.sh`, the schedule loop).
4. The chart move under a checked path. **Written, run, and checked** (`t/sort.hyper`, `chart-move`; `hyper check t/sort.hyper` → `✓ sort_at_A`, `test.sh`).
   The cheap chart is `Carrier isort` (`fibre/src/Fibre/Carrier.agda`): a list, its image under `isort`, and the
   witness. `descend a = (a, isort a, refl)` and `ascend c = base c`, and the two round trips are an iso. The
   prelude's `iso-to-equiv` is agda/cubical's `isoToIsEquiv`, term for term (`fill0`, `fill2`, `sq`, `sq1`,
   `lemIso`), and it makes the iso an equivalence. Transport of A along its `ua` is `descend A` (uaβ), and the
   carried image is `[1,2,3]` in 173 interactions, where the deleted narrowing core took 37,159 to resolve the
   type; no coordinate, split or unification. It is the same under the three schedules.
   **Closed.** `b/sort_at_A` states the specification at that B, `(B, (refl, refl))`, and `hyper check` accepts it: every
   definition on the path is typed, program text unchanged — `leq`, `insert`, `isort`, `sorted`, `A`, the carrier and its
   two round trips (`t/sort.hyper`), and the prelude's `fiber-ty`, `isContr-ty`, `Equiv-ty`, `isContrSingl`, `idequiv`,
   `ua` and the isoToIsEquiv tower `iso-fill0`, `iso-fill2`, `iso-sq`, `iso-sq1`, `iso-lem`, `iso-to-equiv`
   (`prelude.hyper`), the tower's `hfill` written out as the hcomp it is with static faces so the checker reads them; the
   run is unchanged at 173 interactions. `HYPER_CHECK_ALL=1 hyper check FILE` verifies every typed definition, the
   prelude's included (`main.c:73`). What the checker needed, all in conversion (`verify.c`): a face on a spine headed by a
   definition compared with the head still visible (`verify.c:196` `fce_through_spine`); two closures of one code compared
   by their frames and taken coinductively (`verify.c:226` `same_clo`); a restriction on a closure whose code can read
   nothing that mentions the name is the closure (`verify.c:175` `restriction_vacuous_on_closure`, `verify.c:187`
   `strip_scoped_faces`) — without it a restriction read through a frame re-wrapped a fix's closure afresh at every lookup
   and the coinductive memo never saw one pair twice; the memo reset per top-level comparison (`verify.c:138` `eq_reset`);
   `proj` inferred at a Sig (`verify.c:423`); a path accepted as a transport line (`verify.c:324`).
   `t/mustfail.hyper` holds the rejections these rules must keep making (a face the closure reads, two closures of one
   code over different values, `proj` off a non-pair, a path of the wrong family as a line), gated in `test.sh`. The
   checker differential against Bend2 (`checktest.sh`, `bendtest.sh`) was not run for these changes: Bend2's source is
   reachable only from GitHub, which this environment cannot reach, and no build of it is on the machine. Run both where
   Bend2 builds before taking the conversion changes as settled.
5. **A declaration with no body. Written** (`verify.c` `resolve_declaration`, `cell.c` at `T_REF`; `t/declare.hyper`, `b/sort_spec` in
   `t/sort.hyper`, `test.sh`). A declaration `name : T` with no body, when demanded, is the census of the book at `T`: the
   typed entries with a body whose type converts to `T` (the checker's conversion, on the same loop) are the fibre of the
   book over `T`, and the census is the corpus's three-valued one
   (`fibre/src/Fibre/SakalaVikalaDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:111` `देश`):
   `नास्ति`, no entry, and the declaration stays a coordinate (`hyper check` accepts it as one, `hyper run` refuses);
   `सकलादेश`, one entry, and the declaration IS that entry, receipted as one interaction (`declare`) — the identity
   available for its type, which the essay poses together with the declaration and normalizes (§5.27); `विकलादेश`, two
   entries, and the fibre is crowded: which one is concrete information and enters through a free port, never from the
   core (§0, item 5), so the run refuses and says so. The comparison is definitional and is not an event. Nothing is
   solved for: no coordinate is split, nothing is unified, no output is narrowed. `b/sort_spec` declares the sort
   specification at `A` with no body and resolves through `b/sort_at_A` to `([1,2,3], (refl, refl))` in 169 interactions,
   the chart move's 168 and the one `declare`.
   **The census at the point of demand** (`verify.c` `resolve_applied`, `census_point`; `cell.c` at `T_APP`) is §0's
   test met in its runtime form: `sort : Π (A : List Nat). Σ B. (isort A ≡ isort B) × (sorted B ≡ True)` declared with no
   body (`t/sort.hyper`), applied to a list, is a closed `Σ`, the fibre of the specification over that list, and its
   point is read off the book by the type's shape: a `Σ (b : B). P` takes `b` from the book — an entry of type `B`,
   or a book map into `B` at an argument of its domain (`isort`, in the book as data) — and `P[b]` by the same census,
   an `Eql u v` being `refl` when `u` and `v` convert: at a closed point the proof is the computation (§8.6). Points are
   counted up to conversion, three-valued as before. `sort A2` for `A2 = [2,3,1,0]` is `([0,1,2,3], (refl, refl))` in
   750 interactions, the candidates tried and refused included — that trying is the computation and is counted; the
   type comparisons that find the book's entries are not events. A map declared with no body and no entry of its own
   type waits for its arguments; a base result type is no specification and is refused. What is not here: the generic
   proof (`sort` checks as a coordinate of its type; the proof at every `A` is a theorem for the book, as is `sortCost`,
   which the same census serves the moment its identity is an entry).
   **§0, the declaration is the program** (`t/order.hyper`). Over the numeric kind, a comparison is one `op2`
   interaction and the ledger counts exactly the comparisons. The book holds the specification's vocabulary and
   nothing else: `leq` (the machine's comparison), `sorted`, `perm`, and lists. `sort` has a type and no body,
   `Π A. Σ B. (perm A B ≡ True) × (sorted B ≡ True)`, and the checker certifies it (`✓ sort : the arrangement
   census at every argument`). Its point is an assignment of indices to A's elements, and the kernel resolves it
   as such (`verify.c` `arrangement_point`, `cell.c` `arrange_sigma`): the index set has the binary structure of
   the naturals, so the carrier is split by halves — a hypercube of log n dimensions, not the list's succession —
   each half is the same declaration, and two resolved halves compose by the one comparison the specification
   leaves open, which of their two heads takes the next index. That comparison is `sorted` on the two-element
   list: the specification merging singletons is the base comparison, and every comparison made assigns an
   index (`compose` receipts, n⌈lg n⌉ of them). Nothing is written for sorting. `perm A B` holds by construction
   (B is A's own cells rearranged); `sorted B` is run once on the result as its certificate; the point is
   `(B, (refl, refl))`. Measured (`HYPER_CENSUS`):

   | n   | comparisons asc / desc / shuffle | n⌈lg n⌉ − 2^⌈lg n⌉ + 1 | ⌈log₂ n!⌉ | interactions asc / desc / shuffle |
   |-----|----------------------------------|------------------------|-----------|-----------------------------------|
   | 8   | 12 / 12 / 12                     | 17                     | 16        | 259 / 211 / 227                   |
   | 16  | 32 / 32 / 47                     | 49                     | 45        | 643 / 515 / 757                   |
   | 32  | 80 / 80 / 124                    | 129                    | 118       | 1,539 / 1,219 / 1,923             |
   | 64  | 192 / 192 / 293                  | 321                    | 296       | 3,587 / 2,819 / 4,509             |
   | 128 | 448 / 448 / 670                  | 769                    | 716       | 8,195 / 6,403 / 10,279            |

   The comparisons are within merge sort's bound at every n, and the interactions are within 13·n⌈lg n⌉: log n
   layers of composition, linear work in each. The loss against ⌈log₂ n!⌉ is exact and known: a head comparison
   between components of sizes n and m splits the outcomes n:m, which is 1:1 only while the two are equal, so the
   tail of each composition leaks; composing the two smallest components keeps that loss to O(n) in all.
   **The record of the two decompositions that failed** (`t/mapless.hyper`, kept as it was measured): the same
   specification over a line of arrangements built by *insertion* — the successor decomposition 1+(1+(1+…)) of
   the index set, n dependent layers — costs quadratic interactions with the kernel's sharing rules and cubic
   without them, and before those rules the comparisons themselves were re-made in every world, exponential.
   Inserting into a chain of length k extracts log k bits for k touches; composing two halves extracts one bit
   and one index per touch. The rules of `cell.c` that remove re-derivation (a face is the identity on a cell
   holding nothing of its name; a variable read through several restrictions is one face carrying the set; an
   application of a closure to a closed cell is derived once; a superposition with an erased side is its other
   side; an erasing match decides the worlds it meets, in bisection order) stand and are measured there.
   **`sortCost`, produced by the machine** (`t/mapless.hyper`): over a finite element type (`{0,1}`) the greatest cost
   exists and the same mechanism finds it — the domain of all lists of length `n` is one superposed line, its leaves
   are the points, each point's cost is the length of its own trace
   (`research/sat_fibre/InteractionLedger.agda:74` `interactionTotal-is-length`), and the greatest is a fold over them:
   `sortCost 1, 2, 3 = 18, 58, 242` interactions, with `costs2 = [58, 54, 54, 58]` for `[0,0], [0,1], [1,0], [1,1]`.
   A trace is of one run: taken over the superposition it carries every world's events, so the points come first
   and each is traced alone. Over Peano naturals no greatest exists (below) and the fibre is empty.
   **Charts, measured** (`t/msort.hyper`, `t/fj.hyper`). Merge sort written as a map in the book counts its
   n⌈lg n⌉ − 2^⌈lg n⌉ + 1 (worst case 5, 8, 11, 14 at n = 4..7); merge-insertion written as a map counts 5, 7, 10, 13
   at n = 4..7 and 46 at n = 16. These books contain the algorithm and are kept as measurements of the ledger only;
   the mapless book above needs neither.
   **§0, with the map in the book.** `t/sort.hyper` with every identity and lemma removed — `isort` and `sorted` present only as
   data, and the lists — still resolves the bodyless `sort` at `[2,3,1,0]` to `([0,1,2,3], (refl, refl))` in 1333
   interactions (`test.sh`, the no-lemma run): the point is read off the book by the type's shape and the proofs are
   the computation. Nothing written for sorting enters it. **The identities** `isort-sorted : Π l. sorted (isort l) ≡
   True` and `isort-idem : Π A. isort A ≡ isort (isort A)` are hand-written inductions in the same file; with them
   `hyper check` certifies the bodyless `sort` at coordinates (`✓ sort : resolved from the book at every argument`),
   without them it is a coordinate of its type. That line is worth exactly the identities someone wrote: the core
   poses a declaration with the identities available (§5.27) and invents none. The discipline those proofs needed
   (match only on variables; carry a neutral fact as an `Eql` hypothesis and match it against `Refl`; a rewrite is a
   pass, so expose each equation's cell in order — `sorted2`, `sorted3`) is the checker's recorded deviation seen from
   the proof's side; the checker now reads a goal and an inferred type under a branch's equations as it read the
   context (`verify.c` `check`, `verify`). **`sortCost`** is settled by the machine: `leq a b` costs `min(a, b) + 1`
   interactions over Peano naturals, so the cost of sorting a list of fixed length is unbounded in its values
   (`sort-B1`, `sort-B2`: 1132 and 2652 interactions for two elements) and the greatest cost has no point — the
   declaration's fibre is empty, नास्ति, which the census says rather than searches for.
6. **The Bend dialect's grammar as a book with its certificate, and parallel demand over the one arena. Written.**
   *The dialect.* `bend.hyper`'s rows are the book; its certificate is the checker: `transp`, `isProp-ty` and
   `qresp-ty` carry their types and check under `HYPER_CHECK_ALL`, and the recursor rows `srec`, `trec`, `qrec` are typed
   at their applications by the checker's own CRec/TRec/QRec rules with the motive read from the goal
   (`verify.c:838`–`:857`); `t/dialect.hyper` exercises all three, with a must-fail, gated in `test.sh`.
   *Parallel demand.* `HYPER_PARALLEL=N` serves independent demands on N workers over the one heap (`cell.c:33` `NPAR`).
   A demanded node fires once: its claim, taken by compare-and-swap in `whnf` (`cell.c:987`), and a second demand of
   the same node waits for the result instead of firing it again; allocation is an atomic bump on the one reservation
   (`cell.c:54` `alloc`), a receipt an atomic slot in the reserved trace (`cell.c:74` `receipt`), and what a reduction
   carries — the node under reduction, the world, the waiting face — is per thread. The independent demands are the
   other operand of an `op2` and the fields of a value (`cell.c:931` `par_spawn`, a hint: every spawned demand would be
   served anyway, so no interaction is added), the workers are started by `par_init` (`cell.c:948`) and the arena is
   quiet before anything is printed (`cell.c:956` `par_drain`). The diamond fixes what the schedule may change —
   nothing: `test.sh` requires, for fifteen runs, the sequential value, interaction count and words under four workers,
   and eighty runs under eight workers and the coin schedule showed no difference. What differs is the order of the
   receipts and, in the census, which event a word is attributed to; a run that traces itself as a term (`trace`) is
   served on one thread, since its events are its own alone. A declaration's census comparison is not an event:
   `verify.c:303` `NO_COUNT`.

## Read order

Read these before writing anything here, in this order: `fibre/src/Everything.agda`,
`fibre/src/Fibre/CorpusSamvada.agda`, `fibre/src/Fibre/Carrier.agda`,
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda`,
`fibre/src/Fibre/Samvada_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda`,
and §0 of `formal/cubical/Kernel/Avataranika_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda`.
Its test applies to every sentence of this file: a sentence that could have been
written without reading the checked term it is about is narration from prior.
Every identifier named below is cited as `file:line`, and `cite.sh` fails when
the identifier is not on that line of that file.

## The name

In an interaction net the only event is an active pair: two cells whose principal
ports face each other. Everything this program does happens at an active pair, and
a question from the world is one too (§2). The files are `.hyper`, the binary is
`hyper`, this directory is `hyper/`.

## 1. The substrate

A cubical type theory in which ua's β-rule reduces, with demanded (weak head)
reduction. `formal/cubical/Kernel/Avataranika_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda:407` `univalence-acts` is that fact as one term, and the descent note names it as the
whole reason the rest is possible.

The substrate is `cell.c`, `cell.h`, `read.c`, `verify.c` and the two rule files.
It reduces Bend2's dialect: every `.bend` under `collab/bend2-interactive-cubical`
is checked and emitted by Bend2 (`bend F --to-hyper`, `src/Target/Hyper.hs` in
`cubical-paths.patch`), run by `hyper bend`, and its value compared with Bend2's
own normaliser (`bendtest.sh`: 124 programs agree, 12 skipped because the oracle
itself does not run them). `verify.c` checks the same books and agrees with
Bend2's checker verdict by verdict (`checktest.sh`: 3862 definitions over 150
files, the must-fail probes included). `test.sh` holds the checks of the
substrate's own probes, its ledger, its schedules and its census.

What the substrate provides: cells over bound dimension names, frames with
descent, the face map (a dimension's endpoint, a choice name's side, a
coordinate's substitution), the interval as the free De Morgan algebra in
canonical form, transp and hcomp with regularity as an occurs check, Glue and
ua, higher inductive types by a schema (constructor boundaries read from their
types), fixed points, four numeric kinds, superpositions at bound names, and a
reader for its own text. Nothing is erased inside a run: a demanded node is
marked with its result once reduced (`T_IND`) and every holder sees the value.
The checker is bidirectional over static code with coordinates and rewrites via
the face map. The corpus's machine runs on cubical Agda; this evaluator exists
so that the machine can run without Agda or HVM, and it is the part of this
directory that is not itself the corpus.

Deviations from the mathematics, recorded: a non-variable scrutinee rewrites the
goal but not the context; a definition unfolds under conversion by its head
first; the branch-wise comparison of two stuck eliminators is bounded; a face
map passes through an application of a closed name into its arguments before
the name unfolds, the one rule that fires on a node that is not a value.

## 2. The primitive: interaction

Everything in this corpus is interaction, two-place at the least, and the
runtime's one operation is the coalgebra's `react`:
`fibre/src/Fibre/Samvada_TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers.agda:15` `ISC` (coinductive), `:85` `react : (q : Q w) → Σ[ w' ∈ W ] Σ[ o ∈ O w q w' ] (E w q w' o × ISC Q O E w')`:
one encounter returns the successor, the observation, the proof-relevant event,
and the continuation, which is again an interaction. Nothing is globally
normalised; a finite demand of length n asks n questions and forces nothing else
(`:103` `observe`). `:136` `det-observe`, `:143` `det-strategy-independent`: with
the trivial question every strategy sees the same prefix of the orbit; `:176` `counter-demand-matters`: with a real question two strategies disagree at the
first step. `LIFECYCLE.rst`: do not begin by assuming two independent machines
exchanging messages; start from the joint interaction and establish which
projections, dependencies and transports it admits.

Its instances, each a checked module, each computed by one mode of `hyper`:

**A typed point and a typed map** (`fibre/src/Fibre/CorpusSamvada.agda`,
whole: `:16` `Point`, `:22` `Question`, `:25` `target`, `:28` `Receipt`, `:38` `run`, `:40` `step`). A state is `(A, a) : Σ A. A`; a question is `(B, f)` with
`f : A → B`; the answer is `(B, f a)`; the receipt is the path `target s q ≡ s'`,
`refl` at the canonical step. The event is the residual:
`formal/cubical/theorems/residue/CorpusLosslessPresentation.agda:19` `Residual`
(`fiber (query s q) (query s q (source s))`), `:27` `current-residual`
(`source s , refl`), and `formal/cubical/theorems/residue/CorpusSelfPresentation.agda:12`
`present` returns the four together. The state carries its reading losslessly
(`fibre/src/Fibre/CorpusSamvada.agda:47` `State`, `:82` `state≡carried`,
by `fibre/src/Fibre/Carrier.agda:81` `fibre-isContr`, `:85` `descend`, `:104` `Carrier≃`, `:108` `Carrier≡`, `:118` `carry-transport-descend`). As written:
`hyper run FILE [DEF]` is the trivial query; `hyper interact FILE [DEF]` is
`present`: the point, then each line of the world a question, the point
presented along it, the new state `(q a, (a, refl))`; an `ASK` cell is a
question the point asks the world. The residual's census is a program (§3).

**Two parts of one joint**
(`formal/cubical/theorems/logic/Jiva_EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals.agda`).
A joint state is `J` with two projections, and everything is an officer of the
comparison `:137` `तुलना`, `j ↦ (p j , q j)`: `:142` `स्वातन्त्र्यम्` (independence
is the comparison being an equivalence), `:145` `संश्लेष-तन्तुः` (entanglement is
its fibre family), `:152` `संकलनम्` (the joint is the sum of its entanglement
fibres). `:167` `घटः-स्वतन्त्रः`: the product joint is independent. `:181` `रिक्तम्`: the diagonal joint has an empty fibre over `(true, false)`, a pair of
marginal readings the whole never realises. `:210` `गूढौ-भिन्नौ`: the joint over
`Unit × Unit` has two distinct residents over the one reading. A step on `J`
descends along a projection when some endomap of the part closes the square
(`:259` `युगलम्-उभयतः`); `:269` `जीवति`: the controlled-not refuses to descend
along the visible side, interrogated at `(true, false)` and `(true, true)`;
`:279` `दक्षिण-विलयः`: it descends along the hidden side by `refl`; `:289` `विलयः`: the step `(not a, b)` descends on both sides; `:305` `जीवन-द्विः`: the
living step is an involution, globally lossless, locally refusing.

**Two sessions and an overlap**: the encounter, §4b.

**The fixed alphabet.** A Chu evaluation `e : A × X → K` retains `k`; the
lossless interaction retains `fib_e(k)`, forced by
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:133` `fibre-of-run`; the general interaction is a family `R : A × X → 𝒰` classified
by the universal family, and a tower of such families flattens to one
(`fibre/src/Fibre/Visvarupa_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda:312` `flatten`). `CHU_LOSSLESS_INTERACTION.md` is the reading; the census of a map out of a
product domain, resolved pointwise, is the Chu matrix with its fibres.

`hyper check FILE` is `verify.c` on every definition; `hyper bend FILE` runs
`b/main` in Bend2's presentation, for the oracle.

## 3. The trace, and what a computation costs

Two measures, both corpus quantities, and they measure different things.

**The ledger: what a run costs.** `research/sat_fibre/InteractionLedger.agda:13` `Event`, `:20` `Charge` (`interactions`, `heapWords`), `:57` `Trace` (a run is a
sequence of events), `:65` `interactionTotal`, `:74` `interactionTotal-is-length`.
`research/sat_fibre/InteractionGeodesic.agda:14` `RandomDescent`, parametrised by
a one-step `diamond`; `:45` `same-normalization-length`: every complete reduction
of one object to its normal form has the same length; `:53` `normalization-is-geodesic`. As written: every rule appends its receipt to
`TRACE`, with the node it fired on and the heap length at that moment; a run
prints `- Itrs:` (the interactions) and `- Words:` (the heap words allocated),
the two components of `Charge`; `HYPER_CENSUS=1` prints each event's count and
the heap words it allocated, the events of the superposition algebra under the
ledger's own names (`dupNode`, `dupSupEqual`, `appSup`, …; step 5).
**The trace is a term**: `(trace e)` runs `e` to its normal form and is the
pair of the value and the list of its events, each event the rule's name as a
constructor carrying the words it allocated (`#beta{4}`), so the trace lives
over the result as in `fibre-of-run`, `interactionTotal` is `length` and
`ledger` is a fold, both written in the language (`t/meet.hyper`).
`(leaves e)` is the list of the leaves of `e`'s superposition, dead sides
dropped; `HYPER_SCHEDULE` serves the right of two independent demands
first, or a coin per choice, and `test.sh` and `bendtest.sh` require the same
value and the same count under the schedules (the diamond: distinct active pairs
are disjoint, so the order of two independent demands cannot change the count).
Definitional unfolding is not an event. The sharing regimes (`bendtest.sh`,
`bench_*_sup` against `bench_*_sep`; `t/ua.hyper`, a transport used k times)
are the reason a runtime exists at all: the superposition is one line over N
values and its cost is what the ledger shows.

**The census: what a question loses.**
`fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda:94` `Conservative` (`Trace : B → Type`, `whole : A ≃ Σ[ b ∈ B ] Trace b`); `:133` `fibre-of-run`: for any conservative factorisation the trace family is the
homotopy fibre of the visible map it induces. `:163` `exact-when-contractible`,
`:168` `contractible-when-exact`: the trace measures exactly the failure of the
visible result to be the whole event. `:185` `canonical`, `:198` `canonical-recovers`, by `refl`: the source was never left behind.
`fibre/src/Fibre/SakalaVikalaDesa_TheFibreCensusIsATermAndItRefutesTheSequentialDiagnostic.agda:4` `देश`, `:117` `गणना`: the census of a question, pointwise over the codomain,
three-valued.

Erase: nothing is erased inside a run; a forgotten port is one receipt where it
is forgotten (`t/erase.hyper`: the fibre's size never enters). Commutation is
the certificate that an order was removable:
`fibre/src/Fibre/Krama_CommutationIsTheProofThatTheOrderWasNeverThereAndItsFailureIsRetained.agda:106` `serialisation`.

## 4. What is not here, and why

Removed: `install` as this directory had it (a path between two definitions at
a type, then native dispatch), the parser producing Code, and the reifier. The
first was an invented shape. The corpus's `install` is
`formal/cubical/Kernel/ControlledGrammar.agda:27` `install`, from a
`Derivation`, a trace of steps between two terms, to a `NativeOperation`, and
its own theorems bound it:
`formal/cubical/Kernel/Vyapti_TheInstalledOperationHasNoneSoTheKernelMemorisesAndTheSchemaIsWhatMakesItGeneralise.agda:118` `fires-only-at-source`, `:181` `kernel-cannot-reach-a-tower`,
`formal/cubical/Kernel/Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateauSoTheKernelsOwnLibraryCannotGrowItsReach.agda:122` `install-chain-plateau`. In this runtime the derivation of a run is `TRACE`, and
a node once fired is marked with its result (`T_IND`), which is what installing
a run's derivation as a move amounts to here. A grammar's substitution is a
Carrier instance with a base and a carried datum
(`fibre/src/Fibre/Sthanivadbhava_TheAdesasFormIsTheFreeSlotAndItsDesignationsAreCarried.agda`),
not a parser.

## 4b. The encounter of two peers

`formal/cubical/kernel/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:125` `Peer` (a `Session`:
`formal/cubical/kernel/TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation.agda:4` `Session`, with `origin`, `here`, `trace : Derivation origin here`, `library`;
`:166` `_⊕_`),
`formal/cubical/kernel/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:4` `Encounter` (`A B`, `meeting`, `mine : Derivation (here A) meeting`, `theirs :
Derivation meeting (here B)`), `:138` `τ` (`mine ⊕ theirs`),
`:150` `gain` (the three moves installed), `:155` `A′`, `:160` `B′`, `:166` `interact` (`A′ E , B′ E , τ E`), `:174` `receive`. Reversal is
`formal/cubical/kernel/TheKernelIsAReversibleGroupoidWhoseJoinIsConflictFreeSoConsensusOnMeaningIsVacuous.agda:119` `rev`, the length
`formal/cubical/kernel/TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainder.agda:128` `len`.

As written (`t/meet.hyper`, a program over `trace`): a derivation is the trace
of a run as a term, `(trace a)` the value with its events over it; the two peers
meet when the values are equal (`eq-nat`), else there is no meeting; `mine` is
A's events, `theirs` the reversal of B's (each step under `Rev`), `τ` their
concatenation (`cat`), and the round trip `τ ⊕ rev τ`. Lengths are `length`, a
fold in the language. `t/meet.hyper` computes the module's sections:
`formal/cubical/kernel/TheEncounterOfTwoPeersIsOneTraceAndNoScalarProjectionOfItHasASection.agda:258` `the-two-results-need-not-agree` (the meeting is one value reached from two
terms), `:344` `undo` (`rev τ`), `:383` `round-trip` with `:395` `the-round-trip-is-not-done` (2·len τ steps from `a` to `a`; the meaning is refl,
the object is not done), `:412` `the-fabric-composes-strictly` (`cat`), `:447` `the-two-orders-differ` and `:451` `both-orders-cost-the-same` (the crossing:
`cross` under the two schedules reaches the same value with the same events;
the traces differ by the nodes they fire on, `HYPER_TRACE=1`), `:477` `the-scalar-is-additive` (`len (d ⊕ e) = len d + len e`). Not written: `:286` `what-crossed-is-what-B-had`, `:322` `the-pair-holds-it-after`, `:337` `the-prior-trace-is-a-prefix` (the session's library of moves: a construction
to be written as a program when a probe needs it), `:486` `no-section-for-any-order-blind-projection` beyond the crossing, and `:545` `the-receipt-does-not-cross`, which needs a demanded evidence (`demand R d`)
this runtime does not model.

## 5. Files

    hyper/cell.h             the word layout, tags, frames, constructors, the receipts
    hyper/cell.c             the substrate: heap, frames, instantiation, the interval, the face map,
                             case trees, the HIT schema, numbers, transp, hcomp, Glue, the loop, the ledger, printers
    hyper/read.c             the reader for the kernel's own text
    hyper/verify.c           the checker on the same loop
    hyper/main.c             run | bend | check | interact | net
    hyper/net.c              the interaction net the SAT fibre results were computed on: HVM4 6defdfc src/hvm.c
                             taken literally, with build_profile.py's receipt by rule (DUP-SUP-SAME/-DIFF)
    hyper/prelude.hyper 158  the Kan rows, Glue, transpEquiv, the HIT rows, as data
    hyper/bend.hyper     45  the Bend2 dialect's rows
    hyper/test.sh            the substrate's checks
    hyper/satcheck.py        research/sat_fibre reproduced exactly on `hyper net`: outputs, interactions, heap, rules
    hyper/bendtest.sh        values against Bend2's normaliser
    hyper/checktest.sh       verdicts against Bend2's checker
    hyper/cite.sh            every identifier this file names is on the line it cites

## The net (hyper/net.c, test_net.sh)

`cell.c` is a closure evaluator with the ledger's vocabulary; it is not the machine of §5.4 and nothing in it has
the one-step diamond. The machine is `net.c` (HVM4 verbatim, the net the SAT fibre receipts were computed on) with
hyper's agents, and everything cubical as programs on it. State, every line pinned by `test_net.sh`:

- **`%x`, the collapse as a value (COL).** On an erased world `#Nil`; on a superposition `@lcat` of both sides,
  multiplicity conserved; on a value, the superpositions inside lifted to the top (same label correlated) and one
  leaf. Four receipts. `n/xor` `n/same` `n/empty` `n/diff`. The `-C` readback is untouched: satcheck 282/282.
- **`?`, a fresh coordinate (FRS).** One interaction, the next number; `&(?){a,b}` is `dim`. `n/fresh.hvm4` measures
  HVM4's recorded defect (STATE_OF_THE_WORK I.4: labels static per binder) beside the fix: a static label under
  recursion reads the eight Bool lists of length 3 as two leaves; a fresh label names each unfolding, eight leaves.
- **A declaration with no body is a line.** `n/sort3.hvm4`: every arrangement of `[3,1,2]` as one line, `sorted` run on
  it, the survivor read by `%`, 458 interactions, nine comparisons. `n/sat3.hvm4`: a 3-variable proposition's fibre.
- **The cubical layer as net programs.** `n/cubical.hvm4` is the lane's full-runtime prelude (`coe`, `hcomp`, `hfill`,
  paths, the interval, Glue), run here: transport along `ua(not)` both ways (`n/ua`, 268 interactions), `hcomp` in
  Nat deciding a face (`n/hcnat`), transport along one shared superposed universe path read by `%` (`n/supline`).
- **Verify is decide.** `n/judge.hvm4`: a typed point `#Pair{T, D}` is well formed when the one equation
  `T === @infer(D)` reduces to 1 on the same net; `D` is quoted syntax read by `@eval` into the prelude's values.
  Π, Σ, Bool, Nat, Eql/refl; two must-fail cases reduce to 0; a superposed point against a goal is a superposition
  of equations with no rule added (`EQL-SUP`), read by `%` as `[1,0]`. `n/judgment.hvm4` carries the clauses, the
  lane's `Core/Check.hs` rule by rule: the interval and its operations, `Path` formation, `<i> t` against a Path
  with both ends, `p @ r` with the β case, `coe` along a line, `ua` with its six premises, `hcomp` with each tube's
  i0 end checked against the base on every cell of its face (the face's DNF, the environment fixed on the cell)
  and adjacent tubes compared on the cells of φ ∧ ψ, `Glue` formation with each face's equivalence against
  `@equivT`, `glue` against its Glue type with the sections carried to the base by `e`, `unglue`.
  `n/judgecub.hvm4` pins twelve cases including must-fails.
- **Labels are coordinates, in the kernel.** HVM4 gave a duplication binder one static label per binder, so a
  recursive unfolding reused it and distinct coordinates were read as one (the second of the three recorded
  violations). Each instantiation of a binder now takes a fresh label (`wnf_alo_dup`, the entry's third word), the
  default; `-L` keeps HVM4's discipline, under which the SAT receipts were recorded and still reproduce 282/282.
  The identity equivalence's contraction on a Glue face checks only under the fresh discipline (`n/judgecub`, case 11).
- **Neutrals are η-long by their type at creation** (`@nam`): a Π-typed neutral is the function that builds the
  neutral application, a Σ-typed one the pair of its neutral projections, a Path-typed one the line whose ends are
  its type's ends (the endpoint rule) and whose interior is the neutral application. HVM4 has no rule for a match
  on a lambda, so values are never matched for their shape; conversion is type-directed instead (`@convT`): Π by a
  fresh neutral, Σ componentwise, Path at `i0`, `i1` and a fresh neutral interval, the equation at base types.
  Eliminators for Bool, Nat and List against a goal; `fst`/`snd`; List, Unit, Empty.
- **HITs and the rest of CCHM** (`n/judgehit.hvm4`, twenty cases): the circle with `S1.rec`; `Partial`, systems
  (each branch on its own cells, agreement on overlaps, coverage of φ), `pout`; `transp` with a cofibration (the line
  constant on φ, cell by cell); `Sub`/`inS`/`outS`; the set quotient with `[a]`, `eq/` against a Path whose line is
  the quotient, and its recursor.
- **Not done:** Enum; the lane's eleven cubical programs re-run here (no Bend binary to emit them); parallel
  execution (this HVM4 is sequential; the diamond makes it legal).

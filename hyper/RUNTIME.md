# The runtime: cells, faces, and one reduction

This file states the runtime that `hyper/TASK.md` asks for: Lafont/Lévy-optimal reduction of cubical cell complexes.
That means (1) an arbitrary expression is a cell complex, and (2) every face and every identity of that complex is
filled and reduced. Every statement below names its source. A statement marked **derived** follows from sourced
statements but is not written in any source. Nothing else is added.

The previous version of this file was written from about a third of the design. It omitted:
- the face reading of duplication;
- the sharing of isomorphic subexpressions;
- the two-sided examination of operators;
- the colour-frame and cut factorings;
- everything the deleted cell kernel had already built.

It also contradicted the rule that nothing is erased inside a run. This version replaces it.

**What was read for this version, in addition to the sources of the previous one:**
- The essay "Respecting Equality" (`origin/main:docs/index.html`, commit `db2cd2677`): §5 and the section on search.
- The deleted cell kernel at commit `e47e4d185`: `hyper/cell.c`, `hyper/cell.h`, `hyper/NOTES.md` and `hyper/MAP.md`.
- The lane:
  - `README.md`, every section and Appendix A;
  - `PUSC.md`;
  - `CONVERGENCE.md`, Parts 0–IV and VII–XIII;
  - `SETTLED_BY_THE_CORPUS.md` and `TYPED_POINT.md`;
  - `SYNTHESIS.md`, `SUPGEN_DEMO.md`, `RUNTIME_ALGEBRA.md`, `INTERACTION.md` and `FIBRE_LAW.md`;
  - the "Design consequence" paragraphs of `CORPUS_DIGEST.md`.
- `research/sat_fibre/`: the modules SATBoundary, ColorFrame, RepresentativeContinuation, InteractionLedger and
  InteractionGeodesic, and the notes `DIRECTIONAL_SYNTHESIS.md` and `REDUCTION_FOUNDATIONS.md`.
- The construction:
  - `fibre/src/Everything.agda`, `fibre/src/Fibre/Carrier.agda` and `fibre/src/Fibre/CorpusInteraction.agda`;
  - the openings of `Ekatva_…`, `VerifyIsDecide_…`, `Vishvayantra_…`, `Parampara_…` and `Ubhayatah_…`;
  - §7 of the descent note.

## 1. The object

**Every definition is a typed point.**
- A checked definition `name : A = a` is the pair `(A, a)`, a point of `Σ (X : Set). X`.
- The root is `#Pair{@Tmain, @Dmain}`.
- Sources: `TYPED_POINT.md`; `fibre/src/Fibre/CorpusInteraction.agda:17` `Point ℓ = Σ[ A ∈ Type ℓ ] A`.

**Every family is a pullback of that one family.**
- A dependent type over `B` is the pullback of `π : Σ X. X → Set` along its classifying map.
- So types, values, paths and processes are all points of one object.
- Sources: lane `README.md` §4; `fibre/src/Fibre/Universal_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne.agda`.

**Nothing is erased and nothing is pre-normalised.**
- These are all runtime cells: intervals, paths, types, `ua` with all six fields, `hcomp`, Glue and HIT cells.
- Sources: `TYPED_POINT.md` ("Erasing any of them is lossy"); `SYNTHESIS.md` §1.

## 2. Coordinates, labels and faces, precisely

This section is the data structure. It fixes what the word "label" means in this runtime.

### 2.1 A coordinate

**A coordinate is the name of one binary direction of the cube.**
- A cell may depend on finitely many coordinates.
- Source: `PUSC.md` §3, the schematic object `A : Ω × Iⁿ → 𝒰`, in which "Ω indexes correlated branch choices; Iⁿ
  supplies cubical dimensions".

**There are two kinds of coordinate, and they share one face operation.**
- A **dimension** ranges over the interval `I`. A cell along a dimension has an interior. A path `⟨i⟩ t(i)` is defined
  at every `r : I`, and its endpoints are `t(0)` and `t(1)`.
- A **choice coordinate** ranges over the two endpoints only. A superposition `SUP_L{a₀, a₁}` is a cell along `L` with
  the two endpoints `a₀` and `a₁` and no interior.
- Both kinds have a face at 0 and a face at 1.
  - `PUSC.md` §3 says the two kinds "have different semantics" and that they "coexist" in one expression.
  - The deleted kernel gave them one face operation. In it, `T_SUP` is a 1-cell given by its two faces, `T_PLM` is a
    1-cell given by a formula, and `fce_apply` acts on both (`e47e4d185:hyper/cell.c`, `fce_apply`, lines 366–433).

**A label is the name of a coordinate.**
- The same label means the same coordinate.
- A different label means an independent coordinate.
- Source: `SETTLED_BY_THE_CORPUS.md` §1 and §4 item 3.

### 2.2 The face operation

**Definition.** For a coordinate `L` and a side `ε ∈ {0, 1}`, the face `∂_L^ε x` is the restriction of `x` to side
`ε` of `L`. It is defined cell by cell.

**The table.** The table below is the deleted kernel's `fce_apply` (`e47e4d185:hyper/cell.c` lines 366–433). Each case
already carried the ledger event named in its row (`research/sat_fibre/InteractionLedger.agda:13` `data Event`).

| `x` | `∂_L^ε x` | Ledger event |
|---|---|---|
| `SUP_L{a₀, a₁}`, at the same coordinate | `a_ε` | `dupSupEqual` (1 interaction, 0 words) |
| `SUP_M{a₀, a₁}` with `M ≠ L` | `SUP_M{∂_L^ε a₀, ∂_L^ε a₁}` | `dupSupDifferent` (1, 4 words) |
| `λx. t` | the closure, with the face recorded on its frame | `dupLamUsed` or `dupLamErased` |
| a constructor `K{f₁ … f_a}` | `K{∂_L^ε f₁ … ∂_L^ε f_a}` | `dupNode a` (1, 2a words) |
| an atom, or a cell that does not mention `L` | `x` itself, shared | `fce-share` in the kernel |
| the dimension `L` itself | the endpoint `ε` | `dupSupEqual` |
| a stuck cell | waits until its head is a value | none yet |

**Three equations hold, and they are the cubical identities.**
- **Faces at different coordinates commute:** `∂_L^ε ∂_M^δ = ∂_M^δ ∂_L^ε` for `L ≠ M`. The kernel's comment on the
  `dupSupDifferent` case is exactly "δᵢδⱼ = δⱼδᵢ" (`cell.c` line 388).
- **A face of a superposition at its own coordinate selects a side.** That is `dupSupEqual`.
- **A face of a cell that does not depend on `L` is the cell itself.** That is the degeneracy identity, and it is the
  sharing case.

**Substitution.** The kernel also has the substitution `x[L := r]` for an interval value `r` (side 2 in `fce_apply`).
It is the same operation taken at an interior point.

### 2.3 Duplication is the pair of faces

**`DUP_L x = (∂_L^0 x, ∂_L^1 x)`.** A duplication at `L` returns the two faces of `x` along `L`.
- Source: the emitter `Target/Hyper.hs` in `cubical-paths.patch`, whose comment on `SupM` is "the match is two faces".
- In the kernel's own text a duplication is written as the pair `(fce L 0 x)` and `(fce L 1 x)`.

**Derived: every HVM duplication rule is a row of §2.2.** So the ledger's alphabet is the face table, event for event:
- DUP-SUP with the same label is the face of a superposition at its own coordinate.
- DUP-SUP with a different label is the commutation of faces.
- DUP-LAM is the face of a closure.
- DUP-NODE is the face of a constructor.

**Derived: using a value twice is a duplication at a fresh coordinate.**
- A value `x` does not mention a fresh coordinate `L`, so both faces of `x` along `L` are `x` itself (the degeneracy
  row).
- Copying a value is therefore taking the two faces of a degenerate cell.

**The cost identity is the invertibility test.**
- At the same coordinate a duplication routes, with no allocation. That is the contractible fibre.
- At a different coordinate it crosses and allocates. That is the non-contractible fibre.
- Source: `CONVERGENCE.md` IV.1.

### 2.4 A name is the address of its binder instance

**The data structure.**
- A name is a 32-bit heap address: the address of the frame that bound it.
- A binder gets a fresh name each time it is instantiated, not once per occurrence in the source.
- Sources:
  - the deleted kernel's word layout `tag:8 | ext:24 | loc:32` (`e47e4d185:hyper/cell.h`);
  - `dim_push`, which allocates a fresh frame each time a path binder or a definition's dimensions are instantiated
    (`cell.c` lines 96 and 941–946).

**Why.**
- HVM4's labels are 24 bits and fixed per binder in the source.
- Two instances of one definition then carry the same label, and they annihilate where they should cross.
- The lane's prelude names this defect in a comment (`Target/HVM4Full.hs`, `freshName`).
- `CORPUS_DIGEST.md` calls it "labels-as-budget" and lists it as a violation of the specification. `hyper/TASK.md` §0
  item 2 records it.

**A declared label is a global coordinate.**
- A closed numeral label such as `&100` names one coordinate shared by every occurrence.
- That is how `research/sat_fibre/SATProcess.bend` shares one cube.
- Source: `Target/Hyper.hs`, `label`: "a closed numeral is a global choice name; a variable is itself".

## 3. Cells

A cell is a tagged node of words. Sources: `e47e4d185:hyper/cell.h`; `Target/HVM4Full.hs` `emitFull`.

- **Sharing cells:** `LAM`, `APP`, `SUP_L`, `DUP_L` (equivalently, the two faces at `L`), and `ERA`.
- **Constructors:** one per data constructor and one per type former, because types are data. They include:
  - `Set`, `Pi`, `Sig`, `Path` and `Eql`;
  - the inductive and HIT types with their constructors;
  - the interval endpoints;
  - `PLm`, `UaU` with its six fields, `Glue` and `HCm`;
  - faces and systems.
- **Matches:** one per type, each dispatching on the constructor it meets.
- **References:** `@name` unfolds to its definition, with fresh names for its dimensions (§2.4).

## 4. The rules

**Each rule fires at one active pair.**
- Every rule is local to its pair, so two available interactions act on disjoint pairs.
- So the one-step diamond holds.
- Sources: `origin/main:docs/index.html` §5; `research/sat_fibre/InteractionGeodesic.agda:15` `diamond`.

| Active pair | Rewrite | Ledger event |
|---|---|---|
| APP–LAM | β | counted as an interaction |
| APP–SUP | the application distributes, and the argument is faced at the coordinate | `appSup` (1, 3 words) |
| DUP–SUP, DUP–LAM, DUP–constructor | the rows of §2.2 | as in §2.2 |
| MATCH–constructor | the branch is selected | counted |
| MATCH–SUP | the match distributes | `appMatSup` (1, 5 words) |
| ERA at a port | the port is forgotten at the place where it is forgotten, which leaves a receipt | `erase` in the kernel |

**The Kan operations are programs over these cells.**
- `coe` dispatches on the type cell:
  - Π conjugates;
  - Σ is componentwise;
  - `Path` goes through the `hcomp` square;
  - `UaU` gives `f` forward and `g` backward (uaβ);
  - Glue has its own program;
  - a HIT pushes into its constructor.
- `hcomp`:
  - returns the top of a true face;
  - returns the base when every face is false;
  - otherwise dispatches on the type, or becomes the stuck cell `#HCm`, which resumes when the interval is decided.
- Sources: `RUNTIME_FULL.md`; `GLUE.md`; `GENERAL_HCOMP.md`; the deleted kernel's `trp_step` and `hcm_step` (`cell.c`
  lines 735–847), which call the prelude rows `trp/<Ctor>` and `hcm/<Ctor>`.

**The count.**
- Every event is one interaction (`research/sat_fibre/InteractionLedger.agda:74` `interactionTotal-is-length`).
- Under the diamond, every complete reduction to the normal form has the same length
  (`research/sat_fibre/InteractionGeodesic.agda:45` `same-normalization-length`, `:53` `normalization-is-geodesic`).
- The schedule is a gauge (`SETTLED_BY_THE_CORPUS.md` §2).

## 5. Sharing every isomorphic subexpression

**The rule.**
- The essay requires sharing every isomorphic subexpression, "folding all equalities", so that the reduction never
  duplicates an active pair and "no step repeats work". Source: `origin/main:docs/index.html` §5, "Complete,
  deterministic, terminating".
- The kernel had half of this: "a demanded node fires once and every holder sees its value" (`cell.c` `whnf`, the
  `T_IND` mark, lines 922–927).
- That half shares one node among its holders. It does not identify two separately built nodes that are the same.

**What is identified, and at what price.** The design separates two cases.

1. **Identical construction is one cell.**
   - Two cells built by the same constructor from the same sub-cells are one cell.
   - This is a fact about construction, not about meaning, so it costs nothing beyond building the cell.
   - Source: `REDUCTION_FOUNDATIONS.md`. The DUP-SUP distinction "is structural, not a test of semantic equivalence
     between arbitrary residual functions".
2. **Equal meaning is not a free primitive.**
   - Deciding that two residual functions are equal is the problem being solved.
   - `REDUCTION_FOUNDATIONS.md`: "treating equality in this quotient as a unit-cost primitive has moved the original
     decision into the primitive."
   - `DIRECTIONAL_SYNTHESIS.md`: any selector, factorization or normalizer must be represented in the language and
     charged in the runtime cost receiver.
   - **Derived:** two cells with equal meaning become one cell when reduction brings both to the same normal form. At
     that point case 1 applies, and the reduction that brought them there has been counted.

**Isomorphic, not only identical.** The essay says "isomorphic", and the corpus has the construction for it.
- `research/sat_fibre/ColorFrame.agda:174` `frame-presentation`: a colouring is split into a frame (a permutation of
  the colours) and a canonical colouring.
- `:194` `valid-invariant`: the verdict does not change under a permutation.
- `:208` `factored-verdict`: so only the canonical colouring is evaluated, and the frame is kept as the fibre for
  reconstruction. The module calls this "the runtime factoring equation".
- **Derived:**
  - A cell is stored once per class of the symmetry its observation is invariant under.
  - Each holder keeps the permutation that takes the canonical cell to its own.
  - Reading a holder's value is transport along that permutation. That transport is `ua` of an equivalence, and
    transport has no price (`Laghava…`, via `CONVERGENCE.md` III.4).
  - This is how the interchangeability of colours, a symmetry of the definitions, is used by the runtime.

**Multiplicity is kept.**
- Sharing is by reference. A shared cell held twice is still counted twice by collapse.
- Nothing is deduplicated. Sources: `SETTLED_BY_THE_CORPUS.md` §4 item 6; `CORPUS_DIGEST.md`, residue lane: "never
  merge two crowded fibres".
- Every identification keeps its justification. The justifications form chains that explain any derived equality:
  - `formal/cubical/theorems/residue/Parampara_TheDerivableEqualitiesAreExactlyTheWitnessChainsSoExplanationIsTotalAndSound.agda:87`
    `parampara`;
  - with `:78` `complete` and `:69` `sound`.

**The cut factoring is the same rule on SAT.**
- At a variable cut, a left assignment matters to the right only through the crossing clauses it left unsatisfied
  (`research/sat_fibre/SATBoundary.agda:37` `Residual`, `:69` `boundary-equivalence`).
- Left assignments with the same residual "may share a deterministic continuation state" (`DIRECTIONAL_SYNTHESIS.md`).
- What is forgotten is kept by the fibre law (`:119` `retained-reduction`).

## 6. No operator has an evaluation order

**The theorem.** A rule set that can inspect an operator from only one side is sequential, and the omitted side is
free:
- `formal/cubical/NaturalMachine/Ubhayatah_TheOmittedLeftRuleIsFreeAndItsAbsenceIsExactlyTheTrappedCount.agda:94`
  `add-suc-left-sound` is `refl`.
- `:115` `the-untrapping` joins, in one step, a pair that the one-sided calculus cannot join.
- `:133` `no-step²-conservation` shows that the trapped count is no longer conserved. The trapped count is what
  measured the one-sided calculus's cost.

**The design consequence.** "A runtime that can examine an operator from either side removes that cost, and the
interaction net's symmetric rules are exactly that removal." Source: `CORPUS_DIGEST.md`, design consequence (6) of the
natural-machine lane.

**So there is no AND agent.**
- HVM4's `AND` and `OR` reduce on the left operand first. Their events are `andSup`, `andZero` and `andOne`
  (`research/sat_fibre/InteractionLedger.agda:17` `andSup`).
- That is the one-sided rule set. The measured gap between clause orders, `9·2^n + 16n − 4` against `n + 30`, is its
  cost.
- A conjunction is a product type. Source: `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §21, "do not Booleanize".

**Derived: a clause is a face of the cube that is excluded.**
- A clause's falsifying assignments are one codimension-3 subcube. Sources: lane `README.md` A.1–A.2;
  `DIRECTIONAL_SYNTHESIS.md`, "a clause is a projection condition on a three-coordinate face".
- Over the generic assignment (§9), the identity `c_j(a) ≡ true` reduces to a cell along the clause's three
  coordinates, whose vertices are `Unit` or `Empty`.
- Its other coordinates are degenerate (§2.2, the sharing row), so the cell is shared, not copied.
- The specification is the product of these cells.
- No factor is reduced before another, because their active pairs are disjoint.

## 7. Collapse is a value

**The rule.**
- A candidate family is a superposition, and a specification is a map out of it.
- The survivors are its fibre, and `&{}` is the empty fibre.
- Collapse conserves multiplicity.
- Source: `SETTLED_BY_THE_CORPUS.md` §4 item 6.

**Derived: collapse is the set of vertices of the root.**
- Taking the faces of the root along each coordinate it mentions gives its vertices (§2.3).
- The kernel's `lift` does exactly this. It rebuilds a constructor with a superposed field as the superposition of the
  constructor's two faces at that coordinate (`cell.c` lines 1429–1447).
- Faces at different coordinates commute, so the set of vertices does not depend on the order of coordinates.

**Derived: a product with an empty factor has no vertex.**
- The previous version of this file listed this as undetermined. It follows from the rule above.
- A vertex of a pair is the pair of the vertices of its fields at that point. If one field has no vertex there, the
  pair has none.
- This needs no rule that reacts on two ports, and it treats every field alike.

**The leaves are a value.**
- In the deleted kernel, `(leaves e)` is a list cell of the vertices, with dead sides dropped, and computation
  continues on it (`cell.c` `T_LEAVES`, lines 1064–1068).
- HVM4's `-C` is a printer. `CORPUS_DIGEST.md` names this as the violation "printer-as-collapse".

**Where the size of a collapse comes from.**
- Bringing a coordinate to the root crosses it over every other coordinate above it (`dupSupDifferent`).
- With §5, this creates as many cells as there are distinct residuals below each prefix of the chosen coordinate
  order. Lane `README.md` A.5: "the exact residual population at depth k is the number of distinct residual functions,
  not the number of prefixes".
- A different order is a different presentation, with a different population. Sources: lane `README.md` A.6, the
  inner-product example; the essay's section on search.

## 8. There is no checking step

**The point is the pair, and both halves reduce by the same rules.**
- Finding and checking are the two directions of one equivalence:
  `formal/cubical/theorems/residue/VerifyIsDecide_ThereIsNoGapBetweenFindingAndCheckingBecauseBothAreProjectionsOfOneEquivalence.agda:60`
  `decide` and `:65` `verify`.
- That equivalence is the unique lossless completion: `:109` `no-gap-is-forced`, and
  `formal/cubical/theorems/residue/Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda:230`
  `machine-lossless-unique`.
- Conversion is a path cell reducing (`SETTLED_BY_THE_CORPUS.md` §4 item 8).

**Typing a superposition is the face rule applied to the type.** `&l{a, b} : G` holds exactly when `a : ∂_l^0 G` and
`b : ∂_l^1 G`. Source: `SETTLED_BY_THE_CORPUS.md` §1, where it is written with `dup l G`.

**A separate checker is a second evaluator.**
- This covers both the lane's Haskell gate and the deleted kernel's `verify.c`.
- `CORPUS_DIGEST.md` names "checker-outside" as a violation.
- `SETTLED_BY_THE_CORPUS.md` §4 item 8 says to fold it into the net.

## 9. A declaration with no body

**Search is evaluation.**
- A candidate family is a superposition, a specification is a map out of it, and the survivors are its fibre.
- Nothing is enumerated by the host, and the domain is an object of the program.
- Sources: `SETTLED_BY_THE_CORPUS.md` §4 item 6; `TYPED_POINT.md`, "This goes all the way up";
  `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §4, §29 and §30.

**Derived: the generic point of a type is its constructors, superposed.**
- For a type given by constructors, the generic point is the superposition over the constructors the type cell lists.
- Each field is its own fresh coordinate, and is unfolded only when demanded.
- For an infinite type the unfolding is guarded (`COINDUCTION.md`).
- The lane instead writes this family by hand in each program. For example, `SATProcess.bend` writes
  `@assignment{&100{False, True}, &101{False, True}}`.

**The proposition is the first observation.**
- For `Σ B. P A B`, the map `P A` applied to the generic `B` reduces on the shared cube.
- The vertices where the identity cells are inhabited are the fibre.
- When the fibre is contractible, `B` is determined by `A` (`hyper/MAP.md` §0 item 1).

## 10. Cost

- **The cost is the interaction count of the typed root, together with the heap words of each event.** Sources:
  `TYPED_POINT.md`; `research/sat_fibre/InteractionLedger.agda:13` `data Event`.
- **A potential certifies it.**
  - The condition is `Φ(u) ≤ c(u, v) + Φ(v)` on every primitive edge.
  - Such a Φ bounds every realisation from below.
  - A path that attains it edge by edge is a geodesic.
  - Source: lane `README.md` §9.
- **Cost validates the construction. It is not the goal.** Source: `hyper/TASK.md` §4.
- **An exponential lower bound is a family of states the geodesic cannot merge.**
  - The essay's section on search: "an exponential lower bound is an exponential family of states the geodesic cannot
    merge — nonfillable boundary distinctions; the construction fixes exactly what counts as one, and posits no such
    family for SAT."
  - Under §5, a merge is an identification of cells. So this is a statement about how many distinct cells a reduction
    must hold.

## 11. The deleted cell kernel: what it had and what it lacked

**The record.**
- The kernel was deleted in `e891b5bcd` and is intact at `e47e4d185`.
- That commit's message gives the reason: the kernel was "not an interaction net, so nothing gave its counts the
  diamond".
- The reason is correct, but what replaced it was HVM4 taken literally (`net.c`), and that is worse.
- Most of what the design asks for beyond the net was in the kernel and was deleted with it.

**What it had, matching the design:**
- Names as binder-instance addresses (§2.4), which removes labels-as-budget.
- The face operation for both kinds of coordinate, with every case carrying its ledger event (§2.2).
- A demanded node that fires once, after which every holder sees its value (`T_IND`).
- The CCHM Kan rules, Glue, `ua`, HITs by schema, and the interval as a free De Morgan algebra in normal form.
- Trace and leaves as values (`T_TRACE`, `T_LEAVES`).
- Agreement with Bend2's normaliser on 124 programs, and with Bend2's checker on 3,862 definitions (`bendtest.sh`
  and `checktest.sh` at that commit).

**What it lacked:**
- **It was not optimal.**
  - It is an environment machine: a closure applied twice instantiates its body twice.
  - Work in a function body that does not depend on the argument is therefore repeated. That is call-by-need, not
    Lévy-optimal.
  - Its face of a closure (`fce_closure`) is the right DUP-LAM, but nothing duplicates a body incrementally.
- **It did not fold identical cells** (§5, case 1).
- **Its arithmetic and Boolean operators were one-sided.**
  - `T_OP2` reduces its left operand first.
  - An environment variable chose the other side, for testing (`cell.c` lines 1069–1085 and 891–909).
  - §6 says neither side is first.
- **Its checker `verify.c` was a separate pass** (§8).

## 12. Open points

**1. Fresh names inside a duplicated body, without closures.**
- With closures, a name is the address of its binder instance, and a body gets fresh names when it is opened (§2.4).
- A net with no closures copies a body piece by piece through DUP-LAM. A duplication inside that body then meets the
  outer duplication's copies under a single label.
- Lamping's bookkeeping solves this by indexing labels with levels.
- The design states the label discipline (§2.1) but not the mechanism for this case.

**2. The generic point of a function type.**
- §9's derivation covers types given by constructors.
- For a finite domain, a function is a product of its values, so its generic point is a product of generic points.
- For an infinite domain, the design gives only the hand-written candidate families of `SUPGEN_DEMO.md`.

**3. Which coordinate order runs.**
- §7 shows that the size of a collapse depends on the order of coordinates.
- The design does not leave this choice to the machine: "ranking is the caller's act. The machine presents; the caller
  disposes" (`formal/cubical/Kernel/DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda` §7).
- A change of order is a sequence of crossings, and each crossing is a square of the cube (`PUSC.md` §1, "Parallel").
- What is open is only the surface through which a caller supplies the order.

# The runtime, rule by rule, from the handed design

Every line below names its source. A line marked **derived** follows from a sourced line but is not written there.
A line marked **not determined** is a place where the design leaves a choice open. The exact obstruction is given for
each. Nothing else is added.

**Sources, read in one pass:**
- `collab/bend2-interactive-cubical/`:
  - `SETTLED_BY_THE_CORPUS.md` §1–§5;
  - `TYPED_POINT.md`;
  - `RUNTIME_FULL.md`;
  - `CONVERGENCE.md` Parts I–IV;
  - `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §4, §7, §21, §26–§41;
  - `QUOTIENT.md`;
  - the emitters `Target/HVM4Full.hs` and `Target/Hyper.hs` in `cubical-paths.patch`.
- `research/sat_fibre/InteractionLedger.agda` and `research/sat_fibre/InteractionGeodesic.agda`.

## 1. The object

- **Every definition is a typed point.** Each checked definition `name : A = a` is two cells, `@Dname` (the expression)
  and `@Tname` (its type), made by one emitter. The root is `#Pair{@Tmain, @Dmain}`, a point of `Σ (A : Set). A`.
  Source: `TYPED_POINT.md`; `HVM4Full.compileFull`, `def` and `root`.
- **Nothing is erased or pre-normalised.** Intervals, paths, types, `ua`, `hcomp`, Glue and HIT cells are all runtime
  cells. Source: `RUNTIME_FULL.md`, first table; `TYPED_POINT.md` "Cubical cells … are structure in the checked
  term. Erasing any of them is lossy."
- **Ill-typed input is refused, and nothing is emitted.** Source: `TYPED_POINT.md`.

## 2. Cells

There are four kinds of cell. Source: `Target/HVM4Full.hs` `emitFull`; `Target/Hyper.hs` `emitIn`. The two emitters
describe the same set of cells.

- **Sharing:** `LAM`, `APP`, `SUP[L]`, `DUP[L]`, `ERA`.
  - In the kernel text a duplication is written as two face restrictions, `(fce L 0 x)` and `(fce L 1 x)`. Source:
    `Hyper.hs`, `SupM`: "the match is two faces".
- **Constructors.** One per data constructor, and one per type former, because types are data:
  - `Set`, `Pi`, `Sig`, `Path`, `Eql`, `List`, `Nat`, `Bool`, `Unit`, `Empty`, `Enum`, `Num`;
  - HIT types and their point constructors, and quotient cells `QCl` and `QEq`;
  - the interval endpoints `I0` and `I1`;
  - `PLm` (path abstraction), `UaU` with all six fields, `CompU`, `Glue`/`GlB`;
  - `HCm`, the stuck composite;
  - `Face`/`GFace` and `Sys`.
- **Matches.** One per type, dispatching on the constructor met.
- **References.** `@name` unfolds to the definition.

## 3. Interaction rules

These are the only rules. Each fires at one active pair (principal port meeting principal port). The cost alphabet is
`InteractionLedger.Event`, and every event is one interaction (`interactionTotal-is-length`).

| Rule | Rewrite | Event in the ledger | Source |
|---|---|---|---|
| APP-LAM | β | (counted) | `CONVERGENCE.md` Part I |
| APP-SUP | an application distributes over a superposition | `appSup` | Part I; ledger |
| DUP-LAM | duplicating a lambda superposes its variable | `dupLamUsed` / `dupLamErased` | Part I; ledger |
| DUP-SUP, same label | route: the two sides are the two copies, with no allocation | `dupSupEqual` (0 words) | Part I; `SETTLED_BY_THE_CORPUS.md` §1 |
| DUP-SUP, different label | cross: each distributes over the other | `dupSupDifferent` (4 words) | same |
| DUP-NODE | duplicating a constructor duplicates its fields | `dupNode a` (2a words) | ledger; `hyper/MAP.md` §0.2 "Inventing the cost model" |
| MAT-CTR | a match selects its branch | (counted) | the emitted `λ{#K: …}` matches |
| MAT-SUP | a match distributes over a superposition | `appMatSup` | ledger; `RUNTIME_FULL.md` "superposed line … no rule" |
| ERA | erasure | (counted) | Part I |

The ledger also has `andSup`, `orSup`, `andZero`, `andOne`, `orZero` and `orOne`. These are HVM4's Boolean
operators, and they are **not carried over**. `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §21 says "do not
Booleanize". A proposition stays a proposition, so a conjunction is a product type, not an operator.

**Consequence.** Every rule is local to one active pair, so the one-step diamond holds and
`InteractionGeodesic.same-normalization-length` applies. For a fixed object and demand, the count is the same under
every schedule. Schedule is a gauge (`SETTLED_BY_THE_CORPUS.md` §2).

## 4. Programs, not rules

The cubical operations are programs that match on cells. Source: `RUNTIME_FULL.md`, "the prelude is Core.WHNF's
cubical reduction rewritten as an HVM4 program"; `hyper/MAP.md` §0.1. The prelude in `Target/HVM4Full.hs` is the
reference text.

- **The interval:** `@inot`, `@iand`, `@ior`. Each reduces on endpoints and builds `#INot`, `#IAnd` or `#IOr` on a
  symbolic interval.
- **Applying a path:** `@pathAt`, `@pL`, `@pR`, `@pAtSym`.
  - On `PLm` this is β.
  - A HIT path constructor at an endpoint gives its declared boundary; at a symbolic interval it stays canonical.
  - `QEq` gives `QCl a` and `QCl b` at its two ends.
- **Transport:** `@coe(L, r, s, x)`.
  - If r and s are the same end, the result is x.
  - Otherwise it dispatches on `L(#IMark)`:
    - rigid types give x;
    - `Pi` conjugates;
    - `Sig` works componentwise;
    - `Path` goes through the `hcomp` square;
    - `At`/`UaU` gives `f` forward and `g` backward, which is uaβ;
    - `CompU` composes;
    - `Glue` goes to `@coeGlue`;
    - a HIT goes to `@hitCoe`.
- **Composition:** `@hcomp`/`@hcompGo`.
  - A true face gives its tube's top. All-false faces give the base.
  - Otherwise it dispatches on the type:
    - `Set` gives `Glue` with `@transpEquiv`;
    - `Pi`, `Path` and `Sig` follow the CCHM rules;
    - `Glue`, `Nat`, `List` and the nullary types have their own cases;
    - anything else becomes the stuck cell `#HCm`, which is partial knowledge resumed when the interval is decided.
- **Glue and `ua`:** `@glueT`, `@glue`, `@unglue`, `@coeGlue`, `@transpEquiv`. `ua` is derived from Glue, and uaβ is
  definitional (`uaglue.bend`).
- **Eliminators:** `@qrec`, `@trec`, `@srec`, and the generated `@E_T`.
  - On a point constructor each applies its branch.
  - On a path constructor at i it applies the branch's path at i (`qrec(eq/ a b w @ i) = resp a b w @ i`).
  - Each commutes with `hcomp`.
  - Each commutes over a superposition by the ordinary rule. Source: `QUOTIENT.md`.

## 5. Labels

- **A label is the name of a coordinate.**
  - Same label means the same coordinate: the source projection, which routes.
  - A different label means an independent coordinate: the product, which pays.
  - Source: `SETTLED_BY_THE_CORPUS.md` §1, §4 item 3.
- **There are two kinds of label.** Source: `Hyper.hs`, `label`: "a closed numeral is a global choice name; a variable
  is itself".
  - A **declared** label, such as `&100`, names one global coordinate. Every occurrence is the same coordinate, which
    is how `SATProcess.bend` shares its cube.
  - A **binder** label belongs to its binder occurrence. Source: `HVM4Full.hs` `freshName` and its comment: two
    binders sharing a label "would annihilate instead of commuting".
- **Derived: a binder label is fresh per instantiation at run time, not per source occurrence.** Two unfoldings of one
  definition are two coordinates. The prelude's own comment names the defect this removes: "HVM4 auto-dup labels are
  static per binder, and a dup of an argument that already contains an instance of the same definition's dup would
  annihilate instead of commute".
- **A superposition is typed by the duplication of its goal at its label.** `&l{a, b} : G` holds if and only if
  `a : G₀` and `b : G₁`, where `(G₀, G₁) = dup l G`. Source: `SETTLED_BY_THE_CORPUS.md` §1; `sup_dependent.bend` and
  its must-fail sibling.

## 6. Checking runs on the same net

- **The rule.** Checking is the type projection of the typed point, reduced by the same reducer, and conversion is a
  path cell reducing. Source: `SETTLED_BY_THE_CORPUS.md` §4 item 8; `VerifyIsDecide_…`.
- **Status: not written.** Today the Haskell checker (`Core.Check`) runs before emission, and
  `SETTLED_BY_THE_CORPUS.md` §5 lists folding it into the net as labour.
- **What it consists of.** `Core.Check`'s bidirectional rules, including the DUP-of-goal case, written as programs over
  the emitted type cells `@T…`. Those cells are already emitted beside every definition.

## 7. Collapse is a value

- **The rule.**
  - A candidate family is a superposition, and a specification is a map out of it.
  - The survivors are its fibre.
  - Collapse conserves multiplicity and never deduplicates.
  - `&{}` is the empty fibre.
  - Source: `SETTLED_BY_THE_CORPUS.md` §4 item 6, abstracts 16 and 20 via `Avirodha` §5.
- **The leaves of a superposition are a value, a list cell, that computation continues on.** `sortCost` folds over
  them.
- **Status.** HVM4's `-C` is a printer with a priority queue. That is the third violation named in `CORPUS_DIGEST.md`
  ("printer-as-collapse").
- **Derived: a collapse is a nest of same-label duplications.** In the kernel text a duplication at label L is the two
  faces of L. Restricting a value to the faces of each of its labels gives its vertices. Faces at different labels
  commute, so the set of leaves does not depend on the order in which labels are faced.

## 8. A declaration with no body

- **The rule.**
  - The domain must be an object of the program.
  - The proposition is the first observation.
  - Nothing is enumerated by the host.
  - Source: `LANGUAGE_LEVEL_CONDUCTIVE_FIBRE_INTEGRATION.md` §4, §29, §30; `TYPED_POINT.md` "Search is evaluation of
    a typed point whose value happens to be a superposition".
- **Derived: the generic point of a type is a superposition of its constructors.** For an enumerated, inductive or HIT
  type, the generic point is the labelled superposition over the constructors the type cell lists. Each field is its
  own fresh coordinate, and the superposition unfolds only when it is demanded (it is lazy; for an infinite type it is
  guarded, per `COINDUCTION.md`).
  - This is "the domain as an object", read off the type itself rather than written per program as
    `SATProcess.bend`'s `main` writes it.
  - **It is not in the lane.**

## 9. Cost

- **The cost is the interaction count of the typed root.** Source: `TYPED_POINT.md`.
- **It is certified exactly by a potential Φ** with `Φ(u) ≤ c(u,v) + Φ(v)`. Equality along a path proves that path is
  a geodesic. Source: lane `README.md` §9.
- **What runs is the cheapest presentation reachable by executable identity.** Source: `SETTLED_BY_THE_CORPUS.md` §4
  item 9.

## 10. Not determined by the design

1. **A product with an empty factor.** The fibre of `Σ b. P b × Q b` is empty wherever either factor is.
   - A cell that becomes empty when *either* field is empty must react on a non-principal port.
   - Such a rule keeps the one-step diamond against a second empty field.
   - It breaks the diamond against an eliminator that consumes the pair first and discards the empty field. The
     result is then non-empty, and the two orders disagree.
   - So emptiness of a product is either sequential, with its cost depending on which factor is reduced first, or it
     is the collapse's job. The design does not say which.
2. **Labels for a copy containing its own duplication.** Freshness per instantiation (§5) separates instances. It does
   not separate two copies, made by one duplication, of an expression that contains that same duplication. Full
   Lamping bookkeeping extends a label by the path of copies it has passed through. The design does not say whether
   that is needed.
3. **The generic point of a Π type.** That is generating functions, which is SupGen. The lane has hand-written
   candidate families only (`SUPGEN_DEMO.md`). §8's derivation covers types given by constructors, not function types.
4. **The count of a collapse under different label orders.** The leaves do not depend on the order (§7). Whether the
   count does is not settled: a different nesting is a different net, so `InteractionGeodesic` does not compare them.
   This is the same point as the corpus's "cheapest presentation reachable by executable identity" (§9). I found no
   rule in the design for how one net reaches the cheaper order.

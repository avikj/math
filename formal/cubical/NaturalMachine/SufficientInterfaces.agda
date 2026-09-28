{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.SufficientInterfaces
--
-- Sufficient Interfaces for Relational Computation — Delta 01, checked.
-- (collab/upstream/library/raw/SUFFICIENT_INTERFACES_DELTA_01_2026-08-13.md (absent from this repository))
--
-- WHY THIS ONE.  Δ01 is the sufficient-interfaces delta whose content is finite, exact, and
-- decidable end to end — it needs no analytic input and no new
-- mathematics to enter the substrate.  It is also the document that
-- states, as a theorem, a failure mode of context compression:
--
--   §15: "lossy context compression is safe only if every collapsed state
--    shares a valid next action.  If not, the compressor has erased a
--    decision-relevant distinction."
--
-- and then §3 exhibits the minimal witness that this can fail even when
-- every part looks fine — two individually sufficient interfaces whose
-- join is not sufficient.  Delta 01 calls that "an exact finite gluing
-- obstruction", and it is the finite shadow of the question the owner
-- asks in three separate places (U0006 §3; Delta 15 §§15.11–15.12,
-- Programs 15.47–15.49; Delta 17 §17.21): build a cover, compute the
-- transition data, find the obstruction to gluing local sections.  Here
-- the cover is a partition, the local sections are blockwise witnesses,
-- and the obstruction is exhibited rather than conjectured.
--
-- Contents (all proved, no holes, no postulates, --safe):
--
--   Sufficient, Realization    §0/§1: a common witness per block; a
--                              deterministic selector
--   suff→real, real→suff       T1, the selector criterion, both ways
--   IsSimplex, simplex-down    T12: N_R is a simplicial complex
--   suff→simplices             T13: sufficiency is blockwise simplexhood
--   simplices→suff             …and conversely, by construction
--   refine-sufficient          T4: Suff(R) is downward closed — a finer
--                              interface inherits every witness
--   data-processing            T7: Suff(R) ⊆ Suff(S∘R) for total S
--   join-fails                 P6: THE witness.  π, σ sufficient, π∨σ not
--   materialization-gap        T8/§5: the composite is realizable from
--                              one block while the intermediate is not —
--                              an architectural boundary forcing a
--                              distinction the end task does not need
--   unsafe-compression         §15/§16 read back: a compressor whose
--                              collapsed class admits no common action
------------------------------------------------------------------------

module NaturalMachine.SufficientInterfaces where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓA ℓB ℓC ℓQ ℓQ' ℓR ℓS ℓT : Level

------------------------------------------------------------------------
-- §1  The primitive, and Theorem 1
--
-- Δ01 §0: a partition π of A is R-sufficient iff every block E has a
-- common valid output, ⋂_{a∈E} R(a) ≠ ∅.
--
-- A partition is presented by its quotient map q : A → Q; the block over
-- c is the fibre {a : q a ≡ c}.  This is the presentation the rest of the
-- development needs, because refinement (§3) is then just a factorisation
-- of q, and it is faithful: any partition is the kernel of its own
-- quotient map.
------------------------------------------------------------------------

module _ {A : Type ℓA} {B : Type ℓB} {Q : Type ℓQ}
         (R : A → B → Type ℓR) where

  -- Every fibre of q has a witness valid for all of its members.
  Sufficient : (A → Q) → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓQ ℓR)))
  Sufficient q = (c : Q) → Σ[ b ∈ B ] ((a : A) → q a ≡ c → R a b)

  -- Δ01 T1(ii)/(iii): a deterministic realization factoring through q.
  Realization : (A → Q) → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓQ ℓR)))
  Realization q = Σ[ s ∈ (Q → B) ] ((a : A) → R a (s (q a)))

  -- T1, (i) ⇒ (ii).  The selector is the choice of witness at each block.
  -- Constructively this is the type-theoretic axiom of choice — a Π of Σ
  -- becoming a Σ of Π — which is exactly what Δ01's "choose s(E) from the
  -- common intersection" is, and it is available here without assumption.
  suff→real : (q : A → Q) → Sufficient q → Realization q
  suff→real q σ = (λ c → fst (σ c)) , λ a → snd (σ (q a)) a refl

  -- T1, (ii) ⇒ (i).  Conversely any blockwise selector lies in every fibre
  -- in its block; the transport along `cong s p` is that sentence.
  real→suff : (q : A → Q) → Realization q → Sufficient q
  real→suff q (s , h) c = s c , λ a p → subst (R a) (cong s p) (h a)

------------------------------------------------------------------------
-- §2  Theorems 12 and 13: the nerve
--
-- Δ01 §10: N_R = {S ⊆ A : ⋂_{a∈S} R(a) ≠ ∅} is an abstract simplicial
-- complex, and π is sufficient iff every block of π is a simplex.
--
-- Note what T2 becomes here.  Δ01 T2 says S is an admissible block iff
-- S ⊆ E_b for some b, where E_b = {a : b ∈ R(a)}.  Since E_b is literally
-- `λ a → R a b`, the containment S ⊆ E_b *is* `(a : A) → S a → R a b`, so
-- T2 is the definition of `IsSimplex` read twice.  Recording that rather
-- than dressing it as a lemma.
------------------------------------------------------------------------

module _ {A : Type ℓA} {B : Type ℓB} (R : A → B → Type ℓR) where

  IsSimplex : (A → Type ℓS) → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓR ℓS)))
  IsSimplex S = Σ[ b ∈ B ] ((a : A) → S a → R a b)

  -- T12.  Downward closed under subsets: a common witness for S serves
  -- every subset of S.  This is the whole content of "is a complex".
  simplex-down : {S : A → Type ℓS} {S' : A → Type ℓT}
               → ((a : A) → S' a → S a)
               → IsSimplex S → IsSimplex S'
  simplex-down sub (b , h) = b , λ a s' → h a (sub a s')

  -- The block of q over c, as a subset of A.
  block : {Q : Type ℓQ} → (A → Q) → Q → (A → Type ℓQ)
  block q c = λ a → q a ≡ c

  -- T13, both directions.  With blocks presented as fibres, sufficiency
  -- and blockwise simplexhood are the same statement with the quantifiers
  -- in a different order, so each direction is a reassociation.
  suff→simplices : {Q : Type ℓQ} (q : A → Q)
                 → Sufficient R q → (c : Q) → IsSimplex (block q c)
  suff→simplices q σ c = fst (σ c) , snd (σ c)

  simplices→suff : {Q : Type ℓQ} (q : A → Q)
                 → ((c : Q) → IsSimplex (block q c)) → Sufficient R q
  simplices→suff q h c = fst (h c) , snd (h c)

------------------------------------------------------------------------
-- §3  Theorem 4: Suff(R) is an order ideal
--
-- Δ01 §3: if π is sufficient and ρ ≤ π (ρ finer), then ρ is sufficient —
-- every ρ-block lies in a π-block and inherits its witness.
--
-- "ρ finer than π" is presented as a factorisation: π's quotient map
-- factors through ρ's.  That is the same relation, and it makes the proof
-- the transport it should be.
------------------------------------------------------------------------

module _ {A : Type ℓA} {B : Type ℓB} {Q : Type ℓQ} {Q' : Type ℓQ'}
         (R : A → B → Type ℓR) where

  -- ρ (presented by q') refines π (presented by q) when q factors as
  -- r ∘ q'.  Then each q'-fibre sits inside a q-fibre.
  Refines : (q' : A → Q') (q : A → Q) (r : Q' → Q) → Type (ℓ-max ℓA ℓQ)
  Refines q' q r = (a : A) → q a ≡ r (q' a)

  refine-sufficient : (q' : A → Q') (q : A → Q) (r : Q' → Q)
                    → Refines q' q r
                    → Sufficient R q → Sufficient R q'
  refine-sufficient q' q r fac σ c' =
    fst (σ (r c')) , λ a p → snd (σ (r c')) a (fac a ∙ cong r p)

------------------------------------------------------------------------
-- §4  Theorem 7: the data-processing law
--
-- Δ01 §4: (S∘R)(a) = ⋃_{b∈R(a)} S(b), and if S is total on the usable
-- witnesses then Suff(R) ⊆ Suff(S∘R), hence κ₀(S∘R) ≤ κ₀(R).
--
-- "distinctions necessary for an intermediate task can become irrelevant
-- to the final task" — proved here, and made strict in §6.
------------------------------------------------------------------------

-- `compose` and `Total` do not mention the interface, so the interface is
-- quantified on the theorem rather than on the module; otherwise every use
-- of `compose` leaves its type undetermined.
module _ {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (R : A → B → Type ℓR) (S : B → C → Type ℓS) where

  compose : A → C → Type (ℓ-max ℓB (ℓ-max ℓR ℓS))
  compose a c = Σ[ b ∈ B ] (R a b × S b c)

  -- Totality of S, as Δ01 hypothesises it: every usable witness has an
  -- onward output.
  Total : Type (ℓ-max ℓB (ℓ-max ℓC ℓS))
  Total = (b : B) → Σ[ c ∈ C ] S b c

  data-processing : {Q : Type ℓQ} → Total → (q : A → Q)
                  → Sufficient R q → Sufficient compose q
  data-processing tot q σ c₀ =
    let (b , hb) = σ c₀
        (c , sc) = tot b
    in c , λ a p → b , hb a p , sc

------------------------------------------------------------------------
-- §5  Proposition 6 — the exact finite gluing obstruction
--
-- Δ01 §3:
--
--     A = {1,2,3}, B = {x,y}, R(1)={x}, R(2)={x,y}, R(3)={y}.
--     π = {{1,2},{3}} and σ = {{1},{2,3}} are sufficient,
--     but π ∨ σ = {{1,2,3}} is not.
--
--     "locally valid coarse-grainings can glue transitively into a
--      globally invalid class.  This is an exact finite gluing
--      obstruction; no cohomological claim is made yet."
--
-- Therefore Suff(R) is a meet-semilattice and an order ideal, and NOT a
-- sublattice.  §3's downward closure and this failure of upward closure
-- are the two halves of that.
--
-- This is the smallest object in the corpus that does what the owner's
-- descent programme asks for: local sections exist on each piece of a
-- cover, and no global section exists.  Point 2 has a witness; the
-- element 2 is the overlap, valid under both x and y, and it is exactly
-- the freedom at the overlap that lets the two blocks be glued into an
-- invalid one.
------------------------------------------------------------------------

data Pt : Type where
  a1 a2 a3 : Pt

data Wit : Type where
  bx by : Wit

-- R(1)={x}, R(2)={x,y}, R(3)={y}.
R6 : Pt → Wit → Type
R6 a1 bx = Unit
R6 a1 by = ⊥
R6 a2 bx = Unit
R6 a2 by = Unit
R6 a3 bx = ⊥
R6 a3 by = Unit

-- Two blocks.
data Blk : Type where
  β0 β1 : Blk

-- Separation of the two block labels, as a family; `subst` turns a path
-- between distinct labels into ⊥.  This is the only discreteness the
-- module needs.
isβ0 : Blk → Type
isβ0 β0 = Unit
isβ0 β1 = ⊥

-- A point lying outside the block it is being tested against gives a path
-- between distinct labels, hence anything.  Both orientations, so the
-- witness clauses below read the same whether the required output type is
-- `Unit` (the point is admissible but absent) or `⊥` (it is inadmissible).
β0≢β1 : {X : Type ℓA} → β0 ≡ β1 → X
β0≢β1 p = ⊥rec (subst isβ0 p tt)

β1≢β0 : {X : Type ℓA} → β1 ≡ β0 → X
β1≢β0 p = ⊥rec (subst isβ0 (sym p) tt)

-- π = {{1,2},{3}}
qπ : Pt → Blk
qπ a1 = β0
qπ a2 = β0
qπ a3 = β1

-- σ = {{1},{2,3}}
qσ : Pt → Blk
qσ a1 = β0
qσ a2 = β1
qσ a3 = β1

-- π is sufficient: block {1,2} takes witness x, block {3} takes y.
π-sufficient : Sufficient R6 qπ
π-sufficient β0 = bx , w
  where
    w : (a : Pt) → qπ a ≡ β0 → R6 a bx
    w a1 _ = tt
    w a2 _ = tt
    w a3 p = β1≢β0 p
π-sufficient β1 = by , w
  where
    w : (a : Pt) → qπ a ≡ β1 → R6 a by
    w a1 p = β0≢β1 p
    w a2 p = β0≢β1 p
    w a3 _ = tt

-- σ is sufficient: block {1} takes x, block {2,3} takes y.
σ-sufficient : Sufficient R6 qσ
σ-sufficient β0 = bx , w
  where
    w : (a : Pt) → qσ a ≡ β0 → R6 a bx
    w a1 _ = tt
    w a2 p = β1≢β0 p
    w a3 p = β1≢β0 p
σ-sufficient β1 = by , w
  where
    w : (a : Pt) → qσ a ≡ β1 → R6 a by
    w a1 p = β0≢β1 p
    w a2 _ = tt
    w a3 _ = tt

-- The join collapses everything into one block.
qJ : Pt → Unit
qJ _ = tt

-- …and it is NOT sufficient.  x fails at 3, y fails at 1; there is no
-- third option.  P6.
join-fails : ¬ (Sufficient R6 qJ)
join-fails σ = no-common (fst (σ tt)) (snd (σ tt))
  where
    no-common : (b : Wit) → ((a : Pt) → qJ a ≡ tt → R6 a b) → ⊥
    no-common bx h = h a3 refl
    no-common by h = h a1 refl

-- The three facts as one term: Suff(R) is not closed under joins, and the
-- two joined interfaces are individually fine.
suff-not-a-sublattice :
    Sufficient R6 qπ × Sufficient R6 qσ × (¬ (Sufficient R6 qJ))
suff-not-a-sublattice = π-sufficient , σ-sufficient , join-fails

------------------------------------------------------------------------
-- §6  Theorem 8 and the materialization gap
--
-- Δ01 §5: there are R, S with κ₀(S∘R) = 1 while every deterministic
-- protocol that materializes an R-valid intermediate needs κ₀(R) > 1.
--
--     R(a1)={b1}, R(a2)={b2};  S(b1)=S(b2)={c}.
--
-- So Δmat = log κ₀(R) − log κ₀(S∘R) > 0: one full bit is forced by the
-- architectural boundary and is irrelevant to the end task.  This is the
-- strictness that makes §4's data-processing law informative rather than
-- an identity.
------------------------------------------------------------------------

data Pt2 : Type where
  p1 p2 : Pt2

data Wit2 : Type where
  w1 w2 : Wit2

data Out : Type where
  z : Out

Rm : Pt2 → Wit2 → Type
Rm p1 w1 = Unit
Rm p1 w2 = ⊥
Rm p2 w1 = ⊥
Rm p2 w2 = Unit

Sm : Wit2 → Out → Type
Sm w1 z = Unit
Sm w2 z = Unit

qOne : Pt2 → Unit
qOne _ = tt

-- The end task IS realizable from a single block: both points reach z.
composite-sufficient : Sufficient (compose Rm Sm) qOne
composite-sufficient tt = z , w
  where
    w : (a : Pt2) → qOne a ≡ tt → compose Rm Sm a z
    w p1 _ = w1 , tt , tt
    w p2 _ = w2 , tt , tt

-- The intermediate is NOT: no single b is valid for both points.
intermediate-insufficient : ¬ (Sufficient Rm qOne)
intermediate-insufficient σ = no-common (fst (σ tt)) (snd (σ tt))
  where
    no-common : (b : Wit2) → ((a : Pt2) → qOne a ≡ tt → Rm a b) → ⊥
    no-common w1 h = h p2 refl
    no-common w2 h = h p1 refl

materialization-gap :
    Sufficient (compose Rm Sm) qOne × (¬ (Sufficient Rm qOne))
materialization-gap = composite-sufficient , intermediate-insufficient

------------------------------------------------------------------------
-- §7  Δ01 §§11 and 15ℓ16, read back
--
-- Δ01 T11 defines an information edge exactly: given a quotient q, there
-- is no task-relative obstruction precisely when ker(q) ∈ Suff(R).  §15
-- applies it to agents: with Ω the possible research states, q a context
-- compressor, and R(ω) the actions valid in ω, the compressor is safe for
-- action selection iff every collapsed class shares a valid action.
--
-- `Sufficient` above IS that predicate, so the statement needs no new
-- definition — only the naming, and the negative witness, which §5
-- already supplies.  An unsafe compressor is a `Sufficient` that fails,
-- and `join-fails` is the smallest one: two summaries, each individually
-- adequate for its own purpose, merged into a view from which no valid
-- next action is available at all.
--
-- The moral Δ01 draws is that this is not a limitation of language
-- models: it is set cover (T3), and it is NP-hard before any model enters
-- the picture.
------------------------------------------------------------------------

-- The safety predicate of §15, named.  Definitionally `Sufficient`; the
-- alias exists so that the arithmetic and the agent readings can cite the
-- same object rather than two copies of it.
SafeCompressor : {Ω : Type ℓA} {Act : Type ℓB} {C : Type ℓQ}
               → (R : Ω → Act → Type ℓR) → (q : Ω → C)
               → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓQ ℓR)))
SafeCompressor R q = Sufficient R q

-- An unsafe compressor exists, and the witness is P6: the collapsed class
-- {1,2,3} admits no common valid action, while each of the two finer
-- views does.
unsafe-compression : ¬ (SafeCompressor R6 qJ)
unsafe-compression = join-fails

-- …and refinement is the repair.  Δ01 §17: on discovering a block with no
-- common valid action, the agent must refine.  T4 says refinement never
-- costs validity, so the repair is always available and never breaks what
-- already worked.
refinement-repairs : (r : Blk → Unit) → Refines R6 qπ qJ r
                   → Sufficient R6 qJ → Sufficient R6 qπ
refinement-repairs r fac = refine-sufficient R6 qπ qJ r fac

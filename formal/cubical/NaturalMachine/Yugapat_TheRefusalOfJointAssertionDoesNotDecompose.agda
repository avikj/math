{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Yugapat_TheRefusalOfJointAssertionDoesNotDecompose
--
-- युगपत् · yugapat — "at once", the Jaina term for the simultaneous
-- mode of predication, paired with क्रम · krama, "in sequence"
-- (saptabhag: Umsvti, *Tattvrthastra*; Samantabhadra; Akalaka;
-- Siddhasena Divkara).  The distinction is theirs and so is its
-- formalisation in this repository: `Saptabhangi` and
-- `SaptabhangiNaya`, ANOTHER IDENTITY'S modules, define the mode as a
-- DATATYPE `आर्पण` — a parameter of the predication — and prove
-- स्यात्-अस्ति-नास्ति ≢ स्यात्-अवक्तव्यम्.  **Their `आर्पण` is IMPORTED
-- below, not rebuilt**, and nothing here is a claim about their
-- theorem.
--
-- `KramaSaha_TheFourthCornerIWasNamingIsTheSequentialPosition` (absent from this repository)
-- concluded:
--
--   "this formalism, as it stands, cannot express avaktavya at all:
--    every position it can name is reachable sequentially."
--
-- **That was too strong, and the reason is a De Morgan asymmetry I did
-- not check.**  What that cycle proved is that REFUSING BOTH collapses:
-- `¬ (A ⊎ B)` and `(¬ A) × (¬ B)` are interderivable.  It does not
-- follow that every position collapses, because the OTHER De Morgan
-- law runs only one way constructively: `((¬ A) ⊎ (¬ B)) → ¬ (A × B)`
-- always, and the converse does not.
--
-- So there IS a position in my formalism that is not a sequential pair:
-- **the refusal of the JOINT assertion**, `¬ (सामयिक × नित्य)`, which
-- says the two cannot hold together without saying which fails.  That
-- is the shape yugapat has in the tradition — a single act about the
-- pair, not two acts — and it is exactly what a product of refusals
-- cannot express.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   Assert m Q          the mode-parameterised predication over MY
--                       instance family, indexed by their `आर्पण`:
--                       क्रमः gives the sequential pair of refusals,
--                       सहः the refusal of the joint assertion
--   kramaGivesYugapat   the sequential position implies the
--                       simultaneous one — one line, and unconditional
--   yugapatDecompositionGivesWeakExcludedMiddle
--                       the CONVERSE, as a general principle, implies
--                       weak excluded middle: from
--                       `(A B : Type) → ¬ (A × B) → ((¬ A) ⊎ (¬ B))`,
--                       taking `B := ¬ A`, one gets `¬ A ⊎ ¬ ¬ A` for
--                       every `A`
--
-- **So the two modes are not interderivable here for a reason with a
-- name.**  The direction that fails is not an accident of my encoding;
-- decomposing a refusal-of-conjunction is a known constructive taboo,
-- and this module reduces it to that taboo rather than asserting it.
-- The parallel with the rest of this line is exact: the fourth-corner
-- work reduced a position to failure of the double-negation shift,
-- another principle that is classically trivial and constructively not.
------------------------------------------------------------------------

module NaturalMachine.Yugapat_TheRefusalOfJointAssertionDoesNotDecompose where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Saptabhangi using (आर्पण ; क्रमः ; सहः)
open import Mula.AnuktaAvaktavya using (सामयिक ; नित्य)
open import NaturalMachine.OrderAstiNasti_TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift
  using (one)

private
  variable
    R : Type

------------------------------------------------------------------------
-- 1.  The mode is a parameter, as it is in their construction
------------------------------------------------------------------------

Assert : आर्पण → (R → Type) → Type
Assert क्रमः Q = (¬ सामयिक (one Q)) × (¬ नित्य (one Q))
Assert सहः  Q = ¬ (सामयिक (one Q) × नित्य (one Q))

------------------------------------------------------------------------
-- 2.  Sequential implies simultaneous, for nothing
------------------------------------------------------------------------

kramaGivesYugapat : (Q : R → Type) → Assert क्रमः Q → Assert सहः Q
kramaGivesYugapat Q (ns , nn) both = ns (fst both)

------------------------------------------------------------------------
-- 3.  …and the converse is a constructive taboo
------------------------------------------------------------------------

yugapatDecompositionGivesWeakExcludedMiddle :
  ((A B : Type) → ¬ (A × B) → ((¬ A) ⊎ (¬ B)))
  → (A : Type) → (¬ A) ⊎ (¬ (¬ A))
yugapatDecompositionGivesWeakExcludedMiddle dec A =
  dec A (¬ A) (λ p → snd p (fst p))

------------------------------------------------------------------------
-- Whether there is a
-- THIRD position between the sequential pair and the refusal of the
-- joint assertion is answered in
-- `NaturalMachine.Bhanga_ThePositionsOverTwoAtomsAreAThreeStepChain`.  There is:
--
--   Krama = (¬ सामयिक) × (¬ नित्य)
--     ⇒ Vikalpa = (¬ सामयिक) ⊎ (¬ नित्य)
--       ⇒ Yugapat = ¬ (सामयिक × नित्य)
--
-- **and the two gaps are of different KINDS.**  Krama ⊊ Vikalpa is
-- settled outright by an example — at the trivially-true family
-- `¬ सामयिक` holds while `¬ नित्य` fails — so it is a fact about my
-- instance family.  Vikalpa ⇐ Yugapat is not about the family at all:
-- it is the constructive taboo proved here, and no example can settle
-- it inside `--safe`.
--
-- That distinction is the useful part.  A count of positions says less
-- than the character of the gaps between them: one is refutable, one is
-- only reducible.
------------------------------------------------------------------------

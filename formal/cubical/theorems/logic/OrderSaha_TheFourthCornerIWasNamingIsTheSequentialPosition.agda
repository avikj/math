{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- KramaSaha_TheFourthCornerIWasNamingIsTheSequentialPosition (absent from this repository)
--
-- क्रम / सह (युगपद्) — krama, in sequence; saha or yugapad, at once.
-- The distinction is the Jaina one, from the saptabhag literature
-- (Umsvti, *Tattvrthastra*; Samantabhadra; Akalaka; Siddhasena
-- Divkara), and in this repository it is `Saptabhangi` /
-- `SaptabhangiNaya`, which prove the theorem being used here as a lens:
--
--   स्यात्-अस्ति-नास्ति ≢ स्यात्-अवक्तव्यम्
--
-- sequential assertion of asti and nsti is NOT the simultaneous
-- position; avaktavya is a fourth, irreducibly distinct bhaga.
-- Here it is turned on this module's own objects.
--
-- ────────────────────────────────────────────────────────────────────
-- THE FINDING.
--
-- The "fourth corner" is, by its definition,
--
--   (¬ सामयिक (one Q)) × (¬ नित्य (one Q))
--
-- a PRODUCT of two negations.  Three things are checked below:
--
--   1. the two conjuncts are INDEPENDENT — each is satisfiable while
--      the other fails, so the pair is genuinely "one, and also the
--      other", which is krama;
--   2. **the simultaneous denial collapses to the sequential pair**:
--      `¬ (A ⊎ B) → (¬ A) × (¬ B)` and back, constructively, with no
--      hypothesis — so in this formalism "denying both at once" IS
--      "denying one and denying the other", and there is no room
--      between them;
--   3. hence denying both at once, in this formalism, is exactly the
--      sequential pair; the denial of the JOINT assertion is a further
--      position, see `Yugapat_TheDenialOfJointAssertionDoesNotDecompose`.
--
-- By `Saptabhangi`'s theorem
-- the fourth bhaga is exactly what a sequential
-- position is not — and this corner is a product, which is sequential.
-- The corner sits at the THIRD bhaga,
-- स्यात्-अस्ति-नास्ति, the krama position.
--
------------------------------------------------------------------------

module OrderSaha_TheFourthCornerIWasNamingIsTheSequentialPosition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import AnuktaAvaktavya using (सामयिक ; नित्य)
open import OrderAstiNasti_TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift
  using (one)

------------------------------------------------------------------------
-- 1.  Simultaneous denial collapses to sequential denial
------------------------------------------------------------------------

sahaToKrama : {A B : Type} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
sahaToKrama h = (λ a → h (inl a)) , (λ b → h (inr b))

kramaToSaha : {A B : Type} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
kramaToSaha (na , nb) (inl a) = na a
kramaToSaha (na , nb) (inr b) = nb b

------------------------------------------------------------------------
-- 2.  …and the corner is exactly that collapse, at these objects
------------------------------------------------------------------------

Corner : {R : Type} → (R → Type) → Type
Corner Q = (¬ सामयिक (one Q)) × (¬ नित्य (one Q))

cornerIsDenyingBothAtOnce :
  {R : Type} (Q : R → Type)
  → (¬ (सामयिक (one Q) ⊎ नित्य (one Q)) → Corner Q)
  × (Corner Q → ¬ (सामयिक (one Q) ⊎ नित्य (one Q)))
cornerIsDenyingBothAtOnce Q = sahaToKrama , kramaToSaha

------------------------------------------------------------------------
-- 3.  The two conjuncts are independent
--
-- `¬ सामयिक (one Q)` is pointwise non-refutability and
-- `¬ नित्य (one Q)` is the absence of a uniform proof.  Each holds
-- while the other fails, so the corner really is a conjunction of two
-- separately assertible positions.
------------------------------------------------------------------------

trivial : Unit → Type
trivial _ = Unit

firstAloneHolds : ¬ सामयिक (one trivial)
firstAloneHolds f = snd (f tt) tt

secondFailsThere : ¬ (¬ नित्य (one trivial))
secondFailsThere k = k (λ r → tt , tt)

alwaysFalse : Unit → Type
alwaysFalse _ = ⊥

secondAloneHolds : ¬ नित्य (one alwaysFalse)
secondAloneHolds f = snd (f tt)

firstFailsThere : ¬ (¬ सामयिक (one alwaysFalse))
firstFailsThere k = k (λ _ → tt , (λ e → e))

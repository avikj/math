{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FitnessIsNecessaryUpToDoubleNegation
--
-- यो ग्यानुपलब्धि (yogya-anupalabdhi) as a theorem, and — the part that is
-- new — its CONVERSE, which lands exactly where it must: the fitness
-- condition is necessary only up to double negation, and closing that
-- last gap is precisely the stability of the searched domain.
--
-- ────────────────────────────────────────────────────────────────────
-- THE SCHOOL, NAMED BEFORE ITS TERM, AND THE DISPUTE
--
-- अनुपलब्धि — non-apprehension as a means of knowing — is admitted as a
-- separate prama by the Bha Mmsakas (Kumrila Bhaa,
-- *lokavrttika*, Abhvapariccheda, c. 7th c.) and by Advaita, and is
-- REFUSED as separate by the Prbhkaras, who fold it into perception.
-- The Naiyyikas differ again.  That dispute is live and nothing below
-- takes a side: the theorems are about the CONDITION both sides accept,
-- namely that an absence may be inferred only when the thing is such
-- that it WOULD have been apprehended had it been there.
--
-- `interactive/Yogyata.hs` (absent from this repository) states it, sources it, names the dispute, and applies
-- it to this repository's own import graph — every inertness verdict
-- there carries the domain searched.  This module is the type-theoretic
-- half of the same condition.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY THIS IS NOT A FIFTH RESTATEMENT OF THE Σ/¬ AXIS
--
-- §3 says what the freeness of the negative
-- pole COSTS when the domain widens: exactly a fitness Π, and the
-- converse recovers that Π only under ¬¬ — so the residue is a
-- stability hypothesis on the domain, not on the thing sought.  That is
-- a consequence OF the pattern, not another sighting of it.
------------------------------------------------------------------------

module FitnessIsNecessaryUpToDoubleNegation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

Stable : Type ℓ → Type ℓ
Stable A = ¬ ¬ A → A

------------------------------------------------------------------------
-- 1.  An absence carries its domain, and fitness is what makes it
--     absolute
------------------------------------------------------------------------

-- the search: nothing IN THE DOMAIN bears P
AbsenceOn : {X : Type} (D P : X → Type) → Type
AbsenceOn {X} D P = (x : X) → D x → ¬ P x

-- योग्यता: anything bearing P would have been in the domain searched
Yogya : {X : Type} (D P : X → Type) → Type
Yogya {X} D P = (x : X) → P x → D x

-- यो ग्यानुपलब्धि: a FIT non-apprehension licenses the absolute absence
fitAbsenceIsAbsolute :
  {X : Type} (D P : X → Type)
  → Yogya D P → AbsenceOn D P → (x : X) → ¬ P x
fitAbsenceIsAbsolute D P fit abs x p = abs x (fit x p) p

------------------------------------------------------------------------
-- 2.  Without fitness the inference is unwarranted, exhibited
--
-- Domain = {false}, sought = being `true`.  The search over the domain
-- is clean, `P` is inhabited, and the domain-absence licenses nothing.
------------------------------------------------------------------------

Dom Sought : Bool → Type
Dom    x = x ≡ false
Sought x = x ≡ true

cleanSearch : AbsenceOn Dom Sought
cleanSearch x dx px = true≢false (sym px ∙ dx)

soughtIsThere : Σ[ x ∈ Bool ] Sought x
soughtIsThere = true , refl

searchWasNotFit : ¬ Yogya Dom Sought
searchWasNotFit fit = true≢false (fit true refl)

-- so a clean search plus an unfit domain gives a FALSE absence verdict
unfitAbsenceIsUnwarranted :
  (AbsenceOn Dom Sought) × (¬ Yogya Dom Sought)
                         × (Σ[ x ∈ Bool ] Sought x)
unfitAbsenceIsUnwarranted = cleanSearch , searchWasNotFit , soughtIsThere

------------------------------------------------------------------------
-- 3.  THE CONVERSE, and where it stops
--
-- Suppose a domain D is such that a clean search over it licenses the
-- absolute absence FOR EVERY sought property.  Then D is everything —
-- but only under double negation.  Taking the sought property to be
-- `¬ D` itself is what forces it, and that instance is exactly `¬¬`.
------------------------------------------------------------------------

fitnessIsNecessaryUpToDoubleNegation :
  {X : Type} (D : X → Type)
  → ((P : X → Type) → AbsenceOn D P → ((x : X) → ¬ P x))
  → (x : X) → ¬ ¬ D x
fitnessIsNecessaryUpToDoubleNegation D licenses x =
  licenses (λ y → ¬ D y) (λ y dy ndy → ndy dy) x

-- and the residue is a stability hypothesis on the DOMAIN — not on the
-- thing sought, which is the asymmetry worth having
stableDomainMakesItTotal :
  {X : Type} (D : X → Type)
  → ((x : X) → Stable (D x))
  → ((P : X → Type) → AbsenceOn D P → ((x : X) → ¬ P x))
  → (x : X) → D x
stableDomainMakesItTotal D stab licenses x =
  stab x (fitnessIsNecessaryUpToDoubleNegation D licenses x)

------------------------------------------------------------------------
-- 4.  What this says, and its exact scope
--
-- An absence is knowledge to the extent the looking was fit to find it
-- (§1), an unfit looking licenses a false verdict (§2), and a domain
-- that licenses every absence is total up to ¬¬ (§3).  The last gap —
-- ¬¬ D x to D x — is a stability hypothesis on the domain.
------------------------------------------------------------------------

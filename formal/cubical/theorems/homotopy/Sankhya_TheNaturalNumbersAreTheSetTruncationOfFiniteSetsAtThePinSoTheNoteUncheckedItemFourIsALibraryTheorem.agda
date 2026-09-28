{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सङ्ख्या · the natural numbers are the set truncation of the finite sets
--
-- notes/NATURAL_MACHINE.md (absent from this repository) (main), §7.3 "UNCHECKED — stated in this note,
-- not in Agda", item 4:
--
--   "4. **"ℕ ≃ ∥FinSet∥₀."** Not proved. `card≡MereEq` + `card-Fin` say
--    that `card` induces a bijection between ℕ and FinSet-modulo-mere-
--    equality, which is the π₀ statement in propositional-truncation
--    form. The set-truncation `∥ FinSet ∥₂` is never formed, and no
--    equivalence with it is claimed."
--
-- At the pin the statement is a library theorem:
-- Cubical.Data.FinSet.Cardinality (agda/cubical v0.9) holds
--
--     ∥FinSet∥₂≃ℕ : ∥ FinSet ℓ ∥₂ ≃ ℕ
--
-- with the comment "this is the definition of natural numbers you learned
-- from school".  The note was written against v0.5.  This module records
-- the closure in the note's own orientation, ℕ ≃ ∥ FinSet ∥₂, at every
-- universe, and the two computations the note's `card-Fin` wanted: the
-- count of the canonical n-element set is n, and the class of a finite
-- set is the class of the canonical set of its count.  Nothing here is
-- new mathematics; what is new is that the corpus's own list of unchecked
-- items has one fewer entry, by reading the pinned library.
------------------------------------------------------------------------

module Sankhya_TheNaturalNumbersAreTheSetTruncationOfFiniteSetsAtThePinSoTheNoteUncheckedItemFourIsALibraryTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.Induction using (𝔽in)
open import Cubical.HITs.SetTruncation using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ : Level

-- the note's orientation
ℕ≃∥FinSet∥₂ : ℕ ≃ ∥ FinSet ℓ ∥₂
ℕ≃∥FinSet∥₂ = invEquiv ∥FinSet∥₂≃ℕ

-- the count is the inverse: n ↦ the class of the canonical n-element set
count : ∥ FinSet ℓ ∥₂ → ℕ
count = equivFun ∥FinSet∥₂≃ℕ

class : ℕ → ∥ FinSet ℓ ∥₂
class = equivFun ℕ≃∥FinSet∥₂

count-class : (n : ℕ) → count {ℓ = ℓ} (class n) ≡ n
count-class {ℓ = ℓ} n = secEq (∥FinSet∥₂≃ℕ {ℓ = ℓ}) n

class-count : (X : ∥ FinSet ℓ ∥₂) → class (count X) ≡ X
class-count {ℓ = ℓ} X = retEq (∥FinSet∥₂≃ℕ {ℓ = ℓ}) X

-- the note's `card-Fin`: the count of the canonical set is its index
count-𝔽in : (n : ℕ) → count {ℓ = ℓ} ∣ 𝔽in n ∣₂ ≡ n
count-𝔽in n = card𝔽in n

-- and every finite set's class is the class of the canonical set of its count
class-is-canonical : (X : FinSet ℓ) → ∣ X ∣₂ ≡ ∣ 𝔽in (card X) ∣₂
class-is-canonical X = sym (Iso.leftInv Iso-∥FinSet∥₂-ℕ ∣ X ∣₂)

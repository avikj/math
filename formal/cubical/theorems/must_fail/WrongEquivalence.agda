{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WrongEquivalence
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- It is a designed-annihilation control (collab/PROTOCOL.md (absent from this repository) §7): it
-- asserts the equivalence ℕ ≃ Word for RAW digit words, dropping the
-- canonicity hypothesis.  That statement is false --- `Controls.C1`
-- proves it false --- and the point of this file is to exhibit that the
-- type-checker actually catches it rather than waving it through.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it.
------------------------------------------------------------------------

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

module WrongEquivalence (k : ℕ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Unit

open import Digits k

-- The false round trip.  `value-inj` requires a canonicity certificate
-- for its second word; `tt` is offered in its place, which is exactly
-- the step the mathematics forbids.
digits-value-raw : (w : Word) → digits (value w) ≡ w
digits-value-raw w =
  value-inj (digits (value w)) w (canonical-digits (value w)) tt
            (value-digits (value w))

-- If the line above had gone through, this would be an equivalence
-- between ℕ and the raw word chart --- contradicting Controls.C1.
ℕ≃Word : ℕ ≃ Word
ℕ≃Word = isoToEquiv (iso digits value digits-value-raw value-digits)

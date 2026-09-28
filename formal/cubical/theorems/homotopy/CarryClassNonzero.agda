{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CarryClassNonzero
--
-- ATLAS_OF_N.md (absent from this repository) Proposition 2.11, the cohomological half:
--
--     for every base b ≥ 2, every n ≥ 1, and EVERY digit section
--     s : ℤ/bⁿ → ℤ/bⁿ⁺¹ whatever, the carry class
--
--         [cₙ]  ≠  0     in   H²(ℤ/bⁿ ; ker πₙ),
--
-- where H² is the group constructed in `GroupCohomologyH2`
-- as Z²/B² (the library quotient group), cₙ is `CarryObstruction`'s
-- `Carry.carry` — i.e. the note's s(u)+s(v)−s(u+v) — and πₙ is the
-- truncation ℤ/bⁿ⁺¹ ↠ ℤ/bⁿ.
--
-- The two inputs are combined here and nothing else happens:
--
--   * `GroupCohomologyH2.CarryClass.class-zero→hom-section` — if the class
--     of the carry vanishes then the extension has a *homomorphic*
--     section;
--   * `CarryObstruction.BasePower.extension-does-not-split` — it has none.
--
-- Split out of `GroupCohomologyH2` so that the general construction and
-- its arithmetic instance can be checked independently.
--
-- Coefficients are `ker πₙ` as a group in its own right, NOT ℤ/b: the
-- isomorphism bⁿ/b  /b is not used.
------------------------------------------------------------------------

module CarryClassNonzero where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Fin.Arithmetic using (+ₘ-comm)

open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Group.Base

open import CarryObstruction as CO using ()
open import GroupCohomologyH2 using (module CarryClass)

------------------------------------------------------------------------

-- b = 2 + k ≥ 2 and n = 1 + n′ ≥ 1, exactly as in `CarryObstruction`.
module CyclicCarryClass (k n' : ℕ) where

  open CO.BasePower k n'

  -- For an arbitrary digit set.  (`open … public` is deliberately not
  -- used: only the theorem is re-abstracted over s and sect.)
  module At (s : Fin N → Fin M)
            (sect : (q : Fin N) → red (s q) ≡ q) where

    open CarryClass G Q +ₘ-comm redHom s sect

    -- PROPOSITION 2.11.  The carry class is nonzero.
    carryClass≠0 : ¬ (class carryK ≡ GroupStr.1g (snd H²))
    carryClass≠0 =
      class-zero→hom-section (λ σ h → extension-does-not-split σ h)

  -- … and in particular for the schoolbook alphabet {0,…,bⁿ−1}, whose
  -- carry is the note's cₙ literally.
  module Std = At stdSection stdSection-sect

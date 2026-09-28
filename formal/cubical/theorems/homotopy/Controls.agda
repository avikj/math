{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Controls
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7).
--
-- A claim ships with the apparatus that would destroy it.  The three
-- controls for this development are:
--
--   C1 (here)  the canonicity hypothesis is LOAD-BEARING: without it
--              `value` is not injective, so the equivalence fails.
--              Proved, not asserted.
--
--   C2 (here)  a deliberately WRONG reading of the digit chart --- the
--              big-endian misreading, `value ∘ rev` --- fails its round
--              trip.  Proved as a refutation, so the failure is itself
--              machine-checked.
--
--   C3 (separate, and deliberately NOT part of the checked build)
--              `NaturalMachine/Control/WrongEquivalence.agda` asserts
--              the equivalence ℕ ≃ Word without canonicity.
--
-- A fourth control is the type-checker itself: every module carries
-- --safe.
------------------------------------------------------------------------

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

module Controls (k : ℕ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin using (fzero ; fone ; toℕ)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary using (¬_)

open import Digits k
open import Endian k using (w01 ; w01-canonical ; v1 ; value-v1)

------------------------------------------------------------------------
-- C1.  Canonicity is load-bearing.
--
-- Drop it and `value` stops being injective: the empty word and the
-- one-digit word 0 are different words with the same value.  So the
-- specific pair (digits, value) is not an equivalence ℕ ≃ Word — the
-- bare type ℕ ≃ Word is inhabited (Word is countably infinite), but
-- not by these maps — and the CanWord equivalence is not a formality.
------------------------------------------------------------------------

value-not-injective-on-Word :
  Σ[ u ∈ Word ] Σ[ v ∈ Word ] ((value u ≡ value v) × (¬ (u ≡ v)))
value-not-injective-on-Word =
  [] , (fzero ∷ []) , (0≡m·0 b , λ p → znots (cong length p))

-- Equivalently: the round trip that holds on canonical words fails on
-- general words.
no-raw-round-trip : ¬ ((w : Word) → digits (value w) ≡ w)
no-raw-round-trip h = znots (cong length (sym step ∙ h (fzero ∷ [])))
  where
    step : digits (value (fzero ∷ [])) ≡ []
    step = cong digits (sym (0≡m·0 b))

------------------------------------------------------------------------
-- C2.  The big-endian misreading fails its round trip.
--
-- Reading a little-endian word as if it were big-endian is exactly
-- `value ∘ rev`.  If that were the right chart map, `digits` would
-- invert it.  It does not, and 0 ∷ 1 witnesses the failure.
------------------------------------------------------------------------

wrong-endian-round-trip-fails :
  ¬ ((w : Word) → Canonical w → digits (value (rev w)) ≡ w)
wrong-endian-round-trip-fails h = znots (injSuc (cong length chain))
  where
    -- `rev w01 = 1 ∷ 0`, whose value is 1, whose digits are the
    -- one-digit word `1`, while w01 has length 2.
    chain : (fone ∷ []) ≡ w01
    chain = sym (cong digits value-v1) ∙ h w01 w01-canonical

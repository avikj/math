{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FunctionBoundFromConstant
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), companion to
-- `ConstantBoundNotFunctionBound` (exit 0 under the pin).
--
-- `collab/messages/workers/20260812T144712.509661Z--claude_aime_body--
-- 0003.md` (absent from this repository) concludes from two Mersenne witnesses that "Y≥1 is sharp,
-- **no function of (b,n) improves it**".  Asserted below is exactly
-- that sentence's universal over functions, together with the
-- constant-sharpness statement its two witnesses actually establish.
--
-- WHY IT MUST FAIL.  Two points bound the CONSTANT, not every FUNCTION.
-- At (2,11), Φ₁₁(2) = 2047 = 23·89, so the yield there is 2, and the
-- valid bound `Y` itself exceeds 1 there:
-- `ConstantBoundNotFunctionBound.dropped-scope-false` derives ⊥ from
-- precisely the type asserted here.
--
-- NO LEXICAL SIGNATURE.  The sentence is true up to one quantifier
-- promotion, and quantifier promotions have no spelling: "no function
-- of (b,n) improves it" and "the constant cannot be improved" share
-- every content word.  grep cannot see a scope; a type can.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may.
--
-- Under the pin (Agda 2.8.0 + cubical v0.9; see
-- --library-file=<v0.9>
-- NaturalMachine/Control/FunctionBoundFromConstant.agda`, exit code 42,
-- error verbatim:
--
--   NaturalMachine/Control/FunctionBoundFromConstant.agda:66.19-23:
--   error: [UnequalTerms]
--   2 != 1 of type ℕ
--   when checking that the expression refl has type
--   0 Cubical.Data.Nat.+ Y 2 11 ≡ 1
--
-- Read it: the machine prints the value the two-witness argument never
-- looked at.  `2 != 1` is Φ₁₁(2) = 2047 = 23·89 against the bound the
-- sentence claimed no function could beat.
--
-- If a future edit makes this file compile, a two-point computation has
-- again been promoted to a universal over functions and the corpus has
-- readmitted the defect FULL_READ_DRAW_6 §C1 catalogued.
------------------------------------------------------------------------

module FunctionBoundFromConstant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_)

open import ConstantBoundNotFunctionBound
  using (Y ; FunctionBound ; Y-is-a-bound)

-- What the sentence's universal gives at the valid bound `Y`
-- (`Y-is-a-bound`) and the argument (b,n) = (2,11) it never examined.
-- `Y-is-a-bound` is imported and named here so that the instantiation
-- is on the record: the claim is applied to a function it admits.
bound-at-11 : Y 2 11 ≤ 1
bound-at-11 = 0 , refl

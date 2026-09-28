{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- शेषसिद्धि — the kernel accomplishes by induction the frontier lemmas the
-- engine's composition could not reach.  The machine proposes its own
-- ea; the kernel disposes.
--
-- WHAT THIS IS.  The live engine (`interactive/MathMachine.hs` (absent from this repository), its memory in
-- `interactive/library.terms`) discovers true equations over ℕ by enumeration
-- and composition, tagging each with its prama (anumna) and its naya
-- (trace replay, or induction).  Its own instruments name what it cannot
-- handful of equations that are TRUE, survive all refutation, and are
-- **not equational consequences of the base facts at all** — they need
-- structural induction, "a proof principle from outside the equational
-- theory".  Those are its ea.  This module supplies the kernel proof of
-- each, by induction — closing a frontier the machine computed for itself.
--
-- The engine found them (prama=anumna, by enumeration); the kernel
-- verifies them (pramāṇa=the checked term).  This is the propose→dispose
-- loop across the two lanes.
--
-- The named frontier (SamasaBhavana §9; the engine's own DSL translated to
-- ℕ), each PROVED below:
--   §2  x ≡ x + (0 · x)         the "flagship" (RHS bigger than the goal)
--   §3  x ≡ x + (0 · y)
--   §4  x · (y + 0) ≡ (x · y) + (x · 0)
--   §5  ¬ (suc (x + y) ≤ y)      the engine's  0 = le(s(x+y), y)
--   §6  ¬ (suc (suc (suc x)) ≤ x)  the engine's  0 = le(s(s(s(x))), x)
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module ResidueSiddhi_TheKernelProvesByInductionTheFrontierLemmasTheEnginesCompositionCouldNotReach where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; snotz ; injSuc)
open import Cubical.Data.Nat.Properties using (+-zero ; 0≡m·0 ; max)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; ≤-trans ; ¬m<m ; ≤SumRight)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat using (znots) renaming ()

------------------------------------------------------------------------
-- §2  x ≡ x + (0 · x).  (0 · x reduces to 0; then x + 0 ≡ x.)
------------------------------------------------------------------------

ध्वजः : (x : ℕ) → x ≡ x + (0 · x)
ध्वजः x = sym (+-zero x)      -- 0 · x ≡ 0 definitionally, so x + 0·x ≡ x + 0

------------------------------------------------------------------------
-- §3  x ≡ x + (0 · y).
------------------------------------------------------------------------

शून्यगुणः : (x y : ℕ) → x ≡ x + (0 · y)
शून्यगुणः x y = sym (+-zero x)

------------------------------------------------------------------------
-- §4  x · (y + 0) ≡ (x · y) + (x · 0).
------------------------------------------------------------------------

वितरणम्-शून्ये : (x y : ℕ) → x · (y + 0) ≡ (x · y) + (x · 0)
वितरणम्-शून्ये x y =
    cong (x ·_) (+-zero y)          -- x·(y+0) ≡ x·y
  ∙ sym (+-zero (x · y))            -- ≡ x·y + 0
  ∙ cong ((x · y) +_) (0≡m·0 x)     -- ≡ x·y + x·0   (0 ≡ x·0)

------------------------------------------------------------------------
-- §5  ¬ (suc (x + y) ≤ y)   — the engine's  0 = le(s(x + y), y).
------------------------------------------------------------------------

न-ऊर्ध्वम् : (x y : ℕ) → ¬ (suc (x + y) ≤ y)
न-ऊर्ध्वम् x y p = ¬m<m (≤-trans p (≤SumRight {n = y} {k = x}))
  -- p : suc (x+y) ≤ y = (x+y) < y ;  y ≤ x+y (≤SumRight) ;  compose → (x+y)<(x+y)

------------------------------------------------------------------------
-- §6  ¬ (suc (suc (suc x)) ≤ x)  — the engine's  0 = le(s(s(s(x))), x).
------------------------------------------------------------------------

न-त्रिपदम् : (x : ℕ) → ¬ (suc (suc (suc x)) ≤ x)
न-त्रिपदम् x p = ¬m<m (≤-trans (2 , refl) p)
  -- suc x ≤ suc(suc(suc x)) is (2 , refl);  with p : suc³x ≤ x → suc x ≤ x = x<x

------------------------------------------------------------------------
-- §7  the two max demands (SesaPariksa's third and fourth ea).
------------------------------------------------------------------------

-- max(x,y) + 0 ≡ max(x + 0, y + 0)
संयोगः-शून्ये : (x y : ℕ) → max x y + 0 ≡ max (x + 0) (y + 0)
संयोगः-शून्ये x y =
  +-zero (max x y) ∙ sym (cong₂ max (+-zero x) (+-zero y))

-- max(0,x) + 0 ≡ max(0 + 0, x + 0)   (both sides reduce to x + 0)
संयोगः-आदौ-शून्ये : (x : ℕ) → max 0 x + 0 ≡ max (0 + 0) (x + 0)
संयोगः-आदौ-शून्ये x = refl

------------------------------------------------------------------------
-- §8  a CONTROL, mirroring the engine's own falsehood suite: the false
--     neighbour x = x + (1 · x) is REFUTED (at x = 1, it says 1 ≡ 2).
--     A must-fail beside the proofs (as Control/ modules do for the engine).
------------------------------------------------------------------------

नियन्त्रणम्-मिथ्या : ¬ ((x : ℕ) → x ≡ x + (suc zero · x))
नियन्त्रणम्-मिथ्या f = znots (injSuc (f 1))   -- f 1 : 1 ≡ 2, so 0 ≡ 1
  where open import Cubical.Data.Nat using (znots)

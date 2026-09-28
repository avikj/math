{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- BhavanaSemiring — Brahmagupta's composition law over ℕ, proved.
--
-- BRAHMAGUPTA, Brhmasphuasiddhnta, 628 CE, ch. 18, the rule called
-- bhvan ("production", "composition"):
--
--     (x₁² − D y₁²)(x₂² − D y₂²)
--        = (x₁x₂ + D y₁y₂)² − D(x₁y₂ + x₂y₁)²
--
-- the multiplicativity of the norm form N(x,y) = x² − D y².  `Bhavana.agda` (absent from this repository)
-- carries it over ℤ.  This file is about ℕ, and about a fact that is not a
-- restatement of Brahmagupta but a consequence of putting him in a place he
-- was not working in.
--
-- BHĀVANĀ AS STATED IS FALSE OVER ℕ.  Monus is truncated: where both true
-- norms are negative, each side flattens to 0 and the identity fails.  The
-- witness, found by exhaustive search in machine/thoughts.bhavana.math (absent from this repository), is
-- (x₁,y₁,x₂,y₂) = (0,1,0,1): the true norms are (−1,−1) at D = 1, so the
-- left side is 0 ∸ 0 = 0 while the right side is 1.
--
-- The repair is the one this repository uses everywhere for denominators —
-- clear the offending operation instead of restricting the domain.  Move
-- every negative term across.  With cx = x₁x₂ + D y₁y₂ and
-- cy = x₁y₂ + x₂y₁, bhāvanā becomes, subtraction-free:
--
--     cx² + D x₁² y₂² + D x₂² y₁²  =  x₁² x₂² + D² y₁² y₂² + D cy²
--
-- Over ℤ that is bhāvanā, by adding the same two terms to both sides.  Over
-- ℕ it is true with NO hypothesis and no monus at all.
--
-- WHY THIS FILE EXISTS.  That statement was verified on 28561 points at
-- D = 1 and D = 2, zero failures.  Exhaustive checking of a *bounded box* is
-- not a proof of a statement quantified over all of ℕ.
-- The identity is in fact a commutative-semiring identity: expanding both
-- sides gives the same five monomials, with the cross term 2D x₁x₂y₁y₂
-- appearing once on each side.  So it needs no induction, no ordering, and
-- no subtraction — it holds in ANY commutative semiring, and ℕ is one.
--
-- 28561 points become ∀ x₁ y₁ x₂ y₂ : ℕ.
------------------------------------------------------------------------

module CompositionSemiring where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_)
open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)

-- the two composed coordinates, exactly as Brahmagupta gives them
cx : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
cx D x₁ y₁ x₂ y₂ = x₁ · x₂ + D · (y₁ · y₂)

cy : ℕ → ℕ → ℕ → ℕ → ℕ
cy x₁ y₁ x₂ y₂ = x₁ · y₂ + x₂ · y₁

-- BHĀVANĀ OVER ℕ, subtraction-free.
--
-- Read it as the ℤ identity with both negative terms carried across:
-- (x₁²−Dy₁²)(x₂²−Dy₂²) = cx² − D·cy² becomes, adding D x₁²y₂² + D x₂²y₁²
-- to each side, the statement below.
bhavanaℕ : (D x₁ y₁ x₂ y₂ : ℕ)
         → cx D x₁ y₁ x₂ y₂ · cx D x₁ y₁ x₂ y₂
             + (D · (x₁ · x₁ · (y₂ · y₂)) + D · (x₂ · x₂ · (y₁ · y₁)))
         ≡ x₁ · x₁ · (x₂ · x₂)
             + (D · D · (y₁ · y₁ · (y₂ · y₂))
                + D · (cy x₁ y₁ x₂ y₂ · cy x₁ y₁ x₂ y₂))
bhavanaℕ D x₁ y₁ x₂ y₂ = solveℕ!

-- The two specialisations the engine was handed, so the general theorem and
-- the machine's own candidates are visibly the same object.

bhavana₁ : (x₁ y₁ x₂ y₂ : ℕ)
         → cx 1 x₁ y₁ x₂ y₂ · cx 1 x₁ y₁ x₂ y₂
             + (x₁ · x₁ · (y₂ · y₂) + x₂ · x₂ · (y₁ · y₁))
         ≡ x₁ · x₁ · (x₂ · x₂)
             + (y₁ · y₁ · (y₂ · y₂) + cy x₁ y₁ x₂ y₂ · cy x₁ y₁ x₂ y₂)
bhavana₁ x₁ y₁ x₂ y₂ = solveℕ!

bhavana₂ : (x₁ y₁ x₂ y₂ : ℕ)
         → cx 2 x₁ y₁ x₂ y₂ · cx 2 x₁ y₁ x₂ y₂
             + (2 · (x₁ · x₁ · (y₂ · y₂)) + 2 · (x₂ · x₂ · (y₁ · y₁)))
         ≡ x₁ · x₁ · (x₂ · x₂)
             + (4 · (y₁ · y₁ · (y₂ · y₂))
                + 2 · (cy x₁ y₁ x₂ y₂ · cy x₁ y₁ x₂ y₂))
bhavana₂ x₁ y₁ x₂ y₂ = solveℕ!

-- COMMUTATIVITY OF THE COMPOSITION — samāsa-bhāvanā is symmetric in the two
-- composed pairs, which is what makes the solutions a monoid rather than
-- merely a set closed under an operation.  This is the structural half of
-- what cakravla stands on.
cxComm : (D x₁ y₁ x₂ y₂ : ℕ) → cx D x₁ y₁ x₂ y₂ ≡ cx D x₂ y₂ x₁ y₁
cxComm D x₁ y₁ x₂ y₂ = solveℕ!

cyComm : (x₁ y₁ x₂ y₂ : ℕ) → cy x₁ y₁ x₂ y₂ ≡ cy x₂ y₂ x₁ y₁
cyComm x₁ y₁ x₂ y₂ = solveℕ!

-- COMPOSITION WITH THE UNIT (1,0) fixes the pair: the Pell identity element.
cxUnit : (D x y : ℕ) → cx D x y 1 0 ≡ x
cxUnit D x y = solveℕ!

cyUnit : (x y : ℕ) → cy x y 1 0 ≡ y
cyUnit x y = solveℕ!

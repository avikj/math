{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CakravalaNat — the cycle's step over ℕ, every subtraction cleared.
--
-- WHY THIS FILE EXISTS.  `CakravalaDescent.agda` proves the step over an
-- arbitrary commutative ring, which is the right generality and is also
-- unusable for certifying an actual run.  Cubical's ℤ multiplication is
-- UNARY —
--
--     pos (suc n) · m = m + pos n · m        (Cubical/Data/Int/Base.agda)
--
-- — so a `refl` on the nine-digit integers the cakravāla produces at D = 61
-- asks the kernel for about 10¹⁸ unfoldings and never returns.  An attempt
-- had to be killed.  Cubical's ℕ is `Agda.Builtin.Nat`, whose `_+_` and
-- `_·_` are GMP-backed, so the identical statement over ℕ is instant.
--
-- THE REPAIR IS THE ONE THIS REPOSITORY ALREADY USES.  `BhavanaSemiring`
-- found that bhāvanā is FALSE over ℕ as classically written, because monus
-- truncates, and that moving every negative term across makes it true with
-- no hypothesis at all — and, better, makes it a commutative-SEMIRING
-- identity, so it needs no induction, no ordering and no subtraction.  The
-- same move works here, and this file is that move applied to the cycle
-- rather than to the composition.
--
-- WHAT IS CLEARED.  `Bhavana.cakravalaCleared` says
--
--     N D a b · (m² − D)  ≡  N D (am + Db) (a + bm)
--
-- Expand both sides; the cross terms 2abDm cancel and what remains is
--
--     a²m² + D²b² − Da² − Db²m²
--
-- on each side.  Carrying the two negative terms across gives a statement
-- with no subtraction anywhere:
--
--     (am + Db)² + D·a² + D·b²m²  ≡  a²m² + D²b² + D·(a + bm)²
--
-- Over ℤ that IS `cakravalaCleared`, by adding the same two terms to both
-- sides.  Over ℕ it is true for ALL naturals, with no hypothesis, and it is
-- a semiring identity — so `solve` discharges it and no case analysis on the
-- sign of k is needed.  The sign of k was the whole obstacle to stating the
-- cycle over ℕ, and clearing the subtraction removes it rather than handling
-- it.
--
-- WHAT THIS BUYS.  Each turn of a concrete run can now be certified by
-- INSTANTIATING this theorem at that turn's numbers, in arithmetic the
-- kernel actually computes.  `interactive/NalandaEmit.hs` (absent from this repository) does exactly that.
-- The alternative — emitting `refl` for each turn — would prove only that
-- the generator's arithmetic agrees with the kernel's, and would not tie the
-- run to Brahmagupta's law at all.
------------------------------------------------------------------------

module CakravalaNat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_)
open import Cubical.Tactics.NatSolver.Reflection using (solveℕ!)

-- Brahmagupta's two composed coordinates at the trivial triple (m, 1, m²−D),
-- which is the composition the cycle performs at every turn.
--   ca = a·m + D·b      cb = a + b·m
ca : ℕ → ℕ → ℕ → ℕ → ℕ
ca D a b m = a · m + D · b

cb : ℕ → ℕ → ℕ → ℕ
cb a b m = a + b · m

-- THE STEP'S IDENTITY, SUBTRACTION-FREE, FOR ALL NATURALS.
--
-- Read it as `Bhavana.cakravalaCleared` with both negative terms carried
-- across.  `solve` discharges it because after expansion both sides are the
-- same five monomials; the cross term D·a·b·m appears twice on each side.
--
-- `solve` for the NatSolver needs the definition point-free.
cakravalaℕ : (D a b m : ℕ)
           → ca D a b m · ca D a b m + (D · (a · a) + D · (b · b · (m · m)))
           ≡ a · a · (m · m) + (D · D · (b · b) + D · (cb a b m · cb a b m))
cakravalaℕ D a b m = solveℕ!

------------------------------------------------------------------------
-- The two instances a run actually needs, so a certificate can name them
-- rather than re-deriving the shape each time.
------------------------------------------------------------------------

-- At b = 1 — the SEED of every cycle is the trivial triple (⌊√D⌋, 1, ⌊√D⌋²−D),
-- so the first turn is always this case.
cakravalaSeedℕ : (D a m : ℕ)
               → ca D a 1 m · ca D a 1 m + (D · (a · a) + D · (m · m))
               ≡ a · a · (m · m) + (D · D + D · (cb a 1 m · cb a 1 m))
cakravalaSeedℕ D a m = solveℕ!

-- At m = 0 — composition with (0, 1, −D), the degenerate turn.  Stated
-- because a reader checking the general identity at a boundary should not
-- have to trust that it survives one; `solve` proves it does.
cakravalaZeroℕ : (D a b : ℕ)
               → ca D a b 0 · ca D a b 0 + (D · (a · a) + 0)
               ≡ 0 + (D · D · (b · b) + D · (cb a b 0 · cb a b 0))
cakravalaZeroℕ D a b = solveℕ!

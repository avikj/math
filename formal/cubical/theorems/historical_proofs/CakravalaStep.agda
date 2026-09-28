{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Cakravala
--
-- The cyclic method's step, as a checked term.
--
-- `Bhavana.agda` (absent from this repository) has the composition law and the two divisibility
-- conversions; this file supplies the STEP — the thing that makes
-- the method cyclic — and nothing more.
--
-- ────────────────────────────────────────────────────────────────────
-- PROVENANCE
--
-- Jayadeva, c. 950 CE, reported by Udayadivkara in the *Sundar*
-- (11th c.); Bhskara II, *Bjagaita*, 1150 CE, where it is worked in
-- full and applied to D = 61 and D = 67.  It solves x² − D y² = 1 for
-- every non-square D, in a handful of cycles, six centuries before
-- Brouncker and Lagrange.  Euler's attribution of the equation to Pell —
-- who never worked on it — is later still and is the name it is taught
-- under.
--
-- ────────────────────────────────────────────────────────────────────
-- THE STEP
--
-- A state is a triple (a, b, k) with a² − D b² = k.  Given m with
-- k | a + bm, the next state is
--
--     a' = (a m + D b)/k,   b' = (a + b m)/k,   k' = (m² − D)/k.
--
-- `cakravala-step` below proves the state condition is preserved, in
-- CLEARED form — no division anywhere in the statement:
--
--     k·a' = am + Db,  k·b' = a + bm,  k·k' = m² − D
--        ⟹  (k·k)·(a'² − D b'²)  ≡  (k·k)·k'
--
-- One solver identity does the work:
--
--     (am + Db)² − D(a + bm)²  ≡  (a² − Db²)(m² − D)
--
-- which is Brahmagupta's composition specialised to the trivial triple
-- (m, 1, m² − D) — the one instance the cakravāla actually uses.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THE CLEARED FORM SAYS
--
-- The identity is unconditional.  The DESCENT — concluding a'² − Db'² = k'
-- from the cleared form — needs cancelling k², i.e. k invertible or the
-- ring cancellative.  That is precisely what
-- `DescentIsNotInversion` found and `DescentCostsTheIntegers` priced:
-- the cakravla's descent is division by a scalar, not inversion in the
-- composition monoid, and dividing is what costs the integers.
--
-- So the oldest algorithm here and the newest theorem here say the same
-- thing, and the algorithm said it first: **the cycle turns on a
-- division.**
--
------------------------------------------------------------------------

module CakravalaStep where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection

private
  variable
    ℓ : Level

module Cycle (R : CommRing ℓ) where

  open CommRingStr (snd R)

  A : Type ℓ
  A = fst R

  -- the state condition: (a, b, k) lies on the form x² − D y²
  OnForm : A → A → A → A → Type ℓ
  OnForm D a b k = (a · a) - (D · (b · b)) ≡ k

  private
    -- pull k² through the form
    homog : (D k a' b' : A) →
      (k · k) · ((a' · a') - (D · (b' · b')))
      ≡ ((k · a') · (k · a')) - (D · ((k · b') · (k · b')))
    homog D k a' b' = solve! R

    -- BRAHMAGUPTA, at the trivial triple (m, 1, m² − D).  This is the
    -- whole engine of the cyclic method.
    bhavana-trivial : (D a b m : A) →
      (((a · m) + (D · b)) · ((a · m) + (D · b)))
      - (D · ((a + (b · m)) · (a + (b · m))))
      ≡ ((a · a) - (D · (b · b))) · ((m · m) - D)
    bhavana-trivial D a b m = solve! R

    regroup : (k k' : A) → k · (k · k') ≡ (k · k) · k'
    regroup k k' = solve! R

  ----------------------------------------------------------------------
  -- THE STEP.  Cleared of denominators, so no division appears.
  ----------------------------------------------------------------------

  cakravala-step :
    (D a b k m a' b' k' : A)
    → OnForm D a b k
    → k · a' ≡ (a · m) + (D · b)
    → k · b' ≡ a + (b · m)
    → k · k' ≡ (m · m) - D
    → (k · k) · ((a' · a') - (D · (b' · b'))) ≡ (k · k) · k'
  cakravala-step D a b k m a' b' k' onform ha hb hk =
      homog D k a' b'
    ∙ cong₂ (λ p q → (p · p) - (D · (q · q))) ha hb
    ∙ bhavana-trivial D a b m
    ∙ cong₂ _·_ onform (sym hk)
    ∙ regroup k k'

------------------------------------------------------------------------
-- A CYCLE, RUN.  Bhskara's own example, D = 61, first step.
--
--   start   (a,b,k) = (8, 1, 3)        64 − 61 = 3
--   choose  m = 7                      3 | 8 + 1·7 = 15,  m² − D = −12
--   then    a' = (8·7 + 61)/3 = 39,  b' = 15/3 = 5,  k' = −12/3 = −4
--   check   39² − 61·5² = 1521 − 1525 = −4
--
-- The state condition is preserved, and note that |k| RISES here, 3 to 4.
-- The cyclic method does not descend monotonically in |k|; that is why it
-- needs Bhāskara’s choice rule (m = 7 minimises |m² − 61| = 12 among the
-- m with 3 | 8 + m) and why termination is not the algebra.  Both states
-- are checked below by `refl`.
------------------------------------------------------------------------

open Cycle ℤCommRing using (OnForm)

start-61 : OnForm (pos 61) (pos 8) (pos 1) (pos 3)
start-61 = refl

next-61 : OnForm (pos 61) (pos 39) (pos 5) (negsuc 3)
next-61 = refl

-- negsuc 3 is −4, so the next state is (39, 5, −4)
------------------------------------------------------------------------

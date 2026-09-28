{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kuttaka — Āryabhaṭa's pulverizer as a THEOREM, not a name.
--
-- SOURCE AND PRIORITY.  The kuaka ("pulverizer") is ryabhaa's
-- algorithm for the linear indeterminate equation, ryabhaya,
-- Gaṇitapāda 32–33 (499 CE), expounded algorithmically by Bhāskara I,
-- Āryabhaṭīyabhāṣya (629 CE).  The coefficients are "pulverized" —
-- broken into successively smaller ones by repeated division — and the
-- solution is recovered by back-substitution up the resulting column,
-- the vall.  It is the first solution of ax − by = c on record.
-- The module `KuttakaValli.agda` earns "vall" (the
-- trace-as-syntax) but not "kuṭṭaka" — it has no gcd, no Bézout, no
-- back-substitution.  This module supplies the missing theorem.
--
-- (It is self-contained over ℤ — no matrix/continuant dependency.)
--
-- WHAT IS PROVED.  No postulates, no holes, --safe.
--
--   Run a b g     the pulverizer's descent as INDUCTIVE EVIDENCE: the
--                 vall of (a,b) bottoming out at g.  Termination is
--                 carried by the evidence — the run IS Āryabhaṭa's vallī,
--                 a checked trace — so no well-founded recursion is
--                 needed.  Each `div` step records one division
--                 a ≡ q·b + r; the quotients q are the vallī column.
--   bezout        THE KUṬṬAKA: every run yields x, y with a·x + b·y ≡ g,
--                 the coefficients built by back-substitution up the
--                 vallī — x' , y'  become  y' , x' − q·y' at each step.
--                 This is the "keep the remainder and recurse" rule,
--                 made a term.
--   inhomogeneous  a·x + b·y ≡ g  gives, for the equation ax + by = g·k,
--                 the solution (k·x, k·y): the scaled solution family.
--   gcdDivides    the terminal g divides both a and b (g is a COMMON
--                 divisor), by the same descent read for divisibility.
--   gcdGreatest   any common divisor of a and b divides g (g is the
--                 GREATEST).  Together: g is the gcd, and bezout is its
--                 Bézout identity — the whole pulverizer.
------------------------------------------------------------------------

module Kuttaka where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Int.Properties
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

------------------------------------------------------------------------
-- The pulverizer's descent, as inductive evidence (the vall).
------------------------------------------------------------------------

-- Run a b g : the kuaka on (a,b) descends, via genuine divisions
-- a ≡ q·b + r, to the terminal value g (the gcd, when the r's are true
-- remainders).  The list of q's, read top to bottom, is the vall.
data Run : ℤ → ℤ → ℤ → Type where
  stop : (g : ℤ) → Run g (pos 0) g
  div  : (a b q r g : ℤ)
       → a ≡ q · b + r
       → Run b r g
       → Run a b g

------------------------------------------------------------------------
-- Back-substitution up the vall.  The one ring identity the descent
-- needs, isolated: with a replaced by its division q·b + r, the new
-- coefficients (y' , x' − q·y') reproduce the old relation on (b , r).
------------------------------------------------------------------------

private
  -- pure ℤ ring identity (no hypothesis): the heart of back-substitution.
  -- Fully ∀-quantified, as the v0.5 CommRing solver requires.
  backSubst : (b q r x y : ℤ)
            → (q · b + r) · y + b · (x + (- (q · y))) ≡ b · x + r · y
  backSubst b q r x y = solve! ℤCommRing

  -- scaling the Bézout pair through k.
  ringStepL : (a b k x y : ℤ)
            → a · (x · k) + b · (y · k) ≡ (a · x + b · y) · k
  ringStepL a b k x y = solve! ℤCommRing

  -- base coefficients (1,0): pos 0 · pos 0 reduces to pos 0 (first-arg
  -- recursion), g · pos 1 ≡ g by ·IdR, then drop the + pos 0.
  baseId : (g : ℤ) → g · pos 1 + pos 0 · pos 0 ≡ g
  baseId g = cong (_+ pos 0) (·IdR g) ∙ +Comm g (pos 0) ∙ sym (pos0+ g)

------------------------------------------------------------------------
-- The kuṭṭaka: every run yields a Bézout pair for its terminal g.
------------------------------------------------------------------------

bezout : (a b g : ℤ) → Run a b g
       → Σ[ x ∈ ℤ ] Σ[ y ∈ ℤ ] (a · x + b · y ≡ g)
bezout .g .(pos 0) g (stop g) = pos 1 , pos 0 , baseId g
bezout a b g (div a b q r g eq run) =
  let (x' , y' , ih) = bezout b r g run
  in  y'
    , (x' + (- (q · y')))
    , ( cong (λ z → z · y' + b · (x' + (- (q · y')))) eq
        ∙ backSubst b q r x' y'
        ∙ ih )

------------------------------------------------------------------------
-- The iṣṭa-scaled family: a solution of a·x + b·y = g·k for any k.
------------------------------------------------------------------------

inhomogeneous : (a b g k : ℤ) → Run a b g
              → Σ[ x ∈ ℤ ] Σ[ y ∈ ℤ ] (a · x + b · y ≡ g · k)
inhomogeneous a b g k run =
  let (x , y , p) = bezout a b g run
  in  (x · k) , (y · k) , (ringStepL a b k x y ∙ cong (_· k) p)

------------------------------------------------------------------------
-- The answer is a family (KUTTAKA_SOLUTION_FAMILY.md (absent from this repository), stated there only in
-- prose): from one solution of a·x + b·y ≡ g, every (x₀ + t·b , y₀ − t·a)
-- is again a solution — the t·b and t·a cancel.  (The finest step uses
-- b/g, a/g; this coarser b, a family is already infinite and exact.)
------------------------------------------------------------------------

private
  famId : (a b x₀ y₀ t : ℤ)
        → a · (x₀ + t · b) + b · (y₀ + (- (t · a))) ≡ a · x₀ + b · y₀
  famId a b x₀ y₀ t = solve! ℤCommRing

solutionFamily : (a b g x₀ y₀ : ℤ) → a · x₀ + b · y₀ ≡ g
               → (t : ℤ) → a · (x₀ + t · b) + b · (y₀ + (- (t · a))) ≡ g
solutionFamily a b g x₀ y₀ sol t = famId a b x₀ y₀ t ∙ sol

-- Completeness fragment: any two solutions differ by a HOMOGENEOUS
-- solution — a·(x−x') + b·(y−y') = 0.  With solutionFamily, this brackets
-- the solution set from both sides.
private
  famDiffId : (a b x y x' y' : ℤ)
            → a · (x + (- x')) + b · (y + (- y'))
              ≡ (a · x + b · y) + (- (a · x' + b · y'))
  famDiffId a b x y x' y' = solve! ℤCommRing

solutionsDiffer : (a b g x y x' y' : ℤ)
                → a · x + b · y ≡ g → a · x' + b · y' ≡ g
                → a · (x + (- x')) + b · (y + (- y')) ≡ pos 0
solutionsDiffer a b g x y x' y' p q =
  famDiffId a b x y x' y' ∙ cong₂ (λ u v → u + (- v)) p q ∙ -Cancel g

------------------------------------------------------------------------
-- g is the gcd.  Same descent, read for divisibility: g divides both a
-- and b, and any common divisor of a and b divides g.  (No r<b needed:
-- the recurrences carry divisibility regardless; r<b is only for
-- termination and least-remainder.)
------------------------------------------------------------------------

_∣_ : ℤ → ℤ → Type
d ∣ n = Σ[ k ∈ ℤ ] (n ≡ d · k)

private
  -- a = q·b + r with b = g·kb, r = g·kr  ⟹  a = g·(q·kb + kr)
  combineId : (g q kb kr : ℤ)
            → q · (g · kb) + g · kr ≡ g · (q · kb + kr)
  combineId g q kb kr = solve! ℤCommRing

  -- from a ≡ q·b + r, recover r ≡ a + (-(q·b))
  remId : (b q r a : ℤ) → (q · b + r) + (- (q · b)) ≡ r
  remId b q r a = solve! ℤCommRing

  -- a = d·ka, b = d·kb  ⟹  a + (-(q·b)) = d·(ka + (-(q·kb)))
  descId : (d q ka kb : ℤ)
         → d · ka + (- (q · (d · kb))) ≡ d · (ka + (- (q · kb)))
  descId d q ka kb = solve! ℤCommRing

-- g divides a and b, along the run.
gcdDivides : (a b g : ℤ) → Run a b g → (g ∣ a) × (g ∣ b)
gcdDivides .g .(pos 0) g (stop g) =
  (pos 1 , sym (·IdR g)) , (pos 0 , sym (·Comm g (pos 0)))
gcdDivides a b g (div a b q r g eq run) =
  let ((kb , b≡gkb) , _) = gcdDivides b r g run
      (kr , r≡gkr)       = snd (gcdDivides b r g run)
  in  ( (q · kb + kr)
      , ( eq
          ∙ cong₂ (λ u v → q · u + v) b≡gkb r≡gkr
          ∙ combineId g q kb kr ) )
    , (kb , b≡gkb)

-- any common divisor of a and b divides g.
gcdGreatest : (a b g d : ℤ) → Run a b g → d ∣ a → d ∣ b → d ∣ g
gcdGreatest .g .(pos 0) g d (stop g) d∣a _ = d∣a
gcdGreatest a b g d (div a b q r g eq run) (ka , a≡dka) (kb , b≡dkb) =
  gcdGreatest b r g d run (kb , b≡dkb) d∣r
  where
    r≡ : r ≡ a + (- (q · b))
    r≡ = sym (cong (_+ (- (q · b))) eq ∙ remId b q r a)
    d∣r : d ∣ r
    d∣r = (ka + (- (q · kb)))
        , ( r≡
            ∙ cong₂ (λ u v → u + (- (q · v))) a≡dka b≡dkb
            ∙ descId d q ka kb )

------------------------------------------------------------------------
-- Non-vacuity: a concrete vall.  kuaka on (7,5):
--   7 = 1·5 + 2 ,  5 = 2·2 + 1 ,  2 = 2·1 + 0  → gcd 1.
-- The quotient column (the vall) is 1, 2, 2.  `bezout example` then
-- computes a genuine (x,y) with 7·x + 5·y ≡ 1.
------------------------------------------------------------------------

example : Run (pos 7) (pos 5) (pos 1)
example =
  div (pos 7) (pos 5) (pos 1) (pos 2) (pos 1) refl
    (div (pos 5) (pos 2) (pos 2) (pos 1) (pos 1) refl
      (div (pos 2) (pos 1) (pos 2) (pos 0) (pos 1) refl
        (stop (pos 1))))

-- the solved coefficients exist and satisfy the equation, by `bezout`:
exampleSolves : Σ[ x ∈ ℤ ] Σ[ y ∈ ℤ ] (pos 7 · x + pos 5 · y ≡ pos 1)
exampleSolves = bezout (pos 7) (pos 5) (pos 1) example

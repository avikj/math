{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S09SmithKuttaka
--
-- THE TRANSLATION.  Two documents in this repository state the same
-- theorem in vocabularies that do not cite each other:
--
--   notes/LEAN_SMITH_CERTIFICATE_GATE.md (absent from this repository)
--     an untrusted producer submits A, L, R, d₁, d₂; the checker
--     accepts exactly when diag(d₁,d₂) = L A R, |det L| = |det R| = 1,
--     0 ≤ dᵢ, d₁ ∣ d₂.
--
--   collab/messages/workers/…--codex_arithmetic_life--0002.md (absent from this repository)
--     for a z ≡ b (mod m), g = gcd(a,m) is the COMPLETE obstruction:
--     g ∤ b ⇒ unsolvable, g ∣ b ⇒ solvable, and the residue lifts
--     exactly g ways.
--
-- The gate note never says what its certificate BUYS.  This module
-- says it, in the 1×2 case, and proves it: the Smith invariant of the
-- 1×2 matrix [a m] is the complete obstruction of the kuṭṭaka, and the
-- certificate alone — no gcd algorithm, no Euclidean descent, no
-- appeal to a producer — already yields both directions with explicit
-- integer witnesses.
--
--   repToDiv    a z + m k = b  →  d ∣ b        (obstruction is necessary)
--   divToRep    d ∣ b          →  a z + m k = b (obstruction is sufficient,
--                                                witnesses z = u p t,
--                                                          k = u r t)
--
-- Consequence for the gate: a checker for the DIAGONAL FORM already
-- decides solvability of the associated linear Diophantine problem.
-- Nothing about gcd needs to enter the trusted base; `d` is whatever
-- the untrusted producer wrote down, and the equations pin it.
--
-- Method note.  Every proof below is (i) one polynomial identity
-- discharged by the commutative-ring solver and (ii) exactly three
-- hypothesis rewrites: eq1, eq2, and the two unit conditions.  No
-- division, no case split, no ordering of ℤ, no decidability.  The
-- statement is therefore true over any commutative ring with the same
-- certificate shape; ℤ is not used.
------------------------------------------------------------------------

module Swarm.S09SmithKuttaka where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open CommRingStr (ℤCommRing .snd)

R : Type
R = fst ℤCommRing

-- divisibility as a WITNESS, matching Gamma0Partner's convention -----

_Divides_ : R → R → Type
d Divides b = Σ[ t ∈ R ] b ≡ d · t

-- representability: the kuaka's "a z ≡ b (mod m)" without quotients

Rep : R → R → R → Type
Rep a m b = Σ[ z ∈ R ] Σ[ k ∈ R ] a · z + m · k ≡ b

------------------------------------------------------------------------
-- The certificate.  This is the gate note's `Valid`, specialised to a
-- 1×2 matrix A = [a m]:  L = (u) with u² = 1, R = (p q / r s) with
-- det R = ε, ε² = 1, and L A R = [d 0].  d₂ = 0 makes the note's
-- conditions 0 ≤ d₂ and d₁ ∣ d₂ automatic, so they carry no content
-- here and are omitted; nothing else is dropped.
------------------------------------------------------------------------

record Cert (a m : R) : Type where
  constructor cert
  field
    d u ε p q r s : R
    uu  : u · u ≡ 1r                 -- |det L| = 1
    εε  : ε · ε ≡ 1r                 -- |det R| = 1
    dV  : p · s - q · r ≡ ε          -- det R = ε
    eq1 : u · (a · p + m · r) ≡ d    -- (L A R)₁₁ = d
    eq2 : u · (a · q + m · s) ≡ 0r   -- (L A R)₁₂ = 0

------------------------------------------------------------------------
-- Ring identities.  Each is a single polynomial identity; the solver
-- is the whole proof.  keyA and keyM are the two adjugate contractions
--       s·(row 1) − r·(row 2)   and   −q·(row 1) + p·(row 2),
-- which extract a·det R and m·det R from the certificate equations.
------------------------------------------------------------------------

private
  pad : (x c : R) → x ≡ x + c · 0r
  pad _ _ = solve! ℤCommRing

  tidy : (x : R) → 1r · 1r · x ≡ x
  tidy _ = solve! ℤCommRing

  keyA : (a m u ε p q r s : R)
       → (ε · u · s) · (u · (a · p + m · r))
         + (- (ε · u · r)) · (u · (a · q + m · s))
         ≡ (u · u) · (ε · (p · s - q · r)) · a
  keyA _ _ _ _ _ _ _ _ = solve! ℤCommRing

  keyM : (a m u ε p q r s : R)
       → (- (ε · u · q)) · (u · (a · p + m · r))
         + (ε · u · p) · (u · (a · q + m · s))
         ≡ (u · u) · (ε · (p · s - q · r)) · m
  keyM _ _ _ _ _ _ _ _ = solve! ℤCommRing

  dSum : (a m u p r : R) → a · (u · p) + m · (u · r) ≡ u · (a · p + m · r)
  dSum _ _ _ _ _ = solve! ℤCommRing

  repFactor : (d x y z k : R) → (x · d) · z + (y · d) · k ≡ d · (x · z + y · k)
  repFactor _ _ _ _ _ = solve! ℤCommRing

  distT : (a m x y t : R) → a · (x · t) + m · (y · t) ≡ (a · x + m · y) · t
  distT _ _ _ _ _ = solve! ℤCommRing

------------------------------------------------------------------------
-- The theorems.
------------------------------------------------------------------------

module _ {a m : R} (C : Cert a m) where
  open Cert C

  -- The invariant divides both entries.  This is the direction the
  -- gate note's checker does NOT obviously give you: it says d is the
  -- (1,1) entry of a normal form, and we recover d ∣ a, d ∣ m from
  -- unimodularity alone, without inverting R.

  aFromD : (ε · u · s) · d ≡ a
  aFromD =
    pad ((ε · u · s) · d) (- (ε · u · r))
    ∙ cong₂ (λ X Y → (ε · u · s) · X + (- (ε · u · r)) · Y) (sym eq1) (sym eq2)
    ∙ keyA a m u ε p q r s
    ∙ cong₂ (λ X Y → X · (ε · Y) · a) uu dV
    ∙ cong (λ X → 1r · X · a) εε
    ∙ tidy a

  mFromD : (- (ε · u · q)) · d ≡ m
  mFromD =
    pad ((- (ε · u · q)) · d) (ε · u · p)
    ∙ cong₂ (λ X Y → (- (ε · u · q)) · X + (ε · u · p) · Y) (sym eq1) (sym eq2)
    ∙ keyM a m u ε p q r s
    ∙ cong₂ (λ X Y → X · (ε · Y) · m) uu dV
    ∙ cong (λ X → 1r · X · m) εε
    ∙ tidy m

  -- d is itself an a,m-combination: the Bézout direction, read off eq1.

  dFromAM : a · (u · p) + m · (u · r) ≡ d
  dFromAM = dSum a m u p r ∙ eq1

  ---------------------------------------------------------------------
  -- MAIN.  The Smith invariant is the complete obstruction.
  ---------------------------------------------------------------------

  repToDiv : (b : R) → Rep a m b → d Divides b
  repToDiv b (z , k , h) =
    ( (ε · u · s) · z + (- (ε · u · q)) · k
    , sym h
      ∙ cong₂ (λ X Y → X · z + Y · k) (sym aFromD) (sym mFromD)
      ∙ repFactor d (ε · u · s) (- (ε · u · q)) z k )

  divToRep : (b : R) → d Divides b → Rep a m b
  divToRep b (t , h) =
    ( (u · p) · t
    , (u · r) · t
    , distT a m (u · p) (u · r) t ∙ cong (λ X → X · t) dFromAM ∙ sym h )

  obstructionComplete : (b : R)
    → (d Divides b → Rep a m b) × (Rep a m b → d Divides b)
  obstructionComplete b = divToRep b , repToDiv b

  -- The false branch of the broadcast: "12 z ≡ 5 (mod 30) stops at
  -- 6 ∤ 5".  Non-divisibility is a complete refutation, not a heuristic.

  falseBranch : (b : R) → (d Divides b → ⊥) → Rep a m b → ⊥
  falseBranch b nd rep = nd (repToDiv b rep)

------------------------------------------------------------------------
-- A closed instance, so the certificate type is not vacuously stated.
--
--   A = [12  30],  L = (1),  R = ( 3   5 )   det R = 3·(-2) - 5·(-1) = -1
--                                 (-1  -2)
--   L A R = [12·3 + 30·(-1),  12·5 + 30·(-2)] = [6, 0].
--
-- and the broadcast's own example 12 z ≡ 18 (mod 30) is then SOLVED by
-- `divToRep`, which returns z = 9, k = -3.  Note 9 ≡ 4 (mod 5): the
-- broadcast's residue class, recovered from the certificate rather
-- than from a pulverizer run.
------------------------------------------------------------------------

C1230 : Cert (pos 12) (pos 30)
C1230 = cert (pos 6) (pos 1) (negsuc 0) (pos 3) (pos 5) (negsuc 0) (negsuc 1)
             refl refl refl refl refl

six∣18 : (pos 6) Divides (pos 18)
six∣18 = pos 3 , refl

solve1218 : Rep (pos 12) (pos 30) (pos 18)
solve1218 = divToRep C1230 (pos 18) six∣18

-- the witnesses are computed, not asserted
witnessZ : solve1218 .fst ≡ pos 9
witnessZ = refl

witnessK : solve1218 .snd .fst ≡ negsuc 2
witnessK = refl

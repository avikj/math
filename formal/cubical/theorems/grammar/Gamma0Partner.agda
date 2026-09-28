{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Gamma0Partner
--
-- The 2x2 stabilizer partner (R0033), constructively: divisibility is
-- not a predicate here but a WITNESS — the membership q | c is a choice
-- of k with c = k·q (the kuṭṭaka quotient), and the theorem consumes
-- the witness to BUILD the two-sided partner
--
--     K  =  ( ε·e   -ε·b·q )
--           ( -ε·k   ε·a   )
--
-- with H·D·K ≡ D for D = diag(d₁, q·d₁), H = (a b / k·q e),
-- det H = ε, ε² = 1.  Every entry of K is an integer by construction:
-- no division appears anywhere.  Proofs are ring-solver regroupings
-- plus exactly two hypothesis rewrites (det, unimodularity).
--
-- Python finite shadow: chk gamma0-stabilizer in
-- machinery/core_knowledge.py (absent from this repository) (the iff, on windows); this module is
-- the forward direction over ALL of ℤ.  The converse (integrality of
------------------------------------------------------------------------

module Gamma0Partner where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open CommRingStr (ℤCommRing .snd)

R : Type
R = fst ℤCommRing

M : Type
M = R × R × R × R

mul : M → M → M
mul (a , b , c , e) (a' , b' , c' , e') =
  ( a · a' + b · c' , a · b' + b · e'
  , c · a' + e · c' , c · b' + e · e' )

dia : R → R → M
dia x y = (x , 0r , 0r , y)

-- solver lemmas: pure polynomial regroupings over ℤ ------------------

reg11 : (a b e d1 q k ε : R)
      → (a · d1 + b · 0r) · (ε · e)
        + (a · 0r + b · (q · d1)) · (- (ε · k))
        ≡ (ε · (a · e - b · (k · q))) · d1
reg11 _ _ _ _ _ _ _ = solve! ℤCommRing

reg12 : (a b d1 q ε : R)
      → (a · d1 + b · 0r) · (- (ε · (b · q)))
        + (a · 0r + b · (q · d1)) · (ε · a)
        ≡ 0r
reg12 _ _ _ _ _ = solve! ℤCommRing

reg21 : (e d1 q k ε : R)
      → ((k · q) · d1 + e · 0r) · (ε · e)
        + ((k · q) · 0r + e · (q · d1)) · (- (ε · k))
        ≡ 0r
reg21 _ _ _ _ _ = solve! ℤCommRing

reg22 : (a b e d1 q k ε : R)
      → ((k · q) · d1 + e · 0r) · (- (ε · (b · q)))
        + ((k · q) · 0r + e · (q · d1)) · (ε · a)
        ≡ (ε · (a · e - b · (k · q))) · (q · d1)
reg22 _ _ _ _ _ _ _ = solve! ℤCommRing

oneL : (x : R) → 1r · x ≡ x
oneL _ = solve! ℤCommRing

-- the theorem ---------------------------------------------------------

module _ (a b e d1 q k ε : R)
         (hdet : a · e - b · (k · q) ≡ ε)
         (hε : ε · ε ≡ 1r) where

  H D K : M
  H = (a , b , k · q , e)
  D = dia d1 (q · d1)
  K = (ε · e , - (ε · (b · q)) , - (ε · k) , ε · a)

  p11 : (a · d1 + b · 0r) · (ε · e)
        + (a · 0r + b · (q · d1)) · (- (ε · k)) ≡ d1
  p11 = reg11 a b e d1 q k ε
        ∙ cong (λ x → (ε · x) · d1) hdet
        ∙ cong (_· d1) hε
        ∙ oneL d1

  p12 : (a · d1 + b · 0r) · (- (ε · (b · q)))
        + (a · 0r + b · (q · d1)) · (ε · a) ≡ 0r
  p12 = reg12 a b d1 q ε

  p21 : ((k · q) · d1 + e · 0r) · (ε · e)
        + ((k · q) · 0r + e · (q · d1)) · (- (ε · k)) ≡ 0r
  p21 = reg21 e d1 q k ε

  p22 : ((k · q) · d1 + e · 0r) · (- (ε · (b · q)))
        + ((k · q) · 0r + e · (q · d1)) · (ε · a) ≡ q · d1
  p22 = reg22 a b e d1 q k ε
        ∙ cong (λ x → (ε · x) · (q · d1)) hdet
        ∙ cong (_· (q · d1)) hε
        ∙ oneL (q · d1)

  -- the partner stabilizes: H · D · K ≡ D, over all of ℤ, no windows
  stab : mul (mul H D) K ≡ D
  stab i = (p11 i , p12 i , p21 i , p22 i)

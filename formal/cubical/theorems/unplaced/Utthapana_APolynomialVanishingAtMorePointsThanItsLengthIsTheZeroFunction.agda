{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- उत्थापन — evaluation, the raising of an expression to its value at a
-- point (the term is Bhskara II's, Bjagaita (1150), for substituting a
-- value and computing; the theorem below is stated for the runtime's G7
-- gate).
--
-- crystallize/install.py (absent from this repository) G7 decides a polynomial
-- identity "by exact evaluation on an integer grid whose size is a
-- complete bound for the degree" — the completeness of that grid is the
-- gate's license.  Its univariate core,
-- checked here over ℤ:
--
--     a polynomial with MORE DISTINCT ROOTS THAN COEFFICIENTS is the
--     zero function.
--
-- Proof: the Horner quotient.  quot a p is synthetic division of p by
-- (x − a); the factor identity  p(x) − p(a) ≡ (x − a)·(quot a p)(x)  is
-- one induction whose step is pure ring algebra; a root at a plus a root
-- at b ≠ a forces (b−a)·q(b) ≡ 0, and ℤ is an integral domain
-- (isIntegralℤ), so the quotient inherits the remaining roots; lengths
-- drop by one; induction on the point list closes it.
--
-- CONTENTS:
--   §1  evalP, quot, and the factor identity.
--   §2  roots descend to the quotient (integral domain step).
--   §3  grid : length p ≤ length pts, pts distinct, p vanishing on pts
--       ⟹ evalP p x ≡ 0 for EVERY x.
------------------------------------------------------------------------

module Utthapana_APolynomialVanishingAtMorePointsThanItsLengthIsTheZeroFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ; pos; _+_; -_; _·_; _-_)
open import Cubical.Data.Int.Properties using (isIntegralℤ; -Cancel; -≡0)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_≤_; pred-≤-pred; ¬-<-zero; zero-≤; suc-≤-suc)
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

------------------------------------------------------------------------
-- §1 · polynomials as little-endian coefficient lists; Horner evaluation;
-- the Horner quotient by (x − a).
Poly : Type
Poly = List ℤ

evalP : Poly → ℤ → ℤ
evalP []       x = pos 0
evalP (c ∷ cs) x = c + x · evalP cs x

-- synthetic division by (x − a): drops one coefficient.
quot : ℤ → Poly → Poly
quot a []           = []
quot a (c ∷ [])     = []
quot a (c ∷ d ∷ ds) = evalP (d ∷ ds) a ∷ quot a (d ∷ ds)

private
  -- the inductive step of the factor identity, constants generalized so
  -- the solver meets only variables.
  key : (c x a X A Q : ℤ) → X - A ≡ (x - a) · Q
      → (c + x · X) - (c + a · A) ≡ (x - a) · (A + x · Q)
  key c x a X A Q h =
    step1 ∙ cong (λ w → x · w + (x - a) · A) h ∙ step3
    where
    step1 : (c + x · X) - (c + a · A) ≡ x · (X - A) + (x - a) · A
    step1 = solve! ℤCommRing
    step3 : x · ((x - a) · Q) + (x - a) · A ≡ (x - a) · (A + x · Q)
    step3 = solve! ℤCommRing

-- THE FACTOR IDENTITY: p(x) − p(a) ≡ (x − a) · (quot a p)(x).
factor : (p : Poly) (a x : ℤ)
       → evalP p x - evalP p a ≡ (x - a) · evalP (quot a p) x
factor []           a x = solve! ℤCommRing
factor (c ∷ [])     a x = solve! ℤCommRing
factor (c ∷ d ∷ ds) a x =
  key c x a (evalP (d ∷ ds) x) (evalP (d ∷ ds) a)
      (evalP (quot a (d ∷ ds)) x) (factor (d ∷ ds) a x)

-- a root at a rewrites p as its factored form everywhere.
private
  minusZero : (z : ℤ) → z - pos 0 ≡ z
  minusZero z = solve! ℤCommRing

vanish-shift : (p : Poly) (a : ℤ) → evalP p a ≡ pos 0
             → (x : ℤ) → evalP p x ≡ (x - a) · evalP (quot a p) x
vanish-shift p a va x =
  sym (cong (λ w → evalP p x - w) va ∙ minusZero (evalP p x)) ∙ factor p a x

------------------------------------------------------------------------
-- §2 · ROOTS DESCEND TO THE QUOTIENT: a further root b ≠ a of p is a
-- root of quot a p — the integral-domain step.
root-quot : (p : Poly) (a b : ℤ)
          → evalP p a ≡ pos 0 → evalP p b ≡ pos 0 → ¬ b ≡ a
          → evalP (quot a p) b ≡ pos 0
root-quot p a b va vb neq =
  isIntegralℤ (b - a) (evalP (quot a p) b)
    (sym (vanish-shift p a va b) ∙ vb)
    (λ e → neq (-≡0 b a e))

------------------------------------------------------------------------
-- §3 · THE GRID.  All and Distinct, then the theorem by induction on the
-- point list (the quotient is not a subterm of p, so the points carry
-- the recursion; length p ≤ length pts shrinks with them).
data All (P : ℤ → Type) : List ℤ → Type where
  nil  : All P []
  cons : {b : ℤ} {bs : List ℤ} → P b → All P bs → All P (b ∷ bs)

Distinct : List ℤ → Type
Distinct []       = Unit
Distinct (a ∷ as) = All (λ b → ¬ b ≡ a) as × Distinct as

private
  -- push both vanishing and distinctness through the quotient at once.
  descendAll : (p : Poly) (a : ℤ) → evalP p a ≡ pos 0
             → (bs : List ℤ)
             → All (λ b → evalP p b ≡ pos 0) bs
             → All (λ b → ¬ b ≡ a) bs
             → All (λ b → evalP (quot a p) b ≡ pos 0) bs
  descendAll p a va []       nil          nil          = nil
  descendAll p a va (b ∷ bs) (cons vb vs) (cons nb ns) =
    cons (root-quot p a b va vb nb) (descendAll p a va bs vs ns)

  -- the quotient's length: one less than p's (stated as ≤ the tail).
  lenQuot : (a c : ℤ) (cs : Poly) (n : ℕ)
          → length cs ≤ n → length (quot a (c ∷ cs)) ≤ n
  lenQuot a c []       n h = zero-≤
  lenQuot a c (d ∷ ds) n h = subst (_≤ n) (sym lem) h
    where
    lem : length (quot a (c ∷ d ∷ ds)) ≡ length (d ∷ ds)
    lem i = suc (len≡ ds d i)
      where
      len≡ : (ds : Poly) (d : ℤ)
           → length (quot a (d ∷ ds)) ≡ length ds
      len≡ []       d = refl
      len≡ (e ∷ es) d = cong suc (len≡ es e)

  mulZeroR : (z : ℤ) → z · pos 0 ≡ pos 0
  mulZeroR z = solve! ℤCommRing

-- THE THEOREM: more distinct roots than coefficients ⟹ zero function.
grid : (pts : List ℤ) (p : Poly)
     → length p ≤ length pts
     → Distinct pts
     → All (λ b → evalP p b ≡ pos 0) pts
     → (x : ℤ) → evalP p x ≡ pos 0
grid []       []       _   _    _   x = refl
grid []       (c ∷ cs) len _    _   x = Empty.rec (¬-<-zero len)
grid (a ∷ as) []       _   _    _   x = refl
grid (a ∷ as) (c ∷ cs) len dist (cons va vs) x =
  vanish-shift (c ∷ cs) a va x
  ∙ cong ((x - a) ·_) (grid as (quot a (c ∷ cs))
      (lenQuot a c cs (length as) (pred-≤-pred len))
      (snd dist)
      (descendAll (c ∷ cs) a va as vs (fst dist))
      x)
  ∙ mulZeroR (x - a)

------------------------------------------------------------------------
-- §4 · THE TWO-SIDED FORM — the scope note's debt, paid.  The
-- coefficientwise difference, its evaluation law, and the agreement
-- theorem: two polynomials agreeing at more distinct points than either
-- has coefficients agree at EVERY point.  This is G7's actual univariate
-- statement: the grid decides the identity.
negP : Poly → Poly
negP []       = []
negP (c ∷ cs) = (- c) ∷ negP cs

psub : Poly → Poly → Poly
psub p        []       = p
psub []       (d ∷ ds) = (- d) ∷ negP ds
psub (c ∷ cs) (d ∷ ds) = (c - d) ∷ psub cs ds

private
  negStep : (d x E : ℤ) → (- d) + x · (- E) ≡ pos 0 - (d + x · E)
  negStep d x E = solve! ℤCommRing

  subStep : (c d x X D S : ℤ) → S ≡ X - D
          → (c - d) + x · S ≡ (c + x · X) - (d + x · D)
  subStep c d x X D S h =
    cong (λ w → (c - d) + x · w) h ∙ lem
    where
    lem : (c - d) + x · (X - D) ≡ (c + x · X) - (d + x · D)
    lem = solve! ℤCommRing

  eval-negP : (q : Poly) (x : ℤ) → evalP (negP q) x ≡ pos 0 - evalP q x
  eval-negP []       x = solve! ℤCommRing
  eval-negP (d ∷ ds) x =
    cong (λ w → (- d) + x · w) (eval-negP ds x)
    ∙ lem
    where
    lem : (- d) + x · (pos 0 - evalP ds x)
        ≡ pos 0 - (d + x · evalP ds x)
    lem = solve! ℤCommRing

eval-psub : (p q : Poly) (x : ℤ)
          → evalP (psub p q) x ≡ evalP p x - evalP q x
eval-psub p        []       x = sym (minusZero (evalP p x))
eval-psub []       (d ∷ ds) x =
  cong (λ w → (- d) + x · w) (eval-negP ds x) ∙ lem
  where
  lem : (- d) + x · (pos 0 - evalP ds x)
      ≡ pos 0 - (d + x · evalP ds x)
  lem = solve! ℤCommRing
eval-psub (c ∷ cs) (d ∷ ds) x =
  subStep c d x (evalP cs x) (evalP ds x)
          (evalP (psub cs ds) x) (eval-psub cs ds x)

private
  lenNeg : (q : Poly) → length (negP q) ≡ length q
  lenNeg []       = refl
  lenNeg (d ∷ ds) = cong suc (lenNeg ds)

  lenSub : (p q : Poly) (n : ℕ)
         → length p ≤ n → length q ≤ n → length (psub p q) ≤ n
  lenSub p        []       n hp hq = hp
  lenSub []       (d ∷ ds) n hp hq =
    subst (_≤ n) (sym (cong suc (lenNeg ds))) hq
  lenSub (c ∷ cs) (d ∷ ds) zero    hp hq = Empty.rec (¬-<-zero hp)
  lenSub (c ∷ cs) (d ∷ ds) (suc m) hp hq =
    suc-≤-suc (lenSub cs ds m (pred-≤-pred hp) (pred-≤-pred hq))

  agreeVanish : (p q : Poly) (bs : List ℤ)
              → All (λ b → evalP p b ≡ evalP q b) bs
              → All (λ b → evalP (psub p q) b ≡ pos 0) bs
  agreeVanish p q []       nil          = nil
  agreeVanish p q (b ∷ bs) (cons e es)  =
    cons (eval-psub p q b ∙ cong (λ w → w - evalP q b) e ∙ -Cancel (evalP q b))
         (agreeVanish p q bs es)

-- THE AGREEMENT THEOREM: the grid decides the identity.
agree : (pts : List ℤ) (p q : Poly)
      → length p ≤ length pts → length q ≤ length pts
      → Distinct pts
      → All (λ b → evalP p b ≡ evalP q b) pts
      → (x : ℤ) → evalP p x ≡ evalP q x
agree pts p q hp hq dist ag x =
  -≡0 (evalP p x) (evalP q x)
    (sym (eval-psub p q x)
     ∙ grid pts (psub p q) (lenSub p q (length pts) hp hq)
         dist (agreeVanish p q pts ag) x)

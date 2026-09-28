{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- KuttakaValli
--
-- The vall of ryabhaa's pulverizer as SYNTAX, its replay as
-- evaluation, and the two structural laws of the trace, typed:
--
--   replayHom   replay (xs ++ ys) ≡ replay xs · replay ys
--               — concatenating traces IS multiplying their payloads;
--                 the vall is a monoid morphism from lists of
--                 quotients to 2×2 matrices.  (R0035's "the trace
--                 composes", as a theorem about syntax.)
--
--   detReplay   det (replay v) ≡ sgn v      (sgn = (-1)^length)
--               — the sign of a replay is the parity of the vallī;
--                 each division step L q = (q 1 / 1 0) reverses
--                 orientation exactly once.
--
-- The vall is a term, replay is an evaluator, and the laws are
-- structural inductions whose entry obligations the ring solver
-- discharges — the trace calculus of the corpus, native in the
-- constructive lane.
------------------------------------------------------------------------

module KuttakaValli where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (predℤ ; sucℤ)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open import Gamma0Partner using (R ; M ; mul ; dia)
open import M2Unimodular using (det ; idm ; detMul)
open import Gamma0Freeness using (mulAssoc)

open CommRingStr (ℤCommRing .snd)

-- one division step of the pulverizer, as a matrix ---------------------

L : R → M
L q = (q , 1r , 1r , 0r)

-- the vall is a list of quotients; replay evaluates it ---------------

Valli : Type
Valli = List R

replay : Valli → M
replay [] = idm
replay (q ∷ v) = mul (L q) (replay v)

-- law 1: concatenation is multiplication ------------------------------

private
  zA : (c : R) → 0r + c ≡ c
  zA _ = solve! ℤCommRing

mulIdL : (x : M) → mul idm x ≡ x
mulIdL (a , b , c , e) i = ( a , b , zA c i , zA e i )

replayHom : (xs ys : Valli)
          → replay (xs ++ ys) ≡ mul (replay xs) (replay ys)
replayHom [] ys = sym (mulIdL (replay ys))
replayHom (q ∷ xs) ys =
  cong (mul (L q)) (replayHom xs ys)
  ∙ sym (mulAssoc (L q) (replay xs) (replay ys))

-- law 2: the sign of a replay is the parity of the vall --------------

sgn : Valli → R
sgn [] = 1r
sgn (q ∷ v) = (- 1r) · sgn v

private
  mul0 : (q : R) → q · 0r ≡ 0r
  mul0 q = ·Comm q 0r

detL : (q : R) → det (L q) ≡ - 1r
detL q = cong predℤ (mul0 q)

detReplay : (v : Valli) → det (replay v) ≡ sgn v
detReplay [] = refl
detReplay (q ∷ v) =
  detMul (L q) (replay v)
  ∙ cong₂ _·_ (detL q) (detReplay v)

-- law 3: appending a quotient IS the kuaka recurrence ---------------
--
--   p_n = p_{n-1} · q_n + p_{n-2}
--
-- the classical convergent computation is the right-append case of
-- the trace law: new first column = old first column · q + old
-- second column; new second column = old first column.

step : R → M → M
step q (p , p' , r , r') = (p · q + p' , p , r · q + r' , r)

private
  idmR : (q : R) → mul (L q) idm ≡ L q
  idmR q i = ( ·IdR q i , cong sucℤ (·Comm q 0r) i , 1r , 0r )

  stepLaw : (q : R) (x : M) → mul x (L q) ≡ step q x
  stepLaw q (p , p' , r , r') i =
    ( e1 i , e2 i , e3 i , e4 i )
    where
    e1 : p · q + p' · 1r ≡ p · q + p'
    e1 = cong ((p · q) +_) (·IdR p')
    e2 : p · 1r + p' · 0r ≡ p
    e2 = cong₂ _+_ (·IdR p) (·Comm p' 0r)
    e3 : r · q + r' · 1r ≡ r · q + r'
    e3 = cong ((r · q) +_) (·IdR r')
    e4 : r · 1r + r' · 0r ≡ r
    e4 = cong₂ _+_ (·IdR r) (·Comm r' 0r)

convergent : (xs : Valli) (q : R)
           → replay (xs ++ (q ∷ [])) ≡ step q (replay xs)
convergent xs q =
  replayHom xs (q ∷ [])
  ∙ cong (mul (replay xs)) (idmR q)
  ∙ stepLaw q (replay xs)

-- law 4: macro soundness (for the trace-block compiler) ----
--
-- A repeated block replays to the power of its compiled matrix, so
-- "compile b once, invoke r times" is CERTIFIED equal to the full
-- expansion — the typed foundation under KUTTAKA_TRACE_MACRO.md (absent from this repository),
-- whose exact gain law (m-1)(r-1) > 1 prices when to install it.

rep : ℕ → Valli → Valli
rep zero b = []
rep (suc n) b = b ++ rep n b

pow : ℕ → M → M
pow zero x = idm
pow (suc n) x = mul x (pow n x)

macroSound : (n : ℕ) (b : Valli) → replay (rep n b) ≡ pow n (replay b)
macroSound zero b = refl
macroSound (suc n) b =
  replayHom b (rep n b)
  ∙ cong (mul (replay b)) (macroSound n b)

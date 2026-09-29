{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TransportPrice
--
-- In `Anekanta`, collapse is settled (agreement permits it, plurality
-- blocks it); the question about two nayas is what a transport between
-- them COSTS.
--
-- It has an answer, and the answer is that the question is smaller than
-- it looks.
--
-- ────────────────────────────────────────────────────────────────────
-- THE THEOREM
--
-- Suppose a cost `c p q` on transports, subject only to the one thing any
-- cost must satisfy — that going by way of a third standpoint costs the
-- sum:
--
--     c p q + c q r ≡ c p r.
--
-- Then, fixing any base standpoint b,
--
--     cocycle→coboundary :  c p q ≡ c b q − c b p.
--
-- **Every additive transport price is the difference of a potential.**
-- There is no path-dependence to discover, no cheapest route between two
-- standpoints, no holonomy around a loop (`loop-is-free`).  All the
-- content is in the potential — a number attached to each standpoint on
-- its own — and choosing well means choosing an endpoint, never a route.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THE POTENTIAL IS
--
-- `Laghava` supplies it and also says what it cannot be:
--
--   * `size` is a potential: the price of a reformulation is the change
--     in लाघव (`laghava-price` below);
--   * `laghava-is-not-semantic` proves no function of the DENOTATION
--     computes `size`.
--
-- Together: the price of a transport between two nayas is real, is
-- path-independent, and is invisible to every semantic invariant — so a
-- corpus that checks only denotations has no access to it at all, while
-- a grammarian working on presentations has complete access.  That is the
-- whole of Pini's lghava discipline, in two theorems.
--
-- ────────────────────────────────────────────────────────────────────
-- AND WHY "PRICE" IS THE WRONG WORD FOR IT
--
-- The potential is not a fee anyone pays.  It is a coordinate on
-- presentations, and "the price of getting from p to q" is nothing but
-- the difference of two coordinates.  Nothing is spent; a reformulation
-- gains what the difference says and loses nothing, because by
-- `Apavada.Reformulation` the denotation is untouched.  The scarcity
-- reading of this quantity was withdrawn in
-- `notes/THE_BARRIER_BELONGS_TO_THE_LINE.md` (absent from this repository)
-- §24 and is withdrawn here too; the name `TransportPrice` is kept only
-- because the thread that asked the question used it, and
-- `loop-is-free` is the theorem that
-- makes the objection precise.
------------------------------------------------------------------------

module TransportPrice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos ; _+_ ; _-_ ; -_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

open import Laghava using (Expr ; size ; eval)

private
  variable
    ℓ : Level

private
  shift : (x y z : ℤ) → x + y ≡ z → y ≡ z - x
  shift x y z h = sym (lem x y) ∙ cong (_- x) h
    where
    lem : (a b : ℤ) → (a + b) - a ≡ b
    lem a b = solve! ℤCommRing

  idem→zero : (x : ℤ) → x + x ≡ x → x ≡ pos 0
  idem→zero x h = sym (lem x) ∙ cong (_- x) h ∙ self x
    where
    lem  : (a : ℤ) → (a + a) - a ≡ a
    lem a = solve! ℤCommRing
    self : (a : ℤ) → a - a ≡ pos 0
    self a = solve! ℤCommRing

------------------------------------------------------------------------
-- 1.  Additive costs on any type of standpoints
------------------------------------------------------------------------

Additive : {X : Type ℓ} → (X → X → ℤ) → Type ℓ
Additive {X = X} c = (p q r : X) → c p q + c q r ≡ c p r

module _ {X : Type ℓ} (c : X → X → ℤ) (add : Additive c) where

  -- staying put is free, and this is forced, not assumed
  self-is-free : (p : X) → c p p ≡ pos 0
  self-is-free p = idem→zero (c p p) (add p p p)

  -- THE THEOREM.  Every additive cost is the difference of a potential.
  cocycle→coboundary : (b p q : X) → c p q ≡ (c b q) - (c b p)
  cocycle→coboundary b p q = shift (c b p) (c p q) (c b q) (add b p q)

  -- so a round trip costs nothing, whatever route it takes
  loop-is-free : (p q : X) → c p q + c q p ≡ pos 0
  loop-is-free p q = add p q p ∙ self-is-free p

  -- and the reverse transport is the negation of the forward one
  reverse : (p q : X) → c q p ≡ - (c p q)
  reverse p q = shift (c p q) (c q p) (pos 0) (loop-is-free p q) ∙ neg (c p q)
    where
    neg : (a : ℤ) → (pos 0) - a ≡ - a
    neg a = solve! ℤCommRing

------------------------------------------------------------------------
-- 2.  The potential, when the standpoints are presentations
------------------------------------------------------------------------

toℤ : Expr → ℤ
toℤ e = pos (size e)

laghavaPrice : Expr → Expr → ℤ
laghavaPrice p q = (toℤ q) - (toℤ p)

laghava-additive : Additive laghavaPrice
laghava-additive p q r = tri (toℤ p) (toℤ q) (toℤ r)
  where
  tri : (a b d : ℤ) → (b - a) + (d - b) ≡ d - a
  tri a b d = solve! ℤCommRing

-- so all four laws above hold of it, with no further work
laghava-loop-free : (p q : Expr) → laghavaPrice p q + laghavaPrice q p ≡ pos 0
laghava-loop-free = loop-is-free laghavaPrice laghava-additive

------------------------------------------------------------------------
-- 3.  The answer, stated once.
--
-- What does a transport between two nayas cost?  Whatever the potential
-- says, and nothing else.  Additivity alone kills every path structure:
-- no route matters, no loop accumulates, and the reverse is the negation.
-- The question "what is the price of this transport" is therefore not a
-- question about the transport at all — it is a question about the two
-- endpoints, asked in a roundabout way.
--
-- And by `Laghava.laghava-is-not-semantic`, the potential this corpus
-- actually cares about is not a function of the denotation.  So the
-- quantity is real, is entirely determined by where you are rather than
-- how you came, and is invisible to every check this repository performs.
------------------------------------------------------------------------

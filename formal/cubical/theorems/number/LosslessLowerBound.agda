{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- LosslessLowerBound
--
-- ────────────────────────────────────────────────────────────────────
-- THE STATEMENT
--
--     lossless-needs-room :
--       (n : ℕ) (Y : FinSet ℓ) (obs : Fin (suc n) → Y .fst)
--       → Injective obs → suc n ≤ card Y
--
-- Any lossless observation of the inputs 0 … n — ANY, over every scheme,
-- not just residues and not just the walk's — needs at least n+1
-- distinguishable outcomes.  With the walk's outcome space being the
-- residues mod lcm(S), of which there are exactly lcm(S), this is what
-- turns the CRT criterion `lcm(S) > n` from a description of the walk
-- into a bound on every machine.
--
-- ────────────────────────────────────────────────────────────────────
-- PRIOR ART
--
-- `Cubical.Data.FinSet.Cardinality.card↪Inequality'` is the pigeonhole in
-- exactly the needed direction, and `formal/cubical/FinCardinality.agda`
-- already carries CRT (`crtEquiv`, `crtInj`) and the equal-cardinality
-- counting principle for this repository.
--
-- ────────────────────────────────────────────────────────────────────
-- AND WHY THIS SHAPE MATTERS TO THE DEFLATIONARY THREAD
--
-- `DeflationaryTest` §10 shows this lane cannot express a barrier: every
-- absence is stable, every dichotomy is a decision, and `¬ (Dec A)` is
-- contradictory.  It closes by asking what a genuine limitation would
-- have to look like instead.
--
-- This is one.  `lossless-needs-room` is POSITIVE, is quantified over
-- every observation scheme, and bounds them all.  It says "no machine of
-- this kind does better", which is the content people reach for when they
-- write "barrier" — and it is available, expressible, and provable here,
-- because it quantifies over a class rather than negating a proposition.
--
-- A limitation you can state is a Π over machines.  A barrier you cannot
-- state is a ¬ over propositions.  The corpus has been writing the second
------------------------------------------------------------------------

module LosslessLowerBound where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding using (injEmbedding)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.FinSet using (FinSet ; card ; isFinSet→isSet)
open import Cubical.Data.FinSet.Cardinality using (card↪Inequality')
open import FinCardinality using (FinSetFin ; cardFinSetFin)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  Losslessness, as this corpus means it
--
-- The observation separates the inputs it is run on.  This is exactly
-- `WALK_FORCING_LAW.md` (absent from this repository)'s "the observation n ↦ (n mod m) is injective on
-- the walked prefix".
------------------------------------------------------------------------

Injective : {A : Type ℓ} {B : Type ℓ} → (A → B) → Type ℓ
Injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

-- the inputs 0 … n, as a finite set of size n+1
Inputs : ℕ → FinSet ℓ-zero
Inputs n = FinSetFin (suc n)

------------------------------------------------------------------------
-- 2.  THE LOWER BOUND.  Uniform over every observation scheme.
------------------------------------------------------------------------

lossless-needs-room :
  (n : ℕ) (Y : FinSet ℓ-zero) (obs : Fin (suc n) → Y .fst)
  → Injective obs
  → card (Inputs n) ≤ card Y
lossless-needs-room n Y obs inj =
  card↪Inequality' (Inputs n) Y obs
    (injEmbedding (isFinSet→isSet (Y .snd)) inj)

------------------------------------------------------------------------
-- 3.  What it says about the walk, in words the walk uses.
--
-- The walk's outcome space at frontier k is the residues modulo cap k,
-- of which there are exactly cap k.  So by §2 any lossless walk over the
-- prefix [0, n] has cap k ≥ n+1 — which is `WALK_FORCING_LAW.md` (absent from this repository)'s
-- invariant `lcm(S) > n`, now derived as a bound on every scheme rather
-- than stated as a property of one.
--
-- `TheGapWasAUnitsError` then checks the walk attains it with no slack at
-- frontiers 4, 5, 7, 8: state 840, last input 839, at frontier 8.  Bound
-- and attainment, both terms, on both sides of the word "optimal".
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 5.  RELATION TO `WalkCapacity` — they are complements rather than duplicates.
--
-- `WalkCapacity` proves the capacity theorem: any lossless
-- sensor family whose addresses are all ≤ k has lcm DIVIDING lcm(1..k),
-- and the bound is attained.  That bounds the state's MODULUS from above,
-- by two universal properties and no arithmetic.
--
-- This module bounds the OUTCOME COUNT from below, by pigeonhole.
--
-- The two together are what "optimal" needs and neither is the other:
--
--   `WalkCapacity`        no admissible family's modulus exceeds cap k
--   here                  no lossless scheme has fewer than n+1 outcomes
--   `WalkObservationCount` and the walk's scheme has exactly cap k of them
--
-- `WalkCapacity`'s design note is also worth reading against
-- `FrontierList`: it states capacity by universal property BECAUSE this
-- lane has no LCM module, and calls that absence an improvement.  The
-- `frontierList` construction is the deliberate complement — a concrete
-- residue space where that module deliberately avoided one — and neither
-- supersedes the other.
------------------------------------------------------------------------

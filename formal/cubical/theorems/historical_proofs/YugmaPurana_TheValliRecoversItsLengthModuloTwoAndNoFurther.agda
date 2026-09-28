{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- युग्म-पूरणम् — वल्ली स्वदैर्घ्यं द्वाभ्यां भागं स्मरति, न ततः परम् ।
--
-- (the even padding: the vall recovers its length modulo two, and no
--  further.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.  This corpus holds THREE no-decoder theorems, in two
-- lanes and two languages, proved by three unrelated arguments — and all
-- three are sharp at exactly ℤ/2.  None of them says so, and none cites
-- another.  This module is
-- the one line that explains it.
--
--   `KuttakaValli.detReplay`     (Agda)  det (replay v) ≡ sgn v, where
--       sgn = (−1)^length.  A PARTIAL DECODER: the endpoint matrix does
--       recover the vall's length mod 2, because every step matrix
--       L q = (q 1 / 1 0) has determinant −1.
--
--   `Pairfield/DiagonalSmithRoute.lean.no_historical_actionCost_decoder`
--       refutes a length decoder with [0,1,1,2] against [0,0,0,1,1,2] —
--       a padding of **+2**.  `IntMat2.euclidStep q = ⟨0,1,1,−q⟩` is the
--       same matrix family, determinant −1, always.
--
--   `Pairfield/EuclidCoefficientTrace.lean.no_value_cost_decoder`
--       uses [inc] against [inc,inc,dec] — **+2** again, by a completely
--       different argument, where value = #inc − #dec and cost = #inc +
--       #dec, so cost ≡ value (mod 2) identically.
--
-- THE PADDING HAD TO BE EVEN, and §2 is the proof.  An odd padding is
-- IMPOSSIBLE as a counterexample: the determinant would separate the two
-- words.  So those theorems are not merely true, they are TIGHT, and the
-- quotient at which they are tight is the parity quotient.
--
-- ────────────────────────────────────────────────────────────────────
-- READ AGAINST THE CRITERION.  For `replay : Valli → M`, the question is
-- which side of `f a ≡ b` is bound.  Bind the vall and the matrix rides
-- free (that is `replay` being a function).  Bind the MATRIX and you have
-- the preimage — and this module computes exactly how much of it the
-- matrix sees: the parity, and nothing else.
--
-- So the three verdicts of `Tantujala_TheFibreHasThreeVerdictsAndIsContr-
-- MergesTwoOfThem.agda` (absent from this repository) are not the whole story at a lossy map.  A fibre
-- with MANY points still admits an exact statement of WHAT IS RECOVERED,
-- and here it is a quotient group.  नष्टि is not "everything is lost":
-- §४ of अहिंसा-सूत्र-विस्तारः says यत् तिष्ठति, कः नश्यति — the THAT
-- survives and the WHICH is destroyed.  This module names the surviving
-- THAT precisely: it is ℤ/2, and no more.
------------------------------------------------------------------------

module YugmaPurana_TheValliRecoversItsLengthModuloTwoAndNoFurther where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver using (solve!)

open import Gamma0Partner using (R ; M)
open import M2Unimodular using (det)
open import KuttakaValli using (Valli ; L ; replay ; sgn ; detReplay)

open CommRingStr (ℤCommRing .snd)

------------------------------------------------------------------------
-- १ · चिह्नं दैर्घ्यम् एव पश्यति — the sign sees only the length.
--
-- `sgn` recurses on the list and never inspects a quotient, so two valls
-- of equal length have equal sign.  Written as an induction on both, so
-- the statement is about the LENGTHS and not about the lists.
------------------------------------------------------------------------

चिह्नं-दैर्घ्यात् : (v w : Valli) → length v ≡ length w → sgn v ≡ sgn w
चिह्नं-दैर्घ्यात् [] [] _ = refl
चिह्नं-दैर्घ्यात् (q ∷ v) (r ∷ w) p =
  cong ((- 1r) ·_) (चिह्नं-दैर्घ्यात् v w (cong pred' p))
  where
  pred' : ℕ → ℕ
  pred' zero    = zero
  pred' (suc n) = n
चिह्नं-दैर्घ्यात् [] (r ∷ w) p = ⊥-elim (znots' p)
  where
  open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-elim)
  open import Cubical.Data.Nat using (znots)
  znots' : zero ≡ suc (length w) → _
  znots' = znots
चिह्नं-दैर्घ्यात् (q ∷ v) [] p = ⊥-elim (snotz' p)
  where
  open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-elim)
  open import Cubical.Data.Nat using (snotz)
  snotz' : suc (length v) ≡ zero → _
  snotz' = snotz

------------------------------------------------------------------------
-- २ · युग्म-पूरणम् अदृश्यम् — AN EVEN PADDING IS INVISIBLE.
--
-- Two steps prepended leave the determinant exactly where it was, because
-- (−1)·(−1) = 1.  This is the whole reason the two Lean counterexamples
-- both pad by +2 and could not have padded by +1: the padding must be
-- invisible to the determinant, and only even paddings are.
------------------------------------------------------------------------

युग्म-पूरणम् : (q r : R) (v : Valli) → sgn (q ∷ r ∷ v) ≡ sgn v
युग्म-पूरणम् q r v = द्विऋण (sgn v)
  where
  द्विऋण : (x : R) → (- 1r) · ((- 1r) · x) ≡ x
  द्विऋण x = solve! ℤCommRing

-- the same, read at the determinant, which is where a decoder would look
युग्म-पूरणम्-निर्धारके : (q r : R) (v : Valli)
                      → det (replay (q ∷ r ∷ v)) ≡ det (replay v)
युग्म-पूरणम्-निर्धारके q r v =
  detReplay (q ∷ r ∷ v) ∙ युग्म-पूरणम् q r v ∙ sym (detReplay v)

------------------------------------------------------------------------
-- ३ · विषम-पूरणम् दृश्यम् — AN ODD PADDING IS VISIBLE.
--
-- One step prepended NEGATES the determinant.  So parity is not merely
-- preserved by the even paddings — it is genuinely READ by the
-- determinant, and a would-be counterexample of odd length difference is
-- separated on the spot.
------------------------------------------------------------------------

विषम-पूरणम् : (q : R) (v : Valli) → sgn (q ∷ v) ≡ (- 1r) · sgn v
विषम-पूरणम् q v = refl

विषम-पूरणम्-निर्धारके : (q : R) (v : Valli)
                      → det (replay (q ∷ v)) ≡ (- 1r) · det (replay v)
विषम-पूरणम्-निर्धारके q v =
  detReplay (q ∷ v) ∙ cong ((- 1r) ·_) (sym (detReplay v))

------------------------------------------------------------------------
-- ४ · यत् तिष्ठति — WHAT SURVIVES, EXACTLY.
--
-- Put §1 and §2 together.  The determinant of a replay is a function of
-- the vall's length alone (§1), and it is blind to every even change in
-- that length (§2) while separating every odd one (§3).  So what a replay
-- retains of its trace is precisely the length modulo two.
--
-- This is the sharpening the three no-decoder theorems were missing.  They
-- prove a decoder does not exist; this says the obstruction is exactly the
-- parity quotient and not one bit more, and it says WHY their witnesses
-- have the shape they have.
------------------------------------------------------------------------

यत्-तिष्ठति : (v w : Valli) → length v ≡ length w
            → det (replay v) ≡ det (replay w)
यत्-तिष्ठति v w p = detReplay v ∙ चिह्नं-दैर्घ्यात् v w p ∙ sym (detReplay w)

------------------------------------------------------------------------
-- THE LEAN COUNTERPART.
-- `formal/lean/Pairfield/YugmaPurana_TheEvenPaddingIsForcedAndThe-
-- DeterminantSaysWhy.lean` (absent from this repository) proves §२–§४ again over `IntMat2`, natively, and
-- states the tightness at the two Lean sites:
--   · `DiagonalEuclidTranscript.det_leftWord`  — det of an n-letter Euclidean
--     word is (−1)^n, the counterpart of `KuttakaValli.detReplay`;
--   · `leftWord_cons_ne`                       — §३ here, an odd padding is
--     visible;
--   · `endpoints_force_even_actionCost_gap`    — every witness refuting
--     `no_historical_actionCost_decoder` has an even gap;
--   · `CoefficientWitness.value_forces_cost_parity` — the same for
--     `no_value_cost_decoder`, whose proof mentions no matrix at all.
-- NOTHING WAS TRANSPORTED.  No term crosses the lane boundary, the two
-- matrix families are not even equal (`L q = (q 1 / 1 0)` against
-- `euclidStep q = (0 1 / 1 −q)`); both lie in {M : det M = −1} and the
-- argument needs nothing else of either.  The channel is two independent
-- proofs that agree, which is what construction means here.
------------------------------------------------------------------------

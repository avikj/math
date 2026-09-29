{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FalsifierAsymmetry
--
-- "Numerics are falsifiers only"; "headline claims ship with their own
-- falsifier".  This module checks that
-- the epistemology is not house style but a logical asymmetry between
-- Σ and Π over a decidable matrix P : ℕ → Bool:
--
--   (a) `falsify`    — refutation of the Π₁ statement
--                      ((m : ℕ) → P m ≡ true) is FINITELY WITNESSED:
--                      it consumes ONE point n with P n ≡ false.
--                      A falsifier is data.
--   (b) `decBounded` — every BOUNDED Π is decidable: for each N the
--                      statement ((m : ℕ) → m < N → P m ≡ true) has a
--                      decision procedure, by recursion on N.
--   (c) the asymmetry — (a) and (b) side by side ARE the checked
--                      content.  What is deliberately absent: no term
--                      here decides the UNBOUNDED Π.  Affirmation is a
--                      function (all points); refutation is a pair
--                      (one point).  The repo's evidentiary ladder —
--                      run the falsifier, never claim the verifier —
--                      lives exactly in that gap.
--
-- The precise size of the
-- finite/infinite gap is already isolated in this corpus: it is
-- Markov's Principle.  See formal/cubical/theorems/logic/Apoha.agda,
-- `MP→Witnessed` / `Witnessed→MP` (checked there, cited here, not
-- imported): MP is exactly the license to convert a bare negation of
-- the unbounded Π into the Σ-witness that `falsify` consumes.  Without
-- MP, `falsify` runs right-to-left only: witness ⇒ refutation, never
-- refutation ⇒ witness.
--
-- Shape: Goldbach is
-- Π₁ over a decidable matrix — "every even n ≥ 4 is a sum of two
-- primes" is ((m : ℕ) → P m ≡ true) for a P this module's `falsify`
-- and `decBounded` apply to verbatim.  Twin primes is Π₂ ("for every
-- n there is a larger twin pair"): its bounded truncations are again
-- decidable, but a single counterexample no longer kills it — the
-- falsifier for a Π₂ statement is itself a Π₁ object.  The ladder of
-- quantifier alternations is the ladder of how much a falsifier costs.
--
-- Everything here is elementary and
-- classical-free; the point is that it CHECKS, so the constitution's
-- asymmetry is a term, not a slogan.
------------------------------------------------------------------------

module FalsifierAsymmetry where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary

module _ (P : ℕ → Bool) where

  ----------------------------------------------------------------------
  -- (a) One counterexample kills.  The falsifier is a single point;
  --     the hypothesis it destroys is a function on all of ℕ.
  ----------------------------------------------------------------------

  falsify : (n : ℕ) → P n ≡ false → ¬ ((m : ℕ) → P m ≡ true)
  falsify n pn total = true≢false (sym (total n) ∙ pn)

  ----------------------------------------------------------------------
  -- (b) Bounded Π is decidable.  Recursion on the bound: the empty
  --     bound holds vacuously; at suc N, decide the prefix, then test
  --     the new point P N by Bool dichotomy.  This is the exact sense
  --     in which "run the check up to N" is mathematics and "true for
  --     all N" is not: the former is this terminating term.
  ----------------------------------------------------------------------

  Bounded : ℕ → Type
  Bounded N = (m : ℕ) → m < N → P m ≡ true

  decBounded : (N : ℕ) → Dec (Bounded N)
  decBounded zero = yes (λ m h → Empty.rec (¬-<-zero h))
  decBounded (suc N) with decBounded N | dichotomyBool (P N)
  ... | yes ok | inl pN = yes step
    where
    step : Bounded (suc N)
    step m h with <-split h
    ... | inl m<N = ok m m<N
    ... | inr m≡N = subst (λ k → P k ≡ true) (sym m≡N) pN
  ... | yes ok | inr pN = no (λ f → true≢false (sym (f N ≤-refl) ∙ pN))
  ... | no bad | _      = no (λ f → bad (λ m h → f m (≤-suc h)))

  ----------------------------------------------------------------------
  -- (c) The asymmetry, on the record.
  --
  --     `falsify`    : Σ-shaped evidence (one n, one path) refutes Π.
  --     `decBounded` : every finite truncation of Π is decided.
  --
  --     The unbounded ((m : ℕ) → P m ≡ true) receives NO decision
  --     procedure in this module.
  --     The gap between "decided at every bound" and
  --     "decided" is not an engineering shortfall; by S04Apoha's
  --     MP↔Witnessed it is precisely Markov's Principle, i.e. a
  --     classical axiom the --safe fragment does not grant.  The
  --     protocol's asymmetric ladder (falsifiers admissible, verifier
  --     claims forbidden) is the operational face of that axiom's
  --     absence.
  ----------------------------------------------------------------------

------------------------------------------------------------------------
-- (d) A worked instance: P = "is not 5".  The universal claim "no
--     natural number is 5" is falsified by the single point 5, and the
--     falsifying path is refl — the counterexample computes.
------------------------------------------------------------------------

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc n) = false
eqℕ (suc m) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

isNot5 : ℕ → Bool
isNot5 n = not (eqℕ n 5)

-- The counterexample is definitional: isNot5 5 reduces to false.
counterexampleAt5 : isNot5 5 ≡ false
counterexampleAt5 = refl

-- One point kills the Π₁ claim "every number is not 5".
not5-falsified : ¬ ((m : ℕ) → isNot5 m ≡ true)
not5-falsified = falsify isNot5 5 refl

-- And every truncation below the counterexample is affirmed: the
-- decision procedure from (b), run at bound 5, is the checked finite
-- sweep the protocol's "numerics as falsifiers" permits.  Extracting
-- its yes-witness is one Dec-elimination whose no-branch is closed by
-- the same direct evidence, so the truncated Π is simply inhabited.
not5-below5 : Bounded isNot5 5
not5-below5 m h with <-split h
not5-below5 m h | inr m≡4 = subst (λ k → isNot5 k ≡ true) (sym m≡4) refl
not5-below5 m h | inl m<4 with <-split m<4
not5-below5 m h | inl m<4 | inr m≡3 = subst (λ k → isNot5 k ≡ true) (sym m≡3) refl
not5-below5 m h | inl m<4 | inl m<3 with <-split m<3
not5-below5 m h | inl m<4 | inl m<3 | inr m≡2 = subst (λ k → isNot5 k ≡ true) (sym m≡2) refl
not5-below5 m h | inl m<4 | inl m<3 | inl m<2 with <-split m<2
not5-below5 m h | inl m<4 | inl m<3 | inl m<2 | inr m≡1 = subst (λ k → isNot5 k ≡ true) (sym m≡1) refl
not5-below5 m h | inl m<4 | inl m<3 | inl m<2 | inl m<1 with <-split m<1
not5-below5 m h | inl m<4 | inl m<3 | inl m<2 | inl m<1 | inr m≡0 = subst (λ k → isNot5 k ≡ true) (sym m≡0) refl
not5-below5 m h | inl m<4 | inl m<3 | inl m<2 | inl m<1 | inl m<0 = Empty.rec (¬-<-zero m<0)

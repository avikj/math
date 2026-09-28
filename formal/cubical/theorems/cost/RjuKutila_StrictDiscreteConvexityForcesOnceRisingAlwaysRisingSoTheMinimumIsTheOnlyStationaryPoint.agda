{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ऋजु-कुटिल — the straight and the bent.  The licensing theorem behind the
-- machine's convexity certificate (runtime/physics/geodesic.py (absent from this repository)): on a
-- discrete family, STRICT CONVEXITY forces once-weakly-rising ⟹
-- strictly-rising-forever — no plateau, no second dip — so the extracted
-- minimum is the ONLY stationary point, and "cost-minimal route" may be
-- read as "physical ray".  Fermat is stationarity (δOPL = 0); extraction
-- is minimisation; minimal ⟹ stationary always, and the converse is
-- exactly what this theorem licenses.  The mirror maximum (geodesic.py (absent from this repository)'s
-- own counterexample) violates the hypothesis, not the theorem.
--
-- STATED WITHOUT SUBTRACTION.  Over ℕ the second difference is not a
-- term, but strict convexity at the interior point i+1 is:
--
--     v(i) + v(i+2)  >  v(i+1) + v(i+1).
--
-- CHECKED:
--   §1  step  — one weak rise forces the next rise strict:
--         v i ≤ v (suc i)  →  v (suc i) < v (suc (suc i)).
--       (If v(i+2) ≤ v(i+1), then 2·v(i+1) < v(i)+v(i+2) ≤ v(i+1)+v(i+2)
--        ≤ 2·v(i+1) — a term less than itself.  ¬m<m.)
--   §2  always — by induction, strictly rising at every later point:
--         v i ≤ v (suc i) → ∀ k, v (k + suc i) < v (suc (k + suc i)).
--       (k on the LEFT so every index reduces definitionally.)
--   §3  no-return — the corollary the certificate quotes: after a weak
--       rise the value never returns to or below the pre-rise floor:
--       v(i+1) ≤ every later value.  A minimiser that has risen has
--       finished: nothing later is smaller, so no stationary point
--       other than the minimum exists.
--
-- The certificate in geodesic.py (absent from this repository) checks the hypothesis (every interior
-- second difference > 0, exact Surd signs); this term is the implication
-- it then invokes.  Declared there, proved here.
--
-- This term proves the
-- implication for ℕ-VALUED families.  geodesic.py (absent from this repository)'s OPL values are exact
-- Surds (quadratic irrationals); the implication at Surd values has the
-- same proof shape over any cancellative ordered additive structure but
-- is not itself this term.  "Declared there, proved here" holds at ℕ.
------------------------------------------------------------------------

module RjuKutila_StrictDiscreteConvexityForcesOnceRisingAlwaysRisingSoTheMinimumIsTheOnlyStationaryPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-trans; ≤-+k; ≤-k+; ¬m<m; <-weaken; ≤<-trans; <≤-trans)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)

module _ (v : ℕ → ℕ)
         (convex : (i : ℕ) → (v (suc i) + v (suc i)) < (v i + v (suc (suc i))))
  where

  ------------------------------------------------------------------
  -- §1 · one weak rise forces the next rise strict.  Trichotomy-free:
  -- suppose not (v(i+2) ≤ v(i+1)); chain the certificate's inequality
  -- through both monotonicities into m < m.
  private
    absurd-chain : (i : ℕ) → v i ≤ v (suc i) → v (suc (suc i)) ≤ v (suc i) → ⊥
    absurd-chain i rise fall =
      ¬m<m (<≤-trans (<≤-trans (convex i) mono₁) mono₂)
      where
      -- v(i) + v(i+2) ≤ v(i+1) + v(i+2)
      mono₁ : v i + v (suc (suc i)) ≤ v (suc i) + v (suc (suc i))
      mono₁ = ≤-+k rise
      -- v(i+1) + v(i+2) ≤ v(i+1) + v(i+1)
      mono₂ : v (suc i) + v (suc (suc i)) ≤ v (suc i) + v (suc i)
      mono₂ = ≤-k+ fall

  -- ≤ on ℕ is decidable through splitting <; here we use the library's
  -- ¬≤→< shape via Dichotomyℕ-free route: derive < from ¬ ≤ by the
  -- standard split lemma.
  open import Cubical.Data.Nat.Order using (splitℕ-≤; ≤-split)

  step : (i : ℕ) → v i ≤ v (suc i) → v (suc i) < v (suc (suc i))
  step i rise with splitℕ-≤ (v (suc (suc i))) (v (suc i))
  ... | inl fall = Empty.rec (absurd-chain i rise fall)
  ... | inr gt   = gt

  ------------------------------------------------------------------
  -- §2 · strictly rising at every later point.  k rides on the LEFT of +
  -- so both the base and the inductive index reduce definitionally.
  always : (i : ℕ) → v i ≤ v (suc i)
         → (k : ℕ) → v (k + suc i) < v (suc (k + suc i))
  always i rise zero    = step i rise
  always i rise (suc k) = step (k + suc i) (<-weaken (always i rise k))

  ------------------------------------------------------------------
  -- §3 · NO RETURN.  After a weak rise at i, every later value dominates
  -- v (suc i): the family never dips again, so the minimum the extractor
  -- found is the only stationary point — the certificate's license.
  no-return : (i : ℕ) → v i ≤ v (suc i)
            → (k : ℕ) → v (suc i) ≤ v (k + suc i)
  no-return i rise zero    = ≤-refl
  no-return i rise (suc k) =
    ≤-trans (no-return i rise k) (<-weaken (always i rise k))

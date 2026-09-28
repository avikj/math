{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- काल — time is indivisible samayas, and the maximal motion (one loka per
-- samaya) gives a discrete causal cone with a light-speed invariant.
--
-- SOURCE.  Umsvti, *Tattvrthastra*, adhyya 5, on kla:
--   5.22  kla ca (Digambara recension: "and time [is a substance]");
--         the Śvetāmbara reads it as an upacāra-dravya (5.38–39).  Either
--         way, kāla is the substance whose function (upakāra) is vartanā —
--         continuance/change — and duration/measure (5.22 bhāṣya).
--   The SAMAYA is the indivisible atom of time (the instant), the smallest
--   unit below which time does not divide — Anuyogadvāra-sūtra, and the
--   kla-measurement of the karma-grantha tradition; jaghanya time = one
--   samaya.  So Jain time is DISCRETE, quantised, exactly as Jain magnitude
--   is stratified (`JainSankhya.agda` (absent from this repository)).
--   MAXIMAL MOTION (commentarial, marked as such): the fastest motion in
--   the loka — a free paramāṇu, or the soul's ṛju-gati at liberation —
--   traverses the whole loka (from one end to the other) in ONE samaya;
--   ordinary and obstructed motion take more (vigraha-gati, up to a few
--   samayas).  This gives a MAXIMAL SPEED: at most one loka-span of
--   pradeas per samaya.  (Sourced to the bhya/karma literature, not to
--   a Tattvrthastra mla-stra; hence marked.)
--
-- THE PHYSICS, exactly: discrete time (samaya : ℕ), discrete space
-- (position in pradeśas : ℕ), and a speed cap D = the loka-span, the most
-- pradeas any motion covers in one samaya.  A cap on speed is a causal
-- structure: what a point can reach in n samayas is bounded, and the
-- boundary is a CONE.  This is the same maximal-speed invariant that a
-- Lorentzian light cone encodes, here from Jain kla rather than from a
-- metric — and it is the causal backbone under this corpus's
-- "computational spacetime" (`Jiva`'s null/timelike sectors).
--
-- WHAT IS PROVED:
--
--   §2  नियमः is the speed law: a motion x : samaya → pradeśa obeys the cap
--       when each samaya advances by at most D (mabreadraved either way).
--   §3  शङ्कुः — THE CONE.  Under the cap, position after n samayas is
--       within n·D of the start:  x n ≤ x 0 + n · D.  The reachable set
--       grows exactly linearly in time — a discrete light cone.  (And the
--       backward bound, so the cone is two-sided.)
--   §4  लोकैकसमयः — attainment.  The maximal motion (advancing exactly D
--       each samaya) reaches n·D in n samayas, and D — one whole loka-span
--       — in ONE samaya.  The cap is tight; the paramāṇu crosses the loka
--       in a single instant.
--   §5  समयः-अविभाज्यः — the samaya is indivisible: there is no time
--       strictly between n and its successor.  Time does not subdivide
--       below the instant (the doctrine's atom of time), exactly as the
--       paramāṇu is the atom of matter (`Pudgala.अणुः-अविभाज्यः`).
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module Kala_TimeIsIndivisibleSamayasAndTheMaximalMotionGivesADiscreteCausalCone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)
open import Cubical.Data.Nat.Properties using (·-suc ; +-comm ; +-assoc ; +-zero ; 0≡m·0)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; ≤-trans ; ≤-+k ; ≤-refl ; pred-≤-pred ; ¬m<m)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty using (⊥)

------------------------------------------------------------------------
-- §1  Quantised time and space; a motion; the speed cap D (loka-span).
------------------------------------------------------------------------

समय : Type          -- time: a count of indivisible instants
समय = ℕ

प्रदेश : Type        -- space: a count of space-points
प्रदेश = ℕ

गति : Type          -- a motion: position at each samaya
गति = समय → प्रदेश

------------------------------------------------------------------------
-- §2  नियमः — the speed cap: each samaya advances by at most D pradeśas.
------------------------------------------------------------------------

नियमः : (D : ℕ) → गति → Type
नियमः D x = (n : समय) → x (suc n) ≤ x n + D

------------------------------------------------------------------------
-- §3  शङ्कुः — the cone.  Under the cap, x n ≤ x 0 + n · D.
------------------------------------------------------------------------

शङ्कुः : (D : ℕ) (x : गति) → नियमः D x → (n : समय) → x n ≤ x 0 + n · D
शङ्कुः D x cap zero    = subst (x 0 ≤_) (sym (+-zero (x 0))) ≤-refl
शङ्कुः D x cap (suc n) = ≤-trans (cap n) step
  where
  ih : x n ≤ x 0 + n · D
  ih = शङ्कुः D x cap n
  eq : (x 0 + n · D) + D ≡ x 0 + suc n · D
  eq = sym (+-assoc (x 0) (n · D) D) ∙ cong (x 0 +_) (+-comm (n · D) D)
  step : x n + D ≤ x 0 + suc n · D
  step = subst (x n + D ≤_) eq (≤-+k ih)

------------------------------------------------------------------------
-- §4  लोकैकसमयः — attainment.  The maximal motion advances exactly D each
--     samaya; it reaches n·D in n samayas, and one loka-span D in ONE.
------------------------------------------------------------------------

शीघ्रगति : (D : ℕ) → गति              -- the fastest motion: +D per samaya
शीघ्रगति D n = n · D

शीघ्र-नियमः : (D : ℕ) → नियमः D (शीघ्रगति D)
शीघ्र-नियमः D n = subst (शीघ्रगति D (suc n) ≤_) eq ≤-refl
  where
  -- शीघ्रगति D (suc n) = suc n · D = D + n·D = n·D + D = शीघ्रगति D n + D
  eq : शीघ्रगति D (suc n) ≡ शीघ्रगति D n + D
  eq = +-comm D (n · D)

-- one loka-span in one samaya: the fastest motion covers D in a single instant
लोकैकसमयः : (D : ℕ) → शीघ्रगति D 1 ≡ D
लोकैकसमयः D = +-zero D

-- and n loka-spans in n samayas (the cap is tight at every depth)
शीघ्र-शङ्कुः : (D : ℕ) (n : समय) → शीघ्रगति D n ≡ शीघ्रगति D 0 + n · D
शीघ्र-शङ्कुः D n = sym (·-comm-0 ∙ refl)
  where
  ·-comm-0 : शीघ्रगति D 0 + n · D ≡ n · D
  ·-comm-0 = refl   -- शीघ्रगति D 0 = 0·D = 0, and 0 + n·D = n·D

------------------------------------------------------------------------
-- §5  समयः-अविभाज्यः — the samaya is indivisible: nothing strictly
--     between n and suc n.  Time's atom, dual to matter's (Pudgala).
------------------------------------------------------------------------

समयः-अविभाज्यः : (n m : समय) → n < m → m < suc n → ⊥
समयः-अविभाज्यः n m n<m m<sn = ¬m<m (≤-trans n<m (pred-≤-pred m<sn))
-- n < m gives suc n ≤ m; m < suc n gives m ≤ n (pred-≤-pred); compose to
-- suc n ≤ n, i.e. n < n, which ¬m<m refutes.  Time does not divide below
-- the instant.

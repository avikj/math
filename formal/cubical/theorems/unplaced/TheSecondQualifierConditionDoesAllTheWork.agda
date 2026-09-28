{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheSecondUpadhiConditionDoesAllTheWork
--
-- The Naiyyikas state TWO conditions on an updhi.  Proved here: the
-- first alone is satisfied by a candidate that always exists, so it
-- carries no information; the second is what has content; and the bare
-- existential "some updhi exists" is equivalent to "the pervasion
-- fails" and therefore says nothing beyond it.  Only a NAMED updhi is
-- informative — which is why the Navya-Nyāya treatment is a taxonomy of
-- candidates and not an existence claim.
--
-- ────────────────────────────────────────────────────────────────────
-- THE SCHOOL, AND ITS TERMS, NAMED BEFORE USE
--
-- Nyya (Gautama, *Nyyastra*; the updhi machinery developed by the
-- Navya-Naiyyikas, Gagea, *Tattvacintmai*, 14th c.).  A *vypti* is
-- a pervasion — wherever the hetu, there the sādhya.  An *upādhi* is the
-- adventitious condition that defeats one.  The standard pair of
-- conditions on a genuine updhi U, for the inference "hetu H, therefore
-- sdhya S":
--
--   sādhya-vyāpakatva   U pervades the sādhya      (x : D) → S x → U x
--   sādhana-avyāpakatva U does not pervade the hetu ¬ ((x) → H x → U x)
--
-- The textbook instance: "the mountain has smoke because it has fire" —
-- the updhi is wet fuel, which pervades smoke and does not pervade fire
-- (red-hot iron).
--
-- WHAT A RIVAL SCHOOL WOULD SAY.  The Jaina objection to the Naiyyika
-- apparatus is that a pervasion asserted flatly, without its standpoint,
-- is already a durnaya; on that reading `Vyapti` is the durnaya and U is
-- the missing *syt*.  The Naiyyika reply is that this dissolves the
-- inference rather than repairing it: if every vypti is conditioned,
-- no anumna is a prama, and the updhi apparatus exists precisely to
-- keep the unconditioned ones.  Nothing below adjudicates that; the
-- theorems are about the two conditions as the Naiyyikas state them.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT PROVOKED THIS
--
-- `interactive/Upadhi.hs` (absent from this repository).  It reports that the engine's
-- sampler draws 40 assignments reduced `mod 9` and declares two terms
-- equal when their 40 values agree, and it records — in its own words —
-- "the risk is real and the failure is unobserved, and those are
-- different statements."
--
-- §4 is that sentence as a theorem, with the shelf's own numbers used
-- for nothing but the choice of probe size.  NO measurement from that
-- shelf is reproduced, relied on, or needed here: the probe below is
-- nine points because `mod 9` is nine points, and the counterexample is
-- exhibited, not sampled.
------------------------------------------------------------------------

module TheSecondQualifierConditionDoesAllTheWork where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  Vypti and the two conditions
------------------------------------------------------------------------

module _ (D : Type) (H S : D → Type) where

  -- the pervasion itself
  Vyapti : Type
  Vyapti = (x : D) → H x → S x

  -- sdhya-vypakatva: U pervades the sdhya
  SadhyaVyapaka : (D → Type) → Type
  SadhyaVyapaka U = (x : D) → S x → U x

  -- sdhana-avypakatva: U does not pervade the hetu
  SadhanaAvyapaka : (D → Type) → Type
  SadhanaAvyapaka U = ¬ ((x : D) → H x → U x)

  Upadhi : (D → Type) → Type
  Upadhi U = SadhyaVyapaka U × SadhanaAvyapaka U

  --------------------------------------------------------------------
  -- 2.  The first condition alone is vacuous
  --------------------------------------------------------------------

  -- the sdhya pervades itself, so a candidate meeting condition one
  -- exists for EVERY inference, with no hypothesis whatever
  firstConditionAlwaysHasACandidate : Σ[ U ∈ (D → Type) ] SadhyaVyapaka U
  firstConditionAlwaysHasACandidate = S , λ _ s → s

  -- and for that candidate, condition two IS the failure of the
  -- pervasion — the same type, not merely an equivalent one
  secondConditionOnTheTrivialCandidate : SadhanaAvyapaka S ≡ (¬ Vyapti)
  secondConditionOnTheTrivialCandidate = refl

  --------------------------------------------------------------------
  -- 3.  So the existential says nothing, and the naming says everything
  --------------------------------------------------------------------

  -- a genuine updhi refutes the pervasion
  upadhiRefutesVyapti : (U : D → Type) → Upadhi U → ¬ Vyapti
  upadhiRefutesVyapti U (sv , sa) vy = sa (λ x h → sv x (vy x h))

  -- …and conversely, any failed pervasion has one, by the trivial
  -- candidate.  Hence `Σ U. Upadhi U` and `¬ Vyapti` are interderivable:
  -- the existential carries exactly the information that the inference
  -- is bad, and none about WHY.
  failedVyaptiHasAnUpadhi : ¬ Vyapti → Σ[ U ∈ (D → Type) ] Upadhi U
  failedVyaptiHasAnUpadhi nv = S , (λ _ s → s) , nv

  someUpadhiExists→vyaptiFails : Σ[ U ∈ (D → Type) ] Upadhi U → ¬ Vyapti
  someUpadhiExists→vyaptiFails (U , u) = upadhiRefutesVyapti U u

------------------------------------------------------------------------
-- 4.  A named updhi: agreement at an untested point
--
-- The inference under test is the sampler's:
--   hetu    H — the two functions agree on the probe
--   sādhya  S — the two functions are equal
-- and the upādhi is `U` — they agree at 9, the first point `mod 9`
-- cannot reach.
------------------------------------------------------------------------

All : {A : Type} (Q : A → Type) → List A → Type
All Q []       = Unit
All Q (x ∷ xs) = Q x × All Q xs

probe : List ℕ
probe = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []

f₀ : ℕ → ℕ
f₀ _ = 0

g₀ : ℕ → ℕ
g₀ 0 = 0
g₀ 1 = 0
g₀ 2 = 0
g₀ 3 = 0
g₀ 4 = 0
g₀ 5 = 0
g₀ 6 = 0
g₀ 7 = 0
g₀ 8 = 0
g₀ _ = 1

Pair : Type
Pair = (ℕ → ℕ) × (ℕ → ℕ)

Hprobe : Pair → Type
Hprobe (f , g) = All (λ x → f x ≡ g x) probe

Severy : Pair → Type
Severy (f , g) = (x : ℕ) → f x ≡ g x

Uat9 : Pair → Type
Uat9 (f , g) = f 9 ≡ g 9

-- the witness the sampler cannot see: agreement on all nine probe points
agreeOnProbe : Hprobe (f₀ , g₀)
agreeOnProbe =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

-- sdhya-vypakatva: equality everywhere gives agreement at 9
u-pervades-sadhya : SadhyaVyapaka Pair Hprobe Severy Uat9
u-pervades-sadhya (f , g) s = s 9

-- sdhana-avypakatva: probe-agreement does NOT give agreement at 9
u-does-not-pervade-hetu : SadhanaAvyapaka Pair Hprobe Severy Uat9
u-does-not-pervade-hetu h = znots (h (f₀ , g₀) agreeOnProbe)

theUpadhi : Upadhi Pair Hprobe Severy Uat9
theUpadhi = u-pervades-sadhya , u-does-not-pervade-hetu

-- and therefore the sampler's pervasion is not one
probeAgreementDoesNotPervadeEquality : ¬ Vyapti Pair Hprobe Severy
probeAgreementDoesNotPervadeEquality =
  upadhiRefutesVyapti Pair Hprobe Severy Uat9 theUpadhi

------------------------------------------------------------------------
-- 5.  What §2–§3 change about how the shelf's sentence should be read
--
-- `interactive/Upadhi.hs` (absent from this repository) distinguishes "the risk is real" from "the failure
-- is unobserved".  §3 says why that distinction is forced rather than
-- cautious: `Σ U. Upadhi U` is interderivable with `¬ Vyapti`, so
-- asserting that SOME defeating condition exists is not weaker evidence
-- for the same thing — it is the same statement.  What is not the same
-- statement is exhibiting one, and §4 exhibits one for a probe while the
-- shelf's own search for one among ACTUAL engine terms returned nothing.
--
-- The two live on one axis: ` Vyapti` is a
-- negation and is ¬¬-stable for free; `Σ U. Upadhi U` is a search, and
-- its stability is not free — it is bought with a decision or with a
-- construction.  Here the construction is `theUpadhi`, given outright.
-- Cross-reference, same axis, different object:
-- `PermanentUnsaidIsStableAndTemporaryIsASearch`.
------------------------------------------------------------------------

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- एकं छिद्रम् — one aperture.
--
-- The entrypoint note VYAYA_SESA argues that the obstruction the corpus
-- meets in every lane — avaktavya (logic), śeṣa / non-localizing cost
-- (computation), one-wayness (crypto), holonomy (physics) — is ONE
-- class.  This module makes the common type a term: in each lane the
-- obstruction is the NON-EQUIVALENCE of that lane's forgetful map, and a
-- witnessed collision (two distinct points in one fibre) is a witness of
-- it.  Not a bundle of unrelated facts under one Σ — a single type,
-- `WitnessedNonEquiv f`, populated from three lanes, each reducing to
-- the SAME conclusion `¬ isEquiv f`.
--
--   §0  THE TYPE.  `WitnessedNonEquiv f = Σ b, two distinct points of
--       (fiber f b)`.  This is the constructive content of "f is not an
--       equivalence, and here is why": isEquiv means every fibre is
--       contractible, so two distinct fibre points refute it.
--   §1  witnessed→¬isEquiv : the reduction, once, generically.
--   §2  COST.  The meaning map μ d = derivation-sound d sends the two
--       coterminal kernel histories (direct, detour) to the SAME value
--       (meaning-agrees) though they are distinct (len 2 ≠ 4).  A
--       witnessed non-equivalence of μ — cost's śeṣa as ¬ isEquiv.
--   §3  CRYPTO.  Sesa already proved ¬ isEquiv powg (the discrete log is
--       not an equivalence).  Carried here as the same conclusion the
--       cost witness lands in — the two lanes' obstructions are one type.
--
-- LOGIC, the third corner, is the propositional (truncated) shadow:
-- `Yugapat` proves avaktavya = ¬(A × B) does not decompose into
-- (¬A) × (¬B) — the (−1)-truncated form of "no section of the joint".
-- `SaptabhangiNaya` proves the seven bhagas are the nonempty faces of
-- the 2-simplex on {asti, nāsti, avaktavya} — the nerve of the observer
-- cover.  So the fourth position is the H¹ of that cover; ¬ isEquiv is
-- its untruncated form here.  Those are cited, not rebuilt.
--
------------------------------------------------------------------------

module EkamChidram_TheObstructionIsOneClassCostCryptoAndCollisionAreEachANonEquivalenceOfTheForgetfulMap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; equiv-proof ; fiber)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; _×_ ; fst ; snd)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate using (Tm ; Derivation ; Env ; eval ; derivation-sound)
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)
open import ForgetfulCompressionPricesTheDrop using (len ; 2≢4 ; meaning-agrees)
open import GhataFiber_TheDiscreteLogIsTheFiberOfPingalasPowerAndShorsPeriodQueryIsWhatReadsIt
  using (powg)
open import Residue_TheOneWayFunctionIsExactlyANonEquivalenceAndCryptoLivesInTheResidualUnivalenceCannotErase
  using (घातः-न-तुल्यता)

private variable ℓ ℓ' : Level

------------------------------------------------------------------------
-- ० · The one type: a witnessed non-equivalence of a forgetful map.
------------------------------------------------------------------------

WitnessedNonEquiv : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Type (ℓ-max ℓ ℓ')
WitnessedNonEquiv {Y = Y} f =
  Σ[ b ∈ Y ] Σ[ p ∈ fiber f b ] Σ[ q ∈ fiber f b ] (¬ p ≡ q)

------------------------------------------------------------------------
-- १ · The reduction, once and generically: a witness refutes isEquiv.
--     isEquiv makes every fibre contractible; two distinct fibre points
--     then collapse, contradicting the witness.
------------------------------------------------------------------------

witnessed→¬isEquiv : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
  → WitnessedNonEquiv f → ¬ isEquiv f
witnessed→¬isEquiv f (b , p , q , p≢q) ie =
  p≢q (sym (c .snd p) ∙ c .snd q)
  where c = equiv-proof ie b

------------------------------------------------------------------------
-- २ · COST.  The meaning map, and its witnessed non-equivalence.
------------------------------------------------------------------------

-- the forgetful map of the cost lane: a derivation to the endpoint
-- equality it certifies, forgetting the route (and its length).
μ : Derivation seed target₀ → ((ρ : Env) → eval seed ρ ≡ eval target₀ ρ)
μ d = derivation-sound d

costObstruction : WitnessedNonEquiv μ
costObstruction =
  μ direct-history
  , (direct-history , refl)
  , (detour-history , sym (funExt meaning-agrees))
  , λ pq → 2≢4 (cong len (cong fst pq))

costIsNonEquiv : ¬ isEquiv μ
costIsNonEquiv = witnessed→¬isEquiv μ costObstruction

------------------------------------------------------------------------
-- ३ · CRYPTO.  Sesa's discrete-log non-equivalence, the same conclusion.
------------------------------------------------------------------------

cryptoIsNonEquiv : ¬ isEquiv powg
cryptoIsNonEquiv = घातः-न-तुल्यता

------------------------------------------------------------------------
-- The one aperture: cost and crypto obstructions inhabit one type.
-- Each forgetful map fails to be an equivalence; the ea is the fibre
-- that failure leaves, and univalence (ua transports only equivalences)
-- therefore cannot erase it — the same floor Sesa names for crypto,
-- Laghava names for cost, and Yugapat names, truncated, for avaktavya.
------------------------------------------------------------------------

theOneObstruction : (¬ isEquiv μ) × (¬ isEquiv powg)
theOneObstruction = costIsNonEquiv , cryptoIsNonEquiv

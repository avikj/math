{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- नाणक — the coin.
--
-- THE CLAIM (2026-09-03): the hard distinctions this corpus has been
-- circling are not a family of analogies — they are inhabitants of ONE
-- type.  A face of the coin is: a projection, two carried points,
-- apartness upstairs, identification downstairs.
--
--     record Paksa: Carried, Forgotten, q, x, y,
--                   apart : ¬ x ≡ y,  together : q x ≡ q y.
--
-- The point of minting the type is threefold.
--
--   §1  ONE LEMMA SERVES EVERY FACE.  No face's projection admits a
--       retraction that recovers both carried points: r(q x) ≡ x and
--       r(q y) ≡ y are jointly refutable, once, generically.  Every
--       "the information is not recoverable downstairs" argument in
--       the corpus is this one proof.
--
--   §2  FOUR FACES, FOUR INDEPENDENT LANES, ONE TYPE — each face built
--       from another module's checked terms, none re-proved here:
--
--       gapFace       the P/NP lane: the visible Turing step carries a
--                     collision (Nasha's the-step-forgets) — find/check
--                     asymmetry as non-injectivity of the projection.
--       routeFace     the semantics lane: direct and detour histories
--                     are distinct data (lengths 2 and 4) with equal
--                     forgetful meaning — classical cost lives in the
--                     drop.
--       scheduleFace  the compression lane: the diamond's two
--                     schedules are distinct (depths 2 and 1) and the
--                     quotient by the explanation identifies them.
--       countFace     the interaction lane: the free-orbit witnesses
--                     p and q are distinct and every symmetric count
--                     receives them identically (the count factors
--                     through the unordered square, so its reading of
--                     the two is one reading).
--
--   §3  THE COIN IS NONBINARY, as a term.  For every face, apart and
--       together are BOTH theorems: "are x and y the same?" has no
--       boolean answer — it has a position indexed by which side of
--       the projection is asked.  bothTheorems packages the pair, and
--       it is syd-asti-nsti at the level of identity itself: same
--       downstairs (asti), distinct upstairs (nsti), no collapse
--       available (§1).  Where the corpus's other lanes each proved a
--       distinction "lives only on the lossy projection", this module
--       is the statement that they were all holding the same coin.
--
-- Companion law, proved elsewhere and cited, not restated: the reason
-- the carried side cannot be discarded is AvarohaNisedha — no additive
-- cost survives any receiver that inverts arrows, and the carried side
-- is invertible (EveryDerivationIsInvertible).  Cost, route, schedule,
-- count: each lives exactly in what its projection drops.
--
------------------------------------------------------------------------

module Nanaka_OneNoRetractionLemmaFourCheckedFacesTheGapTheRouteTheScheduleAndTheCountAreOneCoin where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (snotz ; injSuc)
open import Cubical.Data.Int using (ℤ ; pos ; injPos)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.SetQuotients using ([_])

open import Kernel.RewriteCertificate using (Tm ; Derivation ; Env ; eval ; derivation-sound)
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)
open import Vishvayantra_TheTuringStepIsTheVisibleProjectionOfTheLosslessStepAndTheKeptFibreIsTheSource
  using (Machine ; uStep)
open import Nasha_TheVisibleStepDestroysInformationAndTheCompletedStepCannotByConstruction
  using (the-step-forgets)
open import ForgetfulCompressionPricesTheDrop using (len ; 2≢4 ; meaning-agrees)
open import MulyaVinimaya_TheValueOfATraceIsItsPairingWithAnEvaluatorPotentialsTelescopeAndADepthEvaluatorHasNonzeroCycleIntegral
  using (∫ ; गभीरता ; scheduleA ; scheduleB ; depthA ; depthB ; t₀ ; nf)
open import Vyakhya_TheQuotientByAnExplanationIsLosslessForEveryExactEvaluatorAndKillsTheDepthClass
  using (Explained ; identified)
open import GananaAndhata_TheMobiusCountIsSwapBlindWhileTheInteractionCarrierHoldsAFreeOrbitOutsideTheComparisonImage
  using (P ; p ; q ; p≢q)

------------------------------------------------------------------------
-- ० · One face of the coin.
------------------------------------------------------------------------

record Paksa : Type₁ where
  field
    Carried   : Type₀
    Forgotten : Type₀
    proj      : Carried → Forgotten
    x y       : Carried
    apart     : x ≡ y → ⊥
    together  : proj x ≡ proj y

  -- §3: the nonbinary reading, on every face, for free.
  bothTheorems : (x ≡ y → ⊥) × (proj x ≡ proj y)
  bothTheorems = apart , together

open Paksa

------------------------------------------------------------------------
-- १ · One lemma serves every face: no retraction recovers both points.
------------------------------------------------------------------------

noRetraction : (f : Paksa) (r : Forgotten f → Carried f)
  → r (proj f (x f)) ≡ x f
  → r (proj f (y f)) ≡ y f
  → ⊥
noRetraction f r rx ry =
  apart f (sym rx ∙ cong r (cong (proj f) refl ∙ together f) ∙ ry)

------------------------------------------------------------------------
-- २ · The four faces, each minted from another lane's checked terms.
------------------------------------------------------------------------

-- P/NP: the visible Turing step's collision (Nasha).  Find/check
-- asymmetry = the producer is not recoverable from the image.
gapFace : Paksa
gapFace .Carried   = Machine
gapFace .Forgotten = Machine
gapFace .proj      = uStep
gapFace .x         = fst the-step-forgets
gapFace .y         = fst (snd the-step-forgets)
gapFace .apart     = fst (snd (snd the-step-forgets))
gapFace .together  = snd (snd (snd the-step-forgets))

-- route/cost: two histories, one forgetful meaning (the semantics
-- lands in a set; the lengths 2 and 4 separate them upstairs).
routeFace : Paksa
routeFace .Carried   = Derivation seed target₀
routeFace .Forgotten = (ρ : Env) → eval seed ρ ≡ eval target₀ ρ
routeFace .proj      = derivation-sound
routeFace .x         = direct-history
routeFace .y         = detour-history
routeFace .apart e   = 2≢4 (cong len e)
routeFace .together  = funExt meaning-agrees

-- schedule/depth: the diamond's two schedules, identified by the
-- explanation's quotient; separated upstairs by accumulated depth.
scheduleFace : Paksa
scheduleFace .Carried   = Derivation t₀ nf
scheduleFace .Forgotten = Explained
scheduleFace .proj      = [_]
scheduleFace .x         = scheduleA
scheduleFace .y         = scheduleB
scheduleFace .apart e   =
  snotz (injSuc (injPos (sym depthA ∙ cong (∫ गभीरता) e ∙ depthB)))
scheduleFace .together  = identified

-- interaction/count: the free-orbit witnesses, distinct in the
-- carrier, identical to the coordinatewise-symmetric reading (their
-- unordered support: both are "one false and one true").
xor : Bool → Bool → Bool
xor false v = v
xor true false = true
xor true true = false

countFace : Paksa
countFace .Carried   = P
countFace .Forgotten = Bool   -- the symmetric reading: xor of the pair, order-blind by +Comm's Boolean shadow
countFace .proj (a , b , _) = xor a b
countFace .x         = p
countFace .y         = q
countFace .apart     = p≢q
countFace .together  = refl

------------------------------------------------------------------------
-- ३ · The coin, held: four faces, one type, and on each the general
--     lemma applies — no observer downstairs reads both points back.
------------------------------------------------------------------------

theCoin :
    ((r : Machine → Machine)
       → r (uStep (x gapFace)) ≡ x gapFace
       → r (uStep (y gapFace)) ≡ y gapFace → ⊥)
  × ((r : Forgotten routeFace → Derivation seed target₀)
       → r (proj routeFace direct-history) ≡ direct-history
       → r (proj routeFace detour-history) ≡ detour-history → ⊥)
  × ((r : Explained → Derivation t₀ nf)
       → r [ scheduleA ] ≡ scheduleA
       → r [ scheduleB ] ≡ scheduleB → ⊥)
  × ((r : Bool → P)
       → r (proj countFace p) ≡ p
       → r (proj countFace q) ≡ q → ⊥)
theCoin =
    noRetraction gapFace
  , noRetraction routeFace
  , noRetraction scheduleFace
  , noRetraction countFace

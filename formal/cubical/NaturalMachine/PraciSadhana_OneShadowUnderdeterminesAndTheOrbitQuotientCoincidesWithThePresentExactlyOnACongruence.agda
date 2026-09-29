{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.PraciSadhana_OneShadowUnderdeterminesAndTheOrbitQuotientCoincidesWithThePresentExactlyOnACongruence
--
-- THE NAME.  प्राचीसाधन (prācī-sādhana), "establishing the east line".
-- The *Sūrya Siddhānta*, chapter 3 — त्रिप्रश्नाधिकार, the chapter of the
-- three questions (दिश् direction, देश place, काल time) — obtains all
-- three from the शङ्कु (śaṅku, gnomon) and its छाया (chāyā, shadow).  The
-- direction procedure: draw a circle about the foot of the aku, mark
-- where the shadow-tip crosses it in the forenoon, mark where it crosses
-- again in the afternoon, join the two marks.  That line is east–west.
--
-- ONE shadow does not give the direction.  TWO shadow-tips, taken at two
-- points of the sun's daily course, do.  The instrument is unchanged
-- between the two readings; what is added is a second reading along the
-- motion.
--
-- Dates and texts, as facts:
--   * Āryabhaṭa, *Āryabhaṭīya*, 499 — śaṅku and chāyā computations; the
--     gnomon is 12 agulas.
--   * *Sūrya Siddhānta*, ch. 3 (Triprashnādhikāra) — the three questions
--     from gnomon shadows.  The surviving recension's date is disputed;
--     a *Srya Siddhnta* is one of the five summarised by Varhamihira,
--     *Pacasiddhntik*, c. 550, which is earlier than that recension.
--   * al-Brn, 11th c., writes on the astrolabe.
--   * Sawai Jai Singh II builds the Jantar Mantar instruments, 1724–34,
--     in masonry: the Samr Yantra's precision comes from its size.
--
-- ────────────────────────────────────────────────────────────────────
-- THE SCHOOLS, NAMED BEFORE THEIR TERMS ARE USED.
--
-- Nyāya-Vaiśeṣika.  §3's `two-shadows-determine` is an अभाव (abhāva,
-- absence), and Navya-Nyya forbids asserting one bare: it must carry its
-- प्रतियोगिन् (pratiyogin, counterpositive) and its अवच्छेदक (avacchedaka,
-- delimitor).  Named here: what is absent is orbit-agreement between the
-- states (false , true) and (false , false); the delimitor is the pair
-- (`turn` , `shadow`).  `NaturalMachine.Abhava` supplies the record that
-- forces this.
--
-- Jaina.  A Jaina logician answers that `Present` and `Orbit` are two
-- नय (naya, standpoints), that neither is false, and that a naya
-- asserting itself by denying the other is a दुर्नय (durnaya).  Their
-- objection to the Naiyyika above is specific: the pratiyogin was named
-- FROM a standpoint — the reading `shadow` — so a different reading names
-- a different counterpositive and the absence is a family, not one
-- entity.  The Naiyyika answers that once the avacchedaka is exhibited
-- the absence is determinate and needs no further relativisation, which
-- is exactly what the record in `Abhva` encodes.
--
-- THIS MODULE TAKES NEITHER SIDE, and can afford not to: every relation
-- below is explicitly indexed by (step , read), and §2's result is a
-- BICONDITIONAL, so no statement here requires the dispute settled.  Where
-- a verdict would be needed, there is a criterion instead.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED.
--
--  §1  For a state space with a step and a present reading, two quotients:
--      `Present` (this reading now) and `Orbit` (this reading at every
--      depth).  `orbit-refines-present`: Orbit ⇒ Present, unconditional,
--      by evaluation at depth 0.
--
--  §2  THE CRITERION, both directions.  Present ⇒ Orbit  ⟺  the present
--      fibre is a CONGRUENCE for the step.  The forward direction is
--      induction on depth; the reverse is evaluation at depth 1.
--      `invariant→congruence`: an invariant reading is a congruence.
--
--  §3  THE WITNESS, prācī-sādhana in two bits.  `Dial = Bool × Bool`,
--      `turn` swaps, `shadow` reads the first coordinate.  Two states
--      share a shadow now (`one-shadow-underdetermines`) and are
--      separated at depth 1 (`two-shadows-determine`); the present
--      quotient is first-coordinate equality and the ORBIT QUOTIENT IS
--      EQUALITY (`orbit-quotient-is-discrete`) — two present blocks, four
--      orbit blocks, both exhibited.
--
--  §4  The two ports of `NaturalMachine.PhysicalLearningCore` are the two
--      sides of §2, checked as instances: the population port is
--      invariant hence a congruence, so its one-state quotient is already
--      predictive AT EVERY DEPTH — which that module proves only one step
--      at a time; the coherent port is NOT invariant and is a congruence
--      anyway.
--
--  §5  `NaturalMachine.GaugeOrbitClasses` §7 proves size buys no
--      separating power.  Here: neither does DEPTH.  A gauge element in
--      qs^⊥ makes the transcript reading invariant, hence a congruence,
--      hence iterating it splits no observable class at any depth
--      (`neutral-gauge-adds-no-depth`), instantiated on the total flip
--      and probe-6.
--  §6  A reading that is not invariant under the step need not be
--      refined by the orbit: `non-invariance-does-not-imply-orbit-refinement`.
------------------------------------------------------------------------

module NaturalMachine.PraciSadhana_OneShadowUnderdeterminesAndTheOrbitQuotientCoincidesWithThePresentExactlyOnACongruence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.List using (List)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator using (Signs ; Number ; obs)
open import ChargeCriterion using (probe-6)
open import GaugeOrbitClasses
  using (Gauge ; _⋆_ ; AllNeutral ; obs-agree⋆ ; τ₋
        ; τ₋-is-neutral-for-probe-6)
open import PhysicalLearningCore
  using (Phase ; Action ; evolve ; Port ; population ; coherent ; observe)
  renaming (flip to flipAction)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- §1  A aku reading: a state space, a step, and one shadow.
--
-- `step` is the motion between readings; `read` is what the instrument
-- returns.  `Present` is the fibre of one reading.  `Orbit` is the fibre
-- of the reading taken at every depth of the motion.
------------------------------------------------------------------------

module Reading {S : Type ℓ} {O : Type ℓ'} (step : S → S) (read : S → O) where

  orbit : ℕ → S → S
  orbit zero    s = s
  orbit (suc k) s = step (orbit k s)

  -- one shadow
  Present : S → S → Type ℓ'
  Present s s' = read s ≡ read s'

  -- the shadow traced along the motion
  Orbit : S → S → Type ℓ'
  Orbit s s' = (k : ℕ) → read (orbit k s) ≡ read (orbit k s')

  -- Unconditional, and it is the whole of the easy direction: the
  -- forenoon mark is already one of the readings the orbit takes.
  orbit-refines-present : (s s' : S) → Orbit s s' → Present s s'
  orbit-refines-present s s' h = h zero

  ----------------------------------------------------------------------
  -- §2  The criterion.
  ----------------------------------------------------------------------

  Congruence : Type (ℓ-max ℓ ℓ')
  Congruence = (s s' : S) → read s ≡ read s' → read (step s) ≡ read (step s')

  Invariant : Type (ℓ-max ℓ ℓ')
  Invariant = (s : S) → read (step s) ≡ read s

  PresentIsOrbit : Type (ℓ-max ℓ ℓ')
  PresentIsOrbit = (s s' : S) → Present s s' → Orbit s s'

  -- forward: induction on depth, the congruence applied at each mark
  congruence→present-is-orbit : Congruence → PresentIsOrbit
  congruence→present-is-orbit c s s' p zero    = p
  congruence→present-is-orbit c s s' p (suc k) =
    c (orbit k s) (orbit k s') (congruence→present-is-orbit c s s' p k)

  -- reverse: evaluation at depth one.  Nothing deeper is needed, which is
  -- why the criterion is about a single step and not about the tail.
  present-is-orbit→congruence : PresentIsOrbit → Congruence
  present-is-orbit→congruence h s s' p = h s s' p 1

  praci-criterion : (Congruence → PresentIsOrbit) × (PresentIsOrbit → Congruence)
  praci-criterion = congruence→present-is-orbit , present-is-orbit→congruence

  invariant→congruence : Invariant → Congruence
  invariant→congruence inv s s' p = inv s ∙ p ∙ sym (inv s')

  invariant→present-is-orbit : Invariant → PresentIsOrbit
  invariant→present-is-orbit inv = congruence→present-is-orbit (invariant→congruence inv)

------------------------------------------------------------------------
-- §3  The witness: one shadow underdetermines.
--
-- Two bits, and the motion exchanges them.  The instrument reads the
-- first bit only.  This is the forenoon mark alone.
------------------------------------------------------------------------

Dial : Type₀
Dial = Bool × Bool

turn : Dial → Dial
turn (a , b) = (b , a)

shadow : Dial → Bool
shadow = fst

module Dialℛ = Reading turn shadow

-- The present reading is exactly first-coordinate agreement: two blocks.
present-quotient-is-the-first-coordinate :
  (s s' : Dial) → Dialℛ.Present s s' ≡ (fst s ≡ fst s')
present-quotient-is-the-first-coordinate s s' = refl

-- The forenoon marks coincide …
one-shadow-underdetermines : Dialℛ.Present (false , true) (false , false)
one-shadow-underdetermines = refl

-- … and the afternoon marks do not.
two-shadows-determine : ¬ (Dialℛ.Orbit (false , true) (false , false))
two-shadows-determine h = true≢false (h 1)

-- so the present fibre is not a congruence, and by §2 that is the only
-- reason it could fail to be the orbit fibre.
turn-is-not-a-congruence : ¬ Dialℛ.Congruence
turn-is-not-a-congruence c = true≢false (c (false , true) (false , false) refl)

-- THE ORBIT QUOTIENT IS EQUALITY: four blocks, against the present two.
-- Depth 0 supplies the first bit, depth 1 the second; nothing deeper is
-- used, and nothing deeper exists (the motion has period two).
orbit-quotient-is-discrete : (s s' : Dial) → Dialℛ.Orbit s s' → s ≡ s'
orbit-quotient-is-discrete (a , b) (a' , b') h = ΣPathP (h 0 , h 1)

------------------------------------------------------------------------
-- §4  The two ports of `PhysicalLearningCore`, as instances of §2.
--
-- That module proves `population-collapses-phase` action by action and
-- `compile-step` one step at a time.  Neither is a statement about depth.
-- Below, both ports are handed to §2 with the flip action as the motion,
-- and the depth statement follows for each — from invariance at the
-- population port, and from congruence WITHOUT invariance at the coherent
-- port, which is §6's point in situ.
------------------------------------------------------------------------

module Popℛ = Reading (evolve flipAction) (observe population)
module Cohℛ = Reading (evolve flipAction) (observe coherent)

population-is-invariant : Popℛ.Invariant
population-is-invariant s = refl

-- The one-state population quotient is predictive at EVERY depth.
population-quotient-is-already-predictive : Popℛ.PresentIsOrbit
population-quotient-is-already-predictive =
  Popℛ.invariant→present-is-orbit population-is-invariant

-- The coherent port is not invariant: the flip moves the reading.
coherent-is-not-invariant : ¬ Cohℛ.Invariant
coherent-is-not-invariant inv = true≢false (inv false)

-- …and it is a congruence all the same.
coherent-is-a-congruence : Cohℛ.Congruence
coherent-is-a-congruence s s' p = cong not p

coherent-quotient-is-already-predictive : Cohℛ.PresentIsOrbit
coherent-quotient-is-already-predictive =
  Cohℛ.congruence→present-is-orbit coherent-is-a-congruence

------------------------------------------------------------------------
-- §5  Depth buys no separating power either.
--
-- `GaugeOrbitClasses` §7: appending arbitrarily large square queries
-- splits no observable class — size is not partial charge.  The same
-- statement one axis over: translating repeatedly by a gauge element of
-- qs^⊥ splits no observable class, at any depth.  `obs-agree⋆` makes the
-- transcript reading invariant under that step, and §2 does the rest.
--
-- This is not a new fact about the gauge group; it is §2 applied to it,
-- and the reason it is short is that `obs-agree⋆` was already there.
------------------------------------------------------------------------

neutral-gauge-adds-no-depth :
    (τ : Gauge) (qs : List Number) → AllNeutral τ qs
  → Reading.PresentIsOrbit (τ ⋆_) (λ ρ → obs ρ qs)
neutral-gauge-adds-no-depth τ qs h =
  Reading.invariant→present-is-orbit (τ ⋆_) (λ ρ → obs ρ qs)
    (λ σ → sym (obs-agree⋆ τ σ qs h))

module Probe6ℛ = Reading (τ₋ ⋆_) (λ ρ → obs ρ probe-6)

-- The total flip, iterated, never splits a probe-6 class.
total-flip-adds-no-depth-on-probe-6 : Probe6ℛ.PresentIsOrbit
total-flip-adds-no-depth-on-probe-6 =
  neutral-gauge-adds-no-depth τ₋ probe-6 τ₋-is-neutral-for-probe-6

------------------------------------------------------------------------
-- §6  Non-invariance does not imply orbit refinement.
--
-- The coherent port of `PhysicalLearningCore` is the counterexample:
-- `evolve flip` is `not` and `observe coherent` is the identity.  The
-- reading is not invariant (`coherent-is-not-invariant`, §4) and the
-- orbit refines nothing (`coherent-quotient-is-already-predictive`, §4).
------------------------------------------------------------------------

non-invariance-does-not-imply-orbit-refinement :
  (¬ Cohℛ.Invariant) × Cohℛ.PresentIsOrbit
non-invariance-does-not-imply-orbit-refinement =
  coherent-is-not-invariant , coherent-quotient-is-already-predictive

------------------------------------------------------------------------
-- INVARIANCE AGAINST CONGRUENCE.
--
-- Invariance is sufficient for the quotients to coincide and is not
-- necessary.  What is necessary and sufficient is congruence (§2), which
-- is strictly weaker: `coherent-is-a-congruence` holds where
-- `Cohℛ.Invariant` is refuted.  The .py file's lemma is therefore sound
-- and its hypothesis is not the boundary; the boundary is one step over,
-- and the "false control" there is a case, not the criterion.
--
-- In the instrument: a reading can move with the sun and still lose
-- nothing to a second reading — that is a reading whose motion is
-- determined by the reading itself.  The prc-sdhana needs its second
-- mark precisely because the shadow's direction is NOT determined by the
-- shadow's length; §3 is that failure in two bits.
------------------------------------------------------------------------

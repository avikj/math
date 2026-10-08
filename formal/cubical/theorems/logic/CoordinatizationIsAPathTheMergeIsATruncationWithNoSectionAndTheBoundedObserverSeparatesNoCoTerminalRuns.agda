{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CoordinatizationIsAPathTheMergeIsATruncationWithNoSectionAndTheBoundedObserverSeparatesNoCoTerminalRuns
--
-- A New Kind of Science, under univalence.  Four of Wolfram's exact
-- sentences, each held to a checked term, over the smallest multiway
-- system that has all four phenomena.  The sentences, verbatim:
--
--   W1. "Each [computational system] can be thought of as defining a
--       different coordinate system for describing the ruliad ...
--       each will ultimately lead to the same limiting object."
--       (The Concept of the Ruliad, 2021)
--   W2. "Whenever we said that two paths in the ruliad 'merge', that's
--       really just saying that we treat the outcomes as equivalent."
--       (The Concept of the Ruliad, 2021)
--   W3. "Because we are computationally bounded observers who imagine
--       a certain coherence in their experience, there are strong
--       constraints on what kinds of equivalence classes we can use."
--       (The Concept of the Ruliad, 2021; the same equivalencing is
--       Observer Theory, 2023: "a large set of possible inputs, a
--       much smaller set of possible outputs".)
--   W4. "Causal invariance can be thought of as being associated with
--       paths of history that diverge, eventually converging again."
--       (The Concept of the Ruliad, 2021)
--
-- THE SYSTEM.  A unary NKS substitution system: states are unary
-- strings, and there are two updating events — append one cell,
-- append two.  Its multiway evolutions from a to b form an indexed
-- inductive type; distinct evolutions between the same endpoints exist
-- and are SEPARATED BY A COMPUTED INVARIANT, not assumed distinct.
--
-- W1 IS A PATH IN THE UNIVERSE (§3).  The same system is presented in
-- two coordinate systems: unary tapes (Tape) and numbers (ℕ).  The
-- coordinate change is an equivalence; univalence turns it into a path
-- ua; and the two STRUCTURED systems — carrier together with both
-- updating events — are connected by a single path in the type of
-- systems (`coordinateChange`, built with ua→ and ua-gluePath, the
-- commuting datum being refl in both components).  Consequently EVERY
-- property of systems transports across the coordinate change by
-- subst, with no re-proof (`propertiesCross`), and the emulation map
-- that "moves" between the two coordinate systems is not postulated
-- beside the path — it IS the path's transport, and it COMPUTES to the
-- coding function (`transportComputes`, by uaβ).  "The same limiting
-- object" is then not agreement-after-inspection but contractibility:
-- the space of coordinatizations of the fixed carrier, each carrying
-- its own identification, is a point (`oneLimitingObject`, by EquivContr —
-- univalence again).  No coordinate system is privileged, and the
-- choice of one costs nothing that transport does not refund.
--
-- W2 IS PROPOSITIONAL TRUNCATION (§4).  The observer's single thread
-- is ∥ Evolve a b ∥₁.  Two named evolutions 0 → 3 — one-then-two, and
-- two-then-one — are proved distinct by the invariant that reads the
-- first updating event (`routesDistinct`), and proved merged by the
-- squash (`merged`).  The merge is therefore real and really lossy,
-- and the loss is exhibited as the branchial pair: two distinct
-- residents of the fibre of ∣_∣₁ over the one merged point
-- (`branchialPair`).  The pair of runs IS the fibre content of the
-- merge — branchial structure as a computed object.
--
-- W3 IS A QUANTIFICATION OVER ALL CONSUMERS (§5).  Any observer that
-- reads only the merged thread — any g : ∥ Evolve 0 3 ∥₁ → X, for
-- every X at every universe level — returns equal answers on the two
-- branches (`boundedObserver`).  And the constraint is not repairable
-- downstream: the merge has NO SECTION — a selector reading a run
-- back out of the thread contradicts the branch distinction
-- (`noSection`).  Equivalencing is many-to-one with the
-- many exhibited, and the one-to-many direction is refuted, not
-- merely absent.  This is also computational irreducibility in its
-- proof-relevant form: the outcome (the endpoint, and even the whole
-- merged thread) does not determine the run, so route information
-- must be carried, since it provably cannot be reconstructed.
--
-- W4 IS DIVERGENCE WITH EXHIBITED RECONVERGENCE (§2).  From every
-- state, the two updating events diverge — one cell apart after one
-- event — and both orders complete to the same state three cells on,
-- with the endpoint agreement DEFINITIONAL (`bothOrdersConverge`, both
-- components refl).  This is the interchange law at the smallest
-- scale: order-independence of co-initial updating events as data.
--
-- RELATION TO THE CORPUS.  Abstract 07 proves
-- the W2/W3 pair for a reversible process calculus (observation
-- factors through truncation; the scheduler is forbidden to merge);
-- abstract 22 proves W3 as full abstraction (the denotation IS the
-- truncation); abstract 06 proves the no-reconstruction half of W3
-- for derivations (soundness factors through the truncation, and the
-- truncation is strict); abstract 25 holds the W1 pole at the machine
-- scale (codes modulo running-the-same, the padding injection
-- ℕ → Code onto one behaviour point, determinism as contractibility,
-- and the strict UTM ⊊ interactive inclusion).  This module adds the
-- statement none of those makes: the coordinatization sentence W1
-- itself, as a path of structured systems whose transport computes,
-- with the one-object claim as contractibility.
------------------------------------------------------------------------

module CoordinatizationIsAPathTheMergeIsATruncationWithNoSectionAndTheBoundedObserverSeparatesNoCoTerminalRuns where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; ua→ ; ua-gluePath ; uaβ ; EquivContr)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)

------------------------------------------------------------------------
-- 1 · the multiway system: two updating events on unary strings.
------------------------------------------------------------------------

-- the ℕ coordinate system: a state is the string's length; the two
-- updating events append one cell and two cells.
event₁ event₂ : ℕ → ℕ
event₁ n = suc n
event₂ n = suc (suc n)

-- a multiway evolution from a to b: at each state, either halt or
-- apply one of the two updating events and continue.
data Evolve : ℕ → ℕ → Type where
  halt : (n : ℕ) → Evolve n n
  ev₁  : {m n : ℕ} → Evolve (event₁ m) n → Evolve m n
  ev₂  : {m n : ℕ} → Evolve (event₂ m) n → Evolve m n

------------------------------------------------------------------------
-- 2 · W4: divergence with exhibited reconvergence, endpoints refl.
------------------------------------------------------------------------

-- from every state m the two orders of the two events diverge after
-- one event and reconverge at m+3; both completions are exhibited and
-- the endpoint agreement is definitional: the two runs inhabit the
-- SAME type, with no transport.
bothOrdersConverge : (m : ℕ) → Evolve m (suc (suc (suc m))) × Evolve m (suc (suc (suc m)))
bothOrdersConverge m = ev₁ (ev₂ (halt _)) , ev₂ (ev₁ (halt _))

------------------------------------------------------------------------
-- 3 · W1: coordinatization is a path, and there is one limiting object.
------------------------------------------------------------------------

-- the second coordinate system: the unary tape itself.
data Tape : Type where
  blank : Tape
  cell  : Tape → Tape

-- the two updating events, in tape coordinates.
write₁ write₂ : Tape → Tape
write₁ t = cell t
write₂ t = cell (cell t)

-- the coordinate change, an equivalence by two inductions.
toNumber : Tape → ℕ
toNumber blank    = zero
toNumber (cell t) = suc (toNumber t)

toTape : ℕ → Tape
toTape zero    = blank
toTape (suc n) = cell (toTape n)

toNumber-toTape : (n : ℕ) → toNumber (toTape n) ≡ n
toNumber-toTape zero    = refl
toNumber-toTape (suc n) = cong suc (toNumber-toTape n)

toTape-toNumber : (t : Tape) → toTape (toNumber t) ≡ t
toTape-toNumber blank    = refl
toTape-toNumber (cell t) = cong cell (toTape-toNumber t)

coordinates : Tape ≃ ℕ
coordinates = isoToEquiv (iso toNumber toTape toNumber-toTape toTape-toNumber)

-- a system is a carrier with its two updating events.
System : Type₁
System = Σ[ S ∈ Type ] (S → S) × (S → S)

tapeSystem numberSystem : System
tapeSystem    = Tape , write₁ , write₂
numberSystem = ℕ    , event₁ , event₂

-- W1 AS A TERM: the two coordinate systems are ONE PATH in the type
-- of systems.  The carrier path is ua; the event components ride over
-- it by ua→, and the commuting datum in each is refl, because the
-- coding function sends cell to suc definitionally.
coordinateChange : tapeSystem ≡ numberSystem
coordinateChange i =
  ua coordinates i ,
  ua→ {e = coordinates} {B = λ i → ua coordinates i} {f₀ = write₁} {f₁ = event₁}
      (λ t → ua-gluePath coordinates refl) i ,
  ua→ {e = coordinates} {B = λ i → ua coordinates i} {f₀ = write₂} {f₁ = event₂}
      (λ t → ua-gluePath coordinates refl) i

-- consequently every property of systems crosses the coordinate
-- change by transport, with no re-proof.
propertiesCross : (P : System → Type) → P tapeSystem → P numberSystem
propertiesCross P = subst P coordinateChange

-- instantiated: the interchange of the two events, proved in tape
-- coordinates by refl, is delivered in number coordinates by subst.
writesCommute : (t : Tape) → write₁ (write₂ t) ≡ write₂ (write₁ t)
writesCommute t = refl

eventsCommute : (n : ℕ) → event₁ (event₂ n) ≡ event₂ (event₁ n)
eventsCommute =
  propertiesCross (λ (S , e₁ , e₂) → (s : S) → e₁ (e₂ s) ≡ e₂ (e₁ s))
                writesCommute

-- the emulation that "moves" between the coordinate systems is the
-- path's own transport, and it computes to the coding function.
transportComputes : (t : Tape) → transport (ua coordinates) t ≡ toNumber t
transportComputes = uaβ coordinates

-- and "the same limiting object": the space of coordinatizations of
-- the fixed carrier, each carrying its identification, is a point.
oneLimitingObject : isContr (Σ[ S ∈ Type ] (S ≃ ℕ))
oneLimitingObject = EquivContr ℕ

------------------------------------------------------------------------
-- 4 · W2: the merge is a truncation, and the branchial pair is its
--        fibre content.
------------------------------------------------------------------------

-- two evolutions 0 → 3: one-then-two, and two-then-one.
route₁ route₂ : Evolve zero (suc (suc (suc zero)))
route₁ = fst (bothOrdersConverge zero)
route₂ = snd (bothOrdersConverge zero)

-- the invariant that reads the first updating event.
firstEvent : {a b : ℕ} → Evolve a b → Bool
firstEvent (halt _) = true
firstEvent (ev₁ _)  = true
firstEvent (ev₂ _)  = false

-- the branches are DISTINCT, by the invariant --
routesDistinct : ¬ route₁ ≡ route₂
routesDistinct p = true≢false (cong firstEvent p)

-- and MERGED in the observer's single thread.
merge : {a b : ℕ} → Evolve a b → ∥ Evolve a b ∥₁
merge = ∣_∣₁

merged : merge route₁ ≡ merge route₂
merged = squash₁ _ _

-- the branchial pair: two distinct residents of the fibre of the
-- merge over the one merged point.
branchialFibre : Type
branchialFibre = Σ[ r ∈ Evolve zero (suc (suc (suc zero))) ]
              merge r ≡ merge route₁

branchialPair : branchialFibre × branchialFibre
branchialPair = (route₁ , refl) , (route₂ , squash₁ _ _)

branchialPairDistinct : ¬ fst branchialPair ≡ snd branchialPair
branchialPairDistinct p = routesDistinct (cong fst p)

------------------------------------------------------------------------
-- 5 · W3: the bounded observer separates nothing co-terminal, and the
--        merge has no section.
------------------------------------------------------------------------

-- any consumer of the single thread — every X, every universe level —
-- answers equally on the two branches.
boundedObserver : {ℓ : Level} {X : Type ℓ}
             (g : ∥ Evolve zero (suc (suc (suc zero))) ∥₁ → X)
           → g (merge route₁) ≡ g (merge route₂)
boundedObserver g = cong g merged

-- and no consumer reads a run back out: a section of the merge would
-- collapse the branch distinction.
noSection :
  ¬ (Σ[ sel ∈ (∥ Evolve zero (suc (suc (suc zero))) ∥₁
               → Evolve zero (suc (suc (suc zero)))) ]
       ((r : Evolve zero (suc (suc (suc zero)))) → sel (merge r) ≡ r))
noSection (sel , h) =
  routesDistinct (sym (h route₁) ∙ cong sel merged ∙ h route₂)

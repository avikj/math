{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheLawBelongsInTheRecordAndTheCertificateComposesAlongAChain
--
-- `ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem` composes
-- a four-component certificate whose migration is a bare function.
-- This module adds the law to the record, leaving that one's 
-- untouched.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   LCertified d e      FIVE components: boundary semantics preserved,
--                       cost strictly improved, a migration, THE LAW
--                       that the migration preserves the observation,
--                       provenance
--   composeLCertified   the five-component certificate composes
--   Chain d e           a NON-EMPTY sequence of certified rewrites
--   chainCertified      a whole chain is one certificate — so the five
--                       components compose along an arbitrary rewrite
--                       sequence, not only across two steps
--   chainMovesNoObservation
--                       after ANY chain, the migrated state is observed
--                       exactly as the original was
--   chainTransportsEveryInvariant
--                       and so is every function of the observation
--   chainImproves       a chain strictly improves the cost
--   noSelfChain         hence no chain returns to its start
--   theLawIsIndependentOfTheOtherFour
--                       a pair that satisfies ALL FOUR of the earlier
--                       module's components and FAILS the law
--
-- **THE LAST ONE IS WHY THIS IS A STRENGTHENING AND NOT A
-- REPACKAGING.**  `MigrationNeedsALawAndTheLawIsNotFree` showed that
-- SOME function fails the law — which leaves open the cheap reading
-- that the other four components already force it, so that adding it
-- costs nothing.  They do not: the witness below is a genuine element
-- of the earlier `Certified` (its semantics path is `refl`, its cost
-- strictly improves, it migrates, it carries provenance) whose
-- migration is `not`.  So the four-component record admits certificates
-- whose migration destroys every observation, and the fifth component
-- is a real constraint on which rewrites are certifiable.
--
-- ────────────────────────────────────────────────────────────────────
-- ON `Chain` BEING NON-EMPTY, which is a structural fact and not an
-- oversight.  `noSelfChain` says no chain runs from a system to itself.
-- If `Chain` had an empty constructor that would be false — the empty
-- chain at `d` is a `Chain d d` — so certified rewrites form a
-- SEMICATEGORY, not a category: composition is associative and total,
-- and there is no identity.  Strict cost improvement is exactly what
-- removes the identities.
--
-- NO NOVELTY.  Simulation/refinement squares, their composition, and
-- the fact that a strict order has no loops are all standard; the
-- content is again only the count — the law is the component that does
-- NOT come for free and does NOT follow from the others.
------------------------------------------------------------------------

module TheLawBelongsInTheRecordAndTheCertificateComposesAlongAChain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (zero-≤ ; ¬-<-zero)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; false≢true)
open import Cubical.Relation.Nullary using (¬_)

open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy)
open import ANonEmptyArchiveHasANonEmptyStratum
  using (⊏-irrefl ; ⊏-trans)
open import MigrationNeedsALawAndTheLawIsNotFree
  using (Lawful ; composeLawful)
open import ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem
  using (Certified)

------------------------------------------------------------------------
-- 1.  The five-component certificate
------------------------------------------------------------------------

module _ {Sys B O Prov : Type}
         (sem  : Sys → B)
         (cost : Sys → List ℕ)
         (M    : Sys → Type)
         (obs  : (d : Sys) → M d → O)
  where

  LCertified : Sys → Sys → Type
  LCertified d e =
    Σ[ mg ∈ (M d → M e) ]
        (sem e ≡ sem d)
      × (StrictlyDominatedBy (cost d) (cost e))
      × (Lawful M obs d e mg)
      × (List Prov)

  mig : {d e : Sys} → LCertified d e → (M d → M e)
  mig c = fst c

  improves : {d e : Sys} → LCertified d e → StrictlyDominatedBy (cost d) (cost e)
  improves c = fst (snd (snd c))

  law : {d e : Sys} (c : LCertified d e) → Lawful M obs d e (mig c)
  law c = fst (snd (snd (snd c)))

  composeLCertified :
    (d e f : Sys) → LCertified d e → LCertified e f → LCertified d f
  composeLCertified d e f (mg₁ , sde , imp₁ , law₁ , prov₁)
                          (mg₂ , sef , imp₂ , law₂ , prov₂) =
      (λ m → mg₂ (mg₁ m))
    , sef ∙ sde
    , ⊏-trans (cost d) (cost e) (cost f) imp₁ imp₂
    , composeLawful M obs d e f mg₁ mg₂ law₁ law₂
    , prov₁ ++ prov₂

  ------------------------------------------------------------------
  -- 2.  A non-empty chain of rewrites is one certificate
  ------------------------------------------------------------------

  data Chain : Sys → Sys → Type where
    one : {d e : Sys} → LCertified d e → Chain d e
    _◅_ : {d e f : Sys} → LCertified d e → Chain e f → Chain d f

  chainCertified : {d e : Sys} → Chain d e → LCertified d e
  chainCertified (one c)  = c
  chainCertified (c ◅ cs) = composeLCertified _ _ _ c (chainCertified cs)

  chainMovesNoObservation :
    {d e : Sys} (c : Chain d e) (m : M d)
    → obs e (mig (chainCertified c) m) ≡ obs d m
  chainMovesNoObservation c m = law (chainCertified c) m

  chainTransportsEveryInvariant :
    {C : Type} (g : O → C) {d e : Sys} (c : Chain d e) (m : M d)
    → g (obs e (mig (chainCertified c) m)) ≡ g (obs d m)
  chainTransportsEveryInvariant g c m = cong g (chainMovesNoObservation c m)

  chainImproves :
    {d e : Sys} (c : Chain d e) → StrictlyDominatedBy (cost d) (cost e)
  chainImproves c = improves (chainCertified c)

  noSelfChain : (d : Sys) → ¬ Chain d d
  noSelfChain d c = ⊏-irrefl (cost d) (chainImproves c)

------------------------------------------------------------------------
-- 3.  The law does not follow from the other four
--
-- Two systems, both with state space `Bool`, observed by the identity,
-- with a constant boundary semantics and a strictly improving cost.
-- `not` migrates the state and satisfies every component of the earlier
-- `Certified`; it destroys the observation.
------------------------------------------------------------------------

semB : Bool → Unit
semB _ = tt

costB : Bool → List ℕ
costB true  = 0 ∷ []
costB false = 1 ∷ []

stateB : Bool → Type
stateB _ = Bool

obsB : (d : Bool) → stateB d → Bool
obsB _ b = b

costImproves : StrictlyDominatedBy (costB true) (costB false)
costImproves = (zero-≤ , tt) , λ z → ¬-<-zero (fst z)

anUnlawfulFourComponentCertificate : Certified {Prov = ℕ} semB costB stateB true false
anUnlawfulFourComponentCertificate = refl , costImproves , not , []

theLawIsIndependentOfTheOtherFour :
  ¬ (Lawful stateB obsB true false not)
theLawIsIndependentOfTheOtherFour l = false≢true (l true)

------------------------------------------------------------------------
-- This record is the one the later work compares against:
--
-- `TheReachableLawDoesNotComposeWithoutPreservation`
-- shows that relativising the fifth component to reachable states
-- costs its free composition, and
-- `TheSixthComponentIsFreeToCarryAndIsWhatMakesTheFifthCompose`
-- adds the sixth component that buys it back — with
-- `aFullFiveComponentCertificateThatDoesNotPreserveTheInvariant`, an
-- element of the `LCertified` DEFINED ABOVE that fails only the new
-- component.  So this five-component record still admits certificates
-- whose migration leaves the invariant, exactly as the four-component
-- one admits certificates whose migration destroys the observation.
--
-- The chain construction above is NOT repeated there: the same
-- induction goes through verbatim with `composeRCertified` in place of
-- `composeLCertified`.
------------------------------------------------------------------------

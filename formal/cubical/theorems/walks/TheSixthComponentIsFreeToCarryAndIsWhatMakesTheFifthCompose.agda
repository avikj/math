{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheSixthComponentIsFreeToCarryAndIsWhatMakesTheFifthCompose
--
-- `TheReachableLawDoesNotComposeWithoutPreservation` shows that a
-- certificate carrying the reachable law must carry a
-- reachability-preservation component as well, or it does not survive
-- sequencing.  That is a SIXTH component, added here in a new module;
-- `LCertified` is left as it stands.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   RCertified d e     SIX components: boundary semantics, strict cost
--                      improvement, the migration, the law ON THE
--                      INVARIANT, PRESERVATION of the invariant,
--                      provenance
--   composePreserves   preservation composes for nothing — one
--                      application after another
--   composeRCertified  and so the whole six-component certificate
--                      composes
--   noSelfRCertified   still no certificate from a system to itself
--   aFullFiveComponentCertificateThatDoesNotPreserveTheInvariant
--                      an element of the FIVE-component `LCertified`
--                      — real cost improvement, real semantics path,
--                      globally lawful migration, provenance —
--                      whose migration leaves the invariant
--   preservationIsNotImpliedByTheOtherFive
--                      hence the sixth component is independent
--
-- **THE COUNT, FINALLY.**  Of the six, four are free (semantics path,
-- migration, preservation, provenance), one is earned by a theorem
-- proved elsewhere for another purpose (cost, by `⊏-trans`), and one
-- — the law on the invariant — composes ONLY BECAUSE the sixth is in
-- the record.  So preservation is free to carry and is not free to
-- omit: it costs nothing to compose and it is what makes the fifth
-- component compose at all.  That is a different kind of component
-- from any of the others, and it is invisible until the law is
-- relativised to reachable states.
--
-- The independence witness is built the way the fifth component's was:
-- not merely "some function fails preservation", which would leave
-- open that the other five exclude it, but a genuine element of the
-- earlier record that fails only the new component.  Its observation
-- type is `Unit`, so its migration is globally lawful — the strongest
-- form of the fifth component — and it still leaves the invariant.
--
------------------------------------------------------------------------

module TheSixthComponentIsFreeToCarryAndIsWhatMakesTheFifthCompose where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Relation.Nullary using (¬_)

open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy)
open import ANonEmptyArchiveHasANonEmptyStratum
  using (⊏-irrefl ; ⊏-trans)
open import TheReachableLawDoesNotComposeWithoutPreservation
  using (LawfulOn ; Preserves ; composeLawfulOn)
open import TheLawBelongsInTheRecordAndTheCertificateComposesAlongAChain
  using (LCertified ; semB ; costB ; stateB ; costImproves)

------------------------------------------------------------------------
-- 1.  The six-component certificate
------------------------------------------------------------------------

module _ {Sys B O Prov : Type}
         (sem  : Sys → B)
         (cost : Sys → List ℕ)
         (M    : Sys → Type)
         (obs  : (d : Sys) → M d → O)
         (R    : (d : Sys) → M d → Type)
  where

  RCertified : Sys → Sys → Type
  RCertified d e =
    Σ[ mg ∈ (M d → M e) ]
        (sem e ≡ sem d)
      × (StrictlyDominatedBy (cost d) (cost e))
      × (LawfulOn M obs R d e mg)
      × (Preserves M obs R d e mg)
      × (List Prov)

  composePreserves :
    (d e f : Sys) (mg₁ : M d → M e) (mg₂ : M e → M f)
    → Preserves M obs R d e mg₁ → Preserves M obs R e f mg₂
    → Preserves M obs R d f (λ m → mg₂ (mg₁ m))
  composePreserves d e f mg₁ mg₂ p₁ p₂ m r = p₂ (mg₁ m) (p₁ m r)

  composeRCertified :
    (d e f : Sys) → RCertified d e → RCertified e f → RCertified d f
  composeRCertified d e f (mg₁ , sde , imp₁ , law₁ , pre₁ , prov₁)
                          (mg₂ , sef , imp₂ , law₂ , pre₂ , prov₂) =
      (λ m → mg₂ (mg₁ m))
    , sef ∙ sde
    , ⊏-trans (cost d) (cost e) (cost f) imp₁ imp₂
    , composeLawfulOn M obs R d e f mg₁ mg₂ pre₁ law₁ law₂
    , composePreserves d e f mg₁ mg₂ pre₁ pre₂
    , prov₁ ++ prov₂

  noSelfRCertified : (d : Sys) → ¬ RCertified d d
  noSelfRCertified d (_ , _ , imp , _ , _ , _) = ⊏-irrefl (cost d) imp

------------------------------------------------------------------------
-- 2.  The sixth component is independent of the other five
--
-- The observation type is `Unit`, so EVERY migration satisfies the
-- fifth component in its strongest (global) form.  The invariant is
-- "the state is `true`"; the migration is the constant `false`.
------------------------------------------------------------------------

obsUnit : (d : Bool) → stateB d → Unit
obsUnit _ _ = tt

Inv : (d : Bool) → stateB d → Type
Inv _ m = m ≡ true

toFalse : stateB true → stateB false
toFalse _ = false

aFullFiveComponentCertificateThatDoesNotPreserveTheInvariant :
  LCertified {Prov = ℕ} semB costB stateB obsUnit true false
aFullFiveComponentCertificateThatDoesNotPreserveTheInvariant =
  toFalse , refl , costImproves , (λ m → refl) , []

preservationIsNotImpliedByTheOtherFive :
  ¬ (Preserves stateB obsUnit Inv true false toFalse)
preservationIsNotImpliedByTheOtherFive p = false≢true (p true refl)

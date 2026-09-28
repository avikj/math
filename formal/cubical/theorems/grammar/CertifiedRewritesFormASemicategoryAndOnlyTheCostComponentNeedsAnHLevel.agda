{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CertifiedRewritesFormASemicategoryAndOnlyTheCostComponentNeedsAnHLevel
--
-- ON THE NAME.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository); `formal/` and
-- invented.**  A semicategory law over certified rewrites has no Indian
-- source I have established; the h-level machinery is Voevodsky's
-- substrate, which this repository declares a tool and not a frame.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY THIS, AND WHY NOW — the rest on this line was LIFTED, with a
-- criterion, at `e52b933e`.  Associativity is named as not-done in
-- THREE modules written in THREE separate cycles
-- (`ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem`,
-- `MigrationNeedsALawAndTheLawIsNotFree`,
-- `TheLawBelongsInTheRecordAndTheCertificateComposesAlongAChain`), so
-- it is demanded from OUTSIDE the line rather than suggested by it, and
-- it is structural rather than another instance of the line's pattern.
-- If that distinction is a rationalisation, say so and put the rest
-- back on.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   isProp≼                 the product order on fitness vectors is
--                           proposition-valued, by induction — `Unit`,
--                           `⊥`, and `isProp≤` at the leaves
--   isPropStrictlyDominatedBy hence so is strict domination
--   composeIsAssociative    `composeCertified` is associative
--
-- **AND THE FOUR COMPONENTS PAY FOUR DIFFERENT PRICES, WHICH IS THE
-- CONTENT.**  Diagnostic (1) placed each before it was written and each
-- came out where predicted:
--
--   semantics   a PATH, so associativity is `assoc` — it holds UP TO A
--               PATH and not definitionally
--   cost        an H-LEVEL, and **this is the only component that could
--               have failed**: two bracketings of `⊏-trans` are two
--               different proof terms, and nothing makes them equal
--               except `StrictlyDominatedBy` being a proposition.  It is
--               one, and §1 proves it rather than assuming it
--   migration   DEFINITIONAL — `λ m → mig₃ (mig₂ (mig₁ m))` either way,
--               so `refl`
--   provenance  a LIBRARY LEMMA, `++-assoc`
--
-- So the answer to "does the composition associate" is yes, and the
-- interesting part is that the obstruction lives in exactly the
-- component that already needed a theorem for composition
-- (`⊏-trans`).  **The component that costs a theorem is the component
-- that costs an h-level.**  Nothing else on the record has proof
-- content to disagree about.
--
-- ────────────────────────────────────────────────────────────────────
-- **IT IS A SEMICATEGORY AND NOT A CATEGORY, AND THAT IS NOT A GAP.**
-- `noSelfRewrite` in the audited module proves `¬ Certified d d`: strict
-- cost improvement removes every identity.  So there is no unit law to
-- prove and none is missing; associativity is the whole of the
-- algebraic structure available here.
------------------------------------------------------------------------

module CertifiedRewritesFormASemicategoryAndOnlyTheCostComponentNeedsAnHLevel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (assoc)
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (isProp≤)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc)
open import Cubical.Data.Unit using (Unit ; isPropUnit)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; ΣPathP)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Relation.Nullary using (¬_ ; isProp¬)

open import AParetoFitnessHasNoBestAndEveryScalarisationAddsADecision
  using (_≼_)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy)
open import ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem
  using (Certified ; composeCertified)

------------------------------------------------------------------------
-- 1.  The cost order is proposition-valued
------------------------------------------------------------------------

isProp≼ : (v w : List ℕ) → isProp (v ≼ w)
isProp≼ []       []       = isPropUnit
isProp≼ []       (_ ∷ _)  = isProp⊥
isProp≼ (_ ∷ _)  []       = isProp⊥
isProp≼ (x ∷ xs) (y ∷ ys) = isProp× isProp≤ (isProp≼ xs ys)

isPropStrictlyDominatedBy :
  (v w : List ℕ) → isProp (StrictlyDominatedBy v w)
isPropStrictlyDominatedBy v w =
  isProp× (isProp≼ v w) (isProp¬ (w ≼ v))

------------------------------------------------------------------------
-- 2.  So the composition associates, one price per component
------------------------------------------------------------------------

module _ {Sys B Prov : Type}
         (sem  : Sys → B)
         (cost : Sys → List ℕ)
         (M    : Sys → Type)
  where

  private
    Cert : Sys → Sys → Type
    Cert = Certified {Prov = Prov} sem cost M

    cmp : (d e f : Sys) → Cert d e → Cert e f → Cert d f
    cmp = composeCertified sem cost M

  composeIsAssociative :
    (d e f g : Sys)
    (c₁ : Cert d e) (c₂ : Cert e f) (c₃ : Cert f g)
    → cmp d f g (cmp d e f c₁ c₂) c₃
      ≡ cmp d e g c₁ (cmp e f g c₂ c₃)
  composeIsAssociative d e f g
    (s₁ , i₁ , m₁ , p₁) (s₂ , i₂ , m₂ , p₂) (s₃ , i₃ , m₃ , p₃) =
    ΣPathP
      ( assoc s₃ s₂ s₁
      , ΣPathP
          ( isPropStrictlyDominatedBy (cost d) (cost g) _ _
          , ΣPathP (refl , ++-assoc p₁ p₂ p₃) ) )

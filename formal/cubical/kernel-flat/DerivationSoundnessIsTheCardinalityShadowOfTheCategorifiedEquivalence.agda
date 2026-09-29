{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DerivationSoundnessIsTheCardinalityShadow — the capstone of the
-- decategorification story.  Two modules established:
--   · `TheCountingSemanticsIsADecategorification…`: every Step is an
--     EQUIVALENCE, so a Derivation a b gives derivation-equiv : ⟦a⟧ ≃ ⟦b⟧
--     (the categorified semantics), and `eval`/`derivation-sound` is a
--     readout into a SET that keeps a cardinality and drops the bijection.
--   · `…IsTheCardinalityOfTheCategorifiedOne…`: card : ⟦t⟧(finEnv ρ) ≃
--     Fin (eval t ρ) — the counting value IS the cardinality of ⟦t⟧.
--
-- Put together, the kernel's ORIGINAL counting soundness is RECOVERED as
-- the π₀ / cardinality image of the categorified equivalence: a derivation
-- a ⇝ b gives a bijection ⟦a⟧ ≃ ⟦b⟧, whose two sides have cardinalities
-- eval a ρ and eval b ρ, and cardinality is injective on Fin — so
-- eval a ρ ≡ eval b ρ falls out, with NO appeal to `derivation-sound`.
--
-- WHAT IS PROVEN, --safe, no postulates:
--   soundnessFromCategorification
--        (d : Derivation a b)(ρ : Env) → eval a ρ ≡ eval b ρ, built ONLY
--        from derivation-equiv, card, and injectivity of Fin's cardinality
--        (SumFin≃Fin ∙ Fin-inj) — the counting soundness derived from the
--        univalent one.
--   recovers-derivation-sound
--        it agrees with the kernel's own derivation-sound (necessarily —
--        both land in ℕ, a set; the content is that the categorified route
--        is an independent construction giving the same equation, retaining
--        the bijection until the final cardinality step).
--
-- READING.  The counting semantics is not merely accompanied by a
-- categorified one; its SOUNDNESS is the shadow of the categorified
-- soundness under decategorification.  eval = cardinality; derivation-sound
-- = cardinality of derivation-equiv.  The bijection is present the whole
-- way and is collapsed only at the last step — "never discard the fibre",
-- at the level of the kernel's semantics.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module DerivationSoundnessIsTheCardinalityShadowOfTheCategorifiedEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEquiv ; compEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.SumFin using (Fin)
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
open import Cubical.Data.Fin.Properties using (Fin-inj)

open import Kernel.RewriteCertificate using (Tm ; Derivation ; Env ; eval ; derivation-sound)
open import TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry
  using (⟦_⟧ ; derivation-equiv)
open import TheCountingSemanticsIsTheCardinalityOfTheCategorifiedOneEveryTermsTypeIsFinOfItsEvaluation
  using (finEnv ; card)

------------------------------------------------------------------------
-- The counting soundness, reconstructed from the categorified semantics.
------------------------------------------------------------------------

soundnessFromCategorification :
  {a b : Tm} (d : Derivation a b) (ρ : Env) → eval a ρ ≡ eval b ρ
soundnessFromCategorification {a} {b} d ρ =
  Fin-inj (eval a ρ) (eval b ρ)
    (ua (compEquiv (invEquiv (SumFin≃Fin (eval a ρ)))
        (compEquiv finEquiv (SumFin≃Fin (eval b ρ)))))
  where
    -- the derivation's bijection, transported onto the cardinalities:
    -- Fin (eval a ρ) ≃ ⟦a⟧ ≃ ⟦b⟧ ≃ Fin (eval b ρ).
    finEquiv : Fin (eval a ρ) ≃ Fin (eval b ρ)
    finEquiv = compEquiv (invEquiv (card a ρ))
                 (compEquiv (derivation-equiv d (finEnv ρ)) (card b ρ))

-- it is the kernel's own soundness (both land in ℕ, a set).
recovers-derivation-sound :
  {a b : Tm} (d : Derivation a b) (ρ : Env)
  → soundnessFromCategorification d ρ ≡ derivation-sound d ρ
recovers-derivation-sound {a} {b} d ρ =
  isSetℕ (eval a ρ) (eval b ρ) _ _

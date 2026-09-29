{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- संक्रमण-श्रेणी — the localization sequence, as one object.
--
-- The sequence
--
--     ker L  →  Derivation  ──L──►  Ĝ  (meaning-only)
--
-- is built here as its exact load-bearing content: the
-- Gabriel–Zisman localization at the meaning-preserving class.  To
-- localize is to invert every rewrite a chosen invariant cannot see; the
-- set-quotient by "same meaning" IS that inversion, and it is enough to
-- state which invariants descend and which do not.
--
--   §0  THE LOCALIZATION.  For any f : X → Y (meaning) and c : X → ℕ
--       (cost),  = X / (a ≈ b := f a ≡ f b) inverts exactly the
--       f-preserving rewrites; L = [_] : X → Ĝ.
--   §1  MEANING DESCENDS (localizing invariant): f factors through L,
--       fDescends ∘ L ≡ f, definitionally — because the relation IS the
--       kernel of f (SetQuotients.rec on isSet Y).
--   §2  COST DOES NOT DESCEND (non-localizing): given a single witness of
--       two meaning-equal points of different cost, NO function on 
--       restricts to c along L.  One `eq/` collapses them; c separates
--       them; ⊥.  This is Laghava's "cost cannot exist on the groupoid"
--       localized to one map, as a term.
--
-- Instantiated on the kernel: f = derivation-sound (meaning), c = len
-- (cost), witness = the two coterminal histories direct/detour (same
-- meaning by meaning-agrees, lengths 2 ≠ 4).  So on the kernel's own
-- localization, meaning descends and cost does not — the sequence, one
-- object.  (The round trips of VyayaSesa are what L collapses: they and
-- `done` share the trivial meaning, so L identifies them while their
-- cost 2·len separates them — the kernel of L is exactly the cost cycles.)
--
------------------------------------------------------------------------

module Kernel.TransportShreni_TheLocalizationSequenceAsOneObjectMeaningDescendsAndCostDoesNot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients using (_/_ ; [_] ; eq/ ; rec)

private variable ℓ ℓ' : Level

------------------------------------------------------------------------
-- ० · The localization of a (meaning, cost) system.
------------------------------------------------------------------------

module Localization {X : Type ℓ} {Y : Type ℓ'} (isSetY : isSet Y)
                    (f : X → Y) (c : X → ℕ) where

  -- invert exactly the meaning-preserving rewrites.
  _≈_ : X → X → Type ℓ'
  a ≈ b = f a ≡ f b

  Ĝ : Type (ℓ-max ℓ ℓ')
  Ĝ = X / _≈_

  L : X → Ĝ
  L = [_]

  -- §1 · meaning descends: the localizing invariant.
  fDescends : Ĝ → Y
  fDescends = rec isSetY f (λ a b r → r)

  fFactors : (x : X) → fDescends (L x) ≡ f x
  fFactors x = refl

  -- §2 · cost does not descend: one witness of meaning-equal / cost-apart
  --      refutes every function on  that would restrict to c.
  costDoesNotDescend : (a b : X) → a ≈ b → ¬ (c a ≡ c b)
    → ¬ (Σ[ ℓc ∈ (Ĝ → ℕ) ] ((x : X) → ℓc (L x) ≡ c x))
  costDoesNotDescend a b a≈b ca≢cb (ℓc , factors) =
    ca≢cb (sym (factors a) ∙ cong ℓc (eq/ a b a≈b) ∙ factors b)

------------------------------------------------------------------------
-- The kernel instance: f = derivation-sound, c = len.
------------------------------------------------------------------------

open import Kernel.RewriteCertificate using (Tm ; Derivation ; Env ; eval ; derivation-sound)
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)
open import ForgetfulCompressionPricesTheDrop using (len ; 2≢4 ; meaning-agrees)

Meaning : Type
Meaning = (ρ : Env) → eval seed ρ ≡ eval target₀ ρ

isSetMeaning : isSet Meaning
isSetMeaning = isProp→isSet (isPropΠ (λ ρ → isSetℕ (eval seed ρ) (eval target₀ ρ)))

open Localization {X = Derivation seed target₀} {Y = Meaning}
                  isSetMeaning derivation-sound len
  public

-- meaning descends, on the nose:
kernelMeaningDescends : (d : Derivation seed target₀)
  → fDescends (L d) ≡ derivation-sound d
kernelMeaningDescends = fFactors

-- and cost does not: the two coterminal histories witness it.
kernelCostDoesNotDescend :
  ¬ (Σ[ ℓc ∈ (Ĝ → ℕ) ] ((d : Derivation seed target₀) → ℓc (L d) ≡ len d))
kernelCostDoesNotDescend =
  costDoesNotDescend direct-history detour-history
    (funExt meaning-agrees)     -- same meaning
    (λ p → 2≢4 p)               -- len 2 ≢ len 4

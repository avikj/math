{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Aresidue_TheWholeDerivationTypeIsOneFibre
--                      SoSoundnessIsNeverAnEquivalence
--
-- TERM.  अशेष · aśeṣa -- "without remainder", hence entire, complete, the
-- whole of it.  ORDINARY , NOT A TECHNICAL TERM, and the compound in
-- this file name IS BUILT HERE.
-- It is chosen for the pun the module
-- proves, which is exact rather than decorative -- the kernel's derivation is
-- *aea ea*, ENTIRELY remainder, without remainder left over as anything
-- else.  `Residue_…` proved the second word; this file proves the first.
--
------------------------------------------------------------------------
-- THE SYNTHESIS OF THE THREE READINGS, AS ONE LEMMA.
--
--   Vyapti_    NativeOperation.control-sound : Control t → t ≡ source
--   Residue_      RewriteCertificate.derivation-sound : D a b → eval a ρ ≡ eval b ρρ
--   Ankapasa_  and the repair is to categorify the codomain.
--
-- Every soundness field of this kernel is a map into an identity type of a
-- SET, hence into a proposition.  So the shape shared by all three findings
-- is one general fact about maps into propositions, and it is proved once in
-- §1 rather than three times by hand:
--
--   §1  fibre-is-everything.  If M is a proposition, then for EVERY m : M,
--       `fiber f m ≃ A`.  The fibre is not a part of the domain; it is the
--       domain.  Nothing at all sits underneath it.
--
--   §2  Instantiated: `Derivation a b ≃ fiber derivation-sound m`, for any
--       meaning m whatsoever.  The kernel's derivation type IS one fibre of
--       its own soundness.
--
--   §3  THE CONTRAST WITH THE ONE PRIMITIVE, which is the point of doing
--       this in this repository.  `fibre/src/Fibre/Carrier.agda`
--       is the fibre law: for f : A → B, BIND THE OUTPUT and the fibre is
--       `singl (f a)`, always contractible, so `A ≃ Carrier f` and the datum
--       rides free; BIND THE INPUT and it is `fiber f b`, the exact loss.
--       Two bindings, two prices.  §1-§2 say that for this kernel THE TWO
--       BINDINGS COINCIDE -- both give back the whole domain -- and that is
--       not two lucky facts but the single statement that soundness is
--       weakly constant.  The kernel sits at the maximally lossy end of the
--       fibre law: everything it computes is priced as loss, because its
--       output side has no room to hold anything.
--
--   §4  isEquiv IS THE MEASURE, and the kernel fails it on its own seed.
--       `machine/AtmaJnana…` reads `isEquiv f` as perfect self-knowledge:
--       every fibre contractible, nothing lost either way.  Here:
--       soundness-is-an-equivalence-only-if-the-route-was-unique -- if
--       `derivation-sound` were an equivalence, any two derivations with the
--       same endpoints would be EQUAL.  `Residue_…` §2 exhibits two that are
--       not, at the kernel's own `seed`/`target₀`.  So
--       soundness-is-not-an-equivalence-at-the-kernels-own-seed, and the
--       exact defect is the fibre of §2: the machine cannot recover its route
--       from its meaning, and the amount it cannot recover is all of it.
--
-- WHAT THIS SAYS ABOUT THE KERNEL, once, plainly.  A generator whose readout
-- is a proposition has a partition function equal to its support: it can say
-- THAT a continuation is correct and can say nothing about WHICH, or HOW
-- MANY, or HOW LONG.  Every quantity a policy would need lives in a fibre
-- that the readout, by its type, collapses.  This is why
-- `advance-preserves-branch-count` -- multiplicity conserved, no dedupe, no
-- sort, no quotient -- is not housekeeping: it is the only place in the
-- kernel where the collapsed information is still held.
------------------------------------------------------------------------

module Kernel.Asesa_TheWholeDerivationTypeIsOneFibreSoSoundnessIsNeverAnEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; isEquiv ; invEquiv ; compEquiv)
open import Cubical.Foundations.HLevels
  using (isPropΠ ; inhProp→isContr ; isOfHLevelRespectEquiv)
open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-contractSnd)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel using (seed ; target₀)
open import Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
  using (direct≢detour)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- §1.  THE LEMMA THE THREE READINGS SHARE.
--
-- A map into a proposition has no fibres in the plural.  Every fibre is the
-- whole domain, so "which fibre am I in" is not a question the codomain can
-- be asked -- which is exactly what it means for the map to carry no
-- information.
------------------------------------------------------------------------

fibre-is-everything :
  {A : Type ℓ} {M : Type ℓ'}
  → isProp M → (f : A → M) (m : M) → fiber f m ≃ A
fibre-is-everything {A = A} isPropM f m =
  Σ-contractSnd (λ a → inhProp→isContr (isPropM (f a) m)
                                       (isProp→isSet isPropM (f a) m))

------------------------------------------------------------------------
-- §2.  INSTANTIATED AT THE KERNEL.
------------------------------------------------------------------------

Meaning : Tm → Tm → Type₀
Meaning a b = (ρ : Env) → eval a ρ ≡ eval b ρ

isPropMeaning : (a b : Tm) → isProp (Meaning a b)
isPropMeaning a b = isPropΠ (λ ρ → isSetℕ (eval a ρ) (eval b ρ))

sound : (a b : Tm) → Derivation a b → Meaning a b
sound a b d = derivation-sound d

-- THE DERIVATION TYPE IS ONE FIBRE OF ITS OWN SOUNDNESS.
the-whole-derivation-type-is-one-fibre :
  (a b : Tm) (m : Meaning a b) → fiber (sound a b) m ≃ Derivation a b
the-whole-derivation-type-is-one-fibre a b m =
  fibre-is-everything (isPropMeaning a b) (sound a b) m

-- Which fibre you name makes no difference, because there is only the one.
-- (Stated because "the fibre over m" reads as a choice, and it is not.)
the-choice-of-meaning-is-no-choice :
  (a b : Tm) (m n : Meaning a b) → m ≡ n
the-choice-of-meaning-is-no-choice a b = isPropMeaning a b

------------------------------------------------------------------------
-- §3.  BOTH BINDINGS OF THE FIBRE LAW COINCIDE HERE.
--
-- `Carrier`'s source-binding always returns the domain.  §2 says the
-- target-binding does too.  The gap between the two readings -- which is
-- where the fibre law puts the price of a computation -- is empty for this
-- map, and that is the maximally lossy case, not the free one: the reason
-- nothing is charged on the output side is that the output side holds
-- nothing.
------------------------------------------------------------------------

both-bindings-agree :
  (a b : Tm) (m n : Meaning a b) → fiber (sound a b) m ≃ fiber (sound a b) n
both-bindings-agree a b m n =
  compEquiv (the-whole-derivation-type-is-one-fibre a b m)
            (invEquiv (the-whole-derivation-type-is-one-fibre a b n))

------------------------------------------------------------------------
-- §4.  isEquiv AS THE MEASURE, AND THE KERNEL'S OWN SEED FAILS IT.
------------------------------------------------------------------------

-- If soundness were an equivalence, the domain would inherit the codomain's
-- h-level: one route, or none.
soundness-is-an-equivalence-only-if-the-route-was-unique :
  (a b : Tm) → isEquiv (sound a b) → (d e : Derivation a b) → d ≡ e
soundness-is-an-equivalence-only-if-the-route-was-unique a b isEq =
  isOfHLevelRespectEquiv 1 (invEquiv (sound a b , isEq)) (isPropMeaning a b)

-- And it is not one, at the kernel's own seed: `GenerativeKernel` ships two
-- derivations there and `Residue_…` separates them by step count.
soundness-is-not-an-equivalence-at-the-kernels-own-seed :
  isEquiv (sound seed target₀) → ⊥
soundness-is-not-an-equivalence-at-the-kernels-own-seed isEq =
  direct≢detour
    (soundness-is-an-equivalence-only-if-the-route-was-unique seed target₀ isEq _ _)

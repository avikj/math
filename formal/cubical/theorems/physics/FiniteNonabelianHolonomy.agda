{-# OPTIONS --cubical --safe #-}

-- A finite, falsifiable nonabelian instance of the holonomy/refinement seam.
-- The group is Sym(Fin 3) ≅ S₃.  This is a precursor test only: it is not

module FiniteNonabelianHolonomy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.SumFin using (Fin ; fzero ; fsuc)
import Cubical.Data.Sum.Properties as Sum
import Cubical.Data.Prod as P
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
-- see NaturalMachine/PathIsSymmetry.agda: v0.9 calls this FinSymGroup and
-- the pinned v0.5 calls it Sym, so it is defined there once instead
open import PathIsSymmetry using (FinSymGroup)

open import NaturalMachine.RelationalHolonomyRefinement
  using (closedLoopGaugeInvariant)
open import OrientedSurfaceFlux
open import SurfaceFluxCylindricalSquare

Fin3 : Type₀
Fin3 = Fin 3

swap01fun : Fin3 → Fin3
swap01fun fzero = fsuc fzero
swap01fun (fsuc fzero) = fzero
swap01fun (fsuc (fsuc fzero)) = fsuc (fsuc fzero)

swap01Iso : Iso Fin3 Fin3
Iso.fun swap01Iso = swap01fun
Iso.inv swap01Iso = swap01fun
Iso.rightInv swap01Iso fzero = refl
Iso.rightInv swap01Iso (fsuc fzero) = refl
Iso.rightInv swap01Iso (fsuc (fsuc fzero)) = refl
Iso.leftInv swap01Iso = Iso.rightInv swap01Iso

swap12fun : Fin3 → Fin3
swap12fun fzero = fzero
swap12fun (fsuc fzero) = fsuc (fsuc fzero)
swap12fun (fsuc (fsuc fzero)) = fsuc fzero

swap12Iso : Iso Fin3 Fin3
Iso.fun swap12Iso = swap12fun
Iso.inv swap12Iso = swap12fun
Iso.rightInv swap12Iso fzero = refl
Iso.rightInv swap12Iso (fsuc fzero) = refl
Iso.rightInv swap12Iso (fsuc (fsuc fzero)) = refl
Iso.leftInv swap12Iso = Iso.rightInv swap12Iso

S₃ = FinSymGroup 3

s₀₁ s₁₂ : ⟨ S₃ ⟩
s₀₁ = isoToEquiv swap01Iso
s₁₂ = isoToEquiv swap12Iso

module S = GroupStr (snd S₃)
module ST = GroupTheory S₃

-- The two adjacent transpositions genuinely do not commute.  Evaluation at
-- vertex zero reduces the proposed equality to distinct constructors.
noncommuting : (s₀₁ S.· s₁₂ ≡ s₁₂ S.· s₀₁) → ⊥
noncommuting p = lower (Sum.⊎Path.encode (fsuc fzero) fzero inner)
  where
  inner : fsuc fzero ≡ fzero
  inner = lower (Sum.⊎Path.encode (fsuc (fsuc fzero)) (fsuc fzero)
    (cong (λ e → fst e fzero) p))

-- A deliberately minimal conjugation-invariant loop observation.  It records
-- only that a loop was observed; the point is that gauge invariance is checked
-- for the concrete nonabelian group; this is not a Wilson trace.
loopObserved : ⟨ S₃ ⟩ → Unit
loopObserved _ = tt

loopObserved-conjugation : (h g : ⟨ S₃ ⟩)
  → loopObserved ((h S.· g) S.· S.inv h) ≡ loopObserved g
loopObserved-conjugation h g = refl

loopObserved-gauge : (h g : ⟨ S₃ ⟩)
  → loopObserved
      (NaturalMachine.RelationalHolonomyRefinement.endpointGauge S₃ (P._,_ h h) g)
    ≡ loopObserved g
loopObserved-gauge =
  closedLoopGaugeInvariant S₃ loopObserved loopObserved-conjugation

-- Concrete signed target on S₃: parallel combination is group composition,
-- orientation negation is inversion, and the positive insertion is identity.
s₃SignedFlux : SignedFluxTarget ℓ-zero
SignedFluxTarget.Carrier s₃SignedFlux = ⟨ S₃ ⟩
SignedFluxTarget.neutral s₃SignedFlux = S.1g
SignedFluxTarget._⊕_ s₃SignedFlux = S._·_
SignedFluxTarget.negate s₃SignedFlux = S.inv
SignedFluxTarget.positive s₃SignedFlux g = g
SignedFluxTarget.left-neutral s₃SignedFlux = S.·IdL
SignedFluxTarget.right-neutral s₃SignedFlux = S.·IdR
SignedFluxTarget.negate-neutral s₃SignedFlux = ST.inv1g
SignedFluxTarget.negate-involutive s₃SignedFlux = ST.invInv

-- The generic theorem now specializes to an executable S₃ refinement square.
s₃-refinement-square =
  surface-flux-cylindrical S₃ s₃SignedFlux (λ g → g)

s₃-reversal-square =
  reversal-cylindrical-square S₃ s₃SignedFlux (λ g → g)

s₃-signed-sum-square =
  signed-sum-cylindrical S₃ s₃SignedFlux (λ g → g)

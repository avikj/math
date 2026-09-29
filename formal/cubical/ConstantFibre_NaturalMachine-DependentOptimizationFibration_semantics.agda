{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- तपस् — a MINTED fibre receipt.  Emitted by
-- machine/Tapas_TheTemplateIsTheProofShapeAndEveryNonMatchIsAWrittenRefusal.hs (absent from this repository)
-- from template T-CONST-BOOL.
--
-- THE EDGE:
--   DependentOptimizationFibration.Configuration  ⟶  ⟨lib⟩.Bool
--   « DependentOptimizationFibration.semantics
--
-- WHAT IS PROVED, following the structure of
-- Lopa_TheSumsFibreIsExactlyNPlusOneAndNoLeftInverseExists:
--   §1  over the constant's value false, the fibre IS the domain:
--       fiber semantics false ≃ Configuration.  A constant map loses
--       EVERYTHING, and the fibre says so exactly: the elided datum is
--       the whole input.
--   §2  off the value the fibre is EMPTY: ¬ fiber semantics true.
--       रिक्तम् — the third verdict, which a two-valued isContr check
--       conflates with §1's opposite.
--   §3  hence no section, and so certainly no left inverse in the other
--       role: nothing the map does can be undone, because half the
--       codomain is never reached.
--
------------------------------------------------------------------------

module ConstantFibre_NaturalMachine-DependentOptimizationFibration_semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Data.Bool using (Bool ; false ; true ; isSetBool ; false≢true)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import DependentOptimizationFibration using (Configuration ; semantics)

-- §1 · over the value: the fibre is the whole domain.
over-value : fiber semantics false ≃ Configuration
over-value = isoToEquiv i where
  i : Iso (fiber semantics false) Configuration
  Iso.fun i = fst
  Iso.inv i x = x , refl
  Iso.rightInv i x = refl
  Iso.leftInv i (x , p) j = x , isSetBool false false refl p j

-- §2 · off the value: the fibre is empty (रिक्तम्, the third verdict).
off-value : ¬ fiber semantics true
off-value (x , p) = false≢true p

-- §3 · no section: the map reaches half the codomain and no map back
-- can pretend otherwise.
no-section : (g : Bool → Configuration) → ((b : Bool) → semantics (g b) ≡ b) → ⊥
no-section g s = false≢true (s true)

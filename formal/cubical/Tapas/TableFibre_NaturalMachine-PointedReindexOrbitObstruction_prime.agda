{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- तपस् — a MINTED fibre receipt.  Emitted by
-- machine/Tapas_TheTemplateIsTheProofShapeAndEveryNonMatchIsAWrittenRefusal.hs (absent from this repository)
-- from template T-TABLE-BOOL-NAT.
--
-- THE EDGE:
--   ⟨lib⟩.Bool  ⟶  ⟨lib⟩.ℕ
--   « PointedReindexOrbitObstruction.prime
--
-- WHAT IS PROVED.  The map is the two-clause table false ↦ 2
--   , true ↦ 3, an INJECTION into ℕ:
--   §1  over each value the fibre is a SINGLE POINT (isContr): the
--       elided datum is nothing — the input is recoverable.
--   §2  off both values (witness 6) the fibre is EMPTY.
--   §3  hence no section: two points of image, infinitely many targets.
--
------------------------------------------------------------------------

module Tapas.TableFibre_NaturalMachine-PointedReindexOrbitObstruction_prime where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; znots ; _∸_)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Relation.Nullary using (¬_)

open import PointedReindexOrbitObstruction using (prime)

-- the three distinctness facts, one discriminator shape
neq-f-t : ¬ Path ℕ 2 3
neq-f-t = λ p → znots (cong (_∸ 2) p)
neq-t-f : ¬ Path ℕ 3 2
neq-t-f = λ p → znots (cong (_∸ 2) (sym p))
neq-f-c : ¬ Path ℕ 2 6
neq-f-c = λ p → znots (cong (_∸ 2) p)
neq-t-c : ¬ Path ℕ 3 6
neq-t-c = λ p → znots (cong (_∸ 3) p)

-- §1 · over each value the fibre is a point: nothing is elided.
over-false : isContr (fiber prime 2)
over-false = (false , refl) , same where
  same : (y : fiber prime 2) → (false , refl) ≡ y
  same (false , p) i = false , isSetℕ 2 2 refl p i
  same (true  , p) = ⊥rec (neq-t-f p)

over-true : isContr (fiber prime 3)
over-true = (true , refl) , same where
  same : (y : fiber prime 3) → (true , refl) ≡ y
  same (true  , p) i = true , isSetℕ 3 3 refl p i
  same (false , p) = ⊥rec (neq-f-t p)

-- §2 · off both values the fibre is empty (रिक्तम्).
off-both : ¬ fiber prime 6
off-both (false , p) = neq-f-c p
off-both (true  , p) = neq-t-c p

-- §3 · no section: the image has two points and ℕ does not.
no-section : (g : ℕ → Bool) → ((n : ℕ) → prime (g n) ≡ n) → ⊥
no-section g s = off-both (g 6 , s 6)

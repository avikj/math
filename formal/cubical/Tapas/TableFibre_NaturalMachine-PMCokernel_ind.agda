{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- तपस् — a MINTED fibre receipt.  Emitted by
-- machine/Tapas_TheTemplateIsTheProofShapeAndEveryNonMatchIsAWrittenRefusal.hs (absent from this repository)
-- from template T-TABLE-BOOL-NAT.
--
-- THE EDGE:
--   ⟨lib⟩.Bool  ⟶  ⟨lib⟩.ℕ
--   « NaturalMachine.PMCokernel.ind
--
-- WHAT IS PROVED.  The map is the two-clause table false ↦ 0
--   , true ↦ 1, an INJECTION into ℕ:
--   §1  over each value the fibre is a SINGLE POINT (isContr): the
--       elided datum is nothing — the input is recoverable.
--   §2  off both values (witness 2) the fibre is EMPTY.
--   §3  hence no section: two points of image, infinitely many targets.
--
------------------------------------------------------------------------

module Tapas.TableFibre_NaturalMachine-PMCokernel_ind where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; znots ; _∸_)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.PMCokernel using (ind)

-- the three distinctness facts, one discriminator shape
neq-f-t : ¬ Path ℕ 0 1
neq-f-t = λ p → znots (cong (_∸ 0) p)
neq-t-f : ¬ Path ℕ 1 0
neq-t-f = λ p → znots (cong (_∸ 0) (sym p))
neq-f-c : ¬ Path ℕ 0 2
neq-f-c = λ p → znots (cong (_∸ 0) p)
neq-t-c : ¬ Path ℕ 1 2
neq-t-c = λ p → znots (cong (_∸ 1) p)

-- §1 · over each value the fibre is a point: nothing is elided.
over-false : isContr (fiber ind 0)
over-false = (false , refl) , same where
  same : (y : fiber ind 0) → (false , refl) ≡ y
  same (false , p) i = false , isSetℕ 0 0 refl p i
  same (true  , p) = ⊥rec (neq-t-f p)

over-true : isContr (fiber ind 1)
over-true = (true , refl) , same where
  same : (y : fiber ind 1) → (true , refl) ≡ y
  same (true  , p) i = true , isSetℕ 1 1 refl p i
  same (false , p) = ⊥rec (neq-f-t p)

-- §2 · off both values the fibre is empty (रिक्तम्).
off-both : ¬ fiber ind 2
off-both (false , p) = neq-f-c p
off-both (true  , p) = neq-t-c p

-- §3 · no section: the image has two points and ℕ does not.
no-section : (g : ℕ → Bool) → ((n : ℕ) → ind (g n) ≡ n) → ⊥
no-section g s = off-both (g 2 , s 2)

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FuelAdequacyIsACollision
--
-- Sixth site of `TranscriptDescent.collisionObstructsDecoder`, and the
-- first one that is about this repository's own code rather than about
-- mathematics.
--
-- ────────────────────────────────────────────────────────────────────
-- WHICH FUELLED FUNCTIONS CARRY THEIR OWN ADEQUACY
--
-- Twenty modules in this corpus are fuel driven, and a type-level
-- criterion separates them.  It is sharp:
--
--   `Factorisation.factorise-fuel : (fuel n : ℕ) → 0 < n → n ≤ fuel
--                                 → Factorisation n`
--   `CoprimeSplitting`'s atom      : … → n ≤ fuel → Σ[ p ] (IsPrime p × p ∣ n)
--   `PFreePart.pFree-fuel`         : … → m ≤ fuel → Split p m
--   `KFlow`                        : … → n ≤ fuel → …
--
-- every one of them takes the budget as a HYPOTHESIS and returns a Σ
-- carrying its own postcondition.  For those, adequacy is discharged by
-- the type: the postcondition is a projection of the result, and there
-- is no theorem left to prove.
--
--   `FrontierList.expOf : ℕ → ℕ → ℕ → ℕ`
--
-- takes the budget as bare data and returns bare data.  It is the only
-- one of the twenty in that shape.
--
-- ────────────────────────────────────────────────────────────────────
-- THE CRITERION, MADE EXACT
--
-- "Bare data cannot carry adequacy" is a slogan until it is a
-- collision.  Here it is one.  Fix the base p = 2 and let the input be
-- the pair (k , gas).  Then
--
--     bare (k , g)       =  expOf 2 k g
--     saturated (k , g)  =  has the climb stopped? — i.e. is
--                           2 ^ (suc (expOf 2 k g)) already past k?
--
-- and the two inputs (2 , 1) and (8 , 1) are a collision:
--
--     expOf 2 2 1  =  1  =  expOf 2 8 1
--     saturated (2 , 1) = true   (2² = 4 > 2, the climb is finished)
--     saturated (8 , 1) = false  (2² = 4 ≤ 8, it has further to go)
--
-- So no decoder on the returned value recovers adequacy, and by the
-- corpus's own lemma that is not a gap in anyone's cleverness — it is
-- `¬ FactorsThrough bare saturated`.
--
-- ────────────────────────────────────────────────────────────────────
-- AND THE REPAIR, IN THE SAME IDIOM
--
-- A collision names the missing distinction, and here the distinction
-- is `k`.  Return the value paired with the bound and adequacy factors
-- immediately, with the decoder written out:
--
--     withK (k , g) = (k , expOf 2 k g)
--     saturated-factors : FactorsThrough withK saturated
--
-- which is the type `expOf` should have had, in the weakest form that
-- works.  The Σ-returning fuelled functions listed above are the strong
-- form of the same repair, and that is why none of them needed a
-- theorem.
------------------------------------------------------------------------

module FuelAdequacyIsACollision where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _^_)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤Dec)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import Cubical.Functions.Image using (Image ; restrictToImage)

open import FrontierList using (expOf)
open import FiniteInformation using (FactorsThrough)
open import TranscriptDescent using (collisionObstructsDecoder)

------------------------------------------------------------------------
-- 1.  The climb's state, as seen from outside
------------------------------------------------------------------------

Inputs : Type
Inputs = ℕ × ℕ            -- (bound k , fuel remaining-count gas), base 2

bare : Inputs → ℕ
bare (k , g) = expOf 2 k g

-- "the climb has stopped": one more step would overshoot the bound
stopped : ℕ → ℕ → Bool
stopped k e with ≤Dec (2 ^ (suc e)) k
... | yes _ = false
... | no  _ = true

saturated : Inputs → Bool
saturated (k , g) = stopped k (expOf 2 k g)

------------------------------------------------------------------------
-- 2.  The collision, computed
------------------------------------------------------------------------

-- both climbs stand at exponent 1 after one step
same-value : bare (2 , 1) ≡ bare (8 , 1)
same-value = refl

-- but one of them is finished and the other is not
sat-2 : saturated (2 , 1) ≡ true
sat-2 = refl

sat-8 : saturated (8 , 1) ≡ false
sat-8 = refl

different-status : ¬ (saturated (2 , 1) ≡ saturated (8 , 1))
different-status p = true≢false (sym sat-2 ∙ p ∙ sat-8)

------------------------------------------------------------------------
-- 3.  THE OBSTRUCTION, from the corpus's own lemma
------------------------------------------------------------------------

fuel-adequacy-does-not-factor : ¬ FactorsThrough bare saturated
fuel-adequacy-does-not-factor =
  collisionObstructsDecoder bare saturated
    {x = (2 , 1)} {x' = (8 , 1)}
    same-value
    different-status

------------------------------------------------------------------------
-- 4.  THE REPAIR: carry the bound, and the decoder writes itself
------------------------------------------------------------------------

withK : Inputs → (ℕ × ℕ)
withK (k , g) = (k , expOf 2 k g)

saturated-factors : FactorsThrough withK saturated
saturated-factors = decode , law
  where
  decode : Image withK → Bool
  decode ((k , e) , _) = stopped k e

  law : (x : Inputs) → decode (restrictToImage withK x) ≡ saturated x
  law (k , g) = refl

------------------------------------------------------------------------
-- 5.  What the sixth site adds to the other five.
--
-- about representations of mathematical objects: लाघव over expressions,
-- अनुवृत्ति over rule lists, carry/borrow over digit strings, the
-- transcript over machine states, the Jain सप्तभङ्गी over standpoints.
--
-- This one is about a TYPE SIGNATURE in this repository, and it says
-- something the other five could not: the discipline in CLAUDE.md (absent from this repository) — that
-- a computed instance must not stand in for a theorem — has a mechanical
-- shadow.  Where the return type of a fuelled function is bare data, the
-- adequacy claim provably cannot ride along, so it will be carried by a
-- `refl` at one input or by nothing at all.  Where the return type is a
-- Σ, it rides along by construction.
------------------------------------------------------------------------

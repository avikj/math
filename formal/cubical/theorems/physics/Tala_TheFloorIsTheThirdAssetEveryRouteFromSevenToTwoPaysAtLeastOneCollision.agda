{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- तलम् — the FLOOR: the third asset class, and the smallest barrier.
--
-- The ledger held two assets: fords (landed equivalences, toll exactly
-- zero) and walls (proved non-equivalences, no identification at any
-- price).  भित्ति-सप्तभङ्गी left the stronger fact on the table: दुर्नयः is
-- not merely "no equivalence सप्तभङ्गी ≃ Bool" — it is "no INJECTION",
-- a statement about EVERY map, not about one candidate identification:
--
--     तलम् : (f : सप्तभङ्गी → Bool)
--          → Σ x, Σ y,  (¬ x ≡ y) × (f x ≡ f y)
--
-- Every possible route from the sevenfold to the twofold pays at least
-- one collision, with the colliding pair EXHIBITED (a receipt, not a
-- bound: the two positions are named, drawn from the three seeds).
--
-- WHY THIS IS AN ASSET CLASS AND NOT A CURIOSITY.  A floor is a proved
-- lower bound on the toll of every crossing — which is exactly what a
-- BARRIER is.  TARGET.md (absent from this repository)'s parity theorem (ParitySeparator,
-- ChargeCriterion) has this same shape one storey up: every method whose
-- queries are parity-neutral pays the parity bit — a floor on the
-- observable graph.  Bombieri's sieve barrier, the depth barrier, the
-- two-valued collapse of the sevenfold: one kind of object, quantified
-- over routes, exhibiting what every route must lose.  Fords say what is
-- free; walls say what is unreachable; FLOORS say what everything else
-- costs at minimum.  The candidate list sorts into three, not two.
--
-- The wall is now a one-line corollary (an equivalence is injective),
-- which is the right dependency direction: barriers are prior to
-- impossibilities.  तल is built here; the load-bearing
-- pigeonhole is Saptabhangi's दुर्नयः, used not reproved.
------------------------------------------------------------------------

module Tala_TheFloorIsTheThirdAssetEveryRouteFromSevenToTwoPaysAtLeastOneCollision where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Saptabhangi
  using ( सप्तभङ्गी ; स्यात्-अस्ति ; स्यात्-नास्ति ; स्यात्-अवक्तव्यम् ; दुर्नयः )
open import BhittiSaptabhangi_TheSevenfoldCannotBeTwoValuedSoTheTopJoinCandidateIsAWall
  using ( वक्ता ; वक्ता-अभेद ; अस्ति≢नास्ति ; अस्ति≢अवक्तव्य ; नास्ति≢अवक्तव्य ; अभेद )

------------------------------------------------------------------------
-- १ · तलम् — the floor.  Every two-valued route collapses two named
-- positions; the pair is exhibited, drawn from the three seeds.
------------------------------------------------------------------------

तलम् : (f : सप्तभङ्गी → Bool)
     → Σ[ x ∈ सप्तभङ्गी ] Σ[ y ∈ सप्तभङ्गी ] ((¬ (x ≡ y)) × (f x ≡ f y))
तलम् f = sort (दुर्नयः g)
  where
    g : सप्तभङ्गी → _
    g x = वक्ता (f x)

    उत्तोल : {x y : सप्तभङ्गी} → g x ≡ g y → f x ≡ f y
    उत्तोल {x} {y} p = वक्ता-अभेद (f x) (f y) p

    sort : (g स्यात्-अस्ति ≡ g स्यात्-नास्ति)
         ⊎ ((g स्यात्-अस्ति ≡ g स्यात्-अवक्तव्यम्)
         ⊎  (g स्यात्-नास्ति ≡ g स्यात्-अवक्तव्यम्))
         → Σ[ x ∈ सप्तभङ्गी ] Σ[ y ∈ सप्तभङ्गी ] ((¬ (x ≡ y)) × (f x ≡ f y))
    sort (inl p)       = स्यात्-अस्ति  , स्यात्-नास्ति     , अस्ति≢नास्ति    , उत्तोल p
    sort (inr (inl p)) = स्यात्-अस्ति  , स्यात्-अवक्तव्यम् , अस्ति≢अवक्तव्य  , उत्तोल p
    sort (inr (inr p)) = स्यात्-नास्ति , स्यात्-अवक्तव्यम् , नास्ति≢अवक्तव्य , उत्तोल p

------------------------------------------------------------------------
-- २ · the wall, re-derived as a corollary: an equivalence is a route, and
-- the floor makes it collide; injectivity refuses the collision.  The
-- dependency now runs the right way — the barrier is prior.
------------------------------------------------------------------------

भित्ति-पुनः : (सप्तभङ्गी ≃ Bool) → ⊥
भित्ति-पुनः e =
  let (x , y , x≢y , coll) = तलम् (equivFun e)
  in x≢y (अभेद e coll)

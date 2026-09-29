{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
--  — the pricing.
-- The mathematics is the fibre of a map (cubical, the one
-- admitted non-Indian substrate); the three-verdict discipline is
-- Avaccheda's (रिक्तम् / एकम् / बहु — a target nothing reaches, a
-- contractible fibre, a fibre that IS the memory required), and the
-- refusal to collapse three verdicts into two is Saptabhangi.दुर्नयः.
--
-- WHY THIS MODULE EXISTS.  Two Bool → ℕ edges live in
-- NaturalMachine.FiniteOccupancyChannelNoGo: `asNat` and `bothNat`.
-- Lopa's deciding rules R1–R4 cannot reach them (target ℕ is neither
-- contractible nor ⊥ nor a truncation).
-- This module
-- forces the verdicts by computation: the COMPLETE fibre spectrum of both
-- maps, at every target, so the edges are priced rather than graded.
--
-- THE PRICES.
--
--   asNat : Bool → ℕ          0 ↦ एकम्, 1 ↦ एकम्, n+2 ↦ रिक्तम्.
--     No बहु anywhere: the elision loses nothing — the WHICH survives
--     at every reached target.  A left inverse exists on the image; the
--     map fails only to reach, never to remember.
--
--   bothNat (uncurried) : Bool × Bool → ℕ
--     1 ↦ एकम् (only (true,true)), n+2 ↦ रिक्तम्, and 0 ↦ बहु with the
--     fibre computed EXACTLY: three points, Unit ⊎ Unit ⊎ Unit — the
--     memory destroyed at 0 is precisely the distinction among
--     (true,false), (false,true), (false,false).  This is the amount,
--     not a flag (Avaccheda: the fibre IS the amount).
--
-- Together the two maps are the sharpest small contrast the verdict
-- lane owns: one Bool→ℕ edge that never forgets and one that forgets
-- exactly two bits' worth at exactly one target.
------------------------------------------------------------------------

module Mulyankana_TheTwoOccupancyEdgesArePricedTheirFibreSpectraComputedAtEveryTarget where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool using (Bool ; false ; true ; true≢false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; znots ; snotz ; injSuc)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Relation.Nullary using (¬_)

open import FiniteOccupancyChannelNoGo using (asNat ; bothNat)

------------------------------------------------------------------------
-- असंख्या-सङ्केतः asNat — the edge that never forgets.
------------------------------------------------------------------------

एकम्-असंख्या-० : isContr (fiber asNat 0)
एकम्-असंख्या-० = (false , refl) , contr
  where
  contr : (q : fiber asNat 0) → (false , refl) ≡ q
  contr (false , p) = ΣPathP (refl , isSetℕ 0 0 refl p)
  contr (true  , p) = Empty.rec (snotz p)

एकम्-असंख्या-१ : isContr (fiber asNat 1)
एकम्-असंख्या-१ = (true , refl) , contr
  where
  contr : (q : fiber asNat 1) → (true , refl) ≡ q
  contr (true  , p) = ΣPathP (refl , isSetℕ 1 1 refl p)
  contr (false , p) = Empty.rec (znots p)

रिक्तम्-असंख्या : (n : ℕ) → ¬ fiber asNat (suc (suc n))
रिक्तम्-असंख्या n (false , p) = znots p
रिक्तम्-असंख्या n (true  , p) = znots (injSuc p)

------------------------------------------------------------------------
-- उभय-सङ्केतः bothNat, uncurried — the edge that forgets exactly once.
------------------------------------------------------------------------

g : Bool × Bool → ℕ
g xy = bothNat (fst xy) (snd xy)

एकम्-उभय-१ : isContr (fiber g 1)
एकम्-उभय-१ = ((true , true) , refl) , contr
  where
  contr : (q : fiber g 1) → ((true , true) , refl) ≡ q
  contr ((true  , true ) , p) = ΣPathP (refl , isSetℕ 1 1 refl p)
  contr ((true  , false) , p) = Empty.rec (znots p)
  contr ((false , true ) , p) = Empty.rec (znots p)
  contr ((false , false) , p) = Empty.rec (znots p)

रिक्तम्-उभय : (n : ℕ) → ¬ fiber g (suc (suc n))
रिक्तम्-उभय n ((true  , true ) , p) = znots (injSuc p)
रिक्तम्-उभय n ((true  , false) , p) = znots p
रिक्तम्-उभय n ((false , true ) , p) = znots p
रिक्तम्-उभय n ((false , false) , p) = znots p

-- बहु at 0, and the fibre computed exactly: three points, no more.
बहु-उभय-० : fiber g 0 ≃ (Unit ⊎ (Unit ⊎ Unit))
बहु-उभय-० = isoToEquiv (iso fun inv rightInv leftInv)
  where
  fun : fiber g 0 → Unit ⊎ (Unit ⊎ Unit)
  fun ((true  , true ) , p) = Empty.rec (snotz p)
  fun ((true  , false) , p) = inl tt
  fun ((false , true ) , p) = inr (inl tt)
  fun ((false , false) , p) = inr (inr tt)

  inv : Unit ⊎ (Unit ⊎ Unit) → fiber g 0
  inv (inl tt)       = (true  , false) , refl
  inv (inr (inl tt)) = (false , true ) , refl
  inv (inr (inr tt)) = (false , false) , refl

  rightInv : (k : Unit ⊎ (Unit ⊎ Unit)) → fun (inv k) ≡ k
  rightInv (inl tt)       = refl
  rightInv (inr (inl tt)) = refl
  rightInv (inr (inr tt)) = refl

  leftInv : (q : fiber g 0) → inv (fun q) ≡ q
  leftInv ((true  , true ) , p) = Empty.rec (snotz p)
  leftInv ((true  , false) , p) = ΣPathP (refl , isSetℕ 0 0 refl p)
  leftInv ((false , true ) , p) = ΣPathP (refl , isSetℕ 0 0 refl p)
  leftInv ((false , false) , p) = ΣPathP (refl , isSetℕ 0 0 refl p)

-- and बहु said as Avaccheda's verdict demands — not merely "not एकम्"
-- but the memory exhibited: two elements the collapse would identify.
बहु-साक्षिन् : ¬ isContr (fiber g 0)
बहु-साक्षिन् c =
  true≢false
    (cong (λ q → fst (fst q))
          (sym (snd c ((true , false) , refl))
           ∙ snd c ((false , true) , refl)))

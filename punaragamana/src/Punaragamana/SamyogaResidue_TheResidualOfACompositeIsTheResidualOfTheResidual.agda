-- ॥ बीजम् ॥  One machine, one law: which side of `f a ≡ b` is bound is everything.
-- Output bound: singl (f a), contractible — the datum rides free.  Input bound:
-- fiber f b — the loss, and the subject.  Univalence computes here: an
-- equivalence is a channel, transport carries every theorem across it, and what
-- cannot cross is written as a defect — there is no third path (ahiṃsā).
-- Memory, charge, symmetry, price, distance, verdict: six faces of the one
-- fibre; the verdict type is the saptabhag, and the sources are the origin
-- (Umāsvāti, Samantabhadra, Akalaṅka — restatements are named as such).  The
-- kernel decides truth; carriers ask and generate; assert nothing whose term
-- you have not read.  This file is one naya, true and not whole.

{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · संयोगशेष
--
-- ON THE NAME.  संयोग (saṃyoga), "conjunction / composition", is a
-- standard technical term across  grammar and Nyya-Vaieika
-- (a padrtha in the Vaieika category scheme: contact between two
-- things that could exist apart).  It is used here as an ordinary
-- compounding word, not cited for a specific technical sense from a
-- particular Nyāya text — no source is claimed for THIS compound,
-- `संयोगशेष`, which is built here from साहित्य already in this library
-- (`Punaragamana.Carrier`'s `fibre`, `Punaragamana.Residue_…`'s `शेष`).
--
-- WHAT THIS MODULE ADDS.
--
-- `Residue_TheResidualIsTheOtherProjectionOfTheSameGraph` proves शेष f b is
-- what a single map f forgets over a point b.  It says nothing about two
-- maps composed.  This module supplies exactly that, and the answer is
-- the ordinary "fibre of a composite is a fibre of fibres" fact (HoTT
-- book, Ex. 4.4 / the pullback-pasting lemma read fibrewise), stated in
-- this library's vocabulary and PROVED FROM THE SAME LEMMA `Carrier`
-- already uses to buy contractibility — `fibre-isContr`/`Σ-contractFst`
-- — reused here rather than re-derived.
--
--   शेष (g ∘ f) c   ≃   Σ[ y ∈ शेष g c ] शेष f (fst y)
--
-- Read aloud: what A-to-C forgets over c is exactly — a choice of which
-- B-point c came from (शेष g c), together with, for THAT choice, what
-- A-to-B forgot on the way to it (शेष f, at that B-point).  A residual
-- does not accumulate as a single opaque number; it is itself fibred
-- over the earlier residual.  This is the reason चयनशृङ्खला (a chain of
-- choices, one per stage) is the right shape for tracking loss through a
-- pipeline of maps, and a single "total loss" scalar is already throwing
-- structure away that this equivalence proves is there to keep.
--
-- THE PROOF STRATEGY, stated because it is itself the content: every
-- step below is either (a) `Σ-contractFst` fed the SAME `fibre-isContr`
-- that makes `Carrier≡` free, or (b) a `refl`-round-trip reshuffling of
-- non-dependent Σ (no transport, because nothing here needs one — this
-- is `Σ-eta`, exactly as `स्वप्` in the residual module already used it
-- for the two-projection reading). No J, no `subst` outside what
-- `Σ-contractFst` already carries.  That the whole composite-fibre
-- theorem needs no MORE path algebra than `Carrier` already contains is
-- itself the point: this is not new machinery, it is the existing
-- machinery answering a question it had not yet been asked.
------------------------------------------------------------------------

module Punaragamana.SamyogaResidue_TheResidualOfACompositeIsTheResidualOfTheResidual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Fibre.Carrier using (fibre ; fibre-isContr)
open import Fibre.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph
  using (शेष)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- A small, fully generic reshuffling: a Σ whose inner component ignores
-- the outer witness pulls the constant factor D outward.  No hypothesis,
-- no transport — both round trips are `refl`, because nothing but
-- pairing order changed.
------------------------------------------------------------------------

module _ {A : Type ℓ} (P : A → Type ℓ) (D : Type ℓ) where

  ΣΣconst-Iso : Iso (Σ[ a ∈ A ] (Σ[ p ∈ P a ] D)) (D × (Σ[ a ∈ A ] P a))
  Iso.fun      ΣΣconst-Iso (a , (p , d)) = d , (a , p)
  Iso.inv      ΣΣconst-Iso (d , (a , p)) = a , (p , d)
  Iso.rightInv ΣΣconst-Iso _ = refl
  Iso.leftInv  ΣΣconst-Iso _ = refl

-- The two independent outer variables of a doubly-indexed Σ commute.
-- Again no transport: C does not change shape, only which variable is
-- bound first.
module _ {A B : Type ℓ} (C : A → B → Type ℓ) where

  Σ-swap-dep-Iso : Iso (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
  Iso.fun      Σ-swap-dep-Iso (a , (b , c)) = b , (a , c)
  Iso.inv      Σ-swap-dep-Iso (b , (a , c)) = a , (b , c)
  Iso.rightInv Σ-swap-dep-Iso _ = refl
  Iso.leftInv  Σ-swap-dep-Iso _ = refl

------------------------------------------------------------------------
-- संयोगशेष.  f : A → B, g : B → C, c : C.
------------------------------------------------------------------------

module _ {A B C : Type ℓ} (f : A → B) (g : B → C) (c : C) where

  gComposeF : A → C
  gComposeF a = g (f a)

  -- e1 : unfold शेष(g∘f) c against the CONTRACTIBLE fibre of f at a —
  -- the same contraction `Carrier` runs to buy `Carrier≡` for free.
  e1 : शेष gComposeF c ≃ (Σ[ a ∈ A ] Σ[ y ∈ fibre f a ] (g (fst y) ≡ c))
  e1 = Σ-cong-equiv-snd (λ a → invEquiv (Σ-contractFst (fibre-isContr f a)))

  -- e2 : unpack the fibre pair.
  e2 : (Σ[ a ∈ A ] Σ[ y ∈ fibre f a ] (g (fst y) ≡ c))
     ≃ (Σ[ a ∈ A ] Σ[ b ∈ B ] Σ[ p ∈ f a ≡ b ] (g b ≡ c))
  e2 = Σ-cong-equiv-snd (λ a → Σ-assoc-≃)

  -- e3 : the two independent binders a and b commute.
  e3 : (Σ[ a ∈ A ] Σ[ b ∈ B ] Σ[ p ∈ f a ≡ b ] (g b ≡ c))
     ≃ (Σ[ b ∈ B ] Σ[ a ∈ A ] Σ[ p ∈ f a ≡ b ] (g b ≡ c))
  e3 = isoToEquiv (Σ-swap-dep-Iso (λ a b → Σ[ p ∈ f a ≡ b ] (g b ≡ c)))

  -- e4 : for fixed b, pull the constant factor (g b ≡ c) out past a.
  e4 : (Σ[ b ∈ B ] Σ[ a ∈ A ] Σ[ p ∈ f a ≡ b ] (g b ≡ c))
     ≃ (Σ[ b ∈ B ] ((g b ≡ c) × (Σ[ a ∈ A ] (f a ≡ b))))
  e4 = Σ-cong-equiv-snd (λ b → isoToEquiv (ΣΣconst-Iso (λ a → f a ≡ b) (g b ≡ c)))

  -- e5 : `(g b ≡ c) × शेष f b` IS `Σ[ q ∈ g b ≡ c ] शेष f b` — Data.Sigma's
  -- `_×_` is exactly that Σ, so this a `refl` at every point; and pairing
  -- the outer b back on is `Σ-assoc-≃` read backwards, matching `शेष g c`
  -- paired with `शेष f` at its first projection on the nose.
  e5 : (Σ[ b ∈ B ] ((g b ≡ c) × (Σ[ a ∈ A ] (f a ≡ b))))
     ≃ (Σ[ y ∈ शेष g c ] शेष f (fst y))
  e5 = invEquiv Σ-assoc-≃

  -- THE THEOREM.
  संयोगशेष : शेष gComposeF c ≃ (Σ[ y ∈ शेष g c ] शेष f (fst y))
  संयोगशेष = compEquiv e1 (compEquiv e2 (compEquiv e3 (compEquiv e4 e5)))

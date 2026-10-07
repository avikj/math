{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- ListAddr — the concrete address model for the spawn machine.
--
-- Addr = List ℕ.  The root judgments sit at [i]; the k-th child of α
-- is k ∷ α, so deeper cells are LONGER lists carrying their parent as a
-- suffix.  Ext β α ("β properly extends α") = α is a proper suffix of β,
-- witnessed by a NON-EMPTY prefix xs with β ≡ xs ++ α.  depth = length.
--
-- This file discharges, by hand-checkable structural reasoning, exactly
-- the axiom interface SpawnMachine abstracts over.  Reviewable without a
-- proof assistant; the checker confirms the clerical layer.
------------------------------------------------------------------------

module ListAddr where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length ; ++-assoc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Discrete ; yes ; no ; ¬_)

Addr : Type
Addr = List ℕ

child : ℕ → Addr → Addr
child k α = k ∷ α

-- A proper extension: a non-empty prefix xs with β = xs ++ α.
record Ext (β α : Addr) : Type where
  constructor ext
  field
    pre      : Addr
    nonempty : ¬ (pre ≡ [])
    eq       : β ≡ pre ++ α
open Ext public

depth : Addr → ℕ
depth = length

------------------------------------------------------------------------
-- Discreteness of List ℕ.
------------------------------------------------------------------------

open import Cubical.Data.Nat using (discreteℕ)
open import Cubical.Data.List using (discreteList)

_≟_ : Discrete Addr
_≟_ = discreteList discreteℕ

------------------------------------------------------------------------
-- child injective in both arguments.
------------------------------------------------------------------------

∷-inj : {k l : ℕ} {α β : Addr} → (k ∷ α) ≡ (l ∷ β) → (k ≡ l) × (α ≡ β)
∷-inj {k} {l} {α} {β} p = (cong headD p) , (cong tailD p)
  where
  headD : Addr → ℕ
  headD []      = k
  headD (x ∷ _) = x
  tailD : Addr → Addr
  tailD []      = α
  tailD (_ ∷ r) = r

child-inj : {k l : ℕ} {α β : Addr} → child k α ≡ child l β → (k ≡ l) × (α ≡ β)
child-inj = ∷-inj

------------------------------------------------------------------------
-- a child properly extends its parent: prefix [k].
------------------------------------------------------------------------

[]≢∷ : {k : ℕ} {α : Addr} → ¬ ((k ∷ α) ≡ [])
[]≢∷ p = subst isCons p tt
  where
  isCons : Addr → Type
  isCons []      = ⊥
  isCons (_ ∷ _) = Unit

child-ext : (k : ℕ) (α : Addr) → Ext (child k α) α
child-ext k α = ext (k ∷ []) []≢∷ refl

------------------------------------------------------------------------
-- transitivity: concatenate prefixes (nonempty + anything = nonempty).
------------------------------------------------------------------------

++-nonempty-l : (xs ys : Addr) → ¬ (xs ≡ []) → ¬ ((xs ++ ys) ≡ [])
++-nonempty-l []       ys ne p = ne refl
++-nonempty-l (x ∷ xs) ys ne p = []≢∷ p

ext-trans : {γ β α : Addr} → Ext γ β → Ext β α → Ext γ α
ext-trans {γ} {β} {α} (ext p pne pe) (ext q qne qe) =
  ext (p ++ q) (++-nonempty-l p q pne)
      (pe ∙ cong (p ++_) qe ∙ sym (++-assoc p q α))

------------------------------------------------------------------------
-- ext-of-child: if k ∷ α extends γ, then γ ≡ α or α extends γ.
-- The prefix is non-empty, so it is z ∷ zs; k ∷ α ≡ z ∷ zs ++ γ gives
-- α ≡ zs ++ γ.  If zs ≡ [] then α ≡ γ; else α extends γ with prefix zs.
------------------------------------------------------------------------

ext-of-child : {k : ℕ} {α γ : Addr} → Ext (child k α) γ → (γ ≡ α) ⊎ Ext α γ
ext-of-child {k} {α} {γ} (ext []       ne eq) = Empty.rec (ne refl)
ext-of-child {k} {α} {γ} (ext (z ∷ zs) ne eq) with zs ≟ []
... | yes z0 = inl (sym α≡γ)
  where
  -- k ∷ α ≡ (z ∷ zs) ++ γ ≡ z ∷ (zs ++ γ); with zs ≡ [], = z ∷ γ.
  α≡zs++γ : α ≡ zs ++ γ
  α≡zs++γ = snd (∷-inj eq)
  α≡γ : α ≡ γ
  α≡γ = α≡zs++γ ∙ cong (_++ γ) z0
... | no zsne = inr (ext zs zsne (snd (∷-inj eq)))

------------------------------------------------------------------------
-- depth axioms.
------------------------------------------------------------------------

child-depth : (k : ℕ) (α : Addr) → depth (child k α) ≡ suc (depth α)
child-depth k α = refl

-- length of a concatenation, and that a nonempty prefix strictly raises it.
length-++ : (xs ys : Addr) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

-- A non-empty prefix is z ∷ zs; concatenation has length
-- suc (length zs + depth α), giving the strict-depth witness directly
-- against cubical's definition  m < n = Σ[ k ] k + suc m ≡ n.
open import Cubical.Data.Nat using (+-suc)

ext-depth : {β α : Addr} → Ext β α → depth α < depth β
ext-depth {β} {α} (ext []       ne eq) = Empty.rec (ne refl)
ext-depth {β} {α} (ext (z ∷ zs) ne eq) =
  length zs , (+-suc (length zs) (depth α) ∙ sym depth-β)
  where
  -- depth β = length ((z ∷ zs) ++ α) = suc (length zs + depth α)
  depth-β : depth β ≡ suc (length zs + depth α)
  depth-β = cong length eq ∙ length-++ (z ∷ zs) α

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module RepresentativeContinuation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
  using (Bool ; false ; true ; _⊕_ ; false≢true ; dichotomyBool)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-trans ; ≤-antisym)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)

-- Weighted representative families can preserve every optimal continuation
-- without preserving every row or every original partial solution.
--
-- This is the reconstruction argument underlying rank-based connectivity
-- reduction (Bodlaender--Cygan--Kratsch--Nederlof, arXiv:1211.1505), stated
-- for arbitrary compatibility predicates. Basis construction and its rank
-- bound are NOT assumed free and are not implemented here.
--
-- P: original partial solutions; Q: future continuations; K: retained ones.
-- A row records compatibility with ALL futures. The selected cheap XOR
-- combination is one object per p, fixed independently of the future q.
module Representation (P Q K : Type)
  (row : P → Q → Bool) (cost : P → ℕ) (embed : K → P) where

  data CheapCombination (p : P) : Type where
    zeroSum : CheapCombination p
    add : (k : K) → cost (embed k) ≤ cost p
      → CheapCombination p → CheapCombination p

  evaluate : {p : P} → CheapCombination p → Q → Bool
  evaluate zeroSum q = false
  evaluate (add k bound rest) q = row (embed k) q ⊕ evaluate rest q

  -- An odd sum has a true summand, and each summand carries its cost bound.
  -- We produce the representative, not merely a truncated existence proof.
  realize : {p : P} (c : CheapCombination p) (q : Q)
    → evaluate c q ≡ true
    → Σ[ k ∈ K ] ((row (embed k) q ≡ true) × (cost (embed k) ≤ cost p))
  realize zeroSum q h = Empty.rec (false≢true h)
  realize (add k bound rest) q h with dichotomyBool (row (embed k) q)
  ... | inl accepted = k , accepted , bound
  ... | inr rejected = realize rest q
    (sym (cong (λ b → b ⊕ evaluate rest q) rejected) ∙ h)

  module Spanning (combination : (p : P) → CheapCombination p)
    (spans : (p : P) (q : Q) → evaluate (combination p) q ≡ row p q)
    where

    replace : (p : P) (q : Q) → row p q ≡ true
      → Σ[ k ∈ K ] ((row (embed k) q ≡ true) × (cost (embed k) ≤ cost p))
    replace p q h = realize (combination p) q (spans p q ∙ h)

    BestOriginal : Q → P → Type
    BestOriginal q p = (row p q ≡ true) ×
      ((p' : P) → row p' q ≡ true → cost p ≤ cost p')

    BestRetained : Q → K → Type
    BestRetained q k = (row (embed k) q ≡ true) ×
      ((k' : K) → row (embed k') q ≡ true → cost (embed k) ≤ cost (embed k'))

    -- Every optimum computed over retained representatives is globally
    -- optimal for the specified continuation.
    retained-optimum-is-global : (q : Q) (k : K)
      → BestRetained q k → BestOriginal q (embed k)
    retained-optimum-is-global q k (accepted , best) = accepted , globalBound
      where
      globalBound : (p : P) → row p q ≡ true → cost (embed k) ≤ cost p
      globalBound p h with replace p q h
      ... | k' , accepted' , cheap = ≤-trans (best k' accepted') cheap

    -- If the original optimum is attained, a retained optimum is attained
    -- at exactly the same cost. No enumeration of P or Q occurs in this
    -- proof; a concrete algorithm must still construct the span evidence.
    original-optimum-is-retained : (q : Q) (p : P)
      → BestOriginal q p
      → Σ[ k ∈ K ] (BestRetained q k × (cost (embed k) ≡ cost p))
    original-optimum-is-retained q p (accepted , best) with replace p q accepted
    ... | k , accepted' , cheap =
      k , (accepted' , λ k' h → ≤-trans cheap (best (embed k') h)) ,
      ≤-antisym cheap (best (embed k) accepted')

    original-empty : (q : Q)
      → ((p : P) → row p q ≡ true → ⊥)
      → (k : K) → row (embed k) q ≡ true → ⊥
    original-empty q no k h = no (embed k) h

    retained-empty : (q : Q)
      → ((k : K) → row (embed k) q ≡ true → ⊥)
      → (p : P) → row p q ≡ true → ⊥
    retained-empty q no p h with replace p q h
    ... | k , accepted , cheap = no k accepted

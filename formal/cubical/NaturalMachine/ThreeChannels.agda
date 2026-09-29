{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.ThreeChannels
--
-- The Chen envelope's three channels and the primitive projector —
-- the multiset skeleton of Factories VIII and IX, reconstructed from
-- the EGB V3 index summaries.
-- Index item 128: "exact projectors onto prime, square, and
-- distinct-semiprime channels."  Index item 132: "π₁(N) = ω(N)−1;
-- 1_ℙ = μ² − π₁ on P₂."
--
-- WHAT THIS MODULE PROVES (no holes, no postulates, --safe):
--
--   SquareChannel, DistinctSemiprime   the two charge-two channels, as types
--   three-channels              every envelope number is prime, a
--                               square, or a distinct semiprime —
--                               the trichotomy CONSTRUCTED by recursion
--   prime-not-square,           the three channels are pairwise
--   prime-not-semiprime,        disjoint, so the trichotomy is a
--   square-not-semiprime        partition, not a covering
--   sqfreeBit  (μ²)             squarefreeness of the multiset
--   π₁bit      (π₁ > 0)         "a second distinct prime exists"
--   sqfree-square,              each charge-two channel is annihilated
--   π₁-semiprime                by EXACTLY ONE of the two factors —
--                               the square by μ², the distinct
--                               semiprime by π₁: which factor kills
--                               which channel is the projector's
--                               anatomy, invisible to parity alone
--   primitive-projector         Factory IX's 1_ℙ = μ² − π₁ on P₂,
--                               subtraction-free: on the envelope,
--                               (μ² ∧ ¬π₁) ⟺ charge 1, both directions
--
-- RELATION TO ChenProjector: parity (1−λ)/2 reads the CHARGE and is
-- complete on the envelope; the primitive projector reads the CHANNEL
-- STRUCTURE (which of μ², π₁ fails) and so distinguishes p² from pq —
-- information parity cannot see (both have λ = +1).  Factory VIII's
-- analytic claim (square branch negligible at Chen scale) is exactly
-- the statement that this extra resolution costs nothing
-- asymptotically.
------------------------------------------------------------------------

module NaturalMachine.ThreeChannels where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; injSuc ; znots ; snotz)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator using (Number ; Ω)
open import NaturalMachine.ChenProjector using (Envelope)

------------------------------------------------------------------------
-- §0  Boolean algebra, top-level so proofs and definitions share
-- symbols and definitional unfolding.
------------------------------------------------------------------------

orB : Bool → Bool → Bool
orB true  _ = true
orB false b = b

andB : Bool → Bool → Bool
andB true  b = b
andB false _ = false

------------------------------------------------------------------------
-- §1  Decidable equality on prime indices.
------------------------------------------------------------------------

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ-sound : (m n : ℕ) → eqℕ m n ≡ true → m ≡ n
eqℕ-sound zero    zero    _ = refl
eqℕ-sound zero    (suc n) h = Empty.rec (true≢false (sym h))
eqℕ-sound (suc m) zero    h = Empty.rec (true≢false (sym h))
eqℕ-sound (suc m) (suc n) h = cong suc (eqℕ-sound m n h)

------------------------------------------------------------------------
-- §2  The three channels, and the constructed trichotomy.
------------------------------------------------------------------------

SquareChannel : Number → Type
SquareChannel n = Σ[ p ∈ ℕ ] n ≡ p ∷ p ∷ []

DistinctSemiprime : Number → Type
DistinctSemiprime n =
  Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] (n ≡ p ∷ q ∷ []) × (eqℕ p q ≡ false)

private
  split-eq : (p q : ℕ) (b : Bool) → eqℕ p q ≡ b
           → SquareChannel (p ∷ q ∷ []) ⊎ DistinctSemiprime (p ∷ q ∷ [])
  split-eq p q true  h =
    inl (p , cong (λ z → p ∷ z ∷ []) (sym (eqℕ-sound p q h)))
  split-eq p q false h = inr (p , q , refl , h)

three-channels : (n : Number) → Envelope n
               → (Ω n ≡ 1) ⊎ (SquareChannel n ⊎ DistinctSemiprime n)
three-channels []               (inl e) = Empty.rec (znots e)
three-channels []               (inr e) = Empty.rec (znots e)
three-channels (p ∷ [])         _       = inl refl
three-channels (p ∷ q ∷ [])     _       = inr (split-eq p q (eqℕ p q) refl)
three-channels (p ∷ q ∷ r ∷ ns) (inl e) = Empty.rec (snotz (injSuc e))
three-channels (p ∷ q ∷ r ∷ ns) (inr e) = Empty.rec (snotz (injSuc (injSuc e)))

-- Pairwise disjointness: the trichotomy is a partition.
prime-not-square : (n : Number) → Ω n ≡ 1 → SquareChannel n → ⊥
prime-not-square n e (p , h) = snotz (injSuc (sym (cong Ω h) ∙ e))

prime-not-semiprime : (n : Number) → Ω n ≡ 1 → DistinctSemiprime n → ⊥
prime-not-semiprime n e (p , q , h , _) = snotz (injSuc (sym (cong Ω h) ∙ e))

square-not-semiprime : (n : Number) → SquareChannel n → DistinctSemiprime n → ⊥
square-not-semiprime n (p , h) (p' , q' , h' , d) =
  true≢false (sym (eqℕ-refl p') ∙ cong (eqℕ p') p'≡q' ∙ d)
  where
  heads : Number → ℕ × ℕ
  heads []          = (zero , zero)
  heads (a ∷ [])    = (a , a)
  heads (a ∷ b ∷ _) = (a , b)

  pair : (p' , q') ≡ (p , p)
  pair = cong heads (sym h' ∙ h)

  p'≡q' : p' ≡ q'
  p'≡q' = cong fst pair ∙ sym (cong snd pair)

------------------------------------------------------------------------
-- §3  The primitive projector: μ² and π₁ as Booleans.
------------------------------------------------------------------------

member : ℕ → List ℕ → Bool
member x []       = false
member x (y ∷ ys) = orB (eqℕ x y) (member x ys)

-- μ²: the multiset is squarefree (no repeated prime).
sqfreeBit : Number → Bool
sqfreeBit []       = true
sqfreeBit (p ∷ ns) = andB (not (member p ns)) (sqfreeBit ns)

-- π₁ > 0 on the envelope: a second prime distinct from the head exists.
π₁bit : Number → Bool
π₁bit []          = false
π₁bit (p ∷ [])    = false
π₁bit (p ∷ q ∷ _) = not (eqℕ p q)

-- The two annihilations: each charge-two channel dies to exactly one
-- factor of the projector.
sqfree-square : (p : ℕ) → sqfreeBit (p ∷ p ∷ []) ≡ false
sqfree-square p =
  cong (λ b → andB (not (orB b false)) (sqfreeBit (p ∷ []))) (eqℕ-refl p)

π₁-semiprime : (p q : ℕ) → eqℕ p q ≡ false → π₁bit (p ∷ q ∷ []) ≡ true
π₁-semiprime p q d = cong not d

-- …and the complementary passes: the square passes π₁ (both its primes
-- are one prime), the distinct semiprime passes μ².
π₁-square : (p : ℕ) → π₁bit (p ∷ p ∷ []) ≡ false
π₁-square p = cong not (eqℕ-refl p)

sqfree-semiprime : (p q : ℕ) → eqℕ p q ≡ false
                 → sqfreeBit (p ∷ q ∷ []) ≡ true
sqfree-semiprime p q d =
  cong (λ b → andB (not (orB b false)) (sqfreeBit (q ∷ []))) d

------------------------------------------------------------------------
-- §4  Factory IX's identity, subtraction-free and both directions.
--
-- 1_ℙ = μ² − π₁ on P₂ becomes: on the envelope, charge 1 holds iff
-- μ² holds and π₁ fails.  Forward is computation at the prime channel;
-- backward is the trichotomy with one channel killed per factor.
------------------------------------------------------------------------

primitive-projector :
  (n : Number) → Envelope n
  → ((Ω n ≡ 1) → (sqfreeBit n ≡ true) × (π₁bit n ≡ false))
  × (((sqfreeBit n ≡ true) × (π₁bit n ≡ false)) → Ω n ≡ 1)
primitive-projector n env = forward , backward
  where
  forward : (Ω n ≡ 1) → (sqfreeBit n ≡ true) × (π₁bit n ≡ false)
  forward e = evalAt n e
    where
    evalAt : (m : Number) → Ω m ≡ 1
           → (sqfreeBit m ≡ true) × (π₁bit m ≡ false)
    evalAt []               e = Empty.rec (znots e)
    evalAt (p ∷ [])         _ = refl , refl
    evalAt (p ∷ q ∷ ms)     e = Empty.rec (snotz (injSuc e))

  backward : ((sqfreeBit n ≡ true) × (π₁bit n ≡ false)) → Ω n ≡ 1
  backward (sf , np) = decide (three-channels n env)
    where
    decide : (Ω n ≡ 1) ⊎ (SquareChannel n ⊎ DistinctSemiprime n) → Ω n ≡ 1
    decide (inl e) = e
    decide (inr (inl sq@(p , h))) =
      Empty.rec (true≢false
        (sym sf ∙ cong sqfreeBit h ∙ sqfree-square p))
    decide (inr (inr sp@(p , q , h , d))) =
      Empty.rec (true≢false
        (sym (cong π₁bit h ∙ π₁-semiprime p q d) ∙ np))

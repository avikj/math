{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- शेष-सञ्चय, the checked half.  Parent note:
-- notes/SesaSancaya_TheAlignmentNumberIsAMinimalTotalRemainderAndTheKnobGainIsAWrapCount.md (absent from this repository)
-- (compound built there; ea is ryabhaa's kept remainder,
-- Āryabhaṭīya gaṇita 32–33, 499 CE — the kuṭṭaka's disposal rule; what
-- is claimed of the source is the NAME and the rule "keep the
-- remainder", not these theorems).
--
-- The alignment number of the twin field's position side is
-- A = |S|(1 − 1/P) − (2/P)·min_u T(u), where T(u) is the total
-- remainder Σ_{c∈S} ((u−c) mod P).  This module makes the two small
-- rows of the witness table kernel-fact:
--
--   z = 5:  P = 30,  S = {0,12,18},   min T = 24,   at u = 18
--   z = 7:  P = 210, S = 15 classes,  min T = 1260, at u = 42
--
-- each as (i) the witness value by refl, and (ii) minimality by a
-- boolean exhaustion over the full period that a soundness lemma
-- lifts to a ∀ — the PMNoSection pattern: the typechecker runs the
-- search, the lemma converts the fold to the quantifier, and no bare
-- boolean is the deliverable.

module ResidueSancaya_TheMinimalTotalRemainderIsWitnessedAndBoundedAtThirtyAndTwoHundredTen where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; zero-≤ ; suc-≤-suc ; pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; _and_ ; if_then_else_ ; true≢false)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)

-- boolean order, with its meaning attached ----------------------------

leb : ℕ → ℕ → Bool
leb zero    _       = true
leb (suc m) zero    = false
leb (suc m) (suc n) = leb m n

lebSound : (m n : ℕ) → leb m n ≡ true → m ≤ n
lebSound zero    n       _ = zero-≤
lebSound (suc m) zero    p = ⊥.rec (true≢false (sym p))
lebSound (suc m) (suc n) p = suc-≤-suc (lebSound m n p)

-- range exhaustion with a soundness lemma -----------------------------

rangeAll : (ℕ → Bool) → ℕ → Bool
rangeAll f zero    = true
rangeAll f (suc n) = f n and rangeAll f n

private
  andL : (x y : Bool) → x and y ≡ true → x ≡ true
  andL true  y p = refl
  andL false y p = p

  andR : (x y : Bool) → x and y ≡ true → y ≡ true
  andR true  y p = p
  andR false true  p = refl
  andR false false p = p

splitBelow : (u n : ℕ) → u < suc n → (u ≡ n) ⊎ (u < n)
splitBelow zero    zero    _  = inl refl
splitBelow zero    (suc n) _  = inr (suc-≤-suc zero-≤)
splitBelow (suc u) zero    u< = ⊥.rec (¬-<-zero (pred-≤-pred u<))
splitBelow (suc u) (suc n) u< with splitBelow u n (pred-≤-pred u<)
... | inl e = inl (cong suc e)
... | inr h = inr (suc-≤-suc h)

soundRange : (f : ℕ → Bool) (n : ℕ) → rangeAll f n ≡ true
           → (u : ℕ) → u < n → f u ≡ true
soundRange f zero    p u u< = ⊥.rec (¬-<-zero u<)
soundRange f (suc n) p u u< with splitBelow u n u<
... | inl e = cong f e ∙ andL (f n) (rangeAll f n) p
... | inr h = soundRange f n (andR (f n) (rangeAll f n) p) u h

-- the remainder-behind, decision-free ---------------------------------
-- gap P c u = (u − c) mod P for u, c < P, computed as a conditional
-- subtraction; both branches name the same residue — the if chooses
-- the representative, it does not destroy a distinction (u and c are
-- still in hand).

gap : ℕ → ℕ → ℕ → ℕ
gap P c u = if leb c u then u ∸ c else (u + P) ∸ c

-- z = 5 ---------------------------------------------------------------

T₅ : ℕ → ℕ
T₅ u = gap 30 0 u + (gap 30 12 u + gap 30 18 u)

witness₅ : T₅ 18 ≡ 24
witness₅ = refl

exhaust₅ : rangeAll (λ u → leb 24 (T₅ u)) 30 ≡ true
exhaust₅ = refl

minimal₅ : (u : ℕ) → u < 30 → 24 ≤ T₅ u
minimal₅ u h =
  lebSound 24 (T₅ u) (soundRange (λ v → leb 24 (T₅ v)) 30 exhaust₅ u h)

-- z = 7 ---------------------------------------------------------------

T₇ : ℕ → ℕ
T₇ u =
  gap 210 0 u + (gap 210 12 u + (gap 210 18 u + (gap 210 30 u +
  (gap 210 42 u + (gap 210 60 u + (gap 210 72 u + (gap 210 102 u +
  (gap 210 108 u + (gap 210 138 u + (gap 210 150 u + (gap 210 168 u +
  (gap 210 180 u + (gap 210 192 u + gap 210 198 u)))))))))))))

witness₇ : T₇ 42 ≡ 1260
witness₇ = refl

exhaust₇ : rangeAll (λ u → leb 1260 (T₇ u)) 210 ≡ true
exhaust₇ = refl

minimal₇ : (u : ℕ) → u < 210 → 1260 ≤ T₇ u
minimal₇ u h =
  lebSound 1260 (T₇ u) (soundRange (λ v → leb 1260 (T₇ v)) 210 exhaust₇ u h)

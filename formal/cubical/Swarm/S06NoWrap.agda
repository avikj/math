{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- S06NoWrap
--
-- The exact no-wrap boundary of notes/RATIONAL_PAIR_CHANNEL.md (absent from this repository) §3.
--
-- The finite Fourier projectors (3.1)-(3.2) of that note compute the
-- pushforward of a graded coefficient along ℤ ↠ ℤ/q.  They recover the
-- integer grade exactly when the grade set injects into ℤ/q, i.e. when
-- q divides no nonzero difference of grades.  The note offers only the
-- sufficient condition "the possible values of m+n lie in an interval
-- of length < q".
--
-- This module proves, over ℕ, with --safe and no postulates:
--
--   narrow→Sep    the interval condition is sufficient (the note's §3);
--   Family.sep    an explicit two-block family, separated modulo Q;
--   Family.diam   its diameter is exactly (k+1)·Q - 1.
--
-- Hence the interval condition is strictly sufficient, and its slack is
-- unbounded: at fixed modulus Q a separated grade set may be spread over
-- (k+1)·Q consecutive integers, for every k.  Separation is a property of
-- the difference set of the grade set, not of its diameter.
------------------------------------------------------------------------

module Swarm.S06NoWrap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  The unsigned difference of two grades
------------------------------------------------------------------------

gap : ℕ → ℕ → ℕ
gap a b = (a ∸ b) + (b ∸ a)

gap-sym : ∀ a b → gap a b ≡ gap b a
gap-sym a b = +-comm (a ∸ b) (b ∸ a)

gap-refl : ∀ a → gap a a ≡ 0
gap-refl a = cong₂ _+_ (n∸n a) (n∸n a)

n∸0 : ∀ n → n ∸ 0 ≡ n
n∸0 n = ∸+ n 0

-- when a ≤ b the gap is the honest difference
gap-le : ∀ a b → a ≤ b → gap a b ≡ b ∸ a
gap-le a b p = cong (_+ (b ∸ a)) (n∸m≡0 a b p)

∸≡0→≤ : ∀ m n → m ∸ n ≡ 0 → m ≤ n
∸≡0→≤ zero n _ = zero-≤
∸≡0→≤ (suc m) zero p = ⊥.rec (snotz p)
∸≡0→≤ (suc m) (suc n) p = suc-≤-suc (∸≡0→≤ m n p)

gap≡0→≡ : ∀ a b → gap a b ≡ 0 → a ≡ b
gap≡0→≡ a b p =
  ≤-antisym (∸≡0→≤ a b (fst (m+n≡0→m≡0×n≡0 p)))
            (∸≡0→≤ b a (snd (m+n≡0→m≡0×n≡0 p)))

-- gap is invariant under a common shift
gap-shift : ∀ c a b → gap (c + a) (c + b) ≡ gap a b
gap-shift c a b = cong₂ _+_ (∸-cancelˡ c a b) (∸-cancelˡ c b a)

-- a common strict bound on both entries bounds the gap
gap-bound : ∀ a b n → a < n → b < n → gap a b < n
gap-bound a b n p q with splitℕ-≤ a b
... | inl a≤b = subst (_< n) (sym (gap-le a b a≤b)) (≤<-trans (∸-≤ b a) q)
... | inr b<a =
  subst (_< n) (sym (gap-sym a b ∙ gap-le b a (<-weaken b<a)))
        (≤<-trans (∸-≤ a b) p)

------------------------------------------------------------------------
-- 2.  Separation:  the grade map is injective into ℤ/q
--
--    Sep S q  says  q ∣ (S i - S j)  implies  S i ≡ S j,
--    which is exactly injectivity of  (S followed by reduction mod q).
------------------------------------------------------------------------

Sep : {A : Type ℓ} (S : A → ℕ) (q : ℕ) → Type ℓ
Sep {A = A} S q = (i j : A) → q ∣ gap (S i) (S j) → S i ≡ S j

-- a divisor cannot divide a strictly smaller positive number
∣<→≡0 : ∀ q d → q ∣ d → d < q → d ≡ 0
∣<→≡0 q d h d<q with discreteℕ d 0
... | yes p = p
... | no ¬p = ⊥.rec (<-asym d<q (m∣n→m≤n ¬p h))

------------------------------------------------------------------------
-- Theorem A (§3 of RATIONAL_PAIR_CHANNEL, generalised and proved):
-- a grade set contained in an interval of length < q is separated.
------------------------------------------------------------------------

narrow→Sep : {A : Type ℓ} (S : A → ℕ) (q : ℕ)
           → ((i j : A) → gap (S i) (S j) < q)
           → Sep S q
narrow→Sep S q narrow i j h = gap≡0→≡ _ _ (∣<→≡0 q _ h (narrow i j))

------------------------------------------------------------------------
-- 3.  The arithmetic needed to refute divisibility
------------------------------------------------------------------------

-- q ∣ (q + m)  →  q ∣ m,  for q > 0
∣-cancel-add : ∀ q m → 0 < q → q ∣ (q + m) → q ∣ m
∣-cancel-add q m qpos h with ∣-untrunc h
... | (zero  , e) =
  ⊥.rec (¬-<-zero (subst (0 <_) (fst (m+n≡0→m≡0×n≡0 (sym e))) qpos))
... | (suc c , e) = ∣ c , inj-m+ {q} e ∣₁

-- the residue obstruction:  q never divides  c·q + r  when 0 < r < q
q∤ : ∀ q c r → 0 < r → r < q → ¬ (q ∣ (c · q + r))
q∤ q zero r rpos rlt h =
  ⊥.rec (¬-<-zero (subst (0 <_) (∣<→≡0 q r h rlt) rpos))
q∤ q (suc c) r rpos rlt h =
  q∤ q c r rpos rlt
    (∣-cancel-add q (c · q + r) (≤<-trans zero-≤ rlt)
      (subst (q ∣_) (sym (+-assoc q (c · q) r)) h))

------------------------------------------------------------------------
-- 4.  The witness family
--
--   B = suc b  (block length),  Q = B + B  (= 2B, the modulus),
--   S = { 0, …, B-1 }  ∪  { k·Q + B, …, k·Q + 2B-1 }.
--
--   Residues mod Q: the low block occupies {0,…,B-1}, the high block
--   occupies {B,…,2B-1}.  Disjoint, so S is separated modulo Q, while
--   the diameter of S is k·Q + 2B - 1 = (k+1)·Q - 1, unbounded in k.
------------------------------------------------------------------------

module Family (b k : ℕ) where

  B : ℕ
  B = suc b

  Q : ℕ
  Q = B + B

  Blk : Type₀
  Blk = Σ[ j ∈ ℕ ] (j < B)

  Idx : Type₀
  Idx = Bool × Blk

  base : ℕ
  base = k · Q + B

  S : Idx → ℕ
  S (false , j , _) = j
  S (true  , j , _) = base + j

  -- the two same-block cases are narrow
  low-gap : (i j : Blk) → gap (S (false , i)) (S (false , j)) < Q
  low-gap (i , pi) (j , pj) = <≤-trans (gap-bound i j B pi pj) ≤SumLeft

  high-gap : (i j : Blk) → gap (S (true , i)) (S (true , j)) < Q
  high-gap (i , pi) (j , pj) =
    subst (_< Q) (sym (gap-shift base i j))
          (<≤-trans (gap-bound i j B pi pj) ≤SumLeft)

  -- the cross case: the gap has the shape k·Q + r with 0 < r < Q
  cross-form : (i j : Blk)
             → gap (S (false , i)) (S (true , j))
               ≡ k · Q + ((B + fst j) ∸ fst i)
  cross-form (i , pi) (j , pj) =
      gap-le i (base + j) i≤hi
    ∙ cong (_∸ i) (sym (+-assoc (k · Q) B j))
    ∙ sym (≤-∸-k i≤Bj)
    where
      i≤Bj : i ≤ B + j
      i≤Bj = ≤-trans (<-weaken pi) ≤SumLeft
      i≤hi : i ≤ base + j
      i≤hi = subst (i ≤_) (+-assoc (k · Q) B j)
                   (≤-trans i≤Bj ≤SumRight)

  cross-pos : (i j : Blk) → 0 < ((B + fst j) ∸ fst i)
  cross-pos (i , pi) (j , pj) = n∸l>0 (B + j) i (<≤-trans pi ≤SumLeft)

  cross-lt : (i j : Blk) → ((B + fst j) ∸ fst i) < Q
  cross-lt (i , pi) (j , pj) = ≤<-trans (∸-≤ (B + j) i) (<-k+ pj)

  cross : (i j : Blk) → ¬ (Q ∣ gap (S (false , i)) (S (true , j)))
  cross i j h =
    q∤ Q k ((B + fst j) ∸ fst i) (cross-pos i j) (cross-lt i j)
       (subst (Q ∣_) (cross-form i j) h)

  ------------------------------------------------------------------
  -- The family is separated modulo Q.
  ------------------------------------------------------------------
  sep : Sep S Q
  sep (false , i) (false , j) h =
    gap≡0→≡ _ _ (∣<→≡0 Q _ h (low-gap i j))
  sep (false , i) (true  , j) h = ⊥.rec (cross i j h)
  sep (true  , i) (false , j) h =
    ⊥.rec (cross j i (subst (Q ∣_) (gap-sym (S (true , i)) (S (false , j))) h))
  sep (true  , i) (true  , j) h =
    gap≡0→≡ _ _ (∣<→≡0 Q _ h (high-gap i j))

  ------------------------------------------------------------------
  -- Its diameter is exactly (k+1)·Q - 1.
  ------------------------------------------------------------------
  lo : Idx
  lo = (false , 0 , suc-≤-suc zero-≤)

  hi : Idx
  hi = (true , b , ≤-refl)

  diam : suc (gap (S lo) (S hi)) ≡ suc k · Q
  diam =
      cong suc (gap-le 0 (base + b) zero-≤ ∙ n∸0 (base + b))
    ∙ cong suc (sym (+-assoc (k · Q) B b))
    ∙ sym (+-suc (k · Q) (B + b))
    ∙ cong (k · Q +_) (sym (+-suc B b))
    ∙ +-comm (k · Q) Q

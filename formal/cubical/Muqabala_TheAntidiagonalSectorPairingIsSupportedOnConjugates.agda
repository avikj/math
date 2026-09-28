{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Muqābala — the antidiagonal sector pairing is supported on conjugates
--
-- SOURCE AND PRIORITY, stated before anything is claimed.
--
-- The operation this file performs on every line is *al-muqbala*:
-- confrontation — cancelling like terms standing on the two sides — and
-- its partner *al-jabr*, restoration, putting back what a sign removed.
-- Both are named in the title of the book that names algebra:
-- MUAMMAD IBN MS AL-KHWRIZM, *al-Kitb al-mukhtaar f isb
-- al-jabr wa'l-muqbala*, Baghdad, c. 820 CE.  The whole content of
-- `sgnSq` and `muqabala` below is that (+1)(+1) and (−1)(−1) confront
-- the unit and cancel, and that +x and −x confront each other and cancel.
--
-- The rule of signs used pointwise here — a product of two signed
-- quantities determined by the four-case table — is stated in general
-- form by AL-SAMAWʾAL AL-MAGHRIB, *al-Bhir f'l-jabr*, c. 1150 CE,
-- which reports it from AL-KARAJ, *al-Fakhr*, c. 1010 CE, together with
-- the law of indices extended to negative exponents and the regressive
-- inductive argument for the binomial array.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS ABOUT, and where it comes from in this repository.
--
-- `collab/messages/goldbach-machine/direct-minor-shadow.md` (absent from this repository)
-- Theorem 4.1 and Proposition 4.2 construct, for a
-- prime r ≡ 3 (mod 4) dividing an even N with N > 2r, the two
-- nonnegative prime-supported weights
--
--     ϑ_{r,±}(n) = ϑ(n)·(1 ± χ_r(n))·[r ∤ n]
--
-- and prove that BOTH self-convolutions vanish at N while
-- R_ϑ(N) = ½ (ϑ_{r,+} * ϑ_{r,−})(N).   The engine is χ_r(−1) = −1: the
-- complementation n ↦ N − n reverses the character's sign.
-- `mixed-sector-prescribed-center.md` (absent from this repository) Theorem 5.1 runs the same move with
-- two characters, one visible and one hidden.
--
-- This module isolates the algebra of that engine at k characters
-- instead of one or two, and states it as what it is: a statement about
-- which pairs of (ℤ/2)^k-isotypic sectors can pair at all.
--
--   * `muqabala`   — the pointwise cancellation, k = 1, no hypotheses.
--   * `vanish`     — THE THEOREM.  If two sign vectors AGREE in even one
--                    coordinate, their antidiagonal sector product is
--                    identically zero.  So the pairing is supported on
--                    the 2^k conjugate pairs (s , ¬s) out of the 4^k
--                    ordered pairs.
--   * `conjugate`  — on a conjugate pair the product is not merely
--                    nonzero: it is 2^k times the LEFT sector's own
--                    weight, pointwise.  That is where the factor ½ in
--                    Proposition 4.2 comes from, and it is where the k
--                    ≥ 2 case stops being a restatement of k = 1.
--   * `pairingIsProduct` — the bridge: `paired` is genuinely the product
--                    of the two sector weights, the left one read at a
--                    and the right one read at σ a.  This is the only
--                    place `odd` is used.
--
-- What `vanish` says about the shadow: the self-annihilating weights of
-- direct-minor-shadow.md (absent from this repository) are not k separate accidents.  They are the
-- diagonal s = t of one pairing law, and the law also kills every partly
-- agreeing pair — 4^k − 2^k of the 4^k ordered pairs.
--
------------------------------------------------------------------------

module Muqabala_TheAntidiagonalSectorPairingIsSupportedOnConjugates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Int
open import Cubical.Data.Int.Properties using (·Comm ; ·Assoc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit*)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 0.  Signs.  The rule of signs, as a four-case table.
------------------------------------------------------------------------

-- `true` is +1 and `false` is −1.  Nothing below depends on the choice.
sgn : Bool → ℤ
sgn true  = pos 1
sgn false = negsuc 0

-- al-Samawʾal's rule of signs, in the only form this file needs:
-- a product of two signs is a sign, and its square is the unit.
sgnSq : (b c : Bool) → (sgn b · sgn c) · (sgn b · sgn c) ≡ pos 1
sgnSq true  true  = refl
sgnSq true  false = refl
sgnSq false true  = refl
sgnSq false false = refl

------------------------------------------------------------------------
-- 1.  al-muqbala: the two confrontations, k = 1.
------------------------------------------------------------------------

-- (1 + x)(1 − x) = 1 − x² = 1 − 1 = 0, for x a product of two signs.
-- The first equality is the confrontation of the cross terms; the second
-- is `sgnSq`; the third is the confrontation of the two units.
muqabala : (b c : Bool)
         → (pos 1 + sgn b · sgn c) · (pos 1 - sgn b · sgn c) ≡ pos 0
muqabala true  true  = refl
muqabala true  false = refl
muqabala false true  = refl
muqabala false false = refl

-- On a CONJUGATE pair the two factors do not confront: they coincide,
-- and the square of a doubled sign is twice it.  (1 + x)² = 2(1 + x).
conjugateSquare : (b c : Bool)
  → (pos 1 + sgn b · sgn c) · (pos 1 + sgn b · sgn c)
  ≡ pos 2 · (pos 1 + sgn b · sgn c)
conjugateSquare true  true  = refl
conjugateSquare true  false = refl
conjugateSquare false true  = refl
conjugateSquare false false = refl

-- al-jabr, restoration: the two sectors of a conjugate pair sum back to
-- twice the original weight.  This is ϑ = ½(ϑ₊ + ϑ₋).
jabr : (b c : Bool)
     → (pos 1 + sgn b · sgn c) + (pos 1 - sgn b · sgn c) ≡ pos 2
jabr true  true  = refl
jabr true  false = refl
jabr false true  = refl
jabr false false = refl

-- Flipping the character's value negates the term it contributes.  This
-- is χ_r(N − n) = −χ_r(n), and it is the only arithmetic input.
flipRight : (b e : Bool)
  → pos 1 + sgn b · sgn (not e) ≡ pos 1 - sgn b · sgn e
flipRight true  true  = refl
flipRight true  false = refl
flipRight false true  = refl
flipRight false false = refl

-- The same identity read the other way: negating the SIGN undoes the
-- subtraction.  Used for the conjugate case, where t = ¬s.
flipSign : (b e : Bool)
  → pos 1 - sgn (not b) · sgn e ≡ pos 1 + sgn b · sgn e
flipSign true  true  = refl
flipSign true  false = refl
flipSign false true  = refl
flipSign false false = refl

------------------------------------------------------------------------
-- 2.  Characters that the complementation makes odd.
------------------------------------------------------------------------

-- A is the domain the weight lives on (think: integers below N).
-- σ is the complementation a ↦ N − a.
-- An `OddChar` is a two-valued character whose value σ reverses: this is
-- exactly χ_r(−1) = −1 together with r | N, and it is the whole
-- arithmetic input of direct-minor-shadow.md (absent from this repository) Theorem 4.1.
record OddChar {A : Type ℓ} (σ : A → A) : Type ℓ where
  constructor oddChar
  field
    χ   : A → Bool
    odd : (a : A) → χ (σ a) ≡ not (χ a)

open OddChar public

------------------------------------------------------------------------
-- 3.  A cell: k characters, and for each one a sign on the left factor
--     and a sign on the right factor.
------------------------------------------------------------------------

-- `Cell σ` is the pairing datum for two sectors s , t over the SAME k
-- characters.  Carrying the two signs together is what makes alignment
-- of the two sectors a fact of the type rather than a side condition in
-- prose.
Cell : {A : Type ℓ} → (A → A) → Type ℓ
Cell σ = List (OddChar σ × Bool × Bool)

-- ∏ᵢ (1 + sᵢ·χᵢ(a)) — the left sector's weight at a, up to the common
-- factor f(a), which never participates and is therefore absent.
left : {A : Type ℓ} {σ : A → A} → Cell σ → A → ℤ
left []                 a = pos 1
left ((c , s , _) ∷ xs) a = (pos 1 + sgn s · sgn (χ c a)) · left xs a

-- ∏ᵢ (1 + tᵢ·χᵢ(σ a)) — the right sector's weight at the complementary
-- point σ a.  This is the factor the convolution actually multiplies by.
right : {A : Type ℓ} {σ : A → A} → Cell σ → A → ℤ
right []                            a = pos 1
right {σ = σ} ((c , _ , t) ∷ xs) a = (pos 1 + sgn t · sgn (χ c (σ a))) · right xs a

-- The same product with oddness already applied: ∏ᵢ (1 − tᵢ·χᵢ(a)).
rightAt : {A : Type ℓ} {σ : A → A} → Cell σ → A → ℤ
rightAt []                 a = pos 1
rightAt ((c , _ , t) ∷ xs) a = (pos 1 - sgn t · sgn (χ c a)) · rightAt xs a

-- The interleaved product ∏ᵢ (1 + sᵢεᵢ)(1 − tᵢεᵢ), εᵢ = χᵢ(a).
paired : {A : Type ℓ} {σ : A → A} → Cell σ → A → ℤ
paired []                 a = pos 1
paired ((c , s , t) ∷ xs) a =
  ((pos 1 + sgn s · sgn (χ c a)) · (pos 1 - sgn t · sgn (χ c a)))
    · paired xs a

------------------------------------------------------------------------
-- 4.  THE THEOREM.  Agreement in one coordinate kills the pairing.
------------------------------------------------------------------------

-- `Agree E` : somewhere in the cell, the left sign and the right sign
-- are the same Boolean.  Defined by recursion on the list rather than as
-- an indexed family, so that no proof below matches on a constructor of
-- an indexed datatype — cubical Agda warns on that.
Agree : {A : Type ℓ} {σ : A → A} → Cell σ → Type ℓ
Agree []                 = ⊥*
Agree ((_ , s , t) ∷ xs) = (s ≡ t) ⊎ Agree xs

·Zeroˡ : (x : ℤ) → pos 0 · x ≡ pos 0
·Zeroˡ x = refl

·Zeroʳ : (x : ℤ) → x · pos 0 ≡ pos 0
·Zeroʳ x = ·Comm x (pos 0)

-- If the two sign vectors agree in ANY ONE coordinate, the product of
-- the two sectors at the antidiagonal point is zero — pointwise, at
-- every a, with no hypothesis on the other coordinates and none on f.
--
-- Consequence, and it is the reason this file exists: of the 4^k ordered
-- pairs of sectors, only the 2^k conjugate pairs (s , ¬s) can pair.  The
-- vanishing self-convolutions of direct-minor-shadow.md (absent from this repository) are the case
-- s = t at k = 1, which is `here refl`.
vanish : {A : Type ℓ} {σ : A → A} (E : Cell σ) (a : A)
       → Agree E → paired E a ≡ pos 0
vanish ((c , s , t) ∷ xs) a (inl p) =
    cong (λ u → ((pos 1 + sgn s · sgn (χ c a))
                   · (pos 1 - sgn u · sgn (χ c a))) · paired xs a)
         (sym p)
  ∙ cong (_· paired xs a) (muqabala s (χ c a))
  ∙ ·Zeroˡ (paired xs a)
vanish ((c , s , t) ∷ xs) a (inr h) =
    cong (((pos 1 + sgn s · sgn (χ c a))
             · (pos 1 - sgn t · sgn (χ c a))) ·_)
         (vanish xs a h)
  ∙ ·Zeroʳ ((pos 1 + sgn s · sgn (χ c a))
              · (pos 1 - sgn t · sgn (χ c a)))

------------------------------------------------------------------------
-- 5.  The bridge: `paired` really is the product of the two sectors.
------------------------------------------------------------------------

-- (p · x) · (q · y) ≡ (p · q) · (x · y), in ℤ.
shuffle : (p q x y : ℤ) → (p · x) · (q · y) ≡ (p · q) · (x · y)
shuffle p q x y =
    sym (·Assoc p x (q · y))
  ∙ cong (p ·_) (·Assoc x q y ∙ cong (_· y) (·Comm x q) ∙ sym (·Assoc q x y))
  ∙ ·Assoc p q (x · y)

-- The right sector read at σ a is the right sector with every character
-- sign reversed.  ONLY here is `odd` used.
rightIsFlipped : {A : Type ℓ} {σ : A → A} (E : Cell σ) (a : A)
               → right E a ≡ rightAt E a
rightIsFlipped []                 a = refl
rightIsFlipped {σ = σ} ((c , s , t) ∷ xs) a =
    cong (λ z → (pos 1 + sgn t · sgn z) · right xs a) (odd c a)
  ∙ cong (_· right xs a) (flipRight t (χ c a))
  ∙ cong ((pos 1 - sgn t · sgn (χ c a)) ·_) (rightIsFlipped xs a)

bridge : {A : Type ℓ} {σ : A → A} (E : Cell σ) (a : A)
       → left E a · rightAt E a ≡ paired E a
bridge []                 a = refl
bridge ((c , s , t) ∷ xs) a =
    shuffle (pos 1 + sgn s · sgn (χ c a))
            (pos 1 - sgn t · sgn (χ c a))
            (left xs a) (rightAt xs a)
  ∙ cong (((pos 1 + sgn s · sgn (χ c a))
             · (pos 1 - sgn t · sgn (χ c a))) ·_)
         (bridge xs a)

-- `paired` is the honest object: the left sector at a times the right
-- sector at σ a.  Everything proved about `paired` is therefore a
-- statement about the antidiagonal term of a convolution.
pairingIsProduct : {A : Type ℓ} {σ : A → A} (E : Cell σ) (a : A)
                 → left E a · right E a ≡ paired E a
pairingIsProduct E a =
  cong (left E a ·_) (rightIsFlipped E a) ∙ bridge E a

------------------------------------------------------------------------
-- 6.  The conjugate pairs, where the pairing does NOT vanish.
------------------------------------------------------------------------

-- `Conj E` : in every coordinate the right sign is the negation of the
-- left sign.  This is t = ¬s, the σ-conjugate sector.
Conj : {A : Type ℓ} {σ : A → A} → Cell σ → Type ℓ
Conj []                 = Unit*
Conj ((_ , s , t) ∷ xs) = (t ≡ not s) × Conj xs

twoPow : ℕ → ℤ
twoPow zero    = pos 1
twoPow (suc n) = pos 2 · twoPow n

-- On a conjugate pair the antidiagonal product is 2^k times the left
-- sector's own weight — pointwise, at every a.
--
-- At k = 1 this is the factor ½ of direct-minor-shadow.md (absent from this repository) (32):
-- summing over the antidiagonal, (ϑ₊ * ϑ₋)(N) = 2·(ϑ * ϑ)(N).
-- At k ≥ 2 the right-hand side still carries the left sector's own sign
-- vector s, which is what the k = 1 statement cannot see, and which is
-- where the conductors stop being interchangeable.
conjugate : {A : Type ℓ} {σ : A → A} (E : Cell σ) (a : A)
          → Conj E → paired E a ≡ twoPow (length E) · left E a
conjugate []                 a _        = refl
conjugate ((c , s , t) ∷ xs) a (q , hs) =
    cong (λ u → ((pos 1 + sgn s · sgn (χ c a))
                   · (pos 1 - sgn u · sgn (χ c a))) · paired xs a) q
  ∙ cong (λ w → ((pos 1 + sgn s · sgn (χ c a)) · w) · paired xs a)
         (flipSign s (χ c a))
  ∙ cong (_· paired xs a) (conjugateSquare s (χ c a))
  ∙ cong ((pos 2 · (pos 1 + sgn s · sgn (χ c a))) ·_) (conjugate xs a hs)
  ∙ shuffle (pos 2) (twoPow (length xs))
            (pos 1 + sgn s · sgn (χ c a)) (left xs a)

------------------------------------------------------------------------
-- 7.  The factor ½, pinned at k = 1.
------------------------------------------------------------------------

-- At one character there are exactly two conjugate pairs, (+,−) and
-- (−,+), and pointwise their antidiagonal products already sum to 4:
--
--     (1+ε)(1+ε) + (1−ε)(1−ε) = 2(1+ε) + 2(1−ε) = 4.
--
-- Summing this over the antidiagonal gives
-- (ϑ₊ * ϑ₋)(N) + (ϑ₋ * ϑ₊)(N) = 4·(ϑ * ϑ)(N), i.e. the ½ of
-- direct-minor-shadow.md (absent from this repository) (32) — and it is pinned here BEFORE any
-- summation, so the factor cannot be a bookkeeping slip in the sum.
oneCharSum : {A : Type ℓ} {σ : A → A} (c : OddChar σ) (a : A)
  →   paired ((c , true  , false) ∷ []) a
    + paired ((c , false , true ) ∷ []) a
  ≡ pos 4
oneCharSum c a = lemma (χ c a)
  where
    lemma : (e : Bool)
      →   ((pos 1 + sgn true  · sgn e) · (pos 1 - sgn false · sgn e)) · pos 1
        + ((pos 1 + sgn false · sgn e) · (pos 1 - sgn true  · sgn e)) · pos 1
      ≡ pos 4
    lemma true  = refl
    lemma false = refl

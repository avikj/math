{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ReversalInvariant
--
-- Reversal as an involution whose invariants are exactly the
-- achromatic data.
--
-- The corpus's one symmetry that every colored ray reports identically
-- is the reflection/reversal ℤ/2.  notes/CROSS_LENS.md (absent from this repository) §3 records the
-- join nobody used: "four vocabularies, one symmetry, no cross-citation"
-- — the "up to reflection" of every rigidity theorem
-- (PARITY_RIGIDITY Thm A′′), the pairing Res(g, g(−x)) behind the whole
-- factor-exclusion tower (PARITY_RESULTANT Thm 1b), the endian class of
-- the digit chart (DIGIT_CRYSTAL; formalized at word level in
-- NaturalMachine/Endian.agda, cited, NOT imported — it is parameterized
-- by a base k and carries the D/E Klein-four story we do not need), and
-- the K-parity shift of KBOUNDARY §4.4.
--
-- This module is the smallest carrier of that one ℤ/2, with its blind
-- and its sighted observables separated by proof:
--
--   (a) rev is an involution on List A            [library's rev-rev]
--   (b) length is reversal-BLIND (achromatic)     [length-rev, here]
--   (c) head? is reversal-SIGHTED (chromatic)     [explicit witness]
--   (d) the fixed locus Palindrome = (rev xs ≡ xs), with one witness
--       and one refutation — where the two readings coincide.
--
-- ATTRIBUTION:
--   * rev            : Cubical/Data/List/Base.agda        (library)
--   * rev-rev        : Cubical/Data/List/Properties.agda  (library)
--   * cons-inj₁      : Cubical/Data/List/Properties.agda  (library)
--   * just-inj       : Cubical/Data/Maybe/Properties.agda (library)
--   * true≢false, false≢true : Cubical/Data/Bool/Properties.agda (library)
--   The library has NO length-rev (checked: only length-map, in
--   Cubical/Data/List/Properties.agda); length-snoc and length-rev below are the only
--   inductions this file performs.
------------------------------------------------------------------------

module ReversalInvariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; just-inj)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; false≢true)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level
    A : Type ℓ

------------------------------------------------------------------------
-- (a) The involution.  This is the LIBRARY's theorem, re-exported under
-- the ray's name with attribution: rev-rev in
-- Cubical/Data/List/Properties.agda (lines 37–39 of the checked copy).
-- Nothing is re-proved here.

rev-involution : (xs : List A) → rev (rev xs) ≡ xs
rev-involution = rev-rev

-- The ℤ/2 action packaged as a self-equivalence of List A: rev is its
-- own inverse, both triangle identities are rev-rev itself.

revIso : Iso (List A) (List A)
revIso = iso rev rev rev-rev rev-rev

revEquiv : List A ≃ List A
revEquiv = isoToEquiv revIso

-- The univalent form (CROSS_LENS §3, "reflection is a path, not a
-- coincidence"): ua turns the involution into a self-path of List A in
-- the universe.  Achromatic data = what transports trivially along it.

revPath : List A ≡ List A
revPath = ua revEquiv

------------------------------------------------------------------------
-- (b) The achromatic observable: length is reversal-blind.
-- Not in the library (only length-map is); one two-line induction via
-- a snoc helper, avoiding any appeal to +-comm.

length-snoc : (xs : List A) (y : A) → length (xs ++ [ y ]) ≡ suc (length xs)
length-snoc []       y = refl
length-snoc (x ∷ xs) y = cong suc (length-snoc xs y)

length-rev : (xs : List A) → length (rev xs) ≡ length xs
length-rev []       = refl
length-rev (x ∷ xs) = length-snoc (rev xs) x ∙ cong suc (length-rev xs)

------------------------------------------------------------------------
-- (c) The chromatic observable: head? sees the reversal.
-- head? is Maybe-valued so it is total; on the two-letter word
-- true ∷ false ∷ [] the two readings disagree, and Maybe Bool is
-- discrete enough (just-inj + true≢false, both library) to make the
-- disagreement a proof, not a remark.

head? : List A → Maybe A
head? []      = nothing
head? (x ∷ _) = just x

-- The chromatic witness word.
w₂ : List Bool
w₂ = true ∷ false ∷ []

head?-w₂ : head? w₂ ≡ just true
head?-w₂ = refl

head?-rev-w₂ : head? (rev w₂) ≡ just false
head?-rev-w₂ = refl

just-true≢just-false : ¬ (Path (Maybe Bool) (just true) (just false))
just-true≢just-false p = true≢false (just-inj true false p)

-- head? is NOT reversal-blind: no pointwise identification of
-- head? ∘ rev with head? exists, already on Bool.
head?-sees-rev : ¬ ((xs : List Bool) → head? (rev xs) ≡ head? xs)
head?-sees-rev blind = just-true≢just-false (sym (blind w₂))

------------------------------------------------------------------------
-- (d) The fixed locus of the ℤ/2 action: palindromes, where the two
-- readings coincide and the chromatic/achromatic distinction closes up.

Palindrome : List A → Type _
Palindrome xs = rev xs ≡ xs

-- One fixed point, by computation alone.
pal₃ : Palindrome (true ∷ false ∷ true ∷ [])
pal₃ = refl

-- One non-fixed point: w₂ is moved by the action (cons-inj₁ is the
-- library's, Cubical/Data/List/Properties.agda).
¬pal-w₂ : ¬ Palindrome w₂
¬pal-w₂ p = false≢true (cons-inj₁ p)

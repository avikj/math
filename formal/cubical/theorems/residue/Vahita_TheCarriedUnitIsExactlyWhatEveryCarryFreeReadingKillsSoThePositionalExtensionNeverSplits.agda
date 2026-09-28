{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- वहित — the carried.  (Compound built here from √vah, "to carry"; no
-- source text is claimed for the term — the mathematics below is the
-- atlas's, the name is this module's.)  The complement of Sthana: that
-- module built the positional word whose addition arrives WITH NO CARRY
-- RULE; this one proves the carry cannot be dispensed with.  It is
-- runtime/atlas/residual.py (absent from this repository)'s splitting_exponent_argument (ATLAS_OF_N
-- Prop. 2.11: the carry class vanishes iff the extension splits iff the
-- exponents agree), at its minimal instance b = 2, one digit — checked.
--
-- THE TWO ADDITIONS on a two-bit counter (low , high):
--   • WITH carry  (+c) : low bits xor; their AND carries into the high
--     bit — Āryabhaṭa's sthānāt sthānaṃ, the tenfold at base two.  This
--     is ℤ/4 in its positional presentation.
--   • WITHOUT carry (⊕) : componentwise xor — ℤ/2 ⊕ ℤ/2, the digits kept
--     apart, exponent 2: everything doubles to zero.
--
-- PROVED:
--   §1  the exponents disagree: under ⊕ every x has x ⊕ x ≡ 0, while
--       under +c the unit doubles to the CARRIED UNIT (0,1) ≢ 0.
--   §2  THE KERNEL OF FORGETTING: every homomorphism h from (+c) to (⊕)
--       sends the carried unit to zero — h (0,1) ≡ h (0,0) ≡ (0,0).  The
--       carry is exactly what any carry-free reading kills: h cannot be
--       injective, no isomorphism exists, the extension
--       ℤ/2 → ℤ/4 → ℤ/2 never splits.  Positional notation's cocycle is
--       essential — the receipt of the tenfold is the carry, and reading
--       the digits separately is the unreceipted compression that loses it.
--
-- Sources for the mathematics: runtime/atlas/residual.py (absent from this repository)
-- Prop. 2.11; ryabhaa, ryabhaya Gaitapda 2 (499) for sthna.
------------------------------------------------------------------------

module Vahita_TheCarriedUnitIsExactlyWhatEveryCarryFreeReadingKillsSoThePositionalExtensionNeverSplits where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; true≢false; not)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

-- the two-bit counter.
B² : Type
B² = Bool × Bool

-- low-bit AND: the carry condition.
_∧b_ : Bool → Bool → Bool
true  ∧b b = b
false ∧b _ = false

-- WITH carry: low bits xor, carry (their AND) folded into the high bits.
_+c_ : B² → B² → B²
(l₁ , h₁) +c (l₂ , h₂) = (l₁ ⊕ l₂) , ((h₁ ⊕ h₂) ⊕ (l₁ ∧b l₂))

-- WITHOUT carry: componentwise xor.
_⊕²_ : B² → B² → B²
(l₁ , h₁) ⊕² (l₂ , h₂) = (l₁ ⊕ l₂) , (h₁ ⊕ h₂)

zero² one² carried : B²
zero²   = false , false
one²    = true  , false     -- the unit, low place
carried = false , true      -- the carried unit, high place

------------------------------------------------------------------------
-- §1 · THE EXPONENTS DISAGREE (lcm 2 2 = 2 < 4 = 2·2).
xor-self : (b : Bool) → b ⊕ b ≡ false
xor-self true  = refl
xor-self false = refl

⊕²-self : (x : B²) → x ⊕² x ≡ zero²
⊕²-self (l , h) i = xor-self l i , xor-self h i

-- while under the carry the unit doubles to the CARRIED unit:
unit-doubles-to-carry : one² +c one² ≡ carried
unit-doubles-to-carry = refl

carried≢zero : ¬ (carried ≡ zero²)
carried≢zero p = true≢false (cong snd p)

------------------------------------------------------------------------
-- §2 · THE KERNEL OF FORGETTING.  Any homomorphism from (+c) to (⊕²)
-- sends the carried unit AND zero to zero — so it conflates them: the
-- carry is exactly what the carry-free reading kills.
module _ (h : B² → B²)
         (hom : (x y : B²) → h (x +c y) ≡ (h x ⊕² h y)) where

  -- h zero² ≡ 0: zero is its own carry-free double.
  kills-zero : h zero² ≡ zero²
  kills-zero = cong h (sym lem) ∙ hom zero² zero² ∙ ⊕²-self (h zero²)
    where
    lem : zero² +c zero² ≡ zero²
    lem = refl

  -- h carried ≡ 0: the carried unit is the double of the unit.
  kills-carry : h carried ≡ zero²
  kills-carry =
    cong h (sym unit-doubles-to-carry) ∙ hom one² one² ∙ ⊕²-self (h one²)

  -- the conflation: carried and zero, distinct, one image.
  conflates : h carried ≡ h zero²
  conflates = kills-carry ∙ sym kills-zero

  -- hence h is not injective — no embedding, no isomorphism, no splitting.
  not-injective : ¬ ((x y : B²) → h x ≡ h y → x ≡ y)
  not-injective inj = carried≢zero (inj carried zero² conflates)

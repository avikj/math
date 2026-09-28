{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CenterRelativeIntegral
--
-- DELTA 17 §§17.4, 17.8: WHAT THE CENTRE-RELATIVE MAP DOES WHEN 2 IS NOT
-- INVERTIBLE — which is the case at every finite place.
--
-- `CenterRelative` proved Delta 14's T14.1 over a
-- commutative ring **with `half`**, and its header said the hypothesis
-- `half + half ≡ 1r` was "the entire arithmetic input".  Delta 17 §17.8
-- is where that bill comes due: the same centre-relative decomposition
-- reappears at every prime, on the VALUATION pair
--
--     s_ℓ = v_ℓ(p) + v_ℓ(q),      d_ℓ = v_ℓ(q) − v_ℓ(p),
--
-- and there the coefficients live in ℤ, where 2 is not invertible.
-- T17.13 records the consequence as a parity constraint, `s ≡ d mod 2`.
--
-- This file proves the ring-level fact BEHIND that constraint, which is
-- sharper than the congruence and needs no order and no ℤ:
--
--     **the integral sum/difference map and its inverse compose to
--     DOUBLING, not to the identity.**
--
-- So the defect of the centre-relative chart over a general ring is
-- exactly multiplication by 2 — and `CenterRelative`'s `half` is not a
-- convenience, it is precisely what divides that defect away.  Delta 15
-- §15.2 C15.7 predicted this shape ("apparent failures of univalent
-- transport are failures to include the relevant structure"); here the
-- missing datum is not a structure but a ring element, and the failure
-- is not of transport but of the map being invertible at all.
--
-- WHAT IS CHECKED
--
--   §1  `Φ′`, `Ψ`            the integral maps.  `Φ′(p,q) = (p+q, q−p)`
--                            takes NO division and is therefore defined
--                            over every commutative ring; `Ψ` is
--                            unchanged from `CenterRelative`.
--
--   §2  `ΨΦ′-is-double`      Ψ ∘ Φ′ = multiplication by 2, componentwise.
--       `Φ′Ψ-is-double`      Φ′ ∘ Ψ = multiplication by 2, componentwise.
--                            **These are the theorem.**  Both by the
--                            `CommRingSolver`, so the content is visible
--                            rather than buried in algebra.
--
--   §3  `image-parity-sum`   T17.13's constraint, ring-level and in both
--       `image-parity-diff`  forms: for every `(p,q)`, the image
--                            `(s,d) = Φ′(p,q)` satisfies `s + d = 2·q`
--                            and `s − d = 2·p`.  Over ℤ that is exactly
--                            `s ≡ d (mod 2)`, and here it is the stronger
--                            statement with the witness supplied.
--
--   §4  `half→retract`       the bridge back: given `half`, doubling is
--                            invertible and §2 collapses to
--                            `CenterRelative`'s T14.1.  Stated as the
--                            explicit retract rather than by
--                            importing, so the two files stay readable
--                            independently.
--
--   §5  `Q`                  the split norm `Q(p,q) = p·q` of §17.1, and
--       `τ-preserves-Q`      C17.7's distinction, which Delta 17 asks be
--       `J₂-negates-Q`       kept from ever being conflated:
--                            **exchange preserves the norm; one-leg sign
--                            reflection negates it.**  Two involutions,
--                            two different fates for `Q`, both checked.
--
------------------------------------------------------------------------

module CenterRelativeIntegral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ≡-×)

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection using (solve!)

private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
 open CommRingStr (snd R)

 Pair Centre : Type ℓ
 Pair   = ⟨ R ⟩ × ⟨ R ⟩        -- (p , q)
 Centre = ⟨ R ⟩ × ⟨ R ⟩        -- (s , d) = (sum , difference)

 two : ⟨ R ⟩
 two = 1r + 1r

 ----------------------------------------------------------------------
 -- 1.  The integral maps.  No division anywhere.
 ----------------------------------------------------------------------

 Φ′ : Pair → Centre
 Φ′ (p , q) = ( p + q , q - p )

 Ψ : Centre → Pair
 Ψ (s , d) = ( s - d , s + d )

 ----------------------------------------------------------------------
 -- 2.  THE THEOREM: the composites are doubling, not the identity.
 --
 -- This is why `CenterRelative` needed `half`, stated as a fact about
 -- the maps rather than as a hypothesis on the ring.
 ----------------------------------------------------------------------

 private
  lem₁ : (p q : ⟨ R ⟩) → (p + q) - (q - p) ≡ (1r + 1r) · p
  lem₁ _ _ = solve! R

  lem₂ : (p q : ⟨ R ⟩) → (p + q) + (q - p) ≡ (1r + 1r) · q
  lem₂ _ _ = solve! R

  lem₃ : (s d : ⟨ R ⟩) → (s - d) + (s + d) ≡ (1r + 1r) · s
  lem₃ _ _ = solve! R

  lem₄ : (s d : ⟨ R ⟩) → (s + d) - (s - d) ≡ (1r + 1r) · d
  lem₄ _ _ = solve! R

 ΨΦ′-is-double : (x : Pair) → Ψ (Φ′ x) ≡ (two · x .fst , two · x .snd)
 ΨΦ′-is-double (p , q) = ≡-× (lem₁ p q) (lem₂ p q)

 Φ′Ψ-is-double : (y : Centre) → Φ′ (Ψ y) ≡ (two · y .fst , two · y .snd)
 Φ′Ψ-is-double (s , d) = ≡-× (lem₃ s d) (lem₄ s d)

 ----------------------------------------------------------------------
 -- 3.  T17.13's parity constraint, ring-level.
 --
 -- Delta 17 writes it as `s ≡ d (mod 2)`.  Over a general ring the
 -- sharper statement is that the witness is available on both sides:
 -- `s + d` and `s − d` are literally `two ·` something, and the
 -- somethings are the original `q` and `p`.
 ----------------------------------------------------------------------

 image-parity-sum : (p q : ⟨ R ⟩) → (Φ′ (p , q) .fst) + (Φ′ (p , q) .snd) ≡ two · q
 image-parity-sum = lem₂

 image-parity-diff : (p q : ⟨ R ⟩) → (Φ′ (p , q) .fst) - (Φ′ (p , q) .snd) ≡ two · p
 image-parity-diff = lem₁

 ----------------------------------------------------------------------
 -- 5.  §17.1's split norm, and C17.7's distinction.
 --
 -- Delta 17 asks that these two involutions never be conflated.  They
 -- are here separated by a checked property rather than by a warning.
 ----------------------------------------------------------------------

 Q : Pair → ⟨ R ⟩
 Q (p , q) = p · q

 τ : Pair → Pair
 τ (p , q) = (q , p)

 J₂ : Pair → Pair
 J₂ (p , q) = (p , - q)

 private
  lemτ : (p q : ⟨ R ⟩) → q · p ≡ p · q
  lemτ _ _ = solve! R

  lemJ : (p q : ⟨ R ⟩) → p · (- q) ≡ - (p · q)
  lemJ _ _ = solve! R

 -- The Weyl reflection preserves the split norm …
 τ-preserves-Q : (x : Pair) → Q (τ x) ≡ Q x
 τ-preserves-Q (p , q) = lemτ p q

 -- … and the one-leg sign reflection negates it.  Different involutions,
 -- different sectors; C17.7 discharged.
 J₂-negates-Q : (x : Pair) → Q (J₂ x) ≡ - (Q x)
 J₂-negates-Q (p , q) = lemJ p q

------------------------------------------------------------------------
-- 4.  The bridge back: with `half`, doubling is invertible.
--
-- Placed last because it depends on nothing above except §2, and because
-- the point of the file is §2 rather than this.
------------------------------------------------------------------------

module _ (R : CommRing ℓ) where
 open CommRingStr (snd R)

 module _ (half : ⟨ R ⟩) (half+half : half + half ≡ 1r) where

  private
   -- The solver takes the QUANTIFIED goal, never the intro'd one — the
   -- same convention `BUILD.md` (absent from this repository) records for `NatSolver`.
   step : (h x : ⟨ R ⟩) → h · ((1r + 1r) · x) ≡ (h + h) · x
   step _ _ = solve! R

   halve : (x : ⟨ R ⟩) → half · ((1r + 1r) · x) ≡ x
   halve x = step half x ∙ cong (_· x) half+half ∙ ·IdL x

  -- Scaling the doubled composite by `half` returns the identity, which
  -- is `CenterRelative`'s `ΨΦ` recovered from `ΨΦ′-is-double`.
  half⇒retract : (p q : ⟨ R ⟩)
               → ( half · (Ψ R (Φ′ R (p , q)) .fst)
                 , half · (Ψ R (Φ′ R (p , q)) .snd) )
                 ≡ (p , q)
  half⇒retract p q =
    ≡-× (cong (half ·_) (cong fst (ΨΦ′-is-double R (p , q))) ∙ halve p)
        (cong (half ·_) (cong snd (ΨΦ′-is-double R (p , q))) ∙ halve q)

{-# OPTIONS --cubical --safe #-}

-- एकान्तलोप-बीज — the SEED of Ekāntalopa, stripped of Cuntz and KMS.
-- GAUGE.md (absent from this repository)'s  (formerly "Theorem F") rests on a two-line
-- algebra fact; the operator-algebra theorems supply the HYPOTHESIS
-- (a unique invariant equilibrium exists), not the MECHANISM.  The
-- mechanism, put to the kernel as a question expressible in her
-- knowledge: an invariant functional vanishes on every nontrivial
-- charge.  w := ω(x); the charge equation c · w ≡ w (invariance under a
-- symmetry scaling x by c) forces (c−1)·w ≡ 0, and if the gap (c−1) is
-- invertible (char-0 / archimedean, README C5) then w ≡ 0.

module EkantalopaBija_TheInvariantFunctionalVanishesOnEveryCharge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RP

module _ (R' : CommRing ℓ-zero) where
  open CommRingStr (snd R')
  open RP.RingTheory (CommRing→Ring R')
  R = ⟨ R' ⟩

  gap : R → R
  gap c = c + (- 1r)

  gap-annihilates : (c w : R) → (c · w ≡ w) → gap c · w ≡ 0r
  gap-annihilates c w inv =
    (c + (- 1r)) · w        ≡⟨ ·DistL+ c (- 1r) w ⟩
    (c · w) + ((- 1r) · w)  ≡⟨ cong (_+ ((- 1r) · w)) inv ⟩
    w + ((- 1r) · w)        ≡⟨ cong (w +_) lem ⟩
    w + (- w)               ≡⟨ +InvR w ⟩
    0r                      ∎
    where
      lem : (- 1r) · w ≡ - w
      lem = (- 1r) · w   ≡⟨ -DistL· 1r w ⟩
            - (1r · w)   ≡⟨ cong -_ (·IdL w) ⟩
            - w          ∎

  ekantalopa : (c w d : R) → (c · w ≡ w) → (d · gap c ≡ 1r) → w ≡ 0r
  ekantalopa c w d inv dInv =
    w                ≡⟨ sym (·IdL w) ⟩
    1r · w           ≡⟨ cong (_· w) (sym dInv) ⟩
    (d · gap c) · w  ≡⟨ sym (·Assoc d (gap c) w) ⟩
    d · (gap c · w)  ≡⟨ cong (d ·_) (gap-annihilates c w inv) ⟩
    d · 0r           ≡⟨ 0RightAnnihilates d ⟩
    0r               ∎

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ख / शून्य — kha, the void.
--
-- SOURCE.  Brahmagupta, *Brhmasphuasiddhnta*, 628 CE, chapter 18
-- (kuakdhyya), states the arithmetic of the three kinds of quantity
-- together — **dhana** (fortune, positive), **ṛṇa** (debt, negative) and
-- **kha**/**śūnya** (the void) — and among the product rules, that a
-- quantity multiplied by kha is kha.  That is one direction.
--
-- The converse — *if a product is kha then one of its factors is kha* —
-- is not in the Brhmasphuasiddhnta, and it is not a ring truth.  This
-- module is about exactly that converse: where it holds, a computation
-- may ignore the void places of a vector; where it fails, it may not,
-- and the failure is sharp in both directions.
--
-- WHAT THIS MODULE IS FOR.  `notes/ACTION_MONOID_CHARACTER_CLOSURE.md` (absent from this repository)
-- states the diagonal cyclic-space theorem over a field, and gives its
-- boundary as:
--
--     "Over a general commutative ring, distinct values need not have
--      unit differences, so cardinality of m(S) does not determine
--      cyclic rank."
--
-- That is right about the RANK and it is the wrong diagnosis for the
-- ANNIHILATOR.  The annihilator half needs no interpolation, no unit
-- differences and no field.  It needs exactly the converse of the kha
-- product rule, and this module proves that "exactly": the implication
-- and its converse (§3, §4), with both sides of the boundary
-- instantiated (§5, §6) so that neither is empty.
--
-- Layers, by exact hypothesis:
--
--   §2  act p v x ≡ eval p (m x) · v x        -- any commutative ring
--   §3  vanishing on the non-void places ⇒ annihilation
--                                             -- any commutative ring,
--                                             --   plus decided voidness
--   §4  annihilation ⇒ vanishing on the non-void places
--                                             -- iff no zero divisors
--   §4  support-relativity of the annihilator -- from §3 + §4
------------------------------------------------------------------------

module Kha_TheAnnihilatorIgnoresVoidPlacesExactlyWhenTheVoidProductRuleReverses where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Algebra.CommRing.DirectProd using (DirectProd-CommRing)

open import Cubical.Data.Int as Int using (ℤ ; pos ; negsuc)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 1.  The converse of the kha product rule, as a property of a ring
------------------------------------------------------------------------

-- Brahmagupta's rule, `a · kha ≡ kha`, is `0RightAnnihilates` and holds
-- in every ring.  Its converse is a hypothesis:

module _ (Rng : CommRing ℓ) where
  open CommRingStr (snd Rng)

  KhaReverses : Type ℓ
  KhaReverses = (a b : ⟨ Rng ⟩) → a · b ≡ 0r → ¬ (b ≡ 0r) → a ≡ 0r

------------------------------------------------------------------------
-- 2.  The diagonal operator and the coordinate identity
------------------------------------------------------------------------

module Diagonal {ℓ ℓ'} (Rng : CommRing ℓ) (X : Type ℓ') (m : X → ⟨ Rng ⟩) where

  open CommRingStr (snd Rng)
  open RingTheory (CommRing→Ring Rng) using (0LeftAnnihilates ; 0RightAnnihilates)

  A : Type ℓ
  A = ⟨ Rng ⟩

  -- a vector is a quantity standing at each place
  V : Type (ℓ-max ℓ ℓ')
  V = X → A

  -- the diagonal operator: multiply, place by place, by m
  diag : V → V
  diag v x = m x · v x

  -- coefficients, lowest first
  Poly : Type ℓ
  Poly = List A

  -- Horner evaluation at a ring element
  eval : Poly → A → A
  eval []       y = 0r
  eval (c ∷ cs) y = c + y · eval cs y

  -- the SAME coefficients acting on a vector through the operator,
  -- defined without reference to `eval`:
  --     c₀·v + c₁·(diag v) + c₂·(diag (diag v)) + …
  act : Poly → V → V
  act []       v x = 0r
  act (c ∷ cs) v x = c · v x + act cs (diag v) x

  ----------------------------------------------------------------
  -- Layer 1.  No hypothesis at all beyond "commutative ring".
  ----------------------------------------------------------------

  actIsEval : (p : Poly) (v : V) (x : X) → act p v x ≡ eval p (m x) · v x
  actIsEval []       v x = sym (0LeftAnnihilates (v x))
  actIsEval (c ∷ cs) v x =
      cong (c · v x +_) (actIsEval cs (diag v) x ∙ shuffle)
    ∙ sym (·DistL+ c (m x · eval cs (m x)) (v x))
    where
      shuffle : eval cs (m x) · (m x · v x) ≡ (m x · eval cs (m x)) · v x
      shuffle = ·Assoc (eval cs (m x)) (m x) (v x)
              ∙ cong (_· v x) (·Comm (eval cs (m x)) (m x))

  ----------------------------------------------------------------
  -- the vocabulary: void places, annihilation, and knowing the support
  ----------------------------------------------------------------

  -- x is a place where v does NOT stand as kha
  NonVoid : V → X → Type ℓ
  NonVoid v x = ¬ (v x ≡ 0r)

  Ann : Poly → V → Type (ℓ-max ℓ ℓ')
  Ann p v = (x : X) → act p v x ≡ 0r

  VanishesOnNonVoid : Poly → V → Type (ℓ-max ℓ ℓ')
  VanishesOnNonVoid p v = (x : X) → NonVoid v x → eval p (m x) ≡ 0r

  -- Knowing which places are void is DATA, not free.  It is the whole
  -- of what §3 needs beyond the ring axioms, and it is the hypothesis a
  -- machine must discharge before it can skip a place.
  VoidDecided : V → Type (ℓ-max ℓ ℓ')
  VoidDecided v = (x : X) → (v x ≡ 0r) ⊎ (NonVoid v x)

  ----------------------------------------------------------------
  -- Layer 2 (⇐).  Any commutative ring.  This is Brahmagupta's own
  -- direction: at a void place the product is void whatever stands
  -- beside it, so such a place imposes no condition.
  ----------------------------------------------------------------

  vanishes→ann : (p : Poly) (v : V)
               → VoidDecided v → VanishesOnNonVoid p v → Ann p v
  vanishes→ann p v dec h x with dec x
  ... | inl void    = actIsEval p v x
                    ∙ cong (eval p (m x) ·_) void
                    ∙ 0RightAnnihilates (eval p (m x))
  ... | inr nonvoid = actIsEval p v x
                    ∙ cong (_· v x) (h x nonvoid)
                    ∙ 0LeftAnnihilates (v x)

  ----------------------------------------------------------------
  -- Layer 2 (⇒).  This is the direction that needs the converse of
  -- the product rule, and needs NOTHING else — no field, no
  -- interpolation, no invertible differences of the distinct values.
  ----------------------------------------------------------------

  ann→vanishes : KhaReverses Rng
               → (p : Poly) (v : V) → Ann p v → VanishesOnNonVoid p v
  ann→vanishes rev p v h x nonvoid =
    rev (eval p (m x)) (v x) (sym (actIsEval p v x) ∙ h x) nonvoid

  ----------------------------------------------------------------
  -- Support-relativity, which is what the two layers were for: the
  -- annihilator depends on v only through WHICH places are void, not
  -- through the quantities standing at them.
  ----------------------------------------------------------------

  SameVoidPattern : V → V → Type (ℓ-max ℓ ℓ')
  SameVoidPattern v w =
    (x : X) → (NonVoid v x → NonVoid w x) × (NonVoid w x → NonVoid v x)

  supportRelative : KhaReverses Rng
                  → (p : Poly) (v w : V)
                  → SameVoidPattern v w → VoidDecided w
                  → Ann p v → Ann p w
  supportRelative rev p v w same decw h =
    vanishes→ann p w decw
      (λ x nvw → ann→vanishes rev p v h x (same x .snd nvw))

------------------------------------------------------------------------
-- 3.  Sharpness: the hypothesis of §2's (⇒) is not merely sufficient
------------------------------------------------------------------------

-- One place is enough to force it.  So `KhaReverses` is not an
-- artefact of the proof: it is equivalent to the conclusion, and the
-- boundary of the support-relative theorem is exactly the presence of
-- zero divisors — not, as the note has it, the invertibility of the
-- differences of the distinct multiplier values.

module Sharp (Rng : CommRing ℓ) where

  open CommRingStr (snd Rng)
  open RingTheory (CommRing→Ring Rng) using (0RightAnnihilates)

  -- the coefficients of the identity polynomial t
  tPoly : List ⟨ Rng ⟩
  tPoly = 0r ∷ 1r ∷ []

  -- eval of t at y is y, in any commutative ring
  evalT : (a : ⟨ Rng ⟩) (y : ⟨ Rng ⟩) → Diagonal.eval Rng Unit (λ _ → a) tPoly y ≡ y
  evalT a y =
      cong (0r +_) ( cong (y ·_) ( cong (1r +_) (0RightAnnihilates y) ∙ +IdR 1r )
                   ∙ ·IdR y )
    ∙ +IdL y

  -- the one-place instance of §2's (⇒), stated on its own
  OnePlaceDetection : Type ℓ
  OnePlaceDetection =
    (a b : ⟨ Rng ⟩)
    → Diagonal.Ann Rng Unit (λ _ → a) tPoly (λ _ → b)
    → Diagonal.VanishesOnNonVoid Rng Unit (λ _ → a) tPoly (λ _ → b)

  khaReverses→onePlace : KhaReverses Rng → OnePlaceDetection
  khaReverses→onePlace rev a b =
    Diagonal.ann→vanishes Rng Unit (λ _ → a) rev tPoly (λ _ → b)

  onePlace→khaReverses : OnePlaceDetection → KhaReverses Rng
  onePlace→khaReverses det a b ab≡0 b≢0 =
    sym (evalT a a) ∙ det a b annProof tt b≢0
    where
      annProof : Diagonal.Ann Rng Unit (λ _ → a) tPoly (λ _ → b)
      annProof tt =
          Diagonal.actIsEval Rng Unit (λ _ → a) tPoly (λ _ → b) tt
        ∙ cong (_· b) (evalT a a)
        ∙ ab≡0

------------------------------------------------------------------------
-- 4.  Non-vacuity, positive side: ℤ satisfies KhaReverses
------------------------------------------------------------------------

-- ℤ is a commutative ring that is not a field, so the field hypothesis
-- of the note's theorem fails here while §2's (⇒) holds.  This is the
-- gap the module exists to exhibit: the annihilator statement survives
-- where the interpolation basis does not.

ℤ-KhaReverses : KhaReverses ℤCommRing
ℤ-KhaReverses a b ab≡0 b≢0 = Int.isIntegralℤ b a (Int.·Comm b a ∙ ab≡0) b≢0

------------------------------------------------------------------------
-- 5.  Non-vacuity, negative side: ℤ × ℤ does not
------------------------------------------------------------------------

-- Without this, §3's equivalence could be true because no commutative
-- ring ever fails `KhaReverses`.  One does.

ℤ×ℤ : CommRing ℓ-zero
ℤ×ℤ = DirectProd-CommRing ℤCommRing ℤCommRing

1≢0ℤ : ¬ (Int.pos 1 ≡ Int.pos 0)
1≢0ℤ p = snotz (Int.injPos p)

ℤ×ℤ-not-KhaReverses : ¬ (KhaReverses ℤ×ℤ)
ℤ×ℤ-not-KhaReverses rev = 1≢0ℤ (cong fst (rev e₁ e₂ refl e₂≢0))
  where
    e₁ e₂ : ⟨ ℤ×ℤ ⟩
    e₁ = (pos 1 , pos 0)
    e₂ = (pos 0 , pos 1)

    e₂≢0 : ¬ (e₂ ≡ CommRingStr.0r (snd ℤ×ℤ))
    e₂≢0 q = 1≢0ℤ (cong snd q)

-- and therefore, by §3, the support-relative detection itself fails there
ℤ×ℤ-detection-fails : ¬ (Sharp.OnePlaceDetection ℤ×ℤ)
ℤ×ℤ-detection-fails det = ℤ×ℤ-not-KhaReverses (Sharp.onePlace→khaReverses ℤ×ℤ det)

------------------------------------------------------------------------
-- 6.  Non-vacuity of the theorem itself: a worked instance over ℤ
------------------------------------------------------------------------

-- Three places.  The multiplier m takes the value 0 at one place and 2
-- at the other two, so its image on a two-element support is either a
-- one- or a two-element set depending on WHICH two places the support
-- is — the number of non-void places does not determine the annihilator.
--
-- The two DISTINCT multiplier values here are 0 and 2, whose difference
-- is 2, which is not invertible in ℤ.  So this instance sits strictly
-- outside the hypothesis `ACTION_MONOID_CHARACTER_CLOSURE.md` (absent from this repository) names as
-- the boundary ("distinct values need not have unit differences"), and
-- the annihilator statement holds here anyway.

data Three : Type where
  p₀ p₁ p₂ : Three

mThree : Three → ℤ
mThree p₀ = pos 0
mThree p₁ = pos 2
mThree p₂ = pos 2

open Diagonal ℤCommRing Three mThree using () renaming
  ( V to V₃ ; Poly to Poly₃ ; Ann to Ann₃ ; act to act₃
  ; VoidDecided to VoidDecided₃ ; NonVoid to NonVoid₃ )

-- v is non-void at p₀ and p₁;  w is non-void at p₁ and p₂.
vThree wThree : V₃
vThree p₀ = pos 1
vThree p₁ = pos 1
vThree p₂ = pos 0

wThree p₀ = pos 0
wThree p₁ = pos 1
wThree p₂ = pos 1

-- t − 2, as coefficients
tMinus2 : Poly₃
tMinus2 = negsuc 1 ∷ pos 1 ∷ []

-- it annihilates w, whose multiplier values on its support are {2}
annihilates-w : Ann₃ tMinus2 wThree
annihilates-w p₀ = refl
annihilates-w p₁ = refl
annihilates-w p₂ = refl

-- it does not annihilate v, whose multiplier values on its support are {0,2}
does-not-annihilate-v : ¬ (Ann₃ tMinus2 vThree)
does-not-annihilate-v h = Int.negsucNotpos 1 0 (h p₀)

-- Both supports have two places.  That is read off the definitions
-- above — `vThree` is non-void at p₀,p₁ and `wThree` at p₁,p₂₂.—
-- The two vectors have different annihilators.  So the number of non-void
-- places does not determine the annihilator, while (below) the SET of
-- non-void places does.

vThree-decided : VoidDecided₃ vThree
vThree-decided p₀ = inr 1≢0ℤ
vThree-decided p₁ = inr 1≢0ℤ
vThree-decided p₂ = inl refl

wThree-decided : VoidDecided₃ wThree
wThree-decided p₀ = inl refl
wThree-decided p₁ = inr 1≢0ℤ
wThree-decided p₂ = inr 1≢0ℤ

------------------------------------------------------------------------
-- 7.  The theorem exercised over ℤ, which is not a field
------------------------------------------------------------------------

-- `wThree′` stands with entirely different quantities from `wThree` at
-- the places where it is non-void — 5 and −3 in place of 1 and 1 — and
-- its annihilation is derived, not recomputed, from `annihilates-w`.
-- Nothing here has an interpolation basis available: the differences of
-- the distinct multiplier values are 1 and −1 in ℤ, which happen to be
-- units, but the coefficients 5 and −3 are not invertible and the proof
-- never divides.

wThree′ : V₃
wThree′ p₀ = pos 0
wThree′ p₁ = pos 5
wThree′ p₂ = negsuc 2

same-pattern : Diagonal.SameVoidPattern ℤCommRing Three mThree wThree wThree′
same-pattern p₀ = (λ nv → Empty.rec (nv refl)) , (λ nv → Empty.rec (nv refl))
same-pattern p₁ = (λ _ → λ q → snotz (Int.injPos q))
                , (λ _ → 1≢0ℤ)
same-pattern p₂ = (λ _ → λ q → Int.negsucNotpos 2 0 q)
                , (λ _ → 1≢0ℤ)

annihilates-w′ : Ann₃ tMinus2 wThree′
annihilates-w′ =
  Diagonal.supportRelative ℤCommRing Three mThree
    ℤ-KhaReverses tMinus2 wThree wThree′
    same-pattern wThree′-decided annihilates-w
  where
    wThree′-decided : Diagonal.VoidDecided ℤCommRing Three mThree wThree′
    wThree′-decided p₀ = inl refl
    wThree′-decided p₁ = inr (λ q → snotz (Int.injPos q))
    wThree′-decided p₂ = inr (λ q → Int.negsucNotpos 2 0 q)

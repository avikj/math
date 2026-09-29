{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Pythagoras_RatioIsTheInvariantAndLengthIsThePresentation
--
-- The Pythagorean root of the sufficiency experiment (India + Pythagorean
-- number-as-structure + univalence), built rather than named.
--
-- THE DOCTRINE, stated so it can be checked: on the monochord a musical
-- interval is a RATIO of string lengths and not a pair of lengths.  Halve
-- the string and you get the octave; halve a string twice as long and you
-- get the same octave.  "Things are numbers" is this: the content is the
-- ratio, and the lengths that carry it are presentation.
--
-- That is the same shape as `Laghava` (cost lives on the
-- presentation, and no function of the denotation computes it) and of
-- `TransportPrice`, arrived at from the other root.  Section 3 below is
-- the monochord's `laghava-is-not-semantic`: no scale-respecting function
-- of a sounding returns a length.  Sections 4-5 are what survives the
-- quotient -- the interval itself, and its composition law.
--
-- SOURCES, and what is claimed of them.  The monochord division and the
-- whole-number ratios of octave, fifth and fourth are the Pythagorean
-- tradition's (Philolaus B6; the ratios as transmitted through Nicomachus
-- and Boethius; the akousmatic/mathematikoi transmission is oral and the
-- attributions to Pythagoras himself are not securely datable).  The same
-- identification of pitch with ratio rather than with length belongs to
-- the Indian naada tradition; Baudhayana's Sulbasutra (~800 BCE) is
-- already in this corpus for the diagonal.  NOTHING below is claimed to
-- be in those texts: the theorems are this corpus's, named for the act
-- the traditions performed.
--
-- No rational-number type is imported and none is needed; the point is
-- precisely that the quotient is the object, so it is exhibited as a
-- relation on presentations and shown to be one.
------------------------------------------------------------------------

module Pythagoras_RatioIsTheInvariantAndLengthIsThePresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _·_ ; injSuc ; snotz)
open import Cubical.Data.Nat.Properties using (·-comm ; ·-assoc)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  A sounding: two string lengths.  A pair, not a number.
------------------------------------------------------------------------

Sounding : Type₀
Sounding = ℕ × ℕ

-- Two soundings name one interval when the strings divide alike.  This
-- is the monochord's own test, cross-multiplication.
SameInterval : Sounding → Sounding → Type₀
SameInterval (a , b) (c , d) = a · d ≡ c · b

octave : Sounding
octave = 1 , 2

octave-long : Sounding
octave-long = 2 , 4

------------------------------------------------------------------------
-- 2.  Scale is not audible: the same interval at every magnification.
--     The doctrine's positive half.
------------------------------------------------------------------------

scale-invariant : (k a b : ℕ) → SameInterval (a , b) (k · a , k · b)
scale-invariant k a b = ·-assoc a k b ∙ cong (_· b) (·-comm a k)

octave-at-two-scales : SameInterval octave octave-long
octave-at-two-scales = scale-invariant 2 1 2

------------------------------------------------------------------------
-- 3.  Length is not audible: the doctrine's negative half, and it is the
--     monochord's `laghava-is-not-semantic`.
--
--     No function that respects the interval can report a string length.
--     The invariant discards exactly the presentation.
------------------------------------------------------------------------

Respects : (Sounding → ℕ) → Type₀
Respects f = (i j : Sounding) → SameInterval i j → f i ≡ f j

1≢2 : ¬ (1 ≡ 2)
1≢2 p = snotz (sym (injSuc p))

length-is-not-an-invariant-of-the-interval :
  ¬ (Σ[ f ∈ (Sounding → ℕ) ] (Respects f × ((i : Sounding) → f i ≡ fst i)))
length-is-not-an-invariant-of-the-interval (f , resp , reads) =
  1≢2 ( sym (reads octave)
      ∙ resp octave octave-long octave-at-two-scales
      ∙ reads octave-long )

------------------------------------------------------------------------
-- 4.  What survives.  The relation is reflexive and symmetric, so "the
--     interval" is a genuine object and not a way of speaking.
------------------------------------------------------------------------

SameInterval-refl : (i : Sounding) → SameInterval i i
SameInterval-refl (a , b) = refl

SameInterval-sym : (i j : Sounding) → SameInterval i j → SameInterval j i
SameInterval-sym (a , b) (c , d) p = sym p

------------------------------------------------------------------------
-- 5.  Intervals compose, and composition is blind to scale.  Stacking a
--     fifth on a fourth multiplies ratios; the lengths that carried them
--     never enter.  This is the structure the doctrine asserts -- the
--     numbers are what compose.
------------------------------------------------------------------------

stack : Sounding → Sounding → Sounding
stack (a , b) (c , d) = a · c , b · d

private
  shuffle : (a c b' d' : ℕ) → (a · c) · (b' · d') ≡ (a · b') · (c · d')
  shuffle a c b' d' =
      ·-assoc (a · c) b' d'
    ∙ cong (_· d') ( sym (·-assoc a c b')
                   ∙ cong (a ·_) (·-comm c b')
                   ∙ ·-assoc a b' c )
    ∙ sym (·-assoc (a · b') c d')

stack-respects-interval :
  (i i' j j' : Sounding) →
  SameInterval i i' → SameInterval j j' →
  SameInterval (stack i j) (stack i' j')
stack-respects-interval (a , b) (a' , b') (c , d) (c' , d') p q =
    shuffle a c b' d'
  ∙ cong₂ _·_ p q
  ∙ sym (shuffle a' c' b d)

------------------------------------------------------------------------
-- 6.  What this pins down, for the sufficiency experiment.
--
-- The Pythagorean root contributes an exact statement and not a mood.
-- Number-as-structure means: the carrier is a quotient, the invariant is
-- the ratio, and the presentation -- the actual lengths of gut and wood
-- -- is discarded by the invariant and is nonetheless what you must hold
-- to sound the note at all.  Sections 2 and 3 are the two halves and
-- neither is optional.
--
-- The India root reaches the same place from grammar and cost: `Laghava`
-- proves no function of the meaning computes the size of the utterance.
-- The univalence root is why the quotient may be treated as the object.
-- Three roots, one shape, and the shape is: an invariant is defined by
-- what it refuses to see.
------------------------------------------------------------------------

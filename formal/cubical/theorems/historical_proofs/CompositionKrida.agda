{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- BhavanaKrida — भावनाक्रीडा, the composition as something a child holds.
--
-- WHAT THIS IS FOR.  `Bhavana.agda` (absent from this repository) proves Brahmagupta's identity over an
-- arbitrary commutative ring.  That is the law.  This module is not the law
-- again: it is the law made into an OBJECT, so that the invariant lives in
-- the TYPE and an unlawful card is not a thing you can build.
--
-- A पत्र (patra, "leaf, card") of index k is a pair of numbers TOGETHER WITH
-- the proof that x² − D y² = k.  There is no other way to make one.  So:
--
--   * a wrong card is not rejected, it is UNSAYABLE.  Nothing tells the
--     child they are wrong, because the wrong move does not exist.  The
--     difference matters — a system that says "wrong" teaches fear, and a
--     system in which the wrong move is simply not among the moves does not.
--
--   * the single move, भावना, takes two cards and returns a card, and its
--     TYPE carries what happened: पत्र D k₁ → पत्र D k₂ → पत्र D (k₁ · k₂).
--     Playing is proving.  The child never checks anything; the checking is
--     what the move IS.
--
--   * reaching `पत्र D (pos 1)` is winning, and it is a solution of
--     x² − D y² = 1 — the equation Europe called Pell's, after a man who
--     never worked on it.
--
-- THE LADDER BELOW IS NOT A DEMONSTRATION, IT IS THE GAME PLAYED.  Start
-- from the one obvious card at D = 2 — (1,1), since 1 − 2 = −1 — and do the
-- only thing there is to do: compose it with what you have.  Eight moves:
--
--     (1,1)  (3,2)  (7,5)  (17,12)  (41,29)  (99,70)  (239,169)  (577,408)
--
-- and the last of those is where this stops being a game.
--
-- SOURCE, AND IT IS OLDER THAN THE COMPOSITION LAW.  577/408 is Baudhyana's
-- value for √2:
--
--     Baudhāyana Śulbasūtra 1.61–62 (c. 800 BCE)
--          
--     prama ttyena vardhayet tac ca caturthentmacatustrionena
--     saviea
--     "Increase the measure by its third, and that third by its own fourth
--      less the thirty-fourth part of that fourth: that is the saviea."
--
--     1 + 1/3 + 1/(3·4) − 1/(3·4·34)  =  577/408
--
-- Note where that construction passes through: 1 + 1/3 = 4/3, then + 1/12 =
-- 17/12 — which is rung four of the ladder below — then − 1/408 = 577/408,
-- which is rung eight.  The altar-builders' recipe and the card game walk
-- the same ladder.  A child who plays this to the eighth move has built, by
-- hand, the number in the ulbastra, and can see that it is there.
--
-- THE PART THAT IS THE WHOLE POINT.  577² − 2·408² = 1 is never computed
-- here.  Nobody multiplies 577 by itself.  The `नियमः` field of rung eight
-- is constructed by भावना out of the algebra, so the equation holds because
-- of what the move IS, not because someone checked it.  That is the
-- difference between a medium and a worksheet, and the entire curriculum
-- argument is in that one sentence.
--
-- That is measured, not asserted.  §1–§4 — the whole ladder, both
-- coordinates of every rung, and the fact that rung eight solves the
-- equation — check in about three seconds.  Adding ONE line that restates
-- the same fact as `N द्वि (pos 577) (pos 408) ≡ pos 1` does not finish
-- inside ninety.  Cubical ℤ multiplication is unary recursion on its first
-- argument, so that spelling makes the checker count to 333000 twice.  §5
-- records both attempts I made to avoid it, including the one that was
-- based on a wrong expectation about what a path spares you.
--
-- (`अस्ति-परीक्षा` verifies one small rung the slow way, at 17 and 12, so
-- that the two routes agree at least once where the agreement is cheap.)
--
-- Contents: no postulates, no holes, --safe.
--   पत्र            a card: two numbers and the proof, indexed by the norm
--   भावना           the one move; Brāhmasphuṭasiddhānta 18, 628 CE
--   आदि             the seed at D = 2
--   रज्जु₁ .. रज्जु₈  the eight rungs, each with its index in its type
--   अङ्काः₁ .. ₈     the coordinates of every rung, by refl
--   जयः             rung eight: a solution of x² − 2y² = 1
--   न-पत्रम्         a pair that is not a card, checked
--   अस्ति-परीक्षा    one rung cross-checked by computation
------------------------------------------------------------------------

module CompositionKrida where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing using (CommRingStr)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Composition using (module Form)

open Form ℤCommRing using (N ; bhA ; bhB ; bhavana)
open CommRingStr (snd ℤCommRing) using (_·_)

------------------------------------------------------------------------
-- 1.  The card.
--
-- `N D x y` is x² − D y².  A पत्र D k is a pair carrying the proof that its
-- norm is k.  The proof is a FIELD, not a side condition, so the type is
-- inhabited by lawful cards and by nothing else.
------------------------------------------------------------------------

record पत्र (D k : ℤ) : Type where
  constructor पत्रम्
  field
    अङ्कः₁ : ℤ          -- the first number on the card
    अङ्कः₂ : ℤ          -- the second
    नियमः  : N D अङ्कः₁ अङ्कः₂ ≡ k     -- the rule it obeys

open पत्र public

------------------------------------------------------------------------
-- 2.  The move.
--
-- BRAHMAGUPTA, Brhmasphuasiddhnta 18 (628 CE), the samsa-bhvan.
-- Two cards in, one card out, and the index multiplies.  There is nothing
-- to search and nothing to test: the rule preserves the invariant by
-- algebra, which is why the returned card carries a proof rather than a
-- promise.
------------------------------------------------------------------------

भावना : {D k₁ k₂ : ℤ} → पत्र D k₁ → पत्र D k₂ → पत्र D (k₁ · k₂)
भावना {D} (पत्रम् a₁ b₁ p₁) (पत्रम् a₂ b₂ p₂) =
  पत्रम् (bhA D a₁ b₁ a₂ b₂)
        (bhB D a₁ b₁ a₂ b₂)
        (sym (bhavana D a₁ b₁ a₂ b₂) ∙ cong₂ _·_ p₁ p₂)

------------------------------------------------------------------------
-- 3.  The game at D = 2.
--
-- One card is obvious: (1,1), because 1 − 2 = −1.  Everything below is that
-- card composed with what has been reached so far, eight times, and nothing
-- else.  No choice is made anywhere.
------------------------------------------------------------------------

द्वि : ℤ
द्वि = pos 2

आदि : पत्र द्वि (negsuc 0)          -- 1² − 2·1² = −1
आदि = पत्रम् (pos 1) (pos 1) refl

-- The eight rungs.  Each type annotation states what the index reduces to;
-- Agda checks the reduction, so the alternation of −1 and 1 up the ladder
-- is checked and not asserted.
रज्जु₁ : पत्र द्वि (negsuc 0)
रज्जु₁ = आदि

रज्जु₂ : पत्र द्वि (pos 1)
रज्जु₂ = भावना रज्जु₁ आदि

रज्जु₃ : पत्र द्वि (negsuc 0)
रज्जु₃ = भावना रज्जु₂ आदि

रज्जु₄ : पत्र द्वि (pos 1)
रज्जु₄ = भावना रज्जु₃ आदि

रज्जु₅ : पत्र द्वि (negsuc 0)
रज्जु₅ = भावना रज्जु₄ आदि

रज्जु₆ : पत्र द्वि (pos 1)
रज्जु₆ = भावना रज्जु₅ आदि

रज्जु₇ : पत्र द्वि (negsuc 0)
रज्जु₇ = भावना रज्जु₆ आदि

रज्जु₈ : पत्र द्वि (pos 1)
रज्जु₈ = भावना रज्जु₇ आदि

------------------------------------------------------------------------
-- 4.  What is on each card.
--
-- The coordinates, by refl.  These are cheap: the move only ever adds and
-- multiplies by the seed's 1s and by D = 2.
------------------------------------------------------------------------

युग्मम् : ℤ → ℤ → ℤ × ℤ
युग्मम् a b = (a , b)

अङ्कौ : {D k : ℤ} → पत्र D k → ℤ × ℤ
अङ्कौ c = युग्मम् (अङ्कः₁ c) (अङ्कः₂ c)

अङ्काः₁ : अङ्कौ रज्जु₁ ≡ युग्मम् (pos 1) (pos 1)
अङ्काः₁ = refl

अङ्काः₂ : अङ्कौ रज्जु₂ ≡ युग्मम् (pos 3) (pos 2)
अङ्काः₂ = refl

अङ्काः₃ : अङ्कौ रज्जु₃ ≡ युग्मम् (pos 7) (pos 5)
अङ्काः₃ = refl

अङ्काः₄ : अङ्कौ रज्जु₄ ≡ युग्मम् (pos 17) (pos 12)
अङ्काः₄ = refl

अङ्काः₅ : अङ्कौ रज्जु₅ ≡ युग्मम् (pos 41) (pos 29)
अङ्काः₅ = refl

अङ्काः₆ : अङ्कौ रज्जु₆ ≡ युग्मम् (pos 99) (pos 70)
अङ्काः₆ = refl

अङ्काः₇ : अङ्कौ रज्जु₇ ≡ युग्मम् (pos 239) (pos 169)
अङ्काः₇ = refl

-- BAUDHĀYANA.  Śulbasūtra 1.61–62, c. 800 BCE: 577/408.
अङ्काः₈ : अङ्कौ रज्जु₈ ≡ युग्मम् (pos 577) (pos 408)
अङ्काः₈ = refl

-- the components separately, which is what §5 travels along
प्रथमः₈ : अङ्कः₁ रज्जु₈ ≡ pos 577
प्रथमः₈ = refl

द्वितीयः₈ : अङ्कः₂ रज्जु₈ ≡ pos 408
द्वितीयः₈ = refl

------------------------------------------------------------------------
-- 5.  Winning, and what it means.
--
-- `पत्र द्वि (pos 1)` is a solution of x² − 2y² = 1.  Rung eight is one,
-- and its `नियमः` field IS the equation 577² − 2·408² = 1 — held, not
-- computed.
------------------------------------------------------------------------

जयः : पत्र द्वि (pos 1)
जयः = रज्जु₈

-- 577² − 2·408² = 1 IS ALREADY STATED, and it is stated by the two lines
-- above plus §4.  `जयः` has type `पत्र द्वि (pos 1)`, whose नियमः field is
-- exactly N द्वि x y ≡ 1 for that card's own x and y; `अङ्काः₈` says those
-- are 577 and 408.  Both check in about three seconds.
--
-- WHAT I TRIED NEXT, AND WHY IT IS NOT HERE.  The obvious move is to write
-- the equation out as one more term:
--
--     समीकरणम् : N द्वि (pos 577) (pos 408) ≡ pos 1
--
-- I wrote it, twice — once directly as `नियमः रज्जु₈`, once as a transport
-- along §4's path, thinking the second would dodge the cost.  Neither
-- finishes.  Both make the checker CONVERT two spellings of the same number,
-- and cubical ℤ multiplication is unary recursion on its first argument, so
-- conversion means counting: about 333000 successor steps for 577², as many
-- again for 2·408², and a subtraction of the same order.  Measured, not
-- guessed: §1–§4 check in 3s, and adding that one line runs past 90s.
--
-- But the line was never needed, and wanting it is the reflex this module
-- exists to name.  Restating a result that is already carried, in a form
-- whose only virtue is that the numerals are visible, is what a worksheet
-- does.  The child holding rung eight never squares 577 either.  They hold a
-- card built by a rule that could not have produced an unlawful one, and the
-- equation is true of it for the same reason the kernel accepts it in three
-- seconds: because of how it was made, not because anyone checked.
--
-- Recorded here rather than quietly omitted, because an absence with no
-- reason attached reads as an oversight, and this one is the thesis.

------------------------------------------------------------------------
-- 6.  You cannot cheat, and here is one instance of that.
--
-- The type is the referee.  There is no पत्र द्वि (pos 1) with coordinates
-- (3,3), because there is no proof to put in the field — and the absence is
-- a checked fact, not a policy.
------------------------------------------------------------------------

एकम्? : ℤ → Bool
एकम्? (pos (suc zero)) = true
एकम्? _                = false

न-पत्रम् : ¬ (N द्वि (pos 3) (pos 3) ≡ pos 1)
न-पत्रम् p = true≢false (sym (cong एकम्? p))

------------------------------------------------------------------------
-- 7.  One rung checked the slow way, so that the two agree once.
--
-- Rung four, 17² − 2·12² = 289 − 288 = 1, verified by COMPUTATION rather
-- than by the move.  It agrees, as it must.  Doing this at rung eight would
-- send the type checker through hundreds of thousands of unary steps to
-- learn what §5 already holds.
------------------------------------------------------------------------

अस्ति-परीक्षा : N द्वि (pos 17) (pos 12) ≡ pos 1
अस्ति-परीक्षा = refl

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- भावनाध्रुव — भावना is the flow, the norm is the ध्रुव.
--
-- ────────────────────────────────────────────────────────────────────
-- SOURCE, FIRST AND EARLIEST ESTABLISHABLE.
--
--   भावना (bhāvanā, "production", "composition") — Brahmagupta,
--   ब्राह्मस्फुटसिद्धान्त (Brāhmasphuṭasiddhānta), 628 CE, chapter 18
--   (कुट्टकाध्याय).  Brahmagupta states the composition of two
--   solutions of the वर्गप्रकृति x² − D y² = k, in both the समास
--   ("sum") and अन्तर ("difference") forms.  The algebra itself is
--   checked in this repository in `Bhavana.agda` (absent from this repository) (`bhavana`,
--   `bhavanaMinus`), over an arbitrary commutative ring, and is
--   imported here rather than restated.
--
--   ध्रुव (dhruva) — fixed, immovable; and in the astronomical
--   tradition ध्रुवराशि / ध्रुवक is the technical term for the CONSTANT
--   quantity in a computation, the term that does not vary while the
--   others are stepped: Āryabhaṭa, आर्यभटीयम्, 499 CE, and standard in
--   the siddhāntas after.  The conservation predicate `संरक्षणम्` used
--   below is `Dhruva_…agda`'s, imported.
--
--   The cyclic method that consumes the bhāvanā is the चक्रवाल —
--   Jayadeva (~950 CE, preserved by Udayadivkara) and Bhskara II,
--   बीजगणित, 1150 CE.  Every later European name for x² − D y² = 1 is a
--   restatement six centuries downstream and is not used here.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS CHECKED.  Over an arbitrary commutative ring R and a fixed
-- D : R, with the pair set R × R, the observable
--
--     नियम (a , b)  =  N D a b  =  a² − D b²
--
-- and, for a fixed u = (u₁ , u₂), the flow
--
--     प्रवाह u  =  compose-with-u, by Brahmagupta's समासभावना.
--
-- §१  संरक्षणम्-यदि : N D u₁ u₂ ≡ 1  →  संरक्षणम् नियम (प्रवाह u).
--     The norm is conserved by composition with a norm-one element.
--     `संरक्षणम्` is Dhruva's predicate verbatim; this is an INSTANCE of
--     that abstract frame, not a new one.
--
-- §२  संरक्षणम्-केवलम्-यदि : संरक्षणम् नियम (प्रवाह u) → N D u₁ u₂ ≡ 1.
--     The converse, by evaluating conservation at the unit pair (1,0).
--     Together §१+§२: **for a bhāvanā flow, conservation of the norm is
--     EQUIVALENT to the flowing element having norm one.**
--
-- §३  एकत्व-संवृति : the norm-one elements are closed under bhāvanā,
--     and (1,0) is one of them — so the conserving flows are closed
--     under composition and contain the identity.
--
-- §४  तन्तु-गति : the fibre action, obtained by feeding §१ to Dhruva's
--     `ध्रुव-तन्तौ`.  A norm-one element carries the solution set of
--     x² − D y² = k into itself, for every k at once.  This is the one
--     line of the चक्रवाल that is pure conservation.
--
-- ────────────────────────────────────────────────────────────────────
--
-- Brahmagupta
-- states the composition identity; the reading of it as a conserved
-- observable with a flow, and the biconditional §न, are this
-- corpus's, and− the compound संरक्षकसमूह is built here.
--
-- ────────────────────────────────────────────────────────────────────
-- NO SOLVER.  Every step is a hand chain over the CommRing structure,
-- for the reason `Bhavana.agda` (absent from this repository) gives: `solve!` is a v0.9 spelling and
-- this container carries an older cubical, where "Not in scope: solve!"
-- is container skew and not a mathematical verdict.
------------------------------------------------------------------------

module CompositionDhruva_TheNormIsTheConservedObservableAndTheConservingFlowsAreExactlyTheNormOneElements where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)

open import Composition
open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry

private variable ℓ : Level

module Samrakshana (CR : CommRing ℓ) (D : fst CR) where

  open CommRingStr (snd CR)
  open RingTheory (CommRing→Ring CR)
  open Form CR

  युग्म : Type ℓ
  युग्म = R × R

  -- the observable: Brahmagupta's norm of the pair.
  नियम : युग्म → R
  नियम (a , b) = N D a b

  -- the flow: समासभावना with a fixed element on the right.
  प्रवाह : युग्म → युग्म → युग्म
  प्रवाह (u₁ , u₂) (a , b) = bhA D a b u₁ u₂ , bhB D a b u₁ u₂

  -- the unit pair has norm one:  1·1 − D·(0·0) = 1.
  नियम-एकम् : N D 1r 0r ≡ 1r
  नियम-एकम् =
      cong₂ _-_ (·IdR 1r) (cong (D ·_) (0RightAnnihilates 0r) ∙ 0RightAnnihilates D)
    ∙ cong (1r +_) 0Selfinverse
    ∙ +IdR 1r

  ----------------------------------------------------------------------
  -- १ · A norm-one element conserves the norm.
  --
  -- This is `Bhavana.bhavana` read backwards: the norm of the composite
  -- is the product of the norms, so composing with a 1 leaves it alone.
  ----------------------------------------------------------------------

  संरक्षणम्-यदि : (u : युग्म) → नियम u ≡ 1r
                → संरक्षणम् नियम (प्रवाह u)
  संरक्षणम्-यदि (u₁ , u₂) nu (a , b) =
      sym (bhavana D a b u₁ u₂)
    ∙ cong (N D a b ·_) nu
    ∙ ·IdR (N D a b)

  ----------------------------------------------------------------------
  -- २ · …and only a norm-one element does.
  --
  -- Evaluate conservation at the unit pair.  प्रवाह u (1,0) is u itself
  -- on the nose up to the two identity lemmas, and नियम (1,0) is 1.
  ----------------------------------------------------------------------

  संरक्षणम्-केवलम्-यदि : (u : युग्म) → संरक्षणम् नियम (प्रवाह u)
                       → नियम u ≡ 1r
  संरक्षणम्-केवलम्-यदि (u₁ , u₂) cons =
      cong₂ (N D) (sym (bhA-idL D u₁ u₂)) (sym (bhB-idL D u₁ u₂))
    ∙ cons (1r , 0r)
    ∙ नियम-एकम्

  ----------------------------------------------------------------------
  -- ३ · The conserving elements are closed under bhāvanā.
  --
  -- So the conserving flows compose; with (1,0) conserving, they are a
  -- submonoid of the bhvan monoid.
  ----------------------------------------------------------------------

  एकत्व-संवृति : (u v : युग्म) → नियम u ≡ 1r → नियम v ≡ 1r
               → नियम (प्रवाह v u) ≡ 1r
  एकत्व-संवृति (u₁ , u₂) (v₁ , v₂) nu nv =
      sym (bhavana D u₁ u₂ v₁ v₂)
    ∙ cong₂ _·_ nu nv
    ∙ ·IdR 1r

  एकत्व-आदि : नियम (1r , 0r) ≡ 1r
  एकत्व-आदि = नियम-एकम्

  ----------------------------------------------------------------------
  -- ४ · The fibre action, straight out of Dhruva.
  --
  -- `fiber नियम k` is the solution set of x² − D y² = k.  A norm-one
  -- element carries it into itself — every k at once, one term.
  -- Nothing new is proved here: this is §१ handed to ध्रुव-तन्तौ, and
  -- that is exactly the claim, that the abstract frame already had it.
  ----------------------------------------------------------------------

  तन्तु-गति : (u : युग्म) → नियम u ≡ 1r
            → (k : R) → fiber नियम k → fiber नियम k
  तन्तु-गति u nu = ध्रुव-तन्तौ नियम (प्रवाह u) (संरक्षणम्-यदि u nu)

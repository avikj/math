{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- बहु-प्रत्यानयनम् — प्रत्यानयनस्य प्रतिबन्धो द्वौ भिन्नौ मूलौ, न तु द्वौ तन्तु-बिन्दू ।
--
-- (the obstruction to undoing a map is two distinct SOURCES over one
--  target — not two points of the fibre; and the circle is not an
--  instance of it.)
--
--   §२  the law   : two points of one fibre WITH DISTINCT SOURCES kill
--                   every retraction.  Four lines, no h-level, no
--                   decidability, no finiteness, arbitrary A and B.
--                   Positive form: a retraction makes every fibre
--                   source-thin.
--   §३  instance  : the discrete log has NO LEFT INVERSE.  0 and 3 both
--                   land on ε, so no `r : C₃ → ℕ` undoes `powg`.  This is
--                   the corpus's second irreversibility theorem and its
--                   first outside homotopy.
--   §४  instance  : `सर्वैकम् : Bool → Unit`, the standing archetype.
--   §५  THE BOUNDARY, and it is the point of the file: `Tantujala`'s
--       बहु — two distinct points of a fibre — IS NOT ENOUGH.  Exhibited:
--       `एकवृत्तम् : Unit → S¹`, `tt ↦ base`, HAS a retraction, and its
--       fibre over `base` is `ΩS¹ ≃ ℤ`, so बहु holds of it.  Its two
--       fibre points differ only in their WITNESS; their sources are
--       equal.  So बहु does not obstruct undoing, and §२'s hypothesis is
--       strictly stronger than .
--   §६  therefore `noDescentS¹` is NOT an instance of §२ and cannot be
--       made one: S¹ is connected, so it has no two distinct points to
--       feed the law.  Its obstruction is π₁ — one level up.  **The
--       corpus has two kinds of irreversibility and neither reduces to
--       the other**, and §५ is the witness that the reduction fails.
--
-- ────────────────────────────────────────────────────────────────────
-- RELATION TO WHAT IS ALREADY HERE.
--
--   `Tantujala_…`            बहु as one of three fibre verdicts.  §५
--                            sharpens it: बहु is not the obstruction to
--                            undoing.
--   `Sesa_…` §5              prices `सर्वैकम्`'s loss at one bit and proves
--                            `¬ isEquiv`.  §४ here is the RETRACTION
--                            statement, which is different and weaker
--                            than `¬ isEquiv` in general.
--   `GhataTantu_…`           exhibits the two exponents.  §३ consumes
--                            them.
--   `Nirdharana_TheReturnLocus…`  the SECTION side: with `q ∘ s ≡ id` the
--                            return locus is `im s`.  This file is the
--                            other side: when no RETRACTION exists at
--                            all.  The two are not the same direction and
--                            neither implies the other.
--   `Arpitanarpita_….न-प्रत्यानयनम्` and `AHIMSA_SUTRA`'s
--   `नास्ति-प्रत्यानयनम्`      are two hand-proved instances of the same
--                            shape.  §न is the law they are instances of.
------------------------------------------------------------------------

module Bahupratyanayana_TheObstructionToUndoingIsTwoDistinctSourcesNotTwoFibrePointsAndTheCircleIsNotAnInstance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (znots)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.S1 using (S¹ ; base ; loop ; winding)

open import GhataFiber_TheDiscreteLogIsTheFiberOfPingalasPowerAndShorsPeriodQueryIsWhatReadsIt
  using (powg ; εC ; शून्यः ; त्रयः)
open import BijamulaKrida_AConcreteKeypairRunsInACyclicGroupWhereTheModThatExhaustsTheHeapIsNotNeeded
  using (C₃)

private variable ℓ ℓ' : Level

------------------------------------------------------------------------
-- १ · प्रत्यानयनम् — the undo.  A left inverse: run f, then r, and be
--     back where you started.  (Not a section — that is the other
--     direction, and `Nirdharana_TheReturnLocus…` treats it.)
------------------------------------------------------------------------

प्रत्यानयनम् : {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
प्रत्यानयनम् {A = A} f = Σ[ r ∈ (_ → A) ] ((a : A) → r (f a) ≡ a)

------------------------------------------------------------------------
-- २ · THE LAW.  Two distinct SOURCES over one target kill every undo.
--
-- No hypothesis on A or B: no h-level, no decidability, no finiteness.
-- The proof is the retraction used twice with the two witnesses glued
-- between.
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where

  -- positive form: an undo makes every fibre THIN IN THE SOURCE.
  प्रत्यानयनम्-तनुः : प्रत्यानयनम् f
                   → (b : B) (x y : fiber f b) → fst x ≡ fst y
  प्रत्यानयनम्-तनुः (r , ret) b (a₁ , p₁) (a₂ , p₂) =
    sym (ret a₁) ∙ cong r (p₁ ∙ sym p₂) ∙ ret a₂

  -- the generator, as the contrapositive: distinct sources, no undo.
  बहु-मूलम्-न-प्रत्यानयनम् : (b : B) (x y : fiber f b)
                          → ¬ (fst x ≡ fst y) → ¬ (प्रत्यानयनम् f)
  बहु-मूलम्-न-प्रत्यानयनम् b x y ne ret =
    ne (प्रत्यानयनम्-तनुः ret b x y)

------------------------------------------------------------------------
-- ३ · THE DISCRETE LOG HAS NO LEFT INVERSE.
--
-- `GhataTantu` exhibits 0 and 3 over ε.  Their sources are 0 and 3, and
-- `znots` separates them.  So no `r : C₃ → ℕ` undoes `powg` — checked,
-- and it is not a hardness statement: it is that the undo DOES NOT
-- EXIST, for the same reason `Bool → Unit`'s does not.
------------------------------------------------------------------------

घातः-न-प्रत्यानयनीयः : ¬ (प्रत्यानयनम् powg)
घातः-न-प्रत्यानयनीयः =
  बहु-मूलम्-न-प्रत्यानयनम् powg εC शून्यः त्रयः znots

------------------------------------------------------------------------
-- ४ · The standing archetype, for free from the same law.
------------------------------------------------------------------------

सर्वैकम् : Bool → Unit
सर्वैकम् _ = tt

सर्वैकम्-न-प्रत्यानयनीयम् : ¬ (प्रत्यानयनम् सर्वैकम्)
सर्वैकम्-न-प्रत्यानयनीयम् =
  बहु-मूलम्-न-प्रत्यानयनम् सर्वैकम् tt (false , refl) (true , refl) false≢true

------------------------------------------------------------------------
-- ५ · THE BOUNDARY.  बहु IS NOT THE OBSTRUCTION.
--
-- `एकवृत्तम् : Unit → S¹` sending tt to base HAS an undo (`r _ = tt`,
-- and `r (f tt) ≡ tt` is refl).  Its fibre over `base` is `Σ[Unit] ΩS¹`,
-- which has two distinct points — `(tt , refl)` and `(tt , loop)`,
-- distinct because `winding` separates them in ℤ.  So `Tantujala`'s बहु
-- holds of a map that is perfectly undoable.
--
-- The two fibre points differ only in their WITNESS; their sources are
-- both `tt`.  §२'s hypothesis is therefore STRICTLY STRONGER than बहु,
-- and the strengthening is exactly the difference between a path in the
-- base and a point of the source.
------------------------------------------------------------------------

एकवृत्तम् : Unit → S¹
एकवृत्तम् _ = base

एकवृत्तम्-प्रत्यानयनीयम् : प्रत्यानयनम् एकवृत्तम्
एकवृत्तम्-प्रत्यानयनीयम् = (λ _ → tt) , (λ _ → refl)

private
  -- a predicate separating pos 0 from pos 1, so the two loops differ
  शून्यम्? : ℤ → Type
  शून्यम्? (pos zero) = Unit
  शून्यम्? _          = ⊥

वृत्त-वाम वृत्त-दक्षिण : fiber एकवृत्तम् base
वृत्त-वाम    = tt , refl
वृत्त-दक्षिण  = tt , loop

वृत्त-बहु : ¬ (वृत्त-वाम ≡ वृत्त-दक्षिण)
वृत्त-बहु p = subst शून्यम्? (cong (λ z → winding (snd z)) p) tt

-- …and yet the sources agree, which is why the undo survives.
वृत्त-मूल-अभेदः : fst वृत्त-वाम ≡ fst वृत्त-दक्षिण
वृत्त-मूल-अभेदः = refl

------------------------------------------------------------------------
-- ६ · शेषः — why `noDescentS¹` is a different theorem.
--
-- §२ needs two points of A that are provably distinct.  S¹ is connected,
-- so it has none: `base ≡ base` is inhabited by `refl`, and the law
-- cannot fire anywhere on it.  `SetTruncationDescentBoundary.noDescentS¹`
-- obstructs the truncation's retraction all the same, and the reason is
-- π₁ — the loop, not the points.  §५ is the witness that the reduction
-- genuinely fails rather than merely being unfound: there the loop-level
-- distinctness is present, the point-level distinctness is absent, and
-- the retraction EXISTS.  So the corpus's two no-return theorems live at
-- two levels and neither implies the other.
------------------------------------------------------------------------

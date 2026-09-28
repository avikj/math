{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- त्रयो निर्णयाः — trayo nirṇayāḥ, "three verdicts."  संरक्षण-सूत्रम् ६:
-- «त्रयो निर्णयाः, न द्वौ ।» — three verdicts, never two.  (Owner's root
-- text, README §संरक्षण-सूत्राणि, 2026-08-22; the grammar of the sūtra is
-- the author's own.  The epistemic frame is the Jaina saptabhaṅgī —
-- asti / nāsti / avaktavya — Umāsvāti, *Tattvārthasūtra* 5.32; the third
-- position is what a standpoint yields when it cannot yet decide.)
--
-- WHAT IT PROVES, and why it is here.  runtime/propagate/invalidate.py (absent from this repository)'s
-- survival rule (README §0-§1): a consequence dies under the retraction
-- of a fact x iff EVERY homotopy class of its justification passes
-- through x; a surviving class is one whose leaf-multiset avoids x.  The
-- decision is computed from a class enumeration that MAY BE INCOMPLETE,
-- and its result type is deliberately three-valued — SURVIVES / DEAD /
-- UNDECIDED — with recompute.apply refusing to act on UNDECIDED
-- (SCALE.md (absent from this repository) §5.1; STATUS.md failure mode #1 is exactly a boolean guess
-- here).  This module proves that the third verdict is IRREDUCIBLE:
--
--   §0  a class is characterised, for the retraction of x, by one bit —
--       true = passes through x (dies with x), false = avoids x (an
--       independent proof).  `avoids` is the GROUND TRUTH and it is
--       two-valued: the consequence's actual survival is asti or nsti.
--   §1  the epistemic verdict `decide seen complete` from a PARTIAL
--       enumeration `seen`.
--   §2  soundness of `survives`: a found survivor is real and stays real
--       under any completion (`avoids` is monotone under ++).
--   §3  soundness of `dead`, and §4 completeness ⟹ never UNDECIDED.
--   §5  THE DURNAYA — the load-bearing theorem.  No two-valued verdict
--       computed from `seen` alone can be correct: two completions of the
--       same seen prefix have DIFFERENT ground truth, so any boolean
--       decision destroys a real asti/nāsti distinction.  त्रयो निर्णयाः,
--       न द्वौ, mechanised for L4 survival.
--
-- The fibre reading: the survivors are the fibre over the seen prefix
-- that the retraction cannot see into; forcing a two-valued answer is the
-- unreceipted compression (हिंसा सङ्क्षेपः) that loses it.  UNDECIDED is
-- the honest receipt that the fibre was not enumerated.
--
-- Sources for the mathematics: runtime/propagate/README.md §0-§1,
-- invalidate.survival; runtime/SCALE.md (absent from this repository) §5.1; runtime/STATUS.md.
------------------------------------------------------------------------

module TrayoNirnayah_SurvivalUnderRetractionHasThreeVerdictsBecauseAPartialClassEnumerationCannotDecide where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Bool
open import Cubical.Data.List

------------------------------------------------------------------------
-- §0  classes, and the ground truth of survival (two-valued).
--   true  = this homotopy class passes through the retracted fact x
--   false = this class avoids x — an independent proof, a survivor
------------------------------------------------------------------------

Classes : Type
Classes = List Bool

-- SURVIVES the retraction of x  ⟺  some class avoids x.
avoids : Classes → Bool
avoids []       = false
avoids (c ∷ cs) = not c or avoids cs

------------------------------------------------------------------------
-- §1  the three verdicts, and the decision from a PARTIAL enumeration.
------------------------------------------------------------------------

data Nirnaya : Type where
  survives undecided dead : Nirnaya

-- `seen` are the classes enumerated so far; `complete` says the
-- enumeration exhausted them.  A found survivor decides SURVIVES at once;
-- otherwise only completeness licenses DEAD, and without it the honest
-- verdict is UNDECIDED.
decide : Classes → Bool → Nirnaya
decide seen complete =
  if avoids seen then survives
  else (if complete then dead else undecided)

-- a discriminator, so the three verdicts are provably distinct.
private
  isSurv : Nirnaya → Bool
  isSurv survives = true
  isSurv _        = false

  survives≢dead : ¬ (survives ≡ dead)
  survives≢dead p = true≢false (cong isSurv p)

  isUndec : Nirnaya → Bool
  isUndec undecided = true
  isUndec _         = false

  survives≢undec : ¬ (survives ≡ undecided)
  survives≢undec p = false≢true (cong isUndec p)

  dead≢undec : ¬ (dead ≡ undecided)
  dead≢undec p = false≢true (cong isUndec p)

------------------------------------------------------------------------
-- §2  soundness of SURVIVES: a found survivor is real under any completion.
--     `avoids` is monotone: appending more classes never loses a survivor.
------------------------------------------------------------------------

avoids-++ : (xs ys : Classes) → avoids xs ≡ true → avoids (xs ++ ys) ≡ true
avoids-++ []           ys h = ⊥.rec (false≢true h)
avoids-++ (true  ∷ cs) ys h = avoids-++ cs ys h
avoids-++ (false ∷ cs) ys h = refl

-- if the partial enumeration already decides SURVIVES, then the true
-- survival over any completion `seen ++ rest` is likewise `true`.
survives-sound : (seen rest : Classes) (complete : Bool)
               → decide seen complete ≡ survives
               → avoids (seen ++ rest) ≡ true
survives-sound seen rest complete h = avoids-++ seen rest seenAvoids
  where
  -- decide reduces to survives only through the `then` branch, i.e.
  -- avoids seen ≡ true; extract it by casing on avoids seen.
  seenAvoids : avoids seen ≡ true
  seenAvoids with avoids seen
  ... | true  = refl
  ... | false = ⊥.rec (helper complete h)
    where
    helper : (c : Bool) → (if c then dead else undecided) ≡ survives → ⊥
    helper true  q = survives≢dead (sym q)
    helper false q = survives≢undec (sym q)

------------------------------------------------------------------------
-- §3  soundness of DEAD: under a COMPLETE enumeration, `dead` is truthful.
------------------------------------------------------------------------

dead-sound : (cs : Classes) → decide cs true ≡ dead → avoids cs ≡ false
dead-sound cs h with avoids cs
... | false = refl
... | true  = ⊥.rec (survives≢dead h)

------------------------------------------------------------------------
-- §4  completeness ⟹ the verdict is never UNDECIDED.
------------------------------------------------------------------------

complete-decides : (cs : Classes) → ¬ (decide cs true ≡ undecided)
complete-decides cs h with avoids cs
... | true  = survives≢undec h
... | false = dead≢undec h

------------------------------------------------------------------------
-- §5  THE DURNAYA — त्रयो निर्णयाः, न द्वौ.
--
-- The incomplete standpoint: one class seen, and it passes through x, so
-- no survivor is found yet and the enumeration is not exhausted.
------------------------------------------------------------------------

seen₀ : Classes
seen₀ = true ∷ []

-- the honest verdict on it is UNDECIDED (checked).
_ : decide seen₀ false ≡ undecided
_ = refl

-- two completions of the SAME seen prefix, disagreeing in ground truth.
cs-survivor cs-dead : Classes
cs-survivor = seen₀ ++ (false ∷ [])   -- a survivor hidden past the prefix
cs-dead     = seen₀ ++ (true  ∷ [])   -- nothing but passes-through classes

_ : avoids cs-survivor ≡ true    -- truly survives
_ = refl
_ : avoids cs-dead     ≡ false   -- truly dead
_ = refl

-- No verdict computed from `seen` ALONE (a function of the seen prefix)
-- can be correct on both completions: it would have to equal both `true`
-- and `false`.  Any two-valued decision on the incomplete standpoint
-- destroys the asti/nāsti distinction the unenumerated classes carry —
-- which is exactly why the third verdict is required, not optional.
durnaya : (v : Classes → Bool)
        → v seen₀ ≡ avoids cs-survivor
        → v seen₀ ≡ avoids cs-dead
        → ⊥
durnaya v p q = true≢false (sym p ∙ q)

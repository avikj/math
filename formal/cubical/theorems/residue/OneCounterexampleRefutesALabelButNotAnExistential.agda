{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OneCounterexampleRefutesALabelButNotAnExistential
--
-- `DARWIN_GODEL_MATH.md` (absent from this repository) §7 lists its criteria, with one that is different in kind from the others:
--
--   "any artifact labeled kernel-checked or independently replayed fails
--    a clean replay.  One such authority-label error is a boundary
--    failure, not tolerable benchmark noise."
--
-- Every other criterion in that list is a threshold on a rate — 25% of
-- compute, 80% of children, half the development gain, 10% relative
-- score.  This one is not a threshold, and §2–§3 are why: a LABEL is a
-- Π-claim, and a Π-claim is refuted by one instance, while the
-- claim-shapes the other criteria use are not.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
-- §2: one labelled artifact that fails to replay refutes the label's
-- soundness outright.  No rate, no tolerance, nothing to average over.
--
-- §3: the same single failure leaves an EXISTENTIAL claim standing.
-- That is the weakest possible witness that claim-shapes differ in
-- refutation conditions, and it is chosen because it needs no counting.
------------------------------------------------------------------------

module OneCounterexampleRefutesALabelButNotAnExistential where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  A label is a claim about every artifact carrying it
------------------------------------------------------------------------

module _ (Artifact : Type) (Labeled Replays : Artifact → Type) where

  LabelSound : Type
  LabelSound = (a : Artifact) → Labeled a → Replays a

  SomethingReplays : Type
  SomethingReplays = Σ[ a ∈ Artifact ] Replays a

  --------------------------------------------------------------------
  -- 2.  One labelled artifact that fails to replay refutes the label
  --------------------------------------------------------------------

  oneFailureRefutesTheLabel :
    (a : Artifact) → Labeled a → ¬ Replays a → ¬ LabelSound
  oneFailureRefutesTheLabel a lab noRep sound = noRep (sound a lab)

------------------------------------------------------------------------
-- 3.  The same failure leaves an existential standing
--
-- Artifacts are `Bool`; every artifact carries the label; an artifact
-- replays exactly when it is `true`.  So `false` is a labelled failure
-- and `true` is a replaying artifact.
------------------------------------------------------------------------

private
  everything : Bool → Type
  everything _ = Unit

  isTrue : Bool → Type
  isTrue b = b ≡ true

theLabelIsRefuted : ¬ LabelSound Bool everything isTrue
theLabelIsRefuted =
  oneFailureRefutesTheLabel Bool everything isTrue false tt false≢true

theExistentialSurvives : SomethingReplays Bool everything isTrue
theExistentialSurvives = true , refl

bothAtOnce :
    (¬ LabelSound Bool everything isTrue)
  × (SomethingReplays Bool everything isTrue)
bothAtOnce = theLabelIsRefuted , theExistentialSurvives

------------------------------------------------------------------------
-- 4.  The reading
--
-- §7's last criterion is not a stricter threshold than the others; it is
-- not a threshold at all.  A label asserts a Π, and a Π has no
-- tolerance: one counterexample is the whole refutation, which is
-- exactly what "a boundary failure, not tolerable benchmark noise"
-- says.
--
-- §3 shows a single failure is compatible with another claim-shape
-- holding, so "noise" is a meaningful notion for SOME claims — just not
-- for this one.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE COUNT.  A genuine RATE claim ("more than half", "at most 25%")
-- needs a measure and a count.  The count is supplied in
-- `RateOneIsExactlyTheUniversalClaim`, over a finite
-- population as a `List Bool`:
--
--   countIsAtMostLength : count bs ≤ length bs
--   allGivesFullCount   : All bs → count bs ≡ length bs
--   fullCountGivesAll   : count bs ≡ length bs → All bs
--
-- So the universal claim and rate one are THE SAME CLAIM, and the label
-- criterion is not a different KIND of criterion from a threshold — it
-- is the threshold at 1, where a single failure moves the count off the
-- length and there is nothing left to tolerate.  A strictly lower
-- threshold surviving that same failure is exhibited there.
------------------------------------------------------------------------

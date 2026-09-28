{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CurvatureIsNonVacuousBecauseHereIsOnePointOffTheImage
--
-- ON THE NAME.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository); `formal/` and
-- invented.**  The content is Δ 28 §36–38's, i.e. this corpus's own,
-- plus the pasting of two squares, which is standard in any category; I
-- have established no Indian source for either and will not attach a
-- label I cannot defend.
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT.  Target: `CurvatureCannotLiveOnTheImageOfAnExactCompression`,
-- a `Cannot` — an impossibility claim.
--
-- **THE TITLE IS EARNED.**  `curvatureVanishesOnTheImage` really does
-- prove that the compressed steps commute at every `C s`, and
-- `curvatureIsOffTheImage` is its contrapositive.  Nothing is smuggled:
-- no injectivity, no surjectivity, no full abstraction.  Recorded
-- explicitly, because this sweep's business is what a title claims and
-- three of its findings so far were faults.
--
-- **ONE READING NOTE, NOT A FAULT.**  The title attributes the
-- conclusion to a property of `C` alone.  The theorem also needs
-- `comm` — that the UNCOMPRESSED steps commute — which is a hypothesis
-- about `f` and `g`, not about the compression.  In Δ 28 that is given
-- ("exact elimination commutes"), so the title is right in its setting
-- and would be an overclaim outside it.
--
-- **BUT THE MODULE SAYS OF ITSELF: "NO CURVATURE IS EXHIBITED.  Nothing
-- below constructs `f' g' C` with genuine curvature, so this is a
-- constraint on where curvature can be and not evidence that it
-- occurs."**  An impossibility theorem with no instance of the thing it
-- constrains is consistent with the constrained thing never existing —
-- in which case the theorem is true and empty.  **That gap is closed
-- here.**
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   Pt / f' / g'     three points and two compressed steps
--   curvatureAtBad   `¬ (f' (g' bad) ≡ g' (f' bad))` — the compressed
--                    steps genuinely fail to commute, at `bad`
--   hypothesesHold   and every hypothesis of the audited theorem is
--                    satisfied by this data: `S = Unit`, `f = g = id`,
--                    `C _ = im`, both intertwining squares `refl`, and
--                    `comm` `refl`
--   badIsNotReached  so, BY the audited theorem rather than by
--                    inspection, `bad` is not `C` of anything
--
-- **SO THE `Cannot` IS SHARP, NOT VACUOUS.**  Curvature exists, it is
-- off the image, and the theorem is what rules it off.  `badIsNotReached`
-- is deliberately routed through `curvatureIsOffTheImage` instead of
-- being proved directly: the point is that the audited theorem HAS
-- content on a case where the conclusion is not free.
--
-- **AND THE SMALLEST WITNESS IS NOT AS SMALL AS IT LOOKS.**  Two points
-- do not suffice: with `T = Bool` and a one-point image, all four
-- choices of `f' false`/`g' false` commute at `false`, since `f'` and
-- `g'` must both fix the image point.  Three points is the minimum for
-- this shape, and the witness needs the two steps to disagree about
-- where `bad` goes — `f' bad = off`, `g' bad = bad`, and `g' off = im`.
------------------------------------------------------------------------

module CurvatureIsNonVacuousBecauseHereIsOnePointOffTheImage where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import CurvatureCannotLiveOnTheImageOfAnExactCompression
  using (curvatureVanishesOnTheImage ; curvatureIsOffTheImage)

------------------------------------------------------------------------
-- 1.  Three points, two steps that disagree off the image
------------------------------------------------------------------------

data Pt : Type where
  im bad off : Pt

f' : Pt → Pt
f' im  = im
f' bad = off
f' off = off

g' : Pt → Pt
g' im  = im
g' bad = bad
g' off = im

-- `off` and `im` are distinguished by a map to `Bool`; this is the whole
-- decidability this module needs.
isOff : Pt → Bool
isOff im  = false
isOff bad = false
isOff off = true

curvatureAtBad : ¬ (f' (g' bad) ≡ g' (f' bad))
curvatureAtBad e = true≢false (cong isOff e)

------------------------------------------------------------------------
-- 2.  Every hypothesis of the audited theorem holds of this data
------------------------------------------------------------------------

Cc : Unit → Pt
Cc _ = im

idU : Unit → Unit
idU u = u

sfU : (u : Unit) → Cc (idU u) ≡ f' (Cc u)
sfU _ = refl

sgU : (u : Unit) → Cc (idU u) ≡ g' (Cc u)
sgU _ = refl

commU : (u : Unit) → idU (idU u) ≡ idU (idU u)
commU _ = refl

-- and the audited conclusion, on the image, is `refl` here
vanishesHere : (u : Unit) → f' (g' (Cc u)) ≡ g' (f' (Cc u))
vanishesHere = curvatureVanishesOnTheImage Cc idU idU f' g' sfU sgU commU

------------------------------------------------------------------------
-- 3.  So the audited theorem, applied, rules `bad` off the image
------------------------------------------------------------------------

badIsNotReached : ¬ (Σ[ u ∈ Unit ] Cc u ≡ bad)
badIsNotReached =
  curvatureIsOffTheImage Cc idU idU f' g' sfU sgU commU bad curvatureAtBad

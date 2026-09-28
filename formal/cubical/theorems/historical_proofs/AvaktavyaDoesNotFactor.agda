{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AvaktavyaDoesNotFactor
--
-- Three things in this repository turn out to be one thing, and none of
-- the three files says so.
--
--   `Saptabhangi.no-single-vacana`  — avaktavya: no single utterance
--       denotes the joint content (Akalaṅka, c. 720–780; the fourth
--       bhaga of the sydvda).
--   `Laghava.laghava-is-not-semantic` — लाघव is not a function of the
--       denotation (Pini's criterion, and why it had to exist).
--   `TranscriptDescent.collisionObstructsDecoder` — the barrier B3 of
--       BARRIER.md (absent from this repository), ` FactorsThrough`.
--
-- All three have the shape
--
--     ¬ Σ[ decoder ] ((x : _) → decoder (coarse x) ≡ fine x)
--
-- and this file writes the first one in that shape, so the identification
-- is a term rather than a remark.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS SETTLES ABOUT AVAKTAVYA
--
-- The fourth bhaga is standardly read as the *inexpressible*, and it is
-- easy to hear that as a truth-value gap or as undecidability.
-- `Saptabhangi` already refutes the first — `joint` is realised and
-- refuted, a genuine two-valued predicate — and this file records the
-- second:
--
--     avaktavya-decidable : (φ : Profile) → Dec (joint φ ≡ true)
--
-- decidable, because `joint φ` is a Boolean.  So avaktavya is neither a
-- gap nor an undecidability.  What it is, exactly, is a **failure to
-- factor through a single utterance** — an expressiveness fact about the
-- medium of predication, not a defect in the object predicated of.
--
-- That is precisely `Laghava`'s situation one domain over: the quantity
-- is perfectly definite, and invisible at the level where you were
-- looking.  And it is what shows that no barrier
-- in any stronger sense is expressible here:
-- avaktavya was the corpus's best candidate for something genuinely
-- inexpressible, and it is exact.
--
-- ────────────────────────────────────────────────────────────────────
------------------------------------------------------------------------

module AvaktavyaDoesNotFactor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; _≟_)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_ ; Dec)

open import SaptabhangiNaya using (Profile ; Vacana ; denotes ; joint ; no-single-vacana)

------------------------------------------------------------------------
-- 1.  Avaktavya is decidable — it is a Boolean condition
------------------------------------------------------------------------

avaktavya-decidable : (φ : Profile) → Dec (joint φ ≡ true)
avaktavya-decidable φ = joint φ ≟ true

------------------------------------------------------------------------
-- 2.  THE SHAPE.  It does not factor through a single utterance.
--
-- `Saptabhangi.no-single-vacana` gives, for each utterance, a profile
-- separating it from the joint content.  That is exactly the negation of
-- a factorisation, and here it is written as one.
------------------------------------------------------------------------

FactorsThroughOneUtterance : Type₀
FactorsThroughOneUtterance =
  Σ[ v ∈ Vacana ] ((φ : Profile) → denotes v φ ≡ joint φ)

avaktavya-does-not-factor : ¬ FactorsThroughOneUtterance
avaktavya-does-not-factor (v , agrees) =
  no-single-vacana v .snd (agrees (no-single-vacana v .fst))

------------------------------------------------------------------------
-- 3.  The three, side by side.
--
--   avaktavya   ¬ Σ[ v ] (∀ φ → denotes v φ ≡ joint φ)          here
--   लाघव        ¬ Σ[ f ] (∀ e → f (eval e) ≡ size e)            Laghava
--   the barrier ¬ Σ[ d ] (∀ x → d (blur x) ≡ observable x)      BARRIER.md (absent from this repository) B3
--
-- One shape, three traditions, and the middle one is the only place this
-- corpus had noticed it.  `TranscriptDescent.collisionObstructsDecoder`
-- records that it was independently reinvented four times here.  This is
-- the fifth site and the first outside mathematics proper.
--
-- The reading that follows, and it is a reading:  what a tradition calls
-- "inexpressible" is often not a claim about truth at all but about the
-- arity of its medium — one utterance, one denotation, one blur value —
-- and the formal content is always the same negation.  Avaktavya says so
-- about predication, लाघव about meaning, and B3 about windowed
-- observation.
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SatisfactionWithoutCodomainAgreement
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), companion to the
-- hypothesis-carrying module `AtomicSatisfaction`
-- (module `SameResponses`, which exits 0 under the pin).
--
-- the standing hypothesis `Y'_{τ(q)} = Y_q`, which appears once in §1
-- prose (line 29) and in neither the Theorem (line 59), the title, nor
-- the Status line.  §2 of the draw traces the drop one artifact
-- downstream: `collab/messages/0410-codex-skein-atomic-satisfaction-
-- result.md` (absent from this repository) states the equivalence "for a proposed probe translation
-- `tau:Q->Q'` and state reduction `s:X'->X`" with no mention of the
-- hypothesis at all.
--
-- Asserted below: the invariant of `SameResponses` — the version whose
-- atoms `(q,y)` are drawn from the OLD response family `Y` — for a
-- revised observer whose responses land in an INDEPENDENT family `Y′`,
-- which is what the sentence says once `Y′ ∘ τ = Y` is gone.
--
-- WHY IT MUST FAIL.  This drop is not of the "false as stated" kind
-- (contrast `Control/ReachabilityWithoutStart.agda`); the audit's words
-- are that without it "the atom `(τ(q),y)` is not even well-typed on
-- the revised side".  A type checker is the exact instrument for that:
-- `r′ q x′ : Y′ q` and `y : Y q`, and with `Y′` unconstrained there is
-- no path type to write down.  The failure is a TYPE failure at the
-- equation, not a failed proof.
--
-- NO LEXICAL SIGNATURE.  The Theorem's sentence is grammatical, cites
-- the right maps, and reads as complete; a hypothesis stated one
-- section earlier is simply not repeated.  Nothing distinguishes it
-- lexically from the correct statement.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may.
--
-- OBSERVED, 2026-08-15, THE PIN (Agda 2.8.0 + cubical v0.9; see
-- --library-file=<v0.9>
-- NaturalMachine/Control/SatisfactionWithoutCodomainAgreement.agda`,
-- exit code 42, error verbatim:
--
--   NaturalMachine/Control/SatisfactionWithoutCodomainAgreement.agda:81.18-19:
--   error: [UnequalTerms]
--   Y q !=< Y′ q
--   when checking that the expression y has type Y′ q
--
-- Read it: the machine names the dropped hypothesis as an equation
-- between the two response families, `Y q !=< Y′ q`, in exactly the
-- position where the Theorem and message 0410 omit it.
--
-- If a future edit makes this file compile, the atomic-satisfaction
-- statement has been silently extended past its codomain hypothesis and
-- the corpus has readmitted the defect FULL_READ_DRAW_6 §D2 catalogued.
------------------------------------------------------------------------

module SatisfactionWithoutCodomainAgreement where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)

module Dropped
  {ℓX ℓX′ ℓQ ℓY ℓY′ : Level}
  {X : Type ℓX} {X′ : Type ℓX′} {Q : Type ℓQ}
  (Y : Q → Type ℓY) (Y′ : Q → Type ℓY′)
  (r : (q : Q) → X → Y q)
  (r′ : (q : Q) → X′ → Y′ q)
  (s : X′ → X)
  where

  SatisfactionInvariant : Type _
  SatisfactionInvariant =
    (x′ : X′) (q : Q) (y : Y q) →
      (r′ q x′ ≡ y → r q (s x′) ≡ y)
      × (r q (s x′) ≡ y → r′ q x′ ≡ y)

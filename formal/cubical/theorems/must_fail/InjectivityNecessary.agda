{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- InjectivityNecessary
--
-- *** THIS FILE MUST FAIL TO TYPE-CHECK. ***
--
-- Designed annihilation (collab/PROTOCOL.md (absent from this repository) §7), companion to
-- `ComparisonNeedNotBeInjective` (exit 0 under the pin).
--
-- `OBSERVER_REVISION_IS_ATOMIC_SATISFACTION.md` (absent from this repository) §4 writes "injectivity
-- of `j_q` is **needed**", and
-- `collab/messages/0469-atomic-satisfaction-is-response-square.md` (absent from this repository)
-- hardens that into a report that the Agda checks the comparison maps
-- "**must be** injective for the backwards implication".  Two
-- assertions, the two ways this modality-drop shows up in prose:
--
--   (a) the sufficiency theorem WITHOUT its injectivity hypothesis —
--       "the square gives the biconditional", full stop, which is what
--       a reader takes away once "needed" is heard as "the condition";
--   (b) the necessity claim's CONSEQUENCE in the checked instance of
--       `ComparisonNeedNotBeInjective`: there `invariant` holds and
--       `j` merges `one` and `two`, so if the invariant forced
--       injectivity we would have `one ≡ two`.
--
-- WHY IT MUST FAIL.  (a) `ChangedResponses.square→satisfaction` wants
-- `InjectiveComparisons` and the general statement without it is false
-- — merge a REALIZED outcome with another and the forward direction
-- breaks.  (b) `one` and `two` are distinct constructors
-- (`one≢two`), so the necessity claim's consequence is refuted by the
-- machine directly.
--
-- NO LEXICAL SIGNATURE.  "Needed" and "must be" are ordinary words in
-- the right places; nothing separates them from a correct sufficiency
-- statement except the mathematics.  grep cannot see a modality; a
-- type can.
--
-- It is NOT part of the checked build.  `agda` does not
-- import it, and nothing else may.
--
-- Under the pin (Agda 2.8.0 + cubical v0.9; see
-- --library-file=<v0.9> NaturalMachine/Control/InjectivityNecessary.agda`,
-- exit code 42, error verbatim:
--
--   NaturalMachine/Control/InjectivityNecessary.agda:80.19-23:
--   error: [UnequalTerms]
--   one != two of type Three
--   when checking that the expression refl has type one ≡ two
--
-- Read it: the machine refutes the necessity claim's consequence by
-- naming the two unrealized outcomes the comparison merges — the exact
-- pair whose merging the note's "needed" and the message's "must be"
-- declare impossible.
--
-- If a future edit makes this file compile, injectivity has been
-- silently promoted from sufficient to necessary and the corpus has
-- readmitted the defect FULL_READ_DRAW_6 §D3 catalogued.
------------------------------------------------------------------------

module InjectivityNecessary where

open import Cubical.Foundations.Prelude

open import AtomicSatisfaction using (module ChangedResponses)
open import ComparisonNeedNotBeInjective using (Three ; one ; two)

-- (b) What "must be injective" would give in the checked instance.
merged-outcomes : one ≡ two
merged-outcomes = refl

-- (a) The sufficiency theorem with its hypothesis deleted.
module Dropped
  {ℓX ℓX′ ℓQ ℓY ℓY′ : Level}
  {X : Type ℓX} {X′ : Type ℓX′} {Q : Type ℓQ}
  (Y : Q → Type ℓY) (Y′ : Q → Type ℓY′)
  (r : (q : Q) → X → Y q)
  (r′ : (q : Q) → X′ → Y′ q)
  (s : X′ → X)
  (j : (q : Q) → Y q → Y′ q)
  where

  open ChangedResponses Y Y′ r r′ s j

  square→satisfaction-dropped : ResponseSquare → SatisfactionInvariant
  square→satisfaction-dropped = square→satisfaction

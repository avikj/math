{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.HolonomyIsInvisibleExactlyToAnInvariantSemantics
--
-- `notes/DEPENDENT_SYSTEM_OPTIMIZATION_DELTA_28.md` (absent from this repository) §36–38 closes:
--
--   "Even flat architectures can carry interface holonomy h : Z ≃ Z
--    around loops in architecture space — harmless for boundary
--    semantics, load-bearing for caches, provenance, optimizer state,
--    proofs."
--
-- That sentence reports TWO observations.  They are one, and saying
-- which one needs the loop to be an actual PATH rather than a metaphor
-- — which is the one place in this section where the cubical substrate
-- earns its keep rather than merely hosting the argument.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   invariantSemanticsIsUnmoved
--       a consumer `sem : Z → B` satisfying `sem ∘ h ≡ sem` sees
--       nothing after transport along `ua h`.  This is the "harmless
--       for boundary semantics" half, and the hypothesis is exactly
--       what "boundary semantics" has to mean for it to hold.
--   nonTrivialHolonomyMovesTheRawInterface
--       a consumer that is the raw interface itself is moved wherever
--       `h` moves a point.  This is the "load-bearing for caches" half:
--       a cache keyed by `Z` is the identity consumer, and the identity
--       consumer is invariant only if `h` is.
--   notIsGenuineHolonomy / theCacheIsMoved
--       and non-trivial holonomy exists: `notEquiv` on `Bool`, where
--       `transport (ua notEquiv) true ≢ true`
--
-- **So the two halves of §36–38's sentence are one theorem read at two
-- consumers.**  Holonomy is invisible exactly to consumers invariant
-- under it, and the list "caches, provenance, optimizer state, proofs"
-- is a list of consumers that are NOT — they are keyed by the raw
-- interface, which is the identity consumer, and the identity consumer
-- is invariant only when the holonomy is trivial.  There is no separate
-- fact about caches to establish.
--
-- ────────────────────────────────────────────────────────────────────
-- WHY UNIVALENCE IS DOING WORK HERE.  Without it, `h : Z ≃ Z` and a
-- loop in architecture space are different objects and the sentence
-- above is an analogy.  `ua` makes the loop a path, `uaβ` computes
-- transport along it back to `h`, and the two theorems are then about
-- the SAME `h` — the invariance hypothesis and the transport are
-- connected rather than merely parallel.  `notEquiv` is the standard
-- witness that this content is not vacuous: a self-equivalence with no
-- fixed point at `true`.
--
-- NO NOVELTY WHATSOEVER.  `ua`, `uaβ` and the `not` automorphism of
-- `Bool` are the first examples in every cubical development, and
-- Voevodsky's univalence axiom is the substrate this repository already
-- runs on.  What is contributed is the identification of §36–38's two
-- clauses as one statement.
------------------------------------------------------------------------

module NaturalMachine.HolonomyIsInvisibleExactlyToAnInvariantSemantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun)
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; notEquiv ; true≢false)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  Interface holonomy
------------------------------------------------------------------------

Holonomy : Type → Type
Holonomy Z = Z ≃ Z

------------------------------------------------------------------------
-- 2.  A consumer invariant under the holonomy sees nothing
------------------------------------------------------------------------

invariantSemanticsIsUnmoved :
  {Z B : Type} (h : Holonomy Z) (sem : Z → B)
  → ((z : Z) → sem (equivFun h z) ≡ sem z)
  → (z : Z) → sem (transport (ua h) z) ≡ sem z
invariantSemanticsIsUnmoved h sem inv z =
  cong sem (uaβ h z) ∙ inv z

------------------------------------------------------------------------
-- 3.  A consumer keyed by the raw interface is moved
------------------------------------------------------------------------

nonTrivialHolonomyMovesTheRawInterface :
  {Z : Type} (h : Holonomy Z) (z : Z)
  → ¬ (equivFun h z ≡ z) → ¬ (transport (ua h) z ≡ z)
nonTrivialHolonomyMovesTheRawInterface h z moved e =
  moved (sym (uaβ h z) ∙ e)

------------------------------------------------------------------------
-- 4.  And non-trivial holonomy exists
------------------------------------------------------------------------

notIsGenuineHolonomy : ¬ (equivFun notEquiv true ≡ true)
notIsGenuineHolonomy e = true≢false (sym e)

theCacheIsMoved : ¬ (transport (ua notEquiv) true ≡ true)
theCacheIsMoved =
  nonTrivialHolonomyMovesTheRawInterface notEquiv true notIsGenuineHolonomy

------------------------------------------------------------------------
-- 5.  One loop, two verdicts
------------------------------------------------------------------------

oneLoopTwoVerdicts :
  ((b : Bool) → (λ (_ : Bool) → b) (transport (ua notEquiv) true)
              ≡ (λ (_ : Bool) → b) true)
  × (¬ (transport (ua notEquiv) true ≡ true))
oneLoopTwoVerdicts =
  (λ b → invariantSemanticsIsUnmoved notEquiv (λ _ → b) (λ _ → refl) true)
  , theCacheIsMoved

------------------------------------------------------------------------
-- §2 proves invariant ⟹ unmoved. The same holds of §3:
-- `nonTrivialHolonomyMovesTheRawInterface` goes one way only.
--
-- **BOTH CONVERSES COST NOTHING.**  `uaβ h z` is a PATH, so it may
-- be walked in either orientation; each backward direction is the
-- forward one composed with `sym`.  In
-- `NaturalMachine.HolonomyIsInvisibleExactlyToAnInvariantConsumerAndExactlyIsNowEarned`:
-- `invisible→invariant`, `invisibleExactlyWhenInvariant`, and —
-- given `isSet B` — `invisibleIsInvariantAsTypes`, an EQUIVALENCE of
-- the two conditions rather than a two-way implication.  `Invariant`
-- and `Invisible` are named there; `invariant→invisible` is
-- `invariantSemanticsIsUnmoved` REUSED, not restated.
------------------------------------------------------------------------

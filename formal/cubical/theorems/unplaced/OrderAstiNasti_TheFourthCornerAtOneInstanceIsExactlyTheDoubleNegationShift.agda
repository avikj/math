{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift
--
-- `TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet` gave a
-- second SUFFICIENT condition for refuting the fourth corner and closed:
--
--
-- A necessary one is here, for one family, and it identifies the corner
-- with a named principle instead of describing it.
--
-- Take the instance set to be a SINGLE instance (`Unit`) and let the
-- remedies be arbitrary.  Then, writing `bad _ r = Q r`:
--
--   ¬ सामयिक bad  ≃  (r : R) → ¬ ¬ Q r
--   ¬ नित्य   bad  ≃  ¬ ((r : R) → Q r)
--
-- so the fourth corner IS
--
--   ((r : R) → ¬ ¬ Q r)  ×  ¬ ((r : R) → Q r)
--
-- which is exactly a counterexample to the DOUBLE-NEGATION SHIFT,
-- `(∀x ¬¬A x) → ¬¬ (∀x A x)` — the principle isolated by Spector's
-- bar-recursion interpretation of analysis (`Provably recursive
-- functionals of analysis`, 1962) and by Kreisel before him.  DNS
-- refutes the configuration outright: from `¬¬ Π` and `¬ Π`.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   notSamayikaIsPointwiseDoubleNegation   both directions
--   notNityaIsNotThePi                     both directions
--   fourthCornerIsDNSFailure               the two together
--   fourthCornerRefutesPointwiseStability
--       and therefore, at this family, the earlier module's hypothesis
--       is NECESSARY and not merely sufficient: the corner exists only
--       where `Stable (Q r)` fails at some r
--
-- The last one is the point.  Two modules gave sufficient conditions and
-- said no necessary one was known.  Here the condition is necessary, so
-- the search for the fourth corner is not "look for an exotic instance
-- family" — a ONE-element instance family already suffices, and the
-- whole question is whether the BADNESS is stable.  The earlier
-- `Enumerated` route was answering a question the corner does not ask.
--
-- The `Unit` instance set is a specialisation: the equivalence is
-- proved for it and NOT for a general instance family, where
-- `¬ सामयिक` does not reduce this way.
--
-- School named before the term: सामयिक and नित्य are `AnuktaAvaktavya`'s,
-- another identity's, imported unchanged; the fourth corner is the
-- position in the saptabhag reading that module sets up.  The
-- double-negation shift is not a Jaina notion;
-- the identification is between a configuration this repository
-- wrote down and a principle from proof theory, and it is an
-- identification of the FORMULA, not of the two traditions' concerns.
--

module OrderAstiNasti_TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import AnuktaAvaktavya using (सामयिक ; नित्य)

private
  variable
    R : Type

Stable : Type → Type
Stable A = ¬ ¬ A → A

------------------------------------------------------------------------
-- 1.  One instance, arbitrary remedies
------------------------------------------------------------------------

one : {R : Type} → (R → Type) → (Unit → R → Type)
one Q _ r = Q r

------------------------------------------------------------------------
-- 2.  The two negations, computed
------------------------------------------------------------------------

notSamayikaGivesPointwise :
  (Q : R → Type) → ¬ सामयिक (one Q) → (r : R) → ¬ ¬ Q r
notSamayikaGivesPointwise Q h r nq = h (λ _ → r , nq)

pointwiseGivesNotSamayika :
  (Q : R → Type) → ((r : R) → ¬ ¬ Q r) → ¬ सामयिक (one Q)
pointwiseGivesNotSamayika Q k f = k (fst (f tt)) (snd (f tt))

notNityaGivesNotThePi :
  (Q : R → Type) → ¬ नित्य (one Q) → ¬ ((r : R) → Q r)
notNityaGivesNotThePi Q h g = h (λ r → tt , g r)

notThePiGivesNotNitya :
  (Q : R → Type) → ¬ ((r : R) → Q r) → ¬ नित्य (one Q)
notThePiGivesNotNitya Q k f = k (λ r → snd (f r))

------------------------------------------------------------------------
-- 3.  So the fourth corner IS a failure of the double-negation shift
------------------------------------------------------------------------

DNSFailure : {R : Type} → (R → Type) → Type
DNSFailure {R} Q = ((r : R) → ¬ ¬ Q r) × (¬ ((r : R) → Q r))

fourthCornerGivesDNSFailure :
  (Q : R → Type)
  → (¬ सामयिक (one Q)) × (¬ नित्य (one Q)) → DNSFailure Q
fourthCornerGivesDNSFailure Q (ns , nn) =
  notSamayikaGivesPointwise Q ns , notNityaGivesNotThePi Q nn

dnsFailureGivesFourthCorner :
  (Q : R → Type)
  → DNSFailure Q → (¬ सामयिक (one Q)) × (¬ नित्य (one Q))
dnsFailureGivesFourthCorner Q (pw , np) =
  pointwiseGivesNotSamayika Q pw , notThePiGivesNotNitya Q np

------------------------------------------------------------------------
-- 4.  Hence the earlier hypothesis is NECESSARY here, not just sufficient
--
-- Pointwise stability turns `(r) → ¬ ¬ Q r` into `(r) → Q r`, which the
-- second component forbids.  So at a one-instance family the corner
-- exists ONLY where the badness fails to be stable — the instance set
-- has nothing to do with it.
------------------------------------------------------------------------

fourthCornerRefutesPointwiseStability :
  (Q : R → Type)
  → (¬ सामयिक (one Q)) × (¬ नित्य (one Q))
  → ¬ ((r : R) → Stable (Q r))
fourthCornerRefutesPointwiseStability Q corner stab =
  snd d (λ r → stab r (fst d r))
  where
    d : DNSFailure Q
    d = fourthCornerGivesDNSFailure Q corner

------------------------------------------------------------------------
-- Enumerability of the REMEDY set is a different matter and is NOT
-- inert.  In `AnEnumerableRemedySetKillsTheFourthCorner`:
--
--   finiteDNSList   `All (¬¬ P) xs → ¬ ¬ All P xs`, by induction — no
--                   decidability, no choice
--   finiteDNS       hence `((r) → ¬¬ Q r) → ¬ ¬ ((r) → Q r)` for an
--                   ENUMERATED remedy set
--   theFourthCornerNeedsANonEnumerableRemedySet
--                   so the corner refutes `Enumerated R`
--
-- **THE TWO ENUMERABILITY HYPOTHESES ARE NOT SYMMETRIC.**  Enumerating
-- the INSTANCES buys nothing — one instance suffices for the corner and
-- one instance is enumerable.  Enumerating the REMEDIES buys
-- everything: DNS becomes a theorem and the corner cannot exist.
--
-- WHERE THE CORNER CAN LIVE, as narrow as it has been: a
-- NON-ENUMERABLE remedy set with a badness that is not stable.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ON THE NAME.
-- `KramaSaha_TheFourthCornerIWasNamingIsTheSequentialPosition` (absent from this repository) proves
-- this line's "fourth corner" is a product of two independent
-- negations and that simultaneous refusal collapses into the
-- sequential pair, so the position is the THIRD bhaṅga —
-- स्यात्-अस्ति-नास्ति, asserted क्रमेण — and not avaktavya.  See also
-- `OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet`.
------------------------------------------------------------------------

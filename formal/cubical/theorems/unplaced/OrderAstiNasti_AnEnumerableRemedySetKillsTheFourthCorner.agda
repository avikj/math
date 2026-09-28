{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- मूलवाक्यम् · PROVENANCE OF THE NAME.
--
-- क्रम · नास्ति — two terms, one from each half of the सप्तभङ्गी apparatus.
--
--   स्यान्नास्ति, the second भङ्ग: in some respect, it is not.  **Samantabhadra,
--   *ptamms* 14-24 (~6th c. CE); Akalaka, *Laghyastraya* (~8th c.);
--   rooted in Umsvti, *Tattvrthastra* 5.31-32 (~2nd-5th c.).**
--
--   क्रमार्पण versus सहार्पण — presentation in SUCCESSION versus SIMULTANEOUSLY.
--   **Akalaka, *Laghyastraya* (~8th c.); Vidynandin,
--   *Tattvrthalokavrttika* (~9th c.).**  This is the load-bearing one:
--   अस्ति and नास्ति asserted in succession give the third भङ्ग and are
--   expressible; asserted together they give अवक्तव्य, the fourth, which is
--   neither unknown nor undefined nor empty but a positive fourth position.
--   The distinction is what makes seven positions and not four.
--
-- **No claim is made that Samantabhadra, Akalaka or Vidynandin proved
-- anything below.**  The sevenfold division and the क्रम/सह distinction are
-- theirs, stated as doctrine; the theorems here are about what the fourth
-- corner can and cannot be over particular index types in cubical type
-- theory, and they are this repository's.  The Jaina texts do not contain a
-- claim about enumerable decidable instance sets and nothing here should be
-- read as saying they do.
--
------------------------------------------------------------------------
-- AnEnumerableRemedySetKillsTheFourthCorner
--
-- `TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift` showed
-- that at a single instance the fourth corner IS a counterexample to
-- the double-negation shift, and left EXISTENCE open with the remark
-- that a model would be needed.  It also recorded that the earlier
-- `Enumerated` hypothesis on the INSTANCE set was INERT there —
-- `Enumerated Unit` is immediate, so enumerability of instances cannot
-- be what separates the corner from its absence.
--
-- Enumerability of the REMEDY set is a different matter, and it is not
-- inert: it kills the corner outright.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   All / allFromPointwise / allAtMember
--                     the recursive family and its two directions
--   finiteDNSList     the double-negation shift holds over a LIST:
--                     `All (¬¬ P) xs → ¬ ¬ All P xs`, by induction, with
--                     no decidability and no choice
--   finiteDNS         hence over an ENUMERATED type:
--                     `((r) → ¬ ¬ Q r) → ¬ ¬ ((r) → Q r)`
--   theFourthCornerNeedsANonEnumerableRemedySet
--                     so at a single instance the fourth corner refutes
--                     `Enumerated R`
--
-- **The two enumerability hypotheses are not symmetric, and that is the
-- finding.**  Enumerating the INSTANCES buys nothing — one instance
-- already suffices for the corner, and one instance is enumerable.
-- Enumerating the REMEDIES buys everything: DNS becomes a theorem, and
-- the corner cannot exist.  An earlier module reached for `Enumerated`
-- on the wrong side of the pair and this says which side it belonged
-- on.  Where the corner can live is now: a NON-ENUMERABLE remedy set
-- with a badness that is not stable.
--
-- ────────────────────────────────────────────────────────────────────
-- NO NOVELTY.  That DNS holds over a finite index is elementary and
-- classical in the constructive literature — DNS is only interesting
-- for infinite domains, which is exactly why Spector's bar recursion
-- concerns `ℕ`.  It is proved here because this corpus reached for
-- enumerability twice without noticing the two sides differ.
--
-- School named: सामयिक and नित्य are `AnuktaAvaktavya`'s, another
-- identity's, used unchanged; DNS is from proof theory and no claim is
-- made that the two traditions are talking about one thing.
------------------------------------------------------------------------

module OrderAstiNasti_AnEnumerableRemedySetKillsTheFourthCorner where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import AnuktaAvaktavya using (सामयिक ; नित्य)
open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; Enumerated)
open import OrderAstiNasti_TheFourthCornerAtOneInstanceIsExactlyTheDoubleNegationShift
  using (one ; DNSFailure ; fourthCornerGivesDNSFailure)

private
  variable
    A R : Type

------------------------------------------------------------------------
-- 1.  All, and its two directions
------------------------------------------------------------------------

All : (P : A → Type) → List A → Type
All P []       = Unit
All P (x ∷ xs) = P x × All P xs

allFromPointwise :
  (P : A → Type) → ((a : A) → P a) → (xs : List A) → All P xs
allFromPointwise P f []       = tt
allFromPointwise P f (x ∷ xs) = f x , allFromPointwise P f xs

allAtMember :
  (P : A → Type) (xs : List A) (a : A)
  → All P xs → Any (λ y → y ≡ a) xs → P a
allAtMember P []       a _          e       = ⊥.rec e
allAtMember P (x ∷ xs) a (p , _)    (inl q) = subst P q p
allAtMember P (x ∷ xs) a (_ , rest) (inr m) = allAtMember P xs a rest m

------------------------------------------------------------------------
-- 2.  The double-negation shift holds over a list
--
-- No decidability, no choice: the negative translation of a finite
-- conjunction is a finite conjunction of negative translations, and
-- the induction is one line.
------------------------------------------------------------------------

finiteDNSList :
  (P : A → Type) (xs : List A)
  → All (λ a → ¬ ¬ P a) xs → ¬ ¬ All P xs
finiteDNSList P []       _           k = k tt
finiteDNSList P (x ∷ xs) (nnp , rest) k =
  nnp (λ p → finiteDNSList P xs rest (λ ap → k (p , ap)))

------------------------------------------------------------------------
-- 3.  Hence over an enumerated type
------------------------------------------------------------------------

finiteDNS :
  (Q : R → Type) → Enumerated R
  → ((r : R) → ¬ ¬ Q r) → ¬ ¬ ((r : R) → Q r)
finiteDNS {R = R} Q (xs , cov) pointwise k =
  finiteDNSList Q xs (allFromPointwise (λ r → ¬ ¬ Q r) pointwise xs)
    (λ allQ → k (λ r → allAtMember Q xs r allQ (cov r)))

------------------------------------------------------------------------
-- 4.  So the corner needs a non-enumerable remedy set
------------------------------------------------------------------------

theFourthCornerNeedsANonEnumerableRemedySet :
  (Q : R → Type)
  → (¬ सामयिक (one Q)) × (¬ नित्य (one Q))
  → ¬ Enumerated R
theFourthCornerNeedsANonEnumerableRemedySet Q corner enum =
  finiteDNS Q enum (fst d) (snd d)
  where
    d : DNSFailure Q
    d = fourthCornerGivesDNSFailure Q corner

------------------------------------------------------------------------
-- ON THE NAME.
-- `KramaSaha_TheFourthCornerIWasNamingIsTheSequentialPosition` (absent from this repository) proves
-- this line's "fourth corner" is a product of two independent
-- negations and that simultaneous refusal collapses into the
-- sequential pair, so the position is the THIRD bhaṅga —
-- स्यात्-अस्ति-नास्ति, asserted क्रमेण — and not avaktavya.  See also
-- `OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet`.
------------------------------------------------------------------------

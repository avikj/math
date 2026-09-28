{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RnaDhana_TheParetoMaximumTransfersToCostCoordinates
--
-- ऋणधन · ṛṇa-dhana — Brahmagupta, *Brāhmasphuṭasiddhānta* (628): the
-- same magnitude read as *dhana* (asset) or *a* (debt).  The sign
-- rules are his; the caps, the adjunction and everything below are not.
--
-- ────────────────────────────────────────────────────────────────────
-- The theorems on the Pareto line are stated for a vector all of whose
-- coordinates point the same way, while DARWIN §5.2's objectives
-- include wall time, tokens and dollars, which are to be MINIMISED.
-- `FlippingACostCoordinateIsSoundButNotFaithful` proves the flip sound
-- and refutes its unrestricted converse, and
-- `RnaDhana_PerCoordinateCapsAreTheHonestVersionAndOneCapIsTheSpecialCase`
-- makes it faithful below per-coordinate caps.
--
-- This module applies it: an existing Pareto theorem is USED, through the
-- flip, to prove a statement about genuinely mixed benefit/cost
-- vectors.  Nothing about maximality is re-proved.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   MixedStrict ds u z   z beats u in the MIXED order: `Dom ds u z`
--                        and not `Dom ds z u` — `≤` at benefit
--                        coordinates, `≥` at cost coordinates
--   MixedMaximal         nothing in the archive beats u
--   AllBounded           every member's cost entries are below their
--                        own caps
--   anyMapBack / memberMaps
--                        the two transfers along `map` that carry
--                        membership and `Any` across the flip
--   mixedMaximalExists   **every non-empty archive of mixed vectors
--                        has a mixed-maximal member, provided the caps
--                        bound its members** — proved by calling
--                        `maximalExists` on the flipped archive and
--                        pulling the result back
--
-- **WHAT THE PULL-BACK COSTS, AND WHERE.**  Soundness moves forward for
-- nothing; the bound is needed only in the NEGATIVE half — to turn
-- "the flipped z does not beat the flipped u" back into "z does not
-- beat u" one needs `flipCapsReflect`, whose hypothesis is a bound on
-- u.  Since u is a member of the archive, `AllBounded` supplies it.
-- So the obligation is: **cap each cost coordinate, in its own units, above the
-- costs of the archive's members — and then every benefit-reading
-- theorem is available.**
--
-- The flip is NOT injective (that is exactly
-- `flipIsNotFaithful`), so the pull-back cannot go through the flipped
-- element: it goes through `anyMapBack`, which recovers a member of the
-- ORIGINAL archive whose flip is the maximal element found.  That is
-- the step where a naive transfer would break.
------------------------------------------------------------------------

module RnaDhana_TheParetoMaximumTransfersToCostCoordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; memberToAny)
open import EveryRemainderMemberIsStrictlyDominated
  using (anyToMember)
open import OneStepCoverageAndDisjointnessOfTheLayer using (Mem)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy ; IsParetoMaximal)
open import ANonEmptyArchiveHasANonEmptyStratum using (maximalExists)
open import FlippingACostCoordinateIsSoundButNotFaithful
  using (Vec ; Dom)
open import RnaDhana_PerCoordinateCapsAreTheHonestVersionAndOneCapIsTheSpecialCase
  using (Caps ; BoundedC ; flipWithCaps ; flipCapsIsSound ; flipCapsReflect)

------------------------------------------------------------------------
-- 1.  The mixed order and the bounded archive
------------------------------------------------------------------------

MixedStrict : (ds : List Bool) → Vec ds → Vec ds → Type
MixedStrict ds u z = Dom ds u z × (¬ Dom ds z u)

MixedMaximal : (ds : List Bool) → List (Vec ds) → Vec ds → Type
MixedMaximal ds vs u = ¬ Any (MixedStrict ds u) vs

AllBounded : (ds : List Bool) → Caps ds → List (Vec ds) → Type
AllBounded ds cs []       = Unit
AllBounded ds cs (v ∷ vs) = BoundedC ds cs v × AllBounded ds cs vs

boundedAtMember :
  (ds : List Bool) (cs : Caps ds) (vs : List (Vec ds)) (u : Vec ds)
  → AllBounded ds cs vs → Mem u vs → BoundedC ds cs u
boundedAtMember ds cs []       u _        e       = ⊥.rec e
boundedAtMember ds cs (v ∷ vs) u (b , bs) (inl q) = subst (BoundedC ds cs) q b
boundedAtMember ds cs (v ∷ vs) u (b , bs) (inr r) =
  boundedAtMember ds cs vs u bs r

------------------------------------------------------------------------
-- 2.  Transfers along `map`
------------------------------------------------------------------------

anyMapBack :
  {A B : Type} (f : A → B) (P : B → Type) (xs : List A)
  → Any P (map f xs) → Any (λ x → P (f x)) xs
anyMapBack f P []       e       = ⊥.rec e
anyMapBack f P (x ∷ xs) (inl p) = inl p
anyMapBack f P (x ∷ xs) (inr q) = inr (anyMapBack f P xs q)

memberMaps :
  {A B : Type} (f : A → B) (xs : List A) (x : A)
  → Mem x xs → Mem (f x) (map f xs)
memberMaps f []       x e       = ⊥.rec e
memberMaps f (y ∷ xs) x (inl q) = inl (cong f q)
memberMaps f (y ∷ xs) x (inr r) = inr (memberMaps f xs x r)

------------------------------------------------------------------------
-- 3.  The maximum transfers
------------------------------------------------------------------------

mixedMaximalExists :
  (ds : List Bool) (cs : Caps ds) (v : Vec ds) (vs : List (Vec ds))
  → AllBounded ds cs (v ∷ vs)
  → Σ[ u ∈ Vec ds ] (Mem u (v ∷ vs) × MixedMaximal ds (v ∷ vs) u)
mixedMaximalExists ds cs v vs ab
  with maximalExists (flipWithCaps ds cs v) (map (flipWithCaps ds cs) vs)
... | (m , memM , maxM)
      with anyToMember (λ u → flipWithCaps ds cs u ≡ m) (v ∷ vs)
             (anyMapBack (flipWithCaps ds cs) (λ y → y ≡ m) (v ∷ vs) memM)
...     | (u , memU , equ) = u , memU , notBeaten
  where
    notBeaten : MixedMaximal ds (v ∷ vs) u
    notBeaten anyStrict with anyToMember (MixedStrict ds u) (v ∷ vs) anyStrict
    ... | (z , memZ , (domUZ , notDomZU)) =
      maxM (memberToAny (StrictlyDominatedBy m) (flipWithCaps ds cs z)
             (map (flipWithCaps ds cs) (v ∷ vs))
             (memberMaps (flipWithCaps ds cs) (v ∷ vs) z memZ)
             (subst (λ t → StrictlyDominatedBy t (flipWithCaps ds cs z)) equ
               ( flipCapsIsSound ds cs u z domUZ
               , (λ le → notDomZU
                   (flipCapsReflect ds cs z u
                     (boundedAtMember ds cs (v ∷ vs) u ab memU) le)))))

------------------------------------------------------------------------
-- THE STRATIFICATION TRANSFERS TOO.  Its first layer is
-- `RnaDhana_TheMixedStratumIsExactlyTheFlippedStratum`: under the caps,
-- `map flip (mixedStratum ds vs) ≡ stratum (map flip vs)` — the two
-- layers are the SAME LIST, order and multiplicity included.  What
-- makes that possible despite the flip not being injective is that
-- both sides are filters of the same list in the same order, so
-- `filterMapCommutes` moves the map across the filter and
-- `filterRespectsOn` needs the two predicates to agree only AT
-- MEMBERS — which is exactly where `AllBounded` gives a cap.  The
-- REMAINDER half (same argument, negated predicate) and the iteration
-- are in `RnaDhana_TheWholeMixedStratificationIsTheFlippedOne`.
------------------------------------------------------------------------

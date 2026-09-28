{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RnaDhana_TheMixedStratumIsExactlyTheFlippedStratum
--
-- ऋणधन · ṛṇa-dhana — Brahmagupta, *Brāhmasphuṭasiddhānta* (628): one
-- magnitude read as *dhana* (asset) or *a* (debt).  His are the sign
-- rules; the caps, the filters and the transfer below are not.
--
-- ────────────────────────────────────────────────────────────────────
-- `RnaDhana_TheParetoMaximumTransfersToCostCoordinates` transferred
-- maximal EXISTENCE.  The first layer is transferred here, and the
-- two layers are the SAME LIST.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   decDom              mixed dominance is decidable
--   decMixedMaximal     hence so is mixed maximality against a finite
--                       archive
--   mixedStratum        the mixed layer, as a computed list of vectors
--   filterMapCommutes   filtering a mapped list is mapping a filtered
--                       one, for the pulled-back predicate
--   filterRespectsOn    two decidable predicates agreeing ON THE
--                       MEMBERS of a list filter it identically — the
--                       restriction to members is what makes it usable
--                       here, since the bound only holds for members
--   mixedMaximalIff     under the caps, `MixedMaximal ds vs u` and
--                       `IsParetoMaximal (flip u) (map flip vs)` are
--                       interderivable, for any bounded u
--   theMixedStratumIsTheFlippedStratum
--                       `map flip (mixedStratum ds vs) ≡
--                        stratum (map flip vs)`
--
-- **WHY LIST EQUALITY AND NOT JUST MEMBERSHIP.**  The flip is not
-- injective, so nothing about individual elements would give the lists.
-- What gives them is that both sides are FILTERS OF THE SAME LIST in
-- the same order — `filterMapCommutes` moves the map across the
-- filter, and `filterRespectsOn` then only needs the two predicates to
-- agree at members.  Order and multiplicity are preserved for free
-- because neither side reorders; a `Mem`-level statement would have
-- thrown that away.
--
-- **AND THE BOUND IS NEEDED EXACTLY ONCE PER DIRECTION.**  Going from
-- the flipped world back to the mixed one needs `flipCapsReflect`,
-- whose hypothesis is a cap on the vector claimed to dominate; in one
-- direction that is the archive member z (supplied by `AllBounded`),
-- in the other it is u itself (supplied by the caller).  Soundness
-- needs nothing.
--
-- ────────────────────────────────────────────────────────────────────
-- NO NOVELTY.  Filter/map commutation and "equal filters from
-- pointwise-equivalent predicates" are standard list lemmas; the
-- Pareto layer is Goldberg/Deb non-dominated sorting.
------------------------------------------------------------------------

module RnaDhana_TheMixedStratumIsExactlyTheFlippedStratum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import OrderAstiNasti_TheFourthCornerCannotLiveOverAnEnumerableDecidableInstanceSet
  using (Any ; decAny ; memberToAny)
open import EveryRemainderMemberIsStrictlyDominated using (anyToMember)
open import OneStepCoverageAndDisjointnessOfTheLayer using (Mem)
open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (dec≤ ; decNeg ; filterDec ; StrictlyDominatedBy ; IsParetoMaximal
        ; decIsParetoMaximal ; stratum)
open import FlippingACostCoordinateIsSoundButNotFaithful
  using (Vec ; Dom)
open import RnaDhana_PerCoordinateCapsAreTheHonestVersionAndOneCapIsTheSpecialCase
  using (Caps ; BoundedC ; flipWithCaps ; flipCapsIsSound ; flipCapsReflect)
open import RnaDhana_TheParetoMaximumTransfersToCostCoordinates
  using (MixedStrict ; MixedMaximal ; AllBounded ; boundedAtMember
        ; anyMapBack ; memberMaps)

private
  variable
    A : Type

------------------------------------------------------------------------
-- 1.  The mixed order is decidable, so the mixed layer is computable
------------------------------------------------------------------------

decDom : (ds : List Bool) (v w : Vec ds) → Dec (Dom ds v w)
decDom []           _        _        = yes tt
decDom (true  ∷ ds) (x , xs) (y , ys) with dec≤ x y
... | no ¬p = no (λ z → ¬p (fst z))
... | yes p with decDom ds xs ys
...   | yes q = yes (p , q)
...   | no ¬q = no (λ z → ¬q (snd z))
decDom (false ∷ ds) (x , xs) (y , ys) with dec≤ y x
... | no ¬p = no (λ z → ¬p (fst z))
... | yes p with decDom ds xs ys
...   | yes q = yes (p , q)
...   | no ¬q = no (λ z → ¬q (snd z))

decMixedStrict :
  (ds : List Bool) (u z : Vec ds) → Dec (MixedStrict ds u z)
decMixedStrict ds u z with decDom ds u z
... | no ¬p = no (λ w → ¬p (fst w))
... | yes p with decNeg (decDom ds z u)
...   | yes q = yes (p , q)
...   | no ¬q = no (λ w → ¬q (snd w))

decMixedMaximal :
  (ds : List Bool) (vs : List (Vec ds)) (u : Vec ds)
  → Dec (MixedMaximal ds vs u)
decMixedMaximal ds vs u =
  decNeg (decAny (MixedStrict ds u) (decMixedStrict ds u) vs)

mixedStratum : (ds : List Bool) → List (Vec ds) → List (Vec ds)
mixedStratum ds vs =
  filterDec (MixedMaximal ds vs) (decMixedMaximal ds vs) vs

------------------------------------------------------------------------
-- 2.  Two list lemmas
------------------------------------------------------------------------

filterMapCommutes :
  {B : Type} (f : A → B) (Q : B → Type) (dq : (b : B) → Dec (Q b))
  (xs : List A)
  → filterDec Q dq (map f xs)
    ≡ map f (filterDec (λ a → Q (f a)) (λ a → dq (f a)) xs)
filterMapCommutes f Q dq []       = refl
filterMapCommutes f Q dq (x ∷ xs) with dq (f x)
... | yes _ = cong (f x ∷_) (filterMapCommutes f Q dq xs)
... | no  _ = filterMapCommutes f Q dq xs

filterRespectsOn :
  (P Q : A → Type) (dp : (a : A) → Dec (P a)) (dq : (a : A) → Dec (Q a))
  (xs : List A)
  → ((a : A) → Mem a xs → (P a → Q a) × (Q a → P a))
  → filterDec P dp xs ≡ filterDec Q dq xs
filterRespectsOn P Q dp dq []       iff = refl
filterRespectsOn P Q dp dq (x ∷ xs) iff with dp x | dq x
... | yes _ | yes _ =
  cong (x ∷_) (filterRespectsOn P Q dp dq xs (λ a m → iff a (inr m)))
... | yes p | no ¬q = ⊥.rec (¬q (fst (iff x (inl refl)) p))
... | no ¬p | yes q = ⊥.rec (¬p (snd (iff x (inl refl)) q))
... | no  _ | no  _ =
  filterRespectsOn P Q dp dq xs (λ a m → iff a (inr m))

------------------------------------------------------------------------
-- 3.  Under the caps the two maximalities agree
------------------------------------------------------------------------

mixedMaximalIff :
  (ds : List Bool) (cs : Caps ds) (vs : List (Vec ds))
  → AllBounded ds cs vs
  → (u : Vec ds) → BoundedC ds cs u
  → (MixedMaximal ds vs u
       → IsParetoMaximal (flipWithCaps ds cs u) (map (flipWithCaps ds cs) vs))
  × (IsParetoMaximal (flipWithCaps ds cs u) (map (flipWithCaps ds cs) vs)
       → MixedMaximal ds vs u)
mixedMaximalIff ds cs vs ab u ub = fwd , bwd
  where
    f : Vec ds → List ℕ
    f = flipWithCaps ds cs

    fwd : MixedMaximal ds vs u → IsParetoMaximal (f u) (map f vs)
    fwd mm anyP
      with anyToMember (λ z → StrictlyDominatedBy (f u) (f z)) vs
             (anyMapBack f (StrictlyDominatedBy (f u)) vs anyP)
    ... | (z , memZ , (le , ¬le)) =
      mm (memberToAny (MixedStrict ds u) z vs memZ
           ( flipCapsReflect ds cs u z (boundedAtMember ds cs vs z ab memZ) le
           , (λ dzu → ¬le (flipCapsIsSound ds cs z u dzu))))

    bwd : IsParetoMaximal (f u) (map f vs) → MixedMaximal ds vs u
    bwd pm anyM with anyToMember (MixedStrict ds u) vs anyM
    ... | (z , memZ , (duz , ¬dzu)) =
      pm (memberToAny (StrictlyDominatedBy (f u)) (f z) (map f vs)
           (memberMaps f vs z memZ)
           ( flipCapsIsSound ds cs u z duz
           , (λ le → ¬dzu (flipCapsReflect ds cs z u ub le))))

------------------------------------------------------------------------
-- 4.  …so the layers are the same list
------------------------------------------------------------------------

theMixedStratumIsTheFlippedStratum :
  (ds : List Bool) (cs : Caps ds) (vs : List (Vec ds))
  → AllBounded ds cs vs
  → map (flipWithCaps ds cs) (mixedStratum ds vs)
    ≡ stratum (map (flipWithCaps ds cs) vs)
theMixedStratumIsTheFlippedStratum ds cs vs ab =
    cong (map (flipWithCaps ds cs))
      (filterRespectsOn (MixedMaximal ds vs)
        (λ u → IsParetoMaximal (flipWithCaps ds cs u)
                               (map (flipWithCaps ds cs) vs))
        (decMixedMaximal ds vs)
        (λ u → decIsParetoMaximal (flipWithCaps ds cs u)
                                  (map (flipWithCaps ds cs) vs))
        vs
        (λ a m → mixedMaximalIff ds cs vs ab a (boundedAtMember ds cs vs a ab m)))
  ∙ sym (filterMapCommutes (flipWithCaps ds cs)
          (λ y → IsParetoMaximal y (map (flipWithCaps ds cs) vs))
          (λ y → decIsParetoMaximal y (map (flipWithCaps ds cs) vs))
          vs)

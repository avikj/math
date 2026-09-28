{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NoObservationDepthDeterminesTheNet
--
-- `interactive/IndraNet.hs` (absent from this repository) says of itself that it "exposes only finite
-- observations of a guarded lazy stream" and is "an implementation of
-- the finite/productive bridge, not a claim that arbitrary
-- self-containing universes have been constructed."  Two things follow,
-- and they point opposite ways:
--
--   * the ROOT survives at every depth, so the invariant the shelf is
--     named for is a finite fact and observation reaches it;
--   * the NET is not determined at any depth, so observation never
--     reaches the object.
--
------------------------------------------------------------------------

module NoObservationDepthDeterminesTheNet where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import FiniteIndraWeave using (TotalView ; LocalAction)
open import RootedIndraTotal
  using (RootedView ; rootOf ; viewOf ; reweaveRooted ; reweaveRooted-root)

------------------------------------------------------------------------
-- 1.  The guarded stream the shelf implements
------------------------------------------------------------------------

record Net (Root Jewel : Type₀) : Type₀ where
  coinductive
  field
    hd : RootedView Root Jewel
    tl : Net Root Jewel

open Net public

propagate : {Root Jewel : Type₀}
          → LocalAction Root Jewel → Net Root Jewel → Net Root Jewel
propagate action net .hd = reweaveRooted action (net .hd)
propagate action net .tl = propagate action (net .tl)

-- the observation at a given finite depth
rootAt : {Root Jewel : Type₀} → ℕ → Net Root Jewel → Root
rootAt zero    net = rootOf (net .hd)
rootAt (suc n) net = rootAt n (net .tl)

viewAt : {Root Jewel : Type₀} (n : ℕ) (net : Net Root Jewel)
       → TotalView Root Jewel
viewAt zero    net = viewOf (net .hd)
viewAt (suc n) net = viewAt n (net .tl)

------------------------------------------------------------------------
-- 2.  The root survives at every depth
--
-- `RootedIndraTotal.reweaveRooted-root` is the base case; the induction
-- carries it along the whole stream.
------------------------------------------------------------------------

propagatePreservesRootAtEveryDepth :
  {Root Jewel : Type₀} (action : LocalAction Root Jewel)
  (n : ℕ) (net : Net Root Jewel)
  → rootAt n (propagate action net) ≡ rootAt n net
propagatePreservesRootAtEveryDepth action zero    net =
  reweaveRooted-root action (net .hd)
propagatePreservesRootAtEveryDepth action (suc n) net =
  propagatePreservesRootAtEveryDepth action n (net .tl)

------------------------------------------------------------------------
-- 3.  No depth determines the net
--
-- `delay d v net` shows the fixed view `v` for the first `d`
-- observations and then `net`.  Two nets so delayed agree at every depth
-- BELOW `d` — expressed as `suc k + n`, so the bound is structural and
-- no order relation is needed — and at depth `d` they show their own
-- heads, which may differ.
------------------------------------------------------------------------

delay : {Root Jewel : Type₀}
      → ℕ → RootedView Root Jewel → Net Root Jewel → Net Root Jewel
delay zero    _ net = net
delay (suc d) v net .hd = v
delay (suc d) v net .tl = delay d v net

-- below the delay: agreement, whatever the delayed nets are
agreeBelowTheDelay :
  {Root Jewel : Type₀} (k n : ℕ) (v : RootedView Root Jewel)
  (m m' : Net Root Jewel)
  → viewAt k (delay (suc (k + n)) v m) ≡ viewAt k (delay (suc (k + n)) v m')
agreeBelowTheDelay zero    n v m m' = refl
agreeBelowTheDelay (suc k) n v m m' = agreeBelowTheDelay k n v m m'

-- at the delay: the net's own head is what is seen
atTheDelayTheNetShows :
  {Root Jewel : Type₀} (d : ℕ) (v : RootedView Root Jewel)
  (m : Net Root Jewel)
  → viewAt d (delay d v m) ≡ viewOf (m .hd)
atTheDelayTheNetShows zero    v m = refl
atTheDelayTheNetShows (suc d) v m = atTheDelayTheNetShows d v m

------------------------------------------------------------------------
-- 4.  A concrete pair, so §3 is inhabited and not merely schematic
------------------------------------------------------------------------

private
  U : Type₀
  U = Unit

  constNet : ℕ → Net U ℕ
  constNet j .hd = tt , (λ _ _ → j)
  constNet j .tl = constNet j

  headJewel : Net U ℕ → ℕ
  headJewel net = viewOf (net .hd) tt tt

  0≢1 : ¬ (0 ≡ 1)
  0≢1 = znots

theNetIsNotDeterminedAtAnyDepth :
  (k n : ℕ) →
    (viewAt k (delay (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 0))
   ≡ viewAt k (delay (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 1)))
  × (¬ (viewAt (suc (k + n)) (delay (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 0)) tt tt
      ≡ viewAt (suc (k + n)) (delay (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 1)) tt tt))
theNetIsNotDeterminedAtAnyDepth k n =
    agreeBelowTheDelay k n (tt , (λ _ _ → 0)) (constNet 0) (constNet 1)
  , λ p → 0≢1
      ( sym (cong (λ f → f tt tt)
              (atTheDelayTheNetShows (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 0)))
      ∙ p
      ∙ cong (λ f → f tt tt)
              (atTheDelayTheNetShows (suc (k + n)) (tt , (λ _ _ → 0)) (constNet 1)) )

------------------------------------------------------------------------
-- 5.  The two halves, side by side
--
-- §2: the ROOT is reached by observation — at every depth, and the base
-- case is `RootedIndraTotal`'s own `refl`.
-- §3–§4: the NET is not — for every depth there are two nets agreeing
-- everywhere below it and differing at it.
--
-- Which is the exact content of the shelf's disclaimer: a finite/
-- productive bridge gives you the invariants and not the object.
------------------------------------------------------------------------

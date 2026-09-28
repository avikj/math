{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RootedIndraTotal
--
-- Delta 25's exact finite bridge: a rooted view is a jewel together with
-- the total view it carries.  This is a dependent total space.
------------------------------------------------------------------------

module RootedIndraTotal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import FiniteIndraWeave
  using (TotalView ; LocalAction ; reweave)

RootedView : (Root Jewel : Type₀) → Type₀
RootedView Root Jewel = Σ[ root ∈ Root ] TotalView Root Jewel

rootOf : {Root Jewel : Type₀} → RootedView Root Jewel → Root
rootOf (root , view) = root

viewOf : {Root Jewel : Type₀} → RootedView Root Jewel → TotalView Root Jewel
viewOf (root , view) = view

-- The projection and its fibre are definitional: the fibre over root is the
-- complete rooted-view space carried at that root.
rootProjection : {Root Jewel : Type₀} → RootedView Root Jewel → Root
rootProjection = rootOf

rootFiber : {Root Jewel : Type₀} → Root → Type₀
rootFiber {Root = Root} {Jewel = Jewel} root = TotalView Root Jewel

rooted : {Root Jewel : Type₀} (root : Root)
       → TotalView Root Jewel → RootedView Root Jewel
rooted root view = root , view

rooted-root : {Root Jewel : Type₀} (root : Root)
            (view : TotalView Root Jewel)
            → rootOf (rooted root view) ≡ root
rooted-root root view = refl

rooted-view : {Root Jewel : Type₀} (root : Root)
            (view : TotalView Root Jewel)
            → viewOf (rooted root view) ≡ view
rooted-view root view = refl

-- A local warranted action reweaves every rooted view while preserving the
-- distinguished jewel.  The root is not silently transported or collapsed.
reweaveRooted : {Root Jewel : Type₀}
              → LocalAction Root Jewel
              → RootedView Root Jewel → RootedView Root Jewel
reweaveRooted action (root , view) = root , reweave action view

reweaveRooted-root : {Root Jewel : Type₀}
                   (action : LocalAction Root Jewel)
                   (rv : RootedView Root Jewel)
                   → rootOf (reweaveRooted action rv) ≡ rootOf rv
reweaveRooted-root action (root , view) = refl

reweaveRooted-view : {Root Jewel : Type₀}
                   (action : LocalAction Root Jewel)
                   (rv : RootedView Root Jewel)
                   → viewOf (reweaveRooted action rv)
                     ≡ reweave action (viewOf rv)
reweaveRooted-view action (root , view) = refl

-- The finite bridge is deliberately weaker than a global Net theorem: it
-- only states that the action is available at every root in the total space.
reweave-all-roots : {Root Jewel : Type₀}
                  (action : LocalAction Root Jewel)
                  (view : TotalView Root Jewel)
                  → (root : Root)
                  → viewOf (reweaveRooted action (rooted root view))
                    ≡ reweave action view
reweave-all-roots action view root = refl

------------------------------------------------------------------------
-- `reweaveRooted-root` above is the ONE-STEP law, and it is `refl`.  It
-- is carried along the stream this module deliberately does not
-- build, in
-- `NoObservationDepthDeterminesTheNet`:
--
--   propagatePreservesRootAtEveryDepth :
--     (action) (n) (net) → rootAt n (propagate action net) ≡ rootAt n net
--
-- whose base case is exactly `reweaveRooted-root`.  The same module
-- proves the opposite half for the object rather than the invariant:
-- for EVERY depth there are two nets agreeing at every depth below it
-- and differing at it, so no finite observation depth determines the
-- net.  That is `interactive/IndraNet.hs` (absent from this repository)'s own disclaimer, checked.
------------------------------------------------------------------------

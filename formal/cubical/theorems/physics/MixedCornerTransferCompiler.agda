{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MixedCornerTransferCompiler
--
-- Factory IV's proof-relevant mixed-corner compiler.  A state contains a
-- finite radius index i (physical radius 1+i) and an excess-charge bit.  The
-- well-founded rank kappa = 2*i + bit admits both fixed-radius purification
-- and radius descent that temporarily creates excess.
--
-- Edges retain a finite bound, strict center advance, and strict rank descent.
-- The compiler transports any supplied cofinal seed along a supplied fabric
-- to (radius index 0, exact charge).
------------------------------------------------------------------------

module MixedCornerTransferCompiler where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.FinData
  using (Fin ; toℕ) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Nat using (ℕ ; _+_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; <-trans)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

------------------------------------------------------------------------
-- 1. Mixed-corner states and the single ranking function
------------------------------------------------------------------------

record CornerState (n : ℕ) : Type₀ where
  constructor corner
  field
    radiusIndex : Fin n
    excess : Bool

open CornerState public

bit : Bool → ℕ
bit false = 0
bit true  = 1

κ : {n : ℕ} → CornerState n → ℕ
κ state = bit (excess state) + (toℕ (radiusIndex state) + toℕ (radiusIndex state))

radius : {n : ℕ} → CornerState n → ℕ
radius state = 1 + toℕ (radiusIndex state)

target : {n : ℕ} → CornerState (Nat.suc n)
target = corner fzero false

-- Two finite controls for the mixed rank.  They certify only the ranking
-- geometry, not the existence of an arithmetic transfer edge.
exact₀ excess₀ : CornerState 1
exact₀ = corner fzero false
excess₀ = corner fzero true

exact₁ excess₀′ : CornerState 2
exact₁ = corner (fsuc fzero) false
excess₀′ = corner fzero true

exact-radius-purification-decreases :
  κ exact₀ < κ excess₀
exact-radius-purification-decreases = 0 , refl

radius-descent-may-create-excess :
  κ excess₀′ < κ exact₁
radius-descent-may-create-excess = 0 , refl

------------------------------------------------------------------------
-- 2. Bounded proof-relevant edges and cofinality transport
------------------------------------------------------------------------

module _ {n : ℕ} (Witness : ℕ → CornerState n → Type₀) where

  Cofinal : CornerState n → Type₀
  Cofinal state =
    (threshold : ℕ) →
      Σ[ center ∈ ℕ ] (threshold < center) × Witness center state

  record BoundedRankedEdge (source target : CornerState n) : Type₀ where
    field
      bound : ℕ → ℕ
      rank-decreases : κ target < κ source
      advances : (center : ℕ) → Witness center source
        → Σ[ later ∈ ℕ ]
            (center < later) × (later ≤ bound center) × Witness later target

  open BoundedRankedEdge public

  edge-transports-cofinal : {source target : CornerState n}
    → BoundedRankedEdge source target → Cofinal source → Cofinal target
  edge-transports-cofinal edge seed threshold =
    later , <-trans threshold<center center<later , targetWitness
    where
    sourceResult = seed threshold
    center = fst sourceResult
    threshold<center = fst (snd sourceResult)
    sourceWitness = snd (snd sourceResult)

    moved = advances edge center sourceWitness
    later = fst moved
    center<later = fst (snd moved)
    targetWitness = snd (snd (snd moved))

  data RankedPath : CornerState n → CornerState n → Type₀ where
    finish : {state goal : CornerState n} → state ≡ goal → RankedPath state goal
    follow : {source middle goal : CornerState n}
      → BoundedRankedEdge source middle
      → RankedPath middle goal → RankedPath source goal

  path-transports-cofinal : {source goal : CornerState n}
    → RankedPath source goal → Cofinal source → Cofinal goal
  path-transports-cofinal (finish equality) seed =
    subst Cofinal equality seed
  path-transports-cofinal (follow edge rest) seed =
    path-transports-cofinal rest (edge-transports-cofinal edge seed)

  CofinalSeed : Type₀
  CofinalSeed = Σ[ state ∈ CornerState n ] Cofinal state

  FabricTo : CornerState n → Type₀
  FabricTo goal = (state : CornerState n) → RankedPath state goal

  compile-mixed-corner : (goal : CornerState n)
    → CofinalSeed → FabricTo goal → Cofinal goal
  compile-mixed-corner goal (state , seed) fabric =
    path-transports-cofinal (fabric state) seed

-- Factory IV target specialization: index 0 and exact charge.  The type
-- requires n+1 states so that the finite radius band is nonempty.
compile-to-exact-radius-one : {n : ℕ}
  (Witness : ℕ → CornerState (Nat.suc n) → Type₀)
  → CofinalSeed Witness
  → FabricTo Witness (target {n})
  → Cofinal Witness (target {n})
compile-to-exact-radius-one {n} Witness seed fabric =
  compile-mixed-corner Witness (target {n}) seed fabric

------------------------------------------------------------------------
-- 3. The two Factory IV seed interfaces over the 123-radius band
------------------------------------------------------------------------

-- These are deliberately interfaces, not arithmetic theorems.
module Finite123Seeds
  (Witness : ℕ → CornerState 123 → Type₀) where

  exactTarget : CornerState 123
  exactTarget = corner fzero false

  excessTarget : CornerState 123
  excessTarget = corner fzero true

  -- A recurrent exact-charge column at some radius 1+i, with i in Fin 123.
  ExactChargeRadiusSeed : Type₀
  ExactChargeRadiusSeed =
    Σ[ i ∈ Fin 123 ] Cofinal Witness (corner i false)

  -- Bounded-gap input alone does not name which exact radius recurs, so its
  -- consumer must cover every exact state in the finite band.
  ExactStateFabric : Type₀
  ExactStateFabric =
    (i : Fin 123) → RankedPath Witness (corner i false) exactTarget

  compile-exact-radius-seed :
    ExactChargeRadiusSeed → ExactStateFabric
    → Cofinal Witness exactTarget
  compile-exact-radius-seed (i , seed) fabric =
    path-transports-cofinal Witness (fabric i) seed

  -- The radius-zero Chen envelope says recurrence lies either already in the
  -- exact target or in its one-bit excess companion.  It intentionally keeps
  -- the disjunction proof-relevant.
  RadiusZeroChenEnvelopeSeed : Type₀
  RadiusZeroChenEnvelopeSeed =
    Cofinal Witness exactTarget ⊎ Cofinal Witness excessTarget

  PurificationPath : Type₀
  PurificationPath =
    RankedPath Witness excessTarget exactTarget

  -- Unlike the exact-radius seed compiler, this needs no paths from all 123
  -- radii: the exact branch returns immediately and only the excess branch
  -- consumes the supplied purification path.
  compile-chen-envelope :
    RadiusZeroChenEnvelopeSeed → PurificationPath
    → Cofinal Witness exactTarget
  compile-chen-envelope (inl targetSeed) purification = targetSeed
  compile-chen-envelope (inr excessSeed) purification =
    path-transports-cofinal Witness purification excessSeed

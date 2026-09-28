{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ActionRefinement
--
-- The exact return of a scalar-observer collision.  Suppose `q` is the
-- installed observation and `action` is the certified next action.  Their
-- product
--
--                         x ↦ (q x , action x)
--
-- retains the old observation and makes the action descend.  It is minimal
-- in the precise refinement preorder: every other observer through which
-- both coordinates descend also determines the product.  If one q-fibre
-- contains two different actions, the product is strictly finer than q.
--
-- The random stimulus was batch-02 anchor #2, an exact byte interval in the
-- retired `coupled_encounter_engine.py` (absent from this repository).  It landed on `meet_smith`, where a
-- scalar residual fibre containing two certified action kinds causes the
-- runtime to add an action-origin sensor.  The bytes nominate this theorem;
-- they are not evidence for it.  Certification is the checked term below.
--
-- This is the standard universal property of a product, expressed in the
-- Natural Machine's existing `Descent.Descends` language.  What it adds
-- locally is the checked bridge from the runtime's collision-triggered
-- sensor revision to the formal core.
------------------------------------------------------------------------

module ActionRefinement where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Bool using (Bool ; false ; true ; false≢true)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_)

import StructuredDefect as SD

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- Refinement as descent
------------------------------------------------------------------------

-- `fine` refines `coarse` exactly when the coarse reading can be decoded
-- from the fine one.  This is an alias for the core descent object, not a
-- second notion of observational order.
Refines : {X : Type ℓ} {Fine Coarse : Type ℓ'}
        → (fine : X → Fine) (coarse : X → Coarse) → Type _
Refines fine coarse = SD.Descent.Descends fine coarse

-- A collision is not a count.  It retains the two states, their common old
-- observation, and the proof that the certified actions differ.
ActionCollision : {X : Type ℓ} {Y Action : Type ℓ'}
                → (q : X → Y) (action : X → Action) → Type _
ActionCollision {X = X} q action =
  Σ[ x ∈ X ] Σ[ x' ∈ X ]
    (q x ≡ q x') × (¬ (action x ≡ action x'))

module ProductRefinement
  {X : Type ℓ} {Y Action : Type ℓ'}
  (q : X → Y) (action : X → Action) where

  joint : X → Y × Action
  joint x = q x , action x

  -- The new observer conservatively retains both old coordinates.
  joint-refines-observation : Refines joint q
  joint-refines-observation = fst , λ _ → refl

  joint-refines-action : Refines joint action
  joint-refines-action = snd , λ _ → refl

  -- Any observer carrying the joint necessarily carries each coordinate.
  refines-joint→refines-observation :
    {R : Type ℓ'} (r : X → R) → Refines r joint → Refines r q
  refines-joint→refines-observation r (decode , replay) =
    (fst ∘ decode) , λ x → cong fst (replay x)

  refines-joint→refines-action :
    {R : Type ℓ'} (r : X → R) → Refines r joint → Refines r action
  refines-joint→refines-action r (decode , replay) =
    (snd ∘ decode) , λ x → cong snd (replay x)

  -- The product is minimal among common refinements.  No surjectivity,
  -- choice, finiteness, or scalar cost is needed.
  common-refinement→refines-joint :
    {R : Type ℓ'} (r : X → R)
    → Refines r q → Refines r action → Refines r joint
  common-refinement→refines-joint r (readQ , replayQ) (readA , replayA) =
    (λ z → readQ z , readA z) , λ x → ΣPathP (replayQ x , replayA x)

  -- A witnessed collision refutes every attempted action decoder from q.
  collision-obstructs-action-descent :
    ActionCollision q action → SD.Reopens q action
  collision-obstructs-action-descent =
    SD.separatedPair→reopens q action

  -- It also refutes a decoder of the whole product from q: projection to
  -- the action coordinate would supply the already-impossible decoder.
  collision-obstructs-joint-descent :
    ActionCollision q action → SD.Reopens q joint
  collision-obstructs-joint-descent collision jointFromQ =
    collision-obstructs-action-descent collision
      (refines-joint→refines-action q jointFromQ)

  -- The exact revision certificate: the product retains q, while q cannot
  -- recover the product.  This is strict refinement without cardinalities.
  collision-forces-strict-refinement :
    ActionCollision q action
    → Refines joint q × SD.Reopens q joint
  collision-forces-strict-refinement collision =
    joint-refines-observation , collision-obstructs-joint-descent collision

------------------------------------------------------------------------
-- Non-vacuity: a constant scalar view cannot carry a Boolean action.
------------------------------------------------------------------------

constantView : Bool → Unit
constantView _ = tt

booleanAction : Bool → Bool
booleanAction b = b

constant-action-collision : ActionCollision constantView booleanAction
constant-action-collision = false , true , refl , false≢true

open ProductRefinement constantView booleanAction

constant-view-strictly-reopens :
  Refines joint constantView × SD.Reopens constantView joint
constant-view-strictly-reopens =
  collision-forces-strict-refinement constant-action-collision

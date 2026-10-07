{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- SpawnStatus — the FULL hyperactive machine (MACHINE.md): cells that
-- both read dependencies (aggregation) and spawn children, with the
-- one-step diamond, hence equal-length / geodesic by RandomDescent.
--
-- It merges two verified halves:
--   * Spawn's batch algebra (ITables.writes / writes-comm) for the
--     pending table — disjoint-domain batches commute, giving write/
--     write disjointness of two fires via the prefix-free invariant Inv
--     + child injectivity;
--   * StatusMachine's reads / read-safety for the out table — an
--     available step reads only done slots, so a competing now-available
--     step (writing done only at its own pending site) leaves the
--     reader's deps untouched (invariant Fresh).
--
-- Carrier = states with BOTH invariants.  This is the step-optimality
-- theorem for the real evaluator: judgments that decompose (spawn) and
-- wait on their children (aggregate) still reduce in min steps under any
-- schedule.
------------------------------------------------------------------------

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ3)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; isOfHLevelMaybe ; ¬nothing≡just)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete)

open import Diamond using (module RandomDescent)
import DecTable

module SpawnStatus
  (Env Cell Out : Type) (isSetCell : isSet Cell) (isSetOut : isSet Out)
  (Addr : Type) (_≟_ : Discrete Addr)
  (child : ℕ → Addr → Addr)
  (Ext : Addr → Addr → Type)
  (depth : Addr → ℕ)
  (child-inj : {k l : ℕ} {α β : Addr} → child k α ≡ child l β → (k ≡ l) × (α ≡ β))
  (child-ext : (k : ℕ) (α : Addr) → Ext (child k α) α)
  (ext-trans : {γ β α : Addr} → Ext γ β → Ext β α → Ext γ α)
  (ext-of-child : {k : ℕ} {α γ : Addr} → Ext (child k α) γ → (γ ≡ α) ⊎ Ext α γ)
  (child-depth : (k : ℕ) (α : Addr) → depth (child k α) ≡ suc (depth α))
  (ext-depth : {β α : Addr} → Ext β α → depth α < depth β)
  (deps : Cell → List Addr)
  (rule : Env → Cell → List Out → Out × List Cell)
  where

  open DecTable Addr _≟_

  record St : Type where
    constructor st
    field
      env     : Env
      pending : Addr → Maybe Cell
      out     : Addr → Maybe Out
  open St public

  St-path : {s t : St} → env s ≡ env t → pending s ≡ pending t → out s ≡ out t → s ≡ t
  St-path pe pp po i = st (pe i) (pp i) (po i)

  -- reads: aggregate the out-verdicts at a dep list (plain fold).
  _»_ : {X Y : Type} → Maybe X → (X → Maybe Y) → Maybe Y
  nothing » _ = nothing
  just x  » f = f x

  reads : St → List Addr → Maybe (List Out)
  reads s []       = just []
  reads s (γ ∷ γs) = out s γ » λ v → reads s γs » λ vs → just (v ∷ vs)

  record Active (s : St) : Type where
    constructor act
    field
      addr     : Addr
      theCell  : Cell
      here     : pending s addr ≡ just theCell
      vals     : List Out
      reads-ok : reads s (deps theCell) ≡ just vals
  open Active public

  verdict : (s : St) (a : Active s) → Out
  verdict s a = fst (rule (env s) (theCell a) (vals a))

  kids : (s : St) (a : Active s) → List Cell
  kids s a = snd (rule (env s) (theCell a) (vals a))

  -- children written at child 0 α, child 1 α, … as a pending batch; the
  -- site itself vacated.  Expressed as an ITables `writes` batch so
  -- Spawn.writes-comm applies to the pending side.
  kidBatch : (α : Addr) → ℕ → List Cell → List (Addr × Maybe Cell)
  kidBatch α k []       = []
  kidBatch α k (c ∷ cs) = (child k α , just c) ∷ kidBatch α (suc k) cs

  pendingBatch : (α : Addr) → List Cell → List (Addr × Maybe Cell)
  pendingBatch α cs = (α , nothing) ∷ kidBatch α 0 cs

  fire : (s : St) → Active s → St
  fire s a =
    st (env s)
       (writes (pendingBatch (addr a) (kids s a)) (pending s))
       (update (addr a) (just (verdict s a)) (out s))

  Step : St → St → Type
  Step s t = Σ[ a ∈ Active s ] (fire s a ≡ t)

  -- The two invariants.
  Fresh : St → Type
  Fresh s = (x : Addr) (c : Cell) → pending s x ≡ just c → out s x ≡ nothing

  Inv : St → Type
  Inv s = (α : Addr) {c : Cell} → pending s α ≡ just c
        → (β : Addr) → Ext β α → pending s β ≡ nothing

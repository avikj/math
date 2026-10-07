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

  ----------------------------------------------------------------------
  -- Maybe/Cell helpers.
  ----------------------------------------------------------------------
  justInj : {x y : Cell} → just x ≡ just y → x ≡ y
  justInj {x} p = cong unwrap p
    where
    unwrap : Maybe Cell → Cell
    unwrap nothing  = x
    unwrap (just c) = c

  isPropFresh : (s : St) → isProp (Fresh s)
  isPropFresh s = isPropΠ3 (λ x c _ → isOfHLevelMaybe 0 isSetOut (out s x) nothing)

  ¬symA : {x y : Addr} → ¬ x ≡ y → ¬ y ≡ x
  ¬symA np q = np (sym q)

  headJust : {X Y : Type} (m : Maybe X) (k : X → Maybe Y) (y : Y)
    → (m » k) ≡ just y → Σ[ x ∈ X ] m ≡ just x
  headJust nothing  k y h = Empty.rec (¬nothing≡just h)
  headJust (just x) k y h = x , refl

  tailJust : {X Y : Type} (m : Maybe X) (g : X → Y) (y : Y)
    → (m » (λ x → just (g x))) ≡ just y → Σ[ x ∈ X ] m ≡ just x
  tailJust nothing  g y h = Empty.rec (¬nothing≡just h)
  tailJust (just x) g y h = x , refl

  ----------------------------------------------------------------------
  -- Read-safety (out side): firing at β (out-write only at β, empty
  -- there) leaves every resolved dep's out-value untouched.
  ----------------------------------------------------------------------
  AllAgree : (s' s : St) → List Addr → Type
  AllAgree s' s []       = Unit*
  AllAgree s' s (γ ∷ γs) = (out s' γ ≡ out s γ) × AllAgree s' s γs

  reads-stable : (s' s : St) (γs : List Addr)
    → AllAgree s' s γs → reads s' γs ≡ reads s γs
  reads-stable s' s []       _          = refl
  reads-stable s' s (γ ∷ γs) (oγ , rest) =
    cong (_» (λ v → reads s' γs » λ vs → just (v ∷ vs))) oγ
    ∙ cong (out s γ »_)
        (funExt λ v → cong (_» (λ vs → just (v ∷ vs))) (reads-stable s' s γs rest))

  agree : (s : St) (b : Active s) → out s (addr b) ≡ nothing
    → (γs : List Addr) (vs : List Out) → reads s γs ≡ just vs
    → AllAgree (fire s b) s γs
  agree s b obn []       vs h = tt*
  agree s b obn (γ ∷ γs) vs h = headAgree , agree s b obn γs ws eqr
    where
    k : Out → Maybe (List Out)
    k v = reads s γs » λ ws → just (v ∷ ws)
    hv : Σ[ v ∈ Out ] out s γ ≡ just v
    hv = headJust (out s γ) k vs h
    v  = fst hv
    oγ = snd hv
    h' : (reads s γs » λ ws → just (v ∷ ws)) ≡ just vs
    h' = subst (λ m → (m » k) ≡ just vs) oγ h
    hw : Σ[ ws ∈ List Out ] reads s γs ≡ just ws
    hw = tailJust (reads s γs) (v ∷_) vs h'
    ws  = fst hw
    eqr = snd hw
    γ≢β : ¬ γ ≡ addr b
    γ≢β q = ¬nothing≡just (sym (cong (out s) q ∙ obn) ∙ oγ)
    headAgree : out (fire s b) γ ≡ out s γ
    headAgree = update-miss (addr b) γ (just (verdict s b)) (out s) (λ q → γ≢β (sym q))

  ----------------------------------------------------------------------
  -- Address domain of a pending batch (pending side).
  ----------------------------------------------------------------------
  kid-cases : (α : Addr) (cs : List Cell) (k : ℕ) (x : Addr)
    → ¬ (find (kidBatch α k cs) x ≡ nothing) → Σ[ j ∈ ℕ ] x ≡ child j α
  kid-cases α []       k x h = Empty.rec (h refl)
  kid-cases α (c ∷ cs) k x h = go (child k α ≟ x)
    where
    go : Dec (child k α ≡ x) → Σ[ j ∈ ℕ ] x ≡ child j α
    go (yes p) = k , sym p
    go (no ¬p) = kid-cases α cs (suc k) x
      (λ e → h (find-miss (child k α) x (just c) (kidBatch α (suc k) cs) ¬p ∙ e))

  batch-cases : (α : Addr) (cs : List Cell) (x : Addr)
    → ¬ (find (pendingBatch α cs) x ≡ nothing) → (x ≡ α) ⊎ (Σ[ j ∈ ℕ ] x ≡ child j α)
  batch-cases α cs x h = go (α ≟ x)
    where
    go : Dec (α ≡ x) → (x ≡ α) ⊎ (Σ[ j ∈ ℕ ] x ≡ child j α)
    go (yes p) = inl (sym p)
    go (no ¬p) = inr (kid-cases α cs 0 x
      (λ e → h (find-miss α x nothing (kidBatch α 0 cs) ¬p ∙ e)))

  kid-nothing : (α : Addr) (cs : List Cell) (k : ℕ) (x : Addr)
    → (∀ j → ¬ x ≡ child j α) → find (kidBatch α k cs) x ≡ nothing
  kid-nothing α []       k x _  = refl
  kid-nothing α (c ∷ cs) k x hc =
    find-miss (child k α) x (just c) (kidBatch α (suc k) cs) (λ q → hc k (sym q))
    ∙ kid-nothing α cs (suc k) x hc

  batch-nothing : (α : Addr) (cs : List Cell) (x : Addr)
    → ¬ x ≡ α → (∀ j → ¬ x ≡ child j α) → find (pendingBatch α cs) x ≡ nothing
  batch-nothing α cs x ¬xα hc =
    find-miss α x nothing (kidBatch α 0 cs) (¬symA ¬xα) ∙ kid-nothing α cs 0 x hc

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Spawn — the machine with cell-creating rules, and its diamond.
--
-- Extends Diamond.agda's consuming machine: a rule now returns a
-- verdict AND a list of child cells; firing at address α consumes α,
-- writes the verdict at α, and writes child k at (child k α).  All
-- writes of a step are determined by its site — freshness by address,
-- never by allocation order, which is what keeps the diamond.
--
-- The invariant (prefix-free occupancy): proper extensions of an
-- occupied address are vacant.  Preserved by every step; under it,
-- distinct sites have pairwise disjoint write sets, and the one-step
-- diamond follows from pointwise commutation of disjoint batches.
--
-- The address structure is abstract here; the axioms are exactly the
-- facts used (reviewed on the page this session):
--   child-inj   children of distinct parents are distinct
--   child-ext   a child properly extends its parent
--   ext-child   extending a child extends the parent
--   ext-irrefl  nothing properly extends itself
--   ext-of-child  what a child extends is the parent or beyond it
-- ListAddr.agda instantiates them for Addr = List ℕ, child = _∷_,
-- Ext = proper suffix.
------------------------------------------------------------------------

module Spawn where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; isOfHLevelMaybe)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete)

open import Diamond using (module RandomDescent)

------------------------------------------------------------------------
-- §1  Tables over an arbitrary discrete index.
------------------------------------------------------------------------

module ITables (I : Type) (_≟_ : Discrete I) {A : Type} where

  update : I → A → (I → A) → (I → A)
  update i v f k with i ≟ k
  ... | yes _ = v
  ... | no  _ = f k

  update-at : (i : I) (v : A) (f : I → A) → update i v f i ≡ v
  update-at i v f with i ≟ i
  ... | yes _ = refl
  ... | no ¬p = Empty.rec (¬p refl)

  update-elsewhere : (i k : I) (v : A) (f : I → A) → ¬ i ≡ k → update i v f k ≡ f k
  update-elsewhere i k v f ¬p with i ≟ k
  ... | yes p = Empty.rec (¬p p)
  ... | no  _ = refl

  -- A batch of writes, applied right to left (later entries deeper).
  writes : List (I × A) → (I → A) → (I → A)
  writes []             f = f
  writes ((i , v) ∷ ws) f = update i v (writes ws f)

  -- Membership of an index in a batch's domain, as a decidable lookup.
  find : List (I × A) → I → Maybe A
  find []             k = nothing
  find ((i , v) ∷ ws) k with i ≟ k
  ... | yes _ = just v
  ... | no  _ = find ws k

  -- The batch's pointwise value is its lookup, else the base.
  writes-char : (ws : List (I × A)) (f : I → A) (k : I)
    → ((find ws k ≡ nothing) × (writes ws f k ≡ f k))
    ⊎ (Σ[ v ∈ A ] (find ws k ≡ just v) × (writes ws f k ≡ v))
  writes-char [] f k = inl (refl , refl)
  writes-char ((i , v) ∷ ws) f k with i ≟ k
  ... | yes _ = inr (v , refl , refl)
  ... | no  _ = writes-char ws f k

  -- Two batches whose domains are disjoint at every index commute.
  writes-comm : (ws vs : List (I × A)) (f : I → A)
    → ((k : I) → (find ws k ≡ nothing) ⊎ (find vs k ≡ nothing))
    → writes ws (writes vs f) ≡ writes vs (writes ws f)
  writes-comm ws vs f disj = funExt point
    where
    point : (k : I) → writes ws (writes vs f) k ≡ writes vs (writes ws f) k
    point k with writes-char ws (writes vs f) k | writes-char vs (writes ws f) k
    point k | inl (wn , we) | inl (vn , ve) =
      we ∙ lemma ∙ sym ve
      where
      lemma : writes vs f k ≡ writes ws f k
      lemma with writes-char vs f k | writes-char ws f k
      ... | inl (_ , e₁) | inl (_ , e₂) = e₁ ∙ sym e₂
      ... | inl (_ , e₁) | inr (v , fv , e₂) =
        Empty.rec (nothing≢justA (sym wn ∙ fv))
      ... | inr (v , fv , e₁) | inl (_ , e₂) =
        Empty.rec (nothing≢justA (sym vn ∙ fv))
      ... | inr (v , fv , e₁) | inr (w , fw , e₂) =
        Empty.rec (nothing≢justA (sym wn ∙ fw))
    point k | inl (wn , we) | inr (v , fv , ve) =
      we ∙ lemma ∙ sym ve
      where
      lemma : writes vs f k ≡ v
      lemma with writes-char vs f k
      ... | inl (vn , _) = Empty.rec (nothing≢justA (sym vn ∙ fv))
      ... | inr (w , fw , e) = e ∙ justInjA (sym fw ∙ fv)
    point k | inr (v , fv , ve) | inl (vn , e) =
      ve ∙ lemma ∙ sym e
      where
      lemma : v ≡ writes ws f k
      lemma with writes-char ws f k
      ... | inl (wn , _) = Empty.rec (nothing≢justA (sym wn ∙ fv))
      ... | inr (w , fw , e') = justInjA (sym fv ∙ fw) ∙ sym e'
    point k | inr (v , fv , _) | inr (w , fw , _) with disj k
    ... | inl n = Empty.rec (nothing≢justA (sym n ∙ fv))
    ... | inr n = Empty.rec (nothing≢justA (sym n ∙ fw))

  -- Maybe discrimination, local and name-independent.
  justInjA : {x y : A} {d : A} → just x ≡ just y → x ≡ y
  justInjA {x} p = cong unwrap p
    where
    unwrap : Maybe A → A
    unwrap nothing  = x
    unwrap (just a) = a

  data Unit' : Type where tt' : Unit'

  nothing≢justA : {x : A} → nothing ≡ just x → ⊥
  nothing≢justA p = subst discr p tt'
    where
    discr : Maybe A → Type
    discr nothing  = Unit'
    discr (just _) = ⊥

------------------------------------------------------------------------
-- §2  The spawning machine over an abstract address structure.
------------------------------------------------------------------------

module SpawnMachine
  (Env Cell Out : Type) (isSetCell : isSet Cell)
  (Addr : Type) (_≟_ : Discrete Addr)
  (child : ℕ → Addr → Addr)
  (Ext : Addr → Addr → Type)                      -- Ext β α : β properly extends α
  (depth : Addr → ℕ)
  -- child is injective in BOTH arguments (k∷α = l∷β ⟺ k≡l ∧ α≡β):
  (child-inj : {k l : ℕ} {α β : Addr} → child k α ≡ child l β → (k ≡ l) × (α ≡ β))
  -- a child properly extends its parent:
  (child-ext : (k : ℕ) (α : Addr) → Ext (child k α) α)
  -- Ext is transitive:
  (ext-trans : {γ β α : Addr} → Ext γ β → Ext β α → Ext γ α)
  -- what a child extends is the parent or something the parent extends:
  (ext-of-child : {k : ℕ} {α γ : Addr} → Ext (child k α) γ → (γ ≡ α) ⊎ Ext α γ)
  -- well-foundedness: a child is one deeper, and extension strictly deepens.
  -- (gives ext-irreflexivity and "no sibling extends a sibling" for free.)
  (child-depth : (k : ℕ) (α : Addr) → depth (child k α) ≡ suc (depth α))
  (ext-depth : {β α : Addr} → Ext β α → depth α < depth β)
  (rule : Env → Cell → Out × List Cell)
  where

  open ITables Addr _≟_

  record St : Type where
    constructor st
    field
      env     : Env
      pending : Addr → Maybe Cell
      out     : Addr → Maybe Out
  open St public

  St-path : {s t : St} → env s ≡ env t → pending s ≡ pending t → out s ≡ out t → s ≡ t
  St-path pe pp po i = st (pe i) (pp i) (po i)

  -- The write batch of a fire at α with children cs: vacate α, place kids.
  kidWrites : ℕ → Addr → List Cell → List (Addr × Maybe Cell)
  kidWrites k α []       = []
  kidWrites k α (c ∷ cs) = (child k α , just c) ∷ kidWrites (suc k) α cs

  pendingBatch : Addr → List Cell → List (Addr × Maybe Cell)
  pendingBatch α cs = (α , nothing) ∷ kidWrites 0 α cs

  Active : St → Type
  Active s = Σ[ ic ∈ Addr × Cell ] (pending s (fst ic) ≡ just (snd ic))

  site : {s : St} → Active s → Addr
  site a = fst (fst a)

  cell : {s : St} → Active s → Cell
  cell a = snd (fst a)

  verdict : (s : St) {a : Active s} → Active s → Out
  verdict s a = fst (rule (env s) (cell {s} a))

  kids : (s : St) → Active s → List Cell
  kids s a = snd (rule (env s) (cell {s} a))

  fire : (s : St) → Active s → St
  fire s a = st (env s)
                (writes (pendingBatch (site {s} a) (kids s a)) (pending s))
                (update (site {s} a) (just (fst (rule (env s) (cell {s} a)))) (out s))

  Step : St → St → Type
  Step s t = Σ[ a ∈ Active s ] (fire s a ≡ t)

  -- Prefix-free occupancy: proper extensions of occupied addresses are vacant.
  Inv : St → Type
  Inv s = (α : Addr) {c : Cell} → pending s α ≡ just c
        → (β : Addr) → Ext β α → pending s β ≡ nothing

------------------------------------------------------------------------
-- §3  What the page proof established, as the statements to discharge.
--     (Stated here; proofs land in this file next pass, gated like
--     everything else on the checker.  Nothing below is claimed yet.)
------------------------------------------------------------------------

  -- (i)   Inv is preserved: Inv s → (a : Active s) → Inv (fire s a)
  -- (ii)  Under Inv, distinct sites have disjoint write domains:
  --         find (pendingBatch α cs) k ≡ nothing ⊎ find (pendingBatch β ds) k ≡ nothing
  --       for α ≠ β, from child-inj / child-ext / ext-of-child + Inv.
  -- (iii) The diamond on Σ St Inv, by writes-comm from (ii), same
  --       shape as Diamond.agda.
  -- (iv)  RandomDescent instantiated on (Σ St Inv).

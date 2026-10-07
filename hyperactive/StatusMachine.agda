{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- StatusMachine — the aggregating dataflow machine of MACHINE.md, with
-- the read-safe one-step diamond, hence equal-length / geodesic by
-- RandomDescent.
--
-- A cell declares `deps` (addresses whose verdicts it reads). It is
-- ACTIVE only when its own slot is pending AND every dep is already
-- done. Firing consumes the site, writes its (write-once) verdict, and
-- spawns children. The verdict may depend on the dep-values, which are
-- carried in the Active witness.
--
-- The diamond's new content over Diamond.agda is read/write non-
-- interference: an available step reads only `done` slots, and a now-
-- available competing step writes `done` only at its own (pending) site,
-- which therefore is not among the reader's deps — so the two fires
-- commute and each survives the other with an unchanged verdict. This is
-- Kahn/monotone-dataflow determinacy; aggregation (a cell waiting on its
-- children) never threatens min-steps.
------------------------------------------------------------------------

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; isOfHLevelMaybe ; ¬nothing≡just)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete)

open import Diamond using (module RandomDescent)
import DecTable

module StatusMachine
  (Env Cell Out : Type) (isSetCell : isSet Cell) (isSetOut : isSet Out)
  (Addr : Type) (_≟_ : Discrete Addr)
  (child : ℕ → Addr → Addr)
  (Ext : Addr → Addr → Type)
  (child-inj : {k l : ℕ} {α β : Addr} → child k α ≡ child l β → (k ≡ l) × (α ≡ β))
  (child-ext : (k : ℕ) (α : Addr) → Ext (child k α) α)
  (ext-irrefl : {α : Addr} → Ext α α → ⊥)
  -- `deps` and `rule`.  rule sees env, the cell, and the list of
  -- dep-verdicts (in deps order); returns this cell's verdict and kids.
  (deps : Cell → List Addr)
  (rule : Env → Cell → List Out → Out × List Cell)
  where

  open DecTable Addr _≟_

  -- Two tables: pending cells and done verdicts.  Status = the pair; the
  -- MACHINE.md three-valued Status is (pending=just/out=nothing),
  -- (pending=nothing/out=just), (both nothing).
  record St : Type where
    constructor st
    field
      env     : Env
      pending : Addr → Maybe Cell
      out     : Addr → Maybe Out
  open St public

  St-path : {s t : St} → env s ≡ env t → pending s ≡ pending t → out s ≡ out t → s ≡ t
  St-path pe pp po i = st (pe i) (pp i) (po i)

  justInj : {x y : Cell} → just x ≡ just y → x ≡ y
  justInj {x} p = cong unwrap p
    where
    unwrap : Maybe Cell → Cell
    unwrap nothing  = x
    unwrap (just c) = c

  isSetMaybeCell : isSet (Maybe Cell)
  isSetMaybeCell = isOfHLevelMaybe 0 isSetCell

  -- Reading the dep-verdicts off the state: a plain function of the
  -- state (not dependent data), so it `cong`s over paths cleanly.
  _»_ : {X Y : Type} → Maybe X → (X → Maybe Y) → Maybe Y
  nothing » _ = nothing
  just x  » f = f x

  reads : St → List Addr → Maybe (List Out)
  reads s []       = just []
  reads s (γ ∷ γs) = out s γ » λ v → reads s γs » λ vs → just (v ∷ vs)

  -- An active site: pending here, and all deps read off as a value list.
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

  -- No-spawn dataflow fragment: fire consumes the site and writes its
  -- (write-once) verdict.  Children are the next layer (Spawn's address
  -- machinery); this fragment is the monotone-dataflow / aggregation
  -- core, where the novel read-safe diamond lives.
  fire : (s : St) → Active s → St
  fire s a =
    st (env s)
       (update (addr a) nothing (pending s))
       (update (addr a) (just (verdict s a)) (out s))

  Step : St → St → Type
  Step s t = Σ[ a ∈ Active s ] (fire s a ≡ t)

  ----------------------------------------------------------------------
  -- Agreement of out-tables on a dep list, and that reads only sees it.
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

  ----------------------------------------------------------------------
  -- Invariant: a pending slot has no verdict yet (write-once / Fresh).
  ----------------------------------------------------------------------
  Fresh : St → Type
  Fresh s = (x : Addr) (c : Cell) → pending s x ≡ just c → out s x ≡ nothing

  isPropFresh : (s : St) → isProp (Fresh s)
  isPropFresh s = isPropΠ3 (λ x c _ → isOfHLevelMaybe 0 isSetOut (out s x) nothing)
    where open import Cubical.Foundations.HLevels using (isPropΠ3)

  -- Maybe-head extraction without `with … in` (unavailable in cubical):
  -- plain matching returns the path directly in the `just` clause.
  headJust : {X Y : Type} (m : Maybe X) (k : X → Maybe Y) (y : Y)
    → (m » k) ≡ just y → Σ[ x ∈ X ] m ≡ just x
  headJust nothing  k y h = Empty.rec (¬nothing≡just h)
  headJust (just x) k y h = x , refl

  tailJust : {X Y : Type} (m : Maybe X) (g : X → Y) (y : Y)
    → (m » (λ x → just (g x))) ≡ just y → Σ[ x ∈ X ] m ≡ just x
  tailJust nothing  g y h = Empty.rec (¬nothing≡just h)
  tailJust (just x) g y h = x , refl

  -- Firing at an active site β whose out-slot is empty leaves every
  -- resolved dep untouched: AllAgree (fire s β) s (the deps).
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
  -- Generic just-injectivity, ¬-symmetry.
  ----------------------------------------------------------------------
  fromJust : {X : Type} → X → Maybe X → X
  fromJust d nothing  = d
  fromJust d (just x) = x

  just-inj : {X : Type} {x y : X} → just x ≡ just y → x ≡ y
  just-inj {x = x} p = cong (fromJust x) p

  ¬sym : {x y : Addr} → ¬ x ≡ y → ¬ y ≡ x
  ¬sym np q = np (sym q)

  ----------------------------------------------------------------------
  -- Same site ⇒ same fire.
  ----------------------------------------------------------------------
  same-site : (s : St) (a b : Active s) → addr a ≡ addr b → fire s a ≡ fire s b
  same-site s a b e = St-path refl pend-eq out-eq
    where
    tcp : theCell a ≡ theCell b
    tcp = justInj (sym (here a) ∙ cong (pending s) e ∙ here b)
    vals-eq : vals a ≡ vals b
    vals-eq = just-inj (sym (reads-ok a) ∙ cong (reads s) (cong deps tcp) ∙ reads-ok b)
    verd-eq : verdict s a ≡ verdict s b
    verd-eq i = fst (rule (env s) (tcp i) (vals-eq i))
    pend-eq : update (addr a) nothing (pending s) ≡ update (addr b) nothing (pending s)
    pend-eq = cong (λ x → update x nothing (pending s)) e
    out-eq : update (addr a) (just (verdict s a)) (out s)
           ≡ update (addr b) (just (verdict s b)) (out s)
    out-eq i = update (e i) (just (verd-eq i)) (out s)

  ----------------------------------------------------------------------
  -- Distinct sites: each survives the other's fire, and the two double
  -- fires join.  (verdict (fire s b) (survive …) is verdict s a by refl,
  -- since fire never touches env and survive keeps addr/theCell/vals.)
  ----------------------------------------------------------------------
  survive : (s : St) → Fresh s → (a b : Active s) → ¬ addr a ≡ addr b → Active (fire s b)
  survive s fr a b ¬ab = act (addr a) (theCell a) here' (vals a) reads-ok'
    where
    obn : out s (addr b) ≡ nothing
    obn = fr (addr b) (theCell b) (here b)
    here' : pending (fire s b) (addr a) ≡ just (theCell a)
    here' = update-miss (addr b) (addr a) nothing (pending s) (¬sym ¬ab) ∙ here a
    reads-ok' : reads (fire s b) (deps (theCell a)) ≡ just (vals a)
    reads-ok' = reads-stable (fire s b) s (deps (theCell a))
                  (agree s b obn (deps (theCell a)) (vals a) (reads-ok a))
                ∙ reads-ok a

  join : (s : St) (fr : Fresh s) (a b : Active s) (¬ab : ¬ addr a ≡ addr b)
    → fire (fire s b) (survive s fr a b ¬ab)
    ≡ fire (fire s a) (survive s fr b a (¬sym ¬ab))
  join s fr a b ¬ab = St-path refl
    (update-comm (addr a) (addr b) nothing nothing (pending s) ¬ab)
    (update-comm (addr a) (addr b) (just (verdict s a)) (just (verdict s b)) (out s) ¬ab)

  ----------------------------------------------------------------------
  -- Fresh is preserved by fire.
  ----------------------------------------------------------------------
  Fresh-fire : (s : St) → Fresh s → (a : Active s) → Fresh (fire s a)
  Fresh-fire s fr a x c hp = goal (addr a ≟ x)
    where
    goal : Dec (addr a ≡ x) → out (fire s a) x ≡ nothing
    goal (yes p) =
      Empty.rec (¬nothing≡just
        (sym (update-hit (addr a) x nothing (pending s) p) ∙ hp))
    goal (no ¬p) =
      update-miss (addr a) x (just (verdict s a)) (out s) ¬p
      ∙ fr x c (sym (update-miss (addr a) x nothing (pending s) ¬p) ∙ hp)

  ----------------------------------------------------------------------
  -- The carrier (states with the invariant), its step, and the diamond.
  ----------------------------------------------------------------------
  Carrier : Type
  Carrier = Σ[ s ∈ St ] Fresh s

  CStep : Carrier → Carrier → Type
  CStep (s , _) (t , _) = Step s t

  open import Cubical.Foundations.HLevels using (isPropΠ3)

  cdiamond : {X Y Z : Carrier} → CStep X Y → CStep X Z
    → (Y ≡ Z) ⊎ (Σ[ W ∈ Carrier ] (CStep Y W × CStep Z W))
  cdiamond {s , fr} {t , ft} {u , fu} (a , pa) (b , pb) = branch (addr a ≟ addr b)
    where
    branch : Dec (addr a ≡ addr b)
      → ((t , ft) ≡ (u , fu))
      ⊎ (Σ[ W ∈ Carrier ] (Step t (fst W) × Step u (fst W)))
    branch (yes e) =
      inl (Σ≡Prop isPropFresh (sym pa ∙ same-site s a b e ∙ pb))
    branch (no ¬e) =
      inr ( (Wst , fw)
          , subst (λ z → Step z Wst) pa (survive s fr b a (¬sym ¬e) , join s fr b a (¬sym ¬e))
          , subst (λ z → Step z Wst) pb (survive s fr a b ¬e , refl) )
      where
      Wst : St
      Wst = fire (fire s b) (survive s fr a b ¬e)
      fw : Fresh Wst
      fw = Fresh-fire (fire s b) (Fresh-fire s fr b) (survive s fr a b ¬e)

  open RandomDescent Carrier CStep (λ {X} {Y} {Z} → cdiamond {X} {Y} {Z}) public
    using (Trace ; done ; stepTrace ; Normal
          ; same-normalization-length ; normalization-is-geodesic)

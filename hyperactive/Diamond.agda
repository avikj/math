{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Diamond — the step relation of the hyperactive machine, with its
-- one-step diamond, and the equal-length theorem inherited by
-- instantiating the essay's RandomDescent module (docs/index.html §5,
-- Theorem 5.13), reproduced verbatim in §1 below.
--
-- The machine shape being proved about (derived in session, from the
-- essay's §5 and the corpus's cost dichotomy):
--
--   * a state has an immutable shared environment (reads are free and
--     unrestricted — many readers, no duplication ceremony), and
--   * a table of slots, each optionally holding a pending cell;
--   * a step fires at one occupied slot: it CONSUMES only that slot and
--     WRITES only that slot's verdict, computing from the cell and the
--     shared environment.
--
-- Distinct steps therefore consume disjoint material and overlap only
-- in reads, which change nothing: the one-step diamond holds (§3), and
-- with it every complete reduction to a normal form has one length —
-- min-steps by theorem, not by strategy (§1 instantiated in §4).
--
-- §5 instantiates the machine at the case that motivated the design:
-- equality-judgment cells (Eql) whose two operands live in the shared
-- environment, including two judgments SHARING an operand — the exact
-- configuration Lafont-style linear formats cannot host without an
-- external checker.
------------------------------------------------------------------------

module Diamond where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; snotz)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; isOfHLevelMaybe)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; decRec)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  RandomDescent, verbatim from docs/index.html §5 (Theorem 5.13).
--     Generic in (S, Step, diamond): any step relation with the
--     one-step diamond has strategy-independent reduction length.
------------------------------------------------------------------------

module RandomDescent (S : Type) (Step : S → S → Type)
  (diamond : {s a b : S} → Step s a → Step s b
    → (a ≡ b) ⊎ (Σ[ c ∈ S ] (Step a c × Step b c))) where

  data Trace : ℕ → S → S → Type where
    done      : {s : S} → Trace zero s s
    stepTrace : {n : ℕ} {s u t : S} → Step s u → Trace n u t → Trace (suc n) s t

  Normal : S → Type
  Normal t = (u : S) → Step t u → ⊥

  peel : {n : ℕ} {s u t : S} → Step s u → Trace (suc n) s t → Normal t → Trace n u t
  peel {zero} jump (stepTrace first done) normal with diamond first jump
  ... | inl same               = subst (λ v → Trace zero v _) same done
  ... | inr (z , left , right) = Empty.rec (normal z left)
  peel {suc n} jump (stepTrace first rest) normal with diamond first jump
  ... | inl same               = subst (λ v → Trace (suc n) v _) same rest
  ... | inr (z , left , right) = stepTrace right (peel left rest normal)

  normal-length-zero : {n : ℕ} {s t : S} → Normal s → Trace n s t → n ≡ zero
  normal-length-zero normal done                   = refl
  normal-length-zero normal (stepTrace first rest) = Empty.rec (normal _ first)

  zero-endpoints : {s t : S} → Trace zero s t → s ≡ t
  zero-endpoints done = refl

  same-normalization-length : {n m : ℕ} {s t : S}
    → Trace n s t → Trace m s t → Normal t → n ≡ m
  same-normalization-length done other normal = sym (normal-length-zero normal other)
  same-normalization-length {m = zero} (stepTrace first rest) other normal =
    Empty.rec (normal _ (subst (λ s → Step s _) (zero-endpoints other) first))
  same-normalization-length {m = suc m} (stepTrace first rest) other normal =
    cong suc (same-normalization-length rest (peel first other normal) normal)

  normalization-is-geodesic : {n m : ℕ} {s t : S}
    → Trace n s t → Trace m s t → Normal t → n ≤ m
  normalization-is-geodesic chosen competitor normal =
    subst (_ ≤_) (same-normalization-length chosen competitor normal) ≤-refl

------------------------------------------------------------------------
-- §2  Pointwise update on ℕ-indexed tables, and its algebra.
--     The table is a function; a step's write is one update.  Updates
--     at distinct indices commute — this is the whole content of
--     "distinct steps consume disjoint material".
------------------------------------------------------------------------

module Tables where

  private variable A : Type

  -- update via decRec: reduces on the Dec value, so it also reduces when
  -- that Dec is the subject of an outer `with` (unlike a with-defined
  -- update, which gets stuck under goal-level abstraction).
  update : ℕ → A → (ℕ → A) → (ℕ → A)
  update i v f k = decRec (λ _ → v) (λ _ → f k) (discreteℕ i k)

  update-hit : {A : Type} (i k : ℕ) (v : A) (f : ℕ → A) → i ≡ k → update i v f k ≡ v
  update-hit i k v f p with discreteℕ i k
  ... | yes _  = refl
  ... | no ¬p  = Empty.rec (¬p p)

  update-miss : {A : Type} (i k : ℕ) (v : A) (f : ℕ → A) → ¬ i ≡ k → update i v f k ≡ f k
  update-miss i k v f ¬p with discreteℕ i k
  ... | yes p  = Empty.rec (¬p p)
  ... | no  _  = refl

  update-at : {A : Type} (i : ℕ) (v : A) (f : ℕ → A) → update i v f i ≡ v
  update-at i v f = update-hit i i v f refl

  update-elsewhere : {A : Type} (i k : ℕ) (v : A) (f : ℕ → A) → ¬ i ≡ k → update i v f k ≡ f k
  update-elsewhere = update-miss

  update-comm : {A : Type} (i j : ℕ) (v w : A) (f : ℕ → A) → ¬ i ≡ j
    → update i v (update j w f) ≡ update j w (update i v f)
  update-comm i j v w f ¬p = funExt point
    where
    -- dispatch through a helper whose codomain is FIXED (the point type),
    -- so the Decs only select a proof branch and never rewrite the goal;
    -- update-hit/miss carry their own reduction.
    point : (k : ℕ) → update i v (update j w f) k ≡ update j w (update i v f) k
    point k = lemma (discreteℕ i k) (discreteℕ j k)
      where
      lemma : Dec (i ≡ k) → Dec (j ≡ k)
            → update i v (update j w f) k ≡ update j w (update i v f) k
      lemma (yes ik) (yes jk) = Empty.rec (¬p (ik ∙ sym jk))
      lemma (yes ik) (no ¬jk) =
        update-hit i k v (update j w f) ik
        ∙ sym (update-miss j k w (update i v f) ¬jk ∙ update-hit i k v f ik)
      lemma (no ¬ik) (yes jk) =
        update-miss i k v (update j w f) ¬ik ∙ update-hit j k w f jk
        ∙ sym (update-hit j k w (update i v f) jk)
      lemma (no ¬ik) (no ¬jk) =
        update-miss i k v (update j w f) ¬ik ∙ update-miss j k w f ¬jk
        ∙ sym (update-miss j k w (update i v f) ¬jk ∙ update-miss i k v f ¬ik)

------------------------------------------------------------------------
-- §3  The machine, generically: shared immutable environment, slotted
--     pending cells, one rule computing a verdict from cell + reads.
--     The diamond is proved from the update algebra alone.
------------------------------------------------------------------------

module Machine (Env : Type) (Cell : Type) (isSetCell : isSet Cell)
               (Out : Type) (rule : Env → Cell → Out) where

  open Tables

  -- A state: the environment never changes (reads are free, shared);
  -- the two tables are what steps consume and produce.
  record St : Type where
    constructor st
    field
      env     : Env
      pending : ℕ → Maybe Cell
      out     : ℕ → Maybe Out
  open St public

  St-path : {s t : St} → env s ≡ env t → pending s ≡ pending t → out s ≡ out t → s ≡ t
  St-path pe pp po i = st (pe i) (pp i) (po i)

  -- Local helpers kept self-contained (no reliance on library lemma names).
  justInj : {x y : Cell} → just x ≡ just y → x ≡ y
  justInj {x} p = cong unwrap p
    where
    unwrap : Maybe Cell → Cell
    unwrap nothing  = x
    unwrap (just c) = c

  -- An active site: an occupied slot, with its cell.
  Active : St → Type
  Active s = Σ[ ic ∈ ℕ × Cell ] (pending s (fst ic) ≡ just (snd ic))

  site : (s : St) → Active s → ℕ
  site _ a = fst (fst a)

  cell : (s : St) → Active s → Cell
  cell _ a = snd (fst a)

  -- Firing: consume the slot, write the verdict.  Nothing else moves.
  fire : (s : St) → Active s → St
  fire s a = st (env s)
                (update {A = Maybe Cell} (site s a) nothing (pending s))
                (update {A = Maybe Out} (site s a) (just (rule (env s) (cell s a))) (out s))

  Step : St → St → Type
  Step s t = Σ[ a ∈ Active s ] (fire s a ≡ t)

  -- Occupancy is a proposition (Maybe Cell is a set), so an active site
  -- is determined by its (slot, cell) pair.
  isSetMaybeCell : isSet (Maybe Cell)
  isSetMaybeCell = isOfHLevelMaybe 0 isSetCell

  occupancyProp : (s : St) (ic : ℕ × Cell) → isProp (pending s (fst ic) ≡ just (snd ic))
  occupancyProp s ic = isSetMaybeCell _ _

  Active-path : {s : St} (a b : Active s) → fst a ≡ fst b → a ≡ b
  Active-path {s} a b eq = Σ≡Prop (occupancyProp s) eq

  -- The diamond, at fired states first.
  module _ (s : St) (a b : Active s) where

    -- Same slot: the cells agree, the fired states agree.
    same-slot : site s a ≡ site s b → fire s a ≡ fire s b
    same-slot p = cong (fire s) (Active-path {s = s} a b pair-path)
      where
      cells-agree : cell s a ≡ cell s b
      cells-agree = justInj (sym (snd a) ∙ cong (pending s) p ∙ snd b)
      pair-path : fst a ≡ fst b
      pair-path i = p i , cells-agree i

    -- Distinct slots: each survives the other's firing...
    survive : (¬ site s a ≡ site s b) → Active (fire s a)
    survive ¬p = fst b ,
      ( Tables.update-elsewhere (site s a) (site s b) nothing (pending s) ¬p
      ∙ snd b )

    -- ...and the two double-firings land on one state.
    join : (¬p : ¬ site s a ≡ site s b) (¬q : ¬ site s b ≡ site s a)
      → fire (fire s a) (survive ¬p)
      ≡ fire (fire s b) ((fst a) ,
          ( Tables.update-elsewhere (site s b) (site s a) nothing (pending s) ¬q
          ∙ snd a ))
    join ¬p ¬q = St-path refl
      (Tables.update-comm (site s b) (site s a) nothing nothing (pending s) ¬q)
      (Tables.update-comm (site s b) (site s a)
        (just (rule (env s) (cell s b))) (just (rule (env s) (cell s a))) (out s) ¬q)

  ¬sym : {x y : ℕ} → ¬ x ≡ y → ¬ y ≡ x
  ¬sym ¬p q = ¬p (sym q)

  diamond : {s t u : St} → Step s t → Step s u
    → (t ≡ u) ⊎ (Σ[ c ∈ St ] (Step t c × Step u c))
  diamond {s} (a , pa) (b , pb) with discreteℕ (site s a) (site s b)
  ... | yes p = inl (sym pa ∙ same-slot s a b p ∙ pb)
  ... | no ¬p =
    inr ( fire (fire s a) (survive s a b ¬p)
        , subst (λ x → Step x (fire (fire s a) (survive s a b ¬p))) pa
            (survive s a b ¬p , refl)
        , subst (λ x → Step x (fire (fire s a) (survive s a b ¬p))) pb
            ( (fst a , ( Tables.update-elsewhere (site s b) (site s a)
                           nothing (pending s) (¬sym ¬p)
                       ∙ snd a ))
            , sym (join s a b ¬p (¬sym ¬p)) ) )

  -- The inheritance: min-steps for this machine is Theorem 5.13
  -- instantiated, not argued.
  open RandomDescent St Step diamond public
    using (Trace ; done ; stepTrace ; Normal
          ; same-normalization-length ; normalization-is-geodesic)

------------------------------------------------------------------------
-- §4  The motivating instance: equality-judgment cells over a shared
--     operand pool, including two judgments sharing an operand.
------------------------------------------------------------------------

module EqlInstance where

  open Tables

  eqBool : Bool → Bool → Bool
  eqBool true  true  = true
  eqBool true  false = false
  eqBool false true  = false
  eqBool false false = true

  -- Cells are pairs of operand addresses into the shared pool.
  CellT : Type
  CellT = ℕ × ℕ

  isSetCellT : isSet CellT
  isSetCellT = isSet× isSetℕ isSetℕ

  ruleT : (ℕ → Bool) → CellT → Bool
  ruleT pool (i , j) = eqBool (pool i) (pool j)

  open Machine (ℕ → Bool) CellT isSetCellT Bool ruleT public

  -- The pool: operand 0 = true, 1 = true, 2 = false.
  pool₀ : ℕ → Bool
  pool₀ zero                = true
  pool₀ (suc zero)          = true
  pool₀ (suc (suc _))       = false

  -- Two judgment cells SHARING operand 0:
  --   slot 0:  Eql (op 0) (op 1)   — expect true
  --   slot 1:  Eql (op 0) (op 2)   — expect false
  pending₀ : ℕ → Maybe CellT
  pending₀ = update 0 (just (0 , 1)) (update 1 (just (0 , 2)) (λ _ → nothing))

  s₀ : St
  s₀ = st pool₀ pending₀ (λ _ → nothing)

  a₀ : Active s₀
  a₀ = (0 , (0 , 1)) , update-at 0 (just (0 , 1)) (update 1 (just (0 , 2)) (λ _ → nothing))

  -- Slot 1 is occupied in s₀: step under the outer update, then hit.
  occupied₁ : pending₀ 1 ≡ just (0 , 2)
  occupied₁ =
      update-elsewhere 0 1 (just (0 , 1)) (update 1 (just (0 , 2)) (λ _ → nothing))
        (λ p → snotz (sym p))
    ∙ update-at 1 (just (0 , 2)) (λ _ → nothing)

  b₀ : Active s₀
  b₀ = (1 , (0 , 2)) , occupied₁

  -- Fire both, in one order; the diamond theorem says the other order
  -- costs the same — no computation of the other order is needed, which
  -- is the point.  But both verdicts are checked by refl:
  s₁ : St
  s₁ = fire s₀ a₀

  verdict-first : out s₁ 0 ≡ just true
  verdict-first = update-at 0 (just true) (out s₀)

  b₁ : Active s₁
  b₁ = (1 , (0 , 2)) ,
    ( update-elsewhere 0 1 nothing (pending s₀) (λ p → snotz (sym p))
    ∙ occupied₁ )

  s₂ : St
  s₂ = fire s₁ b₁

  verdict-second : out s₂ 1 ≡ just false
  verdict-second = update-at 1 (just false) (out s₁)

  -- Both pending slots are now consumed:
  consumed₀ : pending s₂ 0 ≡ nothing
  consumed₀ =
      update-elsewhere 1 0 nothing (pending s₁) (λ p → snotz p)
    ∙ update-at 0 nothing (pending s₀)

  consumed₁ : pending s₂ 1 ≡ nothing
  consumed₁ = update-at 1 nothing (pending s₁)

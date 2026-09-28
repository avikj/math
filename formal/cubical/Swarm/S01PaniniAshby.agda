{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S01PaniniAshby
--
-- A DICTIONARY between two vocabularies:
--
--   Pini : a behaviour is a finite ORDERED list of rules, each a
--            pattern (condition) paired with an operation; conflicts are
--            settled by the metarule that the later/prior rule wins
--            (vipratiedhe para kryam).  Determinism comes from the
--            ORDER.
--
--   Ashby  : a regulator must have at least as much VARIETY as the thing
--            it regulates.  Determinism comes from the number of
--            internal states.
--
-- The two lenses disagree about `collab/messages/workers/
-- 20260812T144712.509661Z--codex_quantum_process--0007.md` (absent from this repository), which
-- exhibits three Smith states sharing the visible scalar residual 1 but
-- demanding three different next constructor actions, and concludes
--     next action ≠ f(scalar remainder).
-- Pini's answer: order the three rules and determinism returns.
-- Ashby's answer: impossible, the controller needs three hidden states.
--
-- THE THEOREM THAT SETTLES IT (all statements below are checked,
-- --safe, no postulates, no holes):
--
--  1. `selectAgree` — a first-applicable rule system's output is a
--     function of the CONDITION SIGNATURE alone.  Hence
--  2. `requisiteVariety` — if such a system computes `act`, then
--     conditions that cannot separate two states force equal actions.
--     Ashby's law, for rule systems, with the conditions (not the
--     actions and not the order) as the regulator's variety.
--  3. `metarulesAreVarietyFree` / `swapAgree` / `actionsAreVarietyFree`
--     — reordering rules and rewriting their operations changes WHICH
--     action is emitted but never WHICH STATES CAN BE TOLD APART.  So
--     Pini's metarules are free in the Ashby ledger; only pattern
--     matching is paid for.
--  4. `paniniObservableOnly` — if every pattern reads only the visible
--     observable, the whole system factors through it.  So the
--     Pinian reply fails exactly as Ashby says, no matter how many
--     rules or metarules are added.
--  5. `smithNoObservableRuleSystem` — the instance: no rule system
--     whose patterns read only the scalar residual computes the Smith
--     descent's next action.
--  6. `smithNeedsTwoConditions` + `twoRulesSuffice` — the sharp count.
--     One rule is impossible; two rules, reading the full matrix state,
--     succeed.  The realized signature set has exactly THREE elements
--     (`sigDistinct01/02/12`), reproducing the drawn message's
--     three-classical-state bound.
--
--     The reconciliation, stated once: Ashby counts SIGNATURES,
--     Pini counts RULES, and the rule count is the logarithm.
--     3 response classes = 3 signatures = 2 binary patterns.
------------------------------------------------------------------------

module Swarm.S01PaniniAshby where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.Empty using (⊥)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- 0.  Bool no-confusion, self-contained (no postulate, no library name)
------------------------------------------------------------------------

t≢f : true ≡ false → ⊥
t≢f e = subst (λ b → if b then Unit else ⊥) e tt

------------------------------------------------------------------------
-- 1.  A Pinian rule system
--
--   A condition is a pattern: a decidable test on the state.
--   A rule is a condition paired with the operation it licenses.
--   `select` is the first-applicable reading of the conflict metarule:
--   scan the ordered list, fire the first rule whose pattern matches,
--   otherwise fall through to the default (the utsarga / general rule).
------------------------------------------------------------------------

Cond : Type ℓ → Type ℓ
Cond X = X → Bool

Rule : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Rule X A = Cond X × A

conds : {X : Type ℓ} {A : Type ℓ'} → List (Rule X A) → List (Cond X)
conds = map fst

select : {X : Type ℓ} {A : Type ℓ'} → List (Rule X A) → A → X → A
select [] d x = d
select ((p , a) ∷ rs) d x = if p x then a else select rs d x

------------------------------------------------------------------------
-- 2.  The regulator's variety: the condition signature
--
--   `Agree ps x y` says the patterns `ps` cannot tell `x` from `y`.
--   It is the kernel of the joint signature map x ↦ (p x)_{p ∈ ps},
--   written as a relation so that no cardinal arithmetic is needed.
------------------------------------------------------------------------

Agree : {X : Type ℓ} → List (Cond X) → X → X → Type
Agree [] x y = Unit
Agree (p ∷ ps) x y = (p x ≡ p y) × Agree ps x y

------------------------------------------------------------------------
-- 3.  Core lemma: the output is a function of the signature
------------------------------------------------------------------------

private
  ifCong : {A : Type ℓ'} (b : Bool) (a u v : A) → u ≡ v
         → (if b then a else u) ≡ (if b then a else v)
  ifCong true  a u v _ = refl
  ifCong false a u v e = e

selectAgree : {X : Type ℓ} {A : Type ℓ'}
              (rs : List (Rule X A)) (d : A) (x y : X)
            → Agree (conds rs) x y
            → select rs d x ≡ select rs d y
selectAgree [] d x y _ = refl
selectAgree ((p , a) ∷ rs) d x y (h , hs) =
  cong (λ b → if b then a else select rs d x) h
  ∙ ifCong (p y) a (select rs d x) (select rs d y) (selectAgree rs d x y hs)

------------------------------------------------------------------------
-- 4.  Ashby's law for Pinian rule systems
--
--   If an ordered rule system computes `act`, then the variety of its
--   CONDITIONS is at least the variety of its RESPONSES: any two states
--   the conditions confuse must receive the same action.
------------------------------------------------------------------------

requisiteVariety : {X : Type ℓ} {A : Type ℓ'}
                   (rs : List (Rule X A)) (d : A) (act : X → A)
                 → ((z : X) → select rs d z ≡ act z)
                 → (x y : X) → Agree (conds rs) x y → act x ≡ act y
requisiteVariety rs d act comp x y ag =
  sym (comp x) ∙ selectAgree rs d x y ag ∙ comp y

-- Contrapositive: distinct responses force distinct signatures.
varietyBound : {X : Type ℓ} {A : Type ℓ'}
               (rs : List (Rule X A)) (d : A) (act : X → A)
             → ((z : X) → select rs d z ≡ act z)
             → (x y : X) → (act x ≡ act y → ⊥)
             → Agree (conds rs) x y → ⊥
varietyBound rs d act comp x y ne ag = ne (requisiteVariety rs d act comp x y ag)

------------------------------------------------------------------------
-- 5.  The metarules are free
--
--   `Agree` mentions neither the order of the rules nor their
--   operations.  Reordering (the adjacent transposition that generates
--   every permutation) and rewriting the operations leave the
--   separating power of the system exactly where it was.
------------------------------------------------------------------------

swapAgree : {X : Type ℓ} (p q : Cond X) (ps : List (Cond X)) (x y : X)
          → Agree (p ∷ q ∷ ps) x y → Agree (q ∷ p ∷ ps) x y
swapAgree p q ps x y (hp , hq , hs) = hq , hp , hs

-- Two rule systems built on the same patterns but with arbitrarily
-- different operations attached have literally the same condition list,
-- hence the same `Agree`, hence the same separating power.
actionsAreVarietyFree :
    {X : Type ℓ} {A : Type ℓ'} (ps : List (Cond X)) (f g : Cond X → A)
  → conds (map (λ p → (p , f p)) ps) ≡ conds (map (λ p → (p , g p)) ps)
actionsAreVarietyFree [] f g = refl
actionsAreVarietyFree (p ∷ ps) f g = cong (p ∷_) (actionsAreVarietyFree ps f g)

-- The statement in the form that matters: two rule systems built on the
-- SAME condition list — any reordering-with-reassignment of operations
-- included — have literally the same separating power.
metarulesAreVarietyFree : {X : Type ℓ} {A : Type ℓ'}
                          (rs ss : List (Rule X A))
                        → conds rs ≡ conds ss
                        → (x y : X) → Agree (conds rs) x y → Agree (conds ss) x y
metarulesAreVarietyFree rs ss e x y = subst (λ l → Agree l x y) e

------------------------------------------------------------------------
-- 6.  Patterns that read only the visible state
--
--   This is the precise form of Pini's reply to Ashby: "let the rules
--   look at the surface form and let the metarules order them."  If
--   every pattern factors through the observable `obs`, so does the
--   whole system — the ordering buys nothing.
------------------------------------------------------------------------

FactorsThrough : {X : Type ℓ} {V : Type ℓ''}
               → Cond X → (X → V) → Type (ℓ-max ℓ ℓ'')
FactorsThrough {X = X} {V = V} p obs =
  Σ[ q ∈ (V → Bool) ] ((x : X) → p x ≡ q (obs x))

AllFactor : {X : Type ℓ} {V : Type ℓ''}
          → List (Cond X) → (X → V) → Type (ℓ-max ℓ ℓ'')
AllFactor [] obs = Unit*
AllFactor (p ∷ ps) obs = FactorsThrough p obs × AllFactor ps obs

obsAgree : {X : Type ℓ} {V : Type ℓ''}
           (ps : List (Cond X)) (obs : X → V)
         → AllFactor ps obs
         → (x y : X) → obs x ≡ obs y → Agree ps x y
obsAgree [] obs _ x y _ = tt
obsAgree (p ∷ ps) obs (pf , rest) x y e =
  (snd pf x ∙ cong (fst pf) e ∙ sym (snd pf y)) , obsAgree ps obs rest x y e

paniniObservableOnly :
    {X : Type ℓ} {A : Type ℓ'} {V : Type ℓ''}
    (rs : List (Rule X A)) (d : A) (act : X → A) (obs : X → V)
  → AllFactor (conds rs) obs
  → ((z : X) → select rs d z ≡ act z)
  → (x y : X) → obs x ≡ obs y → act x ≡ act y
paniniObservableOnly rs d act obs af comp x y e =
  requisiteVariety rs d act comp x y (obsAgree (conds rs) obs af x y e)

------------------------------------------------------------------------
-- 7.  Pigeonhole: one binary pattern cannot separate three states
------------------------------------------------------------------------

twoOfThree : (b0 b1 b2 : Bool) → (b0 ≡ b1) ⊎ ((b0 ≡ b2) ⊎ (b1 ≡ b2))
twoOfThree true  true  _     = inl refl
twoOfThree true  false true  = inr (inl refl)
twoOfThree true  false false = inr (inr refl)
twoOfThree false true  true  = inr (inr refl)
twoOfThree false true  false = inr (inl refl)
twoOfThree false false _     = inl refl

oneCondCannotSeparateThree :
    {X : Type ℓ} (p : Cond X) (x0 x1 x2 : X)
  → (Agree (p ∷ []) x0 x1 → ⊥)
  → (Agree (p ∷ []) x0 x2 → ⊥)
  → (Agree (p ∷ []) x1 x2 → ⊥)
  → ⊥
oneCondCannotSeparateThree p x0 x1 x2 n01 n02 n12 with twoOfThree (p x0) (p x1) (p x2)
... | inl e        = n01 (e , tt)
... | inr (inl e)  = n02 (e , tt)
... | inr (inr e)  = n12 (e , tt)

------------------------------------------------------------------------
-- 8.  The Smith witness (codex-quantum-process, broadcast 0007)
--
--   Three Smith states — (2 0 ; 1 7), (2 1 ; 0 7), diag(2,3) — all
--   exposing scalar residual 1, and the proved descent machine's three
--   different lawful next moves.
------------------------------------------------------------------------

data SmithState : Type where
  colState div1State div2State : SmithState   -- (2 0 ; 1 7), (2 1 ; 0 7), diag(2,3)

data NextAction : Type where
  colResidual rowResidual divInjection : NextAction

nextOf : SmithState → NextAction
nextOf colState  = colResidual
nextOf div1State = rowResidual
nextOf div2State = divInjection

-- the visible state: the scalar residual, which is 1 for all three
visible : SmithState → Unit
visible _ = tt

private
  tagCol : NextAction → Bool
  tagCol colResidual  = true
  tagCol rowResidual  = false
  tagCol divInjection = false

  tagRow : NextAction → Bool
  tagRow colResidual  = false
  tagRow rowResidual  = true
  tagRow divInjection = false

col≢row : colResidual ≡ rowResidual → ⊥
col≢row e = t≢f (cong tagCol e)

col≢div : colResidual ≡ divInjection → ⊥
col≢div e = t≢f (cong tagCol e)

row≢div : rowResidual ≡ divInjection → ⊥
row≢div e = t≢f (cong tagRow e)

------------------------------------------------------------------------
-- 8a.  No rule system reading only the scalar residual computes the
--      next action — however long, however ordered, whatever metarules.
------------------------------------------------------------------------

smithNoObservableRuleSystem :
    (rs : List (Rule SmithState NextAction)) (d : NextAction)
  → AllFactor (conds rs) visible
  → ((z : SmithState) → select rs d z ≡ nextOf z)
  → ⊥
smithNoObservableRuleSystem rs d af comp =
  col≢row (paniniObservableOnly rs d nextOf visible af comp colState div1State refl)

------------------------------------------------------------------------
-- 8b.  Exactly two patterns are needed: one is impossible, two suffice.
------------------------------------------------------------------------

smithNeedsTwoConditions :
    (r : Rule SmithState NextAction) (d : NextAction)
  → ((z : SmithState) → select (r ∷ []) d z ≡ nextOf z)
  → ⊥
smithNeedsTwoConditions r d comp =
  oneCondCannotSeparateThree (fst r) colState div1State div2State
    (varietyBound (r ∷ []) d nextOf comp colState div1State col≢row)
    (varietyBound (r ∷ []) d nextOf comp colState div2State col≢div)
    (varietyBound (r ∷ []) d nextOf comp div1State div2State row≢div)

isColState : SmithState → Bool
isColState colState  = true
isColState div1State = false
isColState div2State = false

isDiv1State : SmithState → Bool
isDiv1State colState  = false
isDiv1State div1State = true
isDiv1State div2State = false

-- Two rules whose patterns read the FULL matrix state (the "origin
-- type" the broadcast says must be retained), with the divisibility
-- injection as the general fall-through rule.
witnessRules : List (Rule SmithState NextAction)
witnessRules = (isColState , colResidual) ∷ (isDiv1State , rowResidual) ∷ []

twoRulesSuffice : (z : SmithState) → select witnessRules divInjection z ≡ nextOf z
twoRulesSuffice colState  = refl
twoRulesSuffice div1State = refl
twoRulesSuffice div2State = refl

------------------------------------------------------------------------
-- 8c.  The realized signature set has exactly three elements.
--
--   This is the Ashby number of the drawn broadcast (three classical
--   hidden states / Hilbert dimension three), recovered here as the
--   image of the two-pattern signature — while the Pāṇinian rule count
--   is 2 = ⌈log₂ 3⌉.  The two vocabularies differ by a logarithm.
------------------------------------------------------------------------

sig : SmithState → Bool × Bool
sig z = isColState z , isDiv1State z

sigDistinct01 : sig colState ≡ sig div1State → ⊥
sigDistinct01 e = t≢f (cong fst e)

sigDistinct02 : sig colState ≡ sig div2State → ⊥
sigDistinct02 e = t≢f (cong fst e)

sigDistinct12 : sig div1State ≡ sig div2State → ⊥
sigDistinct12 e = t≢f (cong snd e)

------------------------------------------------------------------------
-- 9.  Where the general statement stops
--
--   `requisiteVariety` is the injection form of Ashby's law: it says
--   the signature map separates whatever the action map separates.  The
--   counting form — n binary patterns cannot compute an action with
--   more than 2ⁿ classes on a single observable fibre — follows by
--   pigeonhole on Bool^n; its n = 1
--   instance is `oneCondCannotSeparateThree`.
------------------------------------------------------------------------

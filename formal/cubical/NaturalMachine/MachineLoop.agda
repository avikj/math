{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.MachineLoop
--
-- A MODEL OF `machine/MathMachine.hs` (absent from this repository)'s ROUND LOOP.  Not the loop.
--
-- The Haskell engine generates terms up to a size bound, normalises them
-- with everything already proved, fingerprints them against a finite list
-- of random assignments to form equivalence classes, conjectures
-- equalities inside a class, refutes by computation, proves the survivors,
-- installs each proof as a rewrite rule, and — when a round yields nothing
-- — GROWS by widening the vocabulary or raising the size horizon.
--
-- WHAT THIS MODULE CONSTRAINS.  Exactly three decision rules:
--
--   1.  the classification of a round by what it did to the count of open
--       conjectures, and the conclusion that a `decay` round need not
--       grow (§1);
--   2.  the separation clause of the growth gate: DO NOT GROW ON A
--       COLLAPSED TEST SET (§2);
--   3.  the min-plus choice among the growth moves on offer — widen,
--       raise, retire, stay — and the two properties the chooser has:
--       it never picks something worse than staying, and when it strictly
--       wins it exhibits a LISTED move that is strictly cheaper (§3).
--
-- HYPOTHESES THE HASKELL CANNOT SUPPLY are taken as explicit arguments,
-- never assumed: decidable equality on fingerprint values
-- (`Discrete Value`), the fact that a probe list actually contains a
-- term's own reading (`agree→same-fingerprint`), the existence of two
-- distinct terms (`do-not-grow-on-a-collapsed-test-set`), and the
-- provenance of a listed neighbour (`Listed`, in
-- `choose-exhibits-tagged-move`).
--
-- NOTHING IS REPROVED.  §1 instantiates `KFlowWF.decay-wf-𝒦`,
-- `KFlow.resonance`, `KFlow.branching`.  §2 instantiates
-- `ChuAdvance.agree-drop` / `no-tests-no-defect` and `ChuDefect.defect-mono`
-- / `defect-[]`.  §3 instantiates `Residual.Γ↝-never-worse` and
-- `ResidualPath.Γ↝-optimal` / `Γ↝-greatest` / `Γ↝-sound-member`.  The only
-- new inductions in the file are the two small bridges `agree-at` and
-- `disagree-witness`, and the membership transfer `∈-nbrs`.
------------------------------------------------------------------------

module NaturalMachine.MachineLoop where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true ; _≟_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order
  using (_<_ ; _≤_ ; ¬m<m ; <-trans ; lt ; eq ; gt)
  renaming (_≟_ to _≟ℕ_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; Discrete)

import NaturalMachine.KFlow as K
import NaturalMachine.KFlowWF as KWF

open import NaturalMachine.ChuAdvance
  using (Obs ; Agree ; Separates ; agree-drop ; no-tests-no-defect)
open import NaturalMachine.ChuDefect
  using (_∈L_ ; defect ; defect-mono ; defect-[])

open import NaturalMachine.CostGeometry
  using (Cost ; Work ; Presentation ; pres ; Carrier ; Edge ; edge ; detour)
open import NaturalMachine.Residual
  using (Neighbour ; nbr ; there ; out ; back ; work ; route ; Γ↝ ; Γ↝-never-worse)
open import NaturalMachine.ResidualPath
  using (Any ; here ; later ; _∈_ ; Γ↝-optimal ; Γ↝-greatest ; Γ↝-sound-member)

------------------------------------------------------------------------
-- §1.  THE FLOW TRICHOTOMY
--
-- The round's obstruction is ONE natural number: the count of conjectures
-- the round stated and did not close.  (`∂ before` is that count at the
-- start of the round, `∂ after` at its end.)  Nothing else about the round
-- enters the classification, which is the point: the growth rule may read
-- the measure and may not read the round.
------------------------------------------------------------------------

data Flow : Type₀ where
  decay     : Flow
  resonance : Flow
  branching : Flow

-- What each verdict asserts about the two counts.
Reads : ℕ → ℕ → Flow → Type₀
Reads ∂ ∂' decay     = ∂' < ∂
Reads ∂ ∂' resonance = ∂' ≡ ∂
Reads ∂ ∂' branching = ∂ < ∂'

-- The decision procedure, carrying its own evidence.
classify : (∂ ∂' : ℕ) → Σ[ f ∈ Flow ] Reads ∂ ∂' f
classify ∂ ∂' with ∂' ≟ℕ ∂
... | lt p = decay     , p
... | eq p = resonance , p
... | gt p = branching , p

flowOf : ℕ → ℕ → Flow
flowOf ∂ ∂' = fst (classify ∂ ∂')

flow-reads : (∂ ∂' : ℕ) → Reads ∂ ∂' (flowOf ∂ ∂')
flow-reads ∂ ∂' = snd (classify ∂ ∂')

-- (F0)  Totality: the classification always lands in one of the three.
flow-cases : (f : Flow) → (f ≡ decay) ⊎ ((f ≡ resonance) ⊎ (f ≡ branching))
flow-cases decay     = inl refl
flow-cases resonance = inr (inl refl)
flow-cases branching = inr (inr refl)

flow-total :
    (∂ ∂' : ℕ)
  → (flowOf ∂ ∂' ≡ decay) ⊎ ((flowOf ∂ ∂' ≡ resonance) ⊎ (flowOf ∂ ∂' ≡ branching))
flow-total ∂ ∂' = flow-cases (flowOf ∂ ∂')

-- (F1)  Soundness of each verdict.
flow-decay→drop : (∂ ∂' : ℕ) → flowOf ∂ ∂' ≡ decay → ∂' < ∂
flow-decay→drop ∂ ∂' p = subst (Reads ∂ ∂') p (flow-reads ∂ ∂')

flow-resonance→same : (∂ ∂' : ℕ) → flowOf ∂ ∂' ≡ resonance → ∂' ≡ ∂
flow-resonance→same ∂ ∂' p = subst (Reads ∂ ∂') p (flow-reads ∂ ∂')

flow-branching→rise : (∂ ∂' : ℕ) → flowOf ∂ ∂' ≡ branching → ∂ < ∂'
flow-branching→rise ∂ ∂' p = subst (Reads ∂ ∂') p (flow-reads ∂ ∂')

-- (F2)  Mutual exclusivity, in its sharp form: the three readings cannot
--       both hold, so the verdict is DETERMINED by the two counts.
flow-unique : (∂ ∂' : ℕ) (f g : Flow) → Reads ∂ ∂' f → Reads ∂ ∂' g → f ≡ g
flow-unique ∂ ∂' decay     decay     _  _  = refl
flow-unique ∂ ∂' decay     resonance rf rg = ⊥.rec (¬m<m (subst (_< ∂) rg rf))
flow-unique ∂ ∂' decay     branching rf rg = ⊥.rec (¬m<m (<-trans rf rg))
flow-unique ∂ ∂' resonance decay     rf rg = ⊥.rec (¬m<m (subst (_< ∂) rf rg))
flow-unique ∂ ∂' resonance resonance _  _  = refl
flow-unique ∂ ∂' resonance branching rf rg = ⊥.rec (¬m<m (subst (∂ <_) rf rg))
flow-unique ∂ ∂' branching decay     rf rg = ⊥.rec (¬m<m (<-trans rg rf))
flow-unique ∂ ∂' branching resonance rf rg = ⊥.rec (¬m<m (subst (∂ <_) rg rf))
flow-unique ∂ ∂' branching branching _  _  = refl

-- The three exclusion statements the Haskell's `case` arms rely on.
private
  isDecay isResonance isBranching : Flow → Type₀
  isDecay decay = Unit
  isDecay resonance = ⊥
  isDecay branching = ⊥
  isResonance decay = ⊥
  isResonance resonance = Unit
  isResonance branching = ⊥
  isBranching decay = ⊥
  isBranching resonance = ⊥
  isBranching branching = Unit

decay≢resonance : ¬ (decay ≡ resonance)
decay≢resonance p = subst isDecay p tt

decay≢branching : ¬ (decay ≡ branching)
decay≢branching p = subst isDecay p tt

resonance≢branching : ¬ (resonance ≡ branching)
resonance≢branching p = subst isResonance p tt

-- The round-to-round step of the obstruction count.  `K.𝒦 = ℕ → ℕ` is
-- ∂ ∘ Γ already evaluated: `step n` is the count of open conjectures after
-- a round that began with n of them.
LoopDecaying : K.𝒦 → Type₀
LoopDecaying step = (n : ℕ) → 0 < n → flowOf n (step n) ≡ decay

LoopResonant : K.𝒦 → ℕ → Type₀
LoopResonant step n = flowOf n (step n) ≡ resonance

LoopBranching : K.𝒦 → Type₀
LoopBranching step = (n : ℕ) → 0 < n → flowOf n (step n) ≡ branching

decaying→contracting : (step : K.𝒦) → LoopDecaying step → K.Contracting step
decaying→contracting step d n pos = flow-decay→drop n (step n) (d n pos)

-- (F3)  THE PAYOFF, AND THE RULE THE HASKELL ENFORCES.
--       A round in `decay` need not grow: iterating a decaying round
--       reaches ∂ = 0 in finitely many rounds.  This is `KFlowWF.decay-wf-𝒦`
--       — well-founded descent on ∂, no fuel — instantiated, not reproved.
decay-closes-without-growth :
    (step : K.𝒦) → LoopDecaying step
  → (n : ℕ) → Σ[ k ∈ ℕ ] K.iterate step k n ≡ 0
decay-closes-without-growth step d n =
  KWF.decay-wf-𝒦 step (decaying→contracting step d) n

-- (F4)  And the two verdicts that DO force a move.
--
--       Resonance is the deadlock the Haskell's own log recorded: the same
--       rules, vocab and size give the same terms, hence the same
--       conjectures, hence a bit-identical round, forever.  `K.resonance`
--       says exactly that the orbit is the point.
resonance-round-is-bit-identical :
    (step : K.𝒦) (n : ℕ) → LoopResonant step n
  → (k : ℕ) → K.iterate step k n ≡ n
resonance-round-is-bit-identical step n r =
  K.resonance step n (flow-resonance→same n (step n) r)

--       Branching never closes: no finite number of rounds annihilates an
--       expanding obstruction, so waiting is not a strategy.
branching-never-closes :
    (step : K.𝒦) → LoopBranching step
  → (k n : ℕ) → 0 < n → ¬ (K.iterate step k n ≡ 0)
branching-never-closes step b =
  K.branching step (λ n pos → flow-branching→rise n (step n) (b n pos))

------------------------------------------------------------------------
-- §2.  THE ADVANCE GATE'S SEPARATION CLAUSE
--
-- The loop's objects are normalised terms; its tests are the finite list of
-- random assignments; two terms are separated when some assignment gives
-- them different values.  That is literally `ChuAdvance.Agree` — with one
-- honest adjustment, stated here rather than hidden: `Obs X T` is
-- Bool-valued, while the machine's fingerprint is a `Value`.  The Chu
-- observation a Value-valued fingerprint induces is the BIT TEST — at
-- assignment `env` and probe value `v`, does this term read `v`? — and
-- `agree→same-fingerprint` proves that agreement on the bit tests is
-- agreement of fingerprints, provided the probe list contains the term's
-- own reading.  That proviso is the hypothesis the Haskell supplies by
-- construction (it probes with the values it computed) and it is taken as
-- an explicit argument.
------------------------------------------------------------------------

Fingerprint : Type₀ → Type₀ → Type₀ → Type₀
Fingerprint Term Env Value = Term → Env → Value

Probe : Type₀ → Type₀ → Type₀
Probe Env Value = Env × Value

private
  decB : {B : Type₀} → Dec B → Bool
  decB (yes _) = true
  decB (no  _) = false

  decB-true→ : {B : Type₀} (u : Dec B) → decB u ≡ true → B
  decB-true→ (yes p) _ = p
  decB-true→ (no ¬p) q = ⊥.rec (false≢true q)

eqB : {V : Type₀} → Discrete V → V → V → Bool
eqB d a b = decB (d a b)

eqB-refl : {V : Type₀} (d : Discrete V) (a : V) → eqB d a a ≡ true
eqB-refl d a with d a a
... | yes _  = refl
... | no  ¬p = ⊥.rec (¬p refl)

eqB-true→≡ : {V : Type₀} (d : Discrete V) (a b : V) → eqB d a b ≡ true → a ≡ b
eqB-true→≡ d a b q = decB-true→ (d a b) q

-- The Chu space of the round: points are terms, tests are probes.
obsOf : {Term Env Value : Type₀}
      → Discrete Value → Fingerprint Term Env Value
      → Obs Term (Probe Env Value)
obsOf d ev t (env , v) = eqB d (ev t env) v

-- Agreement is pointwise on the list; this is the projection at one test.
agree-at :
    {X T : Type₀} (e : Obs X T) (ts : List T) (x y : X)
  → Agree e ts x y → (t : T) → t ∈L ts → e x t ≡ e y t
agree-at e []       x y a       t m       = ⊥.rec m
agree-at e (s ∷ ts) x y (p , a) t (inl q) = subst (λ z → e x z ≡ e y z) (sym q) p
agree-at e (s ∷ ts) x y (p , a) t (inr m) = agree-at e ts x y a t m

-- THE BRIDGE.  Agreement on the probes IS equality of fingerprints, at
-- every assignment the round probed with the term's own reading.  (The
-- membership hypothesis is explicit: without it the statement is false,
-- and it is false for exactly the reason §2 is about.)
agree→same-fingerprint :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value)
    (ps : List (Probe Env Value)) (x y : Term) (env : Env)
  → ((env , ev x env) ∈L ps)
  → Agree (obsOf d ev) ps x y
  → ev y env ≡ ev x env
agree→same-fingerprint d ev ps x y env m a =
  eqB-true→≡ d (ev y env) (ev x env)
    (sym (agree-at (obsOf d ev) ps x y a (env , ev x env) m)
      ∙ eqB-refl d (ev x env))

--------------------------------------------------------------------------
-- (a)  The defect is monotone in the assignment list: SHRINKING THE TEST
--      SET CAN ONLY MERGE TERMS.  Qualitatively (`agree-drop`) and as an
--      inequality between numbers (`defect-mono`).
--------------------------------------------------------------------------

shrinking-tests-merges :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value)
    (ps qs : List (Probe Env Value)) (x y : Term)
  → Agree (obsOf d ev) (ps ++ qs) x y → Agree (obsOf d ev) ps x y
shrinking-tests-merges d ev ps qs x y a =
  fst (agree-drop (obsOf d ev) ps qs x y a)

defect-monotone-in-assignments :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value)
    (ps qs : List (Probe Env Value)) (ts : List Term)
  → defect (obsOf d ev) ps ts ≤ defect (obsOf d ev) (ps ++ qs) ts
defect-monotone-in-assignments d ev ps qs ts = defect-mono (obsOf d ev) ps qs ts

--------------------------------------------------------------------------
-- (b)  With an EMPTY assignment list every pair agrees, for every
--      fingerprint whatever.  So "this round observed no distinctions" is
--      a statement about the tests and not about the terms.
--------------------------------------------------------------------------

collapsed-tests-agree :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value) (x y : Term)
  → Agree (obsOf d ev) [] x y
collapsed-tests-agree d ev x y = no-tests-no-defect (obsOf d ev) x y

collapsed-tests-zero-defect :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value) (ts : List Term)
  → defect (obsOf d ev) [] ts ≡ 0
collapsed-tests-zero-defect d ev ts = defect-[] (obsOf d ev) ts

-- The same fact said as a limitation: an empty probe list separates only if
-- every two terms are already equal.
collapsed-tests-force-trivial :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value)
  → Separates (obsOf d ev) [] → (x y : Term) → x ≡ y
collapsed-tests-force-trivial d ev sep x y = sep x y tt

--------------------------------------------------------------------------
-- (c)  THEREFORE the gate that permits growth must REQUIRE separation.
--      Stated as the implication it is.
--------------------------------------------------------------------------

record GrowthGate (Term Env Value : Type₀) : Type₀ where
  constructor gate
  field
    probes    : List (Probe Env Value)   -- the round's assignments, with the
                                         -- values it probed them against
    values    : Discrete Value           -- fingerprint equality is decidable
    reading   : Fingerprint Term Env Value
    separated : Separates (obsOf values reading) probes

open GrowthGate public

-- (G1)  The gate's content: growth permitted ⇒ the tests separate.
gate-requires-separation :
    {Term Env Value : Type₀} (g : GrowthGate Term Env Value)
  → Separates (obsOf (values g) (reading g)) (probes g)
gate-requires-separation g = separated g

-- (G2)  DO NOT GROW ON A COLLAPSED TEST SET.  If the round can name two
--       distinct terms, no gate with an empty probe list exists.  The
--       distinctness hypothesis is explicit — a machine whose terms are all
--       equal has nothing to separate and nothing to prove.
do-not-grow-on-a-collapsed-test-set :
    {Term Env Value : Type₀}
    (d : Discrete Value) (ev : Fingerprint Term Env Value) (x y : Term)
  → ¬ (x ≡ y) → ¬ Separates (obsOf d ev) []
do-not-grow-on-a-collapsed-test-set d ev x y x≢y sep =
  x≢y (collapsed-tests-force-trivial d ev sep x y)

gate-has-nonempty-tests :
    {Term Env Value : Type₀} (g : GrowthGate Term Env Value) (x y : Term)
  → ¬ (x ≡ y) → ¬ (probes g ≡ [])
gate-has-nonempty-tests g x y x≢y p =
  do-not-grow-on-a-collapsed-test-set (values g) (reading g) x y x≢y
    (subst (Separates (obsOf (values g) (reading g))) p (separated g))

-- (G3)  The positive half: a gate that fires exhibits, for each pair of
--       distinct terms, a probe ON THE LIST that actually tells them apart.
--       (`disagree-witness` is the one new induction; it uses only that
--       Bool has decidable equality.)
disagree-witness :
    {X T : Type₀} (e : Obs X T) (ts : List T) (x y : X)
  → ¬ Agree e ts x y
  → Σ[ t ∈ T ] ((t ∈L ts) × (¬ (e x t ≡ e y t)))
disagree-witness e []       x y na = ⊥.rec (na tt)
disagree-witness e (s ∷ ts) x y na with e x s ≟ e y s
... | no ¬p = s , inl refl , ¬p
... | yes p =
      let r = disagree-witness e ts x y (λ a → na (p , a))
      in fst r , inr (fst (snd r)) , snd (snd r)

gate-exhibits-distinction :
    {Term Env Value : Type₀} (g : GrowthGate Term Env Value) (x y : Term)
  → ¬ (x ≡ y)
  → Σ[ p ∈ Probe Env Value ]
      ((p ∈L probes g)
       × (¬ (obsOf (values g) (reading g) x p ≡ obsOf (values g) (reading g) y p)))
gate-exhibits-distinction g x y x≢y =
  disagree-witness (obsOf (values g) (reading g)) (probes g) x y
    (λ a → x≢y (separated g x y a))

------------------------------------------------------------------------
-- §3.  Γ↝ OVER GROWTH MOVES
--
-- The loop's growth choice is a min-plus selection over neighbouring
-- states: widen the vocabulary, raise the size horizon, retire an unused
-- invented symbol, or stay — each with a recorded cost.  That is
-- `Residual.Γ↝` at this data.
--
-- A `Presentation`'s carrier and operation are INERT here, and that is the
-- honest reading of `CostGeometry`: the maps are the mathematics, the cost
-- is the physics, and every theorem below uses only the weights.  So the
-- presentation of a loop state carries the state and nothing else.
------------------------------------------------------------------------

record LoopState : Type₀ where
  constructor state
  field
    vocab    : ℕ   -- how many given symbols are in play
    horizon  : ℕ   -- the term-size bound
    invented : ℕ   -- how many symbols the machine named for itself
open LoopState public

data Move : Type₀ where
  stay   : Move
  widen  : Move
  raise  : Move
  retire : Move

apply : Move → LoopState → LoopState
apply stay   s                    = s
apply widen  (state v h i)        = state (suc v) h i
apply raise  (state v h i)        = state v (suc h) i
apply retire (state v h zero)     = state v h zero
apply retire (state v h (suc i))  = state v h i

statePres : LoopState → Presentation
statePres s = pres LoopState (λ a _ → a)

-- A growth move as an edge of the cost geometry: out to the state the move
-- lands in, back to where we stand, with the work a round costs there.
-- `install` and `revert` are the two recorded costs; the Haskell may pass
-- the same number twice.
moveTo : (s : LoopState) → Move → Cost → Cost → Work → Neighbour (statePres s)
moveTo s t install revert w =
  nbr (statePres (apply t s))
      (edge (λ _ → apply t s) install)
      (edge (λ _ → s) revert)
      w

-- The move's target state is recorded in the neighbour it builds.
moveTo-target :
    (s : LoopState) (t : Move) (i o : Cost) (w : Work)
  → there (moveTo s t i o w) ≡ statePres (apply t s)
moveTo-target s t i o w = refl

-- Staying home with no edges to pay for costs exactly the work at home:
-- `route` of the trivial move is the baseline Γ↝ is compared against.
stay-is-the-baseline : (s : LoopState) (w : Work) → route (moveTo s stay 0 0 w) ≡ w
stay-is-the-baseline s w = refl

-- THE CHOOSER.  `wHere` is the work a round costs in the current state;
-- `ns` is the list of moves on offer, each already an edge with its cost.
choose : (s : LoopState) → Work → List (Neighbour (statePres s)) → Cost
choose s wHere ns = Γ↝ wHere ns

-- (Γ1)  IT NEVER PICKS SOMETHING WORSE THAN STAYING.
choose-never-worse :
    (s : LoopState) (wHere : Work) (ns : List (Neighbour (statePres s)))
  → choose s wHere ns ≤ wHere
choose-never-worse s wHere ns = Γ↝-never-worse wHere ns

-- (Γ2)  It is below every move on the list …
choose-optimal :
    (s : LoopState) (wHere : Work) (ns : List (Neighbour (statePres s)))
    (n : Neighbour (statePres s)) → n ∈ ns
  → choose s wHere ns ≤ route n
choose-optimal s wHere ns n m = Γ↝-optimal wHere ns n m

-- … and it is the GREATEST such bound, so `choose` IS the minimum of
-- {stay} ∪ {the listed moves}, certified as a minimum.
choose-greatest :
    (s : LoopState) (wHere : Work) (ns : List (Neighbour (statePres s))) (c : Cost)
  → c ≤ wHere
  → ((n : Neighbour (statePres s)) → n ∈ ns → c ≤ route n)
  → c ≤ choose s wHere ns
choose-greatest s wHere ns c home away = Γ↝-greatest wHere ns c home away

-- (Γ3)  WHEN IT STRICTLY WINS IT EXHIBITS A LISTED MOVE THAT IS STRICTLY
--       CHEAPER.  The witness is IN the list that was searched — this is
--       `ResidualPath.Γ↝-sound-member`, which is falsifiable by an
--       implementation that returns a move it did not look at.
choose-exhibits-listed-move :
    (s : LoopState) (wHere : Work) (ns : List (Neighbour (statePres s)))
  → choose s wHere ns < wHere
  → Σ[ n ∈ Neighbour (statePres s) ] ((n ∈ ns) × (work n < wHere))
choose-exhibits-listed-move s wHere ns lt' = Γ↝-sound-member wHere ns lt'

-- The provenance of a listed neighbour — that it was built by one of the
-- four moves — is a fact about how the Haskell assembled the list, so it is
-- an explicit hypothesis, not an assumption.
Listed : (s : LoopState) → Neighbour (statePres s) → Type₁
Listed s n =
  Σ[ t ∈ Move ] Σ[ i ∈ Cost ] Σ[ o ∈ Cost ] Σ[ w ∈ Work ] (moveTo s t i o w ≡ n)

-- (Γ4)  With that hypothesis supplied, the winner comes back tagged: the
--       machine knows WHICH of widen / raise / retire / stay it took.
choose-exhibits-tagged-move :
    (s : LoopState) (wHere : Work) (ns : List (Neighbour (statePres s)))
  → ((n : Neighbour (statePres s)) → n ∈ ns → Listed s n)
  → choose s wHere ns < wHere
  → Σ[ n ∈ Neighbour (statePres s) ] ((n ∈ ns) × Listed s n × (work n < wHere))
choose-exhibits-tagged-move s wHere ns prov lt' =
  fst r , fst (snd r) , prov (fst r) (fst (snd r)) , snd (snd r)
  where
    r : Σ[ n ∈ Neighbour (statePres s) ] ((n ∈ ns) × (work n < wHere))
    r = choose-exhibits-listed-move s wHere ns lt'

-- A convenience for the Haskell: it hands a list of move descriptions and
-- gets the neighbour list, with membership transported forward.
record GrowthMove : Type₀ where
  constructor gmove
  field
    tag     : Move
    install : Cost
    revert  : Cost
    after   : Work   -- the work a round costs once the move is taken
open GrowthMove public

nbrOf : (s : LoopState) → GrowthMove → Neighbour (statePres s)
nbrOf s m = moveTo s (tag m) (install m) (revert m) (after m)

nbrs : (s : LoopState) → List GrowthMove → List (Neighbour (statePres s))
nbrs s []       = []
nbrs s (m ∷ ms) = nbrOf s m ∷ nbrs s ms

∈-nbrs :
    {ms : List GrowthMove} (s : LoopState) (m : GrowthMove)
  → m ∈ ms → nbrOf s m ∈ nbrs s ms
∈-nbrs s m (here p)  = here (cong (nbrOf s) p)
∈-nbrs s m (later a) = later (∈-nbrs s m a)

-- Every listed neighbour of `nbrs s ms` is `Listed`, by construction.
nbrs-Listed : (s : LoopState) (m : GrowthMove) → Listed s (nbrOf s m)
nbrs-Listed s m = tag m , install m , revert m , after m , refl

-- The chooser at a move list: same three theorems, phrased where the
-- Haskell states them.
chooseMoves : (s : LoopState) → Work → List GrowthMove → Cost
chooseMoves s wHere ms = choose s wHere (nbrs s ms)

chooseMoves-never-worse :
    (s : LoopState) (wHere : Work) (ms : List GrowthMove)
  → chooseMoves s wHere ms ≤ wHere
chooseMoves-never-worse s wHere ms = choose-never-worse s wHere (nbrs s ms)

chooseMoves-optimal :
    (s : LoopState) (wHere : Work) (ms : List GrowthMove) (m : GrowthMove)
  → m ∈ ms → chooseMoves s wHere ms ≤ route (nbrOf s m)
chooseMoves-optimal s wHere ms m mem =
  choose-optimal s wHere (nbrs s ms) (nbrOf s m) (∈-nbrs s m mem)

chooseMoves-exhibits-listed-move :
    (s : LoopState) (wHere : Work) (ms : List GrowthMove)
  → chooseMoves s wHere ms < wHere
  → Σ[ n ∈ Neighbour (statePres s) ] ((n ∈ nbrs s ms) × (work n < wHere))
chooseMoves-exhibits-listed-move s wHere ms lt' =
  choose-exhibits-listed-move s wHere (nbrs s ms) lt'

------------------------------------------------------------------------
--
-- Claimed.  Three decision rules of `machine/MathMachine.hs` (absent from this repository) now name a
-- checked statement rather than a comment:
--
--   round classification / "need not grow"
--       `flow-total`, `flow-unique`, `flow-decay→drop`,
--       `flow-resonance→same`, `flow-branching→rise`,
--       `decay-closes-without-growth`
--   the growth gate's separation clause
--       `defect-monotone-in-assignments`, `collapsed-tests-agree`,
--       `do-not-grow-on-a-collapsed-test-set`, `gate-exhibits-distinction`
--   the growth chooser
--       `choose-never-worse`, `choose-optimal`, `choose-greatest`,
--       `choose-exhibits-listed-move`
--
------------------------------------------------------------------------

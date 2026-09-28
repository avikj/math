{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- InvariantTiebreakIsExactlyAFixedPoint_TransitivityIsFree
--            TotalityIsNotAndTheHLevelDecidesUniquenessNotExistence
--
-- ON THE NAME.  The objects here are group actions, invariant orders,
-- and h-levels.  Group actions and invariant orders are nineteenth- and
-- twentieth-century European algebra; h-levels are Voevodsky's, which
-- CLAUDE.md (absent from this repository) names as the substrate exception.  There is no Indian source
-- for this material and no  label is invented for it, per
-- CLAUDE.md (absent from this repository) file-naming note 2.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS SETTLES
--
-- Two modules, written independently of each other:
--
--   j-0,
--     `InvariantTiebreak_AGaugeFreeShortestDescriptionWouldBeAFixedPoint
--      SoNoneExistsOnATorsor.agda` (absent from this repository), theorem `leastIsFixed`.
--
--   j-2,
--     `MatraVrtta_TheLeastVarnaIsFixedByTheMatraCountAndNoLeastPatternIs
--      .agda`, answering (about its own object) "the h-level of the
--     question decides", with `leastVarnaAt3-unique` on the descending
--     side and `leastPatternsAt3-notProp` / `noRetrogradeChooser` on the
--     blocked side.
--
-- Both modules are IMPORTED here, unmodified, and every claim below is
-- about their actual terms.
--
--  §2  `canonical→tiebreak`.  THE CONVERSE OF `leastIsFixed`.  From a
--      single fixed point `m` the relation `x ≼ y :≡ (x ≡ m)` is
--      antisymmetric, has least element `m`, and is action-monotone.  So
--
--          InvariantTiebreak A ℓ'   ⟺   Canonical A
--
--      (`tiebreakIffCanonical`), with ℓ' the level of the carrier.  The
--      tiebreak axioms carry NO order-theoretic content beyond the bare
--      existence of a fixed point.
--
--  §3  `canonical→transitiveTiebreak`.  TRANSITIVITY IS FREE.  The same
--      relation is transitive, so the class of actions admitting a
--      TRANSITIVE invariant tiebreak is the same class again
--      (`transitiveTiebreakIffCanonical`).  j-0's guess that transitivity
--      is the deciding property is refuted: adding it changes nothing.
--
--  §4  `totalInvolutionFixed`.  TOTALITY IS NOT FREE, and it is the
--      hypothesis that actually separates.  A TOTAL antisymmetric
--      action-monotone relation forces every point to be fixed by every
--      involutive group element — no least element required.  Hence
--      `oneNoTotalTiebreak`: j-0's own `oneAct` (Bool acting on Four by
--      the transposition (ab), fixing c and d) admits an invariant
--      tiebreak, because it has a fixed point, and admits NO total one.
--      That is a strict separation inside j-0's own §5 table.
--
--  §5  `leastIsFixedFromSplitSurjectivity`.  `leastIsFixed` needs no
--      group: it needs each `g ▸ _` to be SPLIT SURJECTIVE, which
--      `▸-inv` supplies (`actionIsSplitSurjective`).  And it needs that:
--      §5.2 exhibits a monoid action (`step`, on a three-element
--      carrier, with `step true` constant) carrying an antisymmetric
--      monotone relation with a least element whose least element is NOT
--      fixed.  So `leastIsFixed` is not a formal triviality; it consumes
--      invertibility exactly once, and only through surjectivity.
--
--  §6  THE H-LEVEL DOES NOT DECIDE EXISTENCE.  Three checked cells:
--        `xorCanonicalIsProp`      + `xorNoFixed`      — prop, empty
--        `swCanonicalIsProp`       + `swCanonical`     — prop, inhabited
--        `oneCanonicalNotProp`     + `oneCanonical`    — not prop, inhabited
--      (the fourth cell is uninhabitable: an empty type is a
--      proposition.)  So proposition-valuedness neither implies nor is
--      implied by the existence of an equivariant selection.  What IS
--      true is the bridge `transitiveCanonicalIsProp`: on a set carrier
--      TRANSITIVITY of the action makes the selection question
--      proposition-valued.  j-0's guess and j-2's answer meet exactly
--      there — and the implication runs the wrong way to decide
--      existence, which is why `xorAct` is transitive, prop-valued, and
--      has no answer.
--
--  §7  THE RELATIONSHIP, SETTLED.  Both theorems are instances of one
--      trivial schema `viaCanonical : (X → Canonical A) → ¬ Canonical A
--      → ¬ X`; all the content is in the map `X → Canonical A`.  For j-2
--      that map is a PROJECTION — fixedness is a field of
--      `EquivariantLeastChoice`, so `equivariantChoiceIsAFixedPoint`
--      uses no hypothesis on σ at all (`selectionIsFixedByAssumption`
--      reproduces it with no structure whatsoever).  For j-0 it is a
--      DERIVATION consuming `▸-inv`.  And they are INCOMPARABLE: §7.2
--      instantiates j-2's own general `Formation.Symmetry` at a σ that
--      is NOT split surjective, where `noEquivariantLeastChoice` still
--      fires and `leastIsFixedFromSplitSurjectivity` provably cannot.
--
--      The generalisation claim fails on that witness.  It survives
--      on j-2's own
--      instance only — `rev` is an involution, hence split surjective
--      (`revIsSplitSurjective`) — and fails in the generality j-2 proved
--      the theorem in.
------------------------------------------------------------------------

module InvariantTiebreakIsExactlyAFixedPoint_TransitivityIsFreeTotalityIsNotAndTheHLevelDecidesUniquenessNotExistence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (znots ; snotz ; injSuc)
open import Cubical.Data.Nat.Order using (_≤_ ; zero-≤)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Bool.Properties using (isSetBool)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.List using (List ; rev)
open import Cubical.Data.List.Properties using (rev-rev)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; Σ≡Prop)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_ ; Discrete ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

-- j-0's module, opened: `Act`, `Fixed`, `Canonical`, `Transitive`,
-- `InvariantTiebreak`, `leastIsFixed`, `Invol`, and the §5 witnesses.
open import InvariantTiebreak_AGaugeFreeShortestDescriptionWouldBeAFixedPointSoNoneExistsOnATorsor
  as J0

-- j-2's module, qualified only, so nothing of it is shadowed.
import MatraVrtta_TheLeastVarnaIsFixedByTheMatraCountAndNoLeastPatternIs
  as J2

private
  variable
    ℓG ℓC ℓR : Level

------------------------------------------------------------------------
-- §1.  The common target.
--
-- Both agents' negative results have the shape "no X, because X would
-- give a fixed point and there is none".  That shape is one line and it
-- is where the two theorems agree; everything that distinguishes them
-- lives in the map `X → Canonical A`, which §7 measures.
------------------------------------------------------------------------

viaCanonical :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C} {X : Type ℓR}
  → (X → Canonical A) → ¬ (Canonical A) → ¬ X
viaCanonical f nc x = nc (f x)

-- j-0's `noFixed→noInvariantTiebreak` is this schema at
-- `X = InvariantTiebreak A ℓR`, with `tiebreak→canonical` as the map.
j0-is-an-instance :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → ¬ (Canonical A) → ¬ (InvariantTiebreak A ℓR)
j0-is-an-instance {A = A} = viaCanonical {A = A} tiebreak→canonical

------------------------------------------------------------------------
-- §2.  An invariant tiebreak is EXACTLY a fixed point.
--
-- j-0 proves `InvariantTiebreak A ℓ'' → Canonical A` for every ℓ''.  The
-- converse holds at the carrier's own level, and it is three lines.  The
-- relation `x ≼ y :≡ (x ≡ m)` ignores its second argument entirely — it
-- is degenerate, and that degeneracy IS the content: the axiom list
-- cannot be strengthened by anything it does not already imply.
------------------------------------------------------------------------

fixed→tiebreak :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  (m : C) → Fixed A m → InvariantTiebreak A ℓC
fixed→tiebreak {A = A} m fix = record
  { _≼_     = λ x _ → x ≡ m
  ; antisym = λ x y p q → p ∙ sym q
  ; least   = m
  ; isLeast = λ _ → refl
  ; mono    = λ g x y p → cong (Act._▸_ A g) p ∙ fix g
  }

canonical→tiebreak :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → Canonical A → InvariantTiebreak A ℓC
canonical→tiebreak (m , fix) = fixed→tiebreak m fix

-- The two notions are logically equivalent.
tiebreakIffCanonical :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → (InvariantTiebreak A ℓC → Canonical A)
  × (Canonical A → InvariantTiebreak A ℓC)
tiebreakIffCanonical = tiebreak→canonical , canonical→tiebreak

------------------------------------------------------------------------
-- §3.  Transitivity is FREE.  (Settling j-0's guess, negatively.)
--
-- j-0 records, correctly and as a strength, that `leastIsFixed` uses no
-- transitivity.  The reason it can afford not to is not that
-- transitivity is a weak hypothesis in general — it is that on THIS
-- axiom list transitivity is already available for nothing, so assuming
-- it cuts the class of actions down by exactly zero.
------------------------------------------------------------------------

record TransitiveTiebreak
         {G : Type ℓG} {C : Type ℓC} (A : Act G C) (ℓR : Level)
       : Type (ℓ-max (ℓ-max ℓG ℓC) (ℓ-suc ℓR)) where
  open Act A
  field
    _≼_     : C → C → Type ℓR
    antisym : (x y : C) → x ≼ y → y ≼ x → x ≡ y
    trans   : (x y z : C) → x ≼ y → y ≼ z → x ≼ z
    least   : C
    isLeast : (c : C) → least ≼ c
    mono    : (g : G) (x y : C) → x ≼ y → (g ▸ x) ≼ (g ▸ y)

forgetTransitivity :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → TransitiveTiebreak A ℓR → InvariantTiebreak A ℓR
forgetTransitivity t = record
  { _≼_     = TransitiveTiebreak._≼_ t
  ; antisym = TransitiveTiebreak.antisym t
  ; least   = TransitiveTiebreak.least t
  ; isLeast = TransitiveTiebreak.isLeast t
  ; mono    = TransitiveTiebreak.mono t
  }

canonical→transitiveTiebreak :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → Canonical A → TransitiveTiebreak A ℓC
canonical→transitiveTiebreak {A = A} (m , fix) = record
  { _≼_     = λ x _ → x ≡ m
  ; antisym = λ x y p q → p ∙ sym q
  ; trans   = λ x y z p _ → p
  ; least   = m
  ; isLeast = λ _ → refl
  ; mono    = λ g x y p → cong (Act._▸_ A g) p ∙ fix g
  }

-- Same class of actions, before and after transitivity.
transitiveTiebreakIffCanonical :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → (TransitiveTiebreak A ℓC → Canonical A)
  × (Canonical A → TransitiveTiebreak A ℓC)
transitiveTiebreakIffCanonical =
  (λ t → tiebreak→canonical (forgetTransitivity t)) , canonical→transitiveTiebreak

------------------------------------------------------------------------
-- §4.  Totality is NOT free, and it is the separating hypothesis.
--
-- Note what this theorem does NOT need: no least element, no
-- transitivity, no finiteness, no decidability.  It needs the group
-- element to be involutive, and it needs the relation to be total.
------------------------------------------------------------------------

record TotalTiebreak
         {G : Type ℓG} {C : Type ℓC} (A : Act G C) (ℓR : Level)
       : Type (ℓ-max (ℓ-max ℓG ℓC) (ℓ-suc ℓR)) where
  open Act A
  field
    _≼_     : C → C → Type ℓR
    antisym : (x y : C) → x ≼ y → y ≼ x → x ≡ y
    total   : (x y : C) → (x ≼ y) ⊎ (y ≼ x)
    mono    : (g : G) (x y : C) → x ≼ y → (g ▸ x) ≼ (g ▸ y)

totalInvolutionFixed :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  (t : TotalTiebreak A ℓR) (g : G)
  → ((y : C) → Act._▸_ A g (Act._▸_ A g y) ≡ y)
  → (x : C) → Act._▸_ A g x ≡ x
totalInvolutionFixed {A = A} t g invol x = decide (total x (g ▸ x))
  where
    open Act A
    open TotalTiebreak t
    decide : ((x ≼ (g ▸ x)) ⊎ ((g ▸ x) ≼ x)) → (g ▸ x) ≡ x
    decide (inl p) =
      sym (antisym x (g ▸ x) p
            (subst (λ z → (g ▸ x) ≼ z) (invol x) (mono g x (g ▸ x) p)))
    decide (inr p) =
      antisym (g ▸ x) x p
        (subst (λ z → z ≼ (g ▸ x)) (invol x) (mono g (g ▸ x) x p))

-- 4.1  On j-0's `oneAct` — Bool acting on Four by (ab), fixing c and d —
--      an invariant tiebreak EXISTS and a total one does NOT.

oneNoTotalTiebreak : ¬ (TotalTiebreak oneAct ℓR)
oneNoTotalTiebreak t = b≢a (totalInvolutionFixed t true swapOne-invol a)

oneHasTiebreak : InvariantTiebreak oneAct ℓ-zero
oneHasTiebreak = canonical→tiebreak oneCanonical

oneSeparatesTotalityFromLeastness :
  (InvariantTiebreak oneAct ℓ-zero) × (¬ (TotalTiebreak oneAct ℓ-zero))
oneSeparatesTotalityFromLeastness = oneHasTiebreak , oneNoTotalTiebreak

-- 4.2  On `xorAct` totality fails too, but for the reason j-0 already
--      has (no fixed point at all).  Recorded so the separation in 4.1 is
--      seen to be the informative one: `xorAct` fails both tests,
--      `oneAct` passes one and fails the other.

xorNoTotalTiebreak : ¬ (TotalTiebreak xorAct ℓR)
xorNoTotalTiebreak t = f≢t (sym (totalInvolutionFixed t true notB-invol false))

------------------------------------------------------------------------
-- §5.  What `leastIsFixed` actually consumes: split surjectivity.
------------------------------------------------------------------------

-- 5.1  The group-free form of j-0's theorem.

record BareTiebreak
         {G : Type ℓG} {C : Type ℓC} (_▸_ : G → C → C) (ℓR : Level)
       : Type (ℓ-max (ℓ-max ℓG ℓC) (ℓ-suc ℓR)) where
  field
    _≼_     : C → C → Type ℓR
    antisym : (x y : C) → x ≼ y → y ≼ x → x ≡ y
    least   : C
    isLeast : (c : C) → least ≼ c
    mono    : (g : G) (x y : C) → x ≼ y → (g ▸ x) ≼ (g ▸ y)

SplitSurjective : {G : Type ℓG} {C : Type ℓC} → (G → C → C) → Type (ℓ-max ℓG ℓC)
SplitSurjective {G = G} {C = C} _▸_ = (g : G) (c : C) → Σ[ x ∈ C ] (g ▸ x ≡ c)

leastIsFixedFromSplitSurjectivity :
  {G : Type ℓG} {C : Type ℓC} {_▸_ : G → C → C}
  (t : BareTiebreak _▸_ ℓR) → SplitSurjective _▸_
  → (g : G) → (_▸_ g (BareTiebreak.least t)) ≡ BareTiebreak.least t
leastIsFixedFromSplitSurjectivity {_▸_ = _▸_} t surj g =
  antisym (g ▸ least) least
    (subst (λ z → (g ▸ least) ≼ z) (snd (surj g least))
           (mono g least (fst (surj g least)) (isLeast (fst (surj g least)))))
    (isLeast (g ▸ least))
  where open BareTiebreak t

-- Every action map of a group action is split surjective: that is
-- literally what `▸-inv` says, read as a section.
actionIsSplitSurjective :
  {G : Type ℓG} {C : Type ℓC} (A : Act G C) → SplitSurjective (Act._▸_ A)
-- (the bound point is named `y`: j-0's `Four` exports constructors
-- `a b c d`, and `c` on a left-hand side would be read as one of them.)
actionIsSplitSurjective A g y = Act.inv A g ▸ y , Act.▸-inv A g y
  where open Act A

tiebreak→bare :
  {G : Type ℓG} {C : Type ℓC} (A : Act G C)
  → InvariantTiebreak A ℓR → BareTiebreak (Act._▸_ A) ℓR
tiebreak→bare A t = record
  { _≼_     = InvariantTiebreak._≼_ t
  ; antisym = InvariantTiebreak.antisym t
  ; least   = InvariantTiebreak.least t
  ; isLeast = InvariantTiebreak.isLeast t
  ; mono    = InvariantTiebreak.mono t
  }

-- j-0's `leastIsFixed`, re-derived through the weaker hypothesis.  This
-- is not a re-landing: it is the demonstration that the group was only
-- ever used through surjectivity.
leastIsFixedReprovedWithoutTheGroup :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  (t : InvariantTiebreak A ℓR) → Fixed A (InvariantTiebreak.least t)
leastIsFixedReprovedWithoutTheGroup {A = A} t =
  leastIsFixedFromSplitSurjectivity (tiebreak→bare A t) (actionIsSplitSurjective A)

-- 5.2  …and the hypothesis is necessary.  A monoid acting on three
--      points, with the non-identity element acting as the constant map
--      at `th1`, carries an antisymmetric monotone relation with a least
--      element `th0` that is NOT fixed.

data Three : Type where
  th0 th1 th2 : Three

code₃ : Three → ℕ
code₃ th0 = 0
code₃ th1 = 1
code₃ th2 = 2

th0≢th1 : ¬ (th0 ≡ th1)
th0≢th1 p = znots (cong code₃ p)

th1≢th0 : ¬ (th1 ≡ th0)
th1≢th0 p = snotz (cong code₃ p)

th0≢th2 : ¬ (th0 ≡ th2)
th0≢th2 p = znots (cong code₃ p)

th2≢th0 : ¬ (th2 ≡ th0)
th2≢th0 p = snotz (cong code₃ p)

th1≢th2 : ¬ (th1 ≡ th2)
th1≢th2 p = znots (injSuc (cong code₃ p))

th2≢th1 : ¬ (th2 ≡ th1)
th2≢th1 p = snotz (injSuc (cong code₃ p))

discreteThree : Discrete Three
discreteThree th0 th0 = yes refl
discreteThree th0 th1 = no th0≢th1
discreteThree th0 th2 = no th0≢th2
discreteThree th1 th0 = no th1≢th0
discreteThree th1 th1 = yes refl
discreteThree th1 th2 = no th1≢th2
discreteThree th2 th0 = no th2≢th0
discreteThree th2 th1 = no th2≢th1
discreteThree th2 th2 = yes refl

isSetThree : isSet Three
isSetThree = Discrete→isSet discreteThree

-- The monoid: `false` acts as the identity, `true` as the constant map.
step : Bool → Three → Three
step false x = x
step true  _ = th1

-- It is a monoid action for the ordinary Boolean "or" multiplication…
stepMult : Bool → Bool → Bool
stepMult false h = h
stepMult true  _ = true

step-e : (x : Three) → step false x ≡ x
step-e x = refl

step-· : (g h : Bool) (x : Three) → step (stepMult g h) x ≡ step g (step h x)
step-· false h     x = refl
step-· true  false x = refl
step-· true  true  x = refl

-- …and it is not split surjective: nothing is carried to `th2`.
stepNotSplitSurjective : ¬ (SplitSurjective step)
stepNotSplitSurjective surj = reach (surj true th2)
  where
    reach : Σ[ x ∈ Three ] (step true x ≡ th2) → ⊥
    reach (th0 , p) = th1≢th2 p
    reach (th1 , p) = th1≢th2 p
    reach (th2 , p) = th1≢th2 p

_≼₃_ : Three → Three → Type
th0 ≼₃ _   = Unit
th1 ≼₃ th0 = ⊥
th1 ≼₃ th1 = Unit
th1 ≼₃ th2 = ⊥
th2 ≼₃ _   = ⊥

antisym₃ : (x y : Three) → x ≼₃ y → y ≼₃ x → x ≡ y
antisym₃ th0 th0 _  _  = refl
antisym₃ th0 th1 _  ()
antisym₃ th0 th2 _  ()
antisym₃ th1 th0 () _
antisym₃ th1 th1 _  _  = refl
antisym₃ th1 th2 () _
antisym₃ th2 y   () _

mono₃ : (g : Bool) (x y : Three) → x ≼₃ y → step g x ≼₃ step g y
mono₃ false x y p = p
mono₃ true  x y p = tt

bareTiebreak₃ : BareTiebreak step ℓ-zero
bareTiebreak₃ = record
  { _≼_     = _≼₃_
  ; antisym = antisym₃
  ; least   = th0
  ; isLeast = λ _ → tt
  ; mono    = mono₃
  }

-- THE POINT.  Least, and not fixed.  So `leastIsFixed` is not formal:
-- drop surjectivity and the conclusion is false.
leastIsNotFixedWithoutSurjectivity :
  ¬ (step true (BareTiebreak.least bareTiebreak₃) ≡ BareTiebreak.least bareTiebreak₃)
leastIsNotFixedWithoutSurjectivity = th1≢th0

------------------------------------------------------------------------
-- §6.  The h-level decides uniqueness, not existence.
--
-- j-2's theorems are correct and this section does not touch them.  The
-- h-level of the goal is not the obstruction j-0's `leastIsFixed` is
-- measuring: the
-- two axes are independent, and every inhabited cell is exhibited.
------------------------------------------------------------------------

-- 6.1  THE BRIDGE, which is real: transitivity makes the selection
--      question proposition-valued.  This is where j-0's guess and j-2's
--      answer actually meet.
--
--      COUSIN, CITED NOT RE-LANDED.  `NaturalMachine.StabilizerTorsor`
--      already carries an h-level statement of this family:
--      `contrStab→uniqueCertificate : isContr (Stab x) → isProp (T x y)`
--      — a trivial stabilizer makes the TRANSPORTER type a proposition.
--      That is a different object (transporters `T x y`, not the
--      fixed-point type `Canonical A`) and a different hypothesis
--      (contractible stabilizer, not transitivity), so the statement
--      below is not that one; but the pattern "a group-theoretic
--      hypothesis collapses a selection type to a proposition" is that
--      module's, and it is credited here.

transitiveCanonicalIsProp :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C}
  → isSet C → Transitive A → isProp (Canonical A)
transitiveCanonicalIsProp {A = A} setC tr u v =
  Σ≡Prop (λ x → isPropΠ (λ g → setC (Act._▸_ A g x) x))
         (transitiveFixed→allEqual A tr (fst v) (snd v) (fst u))

-- 6.2  CELL (prop, empty).  `xorAct` is transitive, so by the bridge the
--      question is proposition-valued — and j-0 already proved it has no
--      answer.  Proposition-valuedness does NOT deliver existence.

xorCanonicalIsProp : isProp (Canonical xorAct)
xorCanonicalIsProp = transitiveCanonicalIsProp {A = xorAct} isSetBool xorTransitive

xorPropAndEmpty : (isProp (Canonical xorAct)) × (¬ (Canonical xorAct))
xorPropAndEmpty = xorCanonicalIsProp , xorNoFixed

-- 6.3  CELL (not prop, inhabited).  `oneAct` has TWO fixed points, so the
--      question is structure-valued — and it has an answer anyway.
--      Failure of proposition-valuedness does NOT block existence.

oneCanonicalNotProp : ¬ (isProp (Canonical oneAct))
oneCanonicalNotProp isP =
  c≢d (cong fst (isP (c , oneCanonicalC) (d , oneCanonicalD)))

oneNotPropAndInhabited : (¬ (isProp (Canonical oneAct))) × (Canonical oneAct)
oneNotPropAndInhabited = oneCanonicalNotProp , oneCanonical

-- 6.4  CELL (prop, inhabited), witnessed by a NON-trivial action, so the
--      cell is not filled by cheating with the trivial group: Bool acts
--      on Three by the transposition (th0 th1), fixing exactly `th2`.

swapZO : Three → Three
swapZO th0 = th1
swapZO th1 = th0
swapZO th2 = th2

swapZO-invol : (x : Three) → swapZO (swapZO x) ≡ x
swapZO-invol th0 = refl
swapZO-invol th1 = refl
swapZO-invol th2 = refl

module Sw = Invol Three swapZO swapZO-invol

swAct : Act Bool Three
swAct = Sw.A

swFaithful : ¬ (swapZO th0 ≡ th0)
swFaithful = th1≢th0

swCanonical : Canonical swAct
swCanonical = th2 , Sw.fixed-from-f th2 refl

swAllFixedIsTh2 : (x : Three) → Fixed swAct x → x ≡ th2
swAllFixedIsTh2 th0 h = ⊥rec (th1≢th0 (Sw.f-from-fixed th0 h))
swAllFixedIsTh2 th1 h = ⊥rec (th0≢th1 (Sw.f-from-fixed th1 h))
swAllFixedIsTh2 th2 h = refl

swCanonicalIsProp : isProp (Canonical swAct)
swCanonicalIsProp u v =
  Σ≡Prop (λ x → isPropΠ (λ g → isSetThree (Act._▸_ swAct g x) x))
         (swAllFixedIsTh2 (fst u) (snd u) ∙ sym (swAllFixedIsTh2 (fst v) (snd v)))

swPropAndInhabited : (isProp (Canonical swAct)) × (Canonical swAct)
swPropAndInhabited = swCanonicalIsProp , swCanonical

-- The fourth cell (not prop, empty) is uninhabitable, since
-- an empty type is a proposition; the three that can exist all do.

------------------------------------------------------------------------
-- §7.  The relationship between the two theorems, settled.
------------------------------------------------------------------------

-- 7.1  j-2's move needs no structure at all.  `EquivariantLeastChoice`
--      carries `σ (pick e n) ≡ pick e n` as a FIELD, so
--      `equivariantChoiceIsAFixedPoint` is a projection.  Here is that
--      projection with every hypothesis on the symmetry removed — it
--      still goes through, which is the measurement.

selectionIsFixedByAssumption :
  {G : Type ℓG} {C : Type ℓC} {A : Act G C} {I : Type ℓR}
  → Σ[ pick ∈ (I → C) ] ((i : I) → Fixed A (pick i))
  → I → Canonical A
selectionIsFixedByAssumption (pick , fx) i = pick i , fx i

-- By contrast `leastIsFixedFromSplitSurjectivity` (§5) cannot be written
-- without `surj`, and §5.2 is the witness that it cannot.

-- 7.2  THE SEPARATING WITNESS.  j-2's `Formation.Symmetry` requires only
--      `σ-ev` and `σ-c`; σ need not be invertible, injective, or
--      surjective.  Instantiate it at a σ that is none of those.  The
--      formation: histories `Three`, one endpoint, constant cost.

module F3 = J2.Formation {W = Three} {E = Unit} (λ _ → tt) (λ _ → 0)

nonSurj : Three → Three
nonSurj th0 = th1
nonSurj th1 = th0
nonSurj th2 = th0

module S3 = F3.Symmetry nonSurj (λ _ → refl) (λ _ → refl)

nonSurjIsNotSplitSurjective : ¬ ((c : Three) → Σ[ x ∈ Three ] (nonSurj x ≡ c))
nonSurjIsNotSplitSurjective surj = reach (surj th2)
  where
    reach : Σ[ x ∈ Three ] (nonSurj x ≡ th2) → ⊥
    reach (th0 , p) = th1≢th2 p
    reach (th1 , p) = th0≢th2 p
    reach (th2 , p) = th0≢th2 p

leastHere : F3.IsLeast tt 0
leastHere = ∣ th0 , refl , refl ∣₁ , (λ _ _ → zero-≤)

noWitnessIsFixed : (w : Three) → F3.Witness tt 0 w → ¬ (nonSurj w ≡ w)
noWitnessIsFixed th0 _ p = th1≢th0 p
noWitnessIsFixed th1 _ p = th0≢th1 p
noWitnessIsFixed th2 _ p = th0≢th2 p

-- j-2's theorem fires here…
noChoiceOnANonSurjectiveSymmetry : ¬ S3.EquivariantLeastChoice
noChoiceOnANonSurjectiveSymmetry =
  S3.noEquivariantLeastChoice tt 0 leastHere noWitnessIsFixed

-- …and j-0's cannot, because every action map of a group action is split
-- surjective (`actionIsSplitSurjective`) and this one is not.  Packaged:
theGeneralisationClaimIsWithdrawn :
  (¬ S3.EquivariantLeastChoice)
  × (¬ ((c : Three) → Σ[ x ∈ Three ] (nonSurj x ≡ c)))
theGeneralisationClaimIsWithdrawn =
  noChoiceOnANonSurjectiveSymmetry , nonSurjIsNotSplitSurjective

-- 7.3  …and on j-2's OWN instance the claim survives in substance,
--      because retrogradation is an involution and hence split
--      surjective.

revIsSplitSurjective :
  {ℓ : Level} {A : Type ℓ} (q : List A) → Σ[ p ∈ List A ] (rev p ≡ q)
revIsSplitSurjective q = rev q , rev-rev q

-- j-2's landed negative, cited unchanged, so this module is checked
-- against the real term and not against a restatement of it.
j2LandedNegative : ¬ J2.EquivariantLeastChoice
j2LandedNegative = J2.noRetrogradeChooser

------------------------------------------------------------------------
-- §8.  REMARKS.
--
--  * WHY totality is the right dividing line in general.  §4 proves it
--    for INVOLUTIVE group elements.  For a group element of infinite
--    order the argument does not run: ℤ acting on ℤ by translation
--    carries the usual order — total, antisymmetric, transitive,
--    monotone - with no fixed point and no least element.
--
--  * WHETHER `leastIsFixed` is a corollary of `noEquivariantLeastChoice`
--    in the WEAK sense of being re-derivable by a detour.  It is: given
--    an equivariant `pick`, the relation `x ≼ y :≡ (x ≡ pick e n)`
--    satisfies §2's axioms.  That detour consumes the equivariance field
--    — which is exactly j-2's proof — so it establishes nothing about
--    relative strength.
------------------------------------------------------------------------

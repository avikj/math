{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- कक्षावतरणम् — the descent to the orbit.
-- (kakṣā, the orbit / the enclosure; avataraṇa, the coming down.)
--
-- ORBIT DESCENT: a set-valued task descends to the orbit set exactly
-- when it is invariant, and coinvariants need no closure lemma.
--
-- SOURCE (quoted verbatim).  `notes/LEAN_TO_CUBICAL_PORT_MAP.md` (absent from this repository) on
-- branch `main`, §3.2:
--
--   ### 3.2 `HolonomyDescent` → `NaturalMachine/OrbitDescent.agda` (absent from this repository) (proposed)
--
--   Imports: `Cubical.HITs.SetQuotients as SQ`, `Cubical.Algebra.Group.Base`,
--   `Cubical.Algebra.AbGroup.Base`, `Cubical.Relation.Binary.Base`,
--   `Cubical.HITs.PropositionalTruncation`.
--
--   ```agda
--   module OrbitDescent {ℓg ℓx} (G : Group ℓg) {X : Type ℓx}
--     (_·_   : ⟨ G ⟩ → X → X)
--     (·-1g  : (x : X) → (GroupStr.1g (snd G)) · x ≡ x)
--     (·-∙   : (g h : ⟨ G ⟩) (x : X) → (GroupStr._·_ (snd G) g h) · x ≡ g · (h · x))
--     where
--
--     OrbitRel : X → X → Type (ℓ-max ℓg ℓx)
--     OrbitRel x y = Σ[ g ∈ ⟨ G ⟩ ] (g · x ≡ y)
--
--     OrbitSet : Type (ℓ-max ℓg ℓx)
--     OrbitSet = X / OrbitRel                    -- raw relation: no setoid proof needed
--
--     orbitMk : X → OrbitSet
--     orbitMk-· : (g : ⟨ G ⟩) (x : X) → orbitMk (g · x) ≡ orbitMk x
--
--     -- Lean: factors_through_orbit_iff (both directions) + orbit_factor_unique,
--     -- fused: descent data is an equivalence of types, uniqueness included.
--     descend : {Y : Type ℓy} (isSetY : isSet Y) (task : X → Y)
--             → ((g : ⟨ G ⟩) (x : X) → task (g · x) ≡ task x)
--             → OrbitSet → Y                      -- SQ.rec; β-rule is refl
--     descend-unique : … → isContr (Σ[ d ∈ (OrbitSet → Y) ] ((x : X) → d (orbitMk x) ≡ task x))
--
--     -- effectivity (needs the equivalence-relation proof, mere-witness form):
--     orbitPath≃∥Rel∥ : (x y : X) → Iso (orbitMk x ≡ orbitMk y) ∥ OrbitRel x y ∥₁
--       -- SQ.isEquivRel→TruncIso; the group laws enter only here
--   ```
--
--   Coinvariants half, for `A : AbGroup ℓa` with action by additive maps
--   (`·-hom : (g : ⟨G⟩)(x y : ⟨A⟩) → g ·A (x + y) ≡ (g ·A x) + (g ·A y)`):
--
--   ```agda
--     DiffRel : ⟨ A ⟩ → ⟨ A ⟩ → Type _
--     DiffRel a b = Σ[ g ∈ ⟨ G ⟩ ] Σ[ x ∈ ⟨ A ⟩ ] (a ≡ b + ((g ·A x) - x))
--
--     Coinv : Type _
--     Coinv = ⟨ A ⟩ / DiffRel                    -- HIT generates the subgroup closure
--
--     _+Q_ : Coinv → Coinv → Coinv               -- SQ.rec2; DiffRel is translation-
--                                                -- invariant, so no closure lemma
--     -Q_  : Coinv → Coinv
--     coinvAbGroup : AbGroup _                   -- laws by SQ.elimProp2/3 from A's laws
--
--     coinvMk-· : (g : ⟨ G ⟩) (x : ⟨ A ⟩) → coinvMk (g ·A x) ≡ coinvMk x
--
--     -- Lean: addHom_factors_through_coinvariants_iff + coinvariant_factor_unique
--     descendHom : (task : AbGroupHom A B)
--                → ((g : ⟨ G ⟩) (x : ⟨ A ⟩) → task .fst (g ·A x) ≡ task .fst x)
--                → AbGroupHom coinvAbGroup B
--     descendHom-unique : …                      -- SQ.elimProp
--   ```
--
--   Port-shorter argument, explicitly: the Lean file spends its entire
--   `Coinvariants` section (≈60 lines) constructing `differenceSubgroup` as an
--   `AddSubgroup.closure`, proving `closure_le` into `task.ker`, and invoking
--   `QuotientAddGroup.lift`/`addMonoidHom_ext`.  In Cubical none of that
--   apparatus exists or is needed: `eq/` on the raw generator relation *is* the
--   closure, and the two universal-property proofs are `SQ.rec`/`SQ.elimProp`
--   applications.
--
-- and its §5 queue entry:
--
--   - `PROVE` (port rank 2): `OrbitDescent.agda` (absent from this repository) per §3.2 — orbit descent +
--     coinvariants on raw HIT quotients; success test: no closure lemma anywhere
--     in the file.
--
-- The Lean original, `formal/lean/Pairfield/HolonomyDescent.lean`, header:
--
--   import Mathlib.GroupTheory.QuotientGroup.Basic
--   import Mathlib.Algebra.GroupWithZero.Action.Basic
--
--   namespace Pairfield.HolonomyDescent
--
--   universe u v w
--
--   section OrbitSet
--
--   variable {G : Type u} [Group G]
--   variable {X : Type v} [MulAction G X]
--
--   /-- Two presentations are identified when a generated holonomy carries one
--   to the other. This is a set quotient; no additive structure is asserted. -/
--   def orbitSetoid : Setoid X where
--     r x y := ∃ g : G, g • x = y
--
-- Its theorems are `orbitMk_smul`, `factors_through_orbit_iff`,
-- `orbit_factor_unique`, `coinvariantMk_smul`,
-- `addHom_factors_through_coinvariants_iff`, `coinvariant_factor_unique`.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--
-- Module `OrbitDescent` (G a group, X any type, action `_·_` with the
-- unit and composition laws as hypotheses, exactly the sketch's header):
--
--   T1  `OrbitRel`, `OrbitSet = X / OrbitRel` (raw relation), `orbitMk`,
--       `orbitMk-·`  — the last is one `eq/`.
--   T2  `descend`  (SQ.rec) and `descend-β` — the β-rule is `refl`.
--   T3  `descend-unique` : the descent data of an invariant task is
--       CONTRACTIBLE (SQ.elimProp for the uniqueness, `isSet Y`).
--   T4  `restrict-invariant` (the converse: anything of the form
--       `d ∘ orbitMk` is invariant), and `descendsIso` / `descends≃` :
--       `Descends task ≃ Invariant task` — the Lean iff, as an
--       equivalence of types, `Y` a set.
--   T5  `orbitRel-isEquivRel` (reflexivity from `·-1g`, symmetry from
--       `·-∙` + `·InvL`, transitivity from `·-∙`) and
--       `orbitPath≃∥Rel∥ : Iso (orbitMk x ≡ orbitMk y) ∥ OrbitRel x y ∥₁`
--       by the library's `SQ.isEquivRel→TruncIso`.  The group laws are
--       used HERE AND NOWHERE ELSE in the orbit half; T1–T4 never touch
--       them (Agda would reject an unused-variable claim silently, so
--       the reader may check: `·-1g`, `·-∙` occur only in T5 and in the
--       controls).
--
-- Module `Coinvariants` (G a group, A an abelian group, action `_·_` by
-- additive maps, hypothesis `·-hom` ONLY — the unit and composition laws
-- of the action are not needed for anything in this half, so they are
-- not assumed; the Lean `DistribMulAction` carries them idly):
--
--   T6  `DiffRel`, `Coinv = ⟨ A ⟩ / DiffRel`, `coinvMk`;
--       `DiffRel-+R`, `DiffRel-+L` (translation invariance, one
--       abelian-group identity each), `DiffRel-neg` (needs `·-hom`,
--       through `presinv`); `_+Q_` (SQ.rec2), `-Q_` (SQ.setQuotUnaryOp),
--       `0Q`; `coinvAbGroup : AbGroup` with every law by
--       SQ.elimProp/2/3 from A's law; `coinvMkHom : AbGroupHom A
--       coinvAbGroup` (additivity is `refl`); `coinvMk-·`;
--       `descendHom` with `descendHom-β` (`refl`), `descendHom-unique`
--       (contractible), `restrictHom-invariant` (converse), and
--       `descendsHomIso` / `descendsHom≃` : `DescendsHom task ≃
--       InvariantHom task`.
--
-- Nothing of T6 is deferred: the full `AbGroup` structure on `Coinv` is
-- delivered.
--
-- Controls:
--   C1  `UnitControl`: for the trivial group and ANY action on a set X,
--       `orbitMk` is an equivalence (`OrbitSet ≃ X`) — the trivial group
--       identifies nothing.
--   C2  `BoolControl`: ℤ/2 (the library's `BoolGroup`) acting on `Bool`
--       by its own multiplication (`false · b = not b`): `OrbitSet` is
--       CONTRACTIBLE, the identity task is NOT invariant, and therefore
--       (by T4, contrapositively) the identity does NOT descend.
--
-- SUCCESS TEST.  There is no closure lemma anywhere in this file: no
-- subgroup is constructed, no generated subgroup, no `closure_le`, no
-- kernel.  The words "closure"/"subgroup" occur only in this header and
-- in the quoted source.  `eq/` on the raw generator relation is the
-- whole of it.
--
-- CHECKED: Agda 2.8.0 + cubical v0.9, `--safe`; no postulates, no
-- holes, no TERMINATING pragma.
------------------------------------------------------------------------

module KaksaAvatarana_OrbitDescentASetValuedTaskDescendsToTheOrbitSetExactlyWhenItIsInvariantAndCoinvariantsNeedNoClosureLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Bool

open Iso
open IsGroupHom

------------------------------------------------------------------------
-- §1  Orbit descent.
------------------------------------------------------------------------

module OrbitDescent {ℓg ℓx} (G : Group ℓg) {X : Type ℓx}
  (_·_   : ⟨ G ⟩ → X → X)
  (·-1g  : (x : X) → (GroupStr.1g (snd G)) · x ≡ x)
  (·-∙   : (g h : ⟨ G ⟩) (x : X) → (GroupStr._·_ (snd G) g h) · x ≡ g · (h · x))
  where

  private
    module Gs = GroupStr (snd G)

  -- T1 ---------------------------------------------------------------

  OrbitRel : X → X → Type (ℓ-max ℓg ℓx)
  OrbitRel x y = Σ[ g ∈ ⟨ G ⟩ ] (g · x ≡ y)

  OrbitSet : Type (ℓ-max ℓg ℓx)
  OrbitSet = X / OrbitRel                    -- raw relation: no setoid proof

  orbitMk : X → OrbitSet
  orbitMk = [_]

  isSetOrbitSet : isSet OrbitSet
  isSetOrbitSet = squash/

  orbitMk-· : (g : ⟨ G ⟩) (x : X) → orbitMk (g · x) ≡ orbitMk x
  orbitMk-· g x = sym (eq/ x (g · x) (g , refl))

  -- T2 ---------------------------------------------------------------

  module _ {ℓy} {Y : Type ℓy} where

    Invariant : (X → Y) → Type (ℓ-max ℓg (ℓ-max ℓx ℓy))
    Invariant task = (g : ⟨ G ⟩) (x : X) → task (g · x) ≡ task x

    Descends : (X → Y) → Type (ℓ-max ℓg (ℓ-max ℓx ℓy))
    Descends task = Σ[ d ∈ (OrbitSet → Y) ] ((x : X) → d (orbitMk x) ≡ task x)

    descend : isSet Y → (task : X → Y) → Invariant task → OrbitSet → Y
    descend isSetY task inv =
      SQ.rec isSetY task (λ a b (g , p) → sym (inv g a) ∙ cong task p)

    descend-β : (isSetY : isSet Y) (task : X → Y) (inv : Invariant task)
              → (x : X) → descend isSetY task inv (orbitMk x) ≡ task x
    descend-β _ _ _ _ = refl

    -- T3 -------------------------------------------------------------

    isPropDescends : isSet Y → (task : X → Y) → isProp (Descends task)
    isPropDescends isSetY task (d , h) (d' , h') =
      Σ≡Prop (λ _ → isPropΠ λ _ → isSetY _ _)
             (funExt (SQ.elimProp (λ _ → isSetY _ _) λ x → h x ∙ sym (h' x)))

    descend-unique : (isSetY : isSet Y) (task : X → Y) (inv : Invariant task)
                   → isContr (Descends task)
    descend-unique isSetY task inv .fst = descend isSetY task inv , λ _ → refl
    descend-unique isSetY task inv .snd = isPropDescends isSetY task _

    -- T4 -------------------------------------------------------------

    restrict-invariant : (d : OrbitSet → Y) → Invariant (d ∘ orbitMk)
    restrict-invariant d g x = cong d (orbitMk-· g x)

    Descends→Invariant : (task : X → Y) → Descends task → Invariant task
    Descends→Invariant task (d , h) g x =
      sym (h (g · x)) ∙ cong d (orbitMk-· g x) ∙ h x

    descendsIso : isSet Y → (task : X → Y) → Iso (Descends task) (Invariant task)
    descendsIso isSetY task =
      isProp→Iso (isPropDescends isSetY task)
                 (isPropΠ2 λ _ _ → isSetY _ _)
                 (Descends→Invariant task)
                 (λ inv → descend isSetY task inv , λ _ → refl)

    descends≃ : isSet Y → (task : X → Y) → Descends task ≃ Invariant task
    descends≃ isSetY task = isoToEquiv (descendsIso isSetY task)

  -- T5 ---------------------------------------------------------------
  -- The group laws enter here and nowhere else in this half.

  orbitRel-isEquivRel : BinaryRelation.isEquivRel OrbitRel
  orbitRel-isEquivRel = record
    { reflexive  = λ x → Gs.1g , ·-1g x
    ; symmetric  = λ x y (g , p) → Gs.inv g ,
        (Gs.inv g · y                    ≡⟨ cong (Gs.inv g ·_) (sym p) ⟩
         Gs.inv g · (g · x)              ≡⟨ sym (·-∙ (Gs.inv g) g x) ⟩
         (Gs.inv g Gs.· g) · x           ≡⟨ cong (_· x) (Gs.·InvL g) ⟩
         Gs.1g · x                       ≡⟨ ·-1g x ⟩
         x ∎)
    ; transitive = λ x y z (g , p) (h , q) → (h Gs.· g) ,
        ((h Gs.· g) · x                  ≡⟨ ·-∙ h g x ⟩
         h · (g · x)                     ≡⟨ cong (h ·_) p ⟩
         h · y                           ≡⟨ q ⟩
         z ∎)
    }

  orbitPath≃∥Rel∥ : (x y : X) → Iso (orbitMk x ≡ orbitMk y) ∥ OrbitRel x y ∥₁
  orbitPath≃∥Rel∥ = SQ.isEquivRel→TruncIso orbitRel-isEquivRel

------------------------------------------------------------------------
-- §2  Coinvariants.  Only `·-hom` is assumed of the action.
------------------------------------------------------------------------

module Coinvariants {ℓg ℓa} (G : Group ℓg) (A : AbGroup ℓa)
  (_·_   : ⟨ G ⟩ → ⟨ A ⟩ → ⟨ A ⟩)
  (·-hom : (g : ⟨ G ⟩) (x y : ⟨ A ⟩)
         → g · (AbGroupStr._+_ (snd A) x y)
         ≡ AbGroupStr._+_ (snd A) (g · x) (g · y))
  where

  open AbGroupStr (snd A) renaming (is-set to isSetA)
  open GroupTheory (AbGroup→Group A) using (invDistr)

  private
    actHom : (g : ⟨ G ⟩)
           → IsGroupHom (snd (AbGroup→Group A)) (g ·_) (snd (AbGroup→Group A))
    actHom g = makeIsGroupHom (·-hom g)

  ·-neg : (g : ⟨ G ⟩) (x : ⟨ A ⟩) → g · (- x) ≡ - (g · x)
  ·-neg g x = presinv (actHom g) x

  -- T6 ---------------------------------------------------------------

  DiffRel : ⟨ A ⟩ → ⟨ A ⟩ → Type (ℓ-max ℓg ℓa)
  DiffRel a b = Σ[ g ∈ ⟨ G ⟩ ] Σ[ x ∈ ⟨ A ⟩ ] (a ≡ b + ((g · x) - x))

  Coinv : Type (ℓ-max ℓg ℓa)
  Coinv = ⟨ A ⟩ / DiffRel                    -- the HIT generates the closure

  coinvMk : ⟨ A ⟩ → Coinv
  coinvMk = [_]

  isSetCoinv : isSet Coinv
  isSetCoinv = squash/

  -- Translation invariance of the raw generator relation: this is the
  -- entire content that Lean's `closure` + `closure_le` supplied.
  DiffRel-+R : (a b c : ⟨ A ⟩) → DiffRel a b → DiffRel (a + c) (b + c)
  DiffRel-+R a b c (g , x , p) = g , x ,
    (a + c                     ≡⟨ cong (_+ c) p ⟩
     (b + ((g · x) - x)) + c   ≡⟨ sym (+Assoc _ _ _) ⟩
     b + (((g · x) - x) + c)   ≡⟨ cong (b +_) (+Comm _ _) ⟩
     b + (c + ((g · x) - x))   ≡⟨ +Assoc _ _ _ ⟩
     (b + c) + ((g · x) - x) ∎)

  DiffRel-+L : (a b c : ⟨ A ⟩) → DiffRel b c → DiffRel (a + b) (a + c)
  DiffRel-+L a b c (g , x , p) = g , x ,
    (a + b                     ≡⟨ cong (a +_) p ⟩
     a + (c + ((g · x) - x))   ≡⟨ +Assoc _ _ _ ⟩
     (a + c) + ((g · x) - x) ∎)

  DiffRel-neg : (a b : ⟨ A ⟩) → DiffRel a b → DiffRel (- a) (- b)
  DiffRel-neg a b (g , x , p) = g , (- x) ,
    (- a                                    ≡⟨ cong (-_) p ⟩
     - (b + ((g · x) + (- x)))              ≡⟨ invDistr b ((g · x) + (- x)) ⟩
     (- ((g · x) + (- x))) + (- b)          ≡⟨ cong (_+ (- b)) (invDistr (g · x) (- x)) ⟩
     ((- (- x)) + (- (g · x))) + (- b)      ≡⟨ +Comm _ _ ⟩
     (- b) + ((- (- x)) + (- (g · x)))      ≡⟨ cong ((- b) +_) (+Comm _ _) ⟩
     (- b) + ((- (g · x)) + (- (- x)))      ≡⟨ cong (λ u → (- b) + (u + (- (- x)))) (sym (·-neg g x)) ⟩
     (- b) + ((g · (- x)) + (- (- x))) ∎)

  0Q : Coinv
  0Q = [ 0g ]

  _+Q_ : Coinv → Coinv → Coinv
  _+Q_ = SQ.rec2 squash/ (λ a b → [ a + b ])
           (λ a b c r → eq/ _ _ (DiffRel-+R a b c r))
           (λ a b c r → eq/ _ _ (DiffRel-+L a b c r))

  -Q_ : Coinv → Coinv
  -Q_ = SQ.setQuotUnaryOp -_ DiffRel-neg

  +Q-β : (a b : ⟨ A ⟩) → coinvMk a +Q coinvMk b ≡ coinvMk (a + b)
  +Q-β _ _ = refl

  -Q-β : (a : ⟨ A ⟩) → -Q coinvMk a ≡ coinvMk (- a)
  -Q-β _ = refl

  coinvAbGroup : AbGroup (ℓ-max ℓg ℓa)
  coinvAbGroup = makeAbGroup 0Q _+Q_ -Q_ squash/
    (SQ.elimProp3 (λ _ _ _ → squash/ _ _) λ a b c → cong [_] (+Assoc a b c))
    (SQ.elimProp  (λ _ → squash/ _ _)     λ a     → cong [_] (+IdR a))
    (SQ.elimProp  (λ _ → squash/ _ _)     λ a     → cong [_] (+InvR a))
    (SQ.elimProp2 (λ _ _ → squash/ _ _)   λ a b   → cong [_] (+Comm a b))

  coinvMkHom : AbGroupHom A coinvAbGroup
  coinvMkHom = coinvMk , makeIsGroupHom (λ _ _ → refl)

  coinvMk-· : (g : ⟨ G ⟩) (x : ⟨ A ⟩) → coinvMk (g · x) ≡ coinvMk x
  coinvMk-· g x = eq/ (g · x) x (g , x , sym
    (x + ((g · x) + (- x))   ≡⟨ +Comm _ _ ⟩
     ((g · x) + (- x)) + x   ≡⟨ sym (+Assoc _ _ _) ⟩
     (g · x) + ((- x) + x)   ≡⟨ cong ((g · x) +_) (+InvL x) ⟩
     (g · x) + 0g            ≡⟨ +IdR _ ⟩
     g · x ∎))

  -- The additive universal property. -----------------------------------

  module _ {ℓb} (B : AbGroup ℓb) where

    private
      module Bs = AbGroupStr (snd B)
      _+B_ = Bs._+_
      -B_  = Bs.-_
      infixr 7 _+B_

    InvariantHom : AbGroupHom A B → Type (ℓ-max ℓg (ℓ-max ℓa ℓb))
    InvariantHom task = (g : ⟨ G ⟩) (x : ⟨ A ⟩) → task .fst (g · x) ≡ task .fst x

    DescendsHom : AbGroupHom A B → Type (ℓ-max ℓg (ℓ-max ℓa ℓb))
    DescendsHom task =
      Σ[ d ∈ AbGroupHom coinvAbGroup B ] ((a : ⟨ A ⟩) → d .fst (coinvMk a) ≡ task .fst a)

    -- An invariant additive task kills every generator difference.
    killsDiff : (task : AbGroupHom A B) → InvariantHom task
              → (a b : ⟨ A ⟩) → DiffRel a b → task .fst a ≡ task .fst b
    killsDiff (t , th) inv a b (g , x , p) =
      t a                                      ≡⟨ cong t p ⟩
      t (b + ((g · x) + (- x)))                ≡⟨ pres· th b _ ⟩
      t b +B t ((g · x) + (- x))               ≡⟨ cong (t b +B_) (pres· th (g · x) (- x)) ⟩
      t b +B (t (g · x) +B t (- x))            ≡⟨ cong (λ u → t b +B (u +B t (- x))) (inv g x) ⟩
      t b +B (t x +B t (- x))                  ≡⟨ cong (λ u → t b +B (t x +B u)) (presinv th x) ⟩
      t b +B (t x +B (-B t x))                 ≡⟨ cong (t b +B_) (Bs.+InvR (t x)) ⟩
      t b +B Bs.0g                             ≡⟨ Bs.+IdR (t b) ⟩
      t b ∎

    descendHom : (task : AbGroupHom A B) → InvariantHom task
               → AbGroupHom coinvAbGroup B
    descendHom task inv .fst = SQ.rec Bs.is-set (task .fst) (killsDiff task inv)
    descendHom task inv .snd =
      makeIsGroupHom (SQ.elimProp2 (λ _ _ → Bs.is-set _ _) λ a b → pres· (task .snd) a b)

    descendHom-β : (task : AbGroupHom A B) (inv : InvariantHom task)
                 → (a : ⟨ A ⟩) → descendHom task inv .fst (coinvMk a) ≡ task .fst a
    descendHom-β _ _ _ = refl

    isPropDescendsHom : (task : AbGroupHom A B) → isProp (DescendsHom task)
    isPropDescendsHom task (d , h) (d' , h') =
      Σ≡Prop (λ _ → isPropΠ λ _ → Bs.is-set _ _)
             (GroupHom≡ (funExt (SQ.elimProp (λ _ → Bs.is-set _ _) λ a → h a ∙ sym (h' a))))

    descendHom-unique : (task : AbGroupHom A B) (inv : InvariantHom task)
                      → isContr (DescendsHom task)
    descendHom-unique task inv .fst = descendHom task inv , λ _ → refl
    descendHom-unique task inv .snd = isPropDescendsHom task _

    restrictHom-invariant : (d : AbGroupHom coinvAbGroup B)
                          → (g : ⟨ G ⟩) (x : ⟨ A ⟩)
                          → d .fst (coinvMk (g · x)) ≡ d .fst (coinvMk x)
    restrictHom-invariant d g x = cong (d .fst) (coinvMk-· g x)

    DescendsHom→InvariantHom : (task : AbGroupHom A B) → DescendsHom task → InvariantHom task
    DescendsHom→InvariantHom task (d , h) g x =
      sym (h (g · x)) ∙ restrictHom-invariant d g x ∙ h x

    descendsHomIso : (task : AbGroupHom A B) → Iso (DescendsHom task) (InvariantHom task)
    descendsHomIso task =
      isProp→Iso (isPropDescendsHom task)
                 (isPropΠ2 λ _ _ → Bs.is-set _ _)
                 (DescendsHom→InvariantHom task)
                 (λ inv → descendHom task inv , λ _ → refl)

    descendsHom≃ : (task : AbGroupHom A B) → DescendsHom task ≃ InvariantHom task
    descendsHom≃ task = isoToEquiv (descendsHomIso task)

------------------------------------------------------------------------
-- §3  Controls.
------------------------------------------------------------------------

-- C1.  The trivial group, with ANY action on a set: orbitMk is an
-- equivalence.  (Every element of Unit is the unit, so `·-1g` already
-- says the action is trivial.)
module UnitControl {ℓx} {X : Type ℓx} (isSetX : isSet X)
  (_·_  : Unit → X → X)
  (·-1g : (x : X) → tt · x ≡ x)
  (·-∙  : (g h : Unit) (x : X) → tt · x ≡ g · (h · x))
  where

  open OrbitDescent UnitGroup₀ _·_ ·-1g ·-∙

  id-invariant : Invariant (idfun X)
  id-invariant tt x = ·-1g x

  orbitIso : Iso OrbitSet X
  orbitIso .fun = descend isSetX (idfun X) id-invariant
  orbitIso .inv = orbitMk
  orbitIso .rightInv _ = refl
  orbitIso .leftInv  = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

  orbitMk-isEquiv : isEquiv orbitMk
  orbitMk-isEquiv = isoToIsEquiv (invIso orbitIso)

  OrbitSet≃X : OrbitSet ≃ X
  OrbitSet≃X = isoToEquiv orbitIso

-- C2.  ℤ/2 = BoolGroup acting on Bool by its own multiplication
-- (`true · b = b`, `false · b = not b`): one orbit, so the identity
-- task — which is not invariant — does not descend.
module BoolControl where

  private
    _·_ : Bool → Bool → Bool
    _·_ = GroupStr._·_ (snd BoolGroup)

    ·-1g : (b : Bool) → true · b ≡ b
    ·-1g _ = refl

    ·-∙ : (g h b : Bool) → (g · h) · b ≡ g · (h · b)
    ·-∙ g h b = sym (GroupStr.·Assoc (snd BoolGroup) g h b)

  open OrbitDescent BoolGroup _·_ ·-1g ·-∙

  isContrOrbitSet : isContr OrbitSet
  isContrOrbitSet .fst = orbitMk true
  isContrOrbitSet .snd = SQ.elimProp (λ _ → squash/ _ _) λ
    { true  → refl
    ; false → eq/ true false (false , refl) }

  id-notInvariant : ¬ Invariant (idfun Bool)
  id-notInvariant inv = false≢true (inv false true)

  id-doesNotDescend : ¬ Descends (idfun Bool)
  id-doesNotDescend desc = id-notInvariant (Descends→Invariant (idfun Bool) desc)

  -- The same conclusion straight from contractibility, without T4:
  -- every map out of a contractible type is constant.
  id-doesNotDescend' : ¬ Descends (idfun Bool)
  id-doesNotDescend' (d , h) =
    false≢true (sym (h false) ∙ cong d (sym (isContrOrbitSet .snd (orbitMk false))
                                        ∙ isContrOrbitSet .snd (orbitMk true)) ∙ h true)

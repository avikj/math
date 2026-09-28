{-# OPTIONS --cubical --safe --no-import-sorts #-}
------------------------------------------------------------------------
-- द्रष्टृ-अवतारणम् — observer descent: an observation factors through
-- an observable exactly when it is constant on the observable's fibres,
-- and the factorization is built without choice.
--
-- SOURCE.  notes/LEAN_TO_CUBICAL_PORT_MAP.md (absent from this repository) (branch main), §3.3
-- "`FiniteInformation` → `NaturalMachine/ObserverDescent.agda` (absent from this repository)
-- (proposed)", whose code sketch reads verbatim:
--
--   module ObserverDescent {ℓx ℓy ℓt} {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt} where
--
--     -- Lean's FactorsThrough, with Set.range replaced by the univalent Image
--     FactorsThrough : (q : X → Y) (t : X → T) → Type _
--     FactorsThrough q t = Σ[ decode ∈ (Image q → T) ]
--                            ((x : X) → decode (restrictToImage q x) ≡ t x)
--
--     FiberConstant : (q : X → Y) (t : X → T) → Type _
--     FiberConstant q t = (x x' : X) → q x ≡ q x' → t x ≡ t x'
--
--     -- Lean: factorsThrough_iff_fiberConstant.  Choice-free: the ← direction
--     -- eliminates ∥ fiber q y ∥₁ by PT.rec→Set with the 2-Constant witness
--     -- extracted from fiber-constancy.  Needs isSet T; Lean needed Classical.choice.
--     factorsThrough≃fiberConstant :
--       (isSetT : isSet T) (q : X → Y) (t : X → T)
--       → … -- Iso (FactorsThrough q t) (FiberConstant q t), or the two maps
--           -- factorsThrough→fiberConstant / fiberConstant→factorsThrough
--
--     -- Lean: Completes, completes_iff_separatesFibers, completes_of_injective,
--     -- completes_mono — verbatim one-liners:
--     Completes : (q : X → Y) (c : X → C) → Type _
--     Completes q c = (x x' : X) → q x ≡ q x' → c x ≡ c x' → x ≡ x'
--     completes-of-inj  : ((x x' : X) → q x ≡ q x' → x ≡ x') → Completes q c
--     completes-mono    : Completes q c → Completes q (λ x → c x , d x)
--
--     -- Lean: factorsThrough_postprocess (deterministic data processing):
--     factorsThrough-postprocess :
--       (q : X → Y) (r : Y → Z) (t : X → T)
--       → FiberConstant (r ∘ q) t → FiberConstant q t
--
--     -- Lean: targetFiber_injects_side.  The Lean statement builds an injection
--     -- TargetFiber → C by choosing witnesses (Classical.choose); constructively
--     -- restate as a surjection OUT of C, which carries the same cardinality
--     -- content (|C| ≥ |t(q⁻¹ y)|) without choice:
--     decode-covers-fiber :
--       (q : X → Y) (t : X → T) (c : X → C)
--       (decode : Y → C → T)
--       (replay : (x : X) → decode (q x) (c x) ≡ t x)
--       (y : Y) (v : T) → ∥ Σ[ x ∈ X ] (q x ≡ y) × (t x ≡ v) ∥₁
--       → ∥ Σ[ k ∈ C ] decode y k ≡ v ∥₁       -- PT.map, two lines
--
-- The same note's standing queue (§5) carries the entry, verbatim:
--
--   - `PROVE` (port rank 3): `ObserverDescent.agda` (absent from this repository) per §3.3 — choice-free
--     factorization through `Image`; success test: no `∥∥`-escape other than
--     `rec→Set`.
--
-- The Lean original is formal/lean/Pairfield/FiniteInformation.lean, whose
-- header says, verbatim: "The statements are deliberately
-- distribution-free.  Shannon entropy may be attached later after choosing
-- a probability law; the algebraic core is simply factorization through an
-- observable and injectivity after adding side data."  Its theorems are
-- factorsThrough_iff_fiberConstant, targetFiber_injects_side,
-- completes_iff_separatesFibers, completes_of_injective,
-- factorsThrough_postprocess, completes_mono.
--
-- WHAT IS PROVED HERE.  With q : X → Y the observable, t : X → T the
-- target, c : X → C the side channel, and `Image q = Σ[ y ∈ Y ] ∥ fiber q y ∥₁`
-- the library image (Cubical.Functions.Image):
--
--   (T1) factorsThrough→fiberConstant — no hypotheses at all.
--   (T2) fiberConstant→factorsThrough — needs only `isSet T`.  The decode is
--        `PT.SetElim.rec→Set` applied to `t ∘ fst : fiber q y → T` with the
--        2-Constant witness read off fibre-constancy.  Where Lean wrote
--        `Classical.choose`, this writes a computation rule:
--        `decode (restrictToImage q x) ≡ t x` is `refl`.
--   (T3) decode-unique: two decodes that replay t agree (restrictToImage is
--        surjective, T is a set); hence FactorsThrough q t is a proposition
--        when T is a set, and factorsThrough≃fiberConstant is an equivalence.
--   (T4) completes≃separatesFibers — an Iso whose round trips are `refl`.
--   (T5) completes-of-injective.
--   (T6) factorsThrough-postprocess — directly, by `PT.map` on the image
--        witness, with NO `isSet T` (stronger than the Lean route through
--        fibre-constancy); the fibre-constant one-liner of the sketch too.
--   (T7) completes-mono.
--   (T8) targetFiber-injects-side, stated as its exact content: inside one
--        observer fibre, equal side values force equal target values; and
--        the sketch's decode-covers-fiber (PT.map).
--   Controls: q constant on Bool with t = id does NOT factor; q = fst on
--   Bool × Bool with t = not ∘ fst does, and the decode is unique.
--
-- The success test holds: the only elimination of ∥_∥₁ into a non-proposition
-- is `rec→Set` (in fiberConstant→factorsThrough).  Every other use is
-- `PT.rec`/`PT.map` into a proposition or into another truncation.
--
-- WHAT IS NOT PROVED HERE.  Nothing probabilistic: no probability law is
-- chosen, no Shannon entropy is attached, no cardinality inequality
-- |C| ≥ |t(q⁻¹ y)| is stated (that is the sketch's parenthetical about
-- Cubical.Data.FinSet.Cardinality and is not invoked).  The Lean
-- `TargetFiber → C` injection is not built as a function — building it
-- would need a choice of witness — and is replaced by its point-level
-- content (T8), which is what the Lean proof actually uses.
------------------------------------------------------------------------
module DrastrAvatarana_ObserverDescentAnObservationFactorsThroughAnObservableExactlyWhenItIsConstantOnFibresWithoutChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; 2-Constant)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels using (isPropΠ ; isPropΠ3 ; isPropΣ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; Σ≡Prop)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; isSetBool ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Image
  using (Image ; restrictToImage ; isPropIsInImage ; isSurjectionImageRestriction)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

private
  variable
    ℓx ℓy ℓz ℓt ℓc ℓd : Level

-- injectivity, spelled out (the library keeps it as a local hypothesis)
Injective : {A : Type ℓx} {B : Type ℓy} → (A → B) → Type _
Injective {A = A} f = (a a' : A) → f a ≡ f a' → a ≡ a'

------------------------------------------------------------------------
-- §१  Descent through an observable
------------------------------------------------------------------------

module _ {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt} where

  -- Lean's FactorsThrough, with Set.range replaced by the univalent Image
  FactorsThrough : (q : X → Y) (t : X → T) → Type _
  FactorsThrough q t =
    Σ[ decode ∈ (Image q → T) ] ((x : X) → decode (restrictToImage q x) ≡ t x)

  FiberConstant : (q : X → Y) (t : X → T) → Type _
  FiberConstant q t = (x x' : X) → q x ≡ q x' → t x ≡ t x'

  -- (T1) descent forces fibre-constancy; no hypothesis on any type
  factorsThrough→fiberConstant :
    (q : X → Y) (t : X → T) → FactorsThrough q t → FiberConstant q t
  factorsThrough→fiberConstant q t (decode , replay) x x' p =
    sym (replay x) ∙ cong decode (Σ≡Prop (isPropIsInImage q) p) ∙ replay x'

  -- (T2) fibre-constancy gives descent, without choice, when T is a set.
  -- The decode eliminates ∥ fiber q y ∥₁ by rec→Set: on a witness (x , _)
  -- it answers t x, and any two witnesses lie in the same fibre so give
  -- the same answer by fibre-constancy.
  module _ (isSetT : isSet T) (q : X → Y) (t : X → T) (fc : FiberConstant q t) where

    onFiber : (y : Y) → fiber q y → T
    onFiber y (x , _) = t x

    onFiber-2-Constant : (y : Y) → 2-Constant (onFiber y)
    onFiber-2-Constant y (x , p) (x' , p') = fc x x' (p ∙ sym p')

    descend : Image q → T
    descend (y , w) = PT.SetElim.rec→Set isSetT (onFiber y) (onFiber-2-Constant y) w

    -- the replay equation is a computation rule
    descend-replay : (x : X) → descend (restrictToImage q x) ≡ t x
    descend-replay x = refl

  fiberConstant→factorsThrough :
    isSet T → (q : X → Y) (t : X → T) → FiberConstant q t → FactorsThrough q t
  fiberConstant→factorsThrough isSetT q t fc =
    descend isSetT q t fc , descend-replay isSetT q t fc

  -- (T3) the decode is unique: restrictToImage is surjective and T is a set
  decode-unique :
    isSet T → (q : X → Y) (t : X → T)
    (d d' : Image q → T)
    → ((x : X) → d (restrictToImage q x) ≡ t x)
    → ((x : X) → d' (restrictToImage q x) ≡ t x)
    → d ≡ d'
  decode-unique isSetT q t d d' h h' = funExt λ y →
    PT.rec (isSetT _ _)
      (λ (x , p) → cong d (sym p) ∙ h x ∙ sym (h' x) ∙ cong d' p)
      (isSurjectionImageRestriction q y)

  isPropFactorsThrough : isSet T → (q : X → Y) (t : X → T) → isProp (FactorsThrough q t)
  isPropFactorsThrough isSetT q t (d , h) (d' , h') =
    Σ≡Prop (λ e → isPropΠ λ x → isSetT _ _) (decode-unique isSetT q t d d' h h')

  isPropFiberConstant : isSet T → (q : X → Y) (t : X → T) → isProp (FiberConstant q t)
  isPropFiberConstant isSetT q t = isPropΠ3 λ _ _ _ → isSetT _ _

  -- Lean: factorsThrough_iff_fiberConstant, as an equivalence of propositions
  factorsThrough≃fiberConstant :
    isSet T → (q : X → Y) (t : X → T) → FactorsThrough q t ≃ FiberConstant q t
  factorsThrough≃fiberConstant isSetT q t =
    propBiimpl→Equiv (isPropFactorsThrough isSetT q t) (isPropFiberConstant isSetT q t)
      (factorsThrough→fiberConstant q t) (fiberConstant→factorsThrough isSetT q t)

------------------------------------------------------------------------
-- §२  Completion by side information
------------------------------------------------------------------------

module _ {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc} where

  -- Lean: Completes := Function.Injective fun x => (q x, c x)
  Completes : (q : X → Y) (c : X → C) → Type _
  Completes q c = Injective (λ x → (q x , c x))

  SeparatesFibers : (q : X → Y) (c : X → C) → Type _
  SeparatesFibers q c = (x x' : X) → q x ≡ q x' → c x ≡ c x' → x ≡ x'

  -- (T4) Lean: completes_iff_separatesFibers; here an Iso with refl round trips
  completesIsoSeparatesFibers :
    (q : X → Y) (c : X → C) → Iso (Completes q c) (SeparatesFibers q c)
  completesIsoSeparatesFibers q c = iso
    (λ h x x' hq hc → h x x' (λ i → hq i , hc i))
    (λ h x x' p → h x x' (cong fst p) (cong snd p))
    (λ _ → refl)
    (λ _ → refl)

  completes≃separatesFibers :
    (q : X → Y) (c : X → C) → Completes q c ≃ SeparatesFibers q c
  completes≃separatesFibers q c = isoToEquiv (completesIsoSeparatesFibers q c)

  -- (T5) Lean: completes_of_injective
  completes-of-injective :
    (q : X → Y) → Injective q → (c : X → C) → Completes q c
  completes-of-injective q inj c x x' p = inj x x' (cong fst p)

-- (T7) Lean: completes_mono — outside the block above, since the side
-- alphabet grows from C to C × D
completes-mono :
  {X : Type ℓx} {Y : Type ℓy} {C : Type ℓc} {D : Type ℓd}
  (q : X → Y) (c : X → C) (d : X → D)
  → Completes q c → Completes q (λ x → c x , d x)
completes-mono q c d h x x' p = h x x' (λ i → fst (p i) , fst (snd (p i)))

------------------------------------------------------------------------
-- §३  Deterministic data processing
------------------------------------------------------------------------

module _ {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz} {T : Type ℓt} where

  -- the sketch's fibre-constant one-liner
  fiberConstant-postprocess :
    (q : X → Y) (r : Y → Z) (t : X → T)
    → FiberConstant (r ∘ q) t → FiberConstant q t
  fiberConstant-postprocess q r t fc x x' p = fc x x' (cong r p)

  -- (T6) Lean: factorsThrough_postprocess — directly, and with no isSet T:
  -- a decode over Image (r ∘ q) is pulled back along the map of images
  -- (y , w) ↦ (r y , PT.map (x , p ↦ x , cong r p) w), and the replay
  -- equation is again a computation rule.
  factorsThrough-postprocess :
    (q : X → Y) (r : Y → Z) (t : X → T)
    → FactorsThrough (r ∘ q) t → FactorsThrough q t
  factorsThrough-postprocess q r t (decode , replay) =
    (λ (y , w) → decode (r y , PT.map (λ (x , p) → x , cong r p) w)) , replay

------------------------------------------------------------------------
-- §४  Side alphabets must separate targets inside a fibre
------------------------------------------------------------------------

module _ {X : Type ℓx} {Y : Type ℓy} {T : Type ℓt} {C : Type ℓc}
  (q : X → Y) (t : X → T) (c : X → C)
  (decode : Y → C → T)
  (replay : (x : X) → decode (q x) (c x) ≡ t x) where

  -- (T8) Lean: targetFiber_injects_side, as its point-level content: two
  -- states in the same observer fibre with the same side value have the
  -- same target value.  This is the injectivity of (the image of t on the
  -- fibre over y) into C, stated without choosing witnesses.
  targetFiber-injects-side :
    (y : Y) (x x' : X) → q x ≡ y → q x' ≡ y → c x ≡ c x' → t x ≡ t x'
  targetFiber-injects-side y x x' hx hx' hc =
      sym (replay x)
    ∙ cong₂ decode hx hc
    ∙ cong (λ z → decode z (c x')) (sym hx')
    ∙ replay x'

  -- the sketch's decode-covers-fiber: every target value occurring in the
  -- fibre over y is hit by decode y from some side value (PT.map)
  decode-covers-fiber :
    (y : Y) (v : T) → ∥ Σ[ x ∈ X ] (q x ≡ y) × (t x ≡ v) ∥₁
    → ∥ Σ[ k ∈ C ] decode y k ≡ v ∥₁
  decode-covers-fiber y v =
    PT.map λ (x , p , e) → c x , cong (λ z → decode z (c x)) (sym p) ∙ replay x ∙ e

------------------------------------------------------------------------
-- §५  Controls
------------------------------------------------------------------------

-- a constant observable on Bool sees nothing; the identity target does not descend
const-tt : Bool → Unit
const-tt _ = tt

id-does-not-factor : ¬ FactorsThrough const-tt (λ b → b)
id-does-not-factor ft =
  false≢true (factorsThrough→fiberConstant const-tt (λ b → b) ft false true refl)

-- the first projection on Bool × Bool is a non-injective observable, and a
-- target depending only on the first coordinate descends through it
fstBool : Bool × Bool → Bool
fstBool = fst

notFst : Bool × Bool → Bool
notFst p = not (fst p)

notFst-factors : FactorsThrough fstBool notFst
notFst-factors = (λ (y , _) → not y) , λ _ → refl

-- the choice-free construction agrees with the hand-written decode
notFst-descend-agrees :
  fst (fiberConstant→factorsThrough isSetBool fstBool notFst
        (λ x x' p → cong not p))
  ≡ fst notFst-factors
notFst-descend-agrees =
  decode-unique isSetBool fstBool notFst _ _
    (snd (fiberConstant→factorsThrough isSetBool fstBool notFst (λ x x' p → cong not p)))
    (snd notFst-factors)

-- the second projection completes the first; a constant side channel does not
snd-completes-fst : Completes fstBool snd
snd-completes-fst _ _ p = p

const-does-not-complete : ¬ Completes fstBool (λ (_ : Bool × Bool) → tt)
const-does-not-complete h =
  false≢true (cong snd (h (true , false) (true , true) refl))

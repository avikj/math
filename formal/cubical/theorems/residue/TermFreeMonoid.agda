{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TermFreeMonoid
--
-- THE CHART TRANSITION FOR THE GENERATIVE LANE.
--
-- `Obstruction` defines
--
--     data Tm : Type₀ where
--       var  : Tm
--       node : Shape → Tm → Tm
--
--     plug : Tm → Tm → Tm
--     plug var        u = u
--     plug (node c t) u = node c (plug t u)
--
-- which is `List Shape` with `_++_`, constructor for constructor.  That
-- observation is the beginning of the work here, not the end of it.
--
-- The reading to avoid — and it was this repository's reading until
-- 2026-08-14 — is "so the lane is 1400 lines of nothing, delete it".
-- That is backwards, and `AtlasResiduals` is the module
-- that says why: a presentation is a CHART, and an atlas is charts
-- together with the transitions between them.  Two presentations with a
-- transition are strictly more than one presentation.  What was missing
-- was never the second chart; it was this file.
--
-- So nothing below deletes anything.  It connects, and then collects
-- what the connection pays for.
--
--
-- WHAT IS CHECKED
--
--   §1  `TmChart`            Iso Tm (List Shape), both round trips by
--       `Tm≃List`            induction; and `toList-plug`, saying the
--       `toList-plug`        chart carries `plug` to `_++_`.  The
--                            transition is a monoid map, which is the
--                            only reason transporting along it is
--                            worth anything.
--
--   §2  `plug-assoc`         (Tm, plug, var) is a MONOID.  Associativity
--       `plug-unit-l`        was not previously stated anywhere in the
--       `plug-unit-r`        lane — the lane had a binary operation and
--                            no law about it — so this is new, and it is
--                            `++-assoc` read through §1.
--
--   §3  `rec`                THE UNIVERSAL PROPERTY, in initial-algebra
--       `rec-unique`         form: for every `e : M` and `f : Shape → M`
--       `rec-hom`            and `_·_`, the function determined by
--       `rec-η`              `var ↦ e`, `node c t ↦ f c · rec t` EXISTS
--                            and is UNIQUE among functions satisfying
--                            those two equations; and if `_·_` is
--                            associative with `e` a unit, that function
--                            is a monoid homomorphism `(Tm, plug, var) →
--                            (M, ·, e)` extending `f` along
--                            `η c = node c var`.  Hence (Tm, plug, var)
--                            is the FREE MONOID on Shape.
--
--                            NO h-LEVEL HYPOTHESIS ANYWHERE.  Uniqueness
--                            is pointwise, proved by induction against
--                            the two equations as paths, so `M` need not
--                            be a set.  (This file was written the day
--                            `AtlasResiduals` had exactly such an
--                            unnecessary set hypothesis removed; the
--                            lesson is applied rather than restated.)
--
--   §4  `size-is-rec`        THE PAYOFF.  The lane's two hand-proved
--       `deficit-is-rec`     additivity lemmas are one theorem.
--       `plug-size′`         `WitnessPolicy.size` is the extension of
--       `plug-deficit′`      `λ _ → 1`, and `GenerativeLoop.deficit V`
--       `rec-additive`       is the extension of `delta V`, both into
--                            (ℕ, +, 0) — each identification is `refl`
--                            at both equations, so `rec-unique` closes
--                            them immediately.  Their additivity over
--                            `plug` is then not a coincidence checked
--                            twice by induction but a single instance of
--                            `rec-hom`, and `rec-additive` states the
--                            general fact: EVERY measure defined by this
--                            recursion into a monoid is automatically
--                            plug-additive.
--
--  * Not that `WitnessPolicy.plug-size` or
--    `ProgressDefinition.plug-deficit` are wrong, or should be removed.
--    They are correct and they are three lines each.  What §4 adds is the
--    reason they hold, which is a property of the recursion scheme and
--    not of `size` or `deficit`; the primed versions are re-derivations
--    THROUGH the universal property, offered as the transition, not as
--    replacements.
--
--  * Not that the free monoid is new mathematics.  It is not, by a very
--    long way.  What is new is that this lane's `Tm` is now connected to
--    it, so the lane inherits statements instead of re-proving them.
--
--  * Not an upstreamable free-monoid module.  Worth recording, though,
--    since the ecosystem survey went looking: cubical v0.5 has
--    `HITs/FreeComMonoids`, `HITs/FreeGroup`, `HITs/FreeAbGroup` and
--    `Algebra/CommMonoid/Instances/FreeComMonoid`, and NO universal
--    property for the free MONOID on a type — `Data/List/Properties`
--    has `++-assoc` and `++-unit-r` but nothing characterising `List`.
--    The gap is real; filling it upstream is a separate job from this
--    one, and this file does not do it (it is stated for `Tm`, not for a
--    general `List A`).
--
--  * `Shape = ℕ` here, as everywhere in the lane.  Nothing below uses
--    that, and nothing below uses decidable equality on Shape; the
--    development would go through verbatim for an arbitrary Shape type.
------------------------------------------------------------------------

module TermFreeMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)

open import ObstructionSubstrate
  using (Shape ; Vocab ; Tm ; var ; node ; plug)
open import WitnessPolicy   using (size)
open import GenerativeLoop  using (delta ; deficit)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  The chart.
--
-- `Tm` and `List Shape` are the same data presented twice.  The Iso is
-- the transition; `toList-plug` is the fact that makes it a transition
-- of MONOIDS rather than of bare types, and that is the whole reason
-- anything can be carried across it.
------------------------------------------------------------------------

toList : Tm → List Shape
toList var        = []
toList (node c t) = c ∷ toList t

fromList : List Shape → Tm
fromList []       = var
fromList (c ∷ cs) = node c (fromList cs)

toFrom : (xs : List Shape) → toList (fromList xs) ≡ xs
toFrom []       = refl
toFrom (c ∷ cs) = cong (c ∷_) (toFrom cs)

fromTo : (t : Tm) → fromList (toList t) ≡ t
fromTo var        = refl
fromTo (node c t) = cong (node c) (fromTo t)

TmChart : Iso Tm (List Shape)
Iso.fun      TmChart = toList
Iso.inv      TmChart = fromList
Iso.rightInv TmChart = toFrom
Iso.leftInv  TmChart = fromTo

Tm≃List : Tm ≃ (List Shape)
Tm≃List = isoToEquiv TmChart

-- The chart carries `plug` to `_++_`.
toList-plug : (t u : Tm) → toList (plug t u) ≡ toList t ++ toList u
toList-plug var        u = refl
toList-plug (node c t) u = cong (c ∷_) (toList-plug t u)

------------------------------------------------------------------------
-- 2.  (Tm, plug, var) is a monoid.
--
-- Associativity is `++-assoc` read through §1.  It is worth being plain
-- about the size of this: the proof is two lines either way, so the
-- chart does not save labour HERE.  What it buys is §3 — a universal
-- property is not something one stumbles into by induction, and it is
-- what the lane was missing.
------------------------------------------------------------------------

plug-assoc : (t u v : Tm) → plug (plug t u) v ≡ plug t (plug u v)
plug-assoc var        u v = refl
plug-assoc (node c t) u v = cong (node c) (plug-assoc t u v)

plug-unit-l : (t : Tm) → plug var t ≡ t
plug-unit-l t = refl

plug-unit-r : (t : Tm) → plug t var ≡ t
plug-unit-r var        = refl
plug-unit-r (node c t) = cong (node c) (plug-unit-r t)

-- The generator map.  Every term is a plug-product of these, which is
-- what `fromTo` says once §3 is in hand.
η : Shape → Tm
η c = node c var

------------------------------------------------------------------------
-- 3.  The universal property.
--
-- Stated in initial-algebra form first, because existence and
-- uniqueness of the recursor need NO hypotheses on the target at all —
-- not associativity, not a unit, and in particular no h-level.  The
-- monoid laws are then assumed only where they are actually used, to
-- upgrade the recursor to a homomorphism.
------------------------------------------------------------------------

module _ {M : Type ℓ} (e : M) (f : Shape → M) (_·_ : M → M → M) where

  rec : Tm → M
  rec var        = e
  rec (node c t) = f c · rec t

  -- Uniqueness, pointwise, against the two defining equations taken as
  -- paths.  This is where a set hypothesis would have been spurious.
  rec-unique : (g : Tm → M)
             → g var ≡ e
             → ((c : Shape) (t : Tm) → g (node c t) ≡ f c · g t)
             → (t : Tm) → g t ≡ rec t
  rec-unique g g-var g-node var        = g-var
  rec-unique g g-var g-node (node c t) =
    g-node c t ∙ cong (f c ·_) (rec-unique g g-var g-node t)

  -- Two functions satisfying the equations agree.
  rec-ext : (g h : Tm → M)
          → g var ≡ e → ((c : Shape) (t : Tm) → g (node c t) ≡ f c · g t)
          → h var ≡ e → ((c : Shape) (t : Tm) → h (node c t) ≡ f c · h t)
          → (t : Tm) → g t ≡ h t
  rec-ext g h g0 gs h0 hs t =
    rec-unique g g0 gs t ∙ sym (rec-unique h h0 hs t)

  module _ (unit-l : (x : M) → e · x ≡ x)
           (assoc  : (x y z : M) → (x · y) · z ≡ x · (y · z)) where

    -- The recursor is a monoid homomorphism (Tm, plug, var) → (M, ·, e).
    rec-hom : (t u : Tm) → rec (plug t u) ≡ rec t · rec u
    rec-hom var        u = sym (unit-l (rec u))
    rec-hom (node c t) u =
      cong (f c ·_) (rec-hom t u) ∙ sym (assoc (f c) (rec t) (rec u))

    rec-unit : rec var ≡ e
    rec-unit = refl

  -- ... and it extends f along η, given a right unit.
  module _ (unit-r : (x : M) → x · e ≡ x) where
    rec-η : (c : Shape) → rec (η c) ≡ f c
    rec-η c = unit-r (f c)

------------------------------------------------------------------------
-- 4.  What the connection pays for.
--
-- `size` and `deficit V` are both defined in the lane by exactly the
-- recursion of §3 into (ℕ, +, 0), and each was separately proved
-- additive over `plug` by its own induction.  Below, each is identified
-- with its recursor — both equations hold by `refl`, so `rec-unique`
-- closes the identification on the spot — and additivity then falls out
-- of `rec-hom` once, for both, and for anything else defined this way.
------------------------------------------------------------------------

+-assoc′ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc′ zero    y z = refl
+-assoc′ (suc x) y z = cong suc (+-assoc′ x y z)

+-unit-l : (x : ℕ) → 0 + x ≡ x
+-unit-l x = refl

-- `size` is the extension of the constant 1.
size-is-rec : (t : Tm) → size t ≡ rec 0 (λ _ → 1) _+_ t
size-is-rec = rec-unique 0 (λ _ → 1) _+_ size refl (λ _ _ → refl)

-- `deficit V` is the extension of `delta V`.
deficit-is-rec : (V : Vocab) (t : Tm) → deficit V t ≡ rec 0 (delta V) _+_ t
deficit-is-rec V = rec-unique 0 (delta V) _+_ (deficit V) refl (λ _ _ → refl)

-- THE GENERAL FACT.  Every measure defined by this recursion into a
-- monoid is plug-additive.  The lane's two additivity lemmas are the
-- instances immediately below; there is no third proof to write for the
-- next such measure.
rec-additive : {M : Type ℓ} (e : M) (f : Shape → M) (_·_ : M → M → M)
             → ((x : M) → e · x ≡ x)
             → ((x y z : M) → (x · y) · z ≡ x · (y · z))
             → (t u : Tm) → rec e f _·_ (plug t u) ≡ rec e f _·_ t · rec e f _·_ u
rec-additive e f _·_ ul as = rec-hom e f _·_ ul as

-- `WitnessPolicy.plug-size`, re-derived through the universal property.
plug-size′ : (t u : Tm) → size (plug t u) ≡ size t + size u
plug-size′ t u =
    size-is-rec (plug t u)
  ∙ rec-additive 0 (λ _ → 1) _+_ +-unit-l +-assoc′ t u
  ∙ cong₂ _+_ (sym (size-is-rec t)) (sym (size-is-rec u))

-- `ProgressDefinition.plug-deficit`, re-derived the same way.
plug-deficit′ : (V : Vocab) (t u : Tm)
              → deficit V (plug t u) ≡ deficit V t + deficit V u
plug-deficit′ V t u =
    deficit-is-rec V (plug t u)
  ∙ rec-additive 0 (delta V) _+_ +-unit-l +-assoc′ t u
  ∙ cong₂ _+_ (sym (deficit-is-rec V t)) (sym (deficit-is-rec V u))

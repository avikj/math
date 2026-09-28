{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- GroupCohomologyH2
--
-- The group H²(Q; A) for a trivial action, built as an actual group, and
-- the carry class of `CarryObstruction` located in it as a
-- **nonzero element**.
--
-- This is successor step 1 of `CarryObstruction`'s own list, and the
-- remaining half of ATLAS_OF_N.md (absent from this repository) §7's formalization pair: that module
-- proved `[c_n] ≠ 0` "stated without the group it lives in".  Here the
-- group is constructed.
--
-- Layers:
--
--  (1) `Cochain`:  2-cochains, the 2-cocycle identity, the coboundary map
--      δ, and `δ-isCocycle` (**coboundaries are cocycles**).  Z² is given
--      a group structure, B² is exhibited as a (normal, since abelian)
--      subgroup of it, and
--
--          H²(Q;A) := Z²(Q;A) / B²(Q;A)
--
--      is the library quotient group `Cubical.Algebra.Group.QuotientGroup`.
--      `class-zero→coboundary` is the effectivity statement: a class is
--      zero *exactly* when its representative is a coboundary.  This uses
--      `SetQuotients.effective`, so an equivalence-relation proof for the
--      subgroup relation is supplied.
--
--  (2) `CarryClass`:  for any extension π : G ↠ Q with G abelian and any
--      set-theoretic section s, the carry with coefficients in the group
--      K = ker π is an element `carryK : Z²(Q; K)`, whose cocycle identity
--      is **imported**, not reproved: it is `Carry.carry-cocycle` of
--      `CarryObstruction` transported along the injection ker π ↪ G.  The
--      theorem is `class-zero→hom-section`: if [carryK] = 0 in H²(Q; ker π)
--      then π admits a *homomorphic* section.  (The converse direction,
--      splitting ⇒ class zero, is `hom-section→class-zero`.)
--
-- The arithmetic instance — b ≥ 2, n ≥ 1, the truncation ℤ/bⁿ⁺¹ ↠ ℤ/bⁿ,
-- and hence Proposition 2.11's `[c_n] ≠ 0` — is the sibling module
-- `CarryClassNonzero`, which combines (2) with
-- `CarryObstruction.BasePower.extension-does-not-split`.  It is split off
-- so that the general construction and the instance check separately (and
-- because instantiating a `public`-opened chain of parametrized modules at
-- `Fin bⁿ⁺¹` is what made the combined file take >15 min; the two files
-- take 6 s and 3 s).
--
--  * H²(ℤ/m; A) ≅ A/mA.  The coefficient group here is `ker π` as a
--    subgroup of ℤ/bⁿ⁺¹, not `ℤ/b`; neither the isomorphism
--    bⁿℤ/bⁿ⁺¹ ≅ ℤ/b nor the computation of H² as A/mA is constructed.
--    Nonvanishing of the class does not need either.
--  * Any *exhibited* carrying pair: the theorem remains a ¬∀.
--
-- Toolchain: Agda 2.6.3 + cubical v0.5, `--safe`, no postulates, no holes.
------------------------------------------------------------------------

module GroupCohomologyH2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; squash/ ; effective)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup using (_/_ ; asGroup ; _~_ ; isRefl~)

open import CarryObstruction as CO using ()

open IsGroupHom
open isSubgroup

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 0.  Abelian bookkeeping
------------------------------------------------------------------------

module AbTools (A : Group ℓ)
               (comm : (x y : ⟨ A ⟩) → GroupStr._·_ (snd A) x y
                                     ≡ GroupStr._·_ (snd A) y x) where
  private
    module A = GroupStr (snd A)
  open GroupTheory A using (invDistr ; invInv ; inv1g) public

  -- (x·y)·(a·c) ≡ (x·a)·(y·c)
  middle4 : (x y a c : ⟨ A ⟩) → (x A.· y) A.· (a A.· c) ≡ (x A.· a) A.· (y A.· c)
  middle4 x y a c =
      sym (A.·Assoc x y (a A.· c))
    ∙ cong (x A.·_) (A.·Assoc y a c)
    ∙ cong (λ z → x A.· (z A.· c)) (comm y a)
    ∙ cong (x A.·_) (sym (A.·Assoc a y c))
    ∙ A.·Assoc x a (y A.· c)

  invDistr' : (x y : ⟨ A ⟩) → A.inv (x A.· y) ≡ A.inv x A.· A.inv y
  invDistr' x y = invDistr x y ∙ comm (A.inv y) (A.inv x)

  -- (P · D⁻¹) · (D · X) ≡ P · X
  slide : (P D X : ⟨ A ⟩) → (P A.· A.inv D) A.· (D A.· X) ≡ P A.· X
  slide P D X =
      sym (A.·Assoc P (A.inv D) (D A.· X))
    ∙ cong (P A.·_) (A.·Assoc (A.inv D) D X)
    ∙ cong (λ z → P A.· (z A.· X)) (A.·InvL D)
    ∙ cong (P A.·_) (A.·IdL X)

  -- X·P⁻¹ ≡ Y·R⁻¹  ⟹  X·Y⁻¹ ≡ P·R⁻¹.   (Cross-multiplication.)
  cross : (X P Y R : ⟨ A ⟩)
        → (X A.· A.inv P) ≡ (Y A.· A.inv R)
        → (X A.· A.inv Y) ≡ (P A.· A.inv R)
  cross X P Y R h =
      cong (A._· A.inv Y) expand
    ∙ cong (λ z → (z A.· P) A.· A.inv Y) h
    ∙ sym (A.·Assoc (Y A.· A.inv R) P (A.inv Y))
    ∙ cong ((Y A.· A.inv R) A.·_) (comm P (A.inv Y))
    ∙ middle4 Y (A.inv R) (A.inv Y) P
    ∙ cong (A._· (A.inv R A.· P)) (A.·InvR Y)
    ∙ A.·IdL (A.inv R A.· P)
    ∙ comm (A.inv R) P
    where
      expand : X ≡ (X A.· A.inv P) A.· P
      expand = sym (A.·IdR X)
             ∙ cong (X A.·_) (sym (A.·InvL P))
             ∙ A.·Assoc X (A.inv P) P

------------------------------------------------------------------------
-- 1.  2-cochains, 2-cocycles, 2-coboundaries, and H²
------------------------------------------------------------------------

-- Q acts trivially on A throughout; A is abelian.
module Cochain (Q : Group ℓ) (A : Group ℓ')
               (Acomm : (x y : ⟨ A ⟩) → GroupStr._·_ (snd A) x y
                                      ≡ GroupStr._·_ (snd A) y x) where

  private
    module Q = GroupStr (snd Q)
    module A = GroupStr (snd A)
  open AbTools A Acomm

  ----------------------------------------------------------------
  -- 1a.  cocycles
  ----------------------------------------------------------------

  C₂ : Type (ℓ-max ℓ ℓ')
  C₂ = ⟨ Q ⟩ → ⟨ Q ⟩ → ⟨ A ⟩

  -- c(u,v) + c(uv,w) = c(v,w) + c(u,vw)
  isCocycle : C₂ → Type (ℓ-max ℓ ℓ')
  isCocycle c = (u v w : ⟨ Q ⟩)
              → (c u v A.· c (u Q.· v) w) ≡ (c v w A.· c u (v Q.· w))

  isPropIsCocycle : (c : C₂) → isProp (isCocycle c)
  isPropIsCocycle c = isPropΠ3 λ _ _ _ → A.is-set _ _

  Z₂ : Type (ℓ-max ℓ ℓ')
  Z₂ = Σ[ c ∈ C₂ ] isCocycle c

  isSetZ₂ : isSet Z₂
  isSetZ₂ = isSetΣ (isSetΠ λ _ → isSetΠ λ _ → A.is-set)
                   λ c → isProp→isSet (isPropIsCocycle c)

  Z₂≡ : {c d : Z₂} → ((u v : ⟨ Q ⟩) → c .fst u v ≡ d .fst u v) → c ≡ d
  Z₂≡ h = Σ≡Prop isPropIsCocycle (funExt λ u → funExt λ v → h u v)

  ----------------------------------------------------------------
  -- 1b.  Z² is a group under pointwise addition
  ----------------------------------------------------------------

  0₂ : Z₂
  0₂ = (λ _ _ → A.1g) , λ _ _ _ → refl

  _+₂_ : Z₂ → Z₂ → Z₂
  (c , hc) +₂ (d , hd) =
      (λ u v → c u v A.· d u v)
    , λ u v w →
          middle4 (c u v) (d u v) (c (u Q.· v) w) (d (u Q.· v) w)
        ∙ cong₂ A._·_ (hc u v w) (hd u v w)
        ∙ middle4 (c v w) (c u (v Q.· w)) (d v w) (d u (v Q.· w))

  -₂_ : Z₂ → Z₂
  -₂ (c , hc) =
      (λ u v → A.inv (c u v))
    , λ u v w →
          sym (invDistr' (c u v) (c (u Q.· v) w))
        ∙ cong A.inv (hc u v w)
        ∙ invDistr' (c v w) (c u (v Q.· w))

  Z₂Group : Group (ℓ-max ℓ ℓ')
  Z₂Group = makeGroup-right 0₂ _+₂_ -₂_ isSetZ₂
              (λ a b c → Z₂≡ λ u v → A.·Assoc _ _ _)
              (λ a → Z₂≡ λ u v → A.·IdR _)
              (λ a → Z₂≡ λ u v → A.·InvR _)

  Z₂comm : (x y : ⟨ Z₂Group ⟩)
         → GroupStr._·_ (snd Z₂Group) x y ≡ GroupStr._·_ (snd Z₂Group) y x
  Z₂comm x y = Z₂≡ λ u v → Acomm _ _

  ----------------------------------------------------------------
  -- 1c.  coboundaries, and (i): coboundaries are cocycles
  ----------------------------------------------------------------

  δ : (⟨ Q ⟩ → ⟨ A ⟩) → C₂
  δ f u v = (f u A.· f v) A.· A.inv (f (u Q.· v))

  -- The same computation as `Carry.carry-cocycle` of CarryObstruction,
  -- which is that statement for a section of a surjection; here f is an
  -- arbitrary 1-cochain, so the hypotheses of that module are unavailable
  -- and the algebra is redone.  (At the arithmetic instance below the
  -- imported version is the one used, so the note's object is the one
  -- shown nonzero.)
  δ-isCocycle : (f : ⟨ Q ⟩ → ⟨ A ⟩) → isCocycle (δ f)
  δ-isCocycle f u v w = left ∙ sym right
    where
      a = f u ; b = f v ; c = f w
      d = f (u Q.· v) ; e = f (v Q.· w) ; g = f ((u Q.· v) Q.· w)

      left : δ f u v A.· δ f (u Q.· v) w ≡ ((a A.· b) A.· c) A.· A.inv g
      left =
          cong (((a A.· b) A.· A.inv d) A.·_) (sym (A.·Assoc d c (A.inv g)))
        ∙ slide (a A.· b) d (c A.· A.inv g)
        ∙ A.·Assoc (a A.· b) c (A.inv g)

      right : δ f v w A.· δ f u (v Q.· w) ≡ ((a A.· b) A.· c) A.· A.inv g
      right =
          cong (λ z → ((b A.· c) A.· A.inv e) A.· ((a A.· e) A.· A.inv (f z)))
               (Q.·Assoc u v w)
        ∙ cong (λ z → ((b A.· c) A.· A.inv e) A.· (z A.· A.inv g)) (Acomm a e)
        ∙ cong (((b A.· c) A.· A.inv e) A.·_) (sym (A.·Assoc e a (A.inv g)))
        ∙ slide (b A.· c) e (a A.· A.inv g)
        ∙ A.·Assoc (b A.· c) a (A.inv g)
        ∙ cong (A._· A.inv g) (Acomm (b A.· c) a)
        ∙ cong (A._· A.inv g) (A.·Assoc a b c)

  δ₂ : (⟨ Q ⟩ → ⟨ A ⟩) → Z₂
  δ₂ f = δ f , δ-isCocycle f

  isCoboundary : Z₂ → Type (ℓ-max ℓ ℓ')
  isCoboundary c = ∥ Σ[ f ∈ (⟨ Q ⟩ → ⟨ A ⟩) ]
                       ((u v : ⟨ Q ⟩) → δ f u v ≡ c .fst u v) ∥₁

  B₂Subset : ℙ Z₂
  B₂Subset c = isCoboundary c , PT.squash₁

  isSubgroupB₂ : isSubgroup Z₂Group B₂Subset
  id-closed isSubgroupB₂ =
    ∣ (λ _ → A.1g)
    , (λ u v → cong (A._· A.inv A.1g) (A.·IdR A.1g)
             ∙ cong (A.1g A.·_) inv1g
             ∙ A.·IdR A.1g) ∣₁
  op-closed isSubgroupB₂ =
    PT.map2 λ { (f , pf) (g , pg) →
      (λ x → f x A.· g x)
      , (λ u v →
            cong (A._· A.inv (f (u Q.· v) A.· g (u Q.· v)))
                 (middle4 (f u) (g u) (f v) (g v))
          ∙ cong (((f u A.· f v) A.· (g u A.· g v)) A.·_)
                 (invDistr' (f (u Q.· v)) (g (u Q.· v)))
          ∙ middle4 (f u A.· f v) (g u A.· g v)
                    (A.inv (f (u Q.· v))) (A.inv (g (u Q.· v)))
          ∙ cong₂ A._·_ (pf u v) (pg u v)) }
  inv-closed isSubgroupB₂ =
    PT.map λ { (f , pf) →
      (λ x → A.inv (f x))
      , (λ u v →
            cong (A._· A.inv (A.inv (f (u Q.· v))))
                 (sym (invDistr' (f u) (f v)))
          ∙ sym (invDistr' (f u A.· f v) (A.inv (f (u Q.· v))))
          ∙ cong A.inv (pf u v)) }

  B₂ : Subgroup Z₂Group
  B₂ = B₂Subset , isSubgroupB₂

  B₂normal : isNormal {G' = Z₂Group} B₂
  B₂normal x y hy = subst-∈ B₂Subset (sym conj) hy
    where
      open GroupStr (snd Z₂Group) using () renaming (_·_ to _⊕_ ; inv to inv₂)
      conj : (x ⊕ (y ⊕ inv₂ x)) ≡ y
      conj = cong (x ⊕_) (Z₂comm y (inv₂ x))
           ∙ GroupStr.·Assoc (snd Z₂Group) x (inv₂ x) y
           ∙ cong (_⊕ y) (GroupStr.·InvR (snd Z₂Group) x)
           ∙ GroupStr.·IdL (snd Z₂Group) y

  B₂NS : NormalSubgroup Z₂Group
  B₂NS = B₂ , B₂normal

  ----------------------------------------------------------------
  -- 1d.  H² := Z²/B², and effectivity
  ----------------------------------------------------------------

  H² : Group (ℓ-max ℓ ℓ')
  H² = Z₂Group / B₂NS

  class : Z₂ → ⟨ H² ⟩
  class c = [ c ]

  -- `class` is a homomorphism onto H², by construction of the quotient.
  classHom : GroupHom Z₂Group H²
  classHom = class , makeIsGroupHom λ _ _ → refl

  private
    _≈_ : Z₂ → Z₂ → Type (ℓ-max ℓ ℓ')
    _≈_ = _~_ Z₂Group B₂ B₂normal

    module ZG = GroupStr (snd Z₂Group)

    ≈isPropValued : isPropValued _≈_
    ≈isPropValued x y = PT.squash₁

    ≈sym : (x y : Z₂) → x ≈ y → y ≈ x
    ≈sym x y h = subst-∈ B₂Subset flip
                   (inv-closed isSubgroupB₂ {x = x ZG.· ZG.inv y} h)
      where
        flip : ZG.inv (x ZG.· ZG.inv y) ≡ (y ZG.· ZG.inv x)
        flip = GroupTheory.invDistr Z₂Group x (ZG.inv y)
             ∙ cong (ZG._· ZG.inv x) (GroupTheory.invInv Z₂Group y)

    ≈trans : (x y z : Z₂) → x ≈ y → y ≈ z → x ≈ z
    ≈trans x y z hxy hyz = subst-∈ B₂Subset collapse
                             (op-closed isSubgroupB₂
                               {x = x ZG.· ZG.inv y} {y = y ZG.· ZG.inv z}
                               hxy hyz)
      where
        collapse : ((x ZG.· ZG.inv y) ZG.· (y ZG.· ZG.inv z))
                 ≡ (x ZG.· ZG.inv z)
        collapse = AbTools.slide Z₂Group Z₂comm x y (ZG.inv z)

    ≈isEquivRel : isEquivRel _≈_
    ≈isEquivRel = equivRel (isRefl~ Z₂Group B₂ B₂normal) ≈sym ≈trans

  -- A class is zero exactly when its representative is a coboundary.
  class-zero→coboundary : (c : Z₂)
                        → class c ≡ GroupStr.1g (snd H²) → isCoboundary c
  class-zero→coboundary c p =
    subst-∈ B₂Subset tidy (effective ≈isPropValued ≈isEquivRel c 0₂ p)
    where
      tidy : (c ZG.· ZG.inv 0₂) ≡ c
      tidy = cong (c ZG.·_) (GroupTheory.inv1g Z₂Group) ∙ ZG.·IdR c

  coboundary→class-zero : (c : Z₂)
                        → isCoboundary c → class c ≡ GroupStr.1g (snd H²)
  coboundary→class-zero c h =
    SQ.eq/ c 0₂ (subst-∈ B₂Subset (sym tidy) h)
    where
      tidy : (c ZG.· ZG.inv 0₂) ≡ c
      tidy = cong (c ZG.·_) (GroupTheory.inv1g Z₂Group) ∙ ZG.·IdR c

------------------------------------------------------------------------
-- 2.  The carry class of an extension, with coefficients in ker π
------------------------------------------------------------------------

-- (Both groups at one universe level: the library's `kerSubgroup` is stated
-- for a homomorphism between groups of the same level.  The arithmetic
-- instance below is at level zero throughout.)
module CarryClass
  (G Q : Group ℓ)
  (Gcomm : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y
                         ≡ GroupStr._·_ (snd G) y x)
  (π : GroupHom G Q) (s : ⟨ Q ⟩ → ⟨ G ⟩)
  (sect : (q : ⟨ Q ⟩) → π .fst (s q) ≡ q)
  where

  private
    module G = GroupStr (snd G)
    module Q = GroupStr (snd Q)
  open AbTools G Gcomm

  -- The coefficient group: ker π, as a group in its own right.
  K : Group ℓ
  K = Subgroup→Group G (kerSubgroup π)

  private
    module K = GroupStr (snd K)

  ι : ⟨ K ⟩ → ⟨ G ⟩
  ι = fst

  ι-inj : {x y : ⟨ K ⟩} → ι x ≡ ι y → x ≡ y
  ι-inj = Σ≡Prop λ z → isPropIsInKer π z

  Kcomm : (x y : ⟨ K ⟩) → x K.· y ≡ y K.· x
  Kcomm x y = ι-inj (Gcomm (ι x) (ι y))

  open Cochain Q K Kcomm public

  ----------------------------------------------------------------
  -- the carry, with its cocycle identity IMPORTED from CarryObstruction
  ----------------------------------------------------------------

  private
    module CarryG = CO.Carry G Q π s sect

  carryK : Z₂
  carryK = (λ u v → CarryG.carry u v , CarryG.carry-inKer u v)
         , λ u v w → ι-inj (CarryG.carry-cocycle Gcomm u v w)

  -- ι of the carry is the carry.
  ι-carryK : (u v : ⟨ Q ⟩) → ι (carryK .fst u v) ≡ CarryG.carry u v
  ι-carryK u v = refl

  ----------------------------------------------------------------
  -- vanishing of the class  ⟺  the extension splits
  ----------------------------------------------------------------

  -- If [carryK] = 0 then π has a homomorphic section.  The conclusion is
  -- taken as a hypothesis-consumer so that the propositional truncation
  -- in `isCoboundary` may be eliminated.
  class-zero→hom-section :
      ((σ : GroupHom Q G) → ((q : ⟨ Q ⟩) → π .fst (σ .fst q) ≡ q) → ⊥)
    → ¬ (class carryK ≡ GroupStr.1g (snd H²))
  class-zero→hom-section noSplit p =
    PT.rec Empty.isProp⊥ build (class-zero→coboundary carryK p)
    where
      build : Σ[ f ∈ (⟨ Q ⟩ → ⟨ K ⟩) ]
                ((u v : ⟨ Q ⟩) → δ f u v ≡ carryK .fst u v) → ⊥
      build (f , pf) = noSplit (σ , makeIsGroupHom σ-pres) σ-sect
        where
          F : ⟨ Q ⟩ → ⟨ G ⟩
          F q = ι (f q)

          F-ker : (q : ⟨ Q ⟩) → π .fst (F q) ≡ Q.1g
          F-ker q = f q .snd

          -- the corrected section
          σ : ⟨ Q ⟩ → ⟨ G ⟩
          σ q = s q G.· G.inv (F q)

          σ-sect : (q : ⟨ Q ⟩) → π .fst (σ q) ≡ q
          σ-sect q =
              π .snd .pres· (s q) (G.inv (F q))
            ∙ cong₂ Q._·_ (sect q)
                (π .snd .presinv (F q) ∙ cong Q.inv (F-ker q)
                 ∙ GroupTheory.inv1g Q)
            ∙ Q.·IdR q

          -- ι of the coboundary equation, in G
          pfG : (u v : ⟨ Q ⟩)
              → ((F u G.· F v) G.· G.inv (F (u Q.· v)))
              ≡ ((s u G.· s v) G.· G.inv (s (u Q.· v)))
          pfG u v = cong ι (pf u v)

          σ-pres : (u v : ⟨ Q ⟩) → σ (u Q.· v) ≡ σ u G.· σ v
          σ-pres u v =
              sym (cross (s u G.· s v) (s (u Q.· v))
                         (F u G.· F v) (F (u Q.· v))
                         (sym (pfG u v)))
            ∙ cong ((s u G.· s v) G.·_) (invDistr' (F u) (F v))
            ∙ middle4 (s u) (s v) (G.inv (F u)) (G.inv (F v))

  -- Conversely, a homomorphic section makes the class vanish: the carry
  -- of s is then the coboundary of the difference cochain.  (Recorded for
  -- symmetry; the nonvanishing direction is the one used below.)
  hom-section→class-zero :
      (σ : GroupHom Q G) → ((q : ⟨ Q ⟩) → π .fst (σ .fst q) ≡ q)
    → class carryK ≡ GroupStr.1g (snd H²)
  hom-section→class-zero σ σsect =
    coboundary→class-zero carryK ∣ f , pf ∣₁
    where
      S : ⟨ Q ⟩ → ⟨ G ⟩
      S = σ .fst

      f : ⟨ Q ⟩ → ⟨ K ⟩
      f q = (s q G.· G.inv (S q))
          , ( π .snd .pres· (s q) (G.inv (S q))
            ∙ cong₂ Q._·_ (sect q)
                (π .snd .presinv (S q) ∙ cong Q.inv (σsect q))
            ∙ Q.·InvR q )

      pf : (u v : ⟨ Q ⟩) → δ f u v ≡ carryK .fst u v
      pf u v = ι-inj step
        where
          P T : ⟨ G ⟩
          P = s u G.· s v
          T = S u G.· S v

          first : (s u G.· G.inv (S u)) G.· (s v G.· G.inv (S v))
                ≡ P G.· G.inv T
          first = middle4 (s u) (G.inv (S u)) (s v) (G.inv (S v))
                ∙ cong (P G.·_) (sym (invDistr' (S u) (S v)))

          second : G.inv (s (u Q.· v) G.· G.inv (S (u Q.· v)))
                 ≡ G.inv (s (u Q.· v)) G.· T
          second = invDistr' (s (u Q.· v)) (G.inv (S (u Q.· v)))
                 ∙ cong (G.inv (s (u Q.· v)) G.·_)
                        (GroupTheory.invInv G (S (u Q.· v))
                         ∙ σ .snd .pres· u v)

          step : ((s u G.· G.inv (S u)) G.· (s v G.· G.inv (S v)))
                   G.· G.inv (s (u Q.· v) G.· G.inv (S (u Q.· v)))
               ≡ P G.· G.inv (s (u Q.· v))
          step =
              cong₂ G._·_ first second
            ∙ middle4 P (G.inv T) (G.inv (s (u Q.· v))) T
            ∙ cong ((P G.· G.inv (s (u Q.· v))) G.·_) (G.·InvL T)
            ∙ G.·IdR (P G.· G.inv (s (u Q.· v)))


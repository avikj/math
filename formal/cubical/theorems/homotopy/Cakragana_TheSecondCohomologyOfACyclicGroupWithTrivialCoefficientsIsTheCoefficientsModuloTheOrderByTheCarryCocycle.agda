{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Cakragana
--   The second cohomology of a cyclic group with trivial coefficients
--   is the coefficients modulo the order, by the carry cocycle.
--
--     H²(ℤ/m ; A)  ≅  A / mA        (m ≥ 1, A abelian, trivial action)
--
-- with H² the group Z²/B² constructed in `GroupCohomologyH2`, ℤ/m the
-- library's `ℤGroup/ m` (the carrier is `Fin m`, addition mod m), and
-- A/mA the library's `A /^ m` (the quotient of A by the image of
-- multiplication by m).  The isomorphism is induced by the invariant
--
--     σ(f) = Σ_{i<m} f(i, 1)
--
-- and its inverse sends a ∈ A to the class of the carry cocycle
--
--     c_a(i, j) = a · ⌊(i + j)/m⌋        (i, j the residues 0..m−1),
--
-- i.e. a if i + j carries and 0 otherwise.
--
-- Sources, quoted verbatim.
--
-- (1) theorems/homotopy/GroupCohomologyH2.agda, "NOT claimed here,
--     deliberately":
--
--       * H²(ℤ/m; A) ≅ A/mA.  The coefficient group here is `ker π` as a
--         subgroup of ℤ/bⁿ⁺¹, not `ℤ/b`; neither the isomorphism
--         bⁿℤ/bⁿ⁺¹ ≅ ℤ/b nor the computation of H² as A/mA is constructed.
--
-- (2) notes/FOUR_REPAIR_MODES.md (absent from this repository) (main), the seed:
--
--       2. **`PROVE`** — Construct $H^2(\mathbb Z/m;A)\cong A/mA$
--          constructively, discharging §4.1's $\Gamma_\circlearrowleft$.
--
-- (3) notes/ATLAS_OF_N.md (absent from this repository) (main):
--
--       Building $H^2$ of a cyclic group constructively, and identifying
--       it with $A/mA$, remains open.
--
-- What is proved, for m = suc n (so every m ≥ 1) and A : AbGroup ℓ:
--
--  (T1) `carry-cocycle`     the carry c_a is a 2-cocycle (the associativity
--                           of addition with carry: the number of carries
--                           in (i+j)+k and in i+(j+k) is ⌊(i+j+k)/m⌋ both
--                           ways, `q-add`).
--  (T2) `σδ`                σ(δh) = m · h(1): the telescoping identity.
--  (T3) `σ/hom`             σ descends to a homomorphism H²(ℤ/m;A) → A/mA.
--  (T4) `AtLeastTwo.σ-carry` σ(c_a) = a for m ≥ 2 (only (m−1, 1) carries);
--       `One.σ/-carry`      for m = 1 the class of σ(c_a) is [a] in A/1A = 0.
--  (T5) `normal-form`       every cocycle f is c_{σ f} + δh with the explicit
--                           h(k) = f(0,0) − Σ_{i<k} f(i,1); `carry-mult`
--                           c_{m·b} = δ(k ↦ k·b); `class-carry` [f] = [c_{σ f}].
--  (T6) `H²[ℤ/m,A]≅A/mA`    the isomorphism of groups, as a `GroupIso`,
--                           by `BijectionIso→GroupIso` from `σ/-inj`
--                           (T5) and `σ/-surj` (T4).
--
-- Instances (§6), both at m = 2:
--   `Instance-ℤ/2`:  H²(ℤ/2; ℤ/2) ≅ (ℤ/2)/2(ℤ/2)  and  [c₁] ≠ 0
--                    (`H²[ℤ/2,ℤ/2]≅ℤ/2/2`, `carry-class-1≠0`, via [1] ≠ [0]);
--   `Instance-ℤ`:    H²(ℤ/2; ℤ)   ≅ ℤ/2ℤ          and  [c₁] ≠ 0
--                    (`H²[ℤ/2,ℤ]≅ℤ/2ℤ`, `carry-class-1≠0`, via 1 odd).
-- The nonvanishing theorem of `CarryClassNonzero` is H²(ℤ/bⁿ; ker π) with
-- ker π ⊂ ℤ/bⁿ⁺¹, not ℤ/b; the instances here have the honest coefficient
-- group and the honest target group, which is what (1) says was missing.
-- (The library's `ℤ/2/2≅ℤ/2 : AbGroupIso (ℤ/2 /^ 2) ℤ/2` would identify the
-- first target with ℤ/2 itself; composing it is a one-liner, but see the
-- check-time note below.)
--
-- Conventions.  A cocycle is c(u,v) + c(u+v,w) = c(v,w) + c(u,v+w) and
-- δh(u,v) = h(u) + h(v) − h(u+v), exactly as in `GroupCohomologyH2`
-- (cochains are not normalised; the constant part of a cocycle is the
-- coboundary of a constant, which is why h carries the term f(0,0)).
-- The library's division `x mod m`, `quotient x / m` is used throughout;
-- `divInd` is a level-polymorphic division induction derived from
-- `≡remainder+quotient`, because the library's `+induction` is stated
-- for `Type₀`-valued predicates only.
--
-- Check-time note.  Every statement is kept in the module's own spelling
-- of the groups involved (`Cyclic.H² n A`, `Cyclic.A/mA n A`, and their
-- copies under `open`).  Restating H² as `Cochain.H² (ℤGroup/ suc n) …`,
-- typing a hom against `snd ℤGroup` instead of `snd G`, or composing with
-- a library isomorphism whose middle group is spelled differently, makes
-- Agda eta-expand quotient-group records during conversion checking; with
-- n abstract that costs ~30 s, at closed n = 1 it does not finish.  The
-- instances therefore instantiate `AtLeastTwo` by module application and
-- let the instance types be inferred.  The file checks in about 7 s.
--
-- Toolchain: Agda 2.8.0 + cubical v0.9, `--safe`, no postulates, no holes.
------------------------------------------------------------------------

module Cakragana_TheSecondCohomologyOfACyclicGroupWithTrivialCoefficientsIsTheCoefficientsModuloTheOrderByTheCarryCocycle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (_∈_ ; ∈-isProp ; subst-∈)

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Fin using (Fin ; fone)
open import Cubical.Data.Fin.Arithmetic using (_+ₘ_)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥ ; isProp⊥)

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup using (_~_ ; isRefl~)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_)
open import Cubical.Algebra.Group.Instances.IntMod
  using (ℤGroup/_ ; ℤ→Fin ; isHomℤ→Fin ; ℤ/2-elim)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Properties
  using (_/^_ ; multₗHom ; module AbGroupTheory)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.AbGroup.Instances.IntMod using (ℤAbGroup/_)

open import GroupCohomologyH2 using (module Cochain)

open IsGroupHom



private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 0.  Residues mod m = suc n, on top of the library's `mod`/`quotient`
------------------------------------------------------------------------

module Residues (n : ℕ) where

  m : ℕ
  m = suc n

  -- remainder and quotient of division by m
  r : ℕ → ℕ
  r x = x mod m

  q : ℕ → ℕ
  q x = quotient x / m

  r-base : (x : ℕ) → x < m → r x ≡ x
  r-base = modIndBase n

  r-step : (x : ℕ) → r (m + x) ≡ r x
  r-step = modIndStep n

  r< : (x : ℕ) → r x < m
  r< = mod< n

  q-base : (x : ℕ) → x < m → q x ≡ 0
  q-base = +inductionBase n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc)

  q-step : (x : ℕ) → q (m + x) ≡ suc (q x)
  q-step = +inductionStep n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc)

  divmod : (x : ℕ) → r x + m · q x ≡ x
  divmod = ≡remainder+quotient m

  -- Division induction, at any universe level.
  divInd : ∀ {ℓ'} (P : ℕ → Type ℓ')
         → ((x : ℕ) → x < m → P x)
         → ((x : ℕ) → P x → P (m + x))
         → (x : ℕ) → P x
  divInd P base step x = subst P (divmod x) (go (q x) (r x) (r< x))
    where
      go : (k y : ℕ) → y < m → P (y + m · k)
      go zero y p = subst P (sym (+-zero y) ∙ cong (y +_) (0≡m·0 m)) (base y p)
      go (suc k) y p = subst P shift (step (y + m · k) (go k y p))
        where
          shift : m + (y + m · k) ≡ y + m · suc k
          shift = +-assoc m y (m · k)
             ∙ cong (_+ m · k) (+-comm m y)
             ∙ sym (+-assoc y m (m · k))
             ∙ cong (y +_) (sym (·-suc m k))

  -- Carries compose: ⌊(x+y)/m⌋ = ⌊x/m⌋ + ⌊((x mod m) + y)/m⌋.
  q-add : (x y : ℕ) → q (x + y) ≡ q x + q (r x + y)
  q-add = +induction n (λ x → (y : ℕ) → q (x + y) ≡ q x + q (r x + y)) base step
    where
      base : (x : ℕ) → x < m → (y : ℕ) → q (x + y) ≡ q x + q (r x + y)
      base x p y = sym (cong₂ (λ a b → a + q (b + y)) (q-base x p) (r-base x p))

      step : (x : ℕ) → ((y : ℕ) → q (x + y) ≡ q x + q (r x + y))
           → (y : ℕ) → q ((m + x) + y) ≡ q (m + x) + q (r (m + x) + y)
      step x ih y =
          cong q (sym (+-assoc m x y))
        ∙ q-step (x + y)
        ∙ cong suc (ih y)
        ∙ sym (cong₂ (λ a b → a + q (b + y)) (q-step x) (r-step x))

  ----------------------------------------------------------------
  -- the cyclic group, and the residue map ι : ℕ → ℤ/m
  ----------------------------------------------------------------

  Q : Group₀
  Q = ℤGroup/ m

  ι : ℕ → Fin m
  ι k = r k , r< k

  ι-eta : (x : Fin m) → ι (fst x) ≡ x
  ι-eta x = Σ≡Prop (λ _ → isProp≤) (r-base (fst x) (snd x))

  ι-per : (k : ℕ) → ι (m + k) ≡ ι k
  ι-per k = Σ≡Prop (λ _ → isProp≤) (r-step k)

  ι-add : (x : Fin m) (k : ℕ) → x +ₘ ι k ≡ ι (fst x + k)
  ι-add x k = Σ≡Prop (λ _ → isProp≤) (sym (mod-rCancel m (fst x) k))

  -- the generator
  g : Fin m
  g = ι 1

  ι-suc : (k : ℕ) → ι k +ₘ g ≡ ι (suc k)
  ι-suc k = Σ≡Prop (λ _ → isProp≤) (sym (mod+mod≡mod m k 1) ∙ cong r (+-comm k 1))

  ι-zero : ι 0 ≡ GroupStr.1g (snd Q)
  ι-zero = Σ≡Prop (λ _ → isProp≤) (r-base 0 (suc-≤-suc zero-≤))

  ι-m : ι m ≡ ι 0
  ι-m = cong ι (sym (+-zero m)) ∙ ι-per 0

------------------------------------------------------------------------
-- 1.  Abelian-group bookkeeping: finite sums and natural multiples
------------------------------------------------------------------------

module AbAlg (A : AbGroup ℓ) where

  private
    module A = AbGroupStr (snd A)

  G : Group ℓ
  G = AbGroup→Group A

  open GroupTheory G using (invDistr ; invInv ; inv1g) public
  open AbGroupTheory A using (comm-4) public

  invDistr' : (x y : ⟨ A ⟩) → A.- (x A.+ y) ≡ (A.- x) A.+ (A.- y)
  invDistr' x y = invDistr x y ∙ A.+Comm _ _

  -- (P − D) + (D + X) ≡ P + X
  slide : (P D X : ⟨ A ⟩) → (P A.+ (A.- D)) A.+ (D A.+ X) ≡ P A.+ X
  slide P D X =
      sym (A.+Assoc _ _ _)
    ∙ cong (P A.+_) (A.+Assoc _ _ _ ∙ cong (A._+ X) (A.+InvL D) ∙ A.+IdL X)

  moveL : (c x y : ⟨ A ⟩) → c A.+ x ≡ y → x ≡ (A.- c) A.+ y
  moveL c x y p =
      sym (A.+IdL x)
    ∙ cong (A._+ x) (sym (A.+InvL c))
    ∙ sym (A.+Assoc _ _ _)
    ∙ cong ((A.- c) A.+_) p

  cancelR : (x y z : ⟨ A ⟩) → x A.+ z ≡ y A.+ z → x ≡ y
  cancelR x y z p =
      sym (A.+IdR x)
    ∙ cong (x A.+_) (sym (A.+InvR z))
    ∙ A.+Assoc _ _ _
    ∙ cong (A._+ (A.- z)) p
    ∙ sym (A.+Assoc _ _ _)
    ∙ cong (y A.+_) (A.+InvR z)
    ∙ A.+IdR y

  cancelL : (u v : ⟨ A ⟩) → (u A.+ v) A.+ (A.- u) ≡ v
  cancelL u v =
      cong (A._+ (A.- u)) (A.+Comm u v)
    ∙ sym (A.+Assoc _ _ _)
    ∙ cong (v A.+_) (A.+InvR u)
    ∙ A.+IdR v

  ----------------------------------------------------------------
  -- natural multiples  k ·A a  (= pos k ℤ[ G ]· a)
  ----------------------------------------------------------------

  infixl 8 _·A_

  _·A_ : ℕ → ⟨ A ⟩ → ⟨ A ⟩
  k ·A a = pos k ℤ[ G ]· a

  ·A-+ : (k l : ℕ) (a : ⟨ A ⟩) → (k + l) ·A a ≡ (k ·A a) A.+ (l ·A a)
  ·A-+ zero l a = sym (A.+IdL _)
  ·A-+ (suc k) l a = cong (a A.+_) (·A-+ k l a) ∙ A.+Assoc _ _ _

  ·A-mul : (k l : ℕ) (a : ⟨ A ⟩) → (k · l) ·A a ≡ k ·A (l ·A a)
  ·A-mul zero l a = refl
  ·A-mul (suc k) l a = ·A-+ l (k · l) a ∙ cong ((l ·A a) A.+_) (·A-mul k l a)

  ·A-one : (a : ⟨ A ⟩) → 1 ·A a ≡ a
  ·A-one a = A.+IdR a

  ----------------------------------------------------------------
  -- finite sums  Σ< k F = F 0 + ⋯ + F (k−1)
  ----------------------------------------------------------------

  Σ< : ℕ → (ℕ → ⟨ A ⟩) → ⟨ A ⟩
  Σ< zero F = A.0g
  Σ< (suc k) F = Σ< k F A.+ F k

  Σ<-ext : (k : ℕ) {F F' : ℕ → ⟨ A ⟩} → ((i : ℕ) → F i ≡ F' i) → Σ< k F ≡ Σ< k F'
  Σ<-ext k h = cong (Σ< k) (funExt h)

  Σ<-+ : (k : ℕ) (F F' : ℕ → ⟨ A ⟩)
       → Σ< k (λ i → F i A.+ F' i) ≡ Σ< k F A.+ Σ< k F'
  Σ<-+ zero F F' = sym (A.+IdL _)
  Σ<-+ (suc k) F F' = cong (A._+ (F k A.+ F' k)) (Σ<-+ k F F') ∙ comm-4 _ _ _ _

  Σ<-neg : (k : ℕ) (F : ℕ → ⟨ A ⟩) → Σ< k (λ i → A.- F i) ≡ A.- Σ< k F
  Σ<-neg zero F = sym inv1g
  Σ<-neg (suc k) F = cong (A._+ (A.- F k)) (Σ<-neg k F) ∙ sym (invDistr' _ _)

  Σ<-const : (k : ℕ) (c : ⟨ A ⟩) → Σ< k (λ _ → c) ≡ k ·A c
  Σ<-const zero c = refl
  Σ<-const (suc k) c = cong (A._+ c) (Σ<-const k c) ∙ A.+Comm _ _

  Σ<-tele : (k : ℕ) (H : ℕ → ⟨ A ⟩)
          → Σ< k (λ i → H i A.+ (A.- H (suc i))) ≡ H 0 A.+ (A.- H k)
  Σ<-tele zero H = sym (A.+InvR (H 0))
  Σ<-tele (suc k) H =
      cong (A._+ (H k A.+ (A.- H (suc k)))) (Σ<-tele k H)
    ∙ slide (H 0) (H k) (A.- H (suc k))

  Σ<-split : (a b : ℕ) (F : ℕ → ⟨ A ⟩)
           → Σ< (a + b) F ≡ Σ< a F A.+ Σ< b (λ l → F (a + l))
  Σ<-split a zero F = cong (λ z → Σ< z F) (+-zero a) ∙ sym (A.+IdR _)
  Σ<-split a (suc b) F =
      cong (λ z → Σ< z F) (+-suc a b)
    ∙ cong (A._+ F (a + b)) (Σ<-split a b F)
    ∙ sym (A.+Assoc _ _ _)

  Σ<-zero : (k : ℕ) (F : ℕ → ⟨ A ⟩) → ((i : ℕ) → i < k → F i ≡ A.0g) → Σ< k F ≡ A.0g
  Σ<-zero zero F h = refl
  Σ<-zero (suc k) F h =
      cong₂ A._+_ (Σ<-zero k F (λ i p → h i (<-trans p (0 , refl)))) (h k (0 , refl))
    ∙ A.+IdR _

------------------------------------------------------------------------
-- 2.  Effectivity of a quotient group  (x ~ y  is an equivalence relation)
------------------------------------------------------------------------

module Effective (G : Group ℓ) (H : NormalSubgroup G) where

  private
    module G = GroupStr (snd G)
    open GroupTheory G
    open isSubgroup (snd (fst H))

  R : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ
  R = _~_ G (fst H) (snd H)

  R-sym : (x y : ⟨ G ⟩) → R x y → R y x
  R-sym x y h =
    subst-∈ ⟪ fst H ⟫
      (invDistr x (G.inv y) ∙ cong (G._· G.inv x) (invInv y))
      (inv-closed h)

  R-trans : (x y z : ⟨ G ⟩) → R x y → R y z → R x z
  R-trans x y z hxy hyz = subst-∈ ⟪ fst H ⟫ collapse (op-closed hxy hyz)
    where
      collapse : (x G.· G.inv y) G.· (y G.· G.inv z) ≡ x G.· G.inv z
      collapse =
          sym (G.·Assoc _ _ _)
        ∙ cong (x G.·_) (G.·Assoc _ _ _ ∙ cong (G._· G.inv z) (G.·InvL y) ∙ G.·IdL _)

  R-equiv : isEquivRel R
  R-equiv = equivRel (isRefl~ G (fst H) (snd H)) R-sym R-trans

  effective : (x y : ⟨ G ⟩) → Path (⟨ G ⟩ SQ./ R) [ x ] [ y ] → R x y
  effective x y p = SQ.effective (λ a b → ∈-isProp ⟪ fst H ⟫ _) R-equiv x y p

------------------------------------------------------------------------
-- 3.  The cyclic group ℤ/m, its H², the carry cocycle and the invariant σ
------------------------------------------------------------------------

module Cyclic (n : ℕ) (A : AbGroup ℓ) where

  open Residues n public
  open AbAlg A public

  private
    module A = AbGroupStr (snd A)
    module Q = GroupStr (snd Q)

  -- H²(ℤ/m ; A) := Z²/B² of GroupCohomologyH2, at Q = ℤ/m, coefficients A.
  open Cochain Q G A.+Comm public

  ----------------------------------------------------------------
  -- 3a.  (T1) the carry cocycle
  ----------------------------------------------------------------

  carry : ⟨ A ⟩ → C₂
  carry a i j = q (fst i + fst j) ·A a

  carry-cocycle : (a : ⟨ A ⟩) → isCocycle (carry a)
  carry-cocycle a i j k =
      sym (·A-+ (q (fst i + fst j)) (q (r (fst i + fst j) + fst k)) a)
    ∙ cong (_·A a)
        ( sym (q-add (fst i + fst j) (fst k))
        ∙ cong q arith
        ∙ q-add (fst j + fst k) (fst i) )
    ∙ ·A-+ (q (fst j + fst k)) (q (r (fst j + fst k) + fst i)) a
    ∙ cong (λ z → (q (fst j + fst k) ·A a) A.+ (q z ·A a))
           (+-comm (r (fst j + fst k)) (fst i))
    where
      arith : (fst i + fst j) + fst k ≡ (fst j + fst k) + fst i
      arith = sym (+-assoc (fst i) (fst j) (fst k)) ∙ +-comm (fst i) (fst j + fst k)

  carryZ : ⟨ A ⟩ → Z₂
  carryZ a = carry a , carry-cocycle a

  ----------------------------------------------------------------
  -- 3b.  the invariant σ(f) = Σ_{i<m} f(i, 1), and (T2) σ(δh) = m·h(1)
  ----------------------------------------------------------------

  σ : C₂ → ⟨ A ⟩
  σ f = Σ< m (λ i → f (ι i) g)

  σ-+ : (f f' : C₂) → σ (λ u v → f u v A.+ f' u v) ≡ σ f A.+ σ f'
  σ-+ f f' = Σ<-+ m _ _

  σ-neg : (f : C₂) → σ (λ u v → A.- f u v) ≡ A.- σ f
  σ-neg f = Σ<-neg m _

  σδ : (h : Fin m → ⟨ A ⟩) → σ (δ h) ≡ m ·A h g
  σδ h =
      Σ<-ext m step
    ∙ Σ<-+ m _ _
    ∙ cong₂ A._+_
        (Σ<-const m (h g))
        ( Σ<-tele m (λ i → h (ι i))
        ∙ cong (λ z → h (ι 0) A.+ (A.- h z)) ι-m
        ∙ A.+InvR _ )
    ∙ A.+IdR _
    where
      step : (i : ℕ) → δ h (ι i) g ≡ h g A.+ (h (ι i) A.+ (A.- h (ι (suc i))))
      step i =
          cong (λ z → (h (ι i) A.+ h g) A.+ (A.- h z)) (ι-suc i)
        ∙ cong (A._+ (A.- h (ι (suc i)))) (A.+Comm _ _)
        ∙ sym (A.+Assoc _ _ _)

  ----------------------------------------------------------------
  -- 3c.  (T5) the normal form of a cocycle:  f = c_{σ f} + δh
  ----------------------------------------------------------------

  module Normal (f : C₂) (fc : isCocycle f) where

    F : ℕ → ⟨ A ⟩
    F k = f (ι k) g

    S : ℕ → ⟨ A ⟩
    S k = Σ< k F

    f₀₀ : ⟨ A ⟩
    f₀₀ = f Q.1g Q.1g

    -- an (unnormalised) cocycle is constant along the unit: f(i,0) = f(0,0)
    f-unitR : (i : Fin m) → f i Q.1g ≡ f₀₀
    f-unitR i = cancelR _ _ _
      ( cong (λ z → f i Q.1g A.+ f z Q.1g) (sym (Q.·IdR i))
      ∙ fc i Q.1g Q.1g
      ∙ cong (λ z → f₀₀ A.+ f i z) (Q.·IdL Q.1g) )

    F-per : (k : ℕ) → F (m + k) ≡ F k
    F-per k = cong (λ z → f z g) (ι-per k)

    S-split : (k : ℕ) → S (m + k) ≡ σ f A.+ S k
    S-split k = Σ<-split m k F ∙ cong (σ f A.+_) (Σ<-ext k F-per)

    -- the partial sums are periodic up to multiples of σ f
    S-per : (x : ℕ) → S x ≡ S (r x) A.+ (q x ·A σ f)
    S-per = divInd (λ x → S x ≡ S (r x) A.+ (q x ·A σ f)) base step
      where
        base : (x : ℕ) → x < m → S x ≡ S (r x) A.+ (q x ·A σ f)
        base x p = sym ( cong₂ (λ a b → S a A.+ (b ·A σ f)) (r-base x p) (q-base x p)
                       ∙ A.+IdR _ )

        step : (x : ℕ) → S x ≡ S (r x) A.+ (q x ·A σ f)
             → S (m + x) ≡ S (r (m + x)) A.+ (q (m + x) ·A σ f)
        step x ih =
            S-split x
          ∙ cong (σ f A.+_) ih
          ∙ A.+Assoc _ _ _
          ∙ cong (A._+ (q x ·A σ f)) (A.+Comm _ _)
          ∙ sym (A.+Assoc _ _ _)
          ∙ sym (cong₂ (λ a b → S a A.+ (b ·A σ f)) (r-step x) (q-step x))

    -- the unbounded normal form, by induction on the second argument
    Φ : Fin m → ℕ → ⟨ A ⟩
    Φ i j = (f₀₀ A.+ S (fst i + j)) A.+ (A.- (S (fst i) A.+ S j))

    private
      rearr : (e Sx Fx Si Sj Fj : ⟨ A ⟩)
            → (A.- Fj) A.+ (((e A.+ Sx) A.+ (A.- (Si A.+ Sj))) A.+ Fx)
            ≡ (e A.+ (Sx A.+ Fx)) A.+ (A.- (Si A.+ (Sj A.+ Fj)))
      rearr e Sx Fx Si Sj Fj = sym
        ( cong₂ A._+_ (A.+Assoc e Sx Fx)
                      (cong A.-_ (A.+Assoc Si Sj Fj) ∙ invDistr' (Si A.+ Sj) Fj)
        ∙ comm-4 (e A.+ Sx) Fx u (A.- Fj)
        ∙ cong (((e A.+ Sx) A.+ u) A.+_) (A.+Comm Fx (A.- Fj))
        ∙ A.+Assoc ((e A.+ Sx) A.+ u) (A.- Fj) Fx
        ∙ cong (A._+ Fx) (A.+Comm ((e A.+ Sx) A.+ u) (A.- Fj))
        ∙ sym (A.+Assoc (A.- Fj) ((e A.+ Sx) A.+ u) Fx) )
        where
          u : ⟨ A ⟩
          u = A.- (Si A.+ Sj)

    nf : (i : Fin m) (j : ℕ) → f i (ι j) ≡ Φ i j
    nf i zero =
        cong (f i) ι-zero
      ∙ f-unitR i
      ∙ sym ( cong₂ (λ a b → (f₀₀ A.+ S a) A.+ (A.- b)) (+-zero (fst i)) (A.+IdR (S (fst i)))
            ∙ sym (A.+Assoc _ _ _)
            ∙ cong (f₀₀ A.+_) (A.+InvR _)
            ∙ A.+IdR _ )
    nf i (suc j) =
        cong (f i) (sym (ι-suc j))
      ∙ moveL (F j) _ _ (sym (fc i (ι j) g))
      ∙ cong (λ z → (A.- F j) A.+ (f i (ι j) A.+ f z g)) (ι-add i j)
      ∙ cong (λ z → (A.- F j) A.+ (z A.+ F (fst i + j))) (nf i j)
      ∙ rearr f₀₀ (S (fst i + j)) (F (fst i + j)) (S (fst i)) (S j) (F j)
      ∙ sym (cong (λ z → (f₀₀ A.+ S z) A.+ (A.- (S (fst i) A.+ S (suc j))))
                  (+-suc (fst i) j))

    -- the 1-cochain
    h : Fin m → ⟨ A ⟩
    h k = (A.- S (fst k)) A.+ f₀₀

    private
      nf-alg : (e a s Si Sj : ⟨ A ⟩)
             → (e A.+ (a A.+ s)) A.+ (A.- (Si A.+ Sj))
             ≡ s A.+ ((((A.- Si) A.+ e) A.+ ((A.- Sj) A.+ e)) A.+ (A.- ((A.- a) A.+ e)))
      nf-alg e a s Si Sj =
          cong ((e A.+ (a A.+ s)) A.+_) (invDistr' Si Sj)
        ∙ cong (A._+ u) (A.+Assoc e a s ∙ A.+Comm (e A.+ a) s)
        ∙ sym (A.+Assoc s (e A.+ a) u)
        ∙ cong (s A.+_) (A.+Comm (e A.+ a) u)
        ∙ cong (s A.+_) (sym inner)
        where
          u : ⟨ A ⟩
          u = (A.- Si) A.+ (A.- Sj)

          inner : (((A.- Si) A.+ e) A.+ ((A.- Sj) A.+ e)) A.+ (A.- ((A.- a) A.+ e))
                ≡ u A.+ (e A.+ a)
          inner =
              cong₂ A._+_ (comm-4 (A.- Si) e (A.- Sj) e)
                          (invDistr' (A.- a) e ∙ cong (A._+ (A.- e)) (invInv a))
            ∙ sym (A.+Assoc u (e A.+ e) (a A.+ (A.- e)))
            ∙ cong (u A.+_)
                ( comm-4 e e a (A.- e)
                ∙ cong ((e A.+ a) A.+_) (A.+InvR e)
                ∙ A.+IdR (e A.+ a) )

    -- THE NORMAL FORM.  f(i,j) = c_{σ f}(i,j) + δh(i,j).
    normal-form : (i j : Fin m) → f i j ≡ carry (σ f) i j A.+ δ h i j
    normal-form i j =
        cong (f i) (sym (ι-eta j))
      ∙ nf i (fst j)
      ∙ cong (λ z → (f₀₀ A.+ z) A.+ (A.- (S (fst i) A.+ S (fst j))))
             (S-per (fst i + fst j))
      ∙ nf-alg f₀₀ (S (r (fst i + fst j))) (q (fst i + fst j) ·A σ f)
               (S (fst i)) (S (fst j))

  -- c_{m·b} is the coboundary of k ↦ k·b.
  carry-mult : (b : ⟨ A ⟩) (i j : Fin m)
             → carry (m ·A b) i j ≡ δ (λ k → fst k ·A b) i j
  carry-mult b i j =
      sym (·A-mul (q x) m b)
    ∙ cong (_·A b) (·-comm (q x) m)
    ∙ sym (cancelL (r x ·A b) _)
    ∙ cong (A._+ (A.- (r x ·A b)))
        ( sym (·A-+ (r x) (m · q x) b)
        ∙ cong (_·A b) (divmod x)
        ∙ ·A-+ (fst i) (fst j) b )
    where
      x : ℕ
      x = fst i + fst j

  δ-+ : (h h' : Fin m → ⟨ A ⟩) (u v : Fin m)
      → δ (λ k → h k A.+ h' k) u v ≡ δ h u v A.+ δ h' u v
  δ-+ h h' u v =
      cong₂ A._+_ (comm-4 (h u) (h' u) (h v) (h' v))
                  (invDistr' (h (u +ₘ v)) (h' (u +ₘ v)))
    ∙ comm-4 _ _ _ _

  -- Every class is the class of a carry cocycle:  [f] = [c_{σ f}].
  class-carry : (z : Z₂) → class z ≡ class (carryZ (σ (fst z)))
  class-carry z = eq/ z (carryZ (σ (fst z))) ∣ h , (λ u v →
      sym (cancelL (carry (σ (fst z)) u v) (δ h u v))
    ∙ cong (A._+ (A.- carry (σ (fst z)) u v)) (sym (normal-form u v))) ∣₁
    where
      open Normal (fst z) (snd z)

  ----------------------------------------------------------------
  -- 3d.  (T3) σ descends:  σ/ : H²(ℤ/m ; A) → A/mA
  ----------------------------------------------------------------

  -- mA ⊂ A, the image of multiplication by m, and A/mA (the library's A /^ m)
  mA : NormalSubgroup G
  mA = imSubgroup (multₗHom A (pos m)) , isNormalIm (multₗHom A (pos m)) A.+Comm

  A/mA : Group ℓ
  A/mA = AbGroup→Group (A /^ m)

  open Effective G mA public using () renaming (effective to effective-mA)

  σ/ : ⟨ H² ⟩ → ⟨ A/mA ⟩
  σ/ = SQ.rec squash/ (λ z → [ σ (fst z) ]) resp
    where
      resp : (z z' : Z₂) → _~_ Z₂Group B₂ B₂normal z z'
           → Path ⟨ A/mA ⟩ [ σ (fst z) ] [ σ (fst z') ]
      resp z z' = PT.rec (squash/ _ _) λ { (h , ph) →
        eq/ _ _ ∣ h g
                , ( sym (σδ h)
                  ∙ Σ<-ext m (λ i → ph (ι i) g)
                  ∙ Σ<-+ m _ _
                  ∙ cong (σ (fst z) A.+_) (Σ<-neg m _) ) ∣₁ }

  σ/hom : GroupHom H² A/mA
  σ/hom = σ/ , makeIsGroupHom
                 (SQ.elimProp2 (λ _ _ → squash/ _ _) λ z z' → cong [_] (Σ<-+ m _ _))

  ----------------------------------------------------------------
  -- 3e.  injectivity (from T5) and the assembly hook (T6)
  ----------------------------------------------------------------

  σ/-inj : isInjective σ/hom
  σ/-inj = SQ.elimProp (λ _ → isPropΠ λ _ → squash/ _ _) inj-rep
    where
      inj-rep : (z : Z₂) → Path ⟨ A/mA ⟩ [ σ (fst z) ] [ A.0g ] → Path ⟨ H² ⟩ [ z ] [ 0₂ ]
      inj-rep z p = coboundary→class-zero z (PT.map witness (effective-mA (σ (fst z)) A.0g p))
        where
          open Normal (fst z) (snd z)

          witness : Σ[ b ∈ ⟨ A ⟩ ] (m ·A b ≡ σ (fst z) A.+ (A.- A.0g))
                  → Σ[ h' ∈ (Fin m → ⟨ A ⟩) ] ((u v : Fin m) → δ h' u v ≡ fst z u v)
          witness (b , pb) = (λ k → h k A.+ (fst k ·A b)) , λ u v →
              δ-+ h (λ k → fst k ·A b) u v
            ∙ cong (δ h u v A.+_)
                ( sym (carry-mult b u v)
                ∙ cong (λ a → carry a u v) (pb ∙ cong (σ (fst z) A.+_) inv1g ∙ A.+IdR _) )
            ∙ A.+Comm _ _
            ∙ sym (normal-form u v)

  module Assemble (σ/-carry : (a : ⟨ A ⟩) → Path ⟨ A/mA ⟩ [ σ (carry a) ] [ a ]) where

    σ/-surj : isSurjective σ/hom
    σ/-surj = SQ.elimProp (λ _ → squash₁) λ a → ∣ class (carryZ a) , σ/-carry a ∣₁

    H²≅A/mA : GroupIso H² A/mA
    H²≅A/mA = BijectionIso→GroupIso (bijIso σ/hom σ/-inj σ/-surj)

------------------------------------------------------------------------
-- 4.  (T4) surjectivity:  σ(c_a) = a for m ≥ 2, and the case m = 1
------------------------------------------------------------------------

module AtLeastTwo (n' : ℕ) (A : AbGroup ℓ) where

  open Cyclic (suc n') A public
  private
    module A = AbGroupStr (snd A)

  g≡1 : fst g ≡ 1
  g≡1 = r-base 1 (suc-≤-suc (suc-≤-suc zero-≤))

  -- Among the pairs (i, 1) with i < m exactly one carries, (m−1, 1).
  σ-carry : (a : ⟨ A ⟩) → σ (carry a) ≡ a
  σ-carry a = cong₂ A._+_ (Σ<-zero (suc n') _ vanish) top ∙ A.+IdL a
    where
      vanish : (i : ℕ) → i < suc n' → q (fst (ι i) + fst g) ·A a ≡ A.0g
      vanish i p =
          cong (λ z → q z ·A a)
               (cong₂ _+_ (r-base i (<-trans p (0 , refl))) g≡1 ∙ +-comm i 1)
        ∙ cong (_·A a) (q-base (suc i) (suc-≤-suc p))

      top : q (fst (ι (suc n')) + fst g) ·A a ≡ a
      top =
          cong (λ z → q z ·A a)
               ( cong₂ _+_ (r-base (suc n') (0 , refl)) g≡1
               ∙ +-comm (suc n') 1
               ∙ sym (+-zero m) )
        ∙ cong (_·A a) (q-step 0 ∙ cong suc (q-base 0 (suc-≤-suc zero-≤)))
        ∙ ·A-one a

  σ/-carry : (a : ⟨ A ⟩) → Path ⟨ A/mA ⟩ [ σ (carry a) ] [ a ]
  σ/-carry a = cong [_] (σ-carry a)

  -- the isomorphism at m ≥ 2, assembled here (n' abstract)
  H²≅A/mA : GroupIso H² A/mA
  H²≅A/mA = Assemble.H²≅A/mA σ/-carry

  -- if [a] ≠ 0 in A/mA then the carry class [c_a] ≠ 0 in H²
  carry-class≠0 : (a : ⟨ A ⟩) → ¬ (Path ⟨ A/mA ⟩ [ a ] [ A.0g ])
                → ¬ (class (carryZ a) ≡ GroupStr.1g (snd H²))
  carry-class≠0 a ne p = ne (sym (σ/-carry a) ∙ cong σ/ p ∙ pres1 (snd σ/hom))

module One (A : AbGroup ℓ) where

  open Cyclic 0 A public
  private
    module A = AbGroupStr (snd A)

  -- A/1A is trivial (every x is 1·x), so [σ(c_a)] = [a] whatever σ(c_a) is.
  σ/-carry : (a : ⟨ A ⟩) → Path ⟨ A/mA ⟩ [ σ (carry a) ] [ a ]
  σ/-carry a = eq/ _ _ ∣ σ (carry a) A.+ (A.- a) , ·A-one _ ∣₁

------------------------------------------------------------------------
-- 5.  (T6) THE THEOREM:  H²(ℤ/m ; A) ≅ A/mA   for every m ≥ 1
------------------------------------------------------------------------

σ/-carry-class : (n : ℕ) (A : AbGroup ℓ) (a : ⟨ A ⟩)
               → Path ⟨ Cyclic.A/mA n A ⟩ [ Cyclic.σ n A (Cyclic.carry n A a) ] [ a ]
σ/-carry-class zero A = One.σ/-carry A
σ/-carry-class (suc n') A = AtLeastTwo.σ/-carry n' A

-- THE THEOREM.  H²(ℤ/m ; A) ≅ A/mA.
--
--   `Cyclic.H² n A`   is, by definition,
--        Cochain.H² (ℤGroup/ suc n) (AbGroup→Group A) (AbGroupStr.+Comm (snd A)),
--   the group Z²/B² of GroupCohomologyH2 at Q = ℤ/m with coefficients A;
--   `Cyclic.A/mA n A` is, by definition,  AbGroup→Group (A /^ suc n),
--   the library's A/mA.
-- (The statement is kept in the module's own spelling of the two groups:
-- respelling either side makes Agda eta-expand the quotient-group records
-- during conversion checking, which does not terminate in practice.)
--
-- The map is σ/ : [f] ↦ [Σ_{i<m} f(i,1)]; its inverse on representatives
-- is a ↦ [c_a].  `σ/-carry-class` and `Cyclic.class-carry` are the two
-- round trips on representatives.
H²[ℤ/m,A]≅A/mA : (n : ℕ) (A : AbGroup ℓ) → GroupIso (Cyclic.H² n A) (Cyclic.A/mA n A)
H²[ℤ/m,A]≅A/mA n A = Cyclic.Assemble.H²≅A/mA n A (σ/-carry-class n A)

H²[ℤ/m,A]≃A/mA : (n : ℕ) (A : AbGroup ℓ) → GroupEquiv (Cyclic.H² n A) (Cyclic.A/mA n A)
H²[ℤ/m,A]≃A/mA n A = GroupIso→GroupEquiv (H²[ℤ/m,A]≅A/mA n A)

------------------------------------------------------------------------
-- 6.  Instances at m = 2:  the class of the carry cocycle c₁ is nonzero
------------------------------------------------------------------------

-- 6a.  Coefficients ℤ/2 (the library's ℤAbGroup/ 2, carrier Fin 2).
--      H²(ℤ/2 ; ℤ/2) ≅ (ℤ/2)/2(ℤ/2), and [c₁] ≠ 0.  (The library's
--      `ℤ/2/2≅ℤ/2` identifies the target with ℤ/2 itself.)
module Instance-ℤ/2 where

  private
    X : AbGroup ℓ-zero
    X = ℤAbGroup/ 2
    module A = AbGroupStr (snd X)

  open AtLeastTwo 0 X public

  private
    -- 2·x = 0 in ℤ/2  (only the underlying naturals are computed)
    two-x : (x : Fin 2) → 2 ·A x ≡ A.0g
    two-x = ℤ/2-elim (Σ≡Prop (λ _ → isProp≤) refl) (Σ≡Prop (λ _ → isProp≤) refl)

  -- [1] ≠ [0] in (ℤ/2)/2(ℤ/2)
  [1]≠[0] : ¬ (Path ⟨ A/mA ⟩ [ fone ] [ A.0g ])
  [1]≠[0] p = PT.rec isProp⊥ contra (effective-mA fone A.0g p)
    where
      contra : Σ[ b ∈ Fin 2 ] (2 ·A b ≡ fone A.+ (A.- A.0g)) → ⊥
      contra (b , pb) =
        znots (cong fst (sym (two-x b) ∙ pb ∙ cong (fone A.+_) inv1g ∙ A.+IdR fone))

  -- H²(ℤ/2 ; ℤ/2) ≅ (ℤ/2)/2(ℤ/2)        (type inferred: GroupIso H² A/mA)
  H²[ℤ/2,ℤ/2]≅ℤ/2/2 = H²≅A/mA

  -- σ(c₁) = 1, and [c₁] ≠ 0 in H²(ℤ/2 ; ℤ/2)
  σ-carry-1 = σ-carry fone
  carry-class-1≠0 = carry-class≠0 fone [1]≠[0]

-- 6b.  Coefficients ℤ.  H²(ℤ/2 ; ℤ) ≅ ℤ/2ℤ, and [c₁] ≠ 0.
module Instance-ℤ where

  private
    module Z = AbGroupStr (snd ℤAbGroup)

  open AtLeastTwo 0 ℤAbGroup public

  private
    x+x : (x : Fin 2) → x +ₘ x ≡ GroupStr.1g (snd (ℤGroup/ 2))
    x+x = ℤ/2-elim (Σ≡Prop (λ _ → isProp≤) refl) (Σ≡Prop (λ _ → isProp≤) refl)

    -- 2·b = b + b reduces to 0 mod 2 (ℤ→Fin 1 is reduction mod 2, a homomorphism)
    double : (b : ℤ) → ℤ→Fin 1 (2 ·A b) ≡ GroupStr.1g (snd (ℤGroup/ 2))
    double b = pres· (isHomℤ→Fin 1) b b ∙ x+x (ℤ→Fin 1 b)

  -- [1] ≠ [0] in ℤ/2ℤ  (1 is odd)
  [1]≠[0] : ¬ (Path ⟨ A/mA ⟩ [ pos 1 ] [ pos 0 ])
  [1]≠[0] p = PT.rec isProp⊥ contra (effective-mA (pos 1) (pos 0) p)
    where
      contra : Σ[ b ∈ ℤ ] (2 ·A b ≡ pos 1 Z.+ (Z.- pos 0)) → ⊥
      contra (b , pb) = znots (cong fst (sym (double b) ∙ cong (ℤ→Fin 1) pb))

  -- H²(ℤ/2 ; ℤ) ≅ ℤ/2ℤ                   (type inferred: GroupIso H² A/mA)
  H²[ℤ/2,ℤ]≅ℤ/2ℤ = H²≅A/mA

  -- σ(c₁) = 1, and [c₁] ≠ 0 in H²(ℤ/2 ; ℤ)
  σ-carry-1 = σ-carry (pos 1)
  carry-class-1≠0 = carry-class≠0 (pos 1) [1]≠[0]

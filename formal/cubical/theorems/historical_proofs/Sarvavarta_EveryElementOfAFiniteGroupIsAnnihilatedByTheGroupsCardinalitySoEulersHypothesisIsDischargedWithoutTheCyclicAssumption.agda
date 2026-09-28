{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सर्वावर्तः — every element of a finite group is annihilated by the
-- group's own cardinality: Euler's theorem for a GENERAL finite group,
-- so the hypothesis that RSA isolates to is discharged without the
-- cyclic assumption.
--
-- ────────────────────────────────────────────────────────────────────
-- `Avarta_TheGeneratorsOrderAnnihilatesEveryPowerSoEulersHypothesisIs
-- DischargedOnACyclicGroup.agda` (absent from this repository) proves `यूलर-सिद्धिः` for a group GIVEN
-- as cyclic.
-- Lagrange is in this corpus: `theorems/unplaced/
-- SubgroupIndex.agda` proves, for a group `G` with `finG : isFinSet ⟨ G ⟩`
-- and a subgroup `H` with decidable membership,
--
--     lagrange : card FG ≡ index ·ℕ order        (order = card of H).
--
-- This file supplies the two things SubgroupIndex does not have and
-- Avarta's theorem needs — the cyclic subgroup of an element, and the
-- count of its elements — and then reads Euler's theorem off Lagrange.
--
-- WHAT IS PROVED.  For every group `G : Group ℓ` (the library's
-- `Cubical.Algebra.Group`), every `finG : isFinSet ⟨ G ⟩`, and every
-- element `a : ⟨ G ⟩`, writing `a ^ n` for the n-fold product:
--
--   §1  `Least`      for a decidable proposition-valued `P : ℕ → Type`,
--                    a least witness from any witness, and a decision of
--                    `Σ k < n, P k` by bounded search;
--   §2  `Powers`     `a ^ (m + n) ≡ a ^ m · a ^ n`, `a ^ (m ·ℕ n) ≡ (a ^ m) ^ n`,
--                    `1g ^ n ≡ 1g`, right-absorption cancels to `1g`;
--   §3  `hasOrder`   two of the powers a⁰ … a^|G| coincide (the library's
--                    `pigeonhole` through the equivalence `⟨ G ⟩ ≃ Fin |G|`),
--                    so some d > 0 has `a ^ d ≡ 1g`; `e` is the LEAST such;
--   §4  `cycSub`     the cyclic subgroup { x | ∃ k, a ^ k ≡ x } is a
--                    `Subgroup G` with decidable membership (search k < e);
--   §5  `cycIso`     its carrier is in bijection with `Fin e`, so
--                    `cardCyc : order ≡ e` for SubgroupIndex's `order`;
--   §6  `euler`      `a ^ card (⟨ G ⟩ , finG) ≡ 1g`,
--                    `orderDivides : e ∣ card (⟨ G ⟩ , finG)`;
--   §7  `Abelian`    on a finite ABELIAN group the same theorem in the
--                    `घात` vocabulary of Bijamula/Avarta, and hence RSA
--                    correctness (`बीजमूल-सिद्धि`) with NO Euler hypothesis
--                    and no cyclic hypothesis: only the pulverizer's
--                    witness `e ·ℕ d ≡ |G| ·ℕ k + 1` remains.
--
-- The route is the classical one.  (i) In a finite set the powers of `a`
-- cannot all be distinct, so `a` has a finite order `e` (least positive
-- exponent with `a ^ e ≡ 1g`).  (ii) The powers `a ^ k`, `k < e`, are
-- pairwise distinct (a coincidence would give a smaller positive
-- exponent) and exhaust the cyclic subgroup (any exponent reduces below
-- `e` by peeling off `a ^ e ≡ 1g`), so the cyclic subgroup has exactly
-- `e` elements.  (iii) Lagrange gives `|G| = index ·ℕ e`.  (iv) Then
-- `a ^ |G| ≡ (a ^ e) ^ index ≡ 1g ^ index ≡ 1g`, which is exactly the
-- arithmetic Avarta's `जनक-आवर्तः` used, now with `e` supplied by
-- counting rather than assumed of a generator.
--
-- §7 takes the abelian finite
-- group as its hypotheses, exactly as Avarta takes the cyclic one.
-- The order `e` is characterised as the least positive annihilating
-- exponent and shown equal to the cardinality of the cyclic
-- subgroup.
--
-- ────────────────────────────────────────────────────────────────────
-- ON THE NAME.  सर्व (all) + आवर्त (a turning; the word Avarta chose for
-- a group that comes back to where it started): "every turning", i.e.
-- every element turns back to the identity.  Ordinary , the
-- compound is built here, and **NO SOURCE IS CLAIMED FOR IT AS A
-- TECHNICAL TERM**.  The group theory is Lagrange's and Euler's, not
-- Indian, and is not dressed as Indian; only §7's vocabulary (घात,
-- Pigala's fold; the kuaka witness, ryabhaa's) is inherited from
-- the sibling modules, with their citations, second-hand.
------------------------------------------------------------------------

module Sarvavarta_EveryElementOfAFiniteGroupIsAnnihilatedByTheGroupsCardinalitySoEulersHypothesisIsDischargedWithoutTheCyclicAssumption where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
-- ℕ multiplication is `_·ℕ_` throughout, the group operation is `_·_`
-- (the same disambiguation SubgroupIndex uses).
open import Cubical.Data.Nat hiding (_·_ ; _^_)
open import Cubical.Data.Nat using () renaming (_·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility using (_∣_)
open import Cubical.Data.Fin using (Fin ; toℕ-injective ; pigeonhole)
-- `isFinSet` is phrased with the SUM-built `Fin` of Cubical.Data.SumFin;
-- the pigeonhole is stated for the Σ-built `Fin` of Cubical.Data.Fin.
-- `SumFin≃Fin` is the library's bridge between the two.
open import Cubical.Data.SumFin using (SumFin≃Fin) renaming (Fin to SumFin)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥ ; isProp⊥)

open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_ ; Discrete)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality using (cardEquiv)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Subgroup

open import SubgroupIndex using (module Index)
open import Bijamula_TheRSAPrivateKeyIsThePulverizersWitnessAndDecryptionIsPingalasExponentiation
  using (CMonoid ; घात ; बीजमूल-सिद्धि)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  Least witnesses of a decidable predicate on ℕ, by bounded search.
------------------------------------------------------------------------

module Least {ℓ' : Level} (P : ℕ → Type ℓ')
             (isPropP : (n : ℕ) → isProp (P n))
             (decP : (n : ℕ) → Dec (P n)) where

  Minimal : ℕ → Type ℓ'
  Minimal e = P e × ((k : ℕ) → k < e → ¬ P k)

  isPropMinimal : (e : ℕ) → isProp (Minimal e)
  isPropMinimal e = isProp× (isPropP e) (isPropΠ3 (λ _ _ _ → isProp⊥))

  Least : Type ℓ'
  Least = Σ[ e ∈ ℕ ] Minimal e

  -- the least witness is unique, so `Least` is a proposition: this is
  -- what lets it be extracted from a merely-existing witness.
  isPropLeast : isProp Least
  isPropLeast (e , pe , me) (e' , pe' , me') = Σ≡Prop isPropMinimal (lemma (e ≟ e'))
    where
    lemma : Trichotomy e e' → e ≡ e'
    lemma (lt e<e') = Empty.rec (me' e e<e' pe)
    lemma (eq p)    = p
    lemma (gt e'<e) = Empty.rec (me e' e'<e pe')

  -- search below n: either a least witness below n, or none below n.
  below : (n : ℕ)
        → (Σ[ e ∈ ℕ ] (e < n) × Minimal e) ⊎ ((k : ℕ) → k < n → ¬ P k)
  below zero = inr (λ k k<0 _ → ¬-<-zero k<0)
  below (suc n) = step (below n)
    where
    split : (k : ℕ) → ((j : ℕ) → j < n → ¬ P j) → ¬ P n
          → (k < n) ⊎ (k ≡ n) → ¬ P k
    split k none ¬pn (inl k<n) = none k k<n
    split k none ¬pn (inr k≡n) = λ pk → ¬pn (subst P k≡n pk)

    step' : ((j : ℕ) → j < n → ¬ P j) → Dec (P n)
          → (Σ[ e ∈ ℕ ] (e < suc n) × Minimal e) ⊎ ((k : ℕ) → k < suc n → ¬ P k)
    step' none (yes pn) = inl (n , ≤-refl , pn , none)
    step' none (no ¬pn) = inr (λ k k<sn → split k none ¬pn (<-split k<sn))

    step : (Σ[ e ∈ ℕ ] (e < n) × Minimal e) ⊎ ((k : ℕ) → k < n → ¬ P k)
         → (Σ[ e ∈ ℕ ] (e < suc n) × Minimal e) ⊎ ((k : ℕ) → k < suc n → ¬ P k)
    step (inl (e , e<n , m)) = inl (e , ≤-suc e<n , m)
    step (inr none)          = step' none (decP n)

  decBelow : (n : ℕ) → Dec (Σ[ k ∈ ℕ ] (k < n) × P k)
  decBelow n = go (below n)
    where
    go : (Σ[ e ∈ ℕ ] (e < n) × Minimal e) ⊎ ((k : ℕ) → k < n → ¬ P k)
       → Dec (Σ[ k ∈ ℕ ] (k < n) × P k)
    go (inl (e , e<n , pe , _)) = yes (e , e<n , pe)
    go (inr none) = no (λ w → none (fst w) (fst (snd w)) (snd (snd w)))

  fromWitness : (d : ℕ) → P d → Least
  fromWitness d pd = go (below (suc d))
    where
    go : (Σ[ e ∈ ℕ ] (e < suc d) × Minimal e) ⊎ ((k : ℕ) → k < suc d → ¬ P k) → Least
    go (inl (e , _ , m)) = e , m
    go (inr none)        = Empty.rec (none d ≤-refl pd)

  fromTrunc : ∥ Σ[ d ∈ ℕ ] P d ∥₁ → Least
  fromTrunc = PropTrunc.rec isPropLeast (λ w → fromWitness (fst w) (snd w))

------------------------------------------------------------------------
-- §2  Powers in a group (not assumed commutative) and their two laws.
------------------------------------------------------------------------

module Powers (G : Group ℓ) where
  open GroupStr (snd G)
  open GroupTheory G

  private
    X : Type ℓ
    X = ⟨ G ⟩

  _^_ : X → ℕ → X
  a ^ zero  = 1g
  a ^ suc n = a · (a ^ n)

  ^+ : (a : X) (m n : ℕ) → a ^ (m + n) ≡ (a ^ m) · (a ^ n)
  ^+ a zero    n = sym (·IdL (a ^ n))
  ^+ a (suc m) n = cong (a ·_) (^+ a m n) ∙ ·Assoc a (a ^ m) (a ^ n)

  ^· : (a : X) (m n : ℕ) → a ^ (m ·ℕ n) ≡ (a ^ m) ^ n
  ^· a m zero    = cong (a ^_) (sym (0≡m·0 m))
  ^· a m (suc n) = cong (a ^_) (·-suc m n)
                 ∙ ^+ a m (m ·ℕ n)
                 ∙ cong ((a ^ m) ·_) (^· a m n)

  1g^ : (n : ℕ) → 1g ^ n ≡ 1g
  1g^ zero    = refl
  1g^ (suc n) = ·IdL (1g ^ n) ∙ 1g^ n

  -- an element absorbed on the left of something is the identity
  absorbed : (x y : X) → (x · y) ≡ y → x ≡ 1g
  absorbed x y p = ·CancelR y (p ∙ sym (·IdL y))

------------------------------------------------------------------------
-- §3–§6  The order of an element of a finite group, its cyclic
--        subgroup, the count of that subgroup, and Euler's theorem.
------------------------------------------------------------------------

module Order (G : Group ℓ) (finG : isFinSet ⟨ G ⟩) (a : ⟨ G ⟩) where
  open GroupStr (snd G)
  open GroupTheory G
  open Powers G

  private
    X : Type ℓ
    X = ⟨ G ⟩

    setX : isSet X
    setX = isFinSet→isSet finG

    discreteX : Discrete X
    discreteX = isFinSet→Discrete finG

  FG : FinSet ℓ
  FG = X , finG

  -- coinciding powers give an annihilating positive exponent
  powDiff : (i t : ℕ) → a ^ (t + suc i) ≡ a ^ i → a ^ suc t ≡ 1g
  powDiff i t p =
    absorbed (a ^ suc t) (a ^ i)
      (sym (^+ a (suc t) i) ∙ cong (a ^_) (sym (+-suc t i)) ∙ p)

  IsOrd : ℕ → Type ℓ
  IsOrd d = (0 < d) × (a ^ d ≡ 1g)

  isPropIsOrd : (d : ℕ) → isProp (IsOrd d)
  isPropIsOrd d = isProp× isProp≤ (setX _ _)

  private
    dec× : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} → Dec A → Dec B → Dec (A × B)
    dec× (yes p) (yes q) = yes (p , q)
    dec× (yes p) (no ¬q) = no (λ w → ¬q (snd w))
    dec× (no ¬p) (yes q) = no (λ w → ¬p (fst w))
    dec× (no ¬p) (no ¬q) = no (λ w → ¬p (fst w))

  decIsOrd : (d : ℕ) → Dec (IsOrd d)
  decIsOrd d = dec× (<Dec 0 d) (discreteX (a ^ d) 1g)

  collide : (i j : ℕ) → ¬ i ≡ j → a ^ i ≡ a ^ j → Σ[ d ∈ ℕ ] IsOrd d
  collide i j i≢j p = go (i ≟ j)
    where
    go : Trichotomy i j → Σ[ d ∈ ℕ ] IsOrd d
    go (lt (t , q)) = suc t , suc-≤-suc zero-≤ , powDiff i t (cong (a ^_) q ∙ sym p)
    go (eq r)       = Empty.rec (i≢j r)
    go (gt (t , q)) = suc t , suc-≤-suc zero-≤ , powDiff j t (cong (a ^_) q ∙ p)

  -- §3  THE PIGEONHOLE: a⁰, …, a^|G| are |G|+1 elements of a set of
  --     size |G|, so two coincide, so a has a finite order.
  hasOrder : ∥ Σ[ d ∈ ℕ ] IsOrd d ∥₁
  hasOrder = PropTrunc.rec isPropPropTrunc
    (λ eqv → fromEquiv (compEquiv eqv (SumFin≃Fin (card FG)))) (finG .snd)
    where
    fromEquiv : X ≃ Fin (card FG) → ∥ Σ[ d ∈ ℕ ] IsOrd d ∥₁
    fromEquiv eqv =
      ∣ collide (fst i) (fst j) (λ r → i≢j (toℕ-injective r)) (fromF fi≡fj) ∣₁
      where
      f : Fin (suc (card FG)) → Fin (card FG)
      f k = equivFun eqv (a ^ fst k)

      ph : Σ[ i ∈ Fin (suc (card FG)) ] Σ[ j ∈ Fin (suc (card FG)) ] (¬ i ≡ j) × (f i ≡ f j)
      ph = pigeonhole ≤-refl f

      i j : Fin (suc (card FG))
      i = fst ph
      j = fst (snd ph)

      i≢j : ¬ i ≡ j
      i≢j = fst (snd (snd ph))

      fi≡fj : f i ≡ f j
      fi≡fj = snd (snd (snd ph))

      fromF : f i ≡ f j → a ^ fst i ≡ a ^ fst j
      fromF q = sym (retEq eqv _) ∙ cong (invEq eqv) q ∙ retEq eqv _

  module L = Least IsOrd isPropIsOrd decIsOrd

  -- THE ORDER of a: the least positive e with a ^ e ≡ 1g.
  ord : L.Least
  ord = L.fromTrunc hasOrder

  e : ℕ
  e = fst ord

  0<e : 0 < e
  0<e = fst (fst (snd ord))

  a^e≡1 : a ^ e ≡ 1g
  a^e≡1 = snd (fst (snd ord))

  minimal : (k : ℕ) → k < e → ¬ IsOrd k
  minimal = snd (snd ord)

  -- every power of a is a power with exponent below e
  reduce : (k : ℕ) → Σ[ k' ∈ ℕ ] (k' < e) × (a ^ k' ≡ a ^ k)
  reduce zero    = 0 , 0<e , refl
  reduce (suc k) = step (reduce k)
    where
    split : (k' : ℕ) → a ^ k' ≡ a ^ k → (suc k' < e) ⊎ (suc k' ≡ e)
          → Σ[ k'' ∈ ℕ ] (k'' < e) × (a ^ k'' ≡ a ^ suc k)
    split k' p (inl sk'<e) = suc k' , sk'<e , cong (a ·_) p
    split k' p (inr sk'≡e) =
      0 , 0<e , sym a^e≡1 ∙ cong (a ^_) (sym sk'≡e) ∙ cong (a ·_) p

    step : Σ[ k' ∈ ℕ ] (k' < e) × (a ^ k' ≡ a ^ k)
         → Σ[ k'' ∈ ℕ ] (k'' < e) × (a ^ k'' ≡ a ^ suc k)
    step (k' , k'<e , p) = split k' p (≤-split k'<e)

  -- the powers with exponent below e are pairwise distinct
  injBelow : (i j : ℕ) → i < e → j < e → a ^ i ≡ a ^ j → i ≡ j
  injBelow i j i<e j<e p = go (i ≟ j)
    where
    -- from t + suc i ≡ j < e: suc t < e
    bound : (i j t : ℕ) → t + suc i ≡ j → j < e → suc t < e
    bound i j t q j<e =
      ≤<-trans (subst (suc t ≤_) (sym (+-suc t i) ∙ q) (suc-≤-suc ≤SumLeft)) j<e

    go : Trichotomy i j → i ≡ j
    go (eq r)       = r
    go (lt (t , q)) =
      Empty.rec (minimal (suc t) (bound i j t q j<e)
        (suc-≤-suc zero-≤ , powDiff i t (cong (a ^_) q ∙ sym p)))
    go (gt (t , q)) =
      Empty.rec (minimal (suc t) (bound j i t q i<e)
        (suc-≤-suc zero-≤ , powDiff j t (cong (a ^_) q ∙ p)))

  ------------------------------------------------------------------
  -- §4  The cyclic subgroup generated by a, with decidable membership.
  ------------------------------------------------------------------

  Mem : X → Type ℓ
  Mem x = ∥ Σ[ k ∈ ℕ ] a ^ k ≡ x ∥₁

  cycℙ : ℙ X
  cycℙ x = Mem x , isPropPropTrunc

  private
    -- e ≡ suc t, so that inverses can be written as powers
    t : ℕ
    t = fst 0<e

    st≡e : suc t ≡ e
    st≡e = sym (+-comm t 1) ∙ snd 0<e

  invPow : (k : ℕ) → inv (a ^ k) ≡ a ^ (k ·ℕ t)
  invPow k = sym (invUniqueR lem)
    where
    lem : (a ^ k) · (a ^ (k ·ℕ t)) ≡ 1g
    lem = sym (^+ a k (k ·ℕ t))
        ∙ cong (a ^_) (sym (·-suc k t) ∙ cong (k ·ℕ_) st≡e ∙ ·-comm k e)
        ∙ ^· a e k
        ∙ cong (_^ k) a^e≡1
        ∙ 1g^ k

  isSubgroupCyc : isSubgroup G cycℙ
  isSubgroupCyc = record
    { id-closed  = ∣ 0 , refl ∣₁
    ; op-closed  = PropTrunc.rec2 isPropPropTrunc
        (λ u v → ∣ fst u + fst v , ^+ a (fst u) (fst v) ∙ cong₂ _·_ (snd u) (snd v) ∣₁)
    ; inv-closed = PropTrunc.rec isPropPropTrunc
        (λ u → ∣ fst u ·ℕ t , sym (invPow (fst u)) ∙ cong inv (snd u) ∣₁)
    }

  cycSub : Subgroup G
  cycSub = cycℙ , isSubgroupCyc

  -- membership is decided by searching the exponents below e
  decMem : (x : X) → Dec (Mem x)
  decMem x = go (Lx.decBelow e)
    where
    module Lx = Least (λ k → a ^ k ≡ x) (λ k → setX _ _) (λ k → discreteX (a ^ k) x)

    go : Dec (Σ[ k ∈ ℕ ] (k < e) × (a ^ k ≡ x)) → Dec (Mem x)
    go (yes (k , _ , p)) = yes ∣ k , p ∣₁
    go (no ¬w) = no (PropTrunc.rec isProp⊥
      (λ u → ¬w (fst (reduce (fst u)) , fst (snd (reduce (fst u)))
                , snd (snd (reduce (fst u))) ∙ snd u)))

  -- SubgroupIndex, instantiated at the cyclic subgroup.
  module I = Index G finG cycSub decMem

  ------------------------------------------------------------------
  -- §5  The cyclic subgroup has exactly e elements.
  ------------------------------------------------------------------

  Rep : X → Type ℓ
  Rep x = Σ[ i ∈ Fin e ] a ^ fst i ≡ x

  isPropRep : (x : X) → isProp (Rep x)
  isPropRep x (i , p) (j , q) =
    Σ≡Prop (λ _ → setX _ _)
      (toℕ-injective (injBelow (fst i) (fst j) (snd i) (snd j) (p ∙ sym q)))

  rep : (x : X) → Mem x → Rep x
  rep x = PropTrunc.rec (isPropRep x)
    (λ u → (fst (reduce (fst u)) , fst (snd (reduce (fst u))))
         , snd (snd (reduce (fst u))) ∙ snd u)

  cycIso : Iso (Σ[ x ∈ X ] Mem x) (Fin e)
  Iso.fun cycIso (x , m) = fst (rep x m)
  Iso.inv cycIso i = a ^ fst i , ∣ fst i , refl ∣₁
  Iso.rightInv cycIso i =
    cong fst (isPropRep (a ^ fst i) (rep (a ^ fst i) ∣ fst i , refl ∣₁) (i , refl))
  Iso.leftInv cycIso (x , m) = Σ≡Prop (λ _ → isPropPropTrunc) (snd (rep x m))

  cardCyc : I.order ≡ e
  cardCyc = cardEquiv I.FH (SumFin e , isFinSetFin)
              ∣ compEquiv (isoToEquiv cycIso) (invEquiv (SumFin≃Fin e)) ∣₁

  ------------------------------------------------------------------
  -- §6  EULER'S THEOREM for a finite group, from Lagrange.
  ------------------------------------------------------------------

  orderDivides : e ∣ card FG
  orderDivides = subst (_∣ card FG) cardCyc I.order∣card

  card≡index·e : card FG ≡ e ·ℕ I.index
  card≡index·e = I.lagrange ∙ cong (I.index ·ℕ_) cardCyc ∙ ·-comm I.index e

  euler : a ^ card FG ≡ 1g
  euler = cong (a ^_) card≡index·e
        ∙ ^· a e I.index
        ∙ cong (_^ I.index) a^e≡1
        ∙ 1g^ I.index

------------------------------------------------------------------------
-- The theorem, stated once at top level with every hypothesis visible.
------------------------------------------------------------------------

यूलर-सिद्धिः-सामान्या
  : (G : Group ℓ) (finG : isFinSet ⟨ G ⟩) (a : ⟨ G ⟩)
  → Powers._^_ G a (card (⟨ G ⟩ , finG)) ≡ GroupStr.1g (snd G)
यूलर-सिद्धिः-सामान्या G finG a = Order.euler G finG a

------------------------------------------------------------------------
-- §7  On a finite ABELIAN group: the same theorem in Bijamula/Avarta's
--     `घात` vocabulary, and RSA correctness with no Euler hypothesis
--     and no cyclic hypothesis.
------------------------------------------------------------------------

module Abelian (G : Group ℓ) (finG : isFinSet ⟨ G ⟩)
               (comm : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y ≡ GroupStr._·_ (snd G) y x) where
  open GroupStr (snd G)
  open Powers G

  private
    X : Type ℓ
    X = ⟨ G ⟩

  CM : CMonoid X
  CM = record
    { ε      = 1g
    ; _⋆_    = _·_
    ; assoc⋆ = λ x y z → sym (·Assoc x y z)
    ; idL    = ·IdL
    ; idR    = ·IdR
    ; comm⋆  = comm
    }

  घात≡^ : (x : X) (n : ℕ) → घात CM x n ≡ x ^ n
  घात≡^ x zero    = refl
  घात≡^ x (suc n) = cong (x ·_) (घात≡^ x n)

  -- Euler, as the sibling modules write it
  यूलर-घातः : (x : X) → घात CM x (card (X , finG)) ≡ 1g
  यूलर-घातः x = घात≡^ x (card (X , finG)) ∙ Order.euler G finG x

  -- RSA correctness: only the pulverizer's witness remains as a hypothesis.
  बीजमूल-सिद्धिः-सामान्या
    : (x : X) (e d k : ℕ) → e ·ℕ d ≡ card (X , finG) ·ℕ k + 1
    → घात CM (घात CM x e) d ≡ x
  बीजमूल-सिद्धिः-सामान्या x e d k witness =
    बीजमूल-सिद्धि CM x e d (card (X , finG)) k witness (यूलर-घातः x)

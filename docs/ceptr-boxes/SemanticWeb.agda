{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module SemanticWeb where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv ; invIso)
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; equivFun ; idEquiv)
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.Bool using (Bool ; true ; false ; notEquiv ; true≢false)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.SetQuotients using (_/_ ; [_])
open import Cubical.HITs.SetQuotients.Properties using (isEquivRel→effectiveIso)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open BinaryRelation using (isPropValued ; isEquivRel ; equivRel)

private variable ℓA ℓB ℓC ℓQ ℓR ℓS : Level

-- 0 · THE TWO KINDS OF SCAPE.  An indexed scape is a property f; the
--     pairs it relates, "item + item = relationship", are its cells
--     squared, so no pair is stored.  A relation is the same-cell
--     relation of a scape exactly when it is an equivalence relation:
--     the kernel of any map is one, and a propositional one is the
--     kernel of its quotient.  Anything else must be asserted.

sameCellPairs : {A : Type ℓA} {B : Type ℓB} (f : A → B)
  → (Σ[ a ∈ A ] Σ[ a' ∈ A ] (f a ≡ f a')) ≃ (Σ[ b ∈ B ] fiber f b × fiber f b)
sameCellPairs {A = A} {B = B} f = isoToEquiv (iso to from to-from from-to)
  where
  to : Σ[ a ∈ A ] Σ[ a' ∈ A ] (f a ≡ f a') → Σ[ b ∈ B ] fiber f b × fiber f b
  to (a , a' , p) = f a' , (a , p) , (a' , refl)
  from : Σ[ b ∈ B ] fiber f b × fiber f b → Σ[ a ∈ A ] Σ[ a' ∈ A ] (f a ≡ f a')
  from (b , (a , p) , (a' , q)) = a , a' , p ∙ sym q
  to-from : (w : Σ[ b ∈ B ] fiber f b × fiber f b) → to (from w) ≡ w
  to-from (b , (a , p) , (a' , q)) =
    J (λ b' q' → (p' : f a ≡ b')
              → Path (Σ[ b ∈ B ] fiber f b × fiber f b)
                     (f a' , (a , p' ∙ sym q') , (a' , refl)) (b' , (a , p') , (a' , q')))
      (λ p' i → f a' , (a , rUnit p' (~ i)) , (a' , refl)) q p
  from-to : (w : Σ[ a ∈ A ] Σ[ a' ∈ A ] (f a ≡ f a')) → from (to w) ≡ w
  from-to (a , a' , p) i = a , a' , rUnit p (~ i)

sameCellIsAnEquivalence : {A : Type ℓA} {B : Type ℓB} (f : A → B)
  → isEquivRel (λ a a' → f a ≡ f a')
sameCellIsAnEquivalence f =
  equivRel (λ _ → refl) (λ _ _ → sym) (λ _ _ _ p q → p ∙ q)

quotientCarriesIt : {A : Type ℓA} (R : A → A → Type ℓR)
  → isPropValued R → isEquivRel R
  → (a a' : A) → R a a' ≃ ([ a ] ≡ [ a' ])
quotientCarriesIt R Rprop Req a a' =
  isoToEquiv (invIso (isEquivRel→effectiveIso Rprop Req a a'))

-- an asserted external relationship: "that we are friends ... doesn't
-- properly belong in either one of them."  Friendship that is symmetric
-- and not transitive is the same-cell relation of no scape at all.

data Profile : Type where
  ann bo cy : Profile

Friend : Profile → Profile → Type
Friend ann bo = Unit
Friend bo ann = Unit
Friend bo cy  = Unit
Friend cy bo  = Unit
Friend _  _   = ⊥

friendshipIsNoScape :
  ¬ (Σ[ B ∈ Type ] Σ[ f ∈ (Profile → B) ]
       ((a a' : Profile) → (Friend a a' → f a ≡ f a') × (f a ≡ f a' → Friend a a')))
friendshipIsNoScape (B , f , h) =
  snd (h ann cy) (fst (h ann bo) tt ∙ fst (h bo cy) tt)


-- 1 · An expectation R says which actions are valid on each datum.  A
--     scape q is sufficient for it when every cell has one action valid
--     on the whole cell.  Sufficiency is responding from the scape alone.

module _ {A : Type ℓA} {B : Type ℓB} {Q : Type ℓQ} (R : A → B → Type ℓR) where

  Sufficient : (A → Q) → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓQ ℓR)))
  Sufficient q = (c : Q) → Σ[ b ∈ B ] ((a : A) → q a ≡ c → R a b)

  RespondsFrom : (A → Q) → Type (ℓ-max ℓA (ℓ-max ℓB (ℓ-max ℓQ ℓR)))
  RespondsFrom q = Σ[ s ∈ (Q → B) ] ((a : A) → R a (s (q a)))

  sufficientIsRespondingFromTheScape : (q : A → Q) → Sufficient q ≃ RespondsFrom q
  sufficientIsRespondingFromTheScape q = isoToEquiv (iso to from to-from from-to)
    where
    to : Sufficient q → RespondsFrom q
    to σ = (λ c → fst (σ c)) , λ a → snd (σ (q a)) a refl
    from : RespondsFrom q → Sufficient q
    from (s , h) c = s c , λ a p → subst (λ c' → R a (s c')) p (h a)
    to-from : (w : RespondsFrom q) → to (from w) ≡ w
    to-from (s , h) i = s , λ a → transportRefl (h a) i
    from-to : (σ : Sufficient q) → from (to σ) ≡ σ
    from-to σ i c = fst (σ c) , λ a p →
      J (λ c' p' → subst (λ c'' → R a (fst (σ c''))) p' (snd (σ (q a)) a refl)
                 ≡ snd (σ c') a p')
        (transportRefl (snd (σ (q a)) a refl)) p i

-- crossing a sufficient scape with any other keeps it sufficient.
crossingKeepsSufficiency : {A : Type ℓA} {B : Type ℓB} {Q Q' : Type ℓQ}
  (R : A → B → Type ℓR) (q : A → Q) (r : A → Q')
  → Sufficient R q → Sufficient R (λ a → q a , r a)
crossingKeepsSufficiency R q r σ (c , _) =
  fst (σ c) , λ a p → snd (σ c) a (cong fst p)

-- 2 · A deterministic expectation: the action is f's output.  Its own
--     scape is sufficient, and no sufficient scape merges two data that
--     f separates.  The differences that make a difference are f's.

module _ {A : Type ℓA} {B : Type ℓB} (f : A → B) where

  Graph : A → B → Type ℓB
  Graph a b = f a ≡ b

  ownScapeIsSufficient : Sufficient Graph f
  ownScapeIsSufficient c = c , λ a p → p

  mergesOnlyIrrelevant : {Q : Type ℓQ} (q : A → Q) → Sufficient Graph q
    → {a a' : A} → q a ≡ q a' → f a ≡ f a'
  mergesOnlyIrrelevant q σ {a} {a'} p =
    snd (σ (q a')) a p ∙ sym (snd (σ (q a')) a' refl)

  relevantDifferencesAreKept : {Q : Type ℓQ} (q : A → Q) → Sufficient Graph q
    → {a a' : A} → ¬ f a ≡ f a' → ¬ q a ≡ q a'
  relevantDifferencesAreKept q σ ne p = ne (mergesOnlyIrrelevant q σ p)

-- 3 · A free expectation: R(1) = {x}, R(2) = {x, y}, R(3) = {y}.  Two
--     scapes are each sufficient, and their join, which merges all
--     three, is not: no coarsest sufficient scape exists.

data Pt : Type where
  a1 a2 a3 : Pt

data Act : Type where
  x y : Act

R3 : Pt → Act → Type
R3 a1 x = Unit
R3 a1 y = ⊥
R3 a2 _ = Unit
R3 a3 x = ⊥
R3 a3 y = Unit

data Cell : Type where
  c0 c1 : Cell

isC0 : Cell → Type
isC0 c0 = Unit
isC0 c1 = ⊥

c0≢c1 : {X : Type} → c0 ≡ c1 → X
c0≢c1 p = ⊥rec (subst isC0 p tt)

c1≢c0 : {X : Type} → c1 ≡ c0 → X
c1≢c0 p = c0≢c1 (sym p)

π σ : Pt → Cell                     -- π = {{1,2},{3}},  σ = {{1},{2,3}}
π a1 = c0 ; π a2 = c0 ; π a3 = c1
σ a1 = c0 ; σ a2 = c1 ; σ a3 = c1

πSufficient : Sufficient R3 π
πSufficient c0 = x , λ { a1 _ → tt ; a2 _ → tt ; a3 p → c1≢c0 p }
πSufficient c1 = y , λ { a1 p → c0≢c1 p ; a2 _ → tt ; a3 _ → tt }

σSufficient : Sufficient R3 σ
σSufficient c0 = x , λ { a1 _ → tt ; a2 p → c1≢c0 p ; a3 p → c1≢c0 p }
σSufficient c1 = y , λ { a1 p → c0≢c1 p ; a2 _ → tt ; a3 _ → tt }

joinFails : ¬ Sufficient R3 (λ (_ : Pt) → tt)
joinFails τ = noCommon (fst (τ tt)) (snd (τ tt))
  where
  noCommon : (b : Act) → ((a : Pt) → tt ≡ tt → R3 a b) → ⊥
  noCommon x h = h a3 refl
  noCommon y h = h a1 refl

-- 4 · Protocols in sequence.  A scape sufficient for R is sufficient for
--     R followed by any total S; and the converse fails by one bit.

module _ {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (R : A → B → Type ℓR) (S : B → C → Type ℓS) where

  _then_ : A → C → Type (ℓ-max ℓB (ℓ-max ℓR ℓS))
  _then_ a c = Σ[ b ∈ B ] (R a b × S b c)

  sequenceKeepsSufficiency : {Q : Type ℓQ} → ((b : B) → Σ[ c ∈ C ] S b c)
    → (q : A → Q) → Sufficient R q → Sufficient _then_ q
  sequenceKeepsSufficiency tot q τ c₀ =
    fst (tot (fst (τ c₀))) , λ a p → fst (τ c₀) , snd (τ c₀) a p , snd (tot (fst (τ c₀)))

data Two : Type where
  p1 p2 : Two

Rm : Two → Two → Type               -- the intermediate must name its input
Rm p1 p1 = Unit
Rm p1 p2 = ⊥
Rm p2 p1 = ⊥
Rm p2 p2 = Unit

Sm : Two → Unit → Type              -- the end task does not care
Sm _ _ = Unit

materializationGap :
    Sufficient (_then_ Rm Sm) (λ (_ : Two) → tt) × (¬ Sufficient Rm (λ (_ : Two) → tt))
materializationGap =
    (λ _ → tt , λ { p1 _ → p1 , tt , tt ; p2 _ → p2 , tt , tt })
  , λ τ → noCommon (fst (τ tt)) (snd (τ tt))
  where
  noCommon : (b : Two) → ((a : Two) → tt ≡ tt → Rm a b) → ⊥
  noCommon p1 h = h p2 refl
  noCommon p2 h = h p1 refl

-- 5 · owl:sameAs.  A bare assertion that two carriers are identifiable
--     is a proposition, and no transport can be read off it: Bool has
--     two self-identifications and the assertion cannot tell them apart.

sameAsTransportsNothing :
  ¬ (Σ[ g ∈ (∥ Bool ≃ Bool ∥₁ → Bool → Bool) ]
       ((e : Bool ≃ Bool) → g ∣ e ∣₁ ≡ equivFun e))
sameAsTransportsNothing (g , h) = true≢false (λ i → path i true)
  where
  path : (λ (b : Bool) → b) ≡ equivFun notEquiv
  path = sym (h (idEquiv Bool)) ∙ cong g (squash₁ _ _) ∙ h notEquiv

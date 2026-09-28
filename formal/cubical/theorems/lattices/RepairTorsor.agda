{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- RepairTorsor
--
-- proposition schema and Proposition 9.  Companion prose: that note.
--
-- The note's mathematics is done; nothing is redone here.  What is
-- formalised is exactly the part that is category theory and therefore
-- machine-checkable: the schema
--
--     "repairs of a defect form a torsor under the automorphisms of the
--      repaired object over the defective one, so the repair is
--      canonical iff that group is trivial"
--
-- stated for an abstract category S of repairs (objects: pairs
-- (Y , ι : X → Y) solving the defect; morphisms: maps under X — the
-- slice is NOT constructed here, because the schema never uses it: it
-- holds verbatim in any category, and the note states it that way).
--
-- HEADLINE STATEMENTS (all checked, no postulates, no holes, --safe):
--
--  1. AutGroup            Aut_S(y) = CatIso S y y is a group.
--     actR                It acts on the repairs Iso S x y on the right,
--     isTorsor            and the action is FREE and TRANSITIVE:
--                         for f g : CatIso S x y the type
--                         Σ[a ∈ Aut y] (f ⋆ a ≡ g) is CONTRACTIBLE.
--                         The centre is the explicit transporter
--                         `transporter f g = f⁻¹ ⋆ g`.
--     actFree             Freeness, separately: f ⋆ a ≡ f ⋆ b → a ≡ b.
--
--  2. trivializeAut       A CHOSEN repair f₀ trivialises the torsor:
--                         Aut y ≃ CatIso S x y, a ↦ f₀ ⋆ a.  This is
--                         FOUR_REPAIR_MODES.md (absent from this repository) Thm 3 ("the set of
--                         completions is empty or a V^Γ-torsor; a lift
--                         must be chosen") as the special case where the
--                         group is Aut of the repaired object — the
--                         specialisation the task asked for, obtained by
--                         instantiating S, not by a second proof.
--
--  3. rigid→isoUnique     RIGIDITY: if Aut_S(y) is trivial then any two
--     rigid→isContrIso    isomorphisms x ≅ y are EQUAL, so x is
--     nonRigid→twoIsos    "unique up to UNIQUE isomorphism"; and
--                         conversely a nonidentity automorphism produces
--                         two distinct isomorphisms.  This is the
--                         rigid/non-rigid separation the note uses to
--                         distinguish tower steps 1–3 from step 4.
--
--  4. initial→AutTrivial  PROPOSITION 9 itself: an initial object of S
--     initial→isContrIso  has trivial automorphism group and is unique
--     nonRigid→notInitial up to unique isomorphism; contrapositively an
--                         object with Aut ≠ 1 is not initial.
--
--  5. Z2Repair            A finite instance, computed: the one-object
--     twoRepairs          groupoid on Bool (id = false, composition =
--     twoRepairs-differ   xor).  Its object has exactly two repairs,
--     Z2-not-rigid        they are distinct, the unique automorphism
--                         carrying one to the other is `true`, and this
--                         is checked BY COMPUTATION (`refl`).
--
-- Inputs quoted from the note, NOT formalised here and deliberately so:
-- Aut(ℤ) = Aut(ℚ) = Aut(ℝ) = 1 and Aut(ℂ/ℝ) ≅ ℤ/2 (note Thm 6) need
-- real and complex analysis and are out of reach of this lane.  They are
-- the note's cited inputs; the general lemma they feed — item 3 — is
-- what is proved here.  Item 5 is the abstract shape of Thm 6(iv): two
-- square roots of −1 interchanged by a group of order two, with no
-- claim that it IS ℂ/ℝ.
--
-- Delta against PathIsSymmetry, which already proves a
-- rigidity result (ℕ-algebra-Aut-trivial, swap01-≢-id): that module
-- shows ONE object is rigid and one is not, in the category of types.
-- This module proves what rigidity BUYS — uniqueness of the comparison
-- isomorphism — for an arbitrary category, and is disjoint from it; it
-- is the general lemma of which that pair is an instance.
------------------------------------------------------------------------

module RepairTorsor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Group.Base using (Group ; makeGroup)

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Initial

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 1.  The torsor.
------------------------------------------------------------------------

module _ (S : Category ℓ ℓ') where

  open Category S

  -- Automorphisms of a repair.
  Aut : ob → Type ℓ'
  Aut y = CatIso S y y

  -- Repairs compared: the isomorphisms in S from x to y.  In the
  -- intended reading x and y are two repairs of one defect and an
  -- element of CatIso S x y is a comparison of them under the defective
  -- object.
  Repairs : ob → ob → Type ℓ'
  Repairs x y = CatIso S x y

  isSetAut : (y : ob) → isSet (Aut y)
  isSetAut y = isSet-CatIso y y

  AutGroup : ob → Group ℓ'
  AutGroup y =
    makeGroup {G = Aut y}
      idCatIso
      ⋆Iso
      invIso
      (isSetAut y)
      (λ a b c → CatIso≡ _ _ (sym (⋆Assoc _ _ _)))
      ⋆IsoIdR
      ⋆IsoIdL
      (λ a → CatIso≡ _ _ (a .snd .isIso.ret))
      (λ a → CatIso≡ _ _ (a .snd .isIso.sec))

  -- The right action of Aut y on the repairs.
  actR : {x y : ob} → Repairs x y → Aut y → Repairs x y
  actR f a = ⋆Iso f a

  actR-id : {x y : ob} (f : Repairs x y) → actR f idCatIso ≡ f
  actR-id f = ⋆IsoIdR f

  actR-⋆ : {x y : ob} (f : Repairs x y) (a b : Aut y)
         → actR (actR f a) b ≡ actR f (⋆Iso a b)
  actR-⋆ f a b = CatIso≡ _ _ (⋆Assoc _ _ _)

  -- The explicit transporter carrying f to g.
  transporter : {x y : ob} → Repairs x y → Repairs x y → Aut y
  transporter f g = ⋆Iso (invIso f) g

  -- Transitivity, with the witness computed rather than merely asserted.
  actR-transporter : {x y : ob} (f g : Repairs x y)
                   → actR f (transporter f g) ≡ g
  actR-transporter f g = CatIso≡ _ _
    ( sym (⋆Assoc _ _ _)
    ∙ cong (_⋆ g .fst) (f .snd .isIso.ret)
    ∙ ⋆IdL (g .fst) )

  -- Uniqueness of the witness: any a moving f to g is the transporter.
  transporter-unique : {x y : ob} (f g : Repairs x y) (a : Aut y)
                     → actR f a ≡ g → a ≡ transporter f g
  transporter-unique f g a p = CatIso≡ _ _
    ( sym (⋆IdL (a .fst))
    ∙ cong (_⋆ a .fst) (sym (f .snd .isIso.sec))
    ∙ ⋆Assoc _ _ _
    ∙ cong (f .snd .isIso.inv ⋆_) (cong fst p) )

  -- THE TORSOR STATEMENT: the action is free and transitive, i.e. the
  -- type of group elements carrying f to g is contractible.
  isTorsor : {x y : ob} (f g : Repairs x y)
           → isContr (Σ[ a ∈ Aut y ] actR f a ≡ g)
  isTorsor f g =
    ( transporter f g , actR-transporter f g )
    , λ (a , p) → Σ≡Prop
        (λ a → isSet-CatIso _ _ (actR f a) g)
        (sym (transporter-unique f g a p))

  -- Freeness on its own.
  actFree : {x y : ob} (f : Repairs x y) (a b : Aut y)
          → actR f a ≡ actR f b → a ≡ b
  actFree f a b p =
    transporter-unique f (actR f b) a p
    ∙ sym (transporter-unique f (actR f b) b refl)

------------------------------------------------------------------------
-- 2.  A chosen repair trivialises the torsor.
--
--     This is FOUR_REPAIR_MODES.md (absent from this repository) Thm 3's "chosen lift" as a special
--     case: with a lift f₀ chosen, the repairs are IN BIJECTION with the
--     group; without one there is a torsor and no distinguished point.
------------------------------------------------------------------------

  trivializeIso : {x y : ob} (f₀ : Repairs x y) → Iso (Aut y) (Repairs x y)
  Iso.fun (trivializeIso f₀)      = actR f₀
  Iso.inv (trivializeIso f₀)      = transporter f₀
  Iso.rightInv (trivializeIso f₀) = actR-transporter f₀
  Iso.leftInv (trivializeIso f₀) a =
    sym (transporter-unique f₀ (actR f₀ a) a refl)

  trivializeAut : {x y : ob} → Repairs x y → (Aut y) ≃ (Repairs x y)
  trivializeAut f₀ = isoToEquiv (trivializeIso f₀)

------------------------------------------------------------------------
-- 3.  Rigidity: trivial Aut ⇒ unique isomorphism, and the converse.
------------------------------------------------------------------------

  AutTrivial : ob → Type ℓ'
  AutTrivial y = (a : Aut y) → a ≡ idCatIso

  -- Any two isomorphisms into a rigid object are equal: "unique up to
  -- UNIQUE isomorphism".
  rigid→isoUnique : {x y : ob} → AutTrivial y
                  → (f g : Repairs x y) → f ≡ g
  rigid→isoUnique {x} {y} triv f g =
      sym (actR-id f)
    ∙ cong (actR f) (sym (triv (transporter f g)))
    ∙ actR-transporter f g

  rigid→isContrIso : {x y : ob} → AutTrivial y
                   → Repairs x y → isContr (Repairs x y)
  rigid→isContrIso triv f = f , rigid→isoUnique triv f

  -- Conversely, a nonidentity automorphism gives two distinct
  -- comparisons — the repair is then not canonical.
  nonRigid→twoIsos : {x y : ob} (f : Repairs x y) (a : Aut y)
                   → ¬ (a ≡ idCatIso) → ¬ (actR f a ≡ f)
  nonRigid→twoIsos f a a≢id p =
    a≢id (transporter-unique f f a p ∙ sym (transporter-unique f f idCatIso (actR-id f)))

------------------------------------------------------------------------
-- 4.  Proposition 9 of the note.
------------------------------------------------------------------------

  -- An initial object has only the identity endomorphism, hence trivial
  -- automorphism group.
  initial→AutTrivial : {y : ob} → isInitial S y → AutTrivial y
  initial→AutTrivial {y} ini a =
    CatIso≡ _ _ (isContr→isProp (ini y) (a .fst) id)

  -- Hence an initial object is unique up to UNIQUE isomorphism.
  initial→isContrIso : {x y : ob} → isInitial S x → isInitial S y
                     → isContr (Repairs x y)
  initial→isContrIso {x} {y} inix iniy =
    rigid→isContrIso (initial→AutTrivial iniy) theIso
    where
    theIso : Repairs x y
    theIso = catiso (inix y .fst) (iniy x .fst)
      (isContr→isProp (iniy y) _ id)
      (isContr→isProp (inix x) _ id)

  -- Contrapositive: an object with a nonidentity automorphism is not
  -- initial.  (Note Prop 9, second sentence.)
  nonRigid→notInitial : {y : ob} (a : Aut y) → ¬ (a ≡ idCatIso)
                      → ¬ (isInitial S y)
  nonRigid→notInitial a a≢id ini = a≢id (initial→AutTrivial ini a)

------------------------------------------------------------------------
-- 5.  A finite instance, checked by computation.
--
--     The one-object groupoid on Bool: identity `false`, composition
--     `xor`.  Every morphism is invertible and is its own inverse, so
--     Aut of the unique object is ℤ/2.  This is the abstract shape of
--     the note's Thm 6(iv) — two square roots of −1, interchanged by a
--     group of order two — WITHOUT any claim to be ℂ/ℝ.
------------------------------------------------------------------------

xorAssoc : (a b c : Bool) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
xorAssoc false b c = refl
xorAssoc true false c = refl
xorAssoc true true false = refl
xorAssoc true true true = refl

xorIdR : (a : Bool) → a ⊕ false ≡ a
xorIdR false = refl
xorIdR true  = refl

xorSelf : (a : Bool) → a ⊕ a ≡ false
xorSelf false = refl
xorSelf true  = refl

-- The category: one object, hom-set Bool.
Z2Repair : Category ℓ-zero ℓ-zero
Category.ob Z2Repair = Unit
Category.Hom[_,_] Z2Repair _ _ = Bool
Category.id Z2Repair = false
Category._⋆_ Z2Repair = _⊕_
Category.⋆IdL Z2Repair f = refl
Category.⋆IdR Z2Repair = xorIdR
Category.⋆Assoc Z2Repair = xorAssoc
Category.isSetHom Z2Repair = isSetBool

-- Every morphism is an isomorphism, since it is its own inverse.
boolIso : Bool → CatIso Z2Repair tt tt
boolIso b = catiso b b (xorSelf b) (xorSelf b)

-- The two repairs, i.e. the two comparison isomorphisms.
twoRepairs : (Bool → Repairs Z2Repair tt tt)
twoRepairs = boolIso

twoRepairs-differ : ¬ (boolIso false ≡ boolIso true)
twoRepairs-differ p = false≢true (cong fst p)

-- The unique automorphism carrying one repair to the other is `true`,
-- and this is checked BY COMPUTATION: the transporter reduces to it.
transporter-computes :
  transporter Z2Repair (boolIso false) (boolIso true) .fst ≡ true
transporter-computes = refl

-- ... and it does carry it there.
transporter-carries :
  actR Z2Repair (boolIso false) (transporter Z2Repair (boolIso false) (boolIso true))
    ≡ boolIso true
transporter-carries = actR-transporter Z2Repair (boolIso false) (boolIso true)

-- The object is NOT rigid: `true` is a nonidentity automorphism.
Z2-not-rigid : ¬ (AutTrivial Z2Repair tt)
Z2-not-rigid triv = true≢false (cong fst (triv (boolIso true)))

-- Hence, by Proposition 9, it is not initial — the finite mirror of the
-- note's step 4.
Z2-not-initial : ¬ (isInitial Z2Repair tt)
Z2-not-initial =
  nonRigid→notInitial Z2Repair (boolIso true)
    (λ p → true≢false (cong fst p))

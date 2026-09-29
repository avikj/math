{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- भित्ति-स्थानिवत् — Pāṇini's carrier is not two-valued, and the wall
-- crosses its own ford.
--
-- Three asset classes compose:
--
--   १  a FLOOR on आधार = वर्ण × वर्णरूप: every map to Bool collides two of
--      three named pairs (one वर्ण, the three forms ई ए अ) — pigeonhole,
--      pair exhibited per route;
--   २  the WALL ¬ (आधार ≃ Bool), one line from the floor;
--   ३  the wall CROSSES THE FORD आधार ≃ स्थानिवत् (the module's own Carrier
--      law) by भित्ति-प्रतिसंक्रमः: ¬ (स्थानिवत् ≃ Bool).
--
-- So the retirement uses no new mathematics at the target: the ford that
-- built स्थानिवत् is the ford its wall arrives over.  A bank's own
-- construction receipt is what its impossibilities travel on.
--
-- PROVENANCE.  This retires ./jiva's fourth join candidate,
-- 2616 ≈ [436 @ Bool] × [6 @ स्थानिवत्], floor-first.
-- भित्ति-स्थानिवत् is built here; the distinctness of ए/अ is
-- proved here in the source module's own coding style (its ई≢ए pattern).
------------------------------------------------------------------------

module Fibre.BhittiPositional_PaninisCarrierIsNotTwoValuedAndTheWallCrossesItsOwnFord where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq ; retEq)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true ; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

open import Fibre.Sthanivadbhava_TheAdesasFormIsTheFreeSlotAndItsDesignationsAreCarried
  using ( वर्ण ; वर्णरूप ; ई ; ए ; अ ; आधार ; स्थानिवत् ; आधार≃स्थानिवत् ; ई-अङ्ग )
-- the transport law, restated locally (one line): this library cannot
-- import formal/cubical, so the law lives in both, cheaply.
open import Cubical.Foundations.Equiv using (compEquiv)

------------------------------------------------------------------------
-- १ · the three forms are pairwise distinct (source module's own style).
------------------------------------------------------------------------

ए-कोड : वर्णरूप → Type
ए-कोड ई = ⊥
ए-कोड ए = Unit
ए-कोड अ = ⊥

ई≢ए : ¬ (_≡_ {A = वर्णरूप} ई ए)
ई≢ए p = subst ए-कोड (sym p) tt

ई≢अ : ¬ (_≡_ {A = वर्णरूप} ई अ)
ई≢अ p = subst ई-कोड p tt
  where
    ई-कोड : वर्णरूप → Type
    ई-कोड ई = Unit
    ई-कोड ए = ⊥
    ई-कोड अ = ⊥

ए≢अ : ¬ (_≡_ {A = वर्णरूप} ए अ)
ए≢अ p = subst ए-कोड p tt

------------------------------------------------------------------------
-- २ · the floor on आधार: three named pairs, every two-valued route
-- collides two of them.  Pigeonhole on Bool, exhibited.
------------------------------------------------------------------------

क ख ग : आधार
क = ई-अङ्ग , ई
ख = ई-अङ्ग , ए
ग = ई-अङ्ग , अ

क≢ख : ¬ (क ≡ ख)
क≢ख p = ई≢ए (cong snd p)

क≢ग : ¬ (क ≡ ग)
क≢ग p = ई≢अ (cong snd p)

ख≢ग : ¬ (ख ≡ ग)
ख≢ग p = ए≢अ (cong snd p)

तल-आधार : (f : आधार → Bool)
        → Σ[ x ∈ आधार ] Σ[ y ∈ आधार ] ((¬ (x ≡ y)) × (f x ≡ f y))
तल-आधार f = judge (f क) (f ख) (f ग) refl refl refl
  where
    judge : (a b c : Bool) → f क ≡ a → f ख ≡ b → f ग ≡ c
          → Σ[ x ∈ आधार ] Σ[ y ∈ आधार ] ((¬ (x ≡ y)) × (f x ≡ f y))
    judge true  true  _     pa pb _  = क , ख , क≢ख , pa ∙ sym pb
    judge false false _     pa pb _  = क , ख , क≢ख , pa ∙ sym pb
    judge true  false true  pa _  pc = क , ग , क≢ग , pa ∙ sym pc
    judge false true  false pa _  pc = क , ग , क≢ग , pa ∙ sym pc
    judge true  false false _  pb pc = ख , ग , ख≢ग , pb ∙ sym pc
    judge false true  true  _  pb pc = ख , ग , ख≢ग , pb ∙ sym pc

------------------------------------------------------------------------
-- ३ · the wall on आधार, one line from the floor; and the crossing.
------------------------------------------------------------------------

अभेद : {A B : Type} (e : A ≃ B) {x y : A} → equivFun e x ≡ equivFun e y → x ≡ y
अभेद e {x} {y} p = sym (retEq e x) ∙ cong (invEq e) p ∙ retEq e y

भित्ति-आधार : (आधार ≃ Bool) → ⊥
भित्ति-आधार e =
  let (x , y , x≢y , coll) = तल-आधार (equivFun e)
  in x≢y (अभेद e coll)

भित्ति-प्रतिसंक्रमः : {A B C : Type} → (A ≃ B) → ((A ≃ C) → ⊥) → (B ≃ C) → ⊥
भित्ति-प्रतिसंक्रमः ford wall e = wall (compEquiv ford e)

-- the wall crosses the module's own construction ford: स्थानिवत् inherits it.
भित्ति-स्थानिवत् : (स्थानिवत् ≃ Bool) → ⊥
भित्ति-स्थानिवत् = भित्ति-प्रतिसंक्रमः आधार≃स्थानिवत् भित्ति-आधार

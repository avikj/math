{-# OPTIONS --cubical --safe --guardedness #-}

-- Punarāgamana · Viśvarūpa
--
-- EVERY FAMILY IS A PULLBACK OF ONE FIBRATION, AND A TOWER OF THEM FLATTENS
-- TO ONE.
--
-- THE CLAIM THIS FILE ANSWERS.  The fibre law is not a recurring motif in
-- this corpus.  It is the object classifier: in a univalent universe a form
-- over a base — any family `B : A → Type` — IS a map into the universe, and
-- `Σ A B` is the total space of the one fibration
--
--     π : Σ[ X ∈ Type ℓ ] X  →  Type ℓ        π = fst
--
-- pulled back along it.  One object classifies every family there is.  The
-- claim was made in prose.  Everything below is the part of it that is a
-- term.
--
-- WHAT IS ALREADY OWNED, AND IS THEREFORE CITED RATHER THAN RE-PROVED.
-- `Cubical.Functions.Fibration` has HoTT Lemma 4.8.1 (`fiberEquiv`), Lemma
-- 4.8.2 (`totalEquiv`) and Theorem 4.8.3 (`fibrationEquiv`), the last of
-- which is the classifier as an equivalence of TYPES:
--
--     (Σ[ E ∈ Type ℓ ] (E → A))  ≃  (A → Type ℓ).
--
-- §3 re-exports it under a corpus name and states where its content sits:
-- its `rightInv` is `ua`.  The classifier is a theorem OF univalence, not a
-- fact about .
--
-- WHAT IS NEW HERE.
--
--   §2  The equivalence is the CANONICAL comparison map — checked by
--       `refl`, not merely exhibited as some equivalence.  Which matters,
--       because of §6.
--
--   §5  `invisible≃contractible`, at the locus where the law lives.
--       `Fibre.Carrier`'s header asserts the converse in prose — "A
--       NON-contractible fibre cannot be declared equivalent to its base" —
--       and the corpus proves it twice, in neither place generally:
--       `DefectCalculus.noEquiv→badFibre` has the fibrewise
--       characterisation of `isEquiv` for an arbitrary map (in cubical Agda
--       that IS the definition, so it is one step), and `TritiyaMarga`'s
--       private `Test` module has both directions for ONE family
--       `Q : ℕ → Type₀`, as a lemma on the way to Markov's principle.  What
--       is new is neither step but the locus: the statement about the
--       projection of an ARBITRARY family, in the library that owns the
--       law, packaged as an equivalence of propositions.  एकाधिकरण — an
--       installed theorem has exactly one place to be quoted from.
--
--       The two directions are joined by a PATH between propositions rather
--       than by an implication assumed, which is why the converse cost
--       nothing here.  README §II, `invisibleExactlyWhenInvariant`, records
--       that lesson about the same shape: a path has an inverse, an
--       implication does not.
--
--   §6  …and the converse is about the PROJECTION, not about the mere
--       existence of an equivalence.  `Σ Bool Br ≃ Bool` holds for a family
--       whose fibres are one EMPTY and one CROWDED: the census's two
--       failures (नास्ति and नष्टि — `WholePartialDesa`) cancel
--       numerically, and an abstract equivalence sees neither.  "Invisible"
--       has to mean invisible OVER THE BASE, and §5's statement does.
--
--   §7  The tower flattens.  A tower of families of any finite height n
--       over A — each storey a family over the previous total space — is
--       ONE family over A, and the flattening is computed (`flatten`), not
--       merely shown to exist.  So iterating the fibre law never leaves the
--       universe, at every finite stage, and §7's last lines exhibit a
--       two-storey tower whose flattening holds by `refl`.
--
-- The tower of §7 is level-uniform (every storey at
-- one level ℓ).
--
-- ON SIZE.  `fiber π X` lives one universe above X, so §2's pullback is an
-- equivalence ACROSS levels.  That is the size of the classifier — the
-- universe classifying its own families is exactly what does not fit inside
-- one level — and not a defect of the statement.
--
-- ON THE NAME.  विश्वरूप (viśvarūpa), "all-formed", "the form that has all
-- forms".  The word names the theophany of the Bhagavadgt's eleventh
-- adhyya.
-- It is used here as the label of this module, chosen for what
-- the theorem says.

module Fibre.Universal_EveryFamilyIsAPullbackOfTheUniverseAndTheTowerFlattensToOne where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Fibration
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit* ; tt* ; isContrUnit*)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Fibre.Carrier

private
  variable
    ℓ ℓa ℓb : Level

------------------------------------------------------------------------
-- §1  THE ONE FIBRATION
--
-- The universe of ℓ-small types, with a point of each chosen — and the
-- projection that forgets the point.  Its fibre over a code IS the type
-- that code names.  There is nothing else in it: no structure, no choice,
-- no parameter.

Universal : (ℓ : Level) → Type (ℓ-suc ℓ)
Universal ℓ = Σ[ X ∈ Type ℓ ] X

π : Universal ℓ → Type ℓ
π = fst

-- HoTT 4.8.1 at the universal family, where p⁻¹ is the identity.  The fibre
-- over the code X is X.
fibreOfπ : (X : Type ℓ) → fiber (π {ℓ}) X ≃ X
fibreOfπ {ℓ = ℓ} X = fiberEquiv (λ (Y : Type ℓ) → Y) X

------------------------------------------------------------------------
-- §2  EVERY FAMILY IS ITS PULLBACK
--
-- Given B : A → Type ℓ, the square
--
--     Σ A B ──────→ Universal ℓ
--       │  (a,b) ↦ (B a , b)  │
--      fst                    π
--       —                     —
--                            
--       A ─────────→ Type ℓ
--                B
--
-- commutes on the nose, and Σ A B is the pullback.  The map that witnesses
-- it is the canonical one — `comparison` below — and `pullback-canonical`
-- says so by `refl`.

module _ {A : Type ℓa} (B : A → Type ℓ) where

  -- The top edge of the square: a point of the total space is a point of
  -- the type its base point names, so it is a point of the universal
  -- family.
  classifying : Σ A B → Universal ℓ
  classifying (a , b) = B a , b

  -- The square commutes, and by refl: the code of the fibre a point lands
  -- in is the code the base point names.
  square : (p : Σ A B) → π (classifying p) ≡ B (fst p)
  square _ = refl

  comparison : Σ A B → Σ[ a ∈ A ] fiber (π {ℓ}) (B a)
  comparison (a , b) = a , (classifying (a , b) , refl)

  -- Fibrewise from §1, with the base component untouched.  Written out
  -- rather than obtained from `Σ-cong-equiv-snd` because that lemma's
  -- generalised variables put the two families at ONE level, and here the
  -- second family is a universe higher than the first (see ON SIZE).
  pullback-Iso : Iso (Σ A B) (Σ[ a ∈ A ] fiber (π {ℓ}) (B a))
  Iso.fun pullback-Iso (a , b) = a , invEq (fibreOfπ (B a)) b
  Iso.inv pullback-Iso (a , u) = a , equivFun (fibreOfπ (B a)) u
  Iso.rightInv pullback-Iso (a , u) i = a , retEq (fibreOfπ (B a)) u i
  Iso.leftInv  pullback-Iso (a , b) i = a , secEq (fibreOfπ (B a)) b i

  pullback : Σ A B ≃ (Σ[ a ∈ A ] fiber (π {ℓ}) (B a))
  pullback = isoToEquiv pullback-Iso

  -- The equivalence IS the comparison map.  Without this line §2 would say
  -- only that the two types are equivalent somehow, which §6 shows is a
  -- strictly weaker statement than being a pullback.
  pullback-canonical : (p : Σ A B) → equivFun pullback p ≡ comparison p
  pullback-canonical _ = refl

------------------------------------------------------------------------
-- §3  THE CLASSIFIER, CITED
--
-- HoTT Theorem 4.8.3, `Cubical.Functions.Fibration.fibrationEquiv`: maps
-- into A and families over A are the same type, not merely in bijection on
-- points.  Read the library's proof for where the content is — `rightInv`
-- is `ua`, `leftInv` is `ua` again with `ua-unglue`.  Univalence is the
-- whole of it.

classifier : (A : Type ℓ) → (Σ[ E ∈ Type ℓ ] (E → A)) ≃ (A → Type ℓ)
classifier {ℓ = ℓ} A = fibrationEquiv A ℓ

------------------------------------------------------------------------
-- §4  THE FIBRE LAW IS THIS, WITH A CONTRACTIBLE CLASSIFYING MAP
--
-- `Fibre.Carrier` takes f : A → B and forms the family `fibre f = singl ∘ f`.
-- That family is the classifying map of `Carrier f`, so the carrier is a
-- pullback of π like anything else — and the law's hypothesis
-- (`fibre-isContr`) is the statement that this classifying map lands in the
-- contractible codes.  Nothing about the law is special except where its
-- classifying map goes.

module _ {A B : Type ℓ} (f : A → B) where

  Carrier-classified : Carrier f ≃ (Σ[ a ∈ A ] fiber (π {ℓ}) (fibre f a))
  Carrier-classified =
    compEquiv (isoToEquiv (Carrier-as-Σ f)) (pullback (fibre f))

------------------------------------------------------------------------
-- §5  INVISIBLE IFF CONTRACTIBLE
--
-- A family is invisible over its base — its projection is an equivalence,
-- so the total space carries no information the base did not — EXACTLY when
-- every fibre is contractible.  Both sides are propositions and the two
-- implications are joined into a path.
--
-- The forward direction is `Σ-contractSnd`, which fifteen files of this
-- corpus already use.  The backward direction is the one `Fibre.Carrier`'s
-- header asserts in prose and none of those fifteen has: it is HoTT 4.8.1
-- (`fiberEquiv`) plus the definition of `isEquiv`, and it costs one line,
-- because the fibre of `fst` over a is B a on the nose.  See the header for
-- the two places the corpus proves it already, and why neither is a locus
-- the law can be quoted from.

module _ {A : Type ℓa} (B : A → Type ℓb) where

  projection : Σ A B → A
  projection = fst

  invisible : Type (ℓ-max ℓa ℓb)
  invisible = isEquiv projection

  contractibleFibres : Type (ℓ-max ℓa ℓb)
  contractibleFibres = (a : A) → isContr (B a)

  -- `Σ-contractSnd` is this direction and is what the corpus quotes, but
  -- its generalised variables tie A and B to one level; the fibre of `fst`
  -- over a is B a on the nose, so the direct construction is as short and
  -- keeps the two levels apart.
  contractible→invisible : contractibleFibres → invisible
  contractible→invisible c .equiv-proof a =
    isOfHLevelRespectEquiv 0 (invEquiv (fiberEquiv B a)) (c a)

  invisible→contractible : invisible → contractibleFibres
  invisible→contractible e a =
    isOfHLevelRespectEquiv 0 (fiberEquiv B a) (e .equiv-proof a)

  invisible≃contractible : invisible ≃ contractibleFibres
  invisible≃contractible =
    propBiimpl→Equiv (isPropIsEquiv projection)
                     (isPropΠ (λ _ → isPropIsContr))
                     invisible→contractible
                     contractible→invisible

------------------------------------------------------------------------
-- §6  AND IT IS ABOUT THE PROJECTION
--
-- §5 cannot be weakened to "Σ A B ≃ A".  Take the base Bool and the family
-- that is empty over one point and two-valued over the other.  The total
-- space is equivalent to the base — and neither fibre is contractible: one
-- is नास्ति (no source at all), the other नष्टि (crowded).  The census of
-- `WholePartialDesa` separates those two failures; an abstract equivalence
-- adds them up and reports nothing.
--
-- So "the fibre law holds here" is never established by producing SOME
-- equivalence between total space and base.  It is established over the
-- base, by the projection, which is what §5 quantifies.

module CensusCancels where

  Br : Bool → Type
  Br true  = Bool
  Br false = ⊥

  Σ-Br-Iso : Iso (Σ Bool Br) Bool
  Iso.fun Σ-Br-Iso (true , b) = b
  Iso.fun Σ-Br-Iso (false , ())
  Iso.inv Σ-Br-Iso b = true , b
  Iso.rightInv Σ-Br-Iso _ = refl
  Iso.leftInv Σ-Br-Iso (true , _) = refl
  Iso.leftInv Σ-Br-Iso (false , ())

  -- The total space is equivalent to the base…
  total≃base : Σ Bool Br ≃ Bool
  total≃base = isoToEquiv Σ-Br-Iso

  -- …and the fibres are not contractible: over `false` there is no point at
  -- all, which is enough.
  fibres-not-contractible : ¬ contractibleFibres Br
  fibres-not-contractible c = c false .fst

  -- Hence the projection is not an equivalence, by §5 read backwards.
  projection-not-invisible : ¬ invisible Br
  projection-not-invisible e =
    fibres-not-contractible (invisible→contractible Br e)

------------------------------------------------------------------------
-- §7  THE TOWER FLATTENS
--
-- A tower of height n over A: a family over A, then a family over ITS total
-- space, then a family over that, n times.  `Tot` is the space at the top.
-- `flatten` computes a single family over A, by iterated Σ, and
-- `flatten-correct` proves the top of the tower is its total space.
--
-- Read as the classifier (`tower-is-pullback`): a stack of n fibrations is
-- one pullback of π.  Iterating the fibre law does not leave the universe
-- at any finite height, and the witness is not an existence proof — the
-- flattened family is written down, and reduces.

Fam : (A : Type ℓ) → ℕ → Type (ℓ-suc ℓ)
Fam A zero            = Unit*
Fam {ℓ = ℓ} A (suc n) = Σ[ B ∈ (A → Type ℓ) ] Fam (Σ A B) n

Tot : {A : Type ℓ} (n : ℕ) → Fam A n → Type ℓ
Tot {A = A} zero _  = A
Tot (suc n) (B , F) = Tot n F

flatten : {A : Type ℓ} (n : ℕ) → Fam A n → A → Type ℓ
flatten zero _ _        = Unit*
flatten (suc n) (B , F) a = Σ[ b ∈ B a ] flatten n F (a , b)

flatten-correct : {A : Type ℓ} (n : ℕ) (F : Fam A n)
                → Tot n F ≃ Σ A (flatten n F)
flatten-correct zero _ = invEquiv (Σ-contractSnd (λ _ → isContrUnit*))
flatten-correct (suc n) (B , F) =
  compEquiv (flatten-correct n F)
            (Σ-assoc-≃ {C = λ a b → flatten n F (a , b)})

tower-is-pullback : {A : Type ℓ} (n : ℕ) (F : Fam A n)
                  → Tot n F ≃ (Σ[ a ∈ A ] fiber (π {ℓ}) (flatten n F a))
tower-is-pullback n F = compEquiv (flatten-correct n F) (pullback (flatten n F))

-- …and it computes.  A two-storey tower over Bool: the naturals, then the
-- proofs that the natural is zero.  Its flattening is not merely equivalent
-- to the hand-written family — it IS it, by refl, in both the family and
-- the space.

private

  twoStorey : Fam Bool 2
  twoStorey = (λ _ → ℕ) , ((λ p → snd p ≡ zero) , tt*)

  flatten-computes : (b : Bool)
                   → flatten 2 twoStorey b ≡ (Σ[ n ∈ ℕ ] Σ[ _ ∈ (n ≡ zero) ] Unit*)
  flatten-computes _ = refl

  tot-computes : Tot 2 twoStorey ≡ (Σ[ p ∈ (Σ Bool (λ _ → ℕ)) ] (snd p ≡ zero))
  tot-computes = refl

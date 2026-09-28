{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- गणना-सप्तभङ्गी — the map-level census IS the sevenfold, and the corpus
-- already holds witnesses of three distinct positions.
--
-- `WholePartialDesa` made the census a term — but
-- PER POINT: three constructors (अवक्तव्यम् / सकलादेश / विकलादेश) at each b.
-- A MAP's character is which of the three kinds occur anywhere across its
-- codomain — a selection from three seeds — and the non-empty selections
-- number 2³ − 1 = 7, which is `Saptabhangi`'s own कुतः-सप्त: the sevenfold
-- is exactly the selection algebra of the three seeds.  So the pointwise
-- census was the seed layer, and the map-level classification is the
-- sevenfold itself — not an analogy: the same 2³−1, with the same three
-- seeds, in the correspondence
--
--     सकलादेश somewhere   ↔  अस्ति       (something carried whole)
--     विकलादेश somewhere   ↔  नास्ति      (something lost, exhibited)
--     अवक्तव्यम् somewhere  ↔  अवक्तव्य    (something the source cannot utter)
--
-- following the note's own readings (empty fibre = avaktavya, धनात्मकम्;
-- crowded = the loss).
--
-- THE THREE WITNESSES, all already in the corpus, classified:
--
--   id : Bool → Bool     every fibre contractible          → pure अस्ति
--   एकम् : Bool → Unit    every fibre crowded               → pure नास्ति
--   asNat : Bool → ℕ     contractible at 0,1; empty above;
--                        NEVER crowded (injectivity ⟹ the
--                        fibres are propositions)          → अस्ति-अवक्तव्य
--
-- Three maps, three DIFFERENT bhagas, each coordinate a term.
--
-- GRADE.  The classification records below are this module's;
-- the sevenfold count and the seed reading are Saptabhangi's and
-- SakalaVikalaDesa's respectively; Malliea (Sydvdamajar, 1292, at
--  grade via the note) for sakaldea/vikaldea.  Their selection
-- algebra is this classification's type, on the nose.
------------------------------------------------------------------------

module GananaSaptabhangi_TheMapLevelCensusIsTheSevenfoldItselfAndTheCorpusAlreadyHoldsThreePositions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots ; snotz ; injSuc ; isSetℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit ; isPropUnit)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

open import FiniteOccupancyChannelNoGo using (asNat)
open import GananaAsNat_TheIndicatorsFullCensusPricesTheBusiestUnpricedEdge
  using (शून्य-सकल ; ऊर्ध्व-रिक्त ; अभेद-asNat)

private
  शेष : {A B : Type} (f : A → B) → B → Type
  शेष {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)

------------------------------------------------------------------------
-- १ · the three seed predicates OF A MAP — the selection coordinates.
-- Witness-carrying (the b that witnesses is the standpoint's locus).
------------------------------------------------------------------------

अस्ति-क्वचित् : {A B : Type} (f : A → B) → Type
अस्ति-क्वचित् {B = B} f = Σ[ b ∈ B ] isContr (शेष f b)

नास्ति-क्वचित् : {A B : Type} (f : A → B) → Type
नास्ति-क्वचित् {B = B} f =
  Σ[ b ∈ B ] Σ[ x ∈ शेष f b ] Σ[ y ∈ शेष f b ] (¬ (x ≡ y))

अवक्तव्य-क्वचित् : {A B : Type} (f : A → B) → Type
अवक्तव्य-क्वचित् {B = B} f = Σ[ b ∈ B ] (¬ शेष f b)

-- and the universal negations, for the pure positions
सर्वत्र-सकलम् : {A B : Type} (f : A → B) → Type
सर्वत्र-सकलम् {B = B} f = (b : B) → isContr (शेष f b)

सर्वत्र-बहु : {A B : Type} (f : A → B) → Type
सर्वत्र-बहु {B = B} f =
  (b : B) → Σ[ x ∈ शेष f b ] Σ[ y ∈ शेष f b ] (¬ (x ≡ y))

न-क्वचित्-बहु : {A B : Type} (f : A → B) → Type
न-क्वचित्-बहु {B = B} f = (b : B) → (x y : शेष f b) → x ≡ y

------------------------------------------------------------------------
-- २ · WITNESS ONE — pure अस्ति: the identity.  Every fibre contractible;
-- this is `isEquiv id`, read as the first bhaga.
------------------------------------------------------------------------

एकत्व-अस्ति : सर्वत्र-सकलम् (λ (b : Bool) → b)
fst (एकत्व-अस्ति b) = b , refl
snd (एकत्व-अस्ति b) (a , p) i = p (~ i) , λ j → p (~ i ∨ j)

------------------------------------------------------------------------
-- ३ · WITNESS TWO — pure नास्ति: एकम् : Bool → Unit.  Every fibre crowded,
-- the two points named, their distinctness a term.
------------------------------------------------------------------------

एकम् : Bool → Unit
एकम् _ = tt

एकम्-नास्ति : सर्वत्र-बहु एकम्
एकम्-नास्ति b =
  (false , refl) , (true , refl) ,
  λ p → false≢true (cong fst p)
  where
    false≢true : ¬ (false ≡ true)
    false≢true q = subst कोड q tt
      where
        कोड : Bool → Type
        कोड false = Unit
        कोड true  = ⊥

------------------------------------------------------------------------
-- ४ · WITNESS THREE — अस्ति-अवक्तव्य, the FIFTH bhaṅga: asNat.
-- Contractible somewhere (अस्ति), empty somewhere (अवक्तव्य), and NEVER
-- crowded — injectivity into a set makes every fibre a proposition, so
-- the नास्ति coordinate is refuted, not merely unexhibited.
------------------------------------------------------------------------

asNat-अस्ति : अस्ति-क्वचित् asNat
asNat-अस्ति = 0 , शून्य-सकल

asNat-अवक्तव्य : अवक्तव्य-क्वचित् asNat
asNat-अवक्तव्य = 2 , ऊर्ध्व-रिक्त 0

asNat-न-नास्ति : न-क्वचित्-बहु asNat
asNat-न-नास्ति n (a , p) (a' , p') =
  ΣPathP ( अभेद-asNat a a' (p ∙ sym p')
         , isProp→PathP (λ i → isSetℕ _ _) p p' )

-- the fifth position, assembled: both coordinates present, third refuted.
asNat-अस्ति-अवक्तव्यम् :
  अस्ति-क्वचित् asNat × अवक्तव्य-क्वचित् asNat × न-क्वचित्-बहु asNat
asNat-अस्ति-अवक्तव्यम् = asNat-अस्ति , asNat-अवक्तव्य , asNat-न-नास्ति

------------------------------------------------------------------------
-- ५ · the three witnesses occupy three DISTINCT selections — stated as
-- terms, so the classification genuinely separates them:
-- the identity has no empty fibre; एकम् has no contractible fibre.
------------------------------------------------------------------------

एकत्व-न-अवक्तव्य : ¬ अवक्तव्य-क्वचित् (λ (b : Bool) → b)
एकत्व-न-अवक्तव्य (b , ne) = ne (b , refl)

एकम्-न-सकल : ¬ अस्ति-क्वचित् एकम्
एकम्-न-सकल (tt , c) =
  snd (snd (एकम्-नास्ति tt))
    (isContr→isProp c (fst (एकम्-नास्ति tt)) (fst (snd (एकम्-नास्ति tt))))

------------------------------------------------------------------------
--   .  The selection "none of the three" is the empty
-- selection.  For FINITE maps with DECIDABLE equality every fibre is empty,
-- contractible or crowded, so for inhabited B the empty selection is
-- excluded and the count is 2³ − 1, as in Saptabhangi's कुतः-सप्त.  Outside
-- that setting the exclusion is NOT a theorem: for sets it holds only up to
-- double negation, and for higher types it fails — `S¹ → Unit` has an
-- inhabited, non-contractible fibre with no two provably distinct points,
-- so it realises the empty selection over an inhabited codomain.  No term
-- below claims the exclusion; this is its scope.
------------------------------------------------------------------------

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EffectiveDescent
--
-- DESCENT ALONG A SURJECTION OF SETS, WITH THE SPLIT HYPOTHESIS REMOVED
-- AND THE SURJECTIVITY HYPOTHESIS SHOWN TO BE NECESSARY.
--
-- WHAT THIS PROVES
--
-- `DefectCalculus` §7 proves T15.40 in the direction that matters only
-- for a SPLIT surjection.  Here it is proved for an arbitrary surjection
-- of sets:
--
--   * a set hypothesis on `C` is genuinely USED — `rec→Set` demands it;
--   * **`SetQuotients` is not needed at all.**  No quotient is
--     constructed anywhere in this file.  The universal property of the
--     propositional truncation into a set — Kraus–Escardó–Coquand–
--     Altenkirch's factorisation of a 2-Constant map, `PT.rec→Set` —
--     supplies `g` directly.  `FiniteInformation`
--     (`fiberConstant→factorsThrough`) does exactly this
--     truncation-into-a-set argument, choice-free, for factorisation
--     through `Image q`; for a surjection `Image q` is `B`.
--
-- WHAT IS PROVED
--
--   §1  `isPropCoequalizes`      the descent datum is a proposition when
--                                the target is a set — so it can be
--                                carried by `Σ≡Prop` and never has to be
--                                compared.
--
--   §2  `descend` / `descend-β`  T15.40 substantive direction for an
--       `descends`               arbitrary surjection.  `descend-β` is
--                                one truncation-propositionality step
--                                away from `refl`.
--
--   §3  `descend-unique`         the factorisation is unique, and
--       `isPropFactorisation`    therefore the type of factorisations is
--                                a proposition.  Uniqueness is where
--                                surjectivity does its work; existence
--                                would survive weaker hypotheses.
--
--   §4  `restrictAlong`          THE STATEMENT THIS FILE EXISTS FOR.
--       `descentEquiv`           `(B → C) ≃ Σ[ f ∈ (A → C) ] Coequalizes q f`
--                                for `q` surjective and `C` a set: the
--                                descent problem is REPRESENTABLE, and
--                                `B` represents it.  Descent data along
--                                a one-map cover of sets are nothing but
--                                coequalising maps; there is no further
--                                cocycle to satisfy and no obstruction
--                                to vanish.
--
--   §5  `split→descends`         DefectCalculus's `descends-split` as a
--       `split-descent-agrees`   corollary (a split map is surjective),
--                                plus the sharper statement: the
--                                section-chosen factorisation `f ∘ s`
--                                EQUALS the choice-free one.  So a proof
--                                that picks a representative computes
--                                the right answer — it just assumes more
--                                than it needs.
--
--   §6  `hProp-descent→surjection`  the CONVERSE.  If the descent map is
--       `descentEquiv→surjection`   injective at the single set `hProp`
--                                — in particular if §4's `restrictAlong`
--                                is an equivalence there — then `q` is
--                                surjective.  With §4 this makes
--                                surjectivity EQUIVALENT to effective
--                                descent, so §2's hypothesis is not a
--                                convenience: it is the content.
--
--   §7  `notSurjection-absurd`   controls, both directions.  NEGATIVE:
--       `two-factorisations`     without surjectivity the factorisation
--       `descend-computes`       is genuinely non-unique (two different
--                                `g`, both checked, and a checked proof
--                                that they differ), so §3 is not
--                                vacuously true.  POSITIVE: on a concrete
--                                surjection `descend` REDUCES —
--                                `descend-computes` is `refl` — so §2 is
--                                not an inert term either.
--
--   §8  `MinimalMachine.R`       the corollary that made this worth
--       `MinimalMachine.R-unique`
--                                landing: `collab/messages/madhavi/
--                                future_quotient_linear_rank.md` (absent from this repository)
--                                Theorem (2) — "there is a unique matrix
--                                `R : Q × W → K` with `T = C R`" — is
--                                §2 + §3 at `C := W → K`.  Its published
--                                proof reads "Define `R(c,w) = T(x,w)`
--                                for any `x` with `q(x) = c`", i.e. it
--                                picks a representative.  Here no
--                                representative is picked.
--
--  * **No novelty.**  "Surjections of sets are effective epimorphisms"
--    is standard; the converse is Mac Lane–Moerdijk p. 143 corollary 5,
--    which the pinned library already has as
--    `Cubical.Functions.Surjection.epi⇒surjective`.  §6 is a
--    repackaging of it at the subobject classifier.  The exact
--    difference: the library's `rightCancellable` quantifies over EVERY type
--    of `Type (ℓ-suc (ℓ ⊔ ℓ'))`, and §6 needs the SINGLE object
--    `hProp (ℓ ⊔ ℓ')` of that same universe.  `hProp` is not one level
--    lower — the subobject classifier never is — so the sharpening is
--    "one test object, and it is a set", not "a smaller universe".  It
--    is what makes §6 the literal converse of §4, whose hypothesis is
--    exactly "`C` is a set".  A hypothesis sharpening, not a theorem.
--
--  * **The two hypotheses are incomparable.**  `descends-split` needs no
--    set hypothesis but needs a section; `descends` needs no section but
--    needs `isSet C`.  What §5 proves is only that once `C` is a set the
--    split statement is subsumed, and that the two produce the same
--    function.  `AsetChidra_↦` exhibits a non-set `C` at which §4 fails,
--    so the set hypothesis is necessary.
--
--    §2 locates the Peres–Mermin obstruction as "a property of the
--    *cover*, i.e. genuinely cohomological — of the nerve, not of the
--    operator set", each observable lying in exactly two contexts.  §4
--    is the exact statement of why that is the only place such an
--    obstruction can live: along a single surjection onto a set there is
--    nothing to obstruct.  That is a boundary remark about scope, and
--    NOT a claim about the Peres–Mermin computation, which is not
--    touched here.
--
--  * **Nothing here is about primes, or about defects.**  §2 is one
--    library lemma applied once.  The value is entirely in which
--    hypothesis was removed and which was shown necessary.
------------------------------------------------------------------------

module EffectiveDescent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; 2-Constant)
open import Cubical.Foundations.HLevels
  using (isPropΠ ; isPropΠ3 ; isSetΠ ; hProp ; isSetHProp ; isPropIsOfHLevel)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; fiber ; isEquiv ; invEq ; retEq)
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt* ; isPropUnit*)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; isSetBool)
open import Cubical.Data.Empty as Empty using (⊥ ; isProp⊥)
open import Cubical.Functions.Surjection using (isSurjection ; section→isSurjection)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc ; rec→Set)

-- The descent datum is DefectCalculus's, not a copy: this file proves a
-- theorem about that module's `Coequalizes` (D15.39), so the two cannot
-- drift apart.
open import DefectCalculus
  using (Coequalizes ; descend-coeq ; descends-split)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- 1.  THE DESCENT DATUM IS A PROPOSITION
--
-- `Coequalizes q f = (x y : A) → q x ≡ q y → f x ≡ f y`.  When `C` is a
-- set this is a proposition, so it never has to be compared and can be
-- carried through `Σ≡Prop`.  Everything downstream leans on this.
------------------------------------------------------------------------

isPropCoequalizes :
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → isSet C → (q : A → B) (f : A → C) → isProp (Coequalizes q f)
isPropCoequalizes setC q f = isPropΠ3 (λ _ _ _ → setC _ _)

------------------------------------------------------------------------
-- 2.  DESCENT ALONG AN ARBITRARY SURJECTION  (T15.40, general case)
--
-- The whole construction.  `coeq` says the map `fiber q b → C` picking
-- out `f` of the witness is 2-Constant; `rec→Set` turns a 2-Constant map
-- into a set into a map out of the truncation.  No quotient is built.
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (setC : isSet C) (q : A → B) (f : A → C) where

  module _ (surj : isSurjection q) (coeq : Coequalizes q f) where

    private
      constOnFibre : (b : B) → 2-Constant {A = fiber q b} (λ u → f (fst u))
      constOnFibre b u v = coeq (fst u) (fst v) (snd u ∙ sym (snd v))

    descend : B → C
    descend b = rec→Set setC (λ u → f (fst u)) (constOnFibre b) (surj b)

    -- The computation rule.  Definitional on `∣_∣₁`; the one step that
    -- is not definitional is replacing the anonymous surjectivity
    -- witness by the canonical one, which costs exactly the
    -- propositionality of `∥_∥₁`.
    descend-β : (a : A) → descend (q a) ≡ f a
    descend-β a =
      cong (rec→Set setC (λ u → f (fst u)) (constOnFibre (q a)))
           (isPropPropTrunc (surj (q a)) ∣ a , refl ∣₁)

    descends : Σ[ g ∈ (B → C) ] ((a : A) → g (q a) ≡ f a)
    descends = descend , descend-β

------------------------------------------------------------------------
-- 3.  UNIQUENESS
--
-- Surjectivity is what makes the factorisation unique; existence alone
-- would survive weaker hypotheses (a non-surjective `q` still admits
-- factorisations — §7 exhibits two).
------------------------------------------------------------------------

  module _ (surj : isSurjection q) where

    descend-unique :
      (g h : B → C)
      → ((a : A) → g (q a) ≡ f a) → ((a : A) → h (q a) ≡ f a)
      → g ≡ h
    descend-unique g h gβ hβ = funExt λ b →
      PT.rec (setC (g b) (h b))
             (λ u → cong g (sym (snd u)) ∙∙ (gβ (fst u) ∙ sym (hβ (fst u)))
                                         ∙∙ cong h (snd u))
             (surj b)

    -- `((a : A) → g (q a) ≡ f a)` is a Π into a path type in a set,
    -- hence a proposition; so the whole factorisation type is one.
    isPropFactorisation :
      isProp (Σ[ g ∈ (B → C) ] ((a : A) → g (q a) ≡ f a))
    isPropFactorisation (g , gβ) (h , hβ) =
      Σ≡Prop (λ _ → isPropΠ (λ _ → setC _ _)) (descend-unique g h gβ hβ)

------------------------------------------------------------------------
-- 4.  REPRESENTABILITY: `B` REPRESENTS THE DESCENT PROBLEM
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (setC : isSet C) (q : A → B) where

  DescentData : Type _
  DescentData = Σ[ f ∈ (A → C) ] Coequalizes q f

  restrictAlong : (B → C) → DescentData
  restrictAlong g = (g ∘ q) , descend-coeq q (g ∘ q) (g , λ _ → refl)

  descentIso : isSurjection q → Iso (B → C) DescentData
  Iso.fun (descentIso surj) = restrictAlong
  Iso.inv (descentIso surj) (f , coeq) = descend setC q f surj coeq
  Iso.rightInv (descentIso surj) (f , coeq) =
    Σ≡Prop (isPropCoequalizes setC q)
           (funExt (descend-β setC q f surj coeq))
  Iso.leftInv (descentIso surj) g =
    descend-unique setC q (g ∘ q) surj
      (descend setC q (g ∘ q) surj (descend-coeq q (g ∘ q) (g , λ _ → refl)))
      g
      (descend-β setC q (g ∘ q) surj (descend-coeq q (g ∘ q) (g , λ _ → refl)))
      (λ _ → refl)

  descentEquiv : isSurjection q → (B → C) ≃ DescentData
  descentEquiv surj = isoToEquiv (descentIso surj)

------------------------------------------------------------------------
-- 5.  THE SPLIT CASE IS A COROLLARY, AND COMPUTES THE SAME ANSWER
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (setC : isSet C) (q : A → B) (f : A → C)
         (s : B → A) (sect : (b : B) → q (s b) ≡ b) where

  private
    surj : isSurjection q
    surj = section→isSurjection sect

  split→descends : Coequalizes q f → Σ[ g ∈ (B → C) ] ((a : A) → g (q a) ≡ f a)
  split→descends coeq = descends setC q f surj coeq

  -- Sharper than "the split case follows": the section-chosen
  -- factorisation `f ∘ s` from DefectCalculus.descends-split and the
  -- choice-free one agree on the nose (as functions).  So a proof that
  -- picks a representative computes the right thing; it merely assumes a
  -- section it does not need.
  split-descent-agrees :
    (coeq : Coequalizes q f)
    → fst (descends-split q f s sect coeq) ≡ descend setC q f surj coeq
  split-descent-agrees coeq =
    descend-unique setC q f surj
      (f ∘ s) (descend setC q f surj coeq)
      (snd (descends-split q f s sect coeq))
      (descend-β setC q f surj coeq)

------------------------------------------------------------------------
-- 6.  CONVERSE: EFFECTIVE DESCENT FORCES SURJECTIVITY
--
-- Tested against a single set — `hProp`, the subobject classifier.  The
-- two subobjects of `B` that agree after restriction along `q` are "the
-- image of q" and "everything"; injectivity of `restrictAlong` at
-- `hProp` identifies them, which says exactly that every fibre is
-- inhabited.
--
-- PRIOR ART, cited not reproved: this is Mac Lane–Moerdijk p. 143
-- corollary 5, present in the pinned library as
-- `Cubical.Functions.Surjection.epi⇒surjective`.  That version demands
-- cancellation against EVERY type of `Type (ℓ-suc (ℓ ⊔ ℓ'))`; §6 demands
-- it against the SINGLE object `hProp (ℓ ⊔ ℓ')` of that same universe —
-- `hProp` is not one level lower, and the library's warning that "f must
-- cancel functions from a higher universe" applies here verbatim.  What
-- is bought is not a smaller universe but a smaller hypothesis: one test
-- object, which is a SET, so that §6's hypothesis is precisely an
-- instance of §4's conclusion and the two compose into an iff.
------------------------------------------------------------------------

module _ {A : Type ℓ} {B : Type ℓ'} (q : A → B) where

  private
    ℓq : Level
    ℓq = ℓ-max ℓ ℓ'

    -- b ↦ "b is in the image of q"
    Im : B → hProp ℓq
    Im b = ∥ fiber q b ∥₁ , isPropPropTrunc

    -- b ↦ "true"
    Top : B → hProp ℓq
    Top _ = Unit* , isPropUnit*

    Im∘q≡Top∘q : Im ∘ q ≡ Top ∘ q
    Im∘q≡Top∘q = funExt λ a →
      Σ≡Prop (λ _ → isPropIsOfHLevel 1)
             (hPropExt isPropPropTrunc isPropUnit*
                       (λ _ → tt*) (λ _ → ∣ a , refl ∣₁))

  hProp-descent→surjection :
    ((g h : B → hProp ℓq) → restrictAlong isSetHProp q g ≡ restrictAlong isSetHProp q h
                          → g ≡ h)
    → isSurjection q
  hProp-descent→surjection inj b =
    transport (sym (cong fst (funExt⁻ Im≡Top b))) tt*
    where
      Im≡Top : Im ≡ Top
      Im≡Top = inj Im Top
        (Σ≡Prop (isPropCoequalizes isSetHProp q) Im∘q≡Top∘q)

  -- Packaged against §4: an equivalence is in particular injective, so
  -- §4's conclusion AT THE SINGLE SET `hProp` already implies `q` is
  -- surjective.  Together with `descentEquiv`, this is
  --
  --     `q` surjective   ⟺   descent along `q` is effective,
  --
  -- and the ⇐ direction needs only one test object.
  descentEquiv→surjection :
    isEquiv (restrictAlong {C = hProp ℓq} isSetHProp q) → isSurjection q
  descentEquiv→surjection eq =
    hProp-descent→surjection
      (λ g h p → sym (retEq E g) ∙∙ cong (invEq E) p ∙∙ retEq E h)
    where
      E : (B → hProp ℓq) ≃ DescentData isSetHProp q
      E = restrictAlong isSetHProp q , eq

------------------------------------------------------------------------
-- 7.  CONTROLS: SURJECTIVITY IS LOAD-BEARING IN §3
--
-- `q : ⊥ → Bool` coequalises vacuously and is not surjective; both
-- constant maps factor it, and they differ.  Without this, §3 could be
-- true because factorisations are never plural.
------------------------------------------------------------------------

emptyMap : ⊥ → Bool
emptyMap = Empty.rec

notSurjection-absurd : isSurjection emptyMap → ⊥
notSurjection-absurd surj = PT.rec isProp⊥ fst (surj true)

emptyCoequalizes : Coequalizes emptyMap emptyMap
emptyCoequalizes x _ _ = Empty.rec x

constTrue-factors : (a : ⊥) → (λ (_ : Bool) → true) (emptyMap a) ≡ emptyMap a
constTrue-factors a = Empty.rec a

constFalse-factors : (a : ⊥) → (λ (_ : Bool) → false) (emptyMap a) ≡ emptyMap a
constFalse-factors a = Empty.rec a

two-factorisations : ((λ (_ : Bool) → true) ≡ (λ (_ : Bool) → false)) → ⊥
two-factorisations p = true≢false (funExt⁻ p true)

-- And the positive control the file would be suspect without: `descend`
-- is not an inert term.  On a surjection whose witness is literally
-- `∣ _ ∣₁`, `rec→Set` reduces, so the descended map COMPUTES — the
-- equation below is `refl`, not a proof.
private
  toUnit : Bool → Unit
  toUnit _ = tt

  surjToUnit : isSurjection toUnit
  surjToUnit _ = ∣ true , refl ∣₁

  constTrue : Bool → Bool
  constTrue _ = true

  coeqTrue : Coequalizes toUnit constTrue
  coeqTrue _ _ _ = refl

descend-computes :
  descend isSetBool toUnit constTrue surjToUnit coeqTrue tt ≡ true
descend-computes = refl

descend-computes-not :
  descend isSetBool toUnit constTrue surjToUnit coeqTrue tt ≡ false → ⊥
descend-computes-not p = true≢false (sym descend-computes ∙ p)

------------------------------------------------------------------------
-- 8.  THE COROLLARY THAT PAID FOR THIS FILE
--
-- `collab/messages/madhavi/future_quotient_linear_rank.md` (absent from this repository), Theorem (2):
--
--     "There is a unique matrix `R : Q × W → K` such that `T = C R`,
--      `C(x,c) = 1` if `q(x) = c` and `0` otherwise."
--
-- `C` is the incidence matrix of the future-behaviour quotient map
-- `q : X → Q`, and `C R` is exactly `R ∘ q`.  Clause (1) of that theorem
-- ("`q x ≡ q y` iff row `T x` equals row `T y`") supplies, in its easy
-- direction, precisely `Coequalizes q T`.  So clause (2) is §2 + §3 at
-- the set `W → K`.
--
-- The published proof begins "Define `R(c,w) = T(x,w)` for ANY `x` with
-- `q(x) = c`" — a representative is chosen and well-definedness is then
-- argued.  Below, no representative is chosen: `q` is surjective ("every
-- quotient class is inhabited", the note's own hypothesis) and `K` is a
-- set, and that is the whole input.
------------------------------------------------------------------------

module MinimalMachine
  {X : Type ℓ} {Q : Type ℓ'} {W K : Type ℓ''}
  (setK : isSet K)
  (q : X → Q) (classesInhabited : isSurjection q)
  (T : X → (W → K))
  (rowsAgreeOnClasses : Coequalizes q T)
  where

  private
    setRows : isSet (W → K)
    setRows = isSetΠ (λ _ → setK)

  R : Q → (W → K)
  R = descend setRows q T classesInhabited rowsAgreeOnClasses

  -- `T = C R`, in the form the note writes it: every row of `T` is the
  -- row of `R` at that state's class.
  T≡CR : (x : X) → R (q x) ≡ T x
  T≡CR = descend-β setRows q T classesInhabited rowsAgreeOnClasses

  -- "unique" in the note's statement, now a theorem rather than an
  -- observation about the definition.
  R-unique :
    (R' : Q → (W → K)) → ((x : X) → R' (q x) ≡ T x) → R' ≡ R
  R-unique R' R'β =
    descend-unique setRows q T classesInhabited R' R R'β T≡CR

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TranscriptComposition
--
-- The object: an exact characterisation of when a STAGEWISE transcript
-- test certifies a COMPOSITE one.
--
-- Setting (codex-quantum-process, worker broadcast 0003).  An action
-- word has an endpoint map `w : X → Y` and a declared transcript
-- `t : X → T`.  The macro that replaces the word by its endpoint
-- preserves the transcript exactly when `t` factors through `w`:
--
--     Factors w t  :=  ∀ x x' → w x ≡ w x' → t x ≡ t x'.
--
-- That broadcast closes with the instruction "apply this test at every
-- nested shortcut stage".  This module shows that instruction is not
-- sufficient, exhibits the exact repair, and characterises precisely
-- which second stages make the stagewise test sufficient.
--
--   laterSurvives          a later stage's transcript always survives
--   compositeImpliesStage  the composite test is STRICTLY stronger
--   criterion→ / criterion←  the exact repair (an iff)
--   injectiveSuffices      second stage injective ⇒ stagewise suffices
--   mergeBreaks            every non-injective second stage carries a
--                          stagewise-clean system whose composite fails
--   recordLowerBound       any sound side record for a fully erasing
--                          composite must be injective on X
--
-- `injectiveSuffices` and `mergeBreaks` together are a sharp dichotomy:
-- the stagewise test is sound for ALL transcripts over `w₂` exactly
-- when `w₂` is injective.  Nothing quantitative is assumed or fitted.
------------------------------------------------------------------------

module TranscriptComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Bool.Properties using (true≢false)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ⁗ : Level

------------------------------------------------------------------------
-- 1.  The two predicates
------------------------------------------------------------------------

-- `Factors w t`: the endpoint value already determines the transcript
-- value, so contracting the word to its endpoint retains nothing.
Factors : {X : Type ℓ} {Y : Type ℓ'} {T : Type ℓ''}
        → (X → Y) → (X → T) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
Factors {X = X} w t = (x x' : X) → w x ≡ w x' → t x ≡ t x'

-- `Determines w r t`: the endpoint TOGETHER WITH a retained side record
-- `r` determines the transcript.  `Factors w t` is the case where the
-- record is constant, i.e. free.
Determines : {X : Type ℓ} {Y : Type ℓ'} {A : Type ℓ''} {T : Type ℓ'''}
           → (X → Y) → (X → A) → (X → T)
           → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))
Determines {X = X} w r t =
  (x x' : X) → w x ≡ w x' → r x ≡ r x' → t x ≡ t x'

isInj : {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Type (ℓ-max ℓ ℓ')
isInj {X = X} f = (x x' : X) → f x ≡ f x' → x ≡ x'

------------------------------------------------------------------------
-- 2.  A two-stage system and its total transcript
------------------------------------------------------------------------

module TwoStage
  {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  {T₁ : Type ℓ'''} {T₂ : Type ℓ⁗}
  (w₁ : X → Y) (t₁ : X → T₁)
  (w₂ : Y → Z) (t₂ : Y → T₂)
  where

  -- composite endpoint map
  W : X → Z
  W = w₂ ∘ w₁

  -- the transcript of the composite word: stage-1 record, then the
  -- stage-2 record read at the intermediate point actually reached
  total : X → T₁ × T₂
  total x = (t₁ x , t₂ (w₁ x))

  ----------------------------------------------------------------------
  -- 2a.  What always composes
  ----------------------------------------------------------------------

  -- A LATER stage's transcript never needs help from earlier stages:
  -- the composite endpoint refines nothing that stage 2 could see.
  laterSurvives : Factors w₂ t₂ → Factors W (t₂ ∘ w₁)
  laterSurvives f x x' p = f (w₁ x) (w₁ x') p

  ----------------------------------------------------------------------
  -- 2b.  The stagewise test is strictly weaker
  ----------------------------------------------------------------------

  -- Passing the composite test implies passing the stage-1 test.
  -- (The converse is refuted in §3.)
  compositeImpliesStage : Factors W t₁ → Factors w₁ t₁
  compositeImpliesStage f x x' p = f x x' (cong w₂ p)

  ----------------------------------------------------------------------
  -- 2c.  The exact repair
  ----------------------------------------------------------------------

  -- The composite word contracts to its endpoint without a side record
  -- iff EVERY stage transcript, including the earlier ones, factors
  -- through the TERMINAL endpoint map `W` — not through its own stage
  -- map.  This is the statement that replaces "test at every stage".
  criterion→ : Factors W total → Factors W t₁ × Factors W (t₂ ∘ w₁)
  criterion→ f =
      (λ x x' p → cong fst (f x x' p))
    , (λ x x' p → cong snd (f x x' p))

  criterion← : Factors W t₁ → Factors W (t₂ ∘ w₁) → Factors W total
  criterion← f g x x' p i = (f x x' p i , g x x' p i)

  ----------------------------------------------------------------------
  -- 2d.  When the stagewise test IS enough
  ----------------------------------------------------------------------

  -- If the second stage merges nothing, no earlier distinction can be
  -- destroyed downstream, and the stagewise tests compose.
  injectiveSuffices : isInj w₂ → Factors w₁ t₁ → Factors w₂ t₂
                    → Factors W total
  injectiveSuffices inj f g x x' p =
    criterion←
      (λ a b q → f a b (inj (w₁ a) (w₁ b) q))
      (laterSurvives g)
      x x' p

------------------------------------------------------------------------
-- 3.  The refutation, in its sharpest form
--
-- Not merely "there is a counterexample": EVERY non-injective second
-- stage carries one.  Given any `w₂` merging two distinct points, the
-- system with first stage the identity, first transcript the identity,
-- and second transcript constant passes both stagewise tests and fails
-- the composite one.  With §2d this is a dichotomy:
--
--     stagewise test sound for all transcripts  ⟺  w₂ injective.
------------------------------------------------------------------------

module MergeBreaks
  {Y : Type ℓ} {Z : Type ℓ'}
  (w₂ : Y → Z) (y y' : Y)
  (merged : w₂ y ≡ w₂ y') (distinct : ¬ (y ≡ y'))
  where

  -- the stagewise-clean system built over the merge
  open TwoStage (idfun Y) (idfun Y) w₂ (λ _ → tt) public

  stage1Clean : Factors (idfun Y) (idfun Y)
  stage1Clean _ _ p = p

  stage2Clean : Factors w₂ (λ (_ : Y) → tt)
  stage2Clean _ _ _ = refl

  compositeFails : ¬ (Factors W total)
  compositeFails f = distinct (cong fst (f y y' merged))

------------------------------------------------------------------------
-- 4.  A concrete instance of §3, self-contained
--
-- X = Y = Bool, Z = Unit.  Stage 1 records everything but hides
-- nothing (its endpoint map is the identity).  Stage 2 records nothing
-- but erases everything.  Each stage is free; the composite needs a
-- full bit.
------------------------------------------------------------------------

module BoolErasure where

  open TwoStage {X = Bool} {Y = Bool} {Z = Unit}
                {T₁ = Bool} {T₂ = Unit}
                (idfun Bool) (idfun Bool) (λ _ → tt) (λ _ → tt) public

  stage1Clean : Factors (idfun Bool) (idfun Bool)
  stage1Clean _ _ p = p

  stage2Clean : Factors {X = Bool} {Y = Unit} {T = Unit}
                        (λ _ → tt) (λ _ → tt)
  stage2Clean _ _ _ = refl

  compositeFails : ¬ (Factors W total)
  compositeFails f = true≢false (cong fst (f true false refl))

------------------------------------------------------------------------
-- 5.  The lower bound on the retained record
--
-- The failure in §3–4 is not a rounding error that one spare symbol
-- absorbs.  When the composite endpoint map is constant, any side
-- record sound for the identity transcript must be injective on `X`;
-- instantiating `X` at an `n`-element type this says the record
-- alphabet admits an injection from that type, i.e. has at least `n`
-- elements.  Since `X` is arbitrary, the gap between the stagewise
-- cost (zero) and the composite cost is unbounded.
------------------------------------------------------------------------

module RecordBound {X : Type ℓ} where

  erase : X → Unit
  erase _ = tt

  recordLowerBound : {A : Type ℓ'} (r : X → A)
                   → Determines erase r (idfun X) → isInj r
  recordLowerBound r d x x' p = d x x' refl p

  -- packaged: a sound record for the erasing composite is an injection
  -- of the whole state space into the record alphabet
  soundRecordIsEmbedding :
    {A : Type ℓ'} → (Σ[ r ∈ (X → A) ] Determines erase r (idfun X))
    → Σ[ r ∈ (X → A) ] isInj r
  soundRecordIsEmbedding (r , d) = r , recordLowerBound r d

------------------------------------------------------------------------
-- 6.  The finite composition law
-- The exact finite composition law (proved elementarily in the
-- accompanying note):
--
--     r₁  ≤  R  ≤  r₁ · f,
--
-- where `r₁` is the stage-1 record size, `f` the merge multiplicity of
-- `w₂` on the image of `w₁`, and `R` the composite record size; both
-- bounds are attained.  `f` is a property of `w₂` alone and is
-- invisible to both stagewise transcript tests — which is the exact
-- sense in which the missing coordinate is a coordinate of the
-- FORGETTING, not of either transcript.
------------------------------------------------------------------------

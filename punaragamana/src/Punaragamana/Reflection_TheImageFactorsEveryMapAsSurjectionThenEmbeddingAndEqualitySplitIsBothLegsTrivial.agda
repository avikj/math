{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- Punarāgamana · प्रतिबिम्ब
--
-- प्रतिबिम्ब (pratibimba) — reflection, image.  The compound is CHOSEN
-- here, descriptively; no source is claimed for it (the same standing as
-- `Carrier` and `EqualitySplit`'s own names).
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.
--
-- `EqualitySplit` proved, fibrewise, that being an equivalence is a
-- PRODUCT of two independent obligations:
--
--     ((b : B) → isContr (शेष f b))  ≃  भेदः f  ×  छादनम् f
--
-- भेदः f  = hasPropFibers f      ("no two points collapsed", an embedding)
-- छादनम् f = (b : B) → शेष f b     ("nothing missing", a split surjection)
--
-- That is a per-point SPLIT of a hypothesis.  This module exhibits the
-- SAME split as a factorisation of the MAP: every f : A → B factors as
--
--     A  --प्रथम-चरण-->  प्रतिबिम्ब f  --द्वितीय-चरण-->  B
--
-- where प्रतिबिम्ब f = Σ[ b ∈ B ] ∥ शेष f b ∥₁ (the propositional image),
-- प्रथम-चरण is UNCONDITIONALLY a surjection, and द्वितीय-चरण is
-- UNCONDITIONALLY an embedding.  f is an equivalence exactly when this
-- factorisation's own obligations trivialise:
--
--   द्वितीय-चरण is an equivalence  ⟺  f is surjective  (isSurjection f)
--   प्रथम-चरण  is an equivalence  ⟺  f is an embedding  (भेदः f, up to
--                                    `EqualitySplit.भेदः→embedding`)
--
-- and both together are exactly `isEquiv≃isEmbedding×isSurjection`
-- (`Cubical.Functions.Surjection`), which is `समता≃भेद×छादन` composed with
-- the observation, proved in §3 below, that छादनम् f and isSurjection f
-- COINCIDE precisely when भेदः f holds — i.e. exactly when the fibres are
-- already propositions, truncation is idempotent (`propTruncIdempotent≃`)
-- and "merely inhabited" and "inhabited" are the same obligation.  So
-- EqualitySplit's per-point product and Image's map factorisation are the
-- SAME theorem, read at two different granularities: EqualitySplit reads it
-- fibre-by-fibre with the UNtruncated छादनम्; the factorisation reads it as
-- one map with the TRUNCATED isSurjection, and §3 is exactly the bridge
-- between the two granularities.
--
-- WHAT IS DONE HERE VS. WHAT IS ALREADY IN THE LIBRARY.
-- `Cubical.Functions.Image` already proves the factorisation itself
-- (`imageInclusion`, `restrictToImage`, `imageFactorization`), the
-- unconditional surjectivity of the first leg
-- (`isSurjectionImageRestriction`), the unconditional embedding-ness of the
-- second leg (built into `imageInclusion`), and the two directions linking
-- an equivalence-first-leg to an embedding (`isEquivEmbeddingOntoImage`,
-- `isEmbeddingFromIsEquivToImage`).  Nothing here reproves those; they are
-- imported and used directly, by name, so their provenance stays visible.
-- What this module adds, as new checked terms:
--
--   1.  the missing converse `isEquiv (द्वितीय-चरण f) ≃ isSurjection f`
--       (the library states the first-leg case; not the second-leg case);
--   2.  the bridge छादनम् f ≃ isSurjection f UNDER भेदः f — the exact
--       identification between EqualitySplit's untruncated obligation and
--       Image's truncated one;
--   3.  `प्रथम-चरण-equiv≃भेदः`, restating the library's embedding-onto-image
--       facts through भेदः so they compose with EqualitySplit directly,
--       exhibiting `प्रतिबिम्ब`'s factorisation and `समता-द्विधा`'s product
--       as the same theorem at two granularities.
------------------------------------------------------------------------

module Punaragamana.Reflection_TheImageFactorsEveryMapAsSurjectionThenEmbeddingAndEqualitySplitIsBothLegsTrivial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; isPropPropTrunc ; propTruncIdempotent≃ ; rec)
open import Cubical.Functions.Embedding
  using (isEmbedding ; hasPropFibers ; hasPropFibers→isEmbedding ; isEmbedding→hasPropFibers)
open import Cubical.Functions.Surjection
  using (isSurjection ; isPropIsSurjection ; isEquiv≃isEmbedding×isSurjection)
open import Cubical.Functions.Image
  using (Image ; isInImage ; isPropIsInImage ; imageInclusion ; restrictToImage
        ; isSurjectionImageRestriction ; imageFactorization
        ; isEquivEmbeddingOntoImage ; isEmbeddingFromIsEquivToImage)

open import Punaragamana.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph
  using (शेष)
open import Punaragamana.EqualitySplit_TheContractibleFibreSplitsAsEmbeddingTimesSurjectionAndTheEmptyAndCrowdedRefusalsAreTheTwoFactorsFailingApart
  using (भेदः ; छादनम् ; समता-द्विधा ; समता≃भेद×छादन ; भेदः→embedding ; embedding→भेदः)

private
  variable
    ℓ : Level

module _ {A B : Type ℓ} (f : A → B) where

  ------------------------------------------------------------------------
  -- 0.  THE FACTORISATION ITSELF, named in this module's vocabulary.
  ------------------------------------------------------------------------

  -- प्रतिबिम्ब f = the propositional image, Σ[ b ∈ B ] ∥ शेष f b ∥₁.
  प्रतिबिम्ब : Type ℓ
  प्रतिबिम्ब = Image f

  प्रथम-चरण : A → प्रतिबिम्ब
  प्रथम-चरण = restrictToImage f

  द्वितीय-चरण : प्रतिबिम्ब → B
  द्वितीय-चरण = fst (imageInclusion f)

  -- the composite recovers f exactly, ON THE NOSE.
  प्रतिबिम्ब-संघटन : द्वितीय-चरण ∘ प्रथम-चरण ≡ f
  प्रतिबिम्ब-संघटन = imageFactorization f

  ------------------------------------------------------------------------
  -- 1.  प्रथम-चरण is UNCONDITIONALLY a surjection.
  ------------------------------------------------------------------------

  प्रथम-चरण-छादकः : isSurjection प्रथम-चरण
  प्रथम-चरण-छादकः = isSurjectionImageRestriction f

  ------------------------------------------------------------------------
  -- 2.  द्वितीय-चरण is UNCONDITIONALLY an embedding.
  ------------------------------------------------------------------------

  द्वितीय-चरण-भिन्नः : isEmbedding द्वितीय-चरण
  द्वितीय-चरण-भिन्नः = snd (imageInclusion f)

  ------------------------------------------------------------------------
  -- 3.  THE BRIDGE.  Under भेदः f (f's fibres already propositions),
  --     the UNTRUNCATED छादनम् f and the TRUNCATED isSurjection f
  --     coincide: truncation is idempotent on an already-prop type.
  ------------------------------------------------------------------------

  छादनम्≃surjection-under-भेदः : भेदः f → छादनम् f ≃ isSurjection f
  छादनम्≃surjection-under-भेदः भ =
    equivΠCod (λ b → invEquiv (propTruncIdempotent≃ (भ b)))

  ------------------------------------------------------------------------
  -- 4.  द्वितीय-चरण IS an equivalence  ⟺  f IS surjective.
  --     (fibre of द्वितीय-चरण over b is isInImage f b, an ALREADY-prop
  --     type by definition, so isEquiv ⟺ inhabited, pointwise.)
  ------------------------------------------------------------------------

  द्वितीय-चरण-equiv≃surjective : isEquiv द्वितीय-चरण ≃ isSurjection f
  द्वितीय-चरण-equiv≃surjective =
    propBiimpl→Equiv (isPropIsEquiv द्वितीय-चरण) isPropIsSurjection to fro
    where
      to : isEquiv द्वितीय-चरण → isSurjection f
      to e b = subst (isInImage f) (equiv-proof e b .fst .snd) (equiv-proof e b .fst .fst .snd)

      द्वितीय-चरण-fibre-prop : (b : B) → isProp (fiber द्वितीय-चरण b)
      द्वितीय-चरण-fibre-prop = isEmbedding→hasPropFibers द्वितीय-चरण-भिन्नः

      fro : isSurjection f → isEquiv द्वितीय-चरण
      equiv-proof (fro sur) b =
        inhProp→isContr
          (rec (द्वितीय-चरण-fibre-prop b)
               (λ (a , pf) → प्रथम-चरण a , pf)
               (sur b))
          (द्वितीय-चरण-fibre-prop b)

  ------------------------------------------------------------------------
  -- 5.  प्रथम-चरण IS an equivalence  ⟺  f IS an embedding.
  --     (Library's `isEquivEmbeddingOntoImage` / `isEmbeddingFromIsEquivToImage`,
  --     restated through भेदः so it composes with EqualitySplit directly.)
  ------------------------------------------------------------------------

  प्रथम-चरण-equiv≃भेदः : isEquiv प्रथम-चरण ≃ भेदः f
  प्रथम-चरण-equiv≃भेदः =
    propBiimpl→Equiv (isPropIsEquiv प्रथम-चरण) (isPropΠ (λ _ → isPropIsProp))
      (λ e → embedding→भेदः f (isEmbeddingFromIsEquivToImage f e))
      (λ भ → isEquivEmbeddingOntoImage (f , भेदः→embedding f भ))

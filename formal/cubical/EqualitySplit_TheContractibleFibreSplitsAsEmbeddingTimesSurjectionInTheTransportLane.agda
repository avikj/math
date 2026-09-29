{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- समता-द्विधा, in the transport lane.
--
-- The punaragamana library (Agda 2.6.3 + cubical v0.5) carries
-- `Punaragamana.SamataDvidha_…`: for any f : A → B,
--
--   ((b : B) → isContr (शेष f b))  ≃  embedding f × split-surjection f
--
-- where शेष f b = fiber f b, embedding = (b → isProp (शेष f b)) =
-- hasPropFibers f, split-surjection = (b → शेष f b).  "Every genuinely
-- independent distinction must survive" (Carrier's law) is a PRODUCT of two
-- orthogonal obligations, and the two ways a residual refuses contractibility
-- — CROWDED (नष्टि) and EMPTY (अवक्तव्यम्) — are the two factors failing apart.
--
-- This module carries the same split into the TRANSPORT lane
-- (`NaturalMachine.SankramanaSesa_EveryTransportOwesItsResidual`), where the
-- identical residual `शेष r = fiber r` already sits under `अलोप-लक्षणम्`
-- (loss-free ⟺ every residual contractible).
-- The split sits beside `-`.
------------------------------------------------------------------------

module EqualitySplit_TheContractibleFibreSplitsAsEmbeddingTimesSurjectionInTheTransportLane where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding using (isEmbedding ; hasPropFibers ; hasPropFibers→isEmbedding ; isEmbedding→hasPropFibers)

open import TransportResidue_EveryTransportOwesItsResidual using (शेष ; अलोप-लक्षणम्)

private
  variable
    ℓ : Level

-- 1.  isContr X ≃ (isProp X × X): contractible = an inhabited proposition.
isContr≃isProp×inhab : {X : Type ℓ} → isContr X ≃ (isProp X × X)
isContr≃isProp×inhab {X = X} =
  propBiimpl→Equiv isPropIsContr rhs-prop to fro
  where
    to  : isContr X → (isProp X × X)
    to c = isContr→isProp c , c .fst
    fro : (isProp X × X) → isContr X
    fro (p , x) = x , p x
    rhs-prop : isProp (isProp X × X)
    rhs-prop = isPropΣ isPropIsProp (λ p → p)

-- 2.  Π distributes over a pointwise product; pure η.
module _ {A : Type ℓ} {P Q : A → Type ℓ} where
  Π×Iso : Iso ((a : A) → (P a × Q a)) (((a : A) → P a) × ((a : A) → Q a))
  Iso.fun      Π×Iso g       = (λ a → fst (g a)) , (λ a → snd (g a))
  Iso.inv      Π×Iso (u , v) = λ a → (u a , v a)
  Iso.rightInv Π×Iso _       = refl
  Iso.leftInv  Π×Iso _       = refl

-- 3.  THE SPLIT.
module _ {A B : Type ℓ} (f : A → B) where

  भेदः   : Type ℓ                    -- no two points collapsed  (= hasPropFibers f)
  भेदः   = (b : B) → isProp (शेष f b)

  छादनम् : Type ℓ                    -- nothing missing          (= split surjection)
  छादनम् = (b : B) → शेष f b

  समता-census : isEquiv f ≃ ((b : B) → isContr (शेष f b))
  समता-census = propBiimpl→Equiv (isPropIsEquiv f) (isPropΠ (λ _ → isPropIsContr))
                                  equiv-proof (λ c → record { equiv-proof = c })

  समता-द्विधा : ((b : B) → isContr (शेष f b)) ≃ (भेदः × छादनम्)
  समता-द्विधा =
    compEquiv (equivΠCod (λ _ → isContr≃isProp×inhab))
              (isoToEquiv Π×Iso)

  समता≃भेद×छादन : isEquiv f ≃ (भेदः × छादनम्)
  समता≃भेद×छादन = compEquiv समता-census समता-द्विधा

  -- the left factor IS "f is an embedding", definitionally (शेष f = fiber f).
  भेदः→embedding : भेदः → isEmbedding f
  भेदः→embedding = hasPropFibers→isEmbedding

  embedding→भेदः : isEmbedding f → भेदः
  embedding→भेदः = isEmbedding→hasPropFibers

  -- THE COROLLARY, tying the split to the lane's headline अलोप-लक्षणम्
  -- (loss-free ⟺ every residual contractible).  Its hypothesis IS the split
  -- product, so: a map that is BOTH an embedding (भेदः) AND split-surjective
  -- (छादनम्) is a transport-equivalence A ≃ B — the exact fibre-census form
  -- of (mono ∧ epi ⟹ iso).  No new proof: invert the split and feed
  -- अलोप-लक्षणम्.
  भेद×छादन→समता : भेदः → छादनम् → A ≃ B
  भेद×छादन→समता e s = अलोप-लक्षणम् f (invEq समता-द्विधा (e , s))

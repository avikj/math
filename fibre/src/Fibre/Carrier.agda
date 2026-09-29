{-# OPTIONS --cubical --safe --guardedness #-}

-- Punarāgamana · Carrier
--
-- THE LAW.
--
--   Every genuinely independent distinction must survive; determined
--   structure may remain explicitly present with its determining path.
--
-- THE SHAPE.  Given f : A → B, a point of Carrier f is a point of A that
-- carries its image along with it, plus the witness that it IS that image:
--
--   base    : A
--   carried : B
--   witness : f base ≡ carried
--
-- Two of those three fields look like new data and are not.  The fibre
--
--   Σ[ b ∈ B ] (f a ≡ b)   =   singl (f a)
--
-- is CONTRACTIBLE: inhabited (it is not empty — (f a , refl) is there), and
-- every inhabitant is joined to that canonical point by a coherent path.  So
-- `carried` and `witness` contribute zero further degrees of freedom, and
--
--   A ≃ Carrier f      and, by univalence,      A ≡ Carrier f.
--
-- Avik's formulation, kept verbatim because it is the whole distinction:
-- carried and witness are "syntactically/proof-relevantly present;
-- informationally determined."
--
-- THE CONVERSE, which is the part that does work.  A NON-contractible fibre
-- cannot be declared equivalent to its base.  Contractibility of the fibre is
-- the hypothesis, not a formality — `fibre-isContr` is what `Σ-law` consumes,
-- and without it `Carrier≃-via-law` does not exist.  The intent is that later
-- number-theoretic constructions literally inhabit this shape rather than be
-- judged to resemble it by prose.
--
-- ON THE NAME.  `punarāgamana` (पुनरागमन), "coming back again / return", is
-- used here as the name of this module family.  It is not being cited from a
-- particular text for a particular technical sense: the compound is chosen
-- here, and no source is claimed for it.
--
-- TWO IMPLEMENTATION FACTS, load-bearing, do not regress them:
--
-- 1. Cubical.Data.Sigma, NOT Cubical.Data.Prod.  Prod's product is a data
--    type with no eta, so nothing reduces until the argument is case-split;
--    Σ has eta, so the commuting square below closes by `refl` for an OPAQUE
--    variable.
--
-- 2. `descend` must NOT pattern match on its argument.  Pattern matching
--    would force a case split where the eta rule already gives reduction.

module Fibre.Carrier where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module _ {A B : Type ℓ} (f : A → B) where

  record Carrier : Type ℓ where
    constructor carry
    field
      base    : A
      carried : B
      witness : f base ≡ carried

  open Carrier public

  -- The fibre over a is singl (f a) — and it is contractible.  Everything
  -- below is a consequence of this one line.
  --
  -- THE SPELLING CARRIES THE DISTINCTION, and that is why it is British.
  -- This is not agda/cubical's `fiber`, and the two are not the same
  -- object:
  --
  --   Cubical.Foundations.Equiv.Base   fiber f y = Σ[ x ∈ A ] (f x ≡ y)
  --   here                             fibre   a = Σ[ b ∈ B ] (f a ≡ b)
  --
  -- Cubical's is a Σ over the DOMAIN — what f collapses onto y, i.e. the
  -- loss.  This one is a Σ over the CODOMAIN — where f a is free to sit,
  -- i.e. the carried slot, which is contractible and therefore free.  The
  -- law below is that those differ, so spelling them alike would not be a
  -- clash to paper over with `hiding`; it would hide the content.
  fibre : A → Type ℓ
  fibre a = singl (f a)

  fibre-isContr : (a : A) → isContr (fibre a)
  fibre-isContr a = isContrSingl (f a)

  -- No pattern match: see implementation fact 2 in the header.
  descend : A → Carrier
  descend a = carry a (f a) refl

  ascend : Carrier → A
  ascend c = base c

  ascend-descend : (a : A) → ascend (descend a) ≡ a
  ascend-descend a = refl

  descend-ascend : (c : Carrier) → descend (ascend c) ≡ c
  descend-ascend (carry a b w) i = carry a (q i .fst) (q i .snd)
    where
      q : Path (singl (f a)) (f a , refl) (b , w)
      q = isContrSingl (f a) .snd (b , w)

  Carrier-Iso : Iso A Carrier
  Carrier-Iso = iso descend ascend descend-ascend ascend-descend

  -- A is equivalent to Carrier f.
  Carrier≃ : A ≃ Carrier
  Carrier≃ = isoToEquiv Carrier-Iso

  -- …and therefore, by univalence, equal to it.
  Carrier≡ : A ≡ Carrier
  Carrier≡ = ua Carrier≃

  carry-transport : A → Carrier
  carry-transport a = transport Carrier≡ a

  -- The β rule for ua.  This is load-bearing rather than decorative:
  -- transport along `ua` does NOT reduce on a neutral variable (it sticks on
  -- prim^unglue), only on canonical form.  Anything downstream that needs
  -- `transport Carrier≡` to BE `descend` has to go through here.
  carry-transport-descend : (a : A) → carry-transport a ≡ descend a
  carry-transport-descend a = uaβ Carrier≃ a

  -- The same statement read as a Σ: a Carrier is a point of A together with a
  -- point of its fibre.  Both round trips are refl, by eta for records and
  -- for Σ.
  Carrier-as-Σ : Iso Carrier (Σ[ a ∈ A ] fibre a)
  Iso.fun      Carrier-as-Σ c       = base c , (carried c , witness c)
  Iso.inv      Carrier-as-Σ (a , p) = carry a (p .fst) (p .snd)
  Iso.rightInv Carrier-as-Σ _       = refl
  Iso.leftInv  Carrier-as-Σ _       = refl

  -- Contracting the second component IS the content.  Feed a non-contractible
  -- fibre here and there is nothing to construct.
  Σ-law : (Σ[ a ∈ A ] fibre a) ≃ A
  Σ-law = Σ-contractSnd fibre-isContr

  Carrier≃-via-law : Carrier ≃ A
  Carrier≃-via-law = compEquiv (isoToEquiv Carrier-as-Σ) Σ-law

-- An endomorphism Φ of the base transports to the carrier and the square
-- commutes on the nose — by refl, for an opaque variable, which is exactly
-- what implementation fact 1 buys.
module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

  Φ-carrier : Carrier f → Carrier f
  Φ-carrier c = descend f (Φ (ascend f c))

  Φ-square : (a : A) → Φ-carrier (descend f a) ≡ descend f (Φ a)
  Φ-square a = refl

  Φ-ascend : (c : Carrier f) → ascend f (Φ-carrier c) ≡ Φ (ascend f c)
  Φ-ascend c = refl

  Φ-transport : (a : A) → carry-transport f (Φ a) ≡ descend f (Φ a)
  Φ-transport a = carry-transport-descend f (Φ a)

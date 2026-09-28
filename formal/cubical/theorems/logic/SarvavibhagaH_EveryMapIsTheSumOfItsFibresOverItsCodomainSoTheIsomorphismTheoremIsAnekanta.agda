{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सर्वविभागः — every map is the sum of its fibres over its codomain, so
-- the isomorphism theorem (and rank–nullity) is anekānta: the image is
-- the naya's quotient, the fibre is exactly what that standpoint cannot
-- see, and the whole domain (prama) is their sum.
--
-- THE ASCENT.  This corpus's one theorem is the quotient/fibre law
-- (`QuotientFiberLaw`, `Abhijnana`): an observation sees a
-- quotient; the fibre is the unseen; the whole is recovered only by taking
-- the fibre into account.  Read on ANY map, that law is the fundamental
-- decomposition of mathematics itself:
--
--     for f : A → B,   A  ≃  Σ[ b ∈ B ] fiber f b .
--
-- The domain is the SUM of its fibres over the codomain.  Every function
-- factors as: send a to its f-value (the QUOTIENT — the naya's view, what
-- is seen), then remember which a it was (the FIBRE — what that view
-- forgot).  This is:
--   • the FIRST ISOMORPHISM THEOREM (A/∼_f ≅ image, ker = the fibre);
--   • RANK–NULLITY (dim A = rank + nullity = image + kernel);
--   • the DRAVYA/PARYĀYA split (`DravyaParyaya`): the substance is the
--     f-value that persists across the fibre, the modes are the fibre's
--     points;
--   • and it is nayavāda (`NayaVada`): the map is a naya reading the
--     b-facet; two a's over one b are the fibre the naya cannot separate;
--     pramāṇa is the whole Σ.
-- One object, worn by all of algebra.
--
-- WHAT IS PROVED:
--   §1  सर्वविभागः : (A ≃ Σ B (fiber f)) for every f — the universal
--       decomposition, constructed (a ↦ (f a, a, refl), inverse the first
--       projection), both round-trips checked.
--   §2  अलुप्तः : the predicate "every fibre is a proposition" (f is an
--       embedding), and one direction: it implies f is injective
--       (`अलुप्त→एकैकः`).  The converse needs B to be a set; it is not
--       proved here.
--   §3  आच्छादकः : the predicate "every fibre has a chosen point" (split
--       surjectivity).  A definition only; no theorem is stated about it.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module SarvavibhagaH_EveryMapIsTheSumOfItsFibresOverItsCodomainSoTheIsomorphismTheoremIsAnekanta where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber ; _≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; iso)
open import Cubical.Foundations.HLevels using (isProp→ ; isPropΠ)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd ; ΣPathP ; Σ-syntax)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

------------------------------------------------------------------------
-- §1  सर्वविभागः — the domain is the sum of its fibres over the codomain.
------------------------------------------------------------------------

सर्वविभाग-समरूपः : (f : A → B) → Iso A (Σ[ b ∈ B ] fiber f b)
Iso.fun      (सर्वविभाग-समरूपः f) a           = f a , a , refl
Iso.inv      (सर्वविभाग-समरूपः f) (b , a , p)  = a
Iso.rightInv (सर्वविभाग-समरूपः f) (b , a , p)  = ΣPathP (p , ΣPathP (refl , triangle))
  where
  -- goal: PathP (λ i → f a ≡ p i) refl p  — the filler of the square
  triangle : PathP (λ i → f a ≡ p i) refl p
  triangle i j = p (i ∧ j)
Iso.leftInv  (सर्वविभाग-समरूपः f) a           = refl

सर्वविभागः : (f : A → B) → A ≃ (Σ[ b ∈ B ] fiber f b)
सर्वविभागः f = isoToEquiv (सर्वविभाग-समरूपः f)

------------------------------------------------------------------------
-- §2  लोपे-एकम् — every fibre a proposition (f an embedding) implies f is
--     injective.  The converse holds when B is a set; not proved here.
------------------------------------------------------------------------

-- any two points of one fibre coincide
अलुप्तः : (f : A → B) → Type _
अलुप्तः {A = A} f = (b : _) → isProp (fiber f b)

अलुप्त→एकैकः : (f : A → B) → अलुप्तः f → (a a' : A) → f a ≡ f a' → a ≡ a'
अलुप्त→एकैकः f h a a' p = cong fst (h (f a') (a , p) (a' , refl))

------------------------------------------------------------------------
-- §3  आच्छादनम् — every fibre has a chosen point (split surjectivity).
--     A definition only.
------------------------------------------------------------------------

आच्छादकः : (f : A → B) → Type _
आच्छादकः {B = B} f = (b : B) → fiber f b

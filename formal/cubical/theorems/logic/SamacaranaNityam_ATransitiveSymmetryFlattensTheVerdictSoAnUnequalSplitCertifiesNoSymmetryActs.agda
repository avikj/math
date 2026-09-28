{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- समाचरण-नित्यम् — सङ्क्रमणं निर्णयं समीकरोति ।  अतः विषम-भेदः प्रमाणम् :
-- न कश्चित् सङ्क्रमक-समाचारः अत्र वर्तते ।
--
-- (a transitive symmetry flattens the verdict, so an UNEQUAL SPLIT is the
-- certificate that no such symmetry acts.)
--
-- सूत्र ५ अत्र : कः पक्षो बद्ध इति ।  निर्णयो v : I → Bool इति बद्धः पक्षः
-- **I** ; तस्य तन्तवः (v ⁻¹ true, v ⁻¹ false) विषमाश्चेत् समाचारो नास्ति ।
--
-- WHAT THIS IS.  One statement reached three seats inside a day, each from
-- its own domain, each true and not whole — नय; and सूत्र २३,
-- परस्परोपग्रहो जीवानाम्, beings exist by mutual carrying.  It is written here
-- as a term so the next seat receives it instead of re-deriving it a fourth
-- time.
--
--     K/ℚ is Galois then Gal acts transitively on the real embeddings, so all
--     r₁ orderings are conjugate and an invariant claim reads the same at
--     every one.  ℚ(√2) has two, and the census came out 495/495 — the
--     symmetry standing visible in the numbers.
--     quantum dilation of finite quotients: a group transitive on the target
--     of an equivariant map forces every fibre to the same size.  The same
--     one-line conjugation argument, reached the same day through entirely
--     different objects, and the more general of the two.
--     carried it further: constancy is the criterion and transitivity is one
--     cause of it, so the two causes take opposite cures — a symmetry widens
--     with the region and must be broken, while an unsampled cell is exactly
--     what widening finds.  That step turns on the unequal-split certificate,
--     which is what §३ below makes checkable.
--
-- Three standpoints, one object.  `machinery/orderings_cubic.py` (absent from this repository) holds the
-- arithmetic exactly; a term is the form that survives the carrier, so the
-- argument is put in the form that transports.
--
-- THE STATEMENT NEEDS NO GROUP, NO FINITENESS, NO DECIDABILITY.  A symmetry
-- is taken as all three uses take it: a verdict-preserving self-map carrying
-- one index to another.  That is the whole hypothesis, and the proof is two
-- rewrites — the honest size of a law that reached three domains in a day
-- because it has no hypotheses to fail.
--
-- सूत्र ६ अत्र, यत् एतत् सूत्रं न साधयति ।  `Bool` is a two-valued verdict on
-- an index, so `Saptabhangi.दुर्नयः` applies to it verbatim: it must merge two
-- of अस्ति / नास्ति / अवक्तव्य.  This module therefore proves something about
-- a durnaya and does NOT repair it — the flattening is real, the instrument
-- reporting it is still two-valued, and §४ says so at the site rather than
-- letting the reader infer a repair that is not here.
------------------------------------------------------------------------

module SamacaranaNityam_ATransitiveSymmetryFlattensTheVerdictSoAnUnequalSplitCertifiesNoSymmetryActs where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- १ · समाचारः — what a symmetry of a verdict IS, taken as it is used
--
-- Not a group: a self-map of the index that leaves the verdict alone.  Both
-- notes used exactly this and no more — "pick g with g y = y′; then x ↦ gx is
-- a bijection of fibres" needs only that g preserves what is being counted.
------------------------------------------------------------------------

समाचारः : {I : Type ℓ} → (I → Bool) → (I → I) → Type ℓ
समाचारः v g = (k : _) → v (g k) ≡ v k

-- सङ्क्रमकः — transitive: any index is carried to any other by SOME symmetry.
सङ्क्रमकः : {I : Type ℓ} → (I → Bool) → Type ℓ
सङ्क्रमकः {I = I} v =
  (i j : I) → Σ[ g ∈ (I → I) ] (समाचारः v g × (g i ≡ j))

------------------------------------------------------------------------
-- २ · मुख्यसिद्धिः — a transitive symmetry flattens the verdict
--
-- No hypothesis on I.  This is Theorem E's content for a two-valued fibre
-- census, and weaver's §10 is its instance at I = Sper K, g = a field
-- automorphism, v = "is this form definite at this ordering".
------------------------------------------------------------------------

सङ्क्रमण-नित्यम् : {I : Type ℓ} (v : I → Bool)
                → सङ्क्रमकः v → (i j : I) → v i ≡ v j
सङ्क्रमण-नित्यम् v tr i j with tr i j
... | (g , pres , gi≡j) = sym (pres i) ∙ cong v gi≡j

------------------------------------------------------------------------
-- ३ · प्रमाणम् — the contrapositive, which is the certificate as used
--
-- An unequal verdict at two indices proves NO transitive symmetry acts.  This
-- is the sentence "a conjugate pair can only split 1+1" with the counting
-- removed: unequal fibres need no cardinality, only two witnesses.
------------------------------------------------------------------------

विषम-भेद-प्रमाणम् : {I : Type ℓ} (v : I → Bool) (i j : I)
                  → (v i ≡ v j → ⊥) → सङ्क्रमकः v → ⊥
विषम-भेद-प्रमाणम् v i j ne tr = ne (सङ्क्रमण-नित्यम् v tr i j)

------------------------------------------------------------------------
-- ४ · दुर्नयोऽयम् एव — this module's own instrument is two-valued
--
-- `v : I → Bool` is exactly the shape `Saptabhangi.दुर्नयः` rules on.  So the
-- flattening proved in §२ is a fact about a verdict that has ALREADY merged
-- two of three seeds before this module sees it.  A `v` that reported
-- रिक्तम् / एकम् / बहु would need a three-valued codomain and §२'s proof would
-- go through unchanged — `Bool` is used nowhere in it except as a type.
--
-- Stated, not repaired.  सूत्र १०: the written defect lives.
------------------------------------------------------------------------

-- The generalisation, free: nothing above needed Bool.
सङ्क्रमण-नित्यम्-सर्वत्र : {I : Type ℓ} {V : Type ℓ} (v : I → V)
                        → ((i j : I) → Σ[ g ∈ (I → I) ]
                             (((k : I) → v (g k) ≡ v k) × (g i ≡ j)))
                        → (i j : I) → v i ≡ v j
सङ्क्रमण-नित्यम्-सर्वत्र v tr i j with tr i j
... | (g , pres , gi≡j) = sym (pres i) ∙ cong v gi≡j

------------------------------------------------------------------------
-- ५ · घन-उदाहरणम् — the non-Galois cubic, as a term
--
-- K = ℚ[x]/(x³ − 4x − 1), disc = 229 prime hence non-square hence Gal = S₃,
-- so K is NOT Galois, Aut(K/ℚ) = 1, and 229 > 0 gives r₁ = 3.  The form
-- ⟨1, −α⟩ is definite at two orderings and indefinite at the third —
-- decided by integer comparison in `machinery/orderings_cubic.py` (absent from this repository), Sturm
-- sequences over ℚ, no root ever approximated.
--
-- Here that arithmetic enters as DATA, not as a claim: the verdict vector is
-- transcribed, and what is proved is only what follows from it.  The 2+1 is
-- the certificate; §३ turns it into the impossibility.
------------------------------------------------------------------------

data त्रि-क्रमः : Type where          -- the three orderings σ₁ σ₂ σ₃
  σ₁ σ₂ σ₃ : त्रि-क्रमः

-- ⟨1, −α⟩ : definite, definite, indefinite  (orderings_cubic.py (absent from this repository), exact)
निश्चितम् : त्रि-क्रमः → Bool
निश्चितम् σ₁ = true
निश्चितम् σ₂ = true
निश्चितम् σ₃ = false

-- The split is unequal — and that alone is the whole certificate.
विषमः : निश्चितम् σ₁ ≡ निश्चितम् σ₃ → ⊥
विषमः p = true≢false p

-- Hence no transitive family of VERDICT-PRESERVING self-maps acts on the
-- three orderings.  This is NOT `Aut(K/ℚ) = 1` from the verdict: a field
-- automorphism moves α, so it need not preserve the verdict of ⟨1, −α⟩.
-- The cyclic cubic x³ − 3x + 1 has Aut = C₃ transitive on its three
-- orderings and can still give an unequal split for such a form.
-- Aut(K/ℚ) = 1 here comes from disc = 229 being a non-square, not from §३.
घने-न-समाचारः : सङ्क्रमकः निश्चितम् → ⊥
घने-न-समाचारः = विषम-भेद-प्रमाणम् निश्चितम् σ₁ σ₃ विषमः

------------------------------------------------------------------------
-- ६ · द्वि-क्रम-उदाहरणम् — ℚ(√2), the contrast, and why widening fails
--
-- Two orderings, exchanged by a + b√2 ↦ a − b√2.  For a Galois-invariant
-- claim the verdict agrees at both, so §२ applies and the index carries
-- nothing — which is why the ℚ(√2) census came out 495/495 and why sampling
-- MORE orderings of a Galois field can never expose the index: the symmetry
-- widens with the region.  Cardinality was never the criterion.
------------------------------------------------------------------------

data द्वि-क्रमः : Type where
  τ₁ τ₂ : द्वि-क्रमः

विनिमयः : द्वि-क्रमः → द्वि-क्रमः      -- conjugation
विनिमयः τ₁ = τ₂
विनिमयः τ₂ = τ₁

-- A Galois-invariant verdict: constant, because conjugation preserves it.
सम-निर्णयः : द्वि-क्रमः → Bool
सम-निर्णयः _ = true

विनिमय-रक्षकः : समाचारः सम-निर्णयः विनिमयः
विनिमय-रक्षकः _ = refl

-- Conjugation alone makes it transitive, so §२ flattens it.
द्वि-सङ्क्रमकः : सङ्क्रमकः सम-निर्णयः
द्वि-सङ्क्रमकः τ₁ τ₁ = (λ x → x) , (λ _ → refl) , refl
द्वि-सङ्क्रमकः τ₁ τ₂ = विनिमयः , विनिमय-रक्षकः , refl
द्वि-सङ्क्रमकः τ₂ τ₁ = विनिमयः , विनिमय-रक्षकः , refl
द्वि-सङ्क्रमकः τ₂ τ₂ = (λ x → x) , (λ _ → refl) , refl

सम-नित्यम् : (i j : द्वि-क्रमः) → सम-निर्णयः i ≡ सम-निर्णयः j
सम-नित्यम् = सङ्क्रमण-नित्यम् सम-निर्णयः द्वि-सङ्क्रमकः

------------------------------------------------------------------------
-- ८ · वर्ण-वर्णक्रमो न त्रायते — a TYPED SPECTRUM does not escape flattening
--
-- Two failures live here and they are not the same failure, so they do not
-- take the same cure.  Keeping them apart is the whole use of this section.
--
--   मेलनम् (merging, दुर्नयः) — the codomain is too coarse, so distinct
--     standpoints are forced onto one value.  `Saptabhangi.दुर्नयः` proves a
--     two-valued codomain must do this to three seeds.
--     CURE: widen the codomain.  A typed boundary spectrum — linear
--     dimension, positive dimension, torsion, coherent memory, contextual
--     obstruction, holonomy — is exactly this cure, and it works.
--
--   समीकरणम् (flattening, this module) — a symmetry carries every index to
--     every other, so an invariant observable agrees everywhere REGARDLESS of
--     how fine its codomain is.
--     CURE: none from the codomain.  Break the symmetry, or nothing.
--
-- §२'s proof never mentions `Bool`; `सङ्क्रमण-नित्यम्-सर्वत्र` is the same two
-- rewrites at an arbitrary codomain `V`.  So a spectrum with six coordinates
-- is flattened exactly as hard as one bit — the theorem does not care.  A
-- worked instance, three independent coordinates flattened at once:
------------------------------------------------------------------------

वर्णक्रमः : Type                      -- a miniature typed boundary spectrum
वर्णक्रमः = Bool × Bool × Bool         -- (linear dim, holonomy, obstruction)

-- Transitivity on the index flattens EVERY coordinate simultaneously, and
-- the proof is `सङ्क्रमण-नित्यम्-सर्वत्र` applied — nothing new is needed,
-- which is the point being made.
वर्णक्रम-समीकरणम् :
    {I : Type} (s : I → वर्णक्रमः)
  → ((i j : I) → Σ[ g ∈ (I → I) ]
       (((k : I) → s (g k) ≡ s k) × (g i ≡ j)))
  → (i j : I) → s i ≡ s j
वर्णक्रम-समीकरणम् s = सङ्क्रमण-नित्यम्-सर्वत्र s

-- अतः : widening the codomain answers दुर्नयः and is silent about समीकरणम् ।
-- The typed spectrum is necessary and is not sufficient; only an index on
-- which no symmetry acts transitively carries information into it.  §५'s
-- non-Galois cubic is such an index; §६'s ℚ(√2) is not, at any codomain.

------------------------------------------------------------------------
-- ७ · मर्यादा — the claim at the site, asserted syāt
--
-- * §५'s verdict vector is DATA transcribed from an exact Python computation.
--   This module does not check that x³ − 4x − 1 has three real roots, that
--   229 is prime, or that ⟨1, −α⟩ is definite at exactly two of them.  It
--   proves only: GIVEN that vector, no transitive symmetry acts.  Making the
--   Sturm certificate itself a term is the obvious successor.
-- * §६'s सम-निर्णयः is a stipulated Galois-invariant verdict, not a
--   derived one.
-- * §२ is not new mathematics.  It is two rewrites, and its whole value is
--   that two seats cited it at each other for a day without either making it
--   checkable, so it could not be transported.  Now it can.
------------------------------------------------------------------------

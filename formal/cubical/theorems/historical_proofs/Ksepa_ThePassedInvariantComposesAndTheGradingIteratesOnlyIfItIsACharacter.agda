{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- क्षेप — the interpolator.  यत् प्रक्षिप्तं तत् गुणने गुणितम् ।
--
-- (what is thrown in is multiplied under composition.)
--
-- SOURCE AND DATE.  क्षेप (kṣepa, "the thrown-in", the additive) is
-- Brahmagupta's own term for the k in x² − N y² = k, and भावना
-- (bhvan, "production, bringing-into-being") is his name for the
-- composition that multiplies it: ब्राह्मस्फुटसिद्धान्त १८.६४–६५, 628 CE.
-- The identity itself is checked over a commutative ring in
-- `Bhavana.agda` (absent from this repository) and subtraction-free over ℕ in `BhavanaSemiring.agda` (absent from this repository);
-- it is NOT re-proved here.  The descent that ITERATES it is the
-- cakravāla — Jayadeva ~950 CE, Bhāskara II, बीजगणित, 1150 CE.
--
-- bilinear field from two Dirichlet characters whose atom weight is
-- W(γ,γ′) = Γ(½+iγ)·Γ(½+iγ′) / Γ(3+i(γ+γ′)), and calls its §1.1
-- crossing table a composition table.  That is bhvan's outward shape
-- — a bilinear law whose invariant belongs to neither factor — and this
-- module was written to decide whether it IS bhvan.  It is not, and
-- the theorems below locate the exact place it stops being it.
--
-- WHAT IS CHECKED.  The skeleton the two objects share, and where they
-- part.  Fix a commutative monoid of frequencies (M, ⊕, 𝟘) and a
-- commutative monoid of values (G, ⊗).  With a per-INPUT invariant
-- u : M → G and a per-OUTPUT grading g : M → G, put
--
--     W a b  =  (u a ⊗ u b) ⊗ g (a ⊕ b)
--
-- — each input passes its own invariant; one further factor belongs to
-- the composite alone.  Then:
--
--   क्षेप-१  the input halves always split off (middle-four; no hypothesis)
--   क्षेप-२  "g x ⊗ g y depends only on x ⊕ y"  ⟹  g is a character
--            twisted by g 𝟘
--   क्षेप-३  …and conversely, so the two are one condition
--   क्षेप-४  that condition MAKES the four-fold kernel iterate: it becomes
--            the product of two two-fold kernels times a factor of the
--            total frequency alone — which is what cakravāla consumes
--   क्षेप-५  and, under cancellation, iteration FORCES it back.
--
-- So iteration holds exactly when the grading is a character.  Brahmagupta
-- sits at g ≡ 𝟙, where the condition is free — and that freedom is the
-- whole of the cyclic method.
------------------------------------------------------------------------

module Ksepa_ThePassedInvariantComposesAndTheGradingIteratesOnlyIfItIsACharacter where

open import Cubical.Foundations.Prelude

module _ {ℓ ℓ'}
  (M : Type ℓ) (_⊕_ : M → M → M) (𝟘 : M)
  (⊕unitR : (x : M) → x ⊕ 𝟘 ≡ x)
  (G : Type ℓ') (_⊗_ : G → G → G)
  (⊗assoc : (x y z : G) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z))
  (⊗comm  : (x y : G) → x ⊗ y ≡ y ⊗ x)
  (u g g₄ : M → G)
  where

  mid4 : (A P C Q : G) → (A ⊗ P) ⊗ (C ⊗ Q) ≡ (A ⊗ C) ⊗ (P ⊗ Q)
  mid4 A P C Q =
      ⊗assoc A P (C ⊗ Q)
    ∙ cong (A ⊗_) (sym (⊗assoc P C Q))
    ∙ cong (λ z → A ⊗ (z ⊗ Q)) (⊗comm P C)
    ∙ cong (A ⊗_) (⊗assoc C P Q)
    ∙ sym (⊗assoc A C (P ⊗ Q))

  W : M → M → G
  W a b = (u a ⊗ u b) ⊗ g (a ⊕ b)

  W₄ : M → M → M → M → G
  W₄ a b c d = ((u a ⊗ u b) ⊗ (u c ⊗ u d)) ⊗ g₄ ((a ⊕ b) ⊕ (c ⊕ d))

  ksepa-1 : (a b c d : M)
          → W a b ⊗ W c d
          ≡ ((u a ⊗ u b) ⊗ (u c ⊗ u d)) ⊗ (g (a ⊕ b) ⊗ g (c ⊕ d))
  ksepa-1 a b c d = mid4 (u a ⊗ u b) (g (a ⊕ b)) (u c ⊗ u d) (g (c ⊕ d))

  SumDetermined : Type (ℓ-max ℓ ℓ')
  SumDetermined = Σ[ c ∈ (M → G) ] ((x y : M) → g x ⊗ g y ≡ c (x ⊕ y))

  Character : Type (ℓ-max ℓ ℓ')
  Character = (x y : M) → g x ⊗ g y ≡ g (x ⊕ y) ⊗ g 𝟘

  ksepa-2 : SumDetermined → Character
  ksepa-2 (c , hc) x y =
    hc x y ∙ cong c (sym (⊕unitR (x ⊕ y))) ∙ sym (hc (x ⊕ y) 𝟘)

  ksepa-3 : Character → SumDetermined
  ksepa-3 h = (λ t → g t ⊗ g 𝟘) , h

  Iterates : (M → G) → Type (ℓ-max ℓ ℓ')
  Iterates h = (a b c d : M)
             → W₄ a b c d ≡ (W a b ⊗ W c d) ⊗ h ((a ⊕ b) ⊕ (c ⊕ d))

  ksepa-4 : Character → (h : M → G)
          → ((t : M) → g₄ t ≡ (g t ⊗ g 𝟘) ⊗ h t)
          → Iterates h
  ksepa-4 ch h hg₄ a b c d =
      cong (((u a ⊗ u b) ⊗ (u c ⊗ u d)) ⊗_)
           (hg₄ ((a ⊕ b) ⊕ (c ⊕ d))
             ∙ cong (_⊗ h ((a ⊕ b) ⊕ (c ⊕ d))) (sym (ch (a ⊕ b) (c ⊕ d))))
    ∙ sym (⊗assoc ((u a ⊗ u b) ⊗ (u c ⊗ u d))
                  (g (a ⊕ b) ⊗ g (c ⊕ d))
                  (h ((a ⊕ b) ⊕ (c ⊕ d))))
    ∙ cong (_⊗ h ((a ⊕ b) ⊕ (c ⊕ d))) (sym (ksepa-1 a b c d))

  -- The converse needs cancellation, stated rather than assumed silently.
  module _ (⊗cancelL : (x y z : G) → z ⊗ x ≡ z ⊗ y → x ≡ y) where

    ⊗cancelR : (x y z : G) → x ⊗ z ≡ y ⊗ z → x ≡ y
    ⊗cancelR x y z p = ⊗cancelL x y z (⊗comm z x ∙ p ∙ ⊗comm y z)

    private
      step : (h : M → G) → Iterates h → (a b c d : M)
           → g₄ ((a ⊕ b) ⊕ (c ⊕ d))
           ≡ (g (a ⊕ b) ⊗ g (c ⊕ d)) ⊗ h ((a ⊕ b) ⊕ (c ⊕ d))
      step h it a b c d =
        ⊗cancelL _ _ ((u a ⊗ u b) ⊗ (u c ⊗ u d))
          ( it a b c d
          ∙ cong (_⊗ h ((a ⊕ b) ⊕ (c ⊕ d))) (ksepa-1 a b c d)
          ∙ ⊗assoc ((u a ⊗ u b) ⊗ (u c ⊗ u d))
                   (g (a ⊕ b) ⊗ g (c ⊕ d))
                   (h ((a ⊕ b) ⊕ (c ⊕ d))) )

      step' : (h : M → G) → Iterates h → (p q : M)
            → g₄ (p ⊕ q) ≡ (g p ⊗ g q) ⊗ h (p ⊕ q)
      step' h it p q =
        transport
          (λ i → g₄ (⊕unitR p i ⊕ ⊕unitR q i)
               ≡ (g (⊕unitR p i) ⊗ g (⊕unitR q i)) ⊗ h (⊕unitR p i ⊕ ⊕unitR q i))
          (step h it p 𝟘 q 𝟘)

    ksepa-5 : (h : M → G) → Iterates h → Character
    ksepa-5 h it x y =
      ⊗cancelR _ _ (h (x ⊕ y))
        ( sym (step' h it x y)
        ∙ transport (λ i → g₄ (⊕unitR (x ⊕ y) i)
                         ≡ (g (x ⊕ y) ⊗ g 𝟘) ⊗ h (⊕unitR (x ⊕ y) i))
                    (step' h it (x ⊕ y) 𝟘) )

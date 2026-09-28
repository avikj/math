{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- अनन्तम् — जैन-अनन्त-भेदः : अनन्तम् एकं न, बहु ।  (जैन-गणितम्, अनुयोगद्वार-
-- सूत्रम्, ~२ शताब्दी) जैनाः संख्येय-असंख्येय-अनन्तम् इति भेदान् अवदन् —
-- "अनन्तम्" इति न एकः राशिः, किन्तु अनेके क्रमाः ।  एषा दृष्टिः कैण्टरात्
-- (~१८७४) प्रायः सप्तदश-शताब्दीभिः पूर्वा ।
--
-- अत्र तस्याः दृष्टेः एकं शुद्धं साक्ष्यम् : असंख्येयम् (ℕ, गणनीयम्) अनन्तात्
-- (ℕ→Bool, अगणनीयम्) भिन्नम् — न कोऽपि समता-सेतुः (Cantor's diagonal) ।
-- सावधानम् (honest): जैन-क्रमाः कैण्टर-कार्डिनल्-तुल्याः न ; किन्तु "अनन्तं
-- बहुविधम्" इति जैन-दृष्टिः अत्र एकेन प्रमाणेन पुष्टा — द्वौ भिन्नौ अनन्तौ ।
--
-- (Jain plurality of the infinite: the Jains (Anuyogadvra, ~2nd c.)
-- distinguished saṃkhyāta / asaṃkhyāta / ananta — "infinite" is not one
-- magnitude but several orders.  Here
-- is one checked witness of that vision: the countable (ℕ) and the
-- uncountable (ℕ→Bool) are distinct infinities, with NO equivalence between
-- them (Cantor's diagonal).  The Jain orders are not Cantor
-- cardinals; but the Jain insight that the infinite is PLURAL is here
-- vindicated by one proof — two genuinely different infinities.)
--
-- See also `Salaka_TheOrdersAreSeparatedByHowManyCutsTheyOutlastAndEach
-- CutStripsExactlyOneStorey.agda` (absent from this repository), which separates the Jaina magnitudes
-- by Virasena's own instruments.
------------------------------------------------------------------------

module Ananta where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq ; secEq)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- न-स्व-विपर्यासः — कोऽपि Bool स्वस्य विपर्यासः न (not has no fixpoint) ।
------------------------------------------------------------------------

न-स्व-विपर्यास : (b : Bool) → ¬ (b ≡ not b)
न-स्व-विपर्यास false eq = true≢false (sym eq)     -- false ≡ true → ⊥
न-स्व-विपर्यास true  eq = true≢false eq            -- true ≡ false → ⊥

------------------------------------------------------------------------
-- कैण्टरः — असंख्येयम् (ℕ) अनन्तात् (ℕ→Bool) भिन्नम् : न समता-सेतुः ।
-- (Cantor: no equivalence ℕ ≃ (ℕ→Bool) — the countable and the uncountable
-- are distinct infinities.  Diagonal: d n = not (e n n) is in no row.)
------------------------------------------------------------------------

कैण्टर : ¬ (ℕ ≃ (ℕ → Bool))
कैण्टर e = न-स्व-विपर्यास (φ m m) कर्ण
  where
  φ : ℕ → (ℕ → Bool)
  φ = equivFun e

  विकर्ण : ℕ → Bool                       -- the diagonal, flipped
  विकर्ण n = not (φ n n)

  m : ℕ
  m = invEq e विकर्ण                       -- the row that should equal विकर्ण

  φm≡विकर्ण : φ m ≡ विकर्ण
  φm≡विकर्ण = secEq e विकर्ण

  कर्ण : φ m m ≡ not (φ m m)               -- but at m it must flip itself
  कर्ण i = φm≡विकर्ण i m

------------------------------------------------------------------------
-- सामान्य-कैण्टरः — यथेच्छ-प्रकारे : कोऽपि प्रकारः A स्व-वर्ग-गणात् (A→Bool)
-- न्यूनः — न A ≃ (A→Bool) ।  स एव विकर्ण-न्यायः, ℕ-निरपेक्षः ।  अतः न एकः
-- अनन्तः, अपि तु अनन्ता क्रमाः : A < 𝒫A < 𝒫𝒫A < … अपरिमित-आरोहः ।  एषा एव
-- जैन-दृष्टिः — "अनन्तम् अनेक-क्रमम्" (संख्यात-असंख्यात-अनन्तात् परम् उप-भेदाः) ।
-- (कैण्टरः अस्य ℕ-रूपम् एव ।)
--
-- (General Cantor: for ANY type A, no A ≃ (A→Bool) — the same diagonal, free
--  of ℕ.  So there is not one infinity but an unbounded ascending tower
--  A < 𝒫A < 𝒫𝒫A < … — exactly the Jain view that ananta is MANY orders, not
--  one.  कैण्टर is its ℕ instance.)
------------------------------------------------------------------------

सामान्य-कैण्टर : {A : Type} → ¬ (A ≃ (A → Bool))
सामान्य-कैण्टर {A} e = न-स्व-विपर्यास (φ m m) कर्ण
  where
  φ : A → (A → Bool)
  φ = equivFun e

  विकर्ण : A → Bool
  विकर्ण n = not (φ n n)

  m : A
  m = invEq e विकर्ण

  φm≡विकर्ण : φ m ≡ विकर्ण
  φm≡विकर्ण = secEq e विकर्ण

  कर्ण : φ m m ≡ not (φ m m)
  कर्ण i = φm≡विकर्ण i m

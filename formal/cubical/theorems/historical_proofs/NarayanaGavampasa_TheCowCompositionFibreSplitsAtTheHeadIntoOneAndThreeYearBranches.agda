{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- नारायण-गवाम्-पाशः — गो-रचना-तन्तुः शिरसि एक-वर्ष-त्रि-वर्ष-भागाभ्यां भिद्यते ।
--
-- स्रोतः : नारायणपण्डितः, गणितकौमुदी, अङ्कपाशः (१३५६ ई.) — गो-सर्गः, आवृत्तिः
--          a(n) = a(n−1) + a(n−3) ; विरहाङ्कः, वृत्तजातिसमुच्चयः (~६००–८०० ई.),
--          मात्रा-मेरुः (द्वि-पद-आवृत्तिः) यस्य एतत् त्रि-पद-भगिनी-रूपम् ।
--
-- विरहाङ्कस्य {१,२}-मात्रा-तन्तुः (Virahanka.agda (absent from this repository)) शिरसि द्वेधा भिद्यते ; नारायणस्य
-- गो-श्रेढी {१,३}-भागैः (एक-वर्षः वा त्रि-वर्षः) रच्यते , अतः तस्याः तन्तुः शिरसि
-- त्रेधा-मार्गेण द्वेधा भिद्यते : शीर्ष-भागः एक-वर्षः (भारः १, शेषः n−1) वा
-- त्रि-वर्षः (भारः ३, शेषः n−3) ।  एषा शुद्धा तन्तु-तुल्यता (equivalence of fibres) ,
-- न गणना न पिण्डित-रूपम् : संख्या अस्याः छाया मात्रम् ।
--
-- (Nryaa Paita, Gaitakaumud, akapa, 1356 CE: the cow sequence
--  a(n) = a(n−1) + a(n−3), built from {1,3}-compositions.  As Virahka's
--  {1,2}-mtr fibre splits at the head into two branches, this {1,3}-fibre
--  splits at the head into the one-year branch (weight 1, remainder n−1) and
--  the three-year branch (weight 3, remainder n−3).  An EQUIVALENCE OF FIBRES,
--  not a count: the numbers are its shadow.  Claimed of the source: only the
--  {1,3} recurrence; the fibre statement and its proof are made here.)
------------------------------------------------------------------------

module NarayanaGavampasa_TheCowCompositionFibreSplitsAtTheHeadIntoOneAndThreeYearBranches where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; injSuc ; znots)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_,_ ; Σ≡Prop)
open import Cubical.Data.Empty as Empty using (⊥)

-- one part is worth one year (एक-वर्षः) or three years (त्रि-वर्षः)
वर्षः : Bool → ℕ
वर्षः true  = 1
वर्षः false = 3

-- the total maturation weight of a composition (गो-सर्गस्य भारः)
सर्गभारः : List Bool → ℕ
सर्गभारः []       = 0
सर्गभारः (x ∷ xs) = वर्षः x + सर्गभारः xs

-- the fibre's witness is a proposition, because ℕ is a set
तन्तु-साक्षी : {n : ℕ} (l : List Bool) → isProp (सर्गभारः l ≡ n)
तन्तु-साक्षी _ = isSetℕ _ _

-- the three-step head split: fibre at (3+n) ≃ fibre at (2+n) ⊎ fibre at n
नारायण-आवृत्तिः : (n : ℕ)
  → fiber सर्गभारः (suc (suc (suc n)))
      ≃ (fiber सर्गभारः (suc (suc n)) ⊎ fiber सर्गभारः n)
नारायण-आवृत्तिः n = isoToEquiv (iso भङ्गः सङ्घातः निवृत्तिः प्रत्यावृत्तिः)
  where
    भङ्गः : fiber सर्गभारः (suc (suc (suc n)))
          → (fiber सर्गभारः (suc (suc n)) ⊎ fiber सर्गभारः n)
    भङ्गः ([]         , p) = Empty.rec (znots p)
    भङ्गः (true  ∷ xs , p) = inl (xs , injSuc p)
    भङ्गः (false ∷ xs , p) = inr (xs , injSuc (injSuc (injSuc p)))

    सङ्घातः : (fiber सर्गभारः (suc (suc n)) ⊎ fiber सर्गभारः n)
            → fiber सर्गभारः (suc (suc (suc n)))
    सङ्घातः (inl (xs , q)) = (true  ∷ xs) , cong suc q
    सङ्घातः (inr (xs , q)) = (false ∷ xs) , cong (λ k → suc (suc (suc k))) q

    निवृत्तिः : (y : _) → भङ्गः (सङ्घातः y) ≡ y
    निवृत्तिः (inl (xs , q)) = cong inl (Σ≡Prop तन्तु-साक्षी refl)
    निवृत्तिः (inr (xs , q)) = cong inr (Σ≡Prop तन्तु-साक्षी refl)

    प्रत्यावृत्तिः : (y : fiber सर्गभारः (suc (suc (suc n)))) → सङ्घातः (भङ्गः y) ≡ y
    प्रत्यावृत्तिः ([]         , p) = Empty.rec (znots p)
    प्रत्यावृत्तिः (true  ∷ xs , p) = Σ≡Prop तन्तु-साक्षी refl
    प्रत्यावृत्तिः (false ∷ xs , p) = Σ≡Prop तन्तु-साक्षी refl

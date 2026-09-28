{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- समास-मेरुः — नारायणस्य समास-भावनायाः सामान्यं रूपम् (गणितकौमुदी, १३५६) ।
--
-- विरहाङ्कस्य {१,२}-मेरुः (Matramerus, j=0) च नारायणस्य {१,३}-गोसर्गः
-- (Narayana, j=1) एकस्य कुलस्य द्वे रूपे : {१, L}-समासाः, L = 2+j ।  इदं तत्
-- सामान्यं वस्तु, यत् Narayana.agda-शीर्षके अवक्तव्यम् आसीत् ।
--
-- जननस्य संरचना : नारायणस्य स्वकीया रीतिः — "परम्परा" (सारणी) — इन्धनेन
-- (fuel) प्रतिबिम्बिता ।  go इन्धने संरचनया आवर्तते, अतः दीर्घ-अंशस्य पश्चात्-
-- मूल्यम् (go f त) पूर्व-गणितं पठति, न पुनः-गणयति — एवं refl-गणना रक्ष्यते ।
-- (SAMASA_MERU_TERMINATION_FINDING.md (absent from this repository) : सरल-अपाकरणः SCT-परीक्षां न सहते ;
--  well-founded refl-गणनां हन्ति ; इन्धन/परम्परा एव धर्म्या ।)
--
-- अस्मिन् पदे सिद्धम् : (१) एकं जनन-सूत्रम्, यस्मात् उभे मेरू (विरहाङ्कः,
-- नारायणः) च {१,४}-कुलं गणनया एव उदेन्ति (refl-उदाहरणे) ; (२) सामान्या
-- आवृत्तिः a(m)=a(m−1)+a(m−L) सर्व-कुले (समास-आवृत्तिः), इन्धन-अनपेक्षत्व-
-- लेम्मया (canon) साधिता — यत् well-founded-आवर्तनं refl-गणनां हनिष्यत् ।
-- (३) साधुता (साधु) : जनितं प्रत्येकं रूपं यथार्थं n-मानं वहति — दीर्घ-योग्यता-
-- विभागेन (splitℕ-≤) । (४) पूर्णता (पूर्णता) : मानं यस्य = n, तत् सर्वं सर्गे n
-- उदेति — अपाकरण-लेम्मया इन्धन-अनपेक्षतया च ।  एवं {१,L}-कुलं पूर्णतया साधितम्
-- (Narayana.agda-तुल्यम्) ; Narayana-शीर्षकस्य अवक्तव्यं ({१,L}-भागे) निवृत्तम् ।
-- केवलं बहु-अंश-गणः (त्रि-अधिक-मानाः) विशाल-अवक्तव्यं तिष्ठति ।
--
-- स्रोतांसि : नारायणपण्डितः, गणितकौमुदी, अङ्कपाशः (१३५६) ; विरहाङ्कः (मेरुः) ।
------------------------------------------------------------------------

module SamasaMeru where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; snotz)
open import Cubical.Data.Nat.Properties using (+-suc)
open import Cubical.Data.Nat.Order using (_≤_ ; _<_ ; ≤-refl ; ≤-trans ; ≤-suc ; pred-≤-pred ; ∸-≤ ; splitℕ-≤)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map ; length)
open import Cubical.Data.List.Properties using (length-map)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Empty as ⊥

------------------------------------------------------------------------
-- गणः — अंशः : ह्रस्वः (=१) वा दीर्घः (=L=2+j) ।  (j-निरपेक्षा संरचना ।)
------------------------------------------------------------------------

data गणः : Type where
  ह्रस्वः : गणः
  दीर्घः : गणः

समासः : Type
समासः = List गणः

length-++ : {A : Type} (xs ys : List A)
          → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- j-आश्रितं जननम् : L = 2+j ।  इन्धन-आवर्तनेन संरचनया समाप्तम् ।
------------------------------------------------------------------------

module _ (j : ℕ) where

  मानम् : समासः → ℕ
  मानम् []           = zero
  मानम् (ह्रस्वः ∷ xs) = suc (मानम् xs)
  मानम् (दीर्घः ∷ xs) = suc (suc (j + मानम् xs))    -- = L + मानम् xs

  ----------------------------------------------------------------------
  -- go इन्धन न : इन्धने संरचनया आवर्तते ।  strip इन्धनं धृत्वा दीर्घ-अंशं
  -- संरचनया अपाकरोति, शेषस्य go इन्धन (पूर्व-गणितम्) आनयति ।
  ----------------------------------------------------------------------

  mutual
    go : ℕ → ℕ → List समासः
    go zero    _       = [] ∷ []               -- इन्धन-क्षयः : केवलं न=0 अर्थे धर्म्यम्
    go (suc f) zero    = [] ∷ []
    go (suc f) (suc m) = map (ह्रस्वः ∷_) (go f m) ++ strip f (suc m) (suc (suc j))

    strip : ℕ → ℕ → ℕ → List समासः
    strip f t       zero    = map (दीर्घः ∷_) (go f t)
    strip f zero    (suc r) = []
    strip f (suc t) (suc r) = strip f t r

  सर्गः : ℕ → List समासः
  सर्गः n = go n n

  L : ℕ
  L = suc (suc j)

  ----------------------------------------------------------------------
  -- go-शून्य : शून्य-मानस्य सर्गः सर्वेन्धने एकः (रिक्तः समासः) ।
  ----------------------------------------------------------------------

  go-शून्य : (f : ℕ) → go f zero ≡ [] ∷ []
  go-शून्य zero    = refl
  go-शून्य (suc f) = refl

  ----------------------------------------------------------------------
  -- अपाकरण-लेम्म : strip f (p+q) p = दीर्घ-आदिकाः (go f q) — शुद्धं जननम् ।
  ----------------------------------------------------------------------

  अपाकरण-लेम्म : (f p q : ℕ)
              → strip f (p + q) p ≡ map (दीर्घः ∷_) (go f q)
  अपाकरण-लेम्म f zero    q = refl
  अपाकरण-लेम्म f (suc p) q = अपाकरण-लेम्म f p q

  ----------------------------------------------------------------------
  -- strip-संगतिः : इन्धन-भेदेऽपि strip समः, यदि go तेषु मानेषु समः ।
  ----------------------------------------------------------------------

  strip-संगतिः : (a₁ a₂ t r : ℕ)
              → (H : (x : ℕ) → x ≤ t → go a₁ x ≡ go a₂ x)
              → strip a₁ t r ≡ strip a₂ t r
  strip-संगतिः a₁ a₂ t       zero    H = cong (map (दीर्घः ∷_)) (H t ≤-refl)
  strip-संगतिः a₁ a₂ zero    (suc r) H = refl
  strip-संगतिः a₁ a₂ (suc t) (suc r) H =
    strip-संगतिः a₁ a₂ t r (λ x x≤t → H x (≤-trans x≤t (≤-suc ≤-refl)))

  ¬s≤z : {m : ℕ} → suc m ≤ zero → ⊥.⊥
  ¬s≤z {m} (k , p) = snotz (sym (+-suc k m) ∙ p)

  ----------------------------------------------------------------------
  -- इन्धन-अनपेक्षता (canon) : पर्याप्तेन्धनं go न परिणमयति ।  बद्ध-प्रबल-
  -- आगमनेन (b-संरचनया) : go f n = go n n यदा n ≤ f (न ≤ b च) ।
  ----------------------------------------------------------------------

  canon : (b f n : ℕ) → n ≤ b → n ≤ f → go f n ≡ go n n
  canon b       f       zero    le lf = go-शून्य f
  canon zero    f       (suc m) le lf = ⊥.rec (¬s≤z le)
  canon (suc b) zero    (suc m) le lf = ⊥.rec (¬s≤z lf)
  canon (suc b) (suc f) (suc m) le lf =
    cong₂ _++_
      (cong (map (ह्रस्वः ∷_)) (canon b f m m≤b m≤f))
      (strip-संगतिः f m m (suc j) Hs)
    where
      m≤b : m ≤ b
      m≤b = pred-≤-pred le
      m≤f : m ≤ f
      m≤f = pred-≤-pred lf
      Hs : (x : ℕ) → x ≤ m → go f x ≡ go m x
      Hs x x≤m = canon b f x (≤-trans x≤m m≤b) (≤-trans x≤m m≤f)
               ∙ sym (canon b m x (≤-trans x≤m m≤b) x≤m)

  ----------------------------------------------------------------------
  -- समास-आवृत्तिः — a(m) = a(m−1) + a(m−L), m = L+n : जनन-दैर्घ्ये ।
  -- L+n-मानस्य पूर्वः = suc j + n ; m−L = n (इन्धन-अनपेक्षतया) ।
  ----------------------------------------------------------------------

  समास-आवृत्तिः : (n : ℕ)
              → length (सर्गः (L + n))
              ≡ length (सर्गः (suc j + n)) + length (सर्गः n)
  समास-आवृत्तिः n =
      cong length step1
    ∙ length-++ A M
    ∙ cong₂ _+_ (length-map (ह्रस्वः ∷_) (go (suc (j + n)) (suc (j + n))))
                ( length-map (दीर्घः ∷_) (go (suc (j + n)) n)
                ∙ cong length fuelinv )
    where
      A : List समासः
      A = map (ह्रस्वः ∷_) (go (suc (j + n)) (suc (j + n)))
      M : List समासः
      M = map (दीर्घः ∷_) (go (suc (j + n)) n)
      step1 : go (L + n) (L + n) ≡ A ++ M
      step1 = cong (A ++_) (अपाकरण-लेम्म (suc (j + n)) (suc (suc j)) n)
      fuelinv : go (suc (j + n)) n ≡ go n n
      fuelinv = canon (suc (j + n)) (suc (j + n)) n (suc j , refl) (suc j , refl)

  ----------------------------------------------------------------------
  -- साधुता — जनितं प्रत्येकं रूपं यथार्थ-मानं वहति ।  (soundness)
  -- अत्र दीर्घ-भागस्य साधुता (साधु-strip) : strip f t r इत्यस्य प्रत्येकं रूपं
  -- मानं L+(t∸r) वहति — दीर्घ-अंशः (L) च शेषः (t∸r) ।  पूर्ण-साधु-go (लघु-भागेन
  -- सह संयोजनम्, दीर्घ-योग्यता-विभागः) उत्तर-पदे ।
  ----------------------------------------------------------------------

  data समास-All (P : समासः → Type) : List समासः → Type where
    []  : समास-All P []
    _∷_ : {x : समासः} {xs : List समासः}
        → P x → समास-All P xs → समास-All P (x ∷ xs)

  All-map : {P Q : समासः → Type} {f : समासः → समासः}
          → ((x : समासः) → P x → Q (f x))
          → {xs : List समासः} → समास-All P xs → समास-All Q (map f xs)
  All-map g []       = []
  All-map g (p ∷ ps) = g _ p ∷ All-map g ps

  साधु-strip : (f t r : ℕ)
             → समास-All (λ ys → मानम् ys ≡ t ∸ r) (go f (t ∸ r))
             → समास-All (λ zs → मानम् zs ≡ suc (suc (j + (t ∸ r)))) (strip f t r)
  साधु-strip f t       zero    H =
    All-map (λ ys pf → cong (λ z → suc (suc (j + z))) pf) H
  साधु-strip f zero    (suc r) H = []
  साधु-strip f (suc t) (suc r) H = साधु-strip f t r H

  All-++ : {P : समासः → Type} {xs ys : List समासः}
         → समास-All P xs → समास-All P ys → समास-All P (xs ++ ys)
  All-++ []       bs = bs
  All-++ (p ∷ ps) bs = p ∷ All-++ ps bs

  -- शेष-रद्दनम् : b ≤ a → b + (a ∸ b) ≡ a (दीर्घ-योग्यतायां मानं यथार्थम्) ।
  शेष-रद्दनम् : (b a : ℕ) → b ≤ a → b + (a ∸ b) ≡ a
  शेष-रद्दनम् zero    a       le = refl
  शेष-रद्दनम् (suc b) zero    le = ⊥.rec (¬s≤z le)
  शेष-रद्दनम् (suc b) (suc a) le = cong suc (शेष-रद्दनम् b a (pred-≤-pred le))

  -- रिक्त-strip : समासः त-मात्रात् अल्पः (त < र) चेत् दीर्घ-भागः रिक्तः ।
  रिक्त-strip : (f t r : ℕ) → suc t ≤ r → strip f t r ≡ []
  रिक्त-strip f t       zero    le = ⊥.rec (¬s≤z le)
  रिक्त-strip f zero    (suc r) le = refl
  रिक्त-strip f (suc t) (suc r) le = रिक्त-strip f t r (pred-≤-pred le)

  ----------------------------------------------------------------------
  -- पूर्ण-साधुता (साधु-go) : पर्याप्तेन्धने जनितं प्रत्येकं रूपं मानं n वहति ।
  -- दीर्घ-योग्यता-विभागः (≤Dec) : L ≤ suc m चेत् दीर्घ-भागः मानं (शेष-रद्दनेन)
  -- suc m आनयति ; अन्यथा (suc m < L) दीर्घ-भागः रिक्तः (रिक्त-strip) ।
  ----------------------------------------------------------------------

  साधु-go : (f n : ℕ) → n ≤ f → समास-All (λ xs → मानम् xs ≡ n) (go f n)
  साधु-go zero    zero    le = refl ∷ []
  साधु-go (suc f) zero    le = refl ∷ []
  साधु-go zero    (suc m) le = ⊥.rec (¬s≤z le)
  साधु-go (suc f) (suc m) le with splitℕ-≤ (suc (suc j)) (suc m)
  ... | inl p =
        All-++ shorts
          (subst (λ w → समास-All (λ zs → मानम् zs ≡ w) (strip f (suc m) (suc (suc j))))
                 (शेष-रद्दनम् (suc (suc j)) (suc m) p)
                 (साधु-strip f (suc m) (suc (suc j))
                   (साधु-go f (suc m ∸ suc (suc j)) (≤-trans (∸-≤ m (suc j)) m≤f))))
    where
      m≤f : m ≤ f
      m≤f = pred-≤-pred le
      shorts : समास-All (λ xs → मानम् xs ≡ suc m) (map (ह्रस्वः ∷_) (go f m))
      shorts = All-map (λ xs pf → cong suc pf) (साधु-go f m m≤f)
  ... | inr q =
        All-++ shorts
          (subst (समास-All (λ zs → मानम् zs ≡ suc m))
                 (sym (रिक्त-strip f (suc m) (suc (suc j)) q))
                 [])
    where
      m≤f : m ≤ f
      m≤f = pred-≤-pred le
      shorts : समास-All (λ xs → मानम् xs ≡ suc m) (map (ह्रस्वः ∷_) (go f m))
      shorts = All-map (λ xs pf → cong suc pf) (साधु-go f m m≤f)

  साधु : (n : ℕ) → समास-All (λ xs → मानम् xs ≡ n) (सर्गः n)
  साधु n = साधु-go n n ≤-refl

  ----------------------------------------------------------------------
  -- पूर्णता — मानं यस्य = n, तत् सर्वं सर्गे n उदेति (completeness) ।
  -- लघु-भागः स्वेन्धने साक्षात् ; दीर्घ-भागः अपाकरण-लेम्मया (strip उद्घाट्य) च
  -- इन्धन-अनपेक्षतया (canon, इन्धनं suc(j+n')-तः n'-मूल्ये संक्रम्य) ।
  ----------------------------------------------------------------------

  data _∈_ (x : समासः) : List समासः → Type where
    here  : {xs : List समासः} → x ∈ (x ∷ xs)
    there : {y : समासः} {xs : List समासः} → x ∈ xs → x ∈ (y ∷ xs)

  ∈-++ˡ : {x : समासः} {xs ys : List समासः} → x ∈ xs → x ∈ (xs ++ ys)
  ∈-++ˡ here      = here
  ∈-++ˡ (there p) = there (∈-++ˡ p)

  ∈-++ʳ : {x : समासः} (xs : List समासः) {ys : List समासः}
        → x ∈ ys → x ∈ (xs ++ ys)
  ∈-++ʳ []       p = p
  ∈-++ʳ (z ∷ zs) p = there (∈-++ʳ zs p)

  ∈-map : {f : समासः → समासः} {x : समासः} {xs : List समासः}
        → x ∈ xs → (f x) ∈ map f xs
  ∈-map here      = here
  ∈-map (there p) = there (∈-map p)

  पूर्णता′ : (ys : समासः) → ys ∈ go (मानम् ys) (मानम् ys)
  पूर्णता′ []          = here
  पूर्णता′ (ह्रस्वः ∷ ys) = ∈-++ˡ (∈-map (पूर्णता′ ys))
  पूर्णता′ (दीर्घः ∷ ys) =
    ∈-++ʳ (map (ह्रस्वः ∷_) (go (suc (j + मानम् ys)) (suc (j + मानम् ys))))
      (subst ((दीर्घः ∷ ys) ∈_)
             (sym (अपाकरण-लेम्म (suc (j + मानम् ys)) (suc (suc j)) (मानम् ys)))
             (∈-map
               (subst (ys ∈_)
                      (sym (canon (suc (j + मानम् ys)) (suc (j + मानम् ys)) (मानम् ys)
                                  (suc j , refl) (suc j , refl)))
                      (पूर्णता′ ys))))

  पूर्णता : (n : ℕ) (ys : समासः) → मानम् ys ≡ n → ys ∈ सर्गः n
  पूर्णता n ys pf = subst (λ k → ys ∈ go k k) pf (पूर्णता′ ys)

------------------------------------------------------------------------
-- प्रति-रूप-उदाहरणे — एकस्मात् सामान्यात् जनन-सूत्रात् उभे मेरू (refl-सिद्धे) ।
--   j=0 : {१,२} = विरहाङ्कः — १,१,२,३,५,८,१३ ।
--   j=1 : {१,३} = नारायणः  — १,१,१,२,३,४,६,९,१३ ।
------------------------------------------------------------------------

विरहाङ्क-५ : length (सर्गः 0 5) ≡ 8      -- {1,2}-रचनाः ५-मानस्य = ८
विरहाङ्क-५ = refl

विरहाङ्क-६ : length (सर्गः 0 6) ≡ 13
विरहाङ्क-६ = refl

नारायण-६ : length (सर्गः 1 6) ≡ 6        -- {1,3}-रचनाः ६-मानस्य = ६
नारायण-६ = refl

नारायण-८ : length (सर्गः 1 8) ≡ 13
नारायण-८ = refl

-- सामान्यता : तृतीयम् उदाहरणम्, {१,४}-कुलम् (j=2) — १,१,१,१,२,३,४,५,६,८,… ।
पञ्चमेरु-८ : length (सर्गः 2 8) ≡ 7       -- {1,4}-रचनाः ८-मानस्य = ७
पञ्चमेरु-८ = refl

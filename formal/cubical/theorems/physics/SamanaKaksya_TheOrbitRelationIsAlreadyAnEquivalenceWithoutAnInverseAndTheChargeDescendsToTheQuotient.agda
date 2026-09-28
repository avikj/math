{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- समानकक्ष्या — एककक्ष्यत्वं समता एव, व्युत्क्रमं विना ।
--
-- (lying on one orbit is already an equivalence relation, with no
--  inverse; and the charge descends to the quotient.)
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS IS.
--
-- For a bare endomorphism `Φ`, the reachability relation `a ~ Φⁿ a` is
-- reflexive and transitive and not symmetric, which suggests a fork:
-- either (a) require `Φ` to be an equivalence and take the groupoid it
-- generates, or (b) state descent along the reflexive-transitive
-- closure and accept a preorder rather than a quotient.
--
-- **The fork is over-specified, and neither rung is needed.**  The
-- reachability relation — `a ~ b := [ n ] Φ a ≡ b`, "b is
-- downstream of a" — is indeed not symmetric.  But that is not the
-- orbit relation; it is a different object.  Lying on ONE orbit is
--
--     a ≈ b  :=  Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] Φᵐ a ≡ Φⁿ b,
--
-- "the two trajectories MEET".  This is symmetric by swapping the two
-- numbers and `sym` — §२ below is three symbols — reflexive at
-- `(0,0,refl)`, and transitive by the commutation of iterates, which
-- holds for a bare endomorphism.  So the equivalence relation needs no
-- inverse at all: `Φ` stays a bare endomorphism throughout §१ℓ§�.
--
-- With that, §४ is the genuine descent statement:
-- for `B` a set, `f` factors as `f̄ ∘ [_]` through `A / ≈`, and the
-- factorisation triangle is `refl` because `SetQuotients.rec` computes
-- on `[ a ]`.  That is "the charge is a function on the quotient, not
-- on the cover" with a quotient actually present, rather than stated on
-- the cover as in `Kaksya` §नℓ§�.
--
-- §५ then shows rung (a) is not a strengthening but a special case:
-- if `Φ` IS an equivalence, its inverse conserves automatically —
-- conservation of `Φ` propagates backwards, one `sym` and one `cong`
-- — and `Φ⁻¹ a ≈ a` holds by `(1, 0, secEq)`.  So the group of
-- `SamraksakaSamuha_…` sits inside this, and  do not use it.§१–§४
--
-- ────────────────────────────────────────────────────────────────────
--
-- **`isSet B` is used only for the quotient** (§४), not for §१–§३, and
-- `A` is not assumed to be a set anywhere.
--
-- TERMS.  कक्ष्या — orbit / orbital circle in the siddhāntic
-- astronomical tradition (Āryabhaṭa, आर्यभटीयम्, 499, and standard in
-- the Sryasiddhnta after); the term is carried in unchanged from
-- `Kaksya_…agda`, with its limit unchanged: attested for a planet's
-- orbit, and its use for the orbit of an endomorphism is this
-- corpus's.  समान — "same, equal", ordinary .  The compound
-- समानकक्ष्या, "same-orbit-ness", is BUILT HERE; no text is claimed for
-- it.  No source states anything below.
------------------------------------------------------------------------

module SamanaKaksya_TheOrbitRelationIsAlreadyAnEquivalenceWithoutAnInverseAndTheChargeDescendsToTheQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; invEq ; secEq ; _≃_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (+-comm)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients using (_/_ ; [_] ; eq/) renaming (rec to /rec)

open import Dhruva_TheSymmetryLivesInTheFibreAndWithoutALossThereIsNoSymmetry
  using (संरक्षणम्)
open import Kaksya_TheChargeIsConstantAlongTheWholeOrbitAndNotOnlyAcrossOneStep
  using (कक्ष्या ; ध्रुवं-कक्ष्यायाम्)

private variable ℓ : Level

------------------------------------------------------------------------
-- १ · कक्ष्या-योगः — iterates add, and therefore commute.
--
-- Both are about `Φ` alone; `f` plays no part and no inverse is used.
------------------------------------------------------------------------

module _ {A : Type ℓ} (Φ : A → A) where

  private
    -- `कक्ष्या` is stated for a pair (f , Φ); the observable is not used
    -- in its definition, so any codomain map will do to name it here.
    φ : ℕ → A → A
    φ = कक्ष्या {B = A} (λ a → a) Φ

  कक्ष्या-योगः : (m n : ℕ) (a : A) → φ (m + n) a ≡ φ m (φ n a)
  कक्ष्या-योगः zero    n a = refl
  कक्ष्या-योगः (suc m) n a = cong Φ (कक्ष्या-योगः m n a)

  कक्ष्या-व्यत्ययः : (m n : ℕ) (a : A) → φ m (φ n a) ≡ φ n (φ m a)
  कक्ष्या-व्यत्ययः m n a =
    sym (कक्ष्या-योगः m n a) ∙ cong (λ k → φ k a) (+-comm m n) ∙ कक्ष्या-योगः n m a

------------------------------------------------------------------------
-- २ · समानकक्ष्या — THE ORBIT RELATION, AND IT IS AN EQUIVALENCE.
--
-- `a ≈ b` says the two forward trajectories MEET.  Not "b is reachable
-- from a" — that is the asymmetric relation, and it is not the orbit's.
------------------------------------------------------------------------

module _ {A : Type ℓ} (Φ : A → A) where

  private
    φ : ℕ → A → A
    φ = कक्ष्या {B = A} (λ a → a) Φ

  समानकक्ष्या : A → A → Type ℓ
  समानकक्ष्या a b = Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ] (φ m a ≡ φ n b)

  -- reflexive: stay put on both sides.
  समान-स्व : (a : A) → समानकक्ष्या a a
  समान-स्व a = zero , zero , refl

  -- SYMMETRIC.  This is the whole of the correction: swap the two
  -- stations and reverse the meeting.  No inverse of `Φ` occurs.
  समान-व्यत्ययः : (a b : A) → समानकक्ष्या a b → समानकक्ष्या b a
  समान-व्यत्ययः a b (m , n , p) = n , m , sym p

  -- transitive: push each meeting along by the other's station, and
  -- use §१'s commutation to line them up.
  समान-संक्रमः : (a b c : A) → समानकक्ष्या a b → समानकक्ष्या b c → समानकक्ष्या a c
  समान-संक्रमः a b c (m , n , p) (p' , q , r) =
    (p' + m) , (n + q) ,
      ( कक्ष्या-योगः Φ p' m a
      ∙ cong (φ p') p
      ∙ कक्ष्या-व्यत्ययः Φ p' n b
      ∙ cong (φ n) r
      ∙ sym (कक्ष्या-योगः Φ n q c) )

------------------------------------------------------------------------
-- ३ · ध्रुवः समानकक्ष्यायाम् — the charge cannot separate two points of
--     one orbit, in the two-sided sense §२ now supplies.
--
-- `Kaksya` §३ gives this for two stations of ONE trajectory.  Here the
-- two points need not be on one trajectory at all: it is enough that
-- their trajectories meet.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) where

  समानकक्ष्ये-अभेदः : संरक्षणम् f Φ → (a b : A) → समानकक्ष्या Φ a b → f a ≡ f b
  समानकक्ष्ये-अभेदः cons a b (m , n , p) =
      sym (ध्रुवं-कक्ष्यायाम् f Φ cons m a)
    ∙ cong f p
    ∙ ध्रुवं-कक्ष्यायाम् f Φ cons n b

------------------------------------------------------------------------
-- ४ · अवतरणम् — THE CHARGE IS A FUNCTION ON THE QUOTIENT.
--
-- The charge is a function on the quotient, with the quotient present.
-- `f` is defined on
-- `A / समानकक्ष्या`, and the factorisation `f ≡ f̄ ∘ [_]` is `refl`,
-- because `SetQuotients.rec` computes on a point class.
--
-- `isSet B` is the quotient's requirement and nothing else's.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A)
         (setB : isSet B) (cons : संरक्षणम् f Φ) where

  भागः : Type ℓ
  भागः = A / समानकक्ष्या Φ

  अवतीर्णः : भागः → B
  अवतीर्णः = /rec setB f (समानकक्ष्ये-अभेदः f Φ cons)

  -- the triangle, on the nose
  अवतरण-त्रिकोणः : (a : A) → अवतीर्णः [ a ] ≡ f a
  अवतरण-त्रिकोणः a = refl

------------------------------------------------------------------------
-- ५ · व्युत्क्रमः — and the inverse case is a special case, not a
--     stronger hypothesis.
--
-- Rung (a) proposed requiring `Φ` to be an equivalence.
-- If it is, two things follow and neither is needed above:
--
--   (a) conservation propagates BACKWARDS with no extra hypothesis —
--       so the "conserving inverse" that `SamraksakaSamuha_…` carries
--       as stored data is derivable whenever the flow is invertible;
--   (b) `Φ⁻¹ a` and `a` lie on one orbit, at stations `(1, 0)`.
--
-- So the group of invertible conserving flows acts within the classes
-- of §, and §§ do not use it.
------------------------------------------------------------------------

module _ {A B : Type ℓ} (f : A → B) (Φ : A → A) (e : isEquiv Φ) where

  private
    ε : A ≃ A
    ε = Φ , e

  व्युत्क्रम-संरक्षणम् : संरक्षणम् f Φ → संरक्षणम् f (invEq ε)
  व्युत्क्रम-संरक्षणम् cons a =
    sym (cons (invEq ε a)) ∙ cong f (secEq ε a)

  व्युत्क्रमः-समानकक्ष्ये : (a : A) → समानकक्ष्या Φ (invEq ε a) a
  व्युत्क्रमः-समानकक्ष्ये a = suc zero , zero , secEq ε a

------------------------------------------------------------------------
--    — the converse, and the h-level of the relation.
--
-- The converse of §४ — that `अवतीर्णः` is injective, i.e. equal charge
-- implies one orbit — is the subject of
-- `Sankramana_TheFibreIsOneOrbitExactlyWhenTheChargeIs
-- InjectiveAndOneSidedReachabilityIsStrictlyStronger.agda` (absent from this repository).  `Kaksya`
-- §'s one-sided `���` is SUFFICIENT and NOT NECESSARY:
-- `A = Bool`, `B = Unit`, `f = λ _ → tt`, `Φ = λ _ → true`.  Every pair
-- meets at stations `(1,1)`, so `अवतीर्णः` is an equivalence, while
-- `सङ्क्रमणम् tt → ⊥` — nothing ever reaches `false`.  The exact
-- hypothesis is the truncated two-sided one, and that module proves the
-- ⟺ and the equivalence
-- `isEquiv f̄ ≃ (isSurjection f × ∀ b → ∥two-sided∥₁)`.
--
-- `समानकक्ष्या` is not valued in propositions — the meeting stations are
-- data.  `SamagamaSthana_TheOrbitRelationIsNeverAPropositionAtAPointAndThe
-- TruncationLosesTheStations.agda` (absent from this repository) §१ proves that `समानकक्ष्या Φ a a` is
-- not a proposition for EVERY `A`, EVERY `Φ` and EVERY `a`, because the
-- diagonal meetings `(0,0,refl)` and `(1,1,refl)` are always there.
--§  there proves the station ωᵀωᵀmapωω does not factor through `_`, and
-- §३ computes the gap exactly in the smallest case:
-- ` id tt tt    ` on `Unit`.  `SetQuotients` truncates
-- the relation, which is the right move for §�.
------------------------------------------------------------------------

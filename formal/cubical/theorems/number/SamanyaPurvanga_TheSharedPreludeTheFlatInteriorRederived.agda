{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SamanyaPurvanga_TheSharedPreludeTheFlatInteriorRederived
--
-- sāmānya — "the common, the universal": the Vaiśeṣika padārtha under
-- which one character inheres in many individuals (Kada,
-- *Vaieika-stra* 1.2.3, "smnya viea iti buddhy-apekam";
-- text dated c. 2nd c. BCE – 2nd c. CE, the date is not settled).
-- prvga — "preceding limb".  The definitions below are
-- the one character that in fact inheres in many modules of this corpus.
--
-- This module REDERIVES, once and in general form, what
-- 9–12 modules each prove locally:
--
--   Family A  eqℕ with refl/soundness/completeness/neq — 9 modules,
--             e.g. NaturalMachine/Obstruction.agda:162 (eqℕ-refl :168,
--             eqℕ→≡ :172), CyclicAliasing.agda:153 (eqℕ-neq :163),
--             ResidueGlue.agda:90 (eqℕ-sound :100).  No one of the
--             nine has all four companion lemmas; this file does.
--   Family B  the Bool equality decider — 10 modules, three names
--             (eqBool/eqb/eqB), three presentations; one table here.
--   Family C  All / Any / _∈_ over lists — 12 modules corpus-wide,
--             e.g. NaturalMachine/AscendingFirstIsTheWorstUnlessThe-
--             ArchiveIsConstant.agda (absent from this repository):86, WalkCapacity.agda:41;
--             level-polymorphic here as in ElsewhereCondition.agda:122.
--   Family D  counting a Bool predicate over a list — 6 modules, with
--             the length bound (RateOneIsExactlyTheUniversalClaim:74).
--   Family E  the HeadDepthTwo.agda / HeadDepthMerge.agda ELEVEN-
--             definition verbatim toolkit: _%%_ _//_ _≤?_ allList
--             countList eqBool mrChain powMod power range vCap.
--   Family F  the componentwise (Pareto) order with transitivity —
--             3 modules (AParetoFitnessHasNoBest…:90, S13OptionSpread:78).
--   Family G  the mod-2 double recursion, made polymorphic — 4 modules
--             (ChargeGrading:134, TransmissionRefutations:176,
--             PingalaPrastara:259, PiPartialOnEveryPrime:135).
------------------------------------------------------------------------

module SamanyaPurvanga_TheSharedPreludeTheFlatInteriorRederived where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; +-suc)
open import Agda.Builtin.Nat using (_==_ ; _<_ ; _*_ ; div-helper ; mod-helper)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-suc ; suc-≤-suc ; zero-≤)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; if_then_else_ ; not ; _and_ ; _or_ ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥ ; ⊥*)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

------------------------------------------------------------------------
-- Family A.  Boolean equality on ℕ, with all four companion lemmas.
-- The Bool form is deliberate: the library's discreteℕ gives Dec, and
-- the engine-style modules demonstrably want Bool (nine times over).
------------------------------------------------------------------------

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ-sound : (m n : ℕ) → eqℕ m n ≡ true → m ≡ n
eqℕ-sound zero    zero    _ = refl
eqℕ-sound zero    (suc n) p = Empty.rec (false≢true p)
eqℕ-sound (suc m) zero    p = Empty.rec (false≢true p)
eqℕ-sound (suc m) (suc n) p = cong suc (eqℕ-sound m n p)

eqℕ-complete : (m n : ℕ) → m ≡ n → eqℕ m n ≡ true
eqℕ-complete m n p = subst (λ k → eqℕ m k ≡ true) p (eqℕ-refl m)

eqℕ-neq : (m n : ℕ) → ¬ m ≡ n → eqℕ m n ≡ false
eqℕ-neq zero    zero    q = Empty.rec (q refl)
eqℕ-neq zero    (suc n) _ = refl
eqℕ-neq (suc m) zero    _ = refl
eqℕ-neq (suc m) (suc n) q = eqℕ-neq m n (λ r → q (cong suc r))

-- The builtin _==_ computes fastest on numerals (the HeadDepth kernels
-- run on it); its soundness is the same induction, so certificates
-- phrased with _==_ need no detour through eqℕ.

==-refl : (n : ℕ) → (n == n) ≡ true
==-refl zero    = refl
==-refl (suc n) = ==-refl n

==-sound : (m n : ℕ) → (m == n) ≡ true → m ≡ n
==-sound zero    zero    _ = refl
==-sound zero    (suc n) p = Empty.rec (false≢true p)
==-sound (suc m) zero    p = Empty.rec (false≢true p)
==-sound (suc m) (suc n) p = cong suc (==-sound m n p)

------------------------------------------------------------------------
-- Family B.  Boolean equality on Bool.  The corpus writes this three
-- ways (4-clause table; if x then y else not y; true c = c / false c =
-- not c); all three agree definitionally on constructors, and the table
-- makes every proof a four-case refl-or-absurdity.
------------------------------------------------------------------------

eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool true  false = false
eqBool false true  = false
eqBool false false = true

eqBool-refl : (b : Bool) → eqBool b b ≡ true
eqBool-refl true  = refl
eqBool-refl false = refl

eqBool-sound : (a b : Bool) → eqBool a b ≡ true → a ≡ b
eqBool-sound true  true  _ = refl
eqBool-sound true  false p = Empty.rec (false≢true p)
eqBool-sound false true  p = Empty.rec (false≢true p)
eqBool-sound false false _ = refl

eqBool-complete : (a b : Bool) → a ≡ b → eqBool a b ≡ true
eqBool-complete a b p = subst (λ c → eqBool a c ≡ true) p (eqBool-refl a)

------------------------------------------------------------------------
-- Family C.  All / Any / membership over lists, as recursive families
-- (an inductive _∈_ indexed by h ∷ gs would rest on injectivity of _∷_,
-- which Cubical Agda does not supply — ElsewhereCondition.agda:118).
-- Level-polymorphic, so both the Type₀ uses and the Guard-level uses
-- instantiate it.
------------------------------------------------------------------------

All : (P : A → Type ℓ') → List A → Type ℓ'
All P []       = Unit*
All P (x ∷ xs) = P x × All P xs

Any : (P : A → Type ℓ') → List A → Type ℓ'
Any P []       = ⊥*
Any P (x ∷ xs) = P x ⊎ Any P xs

_∈_ : {A : Type ℓ} → A → List A → Type ℓ
x ∈ xs = Any (x ≡_) xs

mapAll : {P : A → Type ℓ'} {Q : A → Type ℓ''}
       → ((x : A) → P x → Q x) → (xs : List A) → All P xs → All Q xs
mapAll f []       _        = tt*
mapAll f (x ∷ xs) (p , ps) = f x p , mapAll f xs ps

mapAny : {P : A → Type ℓ'} {Q : A → Type ℓ''}
       → ((x : A) → P x → Q x) → (xs : List A) → Any P xs → Any Q xs
mapAny f []       m       = Empty.rec* m
mapAny f (x ∷ xs) (inl p) = inl (f x p)
mapAny f (x ∷ xs) (inr m) = inr (mapAny f xs m)

-- All is exactly "true at every member".
All-∈ : {P : A → Type ℓ'} {x : A} (xs : List A) → All P xs → x ∈ xs → P x
All-∈ {P = P} []       _        m       = Empty.rec* m
All-∈ {P = P} (y ∷ ys) (p , _)  (inl q) = subst P (sym q) p
All-∈ {P = P} (y ∷ ys) (_ , ps) (inr m) = All-∈ ys ps m

-- Any delivers its witness together with the membership certificate.
Any-witness : {P : A → Type ℓ'} (xs : List A) → Any P xs
            → Σ[ x ∈ A ] ((x ∈ xs) × P x)
Any-witness []       m       = Empty.rec* m
Any-witness (y ∷ ys) (inl p) = y , inl refl , p
Any-witness (y ∷ ys) (inr m) =
  fst r , inr (fst (snd r)) , snd (snd r)
  where r = Any-witness ys m

------------------------------------------------------------------------
-- Family D, and the Bool ⇄ Type bridge.  allList / countList are the
-- kernel-certificate combinators (Family E's list half); the split
-- lemmas connect their Bool verdicts to the All/Any families above,
-- which no local copy in the corpus currently does.
------------------------------------------------------------------------

and-split : (a b : Bool) → (a and b) ≡ true → (a ≡ true) × (b ≡ true)
and-split true  b p = refl , p
and-split false b p = Empty.rec (false≢true p)

or-split : (a b : Bool) → (a or b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-split true  b _ = inl refl
or-split false b p = inr p

or-complete-r : (a b : Bool) → b ≡ true → (a or b) ≡ true
or-complete-r true  b _ = refl
or-complete-r false b p = p

allList : (A → Bool) → List A → Bool
allList f []       = true
allList f (x ∷ xs) = f x and allList f xs

allList-sound : (f : A → Bool) (xs : List A)
              → allList f xs ≡ true → All (λ x → f x ≡ true) xs
allList-sound f []       _ = tt*
allList-sound f (x ∷ xs) p =
  fst q , allList-sound f xs (snd q)
  where q = and-split (f x) (allList f xs) p

allList-complete : (f : A → Bool) (xs : List A)
                 → All (λ x → f x ≡ true) xs → allList f xs ≡ true
allList-complete f []       _        = refl
allList-complete f (x ∷ xs) (p , ps) = cong₂ _and_ p (allList-complete f xs ps)

countList : (A → Bool) → List A → ℕ
countList f []       = 0
countList f (x ∷ xs) = (if f x then 1 else 0) + countList f xs

private
  countStep : (b : Bool) (n m : ℕ) → n ≤ m → ((if b then 1 else 0) + n) ≤ suc m
  countStep true  n m h = suc-≤-suc h
  countStep false n m h = ≤-suc h

countList≤length : (f : A → Bool) (xs : List A) → countList f xs ≤ length xs
countList≤length f []       = zero-≤
countList≤length f (x ∷ xs) = countStep (f x) _ _ (countList≤length f xs)

-- Decidable list membership on ℕ, sound and complete against _∈_.
elemℕ : ℕ → List ℕ → Bool
elemℕ x []       = false
elemℕ x (y ∷ ys) = eqℕ x y or elemℕ x ys

elemℕ-sound : (x : ℕ) (ys : List ℕ) → elemℕ x ys ≡ true → x ∈ ys
elemℕ-sound x []       p = Empty.rec (false≢true p)
elemℕ-sound x (y ∷ ys) p =
  Sum.map (eqℕ-sound x y) (elemℕ-sound x ys)
          (or-split (eqℕ x y) (elemℕ x ys) p)

elemℕ-complete : (x : ℕ) (ys : List ℕ) → x ∈ ys → elemℕ x ys ≡ true
elemℕ-complete x []       m       = Empty.rec* m
elemℕ-complete x (y ∷ ys) (inl q) = cong (_or elemℕ x ys) (eqℕ-complete x y q)
elemℕ-complete x (y ∷ ys) (inr m) =
  or-complete-r (eqℕ x y) (elemℕ x ys) (elemℕ-complete x ys m)

------------------------------------------------------------------------
-- Family E.  The HeadDepthTwo/HeadDepthMerge arithmetic toolkit,
-- verbatim in shape (fast builtin helpers, fuelled where the naive
-- recursion is not structural).  Fuel is a bound on bit length /
-- valuation depth: the HeadDepth kernels run everything at fuel 40.
------------------------------------------------------------------------

_%%_ : ℕ → ℕ → ℕ
n %% zero  = n
n %% suc m = mod-helper 0 m n m

_//_ : ℕ → ℕ → ℕ
n // zero  = 0
n // suc m = div-helper 0 m n m

-- a ≤ e as a Bool (builtin _<_ is Bool-valued)
_≤?_ : ℕ → ℕ → Bool
a ≤? e = a < suc e

power : ℕ → ℕ → ℕ
power b zero    = 1
power b (suc n) = b * power b n

-- modular exponentiation by squaring; fuel bounds the bit length of e
powMod : ℕ → ℕ → ℕ → ℕ → ℕ
powMod zero    m b e = 1 %% m
powMod (suc f) m b e =
  if e == 0 then 1 %% m
  else (let h = powMod f m ((b * b) %% m) (e // 2)
        in if e %% 2 == 1 then (b * h) %% m else h)

-- q-adic valuation, capped by fuel; v(0) saturates to the fuel
vCap : ℕ → ℕ → ℕ → ℕ
vCap zero    q n = 0
vCap (suc f) q n =
  if n == 0 then suc f
  else (if n %% q == 0 then suc (vCap f q (n // q)) else 0)

-- the Miller–Rabin squaring chain (the eleventh name of the pair)
mrChain : ℕ → ℕ → ℕ → Bool
mrChain n zero    x = false
mrChain n (suc k) x =
  if x == n ∸ 1 then true else mrChain n k ((x * x) %% n)

range : ℕ → ℕ → List ℕ
range x zero    = []
range x (suc n) = x ∷ range (suc x) n

range-length : (x n : ℕ) → length (range x n) ≡ n
range-length x zero    = refl
range-length x (suc n) = cong suc (range-length (suc x) n)

------------------------------------------------------------------------
-- Family F.  The componentwise (Pareto) order on List ℕ, with
-- reflexivity and transitivity.
------------------------------------------------------------------------

_≼_ : List ℕ → List ℕ → Type₀
[]       ≼ []       = Unit
[]       ≼ (_ ∷ _)  = ⊥
(_ ∷ _)  ≼ []       = ⊥
(x ∷ xs) ≼ (y ∷ ys) = (x ≤ y) × (xs ≼ ys)

≼-refl : (xs : List ℕ) → xs ≼ xs
≼-refl []       = tt
≼-refl (x ∷ xs) = ≤-refl , ≼-refl xs

≼-trans : (xs ys zs : List ℕ) → xs ≼ ys → ys ≼ zs → xs ≼ zs
≼-trans []       []       []       _       _        = tt
≼-trans []       []       (z ∷ zs) _       q        = Empty.rec q
≼-trans []       (y ∷ ys) _        p       _        = Empty.rec p
≼-trans (x ∷ xs) []       _        p       _        = Empty.rec p
≼-trans (x ∷ xs) (y ∷ ys) []       _       q        = Empty.rec q
≼-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (h , t) (h' , t') =
  ≤-trans h h' , ≼-trans xs ys zs t t'

------------------------------------------------------------------------
-- Family G.  The mod-2 double recursion, once, polymorphic.  The four
-- corpus instances (Bool, ℤ signs, Syllable, a proof-relevant sum) are
-- parityRec at four carriers.
------------------------------------------------------------------------

parityRec : A → A → ℕ → A
parityRec a b zero          = a
parityRec a b (suc zero)    = b
parityRec a b (suc (suc n)) = parityRec a b n

parityRec-step : (a b : A) (n : ℕ) → parityRec a b (suc (suc n)) ≡ parityRec a b n
parityRec-step a b n = refl

parityRec-double : (a b : A) (n : ℕ) → parityRec a b (n + n) ≡ a
parityRec-double a b zero    = refl
parityRec-double a b (suc n) =
  cong (parityRec a b) (cong suc (+-suc n n)) ∙ parityRec-double a b n

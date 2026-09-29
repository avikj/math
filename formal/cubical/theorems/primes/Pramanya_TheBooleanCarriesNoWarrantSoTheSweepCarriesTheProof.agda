{-# OPTIONS --cubical --guardedness --safe #-}

------------------------------------------------------------------------
-- प्रामाण्य — whether a verdict carries its own warrant.
--
-- `Yantra` ships two lanes that compute the same numbers and are
-- joined by nothing.  `Ganana` and `Ekam` decide primality
-- with `prime : ℕ → Bool`, fuelled trial division, and report
-- `fastsweep 500 4 ≡ true`, `tcount 200 ≡ 15`.  `Purna` and
-- `Sakshi` compute the same 15 and the same sweep through `Dec`
-- objects.  The two agree, and nothing in the module set can see that
-- they agree: there is no term of type `prime n ≡ true → IsPrime n`, and
-- a `Bool` that is not the image of a decision asserts a verdict whose
-- ground has been discarded.
--
-- This file does not patch the fuelled `prime`; it removes the need for
-- it.  `decToBool` maps a decision to a boolean and `sound` / `complete`
-- make that map lossless in both directions, so any boolean obtained this
-- way is redeemable for the proof it came from.  Then the Goldbach sweep
-- is rebuilt so that its result is not `true` but the 49 certified
-- decompositions themselves: `everyEvenTo100` is a term of type
-- `AllEven 49 4`, and reading a field out of it produces an actual pair
-- of primes with the addition that closes.
--
-- TERM.  *prmya*, the validity of a cognition, and the dispute over
-- where it comes from: *svataḥ-prāmāṇya*, intrinsic — Kumārila Bhaṭṭa and
-- Prabhākara, Mīmāṃsā, c. 7th c. — against *parataḥ-prāmāṇya*, extrinsic,
-- the Nyya position, where a cognition is certified by successful
-- activity (*pravtti-smarthya*).  A `Dec` arrives carrying its ground; a
-- `Bool` arrives having been stripped of it and must be certified from
-- outside, and the machine provides no outside.
--
------------------------------------------------------------------------

module Pramanya_TheBooleanCarriesNoWarrantSoTheSweepCarriesTheProof where

open import Prakriti using (IsPrime; divides)
open import Purna using (gdec; primeDecAll)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

-- ═══ the bridge, stated once and for all decisions ═══
decToBool : {A : Type₀} → Dec A → Bool
decToBool (yes _) = true
decToBool (no  _) = false

sound : {A : Type₀} (d : Dec A) → decToBool d ≡ true → A
sound (yes a) _ = a
sound (no  _) e = Empty.rec (falseNotTrue e)
  where
  falseNotTrue : false ≡ true → ⊥
  falseNotTrue p = subst F p tt
    where
    F : Bool → Type₀
    F true  = ⊥
    F false = Unit

complete : {A : Type₀} (d : Dec A) → A → decToBool d ≡ true
complete (yes _) _ = refl
complete (no ¬a) a = Empty.rec (¬a a)

-- a boolean primality test that is the image of the certified decision
primeB : ℕ → Bool
primeB n = decToBool (primeDecAll n)

primeB-sound : (n : ℕ) → primeB n ≡ true → IsPrime n
primeB-sound n = sound (primeDecAll n)

primeB-complete : (n : ℕ) → IsPrime n → primeB n ≡ true
primeB-complete n = complete (primeDecAll n)

_ : primeB 97 ≡ true
_ = refl
_ : primeB 91 ≡ false
_ = refl

-- ═══ the extraction habit, used below ═══
True : {A : Type₀} → Dec A → Type₀
True (yes _) = Unit
True (no  _) = ⊥

toWitness : {A : Type₀} {d : Dec A} → True d → A
toWitness {d = yes a} _ = a

-- ═══ Goldbach at one even number, without the search bound in the type ═══
GoldbachAt : ℕ → Type₀
GoldbachAt n = Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] IsPrime p × IsPrime q × (p + q ≡ n)

plusCancelL : (p q : ℕ) → (p + q) ∸ p ≡ q
plusCancelL zero    q = refl
plusCancelL (suc p) q = plusCancelL p q

-- the bound is not a hypothesis: p ≤ n follows from p + q ≡ n
toBounded : (n : ℕ) → GoldbachAt n
          → Σ[ p ∈ ℕ ] (p ≤ n) × (IsPrime p × (IsPrime (n ∸ p) × (p + (n ∸ p) ≡ n)))
toBounded n (p , q , pp , pq , e) =
  p , subst (p ≤_) e ≤SumLeft ,
  pp , subst IsPrime (sym q≡) pq , (cong (p +_) q≡ ∙ e)
  where
  q≡ : n ∸ p ≡ q
  q≡ = cong (_∸ p) (sym e) ∙ plusCancelL p q

fromBounded : (n : ℕ)
            → Σ[ p ∈ ℕ ] (p ≤ n) × (IsPrime p × (IsPrime (n ∸ p) × (p + (n ∸ p) ≡ n)))
            → GoldbachAt n
fromBounded n (p , _ , pp , pq , e) = p , n ∸ p , pp , pq , e

decGoldbachAt : (n : ℕ) → Dec (GoldbachAt n)
decGoldbachAt n with gdec n
... | yes w = yes (fromBounded n w)
... | no ¬w = no λ g → ¬w (toBounded n g)

-- ═══ the sweep, carrying its certificates instead of a flag ═══
AllEven : ℕ → ℕ → Type₀
AllEven zero    n = Unit
AllEven (suc f) n = GoldbachAt n × AllEven f (suc (suc n))

decAllEven : (f n : ℕ) → Dec (AllEven f n)
decAllEven zero    n = yes tt
decAllEven (suc f) n with decGoldbachAt n
... | no ¬g = no λ { (g , _) → ¬g g }
... | yes g with decAllEven f (suc (suc n))
...   | yes rest = yes (g , rest)
...   | no ¬rest = no λ { (_ , rest) → ¬rest rest }

-- ═══ pressed: not `≡ true`, but the proof object itself ═══
everyEvenTo100 : AllEven 49 4
everyEvenTo100 = toWitness {d = decAllEven 49 4} tt

-- and it can be opened: 4 = 2 + 2, with IsPrime on both sides
head-p : ℕ
head-p = fst (fst everyEvenTo100)

head-q : ℕ
head-q = fst (snd (fst everyEvenTo100))

_ : head-p ≡ 2
_ = refl
_ : head-q ≡ 2
_ = refl

-- the certificate for the first summand is a real IsPrime, not a bit
head-prime : IsPrime head-p
head-prime = fst (snd (snd (fst everyEvenTo100)))

-- and the addition closes, by the proof carried in the term
head-sum : head-p + head-q ≡ 4
head-sum = snd (snd (snd (snd (fst everyEvenTo100))))

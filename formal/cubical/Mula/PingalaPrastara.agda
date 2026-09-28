{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Pingala
--
-- The combinatorics of the Chandastra, as checked types.
--
-- SOURCES, with dates.  These are stated as ORIGIN; the European
-- results named at the end are the later restatements.
--
--   Piṅgala, *Chandaḥśāstra* (c. 300–200 BCE), ch. 8: the *pratyaya*,
--   the six procedures on the laghu(light)–guru(heavy) patterns of a
--   metre — prastāra (lay the whole table out), naṣṭa ("the lost one":
--   given a row number, recover its pattern), uddia ("the pointed-at
--   one": given a pattern, recover its row number), sakhy (how many
--   rows), and the *meru-prastra*, the staircase array.
--
--   Virahāṅka, *Vṛttajātisamuccaya* (c. 600–800 CE), ch. 6: states the
--   addition rule for the number of mātrā-vṛtta — metres of fixed
--   DURATION rather than fixed syllable count — explicitly.  This is
--   the *mtrmeru*.
--
--   Halyudha, *Mtasajvan* (10th c.), commentary on Chandastra
--   8.34–8.35: writes the meru-prastāra out as the triangular array in
--   which each interior entry is the sum of the two entries above it.
--
--   Later restatements: Fibonacci, *Liber Abaci* (1202) for the
--   additive sequence; Pascal, *Traité du triangle arithmétique* (1654)
--   for the array; Leibniz, "Explication de l'arithmétique binaire"
--   (1703) for positional binary and the index/pattern conversion.
--
-- WHAT IS PROVED HERE.  No postulates, no holes, no `--safe` escape.
--
--   matrameruIso   Metre (2+n) ≃ Metre (1+n) ⊎ Metre n
--                  Virahāṅka's argument itself — delete the first
--                  syllable.  A bijection of pattern SETS; nothing
--                  numerical has happened yet.
--
--   matrameru      ANY f : ℕ → ℕ with Metre n ≃ Fin (f n) for every n
--                  satisfies f (2+n) ≡ f (1+n) + f n.  The recurrence
--                  is forced by the counting problem — `f` is
--                  arbitrary — so it is not read off a definition.
--
--   uddistaIso     Vak n ≃ Fin (saṅkhyā n), where the forward map is
--                  the explicit uddia algorithm and the inverse is
--                  the explicit naa halving algorithm.  Both round
--                  trips are proved; neither map is defined by
--                  transport along the other.
--
--   pascal         ANY f with Chosen n k ≃ Fin (f n k) satisfies
--                  f (1+n) (1+k) ≡ f n (1+k) + f n k — Halāyudha's
--                  rule for the meru-prastra, forced the same way.
--
-- ONE `Pattern` TYPE, THREE GRADINGS.  A pattern is a plain list of
-- syllables.  `Vak n`, `Metre n` and `Chosen n k` are its fibres over
-- three different statistics — syllable count, mātrā count, and the
-- pair (syllable count, guru count).  That is why the same object
-- carries Piṅgala's 2ⁿ, Virahāṅka's additive sequence and Halāyudha's
-- triangle at once, and it is why no indexed inductive family appears
-- below: matching on one would need injectivity of `suc`, which
-- Cubical Agda flags as not computing under transport.
------------------------------------------------------------------------

module Mula.PingalaPrastara where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (equivToIso)
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc)
open import Cubical.Data.Nat.Properties using (znots ; snotz ; injSuc ; isSetℕ)
open import Cubical.Data.Nat.Order
  using (_<_ ; _≤_ ; ≤-refl ; ≤-trans ; ≤-+-≤ ; <-+-< ; <-asym
        ; ¬-<-zero ; ≤0→≡0 ; pred-≤-pred ; splitℕ-<)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; Σ≡Prop)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties using (⊎Iso)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Fin using (Fin ; toℕ ; toℕ-injective)
open import Cubical.Data.Fin.Properties using (Unit≃Fin1 ; Fin+≅Fin⊎Fin ; Fin-inj)

open Iso

------------------------------------------------------------------------
-- §1  The alphabet: laghu (light, 1 mtr) and guru (heavy, 2 mtr),
--     and the patterns built from it.
--
-- Chandaḥśāstra 1.9–1.10.  Everything below is a word in this
-- two-letter alphabet, weighed in one of three ways.
------------------------------------------------------------------------

data Syllable : Type where
  laghu : Syllable
  guru  : Syllable

Pattern : Type
Pattern = List Syllable

-- the three statistics

mora : Syllable → ℕ           -- mātrā weight of one syllable
mora laghu = 1
mora guru  = 2

matraOf : Pattern → ℕ         -- total duration in mātrā
matraOf []       = 0
matraOf (s ∷ p)  = mora s + matraOf p

varna : Pattern → ℕ           -- number of syllables
varna []       = 0
varna (s ∷ p)  = suc (varna p)

guruOf : Pattern → ℕ          -- number of guru syllables
guruOf []           = 0
guruOf (laghu ∷ p)  = guruOf p
guruOf (guru ∷ p)   = suc (guruOf p)

-- the three graded families, as fibres of those statistics

Metre : ℕ → Type              -- mātrā-vṛtta: fixed duration
Metre n = Σ[ p ∈ Pattern ] (matraOf p ≡ n)

Vak : ℕ → Type                -- varṇa-vṛtta: fixed syllable count
Vak n = Σ[ p ∈ Pattern ] (varna p ≡ n)

Chosen : ℕ → ℕ → Type         -- n syllables of which exactly k guru
Chosen n k = Σ[ p ∈ Pattern ] ((varna p ≡ n) × (guruOf p ≡ k))

-- the fibre conditions are propositions, because ℕ is a set
isPropFib : {f : Pattern → ℕ} {n : ℕ} (p : Pattern) → isProp (f p ≡ n)
isPropFib _ = isSetℕ _ _

isPropFib2 : {n k : ℕ} (p : Pattern) → isProp ((varna p ≡ n) × (guruOf p ≡ k))
isPropFib2 _ = isProp× (isSetℕ _ _) (isSetℕ _ _)

------------------------------------------------------------------------
-- §2  The mtrmeru.
--
-- Virahka's argument, verbatim: look only at the FIRST syllable of a
-- pattern of duration n+2.  If it is laghu, deleting it leaves an
-- arbitrary pattern of duration n+1; if guru, an arbitrary pattern of
-- duration n.  Both deletions are bijections; the two cases are
-- disjoint; the pattern of duration n+2 cannot be empty.
--
-- That sentence is the following Iso and nothing else.
------------------------------------------------------------------------

matrameruIso : (n : ℕ) → Iso (Metre (suc (suc n))) (Metre (suc n) ⊎ Metre n)
fun (matrameruIso n) ([] , e)          = ⊥rec (znots e)
fun (matrameruIso n) (laghu ∷ p , e)   = inl (p , injSuc e)
fun (matrameruIso n) (guru ∷ p , e)    = inr (p , injSuc (injSuc e))
inv (matrameruIso n) (inl (p , e))     = laghu ∷ p , cong suc e
inv (matrameruIso n) (inr (p , e))     = guru ∷ p , cong (λ z → suc (suc z)) e
rightInv (matrameruIso n) (inl (p , e)) = cong inl (Σ≡Prop isPropFib refl)
rightInv (matrameruIso n) (inr (p , e)) = cong inr (Σ≡Prop isPropFib refl)
leftInv (matrameruIso n) ([] , e)         = ⊥rec (znots e)
leftInv (matrameruIso n) (laghu ∷ p , e)  = Σ≡Prop isPropFib refl
leftInv (matrameruIso n) (guru ∷ p , e)   = Σ≡Prop isPropFib refl

-- the mātrāmeru numbers themselves: 1, 1, 2, 3, 5, 8, 13, …
matra : ℕ → ℕ
matra zero          = 1
matra (suc zero)    = 1
matra (suc (suc n)) = matra (suc n) + matra n

-- the two degenerate rows.  Duration 0 admits only the empty pattern;
-- duration 1 only the single laghu.
matraZero : (p : Pattern) → matraOf p ≡ 0 → p ≡ []
matraZero []          e = refl
matraZero (laghu ∷ p) e = ⊥rec (snotz e)
matraZero (guru ∷ p)  e = ⊥rec (snotz e)

Metre0Iso : Iso (Metre 0) Unit
fun Metre0Iso _                     = tt
inv Metre0Iso _                     = [] , refl
rightInv Metre0Iso tt               = refl
leftInv Metre0Iso ([] , e)          = Σ≡Prop isPropFib refl
leftInv Metre0Iso (laghu ∷ p , e)   = ⊥rec (snotz e)
leftInv Metre0Iso (guru ∷ p , e)    = ⊥rec (snotz e)

Metre1Iso : Iso (Metre 1) Unit
fun Metre1Iso _                    = tt
inv Metre1Iso _                    = laghu ∷ [] , refl
rightInv Metre1Iso tt              = refl
leftInv Metre1Iso ([] , e)         = ⊥rec (znots e)
leftInv Metre1Iso (laghu ∷ p , e)  =
  Σ≡Prop isPropFib (cong (laghu ∷_) (sym (matraZero p (injSuc e))))
leftInv Metre1Iso (guru ∷ p , e)   = ⊥rec (snotz (injSuc e))

-- Metre n has exactly `matra n` elements.
matraCount : (n : ℕ) → Iso (Metre n) (Fin (matra n))
matraCount zero       = compIso Metre0Iso (equivToIso Unit≃Fin1)
matraCount (suc zero) = compIso Metre1Iso (equivToIso Unit≃Fin1)
matraCount (suc (suc n)) =
  compIso (matrameruIso n)
    (compIso (⊎Iso (matraCount (suc n)) (matraCount n))
             (invIso (Fin+≅Fin⊎Fin (matra (suc n)) (matra n))))

-- THE THEOREM.  Any function that counts Metre satisfies the mtrmeru
-- recurrence.  `f` is arbitrary and the only hypothesis is that it
-- counts the patterns, so this is a statement about the combinatorics
-- and not about how `matra` happens to be written.
matrameru : (f : ℕ → ℕ)
          → ((n : ℕ) → Iso (Metre n) (Fin (f n)))
          → (n : ℕ) → f (suc (suc n)) ≡ f (suc n) + f n
matrameru f cnt n = Fin-inj _ _ path
  where
    path : Fin (f (suc (suc n))) ≡ Fin (f (suc n) + f n)
    path =
        sym (isoToPath (cnt (suc (suc n))))
      ∙ isoToPath (matrameruIso n)
      ∙ isoToPath (⊎Iso (cnt (suc n)) (cnt n))
      ∙ sym (isoToPath (Fin+≅Fin⊎Fin (f (suc n)) (f n)))

matraRecurrence : (n : ℕ) → matra (suc (suc n)) ≡ matra (suc n) + matra n
matraRecurrence = matrameru matra matraCount

------------------------------------------------------------------------
-- §3  Prastra, sakhy, uddia, naa.
--
-- Chandaḥśāstra 8.24–8.28.  A metre of n syllables has saṅkhyā 2ⁿ
-- patterns.  Piṅgala's naṣṭa is a halving algorithm — halve the row
-- number; if it halves evenly write laghu, otherwise add one, halve,
-- and write guru — and his uddiṣṭa runs it backwards.  Both are
-- written out here as ordinary recursive functions, and both round
-- trips are proved.  Neither is defined by transporting the other.
------------------------------------------------------------------------

count : ℕ → ℕ
count zero    = 1
count (suc n) = count n + count n

-- laghu reads 0, guru reads 1: the positional value of one syllable.
aksara : Syllable → ℕ
aksara laghu = 0
aksara guru  = 1

-- uddiṣṭa: pattern ↦ row number.  The first syllable is the least
-- significant place, which is the direction the halving runs.
uddista : Pattern → ℕ
uddista []      = 0
uddista (s ∷ p) = aksara s + (uddista p + uddista p)

-- the two halves of Pigala's step, each structurally recursive
half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc k)) = suc (half k)

parity : ℕ → Syllable
parity zero          = laghu
parity (suc zero)    = guru
parity (suc (suc k)) = parity k

-- naṣṭa: row number ↦ pattern of n syllables
nasta : ℕ → ℕ → Pattern
nasta zero    k = []
nasta (suc n) k = parity k ∷ nasta n (half k)

varna-nasta : (n k : ℕ) → varna (nasta n k) ≡ n
varna-nasta zero    k = refl
varna-nasta (suc n) k = cong suc (varna-nasta n (half k))

-- ---- the four halving lemmas -----------------------------------------

halfDouble : (u : ℕ) → half (u + u) ≡ u
halfDouble zero    = refl
halfDouble (suc u) =
  cong (λ z → half (suc z)) (+-suc u u) ∙ cong suc (halfDouble u)

halfSucDouble : (u : ℕ) → half (suc (u + u)) ≡ u
halfSucDouble zero    = refl
halfSucDouble (suc u) =
  cong (λ z → half (suc (suc z))) (+-suc u u) ∙ cong suc (halfSucDouble u)

parityDouble : (u : ℕ) → parity (u + u) ≡ laghu
parityDouble zero    = refl
parityDouble (suc u) = cong (λ z → parity (suc z)) (+-suc u u) ∙ parityDouble u

paritySucDouble : (u : ℕ) → parity (suc (u + u)) ≡ guru
paritySucDouble zero    = refl
paritySucDouble (suc u) =
  cong (λ z → parity (suc (suc z))) (+-suc u u) ∙ paritySucDouble u

-- ---- naa ∘ uddia ≡ id --------------------------------------------

nasta-uddista : (p : Pattern) → nasta (varna p) (uddista p) ≡ p
nasta-uddista []          = refl
nasta-uddista (laghu ∷ p) =
  cong₂ _∷_ (parityDouble (uddista p))
            (cong (nasta (varna p)) (halfDouble (uddista p)) ∙ nasta-uddista p)
nasta-uddista (guru ∷ p)  =
  cong₂ _∷_ (paritySucDouble (uddista p))
            (cong (nasta (varna p)) (halfSucDouble (uddista p)) ∙ nasta-uddista p)

-- ---- uddia ∘ naa ≡ id on the table -------------------------------
--
-- This direction needs the bound.  `nasta n` is total on ℕ, but the
-- prastra of an n-syllable metre has only sakhy n rows, and outside
-- them naṣṭa reads the row number modulo 2ⁿ.

-- the division algorithm for 2, which is exactly what Pigala's step is
splitTwo : (k : ℕ) → aksara (parity k) + (half k + half k) ≡ k
splitTwo zero       = refl
splitTwo (suc zero) = refl
splitTwo (suc (suc k)) =
    cong (λ z → aksara (parity k) + suc z) (+-suc (half k) (half k))
  ∙ +-suc (aksara (parity k)) (suc (half k + half k))
  ∙ cong suc (+-suc (aksara (parity k)) (half k + half k))
  ∙ cong (λ z → suc (suc z)) (splitTwo k)

halfLe : (k : ℕ) → (half k + half k) ≤ k
halfLe k = aksara (parity k) , splitTwo k

halfBound : (d k : ℕ) → k < (d + d) → half k < d
halfBound d k k< with splitℕ-< (half k) d
... | inl h<d = h<d
... | inr d≤h = ⊥rec (<-asym k< (≤-trans (≤-+-≤ d≤h d≤h) (halfLe k)))

uddista-nasta : (n k : ℕ) → k < count n → uddista (nasta n k) ≡ k
uddista-nasta zero k k< = sym (≤0→≡0 (pred-≤-pred k<))
uddista-nasta (suc n) k k< =
    cong (λ z → aksara (parity k) + (z + z))
         (uddista-nasta n (half k) (halfBound (count n) k k<))
  ∙ splitTwo k

-- ---- the row number of a pattern is a row of its own table -----------

uddistaBound : (p : Pattern) → uddista p < count (varna p)
uddistaBound []          = ≤-refl
uddistaBound (laghu ∷ p) = <-+-< (uddistaBound p) (uddistaBound p)
uddistaBound (guru ∷ p)  =
  subst (λ z → suc z ≤ (count (varna p) + count (varna p)))
        (+-suc (uddista p) (uddista p))
        (≤-+-≤ (uddistaBound p) (uddistaBound p))

-- THE THEOREM.  uddia and naa are mutually inverse, and the
-- prastāra of an n-syllable metre has exactly saṅkhyā n = 2ⁿ rows.
uddistaIso : (n : ℕ) → Iso (Vak n) (Fin (count n))
fun (uddistaIso n) (p , e) =
  uddista p , subst (λ m → uddista p < count m) e (uddistaBound p)
inv (uddistaIso n) i = nasta n (toℕ i) , varna-nasta n (toℕ i)
rightInv (uddistaIso n) i = toℕ-injective (uddista-nasta n (toℕ i) (i .snd))
leftInv (uddistaIso n) (p , e) =
  Σ≡Prop isPropFib (cong (λ m → nasta m (uddista p)) (sym e) ∙ nasta-uddista p)

------------------------------------------------------------------------
-- §4  The meru-prastra.
--
-- Chandaḥśāstra 8.34–8.35 with Halāyudha's commentary: the staircase
-- array whose (n,k) entry counts the patterns of n syllables carrying
-- exactly k guru, and in which each interior entry is the sum of the
-- two entries above it.
--
-- Halyudha's rule is again a bijection first and an addition second:
-- split an (n+1, k+1) pattern on its first syllable.
------------------------------------------------------------------------

pascalIso : (n k : ℕ)
          → Iso (Chosen (suc n) (suc k)) (Chosen n (suc k) ⊎ Chosen n k)
fun (pascalIso n k) ([] , e , g)         = ⊥rec (znots e)
fun (pascalIso n k) (laghu ∷ p , e , g)  = inl (p , injSuc e , g)
fun (pascalIso n k) (guru ∷ p , e , g)   = inr (p , injSuc e , injSuc g)
inv (pascalIso n k) (inl (p , e , g))    = laghu ∷ p , cong suc e , g
inv (pascalIso n k) (inr (p , e , g))    = guru ∷ p , cong suc e , cong suc g
rightInv (pascalIso n k) (inl (p , e , g)) = cong inl (Σ≡Prop isPropFib2 refl)
rightInv (pascalIso n k) (inr (p , e , g)) = cong inr (Σ≡Prop isPropFib2 refl)
leftInv (pascalIso n k) ([] , e , g)        = ⊥rec (znots e)
leftInv (pascalIso n k) (laghu ∷ p , e , g) = Σ≡Prop isPropFib2 refl
leftInv (pascalIso n k) (guru ∷ p , e , g)  = Σ≡Prop isPropFib2 refl

-- the array
meru : ℕ → ℕ → ℕ
meru zero    zero    = 1
meru zero    (suc k) = 0
meru (suc n) zero    = 1
meru (suc n) (suc k) = meru n (suc k) + meru n k

-- the k = 0 column: the all-laghu pattern of length n, and nothing else
allLaghu : ℕ → Pattern
allLaghu zero    = []
allLaghu (suc n) = laghu ∷ allLaghu n

varna-allLaghu : (n : ℕ) → varna (allLaghu n) ≡ n
varna-allLaghu zero    = refl
varna-allLaghu (suc n) = cong suc (varna-allLaghu n)

guru-allLaghu : (n : ℕ) → guruOf (allLaghu n) ≡ 0
guru-allLaghu zero    = refl
guru-allLaghu (suc n) = guru-allLaghu n

allLaghuUnique : (n : ℕ) (p : Pattern)
               → varna p ≡ n → guruOf p ≡ 0 → p ≡ allLaghu n
allLaghuUnique zero    []          e g = refl
allLaghuUnique zero    (s ∷ p)     e g = ⊥rec (snotz e)
allLaghuUnique (suc n) []          e g = ⊥rec (znots e)
allLaghuUnique (suc n) (laghu ∷ p) e g =
  cong (laghu ∷_) (allLaghuUnique n p (injSuc e) g)
allLaghuUnique (suc n) (guru ∷ p)  e g = ⊥rec (snotz g)

chosenZeroIso : (n : ℕ) → Iso (Chosen n 0) Unit
fun (chosenZeroIso n) _ = tt
inv (chosenZeroIso n) _ = allLaghu n , varna-allLaghu n , guru-allLaghu n
rightInv (chosenZeroIso n) tt = refl
leftInv (chosenZeroIso n) (p , e , g) =
  Σ≡Prop isPropFib2 (sym (allLaghuUnique n p e g))

-- the n = 0 row past the diagonal is empty
chosenEmptyIso : (k : ℕ) → Iso (Chosen 0 (suc k)) (Fin 0)
fun (chosenEmptyIso k) ([] , e , g)     = ⊥rec (znots g)
fun (chosenEmptyIso k) (s ∷ p , e , g)  = ⊥rec (snotz e)
inv (chosenEmptyIso k) i = ⊥rec (¬-<-zero (i .snd))
rightInv (chosenEmptyIso k) i = ⊥rec (¬-<-zero (i .snd))
leftInv (chosenEmptyIso k) ([] , e , g)    = ⊥rec (znots g)
leftInv (chosenEmptyIso k) (s ∷ p , e , g) = ⊥rec (snotz e)

-- Chosen n k has exactly `meru n k` elements.
meruCount : (n k : ℕ) → Iso (Chosen n k) (Fin (meru n k))
meruCount zero zero       = compIso (chosenZeroIso zero) (equivToIso Unit≃Fin1)
meruCount zero (suc k)    = chosenEmptyIso k
meruCount (suc n) zero    = compIso (chosenZeroIso (suc n)) (equivToIso Unit≃Fin1)
meruCount (suc n) (suc k) =
  compIso (pascalIso n k)
    (compIso (⊎Iso (meruCount n (suc k)) (meruCount n k))
             (invIso (Fin+≅Fin⊎Fin (meru n (suc k)) (meru n k))))

-- THE THEOREM.  Any function that counts Chosen obeys Halyudha's rule.
pascal : (f : ℕ → ℕ → ℕ)
       → ((n k : ℕ) → Iso (Chosen n k) (Fin (f n k)))
       → (n k : ℕ) → f (suc n) (suc k) ≡ f n (suc k) + f n k
pascal f cnt n k = Fin-inj _ _ path
  where
    path : Fin (f (suc n) (suc k)) ≡ Fin (f n (suc k) + f n k)
    path =
        sym (isoToPath (cnt (suc n) (suc k)))
      ∙ isoToPath (pascalIso n k)
      ∙ isoToPath (⊎Iso (cnt n (suc k)) (cnt n k))
      ∙ sym (isoToPath (Fin+≅Fin⊎Fin (f n (suc k)) (f n k)))

meruRecurrence : (n k : ℕ) → meru (suc n) (suc k) ≡ meru n (suc k) + meru n k
meruRecurrence = pascal meru meruCount

------------------------------------------------------------------------
-- §5  Worked instances, as kernel-checked computations.
--
-- Each of these is a closed term of an identity type inhabited by
-- `refl`: the kernel evaluates both sides and finds them equal.  They
-- are exact symbolic computation, not measurement.
------------------------------------------------------------------------

-- Piṅgala's saṅkhyā: 2⁵ = 32 patterns in a five-syllable metre.
_ : count 5 ≡ 32
_ = refl

-- Virahka's list, and the duration-12 count that
-- notes/PROSODIC_RECURRENCE_LEARNER.md (absent from this repository) states in prose (233).
_ : matra 6 ≡ 13
_ = refl

_ : matra 12 ≡ 233
_ = refl

-- Halyudha's array: row 4 of the meru-prastra is 1 4 6 4 1.
_ : meru 4 0 ≡ 1
_ = refl

_ : meru 4 1 ≡ 4
_ = refl

_ : meru 4 2 ≡ 6
_ = refl

_ : meru 4 3 ≡ 4
_ = refl

_ : meru 4 4 ≡ 1
_ = refl

_ : meru 4 5 ≡ 0
_ = refl

-- naa on row 11 of the four-syllable prastra, and uddia back.
_ : nasta 4 11 ≡ guru ∷ guru ∷ laghu ∷ guru ∷ []
_ = refl

_ : uddista (guru ∷ guru ∷ laghu ∷ guru ∷ []) ≡ 11
_ = refl

-- that pattern lasts 2+2+1+2 = 7 mtr
_ : matraOf (guru ∷ guru ∷ laghu ∷ guru ∷ []) ≡ 7
_ = refl

------------------------------------------------------------------------
-- RELATION TO `Pingala`.
--
-- The two are not rivals.  `Pingala` now carries the →ℕ
-- equivalence; this carries वाक्, सङ्ख्या, नष्ट/उद्दिष्ट, मात्रा and the
-- meru with their counts.
------------------------------------------------------------------------

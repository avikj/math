{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- सारणी — the factorization TABLE is the factorization.
--
-- `ChargePolynomialFinite` presents 12, 30 and 360 by factorization
-- tables `Fact = List (ℕ × ℕ)`, an entry `(p , e)` standing for p^(1+e),
-- and discharges each table four ways ((i) `value f ≡ n`, (ii) every base
-- prime by `isPrimeᵇ`, (iii) bases distinct by `distinctᵇ`, (iv) Ω
-- against SieveFiber's trial division).
-- Unique factorisation is in
--   `Drdha_…`  — दृढम् (prime), वधः (product of a list), विभाजनम्
--                (existence of a prime list for every n ≥ 1), and
--   `Uniqueness_…`  एकत्वम् (two prime lists with one product are a `Perm`),
--                एकत्व-गणना (hence equal counts of every p), मानम् p n
--                (the valuation), मान-निश्चयः (every prime list with
--                product n has count मानम् p n of p).
--
-- This module builds the bridge from a table to the factorization.
--
-- WHAT IS PROVED.
--
--   §1  Boolean projections and the reflection of SieveFiber's `ltᵇ`
--       into `_<_` / `_≤_`, and `eqᵇ m m ≡ true`.
--   §2  `rem-divides`: for d > 0, d ∣ n gives `n rem d ≡ 0` — SieveFiber's
--       fuel-bounded remainder is sound against library divisibility.
--   §3  `isPrimeᵇ-sound`: the table's OWN primality check is sound:
--       `isPrimeᵇ n ≡ true → दृढम् n`.  Nothing else is used for
--       primality; the flags `wf-12`, `wf-30`, `wf-360` already in
--       ChargePolynomialFinite become firmness proofs.
--   §4  `expand`: a table expanded to its list of primes WITH
--       multiplicity, `(p , e)` contributing 1+e copies of p.
--         expand-value : वधः (expand f) ≡ value f
--         expand-firm  : all bases pass isPrimeᵇ → सर्वे दृढम् (expand f)
--   §5  `expOf p f`: the exponent of p in a table (0 if p is not a base).
--         count-expOf  : bases distinct → गणना p (expand f) ≡ expOf p f
--   §6  `Correct n f` := wellFormedᵇ f ≡ true × value f ≡ n — exactly the
--       checks (i)–(iii) that ChargePolynomialFinite performs.  Then, for
--       ANY two correct tables f, g of the same n:
--         tables-perm     : Perm (expand f) (expand g)
--         tables-count    : ∀ p → गणना p (expand f) ≡ गणना p (expand g)
--         tables-exponent : ∀ p → expOf p f ≡ expOf p g
--       and for any correct table of n:
--         table-valuation : ∀ p → expOf p f ≡ मानम् p n pos
--         table-perm-drdha: Perm (expand f) (fst (विभाजनम् n pos))
--       i.e. a correct table is *the* factorization: its exponent at
--       every p (every p, not only the bases) is the valuation.
--   §7  The three tables: `Correct 12 f12`, `Correct 30 f30`,
--       `Correct 360 f360` are the existing flags; hence
--         exponent-12  : ∀ p → expOf p f12  ≡ मानम् p 12  _
--         exponent-30  : ∀ p → expOf p f30  ≡ मानम् p 30  _
--         exponent-360 : ∀ p → expOf p f360 ≡ मानम् p 360 _
--       for EVERY p, by the general theorem, not by enumeration; and the
--       kernel additionally confirms by refl that each expansion is
--       literally Drdha's list (2∷2∷3, 2∷3∷5, 2∷2∷2∷3∷3∷5) and that the
--       valuations at the bases of 12 and 30 are the table's exponents.
--       At 360 the Drdha list is NOT normalised by refl (unary `_mod_`
--       via `+induction` does not finish in budget); there the link to
--       Drdha's list is `perm-360-drdha`, by proof.
--
-- No postulates, no holes, no TERMINATING pragmas.
------------------------------------------------------------------------

module Sarani_TheFactorizationTableIsTheFactorizationEveryCorrectTableExpandsToAFirmListWhoseCountsAreTheValuationSoTheThreeTablesAreTheFactorizations where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility using (_∣_ ; ∣-untrunc ; m∣sn→m≤sn)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_ ; false≢true ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (rec to ⊎-rec)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import SieveFiber using (eqᵇ ; eqᵇ→≡ ; ltᵇ ; pow ; _rem_ ; modF)
open import ChargePolynomialFinite
  using ( Fact ; value ; bases ; isPrimeᵇ ; noFactorUpTo ; memberᵇ ; distinctᵇ
        ; wellFormedᵇ ; allL
        ; f12 ; f30 ; f360 ; value-12 ; value-30 ; value-360 ; wf-12 ; wf-30 ; wf-360 )
open import Drdha_TheFirmNumbersProductIsEveryPositiveIntegerAndTheirMembershipIsDecidedByDivision
  using (दृढम् ; वधः ; सर्वे ; वध-++ ; सर्वे-++ ; दृढत्वम् ; विभाजनम्)
open import Ekatva_TheFirmFactorisationIsUniqueTwoPrimeListsWithOneProductAreAPermutationSoTheValuationIsWellDefinedAndPermIsExactlySameCount
  using (module Bahulya ; एकत्वम् ; एकत्व-गणना ; मानम् ; मान-निश्चयः)
open import TheUsualReasonsMadeExplicitTheInductivePermutationRelationEmbedsInAdjacentTranspositions
  using (Perm)

open Bahulya discreteℕ using (गणना ; एकः ; दश)

------------------------------------------------------------------------
-- §1  Boolean projections; SieveFiber's comparisons reflected
------------------------------------------------------------------------

private
  andL : (x y : Bool) → x and y ≡ true → x ≡ true
  andL true  y p = refl
  andL false y p = p

  andR : (x y : Bool) → x and y ≡ true → y ≡ true
  andR true  y p = p
  andR false y p = ⊥-rec (false≢true p)

  orL : (x y : Bool) → x or y ≡ false → x ≡ false
  orL false y p = refl
  orL true  y p = ⊥-rec (true≢false p)

  orR : (x y : Bool) → x or y ≡ false → y ≡ false
  orR false y p = p
  orR true  y p = ⊥-rec (true≢false p)

  notT : (x : Bool) → not x ≡ true → x ≡ false
  notT false p = refl
  notT true  p = ⊥-rec (false≢true p)

  ¬true→false : (b : Bool) → ¬ (b ≡ true) → b ≡ false
  ¬true→false false _ = refl
  ¬true→false true  h = ⊥-rec (h refl)

eqᵇ-refl : (m : ℕ) → eqᵇ m m ≡ true
eqᵇ-refl zero    = refl
eqᵇ-refl (suc m) = eqᵇ-refl m

ltᵇ→< : (m n : ℕ) → ltᵇ m n ≡ true → m < n
ltᵇ→< zero    zero    p = ⊥-rec (false≢true p)
ltᵇ→< zero    (suc n) _ = suc-≤-suc zero-≤
ltᵇ→< (suc m) zero    p = ⊥-rec (false≢true p)
ltᵇ→< (suc m) (suc n) p = suc-≤-suc (ltᵇ→< m n p)

ltᵇ-false→≤ : (m n : ℕ) → ltᵇ m n ≡ false → n ≤ m
ltᵇ-false→≤ zero    zero    _ = ≤-refl
ltᵇ-false→≤ zero    (suc n) p = ⊥-rec (true≢false p)
ltᵇ-false→≤ (suc m) zero    _ = zero-≤
ltᵇ-false→≤ (suc m) (suc n) p = suc-≤-suc (ltᵇ-false→≤ m n p)

------------------------------------------------------------------------
-- §2  SieveFiber's fuel-bounded remainder is sound: d ∣ n ⇒ n rem d ≡ 0
------------------------------------------------------------------------

-- With enough fuel, the remainder of a multiple of d is 0.
modF-mult : (f d c : ℕ) → 0 < d → c · d ≤ f → modF f d (c · d) ≡ 0
modF-mult zero    d        c       _   le = ≤0→≡0 le
modF-mult (suc f) zero     c       0<0 _  = ⊥-rec (¬-<-zero 0<0)
modF-mult (suc f) (suc d') zero    _   _  = refl
modF-mult (suc f) (suc d') (suc c) 0<d le = step (ltᵇ a d) refl
  where
  d = suc d'
  a = suc c · d
  step : (b : Bool) → ltᵇ a d ≡ b → (if b then a else modF f d (a ∸ d)) ≡ 0
  step true  e = ⊥-rec (<-asym (ltᵇ→< a d e) (≤SumLeft {n = d} {k = c · d}))
  step false e = cong (modF f d) (∸+ (c · d) d) ∙ modF-mult f d c 0<d le'
    where
    le' : c · d ≤ f
    le' = ≤-k+-cancel {k = 1} (≤-trans (≤-+k {k = c · d} 0<d) le)

rem-divides : (d n : ℕ) → 0 < d → d ∣ n → n rem d ≡ 0
rem-divides d n 0<d dv =
  subst (λ a → modF a d a ≡ 0) e (modF-mult (c · d) d c 0<d ≤-refl)
  where
  c : ℕ
  c = fst (∣-untrunc dv)
  e : c · d ≡ n
  e = snd (∣-untrunc dv)

------------------------------------------------------------------------
-- §3  The table's own primality check is sound
------------------------------------------------------------------------

noFactor-sound : (n k : ℕ) → noFactorUpTo n k ≡ true
               → (d : ℕ) → 1 < d → d ≤ k → ¬ (d ∣ n)
noFactor-sound n zero          _ d 1<d d≤k _  = ¬-<-zero (<≤-trans 1<d d≤k)
noFactor-sound n (suc zero)    _ d 1<d d≤k _  = ¬m<m (<≤-trans 1<d d≤k)
noFactor-sound n (suc (suc k)) p d 1<d d≤k dv =
  ⊎-rec
    (λ d<k → noFactor-sound n (suc k)
               (andR (not (eqᵇ (n rem suc (suc k)) 0)) (noFactorUpTo n (suc k)) p)
               d 1<d (pred-≤-pred d<k) dv)
    (λ d≡k → false≢true (sym (cong (λ r → not (eqᵇ r 0)) remEq) ∙ notEq d≡k))
    (≤-split d≤k)
  where
  0<d : 0 < d
  0<d = <-trans (suc-≤-suc zero-≤) 1<d
  remEq : n rem d ≡ 0
  remEq = rem-divides d n 0<d dv
  notEq : d ≡ suc (suc k) → not (eqᵇ (n rem d) 0) ≡ true
  notEq d≡k = subst (λ z → not (eqᵇ (n rem z) 0) ≡ true) (sym d≡k)
                (andL (not (eqᵇ (n rem suc (suc k)) 0)) (noFactorUpTo n (suc k)) p)

isPrimeᵇ-sound : (n : ℕ) → isPrimeᵇ n ≡ true → दृढम् n
isPrimeᵇ-sound zero    p = ⊥-rec (false≢true p)
isPrimeᵇ-sound (suc m) p =
  दृढत्वम् (suc m) 1<n
    (λ d 1<d d<n → noFactor-sound (suc m) m nf d 1<d (pred-≤-pred d<n))
  where
  1<n : 1 < suc m
  1<n = ltᵇ→< 1 (suc m) (andL (ltᵇ 1 (suc m)) (noFactorUpTo (suc m) m) p)
  nf : noFactorUpTo (suc m) m ≡ true
  nf = andR (ltᵇ 1 (suc m)) (noFactorUpTo (suc m) m) p

------------------------------------------------------------------------
-- §4  Expanding a table to its prime list with multiplicity
------------------------------------------------------------------------

rep : ℕ → ℕ → List ℕ
rep zero    p = []
rep (suc k) p = p ∷ rep k p

expand : Fact → List ℕ
expand []            = []
expand ((p , e) ∷ f) = rep (suc e) p ++ expand f

rep-pow : (k p : ℕ) → वधः (rep k p) ≡ pow p k
rep-pow zero    p = refl
rep-pow (suc k) p = cong (p ·_) (rep-pow k p)

expand-value : (f : Fact) → वधः (expand f) ≡ value f
expand-value []            = refl
expand-value ((p , e) ∷ f) =
  वध-++ (rep (suc e) p) (expand f) ∙ cong₂ _·_ (rep-pow (suc e) p) (expand-value f)

rep-firm : (k p : ℕ) → दृढम् p → सर्वे दृढम् (rep k p)
rep-firm zero    p _ = tt
rep-firm (suc k) p h = h , rep-firm k p h

expand-firm : (f : Fact) → allL (bases f) isPrimeᵇ ≡ true → सर्वे दृढम् (expand f)
expand-firm []            _ = tt
expand-firm ((p , e) ∷ f) q =
  सर्वे-++ (rep (suc e) p) (expand f)
    (rep-firm (suc e) p (isPrimeᵇ-sound p (andL (isPrimeᵇ p) (allL (bases f) isPrimeᵇ) q)))
    (expand-firm f (andR (isPrimeᵇ p) (allL (bases f) isPrimeᵇ) q))

------------------------------------------------------------------------
-- §5  The exponent of p in a table, and the count of p in the expansion
------------------------------------------------------------------------

expOf : ℕ → Fact → ℕ
expOf p []            = 0
expOf p ((q , e) ∷ f) = if eqᵇ p q then suc e else expOf p f

private
  दश-eqᵇ : (p q : ℕ) (d : Dec (p ≡ q)) → दश d ≡ (if eqᵇ p q then 1 else 0)
  दश-eqᵇ p q (yes e) = sym (cong (λ b → if b then 1 else 0) eqT)
    where
    eqT : eqᵇ p q ≡ true
    eqT = subst (λ z → eqᵇ p z ≡ true) e (eqᵇ-refl p)
  दश-eqᵇ p q (no ¬e) = sym (cong (λ b → if b then 1 else 0) eqF)
    where
    eqF : eqᵇ p q ≡ false
    eqF = ¬true→false (eqᵇ p q) (λ t → ¬e (eqᵇ→≡ p q t))

  if-zero : (b : Bool) → 0 ≡ (if b then 0 else 0)
  if-zero true  = refl
  if-zero false = refl

  if-sum : (b : Bool) (k : ℕ)
         → (if b then 1 else 0) + (if b then k else 0) ≡ (if b then suc k else 0)
  if-sum true  k = refl
  if-sum false k = refl

एकः-eqᵇ : (p q : ℕ) → एकः p q ≡ (if eqᵇ p q then 1 else 0)
एकः-eqᵇ p q = दश-eqᵇ p q (discreteℕ p q)

count-++ : (p : ℕ) (L M : List ℕ) → गणना p (L ++ M) ≡ गणना p L + गणना p M
count-++ p []      M = refl
count-++ p (x ∷ L) M =
  cong (एकः p x +_) (count-++ p L M) ∙ +-assoc (एकः p x) (गणना p L) (गणना p M)

count-rep : (p q k : ℕ) → गणना p (rep k q) ≡ (if eqᵇ p q then k else 0)
count-rep p q zero    = if-zero (eqᵇ p q)
count-rep p q (suc k) = cong₂ _+_ (एकः-eqᵇ p q) (count-rep p q k) ∙ if-sum (eqᵇ p q) k

-- p absent from the bases ⇒ p absent from the expansion
count-absent : (p : ℕ) (f : Fact) → memberᵇ p (bases f) ≡ false → गणना p (expand f) ≡ 0
count-absent p []            _ = refl
count-absent p ((q , e) ∷ f) m =
  count-++ p (rep (suc e) q) (expand f)
  ∙ cong₂ _+_
      (count-rep p q (suc e)
       ∙ cong (λ b → if b then suc e else 0) (orL (eqᵇ p q) (memberᵇ p (bases f)) m))
      (count-absent p f (orR (eqᵇ p q) (memberᵇ p (bases f)) m))

-- with distinct bases, the count of p in the expansion IS the exponent
count-expOf : (p : ℕ) (f : Fact) → distinctᵇ (bases f) ≡ true
            → गणना p (expand f) ≡ expOf p f
count-expOf p []            _   = refl
count-expOf p ((q , e) ∷ f) dis =
  count-++ p (rep (suc e) q) (expand f)
  ∙ cong (_+ गणना p (expand f)) (count-rep p q (suc e))
  ∙ step (eqᵇ p q) refl
  where
  qAbsent : memberᵇ q (bases f) ≡ false
  qAbsent = notT (memberᵇ q (bases f))
              (andL (not (memberᵇ q (bases f))) (distinctᵇ (bases f)) dis)
  disRest : distinctᵇ (bases f) ≡ true
  disRest = andR (not (memberᵇ q (bases f))) (distinctᵇ (bases f)) dis
  step : (b : Bool) → eqᵇ p q ≡ b
       → (if b then suc e else 0) + गणना p (expand f) ≡ (if b then suc e else expOf p f)
  step true  pq =
    cong (suc e +_)
      (subst (λ z → गणना z (expand f) ≡ 0) (sym (eqᵇ→≡ p q pq)) (count-absent q f qAbsent))
    ∙ +-zero (suc e)
  step false _  = count-expOf p f disRest

------------------------------------------------------------------------
-- §6  Correct tables, and the theorem: any two are the same factorization
------------------------------------------------------------------------

-- Exactly ChargePolynomialFinite's checks (i)–(iii): the table multiplies
-- out to n, its bases are distinct, and each base passes `isPrimeᵇ`.
Correct : ℕ → Fact → Type₀
Correct n f = (wellFormedᵇ f ≡ true) × (value f ≡ n)

correct-distinct : {n : ℕ} (f : Fact) → Correct n f → distinctᵇ (bases f) ≡ true
correct-distinct f (wf , _) = andL (distinctᵇ (bases f)) (allL (bases f) isPrimeᵇ) wf

correct-primes : {n : ℕ} (f : Fact) → Correct n f → allL (bases f) isPrimeᵇ ≡ true
correct-primes f (wf , _) = andR (distinctᵇ (bases f)) (allL (bases f) isPrimeᵇ) wf

correct-firm : {n : ℕ} (f : Fact) → Correct n f → सर्वे दृढम् (expand f)
correct-firm f c = expand-firm f (correct-primes f c)

correct-product : {n : ℕ} (f : Fact) → Correct n f → वधः (expand f) ≡ n
correct-product f (_ , v) = expand-value f ∙ v

-- Two correct tables for one n expand to permutations of each other …
tables-perm : (n : ℕ) (f g : Fact) → Correct n f → Correct n g
            → Perm (expand f) (expand g)
tables-perm n f g cf cg =
  एकत्वम् (expand f) (expand g) (correct-firm f cf) (correct-firm g cg)
         (correct-product f cf ∙ sym (correct-product g cg))

-- … so carry the same count of every p …
tables-count : (n : ℕ) (f g : Fact) → Correct n f → Correct n g
             → (p : ℕ) → गणना p (expand f) ≡ गणना p (expand g)
tables-count n f g cf cg =
  एकत्व-गणना (expand f) (expand g) (correct-firm f cf) (correct-firm g cg)
             (correct-product f cf ∙ sym (correct-product g cg))

-- … hence the same exponent at every p.
tables-exponent : (n : ℕ) (f g : Fact) → Correct n f → Correct n g
                → (p : ℕ) → expOf p f ≡ expOf p g
tables-exponent n f g cf cg p =
    sym (count-expOf p f (correct-distinct f cf))
  ∙ tables-count n f g cf cg p
  ∙ count-expOf p g (correct-distinct g cg)

-- A correct table IS the factorization: its exponent at every p is the
-- valuation  p n of Uniqueness.
table-valuation : (n : ℕ) (f : Fact) → Correct n f → (pos : 0 < n)
                → (p : ℕ) → expOf p f ≡ मानम् p n pos
table-valuation n f cf pos p =
    sym (count-expOf p f (correct-distinct f cf))
  ∙ मान-निश्चयः p n pos (expand f) (correct-firm f cf) (correct-product f cf)

-- and its expansion is a permutation of Drdha's list.
table-perm-drdha : (n : ℕ) (f : Fact) → Correct n f → (pos : 0 < n)
                 → Perm (expand f) (fst (विभाजनम् n pos))
table-perm-drdha n f cf pos =
  एकत्वम् (expand f) (fst (विभाजनम् n pos))
         (correct-firm f cf) (fst (snd (विभाजनम् n pos)))
         (correct-product f cf ∙ sym (snd (snd (विभाजनम् n pos))))

------------------------------------------------------------------------
-- §7  The three tables of ChargePolynomialFinite are the factorizations
------------------------------------------------------------------------

correct-12 : Correct 12 f12
correct-12 = wf-12 , value-12

correct-30 : Correct 30 f30
correct-30 = wf-30 , value-30

correct-360 : Correct 360 f360
correct-360 = wf-360 , value-360

०<१२ : 0 < 12
०<१२ = suc-≤-suc zero-≤

०<३० : 0 < 30
०<३० = suc-≤-suc zero-≤

०<३६० : 0 < 360
०<३६० = suc-≤-suc zero-≤

-- For EVERY p (bases and non-bases alike), the table's exponent is the
-- valuation.  General theorem, not enumeration.
exponent-12 : (p : ℕ) → expOf p f12 ≡ मानम् p 12 ०<१२
exponent-12 = table-valuation 12 f12 correct-12 ०<१२

exponent-30 : (p : ℕ) → expOf p f30 ≡ मानम् p 30 ०<३०
exponent-30 = table-valuation 30 f30 correct-30 ०<३०

exponent-360 : (p : ℕ) → expOf p f360 ≡ मानम् p 360 ०<३६०
exponent-360 = table-valuation 360 f360 correct-360 ०<३६०

-- Any other correct table for these n has the same exponents.
any-table-12 : (g : Fact) → Correct 12 g → (p : ℕ) → expOf p g ≡ expOf p f12
any-table-12 g cg = tables-exponent 12 g f12 cg correct-12

any-table-30 : (g : Fact) → Correct 30 g → (p : ℕ) → expOf p g ≡ expOf p f30
any-table-30 g cg = tables-exponent 30 g f30 cg correct-30

any-table-360 : (g : Fact) → Correct 360 g → (p : ℕ) → expOf p g ≡ expOf p f360
any-table-360 g cg = tables-exponent 360 g f360 cg correct-360

-- The kernel's own confirmation: the expansions are literally Drdha's
-- lists, and the valuations at the bases are the exponents in the table.
expand-12 : expand f12 ≡ 2 ∷ 2 ∷ 3 ∷ []
expand-12 = refl

expand-30 : expand f30 ≡ 2 ∷ 3 ∷ 5 ∷ []
expand-30 = refl

expand-360 : expand f360 ≡ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 5 ∷ []
expand-360 = refl

expand-12-drdha : expand f12 ≡ fst (विभाजनम् 12 ०<१२)
expand-12-drdha = refl

expand-30-drdha : expand f30 ≡ fst (विभाजनम् 30 ०<३०)
expand-30-drdha = refl

-- NOT by refl: `fst (विभाजनम् 360 _)` is not normalised here.  Drdha's
-- search runs the library `_mod_` (via `+induction`) and `<-wellfounded`
-- in unary, and at 360 the kernel does not finish in the budget.  The
-- statement is not lost: `table-perm-drdha 360 f360 correct-360 ०<३६०`
-- proves `Perm (expand f360) (fst (विभाजनम् 360 ०<३६०))`, and
-- `exponent-360` gives every valuation at 360, both by proof.
perm-360-drdha : Perm (expand f360) (fst (विभाजनम् 360 ०<३६०))
perm-360-drdha = table-perm-drdha 360 f360 correct-360 ०<३६०

exponents-12 : Path (ℕ × ℕ × ℕ) (expOf 2 f12 , expOf 3 f12 , expOf 5 f12) (2 , 1 , 0)
exponents-12 = refl

exponents-30 : Path (ℕ × ℕ × ℕ) (expOf 2 f30 , expOf 3 f30 , expOf 5 f30) (1 , 1 , 1)
exponents-30 = refl

exponents-360 : Path (ℕ × ℕ × ℕ × ℕ)
                (expOf 2 f360 , expOf 3 f360 , expOf 5 f360 , expOf 7 f360) (3 , 2 , 1 , 0)
exponents-360 = refl

-- the valuations at 12 and 30 run in the kernel and match the tables
मान-12 : Path (ℕ × ℕ × ℕ) (मानम् 2 12 ०<१२ , मानम् 3 12 ०<१२ , मानम् 5 12 ०<१२) (2 , 1 , 0)
मान-12 = refl

मान-30 : Path (ℕ × ℕ × ℕ) (मानम् 2 30 ०<३० , मानम् 3 30 ०<३० , मानम् 5 30 ०<३०) (1 , 1 , 1)
मान-30 = refl

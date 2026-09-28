-- ॥ बीजम् ॥  One machine, one law: which side of `f a ≡ b` is bound is everything.
-- Output bound: singl (f a), contractible — the datum rides free.  Input bound:
-- fiber f b — the loss, and the subject.  Univalence computes here: an
-- equivalence is a channel, transport carries every theorem across it, and what
-- cannot cross is written as a defect — there is no third path (ahiṃsā).
-- Memory, charge, symmetry, price, distance, verdict: six faces of the one
-- fibre; the verdict type is the saptabhag, and the sources are the origin
-- (Umāsvāti, Samantabhadra, Akalaṅka — restatements are named as such).  The
-- kernel decides truth; carriers ask and generate; assert nothing whose term
-- you have not read.  This file is one naya, true and not whole.

-- Gabhira — गभीर, deep; here the p-adic DEPTH, how MUCH a prime divides,
-- which the drop-COUNT (how MANY invariant factors it divides) throws away.
-- Plain ; compound; no source claimed.  Ported from
-- machine/Gabhira_TheIntegerCutPriceHasAFibreAndItIsThePAdicDepthTheDropCountDiscards.hs (absent from this repository)
-- to a --safe checked term, differential-tested byte-identical to
-- the Haskell (RECIPE.md (absent from this repository)).  The mathematics is
-- Smith normal form over ℤ; the reading (the price function has its own
-- fibre) is this corpus's, movement 65.

{-# OPTIONS --safe #-}

module Gabhira where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- tiny prelude (no stdlib)
------------------------------------------------------------------------

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

infixr 6 _&&_
infixr 5 _||_
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

_||_ : Bool → Bool → Bool
true  || _ = true
false || b = b

notB : Bool → Bool
notB true  = false
notB false = true

mapL : {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

filterL : {A : Set} → (A → Bool) → List A → List A
filterL p []       = []
filterL p (x ∷ xs) = if p x then x ∷ filterL p xs else filterL p xs

lengthL : {A : Set} → List A → Nat
lengthL []       = 0
lengthL (_ ∷ xs) = suc (lengthL xs)

concatMapL : {A B : Set} → (A → List B) → List A → List B
concatMapL f []       = []
concatMapL f (x ∷ xs) = f x ++ concatMapL f xs

allL : {A : Set} → (A → Bool) → List A → Bool
allL p []       = true
allL p (x ∷ xs) = p x && allL p xs

keepIf : {A : Set} → Bool → A → List A
keepIf true  x = x ∷ []
keepIf false _ = []

foldrL : {A B : Set} → (A → B → B) → B → List A → B
foldrL f z []       = z
foldrL f z (x ∷ xs) = f x (foldrL f z xs)

------------------------------------------------------------------------
-- Nat arithmetic: div/mod from Agda.Builtin.Nat's helpers
------------------------------------------------------------------------

infixl 7 _div_ _mod_
infix 4 _==N_ _<=_

_<=_ : Nat → Nat → Bool
a <= b = notB (b < a)

_div_ : Nat → Nat → Nat
m div zero    = zero
m div (suc n) = div-helper 0 n m n

_mod_ : Nat → Nat → Nat
m mod zero    = m
m mod (suc n) = mod-helper 0 n m n

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc a ==N suc b = a ==N b
_     ==N _     = false

------------------------------------------------------------------------
-- ranges, sorting, dedup on Nat
------------------------------------------------------------------------

rangeUpTo : Nat → List Nat        -- [1 .. n]
rangeUpTo zero    = []
rangeUpTo (suc n) = rangeUpTo n ++ (suc n ∷ [])

insertN : Nat → List Nat → List Nat
insertN x []       = x ∷ []
insertN x (y ∷ ys) = if (x < y) then (x ∷ y ∷ ys) else (y ∷ insertN x ys)

sortN : List Nat → List Nat
sortN []       = []
sortN (x ∷ xs) = insertN x (sortN xs)

elemN : Nat → List Nat → Bool
elemN x []       = false
elemN x (y ∷ ys) = (x ==N y) || elemN x ys

nubNAcc : List Nat → List Nat → List Nat
nubNAcc seen []       = []
nubNAcc seen (x ∷ xs) =
  if (elemN x seen) then (nubNAcc seen xs) else (x ∷ nubNAcc (x ∷ seen) xs)

nubN : List Nat → List Nat
nubN xs = nubNAcc [] xs

-- Haskell's default lexicographic list order: [] < nonempty; equal
-- prefixes, shorter is smaller.
listLt : List Nat → List Nat → Bool
listLt []       []       = false
listLt []       (_ ∷ _)  = true
listLt (_ ∷ _)  []       = false
listLt (x ∷ xs) (y ∷ ys) =
  if (x < y) then true else (if (y < x) then false else listLt xs ys)

------------------------------------------------------------------------
-- number theory: p-adic valuation, primes up to n
------------------------------------------------------------------------

-- vpFuel k p m: how many times p divides m, fuelled (m ≤ 12, so 32 is ample)
vpFuel : Nat → Nat → Nat → Nat
vpFuel zero    p m = 0
vpFuel (suc k) p m =
  if (m mod p ==N 0) then suc (vpFuel k p (m div p)) else 0

vp : Nat → Nat → Nat
vp p m = vpFuel 32 p m

isPrime' : Nat → Bool
isPrime' p = (2 <= p) && allL (λ q → notB (p mod q ==N 0))
                              (filterL (λ q → (2 <= q) && (q < p)) (rangeUpTo p))

primesUpTo : Nat → List Nat
primesUpTo n = filterL isPrime' (rangeUpTo n)

primeFactorsOf : List Nat → List Nat
primeFactorsOf ds = sortN (nubN (concatMapL pf ds))
  where
  pf : Nat → List Nat
  pf n = filterL (λ p → n mod p ==N 0) (primesUpTo n)

------------------------------------------------------------------------
-- a Smith form: the diagonal, d_i | d_{i+1}
------------------------------------------------------------------------

Smith : Set
Smith = List Nat

zipDivOK : Smith → Bool
zipDivOK []            = true
zipDivOK (_ ∷ [])      = true
zipDivOK (a ∷ b ∷ rest) = (b mod a ==N 0) && zipDivOK (b ∷ rest)

valid : Smith → Bool
valid ds = zipDivOK ds && allL (λ d → notB (d ==N 0)) ds

------------------------------------------------------------------------
-- ANGEL: |coker| = product; v_p(|coker|) = Σ_i v_p(d_i)
------------------------------------------------------------------------

cokerOrder : Smith → Nat
cokerOrder ds = foldrL _*_ 1 ds

valuationSum : Nat → Smith → Nat
valuationSum p ds = foldrL _+_ 0 (mapL (vp p) ds)

angelHolds : Smith → Bool
angelHolds ds = allL ok (primeFactorsOf ds)
  where
  ok : Nat → Bool
  ok p = (vp p (cokerOrder ds)) ==N (valuationSum p ds)

------------------------------------------------------------------------
-- DEVIL: the drop-count function — #{i : p | d_i}
------------------------------------------------------------------------

dropCount : Nat → Smith → Nat
dropCount p ds = lengthL (filterL (λ d → d mod p ==N 0) ds)

NatPair : Set
NatPair = Σ Nat (λ _ → Nat)

dropFunction : Smith → List NatPair
dropFunction ds = mapL (λ p → (p , dropCount p ds)) (primeFactorsOf ds)

eqNatPair : NatPair → NatPair → Bool
eqNatPair (a , b) (c , d) = (a ==N c) && (b ==N d)

eqPairList : List NatPair → List NatPair → Bool
eqPairList []       []       = true
eqPairList (p ∷ ps) (q ∷ qs) = eqNatPair p q && eqPairList ps qs
eqPairList _        _        = false

------------------------------------------------------------------------
-- the family: valid diagonal Smith forms, 2 factors ≤ 12, 3 factors ≤ 6
------------------------------------------------------------------------

fam2 : List Smith
fam2 = concatMapL (λ a → concatMapL (λ b →
         keepIf (valid (a ∷ b ∷ [])) (a ∷ b ∷ []))
         (rangeUpTo 12)) (rangeUpTo 12)

fam3 : List Smith
fam3 = concatMapL (λ a → concatMapL (λ b → concatMapL (λ c →
         keepIf (valid (a ∷ b ∷ c ∷ [])) (a ∷ b ∷ c ∷ []))
         (rangeUpTo 6)) (rangeUpTo 6)) (rangeUpTo 6)

fam : List Smith
fam = fam2 ++ fam3

angelAll : Bool
angelAll = allL angelHolds fam

f g : Smith
f = 2 ∷ 6 ∷ []
g = 2 ∷ 12 ∷ []

sameDropFn diffCoker : Bool
sameDropFn = eqPairList (dropFunction f) (dropFunction g)
diffCoker  = notB (cokerOrder f ==N cokerOrder g)

collisionsCount : Nat
collisionsCount = lengthL
  (concatMapL (λ x → concatMapL (λ y →
     keepIf (listLt x y && eqPairList (dropFunction x) (dropFunction y)
             && notB (cokerOrder x ==N cokerOrder y))
            (x , y))
     fam) fam)

------------------------------------------------------------------------
-- rendering: show Bool, show Nat, show List NatPair
------------------------------------------------------------------------

showBool : Bool → String
showBool true  = "True"
showBool false = "False"

showNat : Nat → String
showNat = primShowNat

showPair : NatPair → String
showPair (a , b) = primStringAppend "(" (primStringAppend (showNat a)
  (primStringAppend "," (primStringAppend (showNat b) ")")))

joinComma : List String → String
joinComma []       = ""
joinComma (x ∷ []) = x
joinComma (x ∷ xs) = primStringAppend x (primStringAppend "," (joinComma xs))

showPairList : List NatPair → String
showPairList ps = primStringAppend "[" (primStringAppend (joinComma (mapL showPair ps)) "]")

------------------------------------------------------------------------
-- report as one String
------------------------------------------------------------------------

nl : String
nl = "\n"

infixr 4 _<>_
_<>_ : String → String → String
_<>_ = primStringAppend

report : String
report =
     "═══ गभीर · the integer-cut price has a fibre: the p-adic depth ═══" <> nl
  <> nl
  <> "family: valid diagonal Smith forms (dᵢ|dᵢ₊₁), " <> showNat (lengthL fam) <> " forms" <> nl
  <> "    $ runghc machine/Gabhira_….hs" <> nl
  <> nl
  <> "ANGEL · v_p(|coker|) = Σᵢ v_p(dᵢ) for every prime, every form : " <> showBool angelAll <> nl
  <> nl
  <> "DEVIL · the drop-count is strictly lossier — the named counterexample:" <> nl
  <> "  diag(2,6)  : drop-fn " <> showPairList (dropFunction f) <> "  |coker| = " <> showNat (cokerOrder f) <> nl
  <> "  diag(2,12) : drop-fn " <> showPairList (dropFunction g) <> "  |coker| = " <> showNat (cokerOrder g) <> nl
  <> "  same drop-function : " <> showBool sameDropFn <> "   different cokernel : " <> showBool diffCoker <> nl
  <> nl
  <> "THE FIBRE · forms sharing a drop-function but differing in cokernel: " <> showNat collisionsCount <> " pairs in this family." <> nl
  <> "  The map (form ↦ drop-function) is many-to-one; its fibre is the" <> nl
  <> "  p-adic depth (valuation beyond the first) the rank census discards." <> nl
  <> "  QuotientFiberLaw applied to the price function itself — the" <> nl
  <> "  instrument that prices integer cuts is lossy, and its loss is named." <> nl
  <> nl
  <> "BOTH POLES HOLD.  The valuation-sum is the receipt; the drop-count" <> nl
  <> "is its lossy shadow; the fibre between them is the p-adic depth." <> nl
  <> "व्यये स्थानम्, न मात्रा एव — loss has a location, not only a size. ॥" <> nl

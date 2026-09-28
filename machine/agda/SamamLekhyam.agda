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

{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- समं लेख्यम् — ported term-for-term from
-- machine/SamamLekhyam_TheHilbertProductBalancesAtEveryPlaceAndDroppingTheInfiniteColumnBreaksExactlyTheDoublyNegativePairs.hs (absent from this repository)
-- into --safe Agda, compiled by the kernel's own backend (MAlonzo/GHC).
-- See that file's header for the mathematics, sources and what is/isn't
-- claimed.  Exact integer arithmetic throughout: Integer is modelled here
-- as sign×magnitude (Z below) with hand-rolled floor div/mod matching
-- Haskell's `div`/`mod` semantics for a positive divisor, since only
-- positive moduli (2, odd primes) are ever divided by in this program.
------------------------------------------------------------------------

module SamamLekhyam where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- tiny prelude
------------------------------------------------------------------------

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

_==B_ : Bool → Bool → Bool
true  ==B true  = true
false ==B false = true
_     ==B _     = false

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

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

revApp : {A : Set} → List A → List A → List A
revApp []       acc = acc
revApp (x ∷ xs) acc = revApp xs (x ∷ acc)

reverseL : {A : Set} → List A → List A
reverseL xs = revApp xs []

takeL : {A : Set} → Nat → List A → List A
takeL zero    _        = []
takeL (suc n) []       = []
takeL (suc n) (x ∷ xs) = x ∷ takeL n xs

tailL : {A : Set} → List A → List A
tailL []       = []
tailL (_ ∷ xs) = xs

------------------------------------------------------------------------
-- Nat comparisons, monus, and fuel-bounded div/mod
------------------------------------------------------------------------

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc a ==N suc b = a ==N b
_     ==N _     = false

_<=N_ : Nat → Nat → Bool
zero  <=N _     = true
suc _ <=N zero  = false
suc a <=N suc b = a <=N b

_<N_ : Nat → Nat → Bool
a <N b = suc a <=N b

infixl 6 _∸_
_∸_ : Nat → Nat → Nat
zero  ∸ _     = zero
suc n ∸ zero  = suc n
suc n ∸ suc m = n ∸ m

natDivModF : Nat → Nat → Nat → Σ Nat (λ _ → Nat)
natDivModF zero    n d = (0 , n)
natDivModF (suc f) n d with n <N d
... | true  = (0 , n)
... | false = let r = natDivModF f (n ∸ d) d in (suc (fst r) , snd r)

natDivMod : Nat → Nat → Σ Nat (λ _ → Nat)
natDivMod n d = natDivModF (suc n) n d

divN : Nat → Nat → Nat
divN n d = fst (natDivMod n d)

modN : Nat → Nat → Nat
modN n d = snd (natDivMod n d)

evenN : Nat → Bool
evenN zero            = true
evenN (suc zero)      = false
evenN (suc (suc n))   = evenN n

oddN : Nat → Bool
oddN n = notB (evenN n)

halfN : Nat → Nat
halfN zero            = zero
halfN (suc zero)      = zero
halfN (suc (suc n))   = suc (halfN n)

predN : Nat → Nat
predN zero    = zero
predN (suc n) = n

------------------------------------------------------------------------
-- Z : the integers, as sign × magnitude, canonical (mag 0 ⇒ sign false)
------------------------------------------------------------------------

record Z : Set where
  constructor mkZ
  field
    negS : Bool
    magN : Nat
open Z

mkZcanon : Bool → Nat → Z
mkZcanon s zero = mkZ false zero
mkZcanon s m    = mkZ s m

zeroZ negOneZ oneZ : Z
zeroZ   = mkZ false 0
negOneZ = mkZ true 1
oneZ    = mkZ false 1

fromNat : Nat → Z
fromNat n = mkZ false n

isNegZ : Z → Bool
isNegZ z = negS z

eqZ : Z → Z → Bool
eqZ a b = (negS a ==B negS b) && (magN a ==N magN b)

xorB : Bool → Bool → Bool
xorB true  b = notB b
xorB false b = b

negZ : Z → Z
negZ z = mkZcanon (notB (negS z)) (magN z)

addZ : Z → Z → Z
addZ (mkZ s1 m1) (mkZ s2 m2) =
  if s1 ==B s2
  then mkZcanon s1 (m1 + m2)
  else if m2 <=N m1
       then mkZcanon s1 (m1 ∸ m2)
       else mkZcanon s2 (m2 ∸ m1)

subZ : Z → Z → Z
subZ a b = addZ a (negZ b)

mulZ : Z → Z → Z
mulZ (mkZ s1 m1) (mkZ s2 m2) = mkZcanon (xorB s1 s2) (m1 * m2)

-- floor mod by a positive Nat modulus, result in [0,d)
modZ : Z → Nat → Nat
modZ (mkZ false m) d = modN m d
modZ (mkZ true  m) d =
  let r = modN m d
  in if r ==N 0 then 0 else d ∸ r

-- floor div by a positive Nat modulus
divZ : Z → Nat → Z
divZ (mkZ false m) d = mkZcanon false (divN m d)
divZ (mkZ true  m) d =
  let r = natDivMod m d
      q = fst r
      s = snd r
  in if s ==N 0 then mkZcanon true q else mkZcanon true (suc q)

showZ : Z → String
showZ (mkZ s m) = if s then primStringAppend "-" (primShowNat m) else primShowNat m

------------------------------------------------------------------------
-- range builders
------------------------------------------------------------------------

upToDesc : Nat → List Nat   -- [n, n-1, ..., 1]
upToDesc zero    = []
upToDesc (suc n) = suc n ∷ upToDesc n

upToAsc : Nat → List Nat    -- [1, 2, ..., n]
upToAsc n = reverseL (upToDesc n)

------------------------------------------------------------------------
-- exact modular arithmetic (mirrors the Haskell exactly)
------------------------------------------------------------------------

powmodF : Nat → Z → Nat → Nat → Nat
powmodF zero    b e m = 1
powmodF (suc f) b e m with e ==N 0
... | true  = 1
... | false with evenN e
...   | true  = let h = powmodF f b (halfN e) m in modN (h * h) m
...   | false = modN ((modZ b m) * powmodF f b (predN e) m) m

powmod : Z → Nat → Nat → Nat
powmod b e m = powmodF e b e m

-- Legendre symbol (u|p) for odd prime p, by Euler's criterion.
legendre : Z → Nat → Z
legendre u p =
  let r = powmod u (halfN (predN p)) p
  in if r ==N (predN p) then negOneZ else fromNat r

-- p-adic valuation and unit part: m = p^k · u, p ∤ u.
valUnitF : Nat → Nat → Nat → Z → Σ Nat (λ _ → Z)
valUnitF zero    p k m = (k , m)
valUnitF (suc f) p k m with modZ m p ==N 0
... | true  = valUnitF f p (suc k) (divZ m p)
... | false = (k , m)

valUnit : Nat → Z → Σ Nat (λ _ → Z)
valUnit p m0 = valUnitF (suc (magN m0)) p 0 m0

epsO : Z → Nat
epsO u = if modZ u 4 ==N 1 then 0 else 1

omg : Z → Nat
omg u = let r = modZ u 8 in if (r ==N 1) || (r ==N 7) then 0 else 1

sgnPow : Z → Nat → Z         -- (±1)^k, s a sign (as legendre's result)
sgnPow s k = if oddN k && eqZ s negOneZ then negOneZ else oneZ

------------------------------------------------------------------------
-- the local columns
------------------------------------------------------------------------

hilbertInf : Z → Z → Z
hilbertInf a b = if isNegZ a && isNegZ b then negOneZ else oneZ

hilbert2 : Z → Z → Z
hilbert2 a b =
  let ru = valUnit 2 a
      al = fst ru
      u  = snd ru
      rv = valUnit 2 b
      be = fst rv
      v  = snd rv
      ex = epsO u * epsO v + al * omg v + be * omg u
  in if oddN ex then negOneZ else oneZ

hilbertOdd : Nat → Z → Z → Z
hilbertOdd p a b =
  let ru = valUnit p a
      al = fst ru
      u  = snd ru
      rv = valUnit p b
      be = fst rv
      v  = snd rv
      e  = halfN (predN p)
      s0 = if oddN (al * be * e) then negOneZ else oneZ
  in mulZ (mulZ s0 (sgnPow (legendre u p) be)) (sgnPow (legendre v p) al)

------------------------------------------------------------------------
-- odd prime divisors of |n0|
------------------------------------------------------------------------

stripTwosF : Nat → Nat → Nat
stripTwosF zero    m = m
stripTwosF (suc f) m = if (notB (m ==N 0)) && evenN m then stripTwosF f (halfN m) else m

stripF : Nat → Nat → Nat → Nat
stripF zero    p k = k
stripF (suc f) p k = if modN k p ==N 0 then stripF f p (divN k p) else k

goOddPDF : Nat → Nat → Nat → List Nat
goOddPDF zero    p m = []
goOddPDF (suc f) p m =
  if m ==N 1 then []
  else if m <N (p * p) then m ∷ []
  else if modN m p ==N 0 then p ∷ goOddPDF f p (stripF (suc m) p m)
  else goOddPDF f (p + 2) m

oddPrimeDivisors : Z → List Nat
oddPrimeDivisors n0 =
  let a = magN n0
  in goOddPDF (suc a) 3 (stripTwosF (suc a) a)

------------------------------------------------------------------------
-- the ledger, and the balance
------------------------------------------------------------------------

ledger : Z → Z → List (Σ String (λ _ → Z))
ledger a b =
  ("infinity" , hilbertInf a b)
  ∷ ("2" , hilbert2 a b)
  ∷ mapL (λ p → (primShowNat p , hilbertOdd p a b)) (oddPrimeDivisors (mulZ a b))

productZ : List Z → Z
productZ []       = oneZ
productZ (z ∷ zs) = mulZ z (productZ zs)

balance : Z → Z → Z
balance a b = productZ (mapL snd (ledger a b))

------------------------------------------------------------------------
-- primes up to n (sieve, fuel-bounded)
------------------------------------------------------------------------

rangeFrom2 : Nat → List Nat
rangeFrom2 n = tailL (upToAsc n)

sieveF : Nat → List Nat → List Nat
sieveF zero    xs       = xs
sieveF (suc f) []       = []
sieveF (suc f) (p ∷ xs) = p ∷ sieveF f (filterL (λ x → notB (modN x p ==N 0)) xs)

primesTo : Nat → List Nat
primesTo n = sieveF (lengthL (rangeFrom2 n)) (rangeFrom2 n)

------------------------------------------------------------------------
-- pairs over the box |a|,|b| ≤ nBox, a,b ≠ 0
------------------------------------------------------------------------

nBox : Nat
nBox = 60

allVals : List Z
allVals = mapL (λ n → mkZ true n) (upToDesc nBox) ++ mapL (λ n → mkZ false n) (upToAsc nBox)

pairs : List (Σ Z (λ _ → Z))
pairs = concatMapL (λ a → mapL (λ b → (a , b)) allVals) allVals

------------------------------------------------------------------------
-- १ · the balance
------------------------------------------------------------------------

unbalanced : List (Σ Z (λ _ → Z))
unbalanced = filterL (λ pr → notB (eqZ (balance (fst pr) (snd pr)) oneZ)) pairs

------------------------------------------------------------------------
-- २ · drop the infinite column
------------------------------------------------------------------------

finiteOnly : Σ Z (λ _ → Z) → Z
finiteOnly pr =
  productZ (mapL snd (filterL (λ vp → notB (primStringEquality (fst vp) "infinity")) (ledger (fst pr) (snd pr))))

brokenNoInf : Nat
brokenNoInf = lengthL (filterL (λ pr → notB (eqZ (finiteOnly pr) oneZ)) pairs)

doublyNegative : Nat
doublyNegative = lengthL (filterL (λ pr → isNegZ (fst pr) && isNegZ (snd pr)) pairs)

------------------------------------------------------------------------
-- ३ · drop the column at 2
------------------------------------------------------------------------

no2 : Σ Z (λ _ → Z) → Z
no2 pr =
  productZ (mapL snd (filterL (λ vp → notB (primStringEquality (fst vp) "2")) (ledger (fst pr) (snd pr))))

brokenNo2 : Nat
brokenNo2 = lengthL (filterL (λ pr → notB (eqZ (no2 pr) oneZ)) pairs)

------------------------------------------------------------------------
-- ४ · the shadow — Gauss extracted back out
------------------------------------------------------------------------

ops : List Nat
ops = tailL (primesTo 97)

emptyPQ : List (Σ Nat (λ _ → Nat))
emptyPQ = []

singPQ : Nat → Nat → List (Σ Nat (λ _ → Nat))
singPQ p q = (p , q) ∷ []

recipCheck : Nat → Nat → List (Σ Nat (λ _ → Nat))
recipCheck p q =
  let lhs = mulZ (legendre (fromNat p) q) (legendre (fromNat q) p)
      rhs = if oddN (epsO (fromNat p) * epsO (fromNat q)) then negOneZ else oneZ
  in if eqZ lhs rhs then emptyPQ else singPQ p q

recipBad : List (Σ Nat (λ _ → Nat))
recipBad = concatMapL (λ p → concatMapL (λ q → if p <N q then recipCheck p q else emptyPQ) ops) ops

supCheck : Nat → Bool
supCheck p =
  let c1 = notB (eqZ (legendre negOneZ p) (if epsO (fromNat p) ==N 1 then negOneZ else oneZ))
      c2 = notB (eqZ (legendre (fromNat 2) p) (if omg (fromNat p) ==N 1 then negOneZ else oneZ))
  in c1 || c2

supBad : List Nat
supBad = filterL supCheck ops

------------------------------------------------------------------------
-- report as one String
------------------------------------------------------------------------

nl : String
nl = "\n"

_+s_ : String → String → String
_+s_ = primStringAppend

infixr 5 _+s_

rowLine : Σ String (λ _ → Z) → String
rowLine vp = "      place " +s fst vp +s " : " +s showZ (snd vp) +s nl

joinRows : List (Σ String (λ _ → Z)) → String
joinRows []       = ""
joinRows (r ∷ rs) = rowLine r +s joinRows rs

receiptA receiptB : Z
receiptA = mkZ true 7
receiptB = mkZ true 15

allHold : Bool
allHold = (lengthL unbalanced ==N 0) && (brokenNoInf ==N doublyNegative)
          && (lengthL recipBad ==N 0) && (lengthL supBad ==N 0)

finalBlock : Bool → String
finalBlock true =
  "ALL CHECKS HOLD.  Loss is always local; globally the books" +s nl
  +s "have always balanced; and the column physics forgets is the" +s nl
  +s "one that pays for all the others.   समं लेख्यम् ॥" +s nl
finalBlock false = "A CHECK FAILED — the failing objects are the finding:" +s nl

report : String
report =
  "═══ समं लेख्यम् · the Hilbert product balances at every place ═══" +s nl
  +s nl
  +s "१ · THE BALANCE over |a|,|b| <= " +s primShowNat nBox
     +s ": " +s primShowNat (lengthL pairs) +s " pairs, "
     +s primShowNat (lengthL unbalanced) +s " unbalanced." +s nl
  +s "    (every pair's product over infinity, 2, and the odd primes" +s nl
  +s "     dividing ab is exactly 1 — the total was always zero.)" +s nl
  +s nl
  +s "    one row shown whole, the receipt of (-7,-15):" +s nl
  +s joinRows (ledger receiptA receiptB)
  +s "      product      : " +s showZ (balance receiptA receiptB) +s nl
  +s nl
  +s "२ · SINGLE-ENTRY CONTROL — the infinite column dropped: "
     +s primShowNat brokenNoInf +s " pairs break; pairs with a<0 and b<0: "
     +s primShowNat doublyNegative +s "."
     +s (if brokenNoInf ==N doublyNegative
         then "  EQUAL: the archimedean column carries exactly the joint-sign charge and nothing else."
         else "  NOT EQUAL — a formula above is wrong.")
     +s nl
  +s nl
  +s "३ · FIRST-VEIL CONTROL — the column at 2 dropped: "
     +s primShowNat brokenNo2 +s " of " +s primShowNat (lengthL pairs)
     +s " pairs break.  That is how much of this box's ledger the" +s nl
  +s "    smallest prime carries; counted, not estimated." +s nl
  +s nl
  +s "४ · THE SHADOW — Gauss extracted back out: all odd prime pairs"
     +s " p<q<=97: " +s primShowNat (lengthL recipBad) +s " violations;"
     +s " supplements (-1|p),(2|p): " +s primShowNat (lengthL supBad)
     +s " violations." +s nl
  +s nl
  +s finalBlock allHold

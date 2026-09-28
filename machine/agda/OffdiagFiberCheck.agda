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
-- OffdiagFiberCheck — exact exhaustive verification of the fiber statement
-- in notes/OFFDIAGONAL_NO_GO_FIBER.md (absent from this repository).
--
-- Ported term-for-term from machine/OffdiagFiberCheck.hs (absent from this repository) into --safe Agda,
-- compiled by the kernel's own backend (MAlonzo/GHC).  All lists involved
-- are of fixed, small, statically-known size (≤ 16 elements), so every
-- recursion below is structural on its argument list — no fuel needed.
------------------------------------------------------------------------

module OffdiagFiberCheck where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- tiny prelude
------------------------------------------------------------------------

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

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

_<=_ : Nat → Nat → Bool
zero  <= _     = true
suc _ <= zero  = false
suc a <= suc b = a <= b

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc a ==N suc b = a ==N b
_     ==N _     = false

minN : Nat → Nat → Nat
minN a b = if a <= b then a else b

------------------------------------------------------------------------
-- list-of-Nat equality / lexicographic order (for canon / dedup)
------------------------------------------------------------------------

eqLN : List Nat → List Nat → Bool
eqLN []       []       = true
eqLN (a ∷ as) (b ∷ bs) = (a ==N b) && eqLN as bs
eqLN _        _        = false

-- lexicographic ≤, matching Haskell's derived Ord for [Int]
leLN : List Nat → List Nat → Bool
leLN []       []       = true
leLN []       (_ ∷ _)  = true
leLN (_ ∷ _)  []       = false
leLN (a ∷ as) (b ∷ bs) with a ==N b
... | true  = leLN as bs
... | false = a <= b

------------------------------------------------------------------------
-- sort (insertion sort, ascending) on List Nat
------------------------------------------------------------------------

insertN : Nat → List Nat → List Nat
insertN x []       = x ∷ []
insertN x (y ∷ ys) = if x <= y then (x ∷ (y ∷ ys)) else (y ∷ insertN x ys)

sortN : List Nat → List Nat
sortN []       = []
sortN (x ∷ xs) = insertN x (sortN xs)

------------------------------------------------------------------------
-- indexed values: (index, value)
------------------------------------------------------------------------

IV : Set
IV = Σ Nat (λ _ → Nat)

zipIdx0 : Nat → List Nat → List IV
zipIdx0 i []       = []
zipIdx0 i (x ∷ xs) = (i , x) ∷ zipIdx0 (suc i) xs

zipIdx : List Nat → List IV
zipIdx = zipIdx0 0

elemN : Nat → List Nat → Bool
elemN x []       = false
elemN x (y ∷ ys) = (x ==N y) || elemN x ys

notElemN : Nat → List Nat → Bool
notElemN x xs = notB (elemN x xs)

------------------------------------------------------------------------
-- offdiag: sorted list of pairwise sums a_i+a_j, i<j
------------------------------------------------------------------------

-- sums of x's value against every later element's value in a list that is
-- already in increasing-index order (as zipIdx produces): so simply pair x
-- against every element of the remaining tail.
sumsWithLater : IV → List IV → List Nat
sumsWithLater (i , a) []             = []
sumsWithLater (i , a) ((j , b) ∷ ps) = (a + b) ∷ sumsWithLater (i , a) ps

allSums : List IV → List Nat
allSums []       = []
allSums (p ∷ ps) = sumsWithLater p ps ++ allSums ps

offdiag : List Nat → List Nat
offdiag xs = sortN (allSums (zipIdx xs))

------------------------------------------------------------------------
-- balanced: nontrivial unordered {A,B} decompositions with equal offdiag
------------------------------------------------------------------------

PairLL : Set
PairLL = Σ (List Nat) (λ _ → List Nat)

-- subsequences over IV, Haskell order: [] first, then for each element x
-- (in order) the previous subsequences with x consed on, interleaved as
-- Haskell's `subsequences` does. We only need the SET of subsequences
-- (order of enumeration does not affect the final nub'd/sorted result),
-- so we use the simpler standard construction:
--   subs []     = [[]]
--   subs (x:xs) = subs xs ++ map (x:) (subs xs)
subsIV : List IV → List (List IV)
subsIV []       = [] ∷ []
subsIV (x ∷ xs) = let rest = subsIV xs in rest ++ mapL (λ ys → x ∷ ys) rest

isNullIV : List IV → Bool
isNullIV [] = true
isNullIV (_ ∷ _) = false

canon : PairLL → PairLL
canon (x , y) = if leLN x y then (x , y) else (y , x)

eqPairLL : PairLL → PairLL → Bool
eqPairLL (a , b) (c , d) = eqLN a c && eqLN b d

elemPairLL : PairLL → List PairLL → Bool
elemPairLL p []       = false
elemPairLL p (q ∷ qs) = eqPairLL p q || elemPairLL p qs

nubPairLLAcc : List PairLL → List PairLL → List PairLL
nubPairLLAcc seen []       = []
nubPairLLAcc seen (p ∷ ps) with elemPairLL p seen
... | true  = nubPairLLAcc seen ps
... | false = p ∷ nubPairLLAcc (p ∷ seen) ps

nubPairLL : List PairLL → List PairLL
nubPairLL xs = nubPairLLAcc [] xs

-- one candidate `a` (a nonempty sub-selection of ix) against its
-- complement `b` inside the full indexed list `ix`
mkCand : List IV → List IV → List PairLL
mkCand ix a =
  let sel   = mapL fst a
      b     = filterL (λ p → notElemN (fst p) sel) ix
      avals = mapL snd a
      bvals = mapL snd b
  in if isNullIV a then []
     else (if isNullIV b then []
     else (if eqLN avals bvals then []
     else (if notB (eqLN (offdiag avals) (offdiag bvals)) then []
     else (canon (sortN avals , sortN bvals) ∷ []))))

balanced : List Nat → List PairLL
balanced t =
  let ix  = zipIdx t
      raw = concatMapL (mkCand ix) (subsIV ix)
  in nubPairLL raw

minMult : List Nat → Nat
minMult t =
  let m = go1 t
  in lengthL (filterL (λ x → x ==N m) t)
  where
    go1 : List Nat → Nat
    go1 []       = 0            -- unused: every total is nonempty
    go1 (x ∷ []) = x
    go1 (x ∷ (y ∷ xs)) = minN x (go1 (y ∷ xs))

------------------------------------------------------------------------
-- the fixed battery of total multisets, mirroring the Haskell exactly
------------------------------------------------------------------------

rangeUpTo : Nat → List Nat
rangeUpTo zero    = zero ∷ []
rangeUpTo (suc n) = rangeUpTo n ++ (suc n ∷ [])

lit : List Nat → List Nat
lit xs = xs

totals : List (List Nat)
totals =
  mapL rangeUpTo (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ [])
  ++ (rangeUpTo 15 ∷ [])
  ++ ( lit (0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ [])
     ∷ lit (0 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 4 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ [])
     ∷ lit (0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ [])
     ∷ lit (0 ∷ 2 ∷ 3 ∷ 5 ∷ 6 ∷ 8 ∷ 9 ∷ 11 ∷ [])
     ∷ lit (0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 7 ∷ [])
     ∷ [])
  ++ ( lit (0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ [])
     ∷ lit (0 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
     ∷ lit (0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
     ∷ lit (0 ∷ 0 ∷ 1 ∷ 1 ∷ [])
     ∷ lit (0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 4 ∷ 5 ∷ 5 ∷ 6 ∷ 6 ∷ 7 ∷ 7 ∷ [])
     ∷ lit (0 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 4 ∷ [])
     ∷ [])

------------------------------------------------------------------------
-- rendering, matching Haskell's `show` exactly
------------------------------------------------------------------------

nl : String
nl = primStringFromList ('\n' ∷ [])

comma : String
comma = primStringFromList (',' ∷ [])

showNat : Nat → String
showNat = primShowNat

joinComma : List String → String
joinComma []            = ""
joinComma (s ∷ [])      = s
joinComma (s ∷ s2 ∷ ss) = primStringAppend s (primStringAppend comma (joinComma (s2 ∷ ss)))

showListNat : List Nat → String
showListNat xs = primStringAppend "[" (primStringAppend (joinComma (mapL showNat xs)) "]")

showPairLLN : PairLL → Nat → String
showPairLLN (t , _) c = primStringAppend "(" (primStringAppend (showListNat t)
  (primStringAppend comma (primStringAppend (showNat c) ")")))

-- violation entries are ([Int], Int) in the Haskell; here we carry the
-- total's own List Nat and its balanced-count
Viol : Set
Viol = Σ (List Nat) (λ _ → Nat)

showViol : Viol → String
showViol (t , c) = primStringAppend "(" (primStringAppend (showListNat t)
  (primStringAppend comma (primStringAppend (showNat c) ")")))

showViols : List Viol → String
showViols vs = primStringAppend "[" (primStringAppend (joinComma (mapL showViol vs)) "]")

------------------------------------------------------------------------
-- rows and report
------------------------------------------------------------------------

Row : Set
Row = Σ (List Nat) (λ _ → Σ Nat (λ _ → Nat))  -- (t, minMult t, |balanced t|)

mkRow : List Nat → Row
mkRow t = (t , (minMult t , lengthL (balanced t)))

rows : List Row
rows = mapL mkRow totals

rowLine : Row → String
rowLine (t , (m , c)) =
  primStringAppend (if 2 <= m then "minREP " else "minUNQ ")
  (primStringAppend (showListNat t)
  (primStringAppend "  balanced=" (primStringAppend (showNat c) nl)))

rowLines : List Row → String
rowLines []       = ""
rowLines (r ∷ rs) = primStringAppend (rowLine r) (rowLines rs)

viol3Of : List Row → List Viol
viol3Of []                 = []
viol3Of ((t , (m , c)) ∷ rs) =
  if notB (c <= 1)  -- c > 1
  then (t , c) ∷ viol3Of rs
  else viol3Of rs

viol1Of : List Row → List Viol
viol1Of []                   = []
viol1Of ((t , (m , c)) ∷ rs) =
  if (2 <= m) && notB (c ==N 0)
  then (t , c) ∷ viol1Of rs
  else viol1Of rs

isNullViol : List Viol → Bool
isNullViol [] = true
isNullViol (_ ∷ _) = false

report : String
report =
  let v3 = viol3Of rows
      v1 = viol1Of rows
      hdr = rowLines rows
      dashLine = primStringAppend "----" nl
      l3 = primStringAppend "(iii) at-most-one violations : " (primStringAppend (showViols v3) nl)
      l1 = primStringAppend "(i)  repeated-min violations : " (primStringAppend (showViols v1) nl)
      final = if isNullViol v3 && isNullViol v1
              then primStringAppend "PASS: fiber ≤ 1 per total, and repeated-minimum ⟹ 0, on every total checked." nl
              else primStringAppend "FAIL: a prediction of OFFDIAGONAL_NO_GO_FIBER.md was violated." nl
  in primStringAppend hdr (primStringAppend dashLine (primStringAppend l3 (primStringAppend l1 final)))

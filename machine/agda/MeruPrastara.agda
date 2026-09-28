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
-- मेरु-प्रस्तारः — ported from machine/MeruPrastara_TheSignedArrayIsOne
-- ProductAndTheZetaDualityIsAShiftOfOne.hs (absent from this repository).  The default (no-argument) report of that
-- program, term for term, as a --safe checked value compiled by the
-- kernel's own backend (MAlonzo/GHC).  प्रस्तार is Piṅgala's word for the
-- systematic laying-out of metres (Chandastra 8, ~300 BCE; Halyudha's
-- Mtasajvan, 10th c., names the meru); the sign on the array is the
-- Mbius sign.  The identity behind this
-- display: formal/cubical/MulaShakti_TheMarkingParameterIsAPowerAndThe
-- ZetaTwistIsTranslationByOne.agda (absent from this repository).
------------------------------------------------------------------------

module MeruPrastara where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Int

------------------------------------------------------------------------
-- tiny prelude (no stdlib)
------------------------------------------------------------------------

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

infixr 5 _++L_
_++L_ : {A : Set} → List A → List A → List A
[]       ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

upTo : Nat → List Nat            -- [0 .. n], inclusive
upTo zero    = zero ∷ []
upTo (suc n) = upTo n ++L (suc n ∷ [])

replicateB : Nat → Bool → List Bool
replicateB zero    _ = []
replicateB (suc n) b = b ∷ replicateB n b

concatL : List String → String
concatL []       = ""
concatL (x ∷ xs) = primStringAppend x (concatL xs)

intercalateS : String → List String → String
intercalateS sep []             = ""
intercalateS sep (x ∷ [])       = x
intercalateS sep (x ∷ xs@(_ ∷ _)) =
  primStringAppend x (primStringAppend sep (intercalateS sep xs))

strLen : String → Nat
strLen s = lengthL (primStringToList s)

padStr : Nat → String → String
padStr w s = primStringAppend
  (primStringFromList (replicateCh (w - strLen s) ' ')) s
  where
    replicateCh : Nat → Char → List Char
    replicateCh zero    _ = []
    replicateCh (suc n) c = c ∷ replicateCh n c

nl : String
nl = primStringFromList ('\n' ∷ [])

------------------------------------------------------------------------
-- Int arithmetic (Agda.Builtin.Int gives only the type + primShowInteger)
------------------------------------------------------------------------

negateInt : Int → Int
negateInt (pos zero)    = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n)    = pos (suc n)

-- a - b, both Nat, as a signed Int
subNat : Nat → Nat → Int
subNat a b = if b <= a then pos (a - b) else negsuc ((b - a) - 1)
  where
    _<=_ : Nat → Nat → Bool
    zero  <= _     = true
    suc _ <= zero  = false
    suc x <= suc y = x <= y

addInt : Int → Int → Int
addInt (pos a)    (pos b)    = pos (a + b)
addInt (negsuc a) (negsuc b) = negsuc (suc (a + b))
addInt (pos a)    (negsuc b) = subNat a (suc b)
addInt (negsuc a) (pos b)    = subNat b (suc a)

mulInt : Int → Int → Int
mulInt (pos a)    (pos b)    = pos (a * b)
mulInt (negsuc a) (negsuc b) = pos (suc a * suc b)
mulInt (pos a)    (negsuc b) = negateInt (pos (a * suc b))
mulInt (negsuc a) (pos b)    = negateInt (pos (suc a * b))

eqNatL : Nat → Nat → Bool
eqNatL zero    zero    = true
eqNatL (suc x) (suc y) = eqNatL x y
eqNatL _       _       = false

eqInt : Int → Int → Bool
eqInt (pos a)    (pos b)    = eqNatL a b
eqInt (negsuc a) (negsuc b) = eqNatL a b
eqInt _ _ = false

powInt : Int → Nat → Int
powInt t zero    = pos 1
powInt t (suc n) = mulInt t (powInt t n)

showInt : Int → String
showInt = primShowInteger

------------------------------------------------------------------------
-- चिह्नम् / सक्रियम् / निष्क्रियम् — the one rule, and ओजः, and बिन्दुः
------------------------------------------------------------------------

chihna : Bool → Int
chihna true  = negsuc 0
chihna false = pos 1

sakriya : Bool → Int
sakriya true  = pos 1
sakriya false = pos 0

nishkriya : Bool → Int
nishkriya true  = pos 0
nishkriya false = pos 1

oja : List Bool → Nat
oja bs = lengthL (filterL (λ b → b) bs)

productL : List Int → Int
productL []       = pos 1
productL (x ∷ xs) = mulInt x (productL xs)

ghata jyoti : Int → List Bool → Int
ghata t bs = productL (mapL (λ b → addInt (chihna b)   (mulInt (sakriya b) t)) bs)
jyoti t bs = productL (mapL (λ b → addInt (nishkriya b) (mulInt (sakriya b) t)) bs)

-- बिन्दुः m k — Piṅgala's array with the Möbius sign, by the recursion.
bindu : Nat → Nat → Int
bindu zero    zero    = pos 1
bindu zero    (suc k) = pos 0
bindu (suc m) zero    = negateInt (bindu m zero)
bindu (suc m) (suc k) = addInt (negateInt (bindu m (suc k))) (bindu m k)

------------------------------------------------------------------------
-- display
------------------------------------------------------------------------

meruRowStr : Nat → Nat → String
meruRowStr n m = primStringAppend
  (padStr ((n - m) * 4) "")
  (intercalateS "  " (mapL (λ k → padStr 5 (showInt (bindu m k))) (upTo m)))

meruLines : Nat → List String
meruLines n = mapL (λ m → primStringAppend "  " (meruRowStr n m)) (upTo n)

okStr : Bool → String
okStr true  = " ✓"
okStr false = " ✗"

rowStr : Int → Nat → String
rowStr t m =
  let bs   = replicateB m true
      lhs  = ghata t bs
      rhs  = powInt (addInt t (negsuc 0)) m
      lhs' = jyoti t bs
      rhs' = powInt t m
      shft = ghata (addInt (pos 1) t) bs
  in concatL
       ( "  ω=" ∷ padStr 2 (primShowNat m)
       ∷ "   ∏(χ+σt) = " ∷ padStr 8 (showInt lhs)
       ∷ "   (t−1)^ω = " ∷ padStr 8 (showInt rhs) ∷ okStr (eqInt lhs rhs)
       ∷ "   ζ∏ = " ∷ padStr 8 (showInt lhs')
       ∷ "   t^ω = " ∷ padStr 8 (showInt rhs') ∷ okStr (eqInt lhs' rhs')
       ∷ "   ∏ at t+1 = " ∷ padStr 8 (showInt shft) ∷ okStr (eqInt lhs' shft)
       ∷ [] )

bitChar : Bool → Char
bitChar true  = '1'
bitChar false = '0'

bitsStr : List Bool → String
bitsStr p = primStringAppend "\""
  (primStringAppend (primStringFromList (mapL bitChar p)) "\"")

showIntList : List Int → String
showIntList xs = primStringAppend "["
  (primStringAppend (intercalateS "," (mapL showInt xs)) "]")

patterns : List (List Bool)
patterns =
  ( true ∷ false ∷ false ∷ true ∷ false ∷ [] )
  ∷ ( false ∷ true ∷ true ∷ false ∷ false ∷ [] )
  ∷ ( false ∷ false ∷ true ∷ false ∷ true ∷ [] )
  ∷ ( true ∷ true ∷ false ∷ false ∷ false ∷ [] )
  ∷ []

blindLine : List Bool → String
blindLine p = concatL
  ( "  " ∷ bitsStr p
  ∷ "  ω=" ∷ primShowNat (oja p)
  ∷ "   levels " ∷ showIntList (mapL (λ k → bindu (oja p) k) (upTo (lengthL p)))
  ∷ [] )

blindLines : List String
blindLines = mapL blindLine patterns

withNl : List String → String
withNl ls = concatL (mapL (λ l → primStringAppend l nl) ls)

------------------------------------------------------------------------
-- report — the no-argument default: n = 7, t = 3
------------------------------------------------------------------------

report : String
report =
  let n = 7
      t = pos 3
  in concatL
       ( "मेरु-प्रस्तारः — one product, one parameter, and what falls out of it.\n"
       ∷ nl
       ∷ primStringAppend "the array, rows ω = 0 .. "
           (primStringAppend (primShowNat n)
             "  (row ω, entry k = the k-marked prime charge):")
       ∷ nl
       ∷ withNl (meruLines n)
       ∷ "\nrow 0 of each is the parity character (−1)^ω; entry k=1 is the Möbius-signed charge itself."
       ∷ nl
       ∷ primStringAppend "\nthe rule against its closed form, at t = "
           (primStringAppend (showInt t) ":")
       ∷ nl
       ∷ withNl (mapL (rowStr t) (upTo n))
       ∷ "\nthe ζ duality is a shift of one — the last two columns above are the same number,\nfor every ω and every t.  Try another t."
       ∷ nl
       ∷ "\nand what the rule cannot see: same ω, different places."
       ∷ nl
       ∷ withNl blindLines
       ∷ "  identical at every level.  The array factors through ω, so the\n  rule is blind to WHICH primes divide and sees only HOW MANY."
       ∷ nl
       ∷ "\n(checked: formal/cubical/MulaShakti_TheMarkingParameterIsAPowerAndTheZetaTwistIsTranslationByOne.agda)"
       ∷ nl
       ∷ [] )

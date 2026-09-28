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

-- Svarga_TheLawRunsOnAnyCpuInOnePageBothPolesExactAndTheBooleanVerdictIsProvablyADurnaya
--
-- स्वर्ग — heaven, the weightless place; here: the law made portable enough
-- to run on any CPU, in one page, with no kernel, no model, no float — the
-- akara form that survives every avatar.  Ordinary ; the compound
-- is built here; no text is claimed for it and no source claims
-- the theorems, which are cubical-corpus facts (Punaragamana.Carrier;
-- Saptabhangi.दुर्नयः) restated as a FINITE EXHAUSTIVE computation, which is
-- proof for the stated box, NOT a reproof of the general cubical terms.
--
-- Ported from machine/Svarga_…hs, term-for-term, into --safe Agda,
-- compiled by the kernel's own backend (MAlonzo/GHC) per the recipe in
-- SanghattaYantra (this repo).  `report : String` is the entire pure
-- computation; the IO membrane lives in SvargaMukha.agda.

{-# OPTIONS --safe #-}

module Svarga where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
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

boolEq : Bool → Bool → Bool
boolEq true  b = b
boolEq false b = notB b

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

andAll : List Bool → Bool
andAll []       = true
andAll (x ∷ xs) = x && andAll xs

sumL : List Nat → Nat
sumL []       = 0
sumL (x ∷ xs) = x + sumL xs

_<=_ : Nat → Nat → Bool
zero  <= _     = true
suc _ <= zero  = false
suc a <= suc b = a <= b

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc a ==N suc b = a ==N b
_     ==N _     = false

elemN : Nat → List Nat → Bool
elemN n []       = false
elemN n (x ∷ xs) = (n ==N x) || elemN n xs

nubNAcc : List Nat → List Nat → List Nat
nubNAcc seen []       = []
nubNAcc seen (x ∷ xs) with elemN x seen
... | true  = nubNAcc seen xs
... | false = x ∷ nubNAcc (x ∷ seen) xs

nubN : List Nat → List Nat
nubN xs = nubNAcc [] xs

-- [0 .. n-1], ascending, via an accumulator that recurses structurally on
-- the fuel-like second argument (which is exactly the count remaining).
rangeUpAcc : Nat → Nat → List Nat
rangeUpAcc start zero    = []
rangeUpAcc start (suc k) = start ∷ rangeUpAcc (suc start) k

rangeUp : Nat → List Nat
rangeUp n = rangeUpAcc 0 n

-- String join helpers
infixr 5 _<>_
_<>_ : String → String → String
_<>_ = primStringAppend

nl : String
nl = "\n"

joinLinesNL : List String → String
joinLinesNL []       = ""
joinLinesNL (l ∷ ls) = l <> nl <> joinLinesNL ls

joinCommaNat : List Nat → String
joinCommaNat []             = ""
joinCommaNat (x ∷ [])       = primShowNat x
joinCommaNat (x ∷ xs@(_ ∷ _)) = primShowNat x <> "," <> joinCommaNat xs

showNatList : List Nat → String
showNatList xs = "[" <> joinCommaNat xs <> "]"

showBool : Bool → String
showBool true  = "True"
showBool false = "False"

------------------------------------------------------------------------
-- A finite map A → B is a list of images, one per element of A.
------------------------------------------------------------------------

Map : Set
Map = List Nat

-- all maps A → B, |A| = na, |B| = nb  (nb^na of them), same order as the
-- Haskell list comprehension: [ b : rest | b <- [0..nb-1], rest <- allMaps (na-1) nb ]
allMaps : Nat → Nat → List Map
allMaps zero    nb = [] ∷ []
allMaps (suc na) nb =
  concatMapL (λ b → mapL (λ rest → b ∷ rest) (allMaps na nb)) (rangeUp nb)

------------------------------------------------------------------------
-- ANGEL · road one.  |graph f| = |A| for every f (the finite face of
-- `singl (f a)` being contractible — for each a exactly one b = f a).
------------------------------------------------------------------------

-- the image of a at position a (0 when out of range; never used there)
at : Map → Nat → Nat
at []       _       = 0
at (b ∷ _)  zero    = b
at (_ ∷ bs) (suc a) = at bs a

-- the graph, computed as a SUBSET of A × B (not read off the list shape):
-- every pair (a , b) with f a = b.  Counting it is a genuine check that
-- each a meets exactly one b.
graphSize : Nat → Map → Nat
graphSize nb f =
  lengthL (concatMapL (λ a → filterL (λ b → at f a ==N b) (rangeUp nb))
                      (rangeUp (lengthL f)))

angelHolds : Nat → Map → Bool
angelHolds nb f = graphSize nb f ==N lengthL f

------------------------------------------------------------------------
-- DEVIL · road two.  The fibre census, three-valued.
------------------------------------------------------------------------

data Verdict : Set where
  Riktam Ekam Bahu : Verdict

verdictEq : Verdict → Verdict → Bool
verdictEq Riktam Riktam = true
verdictEq Ekam   Ekam   = true
verdictEq Bahu   Bahu   = true
verdictEq _      _      = false

fibreSize : Map → Nat → Nat
fibreSize f b = lengthL (filterL (λ x → x ==N b) f)

verdict : Nat → Nat → Verdict
verdict _ zero          = Riktam
verdict _ (suc zero)    = Ekam
verdict _ (suc (suc _)) = Bahu

census : Nat → Map → List (Σ Nat (λ _ → Verdict))
census nb f = mapL (λ b → (b , verdict nb (fibreSize f b))) (rangeUp nb)

isEquivFin : Nat → Map → Bool
isEquivFin nb f = andAll (mapL (λ p → verdictEq (snd p) Ekam) (census nb f))

-- both poles must agree on |A| (fibres partition the domain)
polesAgree : Nat → Map → Bool
polesAgree nb f = sumL (mapL (fibreSize f) (rangeUp nb)) ==N lengthL f

------------------------------------------------------------------------
-- verdict lists: show, and Haskell `sort` (ascending by declaration order)
------------------------------------------------------------------------

showVerdict : Verdict → String
showVerdict Riktam = "Riktam"
showVerdict Ekam   = "Ekam"
showVerdict Bahu   = "Bahu"

joinCommaVerdict : List Verdict → String
joinCommaVerdict []               = ""
joinCommaVerdict (x ∷ [])         = showVerdict x
joinCommaVerdict (x ∷ xs@(_ ∷ _)) = showVerdict x <> "," <> joinCommaVerdict xs

showVerdictList : List Verdict → String
showVerdictList xs = "[" <> joinCommaVerdict xs <> "]"

verdictOrd : Verdict → Nat
verdictOrd Riktam = 0
verdictOrd Ekam   = 1
verdictOrd Bahu   = 2

verdictLe : Verdict → Verdict → Bool
verdictLe a b = verdictOrd a <= verdictOrd b

insertVerdict : Verdict → List Verdict → List Verdict
insertVerdict v []       = v ∷ []
insertVerdict v (x ∷ xs) = if verdictLe v x then (v ∷ (x ∷ xs)) else (x ∷ insertVerdict v xs)

sortVerdict : List Verdict → List Verdict
sortVerdict []       = []
sortVerdict (x ∷ xs) = insertVerdict x (sortVerdict xs)

listVerdictEq : List Verdict → List Verdict → Bool
listVerdictEq []       []       = true
listVerdictEq (a ∷ as) (b ∷ bs) = verdictEq a b && listVerdictEq as bs
listVerdictEq _        _        = false

vsOf3 : Map → List Verdict
vsOf3 m = sortVerdict (mapL snd (census 3 m))

------------------------------------------------------------------------
-- THE DURNAYA CONTROL: first (f,g) in ms × ms (ms = allMaps 3 3), in the
-- exact nested order of the Haskell list comprehension, both `not
-- isEquivFin`, whose sorted censuses differ.
------------------------------------------------------------------------

innerSearch : Map → List Verdict → List Map → Maybe Map
innerSearch f vf []       = nothing
innerSearch f vf (g ∷ gs) with notB (isEquivFin 3 g)
... | false = innerSearch f vf gs
... | true with listVerdictEq vf (vsOf3 g)
...   | true  = innerSearch f vf gs
...   | false = just g

outerSearch : List Map → List Map → Maybe (Σ Map (λ _ → Map))
outerSearch msAll []       = nothing
outerSearch msAll (f ∷ fs) with notB (isEquivFin 3 f)
... | false = outerSearch msAll fs
... | true with innerSearch f (vsOf3 f) msAll
...   | just g  = just (f , g)
...   | nothing = outerSearch msAll fs

durnayaWitness : Maybe (Σ Map (λ _ → Map))
durnayaWitness = outerSearch (allMaps 3 3) (allMaps 3 3)

------------------------------------------------------------------------
-- assembling the checked report
------------------------------------------------------------------------

BoundsList : List (Σ Nat (λ _ → Nat))
BoundsList = concatMapL (λ na → mapL (λ nb → (na , nb)) (rangeUp 5)) (rangeUp 5)

mapsOf : Σ Nat (λ _ → Nat) → List Map
mapsOf ab = allMaps (fst ab) (snd ab)

nMaps : Nat
nMaps = sumL (mapL (λ ab → lengthL (mapsOf ab)) BoundsList)

angelAll : Bool
angelAll = andAll (concatMapL (λ ab → mapL (angelHolds (snd ab)) (mapsOf ab)) BoundsList)

polesAll : Bool
polesAll = andAll (concatMapL (λ ab → mapL (polesAgree (snd ab)) (mapsOf ab)) BoundsList)

devilSound : Bool
devilSound = andAll
  (concatMapL
    (λ ab → mapL
      (λ f → boolEq (isEquivFin (snd ab) f)
                     ((lengthL f ==N snd ab) && (lengthL (nubN f) ==N lengthL f)))
      (mapsOf ab))
    BoundsList)

durnayaLines : List String
durnayaLines with durnayaWitness
... | nothing = "DURNAYA CONTROL: no witness found — the boolean would suffice (unexpected)." ∷ []
... | just (f , g) =
  let vf = vsOf3 f
      vg = vsOf3 g
  in "THE DURNAYA, exhibited at three seeds (न द्वौ, त्रयः):"
   ∷ ("  f = " <> showNatList f <> "   census = " <> showVerdictList vf <> "   isEquiv? False")
   ∷ ("  g = " <> showNatList g <> "   census = " <> showVerdictList vg <> "   isEquiv? False")
   ∷ "  same boolean verdict, different census — the bit merged"
   ∷ "  रिक्तम् and बहु into one 'no'.  Three verdicts, never two."
   ∷ []

report : String
report = joinLinesNL
  ( "═══ स्वर्ग · the law on any CPU, one page, both poles, exact ═══"
  ∷ ""
  ∷ ("checked over every map A→B with |A|,|B| ≤ 4 : " <> primShowNat nMaps <> " maps")
  ∷ "    $ runghc machine/Svarga_….hs"
  ∷ ""
  ∷ ("ANGEL · road one · |graph f| = |A| for EVERY f (bind b is free) : " <> showBool angelAll)
  ∷ ("both poles agree on |A| (fibres partition the domain)          : " <> showBool polesAll)
  ∷ ("DEVIL · road two · isEquiv ⟺ every fibre एकम् ⟺ |A|=|B| ∧ inj   : " <> showBool devilSound)
  ∷ ""
  ∷ durnayaLines
  ++ ("" ∷ "BOTH POLES HOLD, disjoint and exhaustive; the boolean is a durnaya."
        ∷ "The god fits on a page and runs on any CPU.  अल्पं स्थापय, शेषं जनय ॥"
        ∷ [])
  )

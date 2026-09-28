-- ॥ बीजम् ॥  One machine, one law: which side of `f a ≡ b` is bound is everything.
-- Output bound: singl (f a), contractible — the datum rides free.  Input bound:
-- fiber f b — the loss, and the subject.  Univalence computes here: an
-- equivalence is a channel, transport carries every theorem across it, and what
-- cannot cross is written as a defect — there is no third path (ahiṃsā).
-- Memory, charge, symmetry, price, distance, verdict: six faces of the one
-- fibre; the verdict type is the saptabhag, and the sources are the origin
-- (Umāsvāti, Samantabhadra, Akalaṅka — restatements are named as such).  The
-- kernel decides truth; carriers ask and generate.  This file is one naya, true
-- and not whole.

{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- सङ्घट्ट-यन्त्र — the critical-pair organ, rewritten as CHECKED TERMS and
-- compiled by the kernel's OWN backend (MAlonzo/GHC), so the machine's
-- limb is body, not a reimplementation standing beside the body.
--
-- The pure core of
-- machine/Sanghatta_…hs (parse, term order, unification, matching,
-- rewriting to normal form, critical pairs, the non-joining census) is
-- ported here term-for-term into --safe Agda; `agda -c` compiles it to a
-- native executable through GHC.  Nothing here is postulated except the IO membrane at the very
-- bottom — the typed world-leaf (readFile/putStrLn), which is the only
-- part that CANNOT be a checked term and is kept to ~a dozen lines.
--
-- --safe means: every recursion the Haskell left unbounded (the parser,
-- unification's worklist, matching, one rewrite step) is here bounded by
-- explicit fuel, structural on the fuel.  STATED PLAINLY: at the type level
-- fuel exhaustion is NOT distinguished from failure — `unify`, `matchT`,
-- `step` and `parseT` return `nothing` in both cases, and `normal` returns
-- whatever term it reached after 400 steps.  The fuel constants are only
-- set large enough for library.terms; a three-outcome result (finished /
-- failed / out of fuel) would make the distinction a term.
--
-- ORIENTATION IS BY SIZE (`size r ≥ size l` becomes r → l), which is not a
-- reduction order: equal-size equations such as commutativity are oriented
-- and can loop.  The critical-pair lemma needs termination, so the
-- NON-JOINING count below is meaningful only where `normal` really reached
-- normal forms; with a reduction order (LPO/KBO) it would be exact.
------------------------------------------------------------------------

module SanghattaMachine_TheCriticalPairOrganAsCheckedTermsCompiledByTheKernelsOwnBackend where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- tiny prelude (no stdlib; keeps the organ free of version-skew)
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

revApp : {A : Set} → List A → List A → List A
revApp []       acc = acc
revApp (x ∷ xs) acc = revApp xs (x ∷ acc)

reverseL : {A : Set} → List A → List A
reverseL xs = revApp xs []

takeL : {A : Set} → Nat → List A → List A
takeL zero    _        = []
takeL (suc n) []       = []
takeL (suc n) (x ∷ xs) = x ∷ takeL n xs

zipL : {A B : Set} → List A → List B → List (Σ A (λ _ → B))
zipL []       _        = []
zipL _        []       = []
zipL (a ∷ as) (b ∷ bs) = (a , b) ∷ zipL as bs

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


-- Nat compare
_<=_ : Nat → Nat → Bool
zero  <= _     = true
suc _ <= zero  = false
suc a <= suc b = a <= b

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc a ==N suc b = a ==N b
_     ==N _     = false

------------------------------------------------------------------------
-- terms, over String names
------------------------------------------------------------------------

data Term : Set where
  V : String → Term
  F : String → List Term → Term

_==S_ : String → String → Bool
a ==S b = primStringEquality a b

eqT  : Term → Term → Bool
eqTs : List Term → List Term → Bool
eqT (V a)    (V b)    = a ==S b
eqT (F f as) (F g bs) = (f ==S g) && eqTs as bs
eqT _        _        = false
eqTs []       []       = true
eqTs (a ∷ as) (b ∷ bs) = eqT a b && eqTs as bs
eqTs _        _        = false

sizeT : Term → Nat
sizeTs : List Term → Nat
sizeT (V _)    = 1
sizeT (F _ as) = suc (sizeTs as)
sizeTs []       = 0
sizeTs (t ∷ ts) = sizeT t + sizeTs ts

elemS : String → List String → Bool
elemS s []       = false
elemS s (x ∷ xs) = (s ==S x) || elemS s xs

nubAccS : List String → List String → List String
nubAccS seen [] = []
nubAccS seen (x ∷ xs) with elemS x seen
... | true  = nubAccS seen xs
... | false = x ∷ nubAccS (x ∷ seen) xs

nubS : List String → List String
nubS xs = nubAccS [] xs

varsOf : Term → List String
varsOfs : List Term → List String
varsOf (V v)    = v ∷ []
varsOf (F _ as) = nubS (varsOfs as)
varsOfs []       = []
varsOfs (t ∷ ts) = varsOf t ++ varsOfs ts

-- render, exactly as the Haskell Show: V v = v ; F f [] = f ;
-- F f as = f(a,b,…) comma-joined.
render : Term → String
renderArgs : List Term → String
render (V v)    = v
render (F f []) = f
render (F f (a ∷ as)) = primStringAppend f
  (primStringAppend "(" (primStringAppend (renderArgs (a ∷ as)) ")"))
renderArgs []           = ""
renderArgs (a ∷ [])     = render a
renderArgs (a ∷ b ∷ as) = primStringAppend (render a)
  (primStringAppend "," (renderArgs (b ∷ as)))

------------------------------------------------------------------------
-- substitution as an assoc list; apply is structural on the term
------------------------------------------------------------------------

Sub : Set
Sub = List (Σ String (λ _ → Term))

lookupS : String → Sub → Maybe Term
lookupS v []             = nothing
lookupS v ((k , t) ∷ xs) = if v ==S k then just t else lookupS v xs

apply : Sub → Term → Term
applys : Sub → List Term → List Term
apply s (V v)    with lookupS v s
... | just t  = t
... | nothing = V v
apply s (F f as) = F f (applys s as)
applys s []       = []
applys s (t ∷ ts) = apply s t ∷ applys s ts

occurs : String → Term → Bool
occurs v t = elemS v (varsOf t)

------------------------------------------------------------------------
-- unification (worklist, fuel-bounded) — faithful to the Haskell `go`
------------------------------------------------------------------------

Pair : Set
Pair = Σ Term (λ _ → Term)

unifyGo : Nat → List Pair → Sub → Maybe Sub
unifyGo zero    _  _ = nothing
unifyGo (suc n) [] s = just s
unifyGo (suc n) ((V v , t) ∷ rest) s =
  if eqT (V v) t then unifyGo n rest s
  else if occurs v t then nothing
  else let s1 : Sub
           s1 = (v , t) ∷ mapL (λ p → (fst p , apply ((v , t) ∷ []) (snd p))) s
       in unifyGo n (mapL (λ p → (apply s1 (fst p) , apply s1 (snd p))) rest) s1
unifyGo (suc n) ((t , V v) ∷ rest) s = unifyGo n ((V v , t) ∷ rest) s
unifyGo (suc n) ((F f as , F g bs) ∷ rest) s =
  if (f ==S g) && (lengthL as ==N lengthL bs)
  then unifyGo n (zipL as bs ++ rest) s
  else nothing

unify : Term → Term → Maybe Sub
unify a b = unifyGo 100000 ((a , b) ∷ []) []

------------------------------------------------------------------------
-- matching (l's vars bind), fuel-bounded
------------------------------------------------------------------------

matchGo  : Nat → Term → Term → Sub → Maybe Sub
matchLs  : Nat → List (Σ Term (λ _ → Term)) → Sub → Maybe Sub
matchGo zero _ _ _ = nothing
matchGo (suc n) (V v) u s with lookupS v s
... | nothing = just ((v , u) ∷ s)
... | just u' = if eqT u u' then just s else nothing
matchGo (suc n) (F f as) (F g bs) s =
  if (f ==S g) && (lengthL as ==N lengthL bs)
  then matchLs n (zipL as bs) s else nothing
matchGo (suc n) (F _ _) (V _) _ = nothing
matchLs zero _ _ = nothing
matchLs (suc n) [] s = just s
matchLs (suc n) ((a , b) ∷ rest) s with matchGo n a b s
... | nothing = nothing
... | just s' = matchLs n rest s'

matchT : Term → Term → Maybe Sub
matchT l t = matchGo 100000 l t []

------------------------------------------------------------------------
-- one rewrite step, then normal form (fuel like the Haskell's 400)
------------------------------------------------------------------------

Rule : Set
Rule = Σ Term (λ _ → Term)

firstRedex : List Rule → Term → Maybe Term
firstRedex [] _ = nothing
firstRedex ((l , r) ∷ rs) t with matchT l t
... | just s  = just (apply s r)
... | nothing = firstRedex rs t

step     : Nat → List Rule → Term → Maybe Term
stepFirst : Nat → List Rule → List Term → Maybe (List Term)
step zero _ _ = nothing
step (suc n) rules t with firstRedex rules t
... | just t' = just t'
... | nothing with t
...   | V _    = nothing
...   | F f as with stepFirst n rules as
...     | just as' = just (F f as')
...     | nothing  = nothing
stepFirst zero _ _ = nothing
stepFirst (suc n) rules [] = nothing
stepFirst (suc n) rules (a ∷ as) with step n rules a
... | just a' = just (a' ∷ as)
... | nothing with stepFirst n rules as
...   | just as' = just (a ∷ as')
...   | nothing  = nothing

normal : List Rule → Term → Term
normal rules = go 400
  where
    go : Nat → Term → Term
    go zero    t = t
    go (suc k) t with step 100000 rules t
    ... | just t' = go k t'
    ... | nothing = t

------------------------------------------------------------------------
-- critical pairs
------------------------------------------------------------------------

-- non-variable subterm positions (path is [Nat]); root first
nonVarPos : Term → List (Σ (List Nat) (λ _ → Term))
nonVarPosArgs : Nat → List Term → List (Σ (List Nat) (λ _ → Term))
nonVarPos (V _) = []
nonVarPos (F f as) = ([] , F f as) ∷ nonVarPosArgs 0 as
nonVarPosArgs _ [] = []
nonVarPosArgs i (a ∷ as) =
  mapL (λ p → (i ∷ fst p , snd p)) (nonVarPos a) ++ nonVarPosArgs (suc i) as

replaceAt : Term → List Nat → Term → Term
replaceAtArgs : Nat → List Term → List Nat → Term → List Term
replaceAt _ [] u = u
replaceAt (V v) (_ ∷ _) _ = V v
replaceAt (F f as) (i ∷ p) u = F f (replaceAtArgs i as p u)
replaceAtArgs _ [] _ _ = []
replaceAtArgs zero    (a ∷ as) p u = replaceAt a p u ∷ as
replaceAtArgs (suc i) (a ∷ as) p u = a ∷ replaceAtArgs i as p u

-- rename rule2's vars apart from rule1 (append ' to any shared with `against`)
renV : List String → String → String
renV taken v = if elemS v taken then primStringAppend v "'" else v

renTerm  : List String → Term → Term
renTerms : List String → List Term → List Term
renTerm taken (V v)    = V (renV taken v)
renTerm taken (F f as) = F f (renTerms taken as)
renTerms taken []       = []
renTerms taken (t ∷ ts) = renTerm taken t ∷ renTerms taken ts

freshen : Term → Rule → Rule
freshen against rl =
  let taken = varsOf against
  in (renTerm taken (fst rl) , renTerm taken (snd rl))

-- overlap rule2 into non-var positions of rule1's lhs
isNullP : List Nat → Bool
isNullP [] = true
isNullP (_ ∷ _) = false

-- unify the subterm `sub` (at position `posn` in l1) with l2; on success
-- emit (apply s r1r , apply s (replaceAt l1 posn re2)).
cpAt : Term → Term → Term → Term → Term → List Nat → List Pair
cpAt l1 r1r l2 re2 sub posn with unify sub l2
... | just s  = (apply s r1r , apply s (replaceAt l1 posn re2)) ∷ []
... | nothing = []

cpOne : Term → Term → Term → Term → Σ (List Nat) (λ _ → Term) → List Pair
cpOne l1 r1r l2 re2 ps =
  let pos = fst ps
      sub = snd ps
      keep = notB (isNullP pos) || notB (eqT l1 l2)
  in if keep then cpAt l1 r1r l2 re2 sub pos else []

criticalPairs : Rule → Rule → List Pair
criticalPairs r1 r2 =
  let l1 = fst r1
      r1r = snd r1
      fr = freshen l1 r2
      l2 = fst fr
      re2 = snd fr
      poss = nonVarPos l1
  in concatMapL (cpOne l1 r1r l2 re2) poss

------------------------------------------------------------------------
-- the census: parse library.terms, orient, critical pairs, non-joining
------------------------------------------------------------------------

-- parse the engine's surface syntax with fuel, over List Char
isNameChar : Char → Bool
isNameChar c =
  primCharEquality c '-' || primCharEquality c '*' || primCharEquality c '+'
  || inRange 'a' 'z' || inRange 'A' 'Z' || inRange '0' '9'
  where
    inRange : Char → Char → Bool
    inRange lo hi = (primCharToNat lo <= primCharToNat c)
                    && (primCharToNat c <= primCharToNat hi)

isVarName : String → Bool
isVarName s =
  (s ==S "x") || (s ==S "y") || (s ==S "z")
  || (s ==S "u") || (s ==S "v") || (s ==S "w")

spanName : List Char → Σ (List Char) (λ _ → List Char)
spanName [] = ([] , [])
spanName (c ∷ cs) =
  if isNameChar c then (let r = spanName cs in (c ∷ fst r , snd r))
  else ([] , c ∷ cs)

ParseR : Set
ParseR = Maybe (Σ Term (λ _ → List Char))

pTerm : Nat → List Char → ParseR
pArgs : Nat → List Char → List Term → Maybe (Σ (List Term) (λ _ → List Char))
pTerm zero _ = nothing
pTerm (suc n) cs =
  let nm = spanName cs
      name = primStringFromList (fst nm)
      rest = snd nm
  in if isNull (fst nm) then nothing
     else openParen name rest
  where
    isNull : List Char → Bool
    isNull [] = true
    isNull (_ ∷ _) = false
    openParen : String → List Char → ParseR
    openParen name [] = just (if isVarName name then V name else F name [] , [])
    openParen name (c ∷ cs') with primCharEquality c '('
    ... | false = just (if isVarName name then V name else F name [] , c ∷ cs')
    ... | true  with pArgs n cs' []
    ...   | nothing = nothing
    ...   | just r  = just (F name (fst r) , snd r)
pArgs zero _ _ = nothing
pArgs (suc n) cs acc with pTerm n cs
... | nothing = nothing
... | just r with snd r
...   | (c ∷ cs') = if primCharEquality c ','
                    then pArgs n cs' (acc ++ (fst r ∷ []))
                    else if primCharEquality c ')'
                    then just (acc ++ (fst r ∷ []) , cs')
                    else nothing
...   | [] = nothing

open import Agda.Builtin.String using () renaming (primStringToList to s2l)

parseT : String → Maybe Term
parseT s with pTerm 100000 (filterL (λ c → notB (primCharEquality c ' ')) (s2l s))
... | nothing = nothing
... | just r with snd r
...   | [] = just (fst r)
...   | (_ ∷ _) = nothing

-- split a line on the first tab
break1 : Char → List Char → Σ (List Char) (λ _ → List Char)
break1 sep [] = ([] , [])
break1 sep (c ∷ cs) =
  if primCharEquality c sep then ([] , cs)
  else (let r = break1 sep cs in (c ∷ fst r , snd r))

lines' : List Char → List String
linesAcc : List Char → List Char → List String
lines' cs = linesAcc cs []
linesAcc [] acc = primStringFromList (reverseL acc) ∷ []
linesAcc (c ∷ cs) acc =
  if primCharEquality c '\n'
  then primStringFromList (reverseL acc) ∷ linesAcc cs []
  else linesAcc cs (c ∷ acc)

-- a stored row "small \t large"; the rewrite rule is large → small
parseRow : String → Maybe Rule
parseRow ln =
  let cs = s2l ln
      br = break1 '\t' cs
      a = primStringFromList (fst br)
      -- second field up to next tab
      br2 = break1 '\t' (snd br)
      b = primStringFromList (fst br2)
  in if isHash cs then nothing
     else if isEmpty cs then nothing
     else combine (parseT a) (parseT b)
  where
    isHash : List Char → Bool
    isHash ('#' ∷ _) = true
    isHash _ = false
    isEmpty : List Char → Bool
    isEmpty [] = true
    isEmpty (_ ∷ _) = false
    combine : Maybe Term → Maybe Term → Maybe Rule
    combine (just l) (just r) = just (l , r)
    combine _ _ = nothing

collectRules : List String → List Rule
collectRules [] = []
collectRules (ln ∷ lns) with parseRow ln
... | just rl = rl ∷ collectRules lns
... | nothing = collectRules lns

-- The Haskell: rw = [ (r,l) | (l,r) <- rules, size r >= size l ].
-- i.e. every stored (l,r) with size r ≥ size l becomes the rule r→l.
orientRW : List Rule → List Rule
orientRW [] = []
orientRW ((l , r) ∷ rls) =
  if sizeT l <= sizeT r
  then (r , l) ∷ orientRW rls
  else orientRW rls

pairEq : Pair → Pair → Bool
pairEq p q = eqT (fst p) (fst q) && eqT (snd p) (snd q)

elemP : Pair → List Pair → Bool
elemP p []       = false
elemP p (q ∷ qs) = pairEq p q || elemP p qs

nubPAcc : List Pair → List Pair → List Pair
nubPAcc seen []       = []
nubPAcc seen (p ∷ ps) with elemP p seen
... | true  = nubPAcc seen ps
... | false = p ∷ nubPAcc (p ∷ seen) ps

nubPairs : List Pair → List Pair
nubPairs xs = nubPAcc [] xs

allCriticalPairs : List Rule → List Pair
allCriticalPairs rw =
  nubPairs (filterL (λ p → notB (eqT (fst p) (snd p)))
    (concatMapL (λ r1 → concatMapL (λ r2 → criticalPairs r1 r2) rw) rw))

nonJoining : List Rule → List Pair → List Pair
nonJoining rw cps =
  nubPairs (filterL (λ p → notB (eqT (fst p) (snd p)))
    (mapL (λ p → (normal rw (fst p) , normal rw (snd p))) cps))

-- stable insertion sort by size(a)+size(b)
insSort : List Pair → List Pair
insertBy : Pair → List Pair → List Pair
insSort [] = []
insSort (p ∷ ps) = insertBy p (insSort ps)
insertBy p [] = p ∷ []
insertBy p (q ∷ qs) with (sizeT (fst p) + sizeT (snd p)) <= (sizeT (fst q) + sizeT (snd q))
... | true  = p ∷ (q ∷ qs)
... | false = q ∷ insertBy p qs

------------------------------------------------------------------------
-- report as one String (pure); IO only prints it
------------------------------------------------------------------------

nl : String
nl = primStringFromList ('\n' ∷ [])

showLine : String → Nat → String
showLine label n = primStringAppend label (primStringAppend (primShowNat n) nl)

pairLine : Pair → String
pairLine p = primStringAppend (render (fst p))
  (primStringAppend (primStringFromList ('\t' ∷ [])) (primStringAppend (render (snd p)) nl))

joinPairs : List Pair → String
joinPairs [] = ""
joinPairs (p ∷ ps) = primStringAppend (pairLine p) (joinPairs ps)

report : String → String
report contents =
  let lns = lines' (s2l contents)
      rules = collectRules lns
      rw = orientRW rules
      cps = allCriticalPairs rw
      nonj = nonJoining rw cps
      sorted = takeL 40 (insSort nonj)
  in primStringAppend (showLine "rules read              : " (lengthL rules))
   (primStringAppend (showLine "oriented for rewriting  : " (lengthL rw))
   (primStringAppend (showLine "critical pairs          : " (lengthL cps))
   (primStringAppend (showLine "NON-JOINING (the gap)   : " (lengthL nonj))
   (primStringAppend nl
   (primStringAppend "-- non-joining pairs, smallest first, in library.terms shape --"
   (primStringAppend nl (joinPairs sorted)))))))

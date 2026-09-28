{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- प्रस्ताव — the proposer is a checked term, and the loop closes
-- through the store.
--
-- TERM.  prastāva, a proposal, that-which-is-set-forth — ordinary
-- ; the compound title is built here.
--
-- WHAT THIS IS.  The machine's four powers are: utter (propose a term
-- to the kernel), judge (the kernel accepts or refuses), keep (append
-- the result to the store), re-read (the store feeds the next
-- utterance).  This module is the UTTER power as a checked term: a total
-- function from the machine's own refusal list (the Sanghatta
-- non-joining pairs, machine/sanghatta-report-2026-08-23.txt (absent from this repository) — the
-- exact theorems the rewriter told itself it needs) to candidate
-- kernel modules.  It is compiled by MAlonzo — the extraction lane
-- this directory already runs (RewriteDynamics → ExtractedRewrite) —
-- and driven by one small unjudged mouth whose only job is IO.
--
-- WHY THIS CLOSES THE LOOP.  This module lives in the store it reads
-- for.  A refusal lands in the store; the next run of the extracted
-- proposer sees it; and because the proposer is itself a term of the
-- store, a future landing may be a stronger proposer — judged by the
-- same kernel as any theorem, extracted, and swapped in.
-- Self-improvement as an ordinary landing, no organ in between.
--
-- The kernel has checked that every function below is total and well-typed,
-- and the refl-pinned examples at the bottom are executable specifications:
-- the parser reads the report's own lines to exactly the intended pairs. The
-- MATHEMATICAL soundness gate is not here and needs not be: every candidate
-- this module utters is judged by the cubical kernel before it can land, so a
-- wrong proposal costs one refusal and nothing else. A pair over more than
-- six variables is refused with its reason.
-- ride the ladder.)      
------------------------------------------------------------------------

module Prastava where

open import Agda.Builtin.Nat using (Nat ; zero ; suc ; _+_ ; _*_ ; _==_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Agda.Builtin.Char using (Char ; primCharEquality)
open import Agda.Builtin.String
  using (String ; primStringToList ; primStringAppend ; primStringEquality)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Agda.Builtin.Sigma using (Σ ; _,_ ; fst ; snd)
open import Agda.Builtin.Equality using (_≡_ ; refl)

-- the term language and the AC classifier live in ONE module shared
-- with the soundness theorem (PrastavaSatya, cubical lane): the same
-- clauses are extracted here and proved about there.  Nothing below
-- respells them.
open import PrastavaHrdaya_TheClassifierHasOneSpellingSharedByProposerAndTheorem

------------------------------------------------------------------------
-- small library, total and closed
------------------------------------------------------------------------

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} → List A → Nat
length [] = 0
length (x ∷ xs) = suc (length xs)

-- if_then_else_ comes from the heart module
elem : Nat → List Nat → Bool
elem n [] = false
elem n (m ∷ ms) = if n == m then true else elem n ms

nub : List Nat → List Nat
nub [] = []
nub (n ∷ ns) = if elem n (nub ns) then nub ns else (n ∷ nub ns)

maxN : Nat → Nat → Nat
maxN zero m = m
maxN (suc n) zero = suc n
maxN (suc n) (suc m) = suc (maxN n m)

maxOf : List Nat → Nat
maxOf [] = 0
maxOf (n ∷ ns) = maxN n (maxOf ns)

ltN : Nat → Nat → Bool
ltN zero zero = false
ltN zero (suc _) = true
ltN (suc _) zero = false
ltN (suc a) (suc b) = ltN a b

infixr 4 _&_
_&_ : String → String → String
_&_ = primStringAppend

concatS : List String → String
concatS [] = ""
concatS (s ∷ ss) = s & concatS ss

Pair : Set → Set → Set
Pair A B = Σ A (λ _ → B)

bindM : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindM nothing _ = nothing
bindM (just a) k = k a

------------------------------------------------------------------------
-- the term language of library.terms (Sym, Tm — imported from the
-- heart: V's variables read x y z u v w, each prime adding six)
------------------------------------------------------------------------
-- the parser: report shape → Tm, recursive descent with fuel.
-- Fuel is the input length plus one; every recursive call consumes at
-- least one character, so the fuel never dries on genuine input — and
-- if it did, the result is `nothing`, a refusal, never a wrong term.
------------------------------------------------------------------------

ch : Char → Char → Bool
ch = primCharEquality

varLetter : Char → Maybe Nat
varLetter c =
  if ch c 'x' then just 0 else
  if ch c 'y' then just 1 else
  if ch c 'z' then just 2 else
  if ch c 'u' then just 3 else
  if ch c 'v' then just 4 else
  if ch c 'w' then just 5 else nothing

primes : List Char → Pair Nat (List Char)
primes ('\'' ∷ cs) = let p = primes cs in (suc (fst p) , snd p)
primes cs = (0 , cs)

binOf : Char → Maybe Sym
binOf c =
  if ch c '+' then just plus else
  if ch c '*' then just times else
  if ch c '-' then just monus else nothing

-- expect a closing/separating character at the head
eat : Char → List Char → Maybe (List Char)
eat c [] = nothing
eat c (d ∷ cs) = if ch c d then just cs else nothing

mutual
  parseTm : Nat → List Char → Maybe (Pair Tm (List Char))
  parseTm zero _ = nothing
  parseTm (suc f) [] = nothing
  parseTm (suc f) ('0' ∷ cs) = just (Z , cs)
  parseTm (suc f) ('s' ∷ '(' ∷ cs) =
    bindM (parseTm f cs) λ p →
    bindM (eat ')' (snd p)) λ rest →
    just (S (fst p) , rest)
  parseTm (suc f) ('l' ∷ 'e' ∷ '(' ∷ cs) = parseBin f leS cs
  parseTm (suc f) ('m' ∷ 'a' ∷ 'x' ∷ '(' ∷ cs) = parseBin f maxS cs
  parseTm (suc f) ('g' ∷ 'c' ∷ 'd' ∷ '(' ∷ cs) = parseBin f gcdS cs
  parseTm (suc f) ('+' ∷ '(' ∷ cs) = parseBin f plus cs
  parseTm (suc f) ('*' ∷ '(' ∷ cs) = parseBin f times cs
  parseTm (suc f) ('-' ∷ '(' ∷ cs) = parseBin f monus cs
  parseTm (suc f) (c ∷ cs) =
    bindM (varLetter c) λ i →
    let p = primes cs in
    just (V (i + 6 * fst p) , snd p)

  parseBin : Nat → Sym → List Char → Maybe (Pair Tm (List Char))
  parseBin f s cs =
    bindM (parseTm f cs) λ a →
    bindM (eat ',' (snd a)) λ rest →
    bindM (parseTm f rest) λ b →
    bindM (eat ')' (snd b)) λ rest' →
    just (Bin s (fst a) (fst b) , rest')

-- one report line: "LHS<TAB>RHS"
splitTab : List Char → Maybe (Pair (List Char) (List Char))
splitTab [] = nothing
splitTab ('\t' ∷ cs) = just ([] , cs)
splitTab (c ∷ cs) =
  bindM (splitTab cs) λ p → just (c ∷ fst p , snd p)

closed : Pair Tm (List Char) → Maybe Tm
closed (t , []) = just t
closed (t , _ ∷ _) = nothing

parseLine : String → Maybe (Pair Tm Tm)
parseLine s =
  bindM (splitTab (primStringToList s)) λ lr →
  bindM (bindM (parseTm (suc (length (fst lr))) (fst lr)) closed) λ l →
  bindM (bindM (parseTm (suc (length (snd lr))) (snd lr)) closed) λ r →
  just (l , r)

------------------------------------------------------------------------
-- the AC classifier.  + and · are associative-commutative in the
-- library (commutativity is literally in library.terms), and plain
-- completion provably diverges on an AC theory (Baader–Nipkow §7;
-- notes/SamataChakra).  A pair whose two sides are equal as AC-canonical
-- forms is an AC rearrangement: true, joinable under completion modulo
-- AC, and the WRONG thing to land as one lemma per shuffle.  The
-- classifier refuses it with the law named, so the store stays clean
-- and the refusal is a statement, not a failure.
-- Its functions (cmpTm, acCanon, eqTm, acShuffle) are imported from
-- the heart module above; PrastavaSatya proves acShuffle sound against
-- eval, so a refusal here is a kernel-judged true equation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- variables of a term, and their display names
------------------------------------------------------------------------

varsOf : Tm → List Nat
varsOf (V i) = i ∷ []
varsOf Z = []
varsOf (S t) = varsOf t
varsOf (Bin _ a b) = varsOf a ++ varsOf b

-- canonicalisation by order of first appearance — the engine's own
-- canonVars discipline, so `x'` alone is index 0, not index six.
posIn : Nat → List Nat → Nat
posIn n [] = 0
posIn n (m ∷ ms) = if n == m then 0 else suc (posIn n ms)

rename : List Nat → Tm → Tm
rename order (V i) = V (posIn i order)
rename order Z = Z
rename order (S t) = S (rename order t)
rename order (Bin s a b) = Bin s (rename order a) (rename order b)

canon : Pair Tm Tm → Pair Tm Tm
canon (l , r) =
  let order = nub (varsOf l ++ varsOf r) in
  (rename order l , rename order r)

varName : Nat → String
varName 0 = "a"
varName 1 = "b"
varName 2 = "c"
varName 3 = "d"
varName 4 = "e"
varName 5 = "f"
varName _ = "?"

------------------------------------------------------------------------
-- the emitter: Tm → cubical Agda syntax.  Self-contained candidates:
-- each module carries its own ∸' / le / max' clauses, so a candidate
-- couples to nothing but the library prelude and checks on any pin.
------------------------------------------------------------------------

emit : Tm → String
emit (V i) = varName i
emit Z = "zero"
emit (S t) = "suc (" & emit t & ")"
emit (Bin plus a b)  = "(" & emit a & " + " & emit b & ")"
emit (Bin times a b) = "(" & emit a & " · " & emit b & ")"
emit (Bin monus a b) = "(" & emit a & " ∸' " & emit b & ")"
emit (Bin leS a b)   = "le (" & emit a & ") (" & emit b & ")"
emit (Bin maxS a b)  = "max' (" & emit a & ") (" & emit b & ")"
emit (Bin gcdS a b)  = "gcd' (" & emit a & ") (" & emit b & ")"

argRange : Nat → List Nat
argRange zero = []
argRange (suc n) = argRange n ++ (n ∷ [])

binder : Nat → String
binder n = "(" & concatS (map (λ i → varName i & " ") (argRange n)) & ": ℕ)"

argsPlain : Nat → String
argsPlain n = concatS (map (λ i → varName i & " ") (argRange n))

argsAt : Nat → Nat → String → String
argsAt n i patt =
  concatS (map (λ j → (if j == i then patt else varName j) & " ") (argRange n))

prelude : String
prelude =
  "open import Cubical.Foundations.Prelude\n"
  & "open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)\n\n"
  & "_∸'_ : ℕ → ℕ → ℕ\n"
  & "n ∸' zero = n\n"
  & "zero ∸' suc _ = zero\n"
  & "suc n ∸' suc m = n ∸' m\n\n"
  & "le : ℕ → ℕ → ℕ\n"
  & "le zero _ = suc zero\n"
  & "le (suc _) zero = zero\n"
  & "le (suc a) (suc b) = le a b\n\n"
  & "max' : ℕ → ℕ → ℕ\n"
  & "max' zero n = n\n"
  & "max' (suc m) zero = suc m\n"
  & "max' (suc m) (suc n) = suc (max' m n)\n\n"
  & "-- Euclidean gcd by subtraction, fuel-typed (the close SanghattaSamapti\n"
  & "-- named as owed): fuel a + b bounds the descent, since each step\n"
  & "-- strictly shrinks the sum while both sides are positive.\n"
  & "mutual\n"
  & "  gcdGo : ℕ → ℕ → ℕ → ℕ → ℕ\n"
  & "  gcdGo f (suc zero) a b = gcdF f a (b ∸' a)\n"
  & "  gcdGo f _ a b = gcdF f (a ∸' b) b\n\n"
  & "  gcdF : ℕ → ℕ → ℕ → ℕ\n"
  & "  gcdF zero a _ = a\n"
  & "  gcdF (suc f) a zero = a\n"
  & "  gcdF (suc f) zero b = b\n"
  & "  gcdF (suc f) (suc a) (suc b) = gcdGo f (le (suc a) (suc b)) (suc a) (suc b)\n\n"
  & "gcd' : ℕ → ℕ → ℕ\n"
  & "gcd' a b = gcdF (a + b) a b\n\n"

header : String → String
header name =
  "{-# OPTIONS --cubical --safe #-}\n"
  & "-- uttered by the checked proposer (formal/executable/Prastava.agda),\n"
  & "-- judged by the kernel before landing; the source pair is a Sanghatta\n"
  & "-- non-joining critical pair — a theorem the rewriter said it needs.\n"
  & "module Prastuta." & name & " where\n" & prelude

nVarsOf : Tm → Tm → Nat
nVarsOf l r =
  if length (varsOf l ++ varsOf r) == 0
  then 0
  else suc (maxOf (varsOf l ++ varsOf r))

sigLine : Nat → Tm → Tm → String
sigLine n l r =
  -- parenthesised: if_then_else_ binds tighter than _&_, so without
  -- them the " → " would ride OUTSIDE the conditional.
  "prastava : " & (if n == 0 then "" else (binder n & " → "))
  & emit l & " ≡ " & emit r & "\n"

reflCandidate : String → Tm → Tm → String
reflCandidate name l r =
  let n = nVarsOf l r in
  header name & sigLine n l r
  & "prastava " & argsPlain n & "= refl\n"

-- case split at variable i with both clauses refl: for pairs where each
-- branch is definitional once the split is made (max'(suc a) 0 = suc a).
splitCandidate : String → Tm → Tm → Nat → String
splitCandidate name l r i =
  let n = nVarsOf l r in
  header name & sigLine n l r
  & "prastava " & argsAt n i "zero" & "= refl\n"
  & "prastava " & argsAt n i ("(suc " & varName i & ")") & "= refl\n"

indCandidate : String → Tm → Tm → Nat → String
indCandidate name l r i =
  let n = nVarsOf l r in
  header name & sigLine n l r
  & "prastava " & argsAt n i "zero" & "= refl\n"
  & "prastava " & argsAt n i ("(suc " & varName i & ")")
  & "= cong suc (prastava " & argsPlain n & ")\n"

------------------------------------------------------------------------
-- the reflection rung: when the two sides share a normal form (nf,
-- the heart), the candidate is not a schema but a PROOF — two
-- applications of the kernel-judged nf-sound (PrastavaSatya) around a
-- definitional middle.  The quoted terms are closed, so the kernel
-- normalises both nf applications itself; the middle holds exactly
-- when the classifier's nfEqual said yes, and if the classifier were
-- wrong the candidate is refused and costs one receipt.
------------------------------------------------------------------------

showIx : Nat → String
showIx 0 = "0"
showIx 1 = "1"
showIx 2 = "2"
showIx 3 = "3"
showIx 4 = "4"
showIx 5 = "5"
showIx _ = "0"

symName : Sym → String
symName plus = "plus"
symName times = "times"
symName monus = "monus"
symName leS = "leS"
symName maxS = "maxS"
symName gcdS = "gcdS"

quoteTm : Tm → String
quoteTm (V i) = "(V " & showIx i & ")"
quoteTm Z = "Z"
quoteTm (S t) = "(S " & quoteTm t & ")"
quoteTm (Bin s a b) =
  "(Bin " & symName s & " " & quoteTm a & " " & quoteTm b & ")"

envLines : Nat → String
envLines n =
  concatS (map (λ i → "  env " & showIx i & " = " & varName i & "\n")
               (argRange n))
  & "  env _ = zero\n"

nfHeader : String → String
nfHeader name =
  "{-# OPTIONS --cubical --safe #-}\n"
  & "-- uttered by the checked proposer: the sides share a normal form\n"
  & "-- (nf, PrastavaHrdaya), so the proof is two applications of the\n"
  & "-- kernel-judged nf-sound (PrastavaSatya) around a definitional middle.\n"
  & "module Prastuta." & name & " where\n"
  & "open import Cubical.Foundations.Prelude\n"
  & "open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)\n"
  & "open import PrastavaHrdaya_TheClassifierHasOneSpellingSharedByProposerAndTheorem\n"
  & "open import PrastavaSatya_TheClassifiersACClaimIsJudgedByTheKernel\n"
  & "  using (eval ; nf-sound ; _∸'_ ; le ; max' ; gcd')\n\n"

nfCandidate : String → Tm → Tm → String
nfCandidate name l r =
  let n = nVarsOf l r in
  nfHeader name & sigLine n l r
  & "prastava " & argsPlain n & "=\n"
  & "  sym (nf-sound env " & quoteTm l & ") ∙ nf-sound env " & quoteTm r & "\n"
  & "  where\n"
  & "  env : ℕ → ℕ\n"
  & envLines n

------------------------------------------------------------------------
-- the split-then-normalise rung — the machine acting on its own
-- vibhaga diagnosis.  When a pair is not nf-equal open but BOTH
-- branches of a case split on some variable are (the zero branch
-- erases; the suc branch unfolds max/le/monus/·/+ on the now
-- suc-headed argument), the candidate is two clauses, each a
-- reflection proof.  The classifier decides per branch BEFORE
-- uttering, so a split candidate is emitted exactly when the checked
-- normaliser says both branches close.
------------------------------------------------------------------------

filterL : {A : Set} → (A → Bool) → List A → List A
filterL p [] = []
filterL p (x ∷ xs) = if p x then (x ∷ filterL p xs) else filterL p xs

splitNfOK : Tm → Tm → Nat → Bool
splitNfOK l r i =
  if nfEqual (substV i Z l) (substV i Z r)
  then nfEqual (substV i (S (V i)) l) (substV i (S (V i)) r)
  else false

-- env for one branch: the split variable reads as the given pattern's
-- denotation (zero, or the suc-bound name), the others as themselves
envLinesAt : Nat → Nat → String → String
envLinesAt n i patt =
  concatS (map (λ j → "  env " & showIx j & " = "
                 & (if j == i then patt else varName j) & "\n")
               (argRange n))
  & "  env _ = zero\n"

splitNfCandidate : String → Tm → Tm → Nat → String
splitNfCandidate name l r i =
  let n = nVarsOf l r in
  let l0 = substV i Z l in
  let r0 = substV i Z r in
  let l1 = substV i (S (V i)) l in
  let r1 = substV i (S (V i)) r in
  nfHeader name & sigLine n l r
  & "prastava " & argsAt n i "zero" & "=\n"
  & "  sym (nf-sound env " & quoteTm l0 & ") ∙ nf-sound env " & quoteTm r0 & "\n"
  & "  where\n"
  & "  env : ℕ → ℕ\n"
  & envLinesAt n i "zero"
  & "prastava " & argsAt n i ("(suc " & varName i & ")") & "=\n"
  & "  sym (nf-sound env " & quoteTm l1 & ") ∙ nf-sound env " & quoteTm r1 & "\n"
  & "  where\n"
  & "  env : ℕ → ℕ\n"
  & envLinesAt n i (varName i)

------------------------------------------------------------------------
-- the proposer.  For one report line and a module name: either a list
-- of candidate module texts (tried in order — the mouth stops at the
-- first the kernel accepts), or a written refusal with its reason.
------------------------------------------------------------------------

data Uttara : Set where
  candidates : List String → Uttara
  refusal    : String → Uttara

proposeParsed : String → Maybe (Pair Tm Tm) → Uttara
proposeParsed name nothing =
  refusal "unparsed: outside the closed signature {0,s,+,*,-,le,max,gcd} over x..w with primes"
proposeParsed name (just lr) =
  let l = fst (canon lr) in
  let r = snd (canon lr) in
  if ltN 6 (nVarsOf l r)
  then refusal "more than six variables: outside the emitter's binder range"
  else if acShuffle l r
  then refusal "AC rearrangement: the sides are equal modulo associativity-commutativity of +/·; the close is completion modulo AC (Peterson-Stickel; notes/SamataChakra), not one lemma per shuffle"
  else if nfEqual l r
  then candidates (reflCandidate name l r ∷ nfCandidate name l r ∷ [])
  else candidates
    (reflCandidate name l r
      ∷ (map (splitNfCandidate name l r)
             (filterL (splitNfOK l r) (nub (varsOf l ++ varsOf r)))
         ++ map (splitCandidate name l r) (nub (varsOf l ++ varsOf r))
         ++ map (indCandidate name l r) (nub (varsOf l ++ varsOf r))))

propose : String → String → Uttara
propose name line = proposeParsed name (parseLine line)

------------------------------------------------------------------------
-- the extraction surface: one flat function the mouth consumes.
-- head "OK" followed by the candidates in order, or head "NO" followed
-- by the written reason.  Builtin lists and strings compile to Haskell
-- lists and Text, so the mouth needs no knowledge of this module's
-- datatypes.
------------------------------------------------------------------------

run : String → String → List String
run name line with propose name line
... | candidates cs = "OK" ∷ cs
... | refusal why   = "NO" ∷ why ∷ []

------------------------------------------------------------------------
-- निदान — the machine names its own disease.  When every candidate for
-- a pair is refused by the kernel, the mouth asks THIS function what
-- transformation the refusal wants, and writes the answer into the
-- receipt.  The residue is thereby machine-labelled: the next organ is
-- specified by the store itself, not by a carrier reading it.
------------------------------------------------------------------------

hasVar : Tm → Bool
hasVar (V _) = true
hasVar Z = false
hasVar (S t) = hasVar t
hasVar (Bin _ a b) = if hasVar a then true else hasVar b

symEq : Sym → Sym → Bool
symEq s s' = is1 (cmpN (symCode s) (symCode s'))

-- an s-node applied to an argument containing a variable: the class of
-- pairs wanting a CASE organ (compare, then split) for that symbol
openUnder : Sym → Tm → Bool
openUnder s (Bin s' a b) =
  if (if symEq s s' then (if hasVar a then true else hasVar b) else false)
  then true
  else (if openUnder s a then true else openUnder s b)
openUnder s (S t) = openUnder s t
openUnder s _ = false

mark : Bool → String → String
mark true tag = tag & " "
mark false _ = ""

diagTm : Tm → Tm → String
diagTm l r =
  let vs = length (nub (varsOf l ++ varsOf r)) in
  let both = λ (s : Sym) → if openUnder s l then true else openUnder s r in
  let d = mark (ltN 1 vs) "dvi-cara:wants-induction-generalised-over-a-second-variable"
        & mark (both maxS) "vibhaga-max:wants-a-case-organ-comparing-the-arguments"
        & mark (both leS) "vibhaga-le:wants-a-case-organ-comparing-the-arguments"
        & mark (both monus) "vibhaga-monus:wants-a-case-organ-comparing-the-arguments"
        & mark (both gcdS) "vibhaga-gcd:wants-the-euclidean-descent-as-a-lemma"
  in if primStringEquality d "" then "ajnata:a-genuinely-new-transformation-is-owed" else d

diag : String → String
diag line with parseLine line
... | nothing = "aparsita:outside-the-signature"
... | just lr = diagTm (fst (canon lr)) (snd (canon lr))

------------------------------------------------------------------------
-- executable specification, pinned by refl: the parser reads the
-- report's own lines to exactly the intended pairs, and the variable
-- census is exact.  The kernel evaluates each parse at check time.
------------------------------------------------------------------------

spec-parse-1 : parseLine "x'\tmax(x',0)" ≡ just (V 6 , Bin maxS (V 6) Z)
spec-parse-1 = refl

spec-parse-2 : parseLine "0\tle(s(y),0)" ≡ just (Z , Bin leS (S (V 1)) Z)
spec-parse-2 = refl

spec-parse-3 : parseLine "x\t*(x,s(0))" ≡ just (V 0 , Bin times (V 0) (S Z))
spec-parse-3 = refl

spec-parse-4 : parseLine "x'\t+(x',*(x',0))"
             ≡ just (V 6 , Bin plus (V 6) (Bin times (V 6) Z))
spec-parse-4 = refl

spec-vars : nub (varsOf (Bin plus (V 0) (Bin times (V 0) Z)) ++ []) ≡ (0 ∷ [])
spec-vars = refl

-- the zero-variable signature is pinned whole: a closed pair's line
-- carries no binder and no arrow.
spec-sig-0 : sigLine 0 Z (S Z) ≡ "prastava : zero ≡ suc (zero)\n"
spec-sig-0 = refl

-- gcd: the fuel-typed definition lives in the candidate prelude (gcdF/gcd'),
-- so gcd pairs ride the same ladder as every other symbol.
spec-gcd-parsed : parseLine "s(y)\tgcd(s(y),0)"
                ≡ just (S (V 1) , Bin gcdS (S (V 1)) Z)
spec-gcd-parsed = refl

-- the AC classifier's receipts: a genuine +-shuffle is recognised, and a
-- pair that differs by real content (an absorbed ·0) is NOT — so the
-- classifier cannot eat a theorem.
spec-ac-yes : acShuffle (Bin plus (V 0) (Bin plus (V 0) (V 1)))
                        (Bin plus (Bin plus (V 0) (V 0)) (V 1)) ≡ true
spec-ac-yes = refl

spec-ac-no : acShuffle (Bin plus (Bin times (V 0) (V 1)) (Bin times (V 0) Z))
                       (Bin times (V 0) (V 1)) ≡ false
spec-ac-no = refl

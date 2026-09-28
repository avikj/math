{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Dviḥpāṭha — the antichain bound on anubandhas is not tight, and what
-- buys the difference is permission to recite a sound twice.
--
-- SOURCE.  Pini, *Adhyy* (~500 BCE), opens with the fourteen
-- Mhevara-stras: the sounds laid in ONE recited line, each stra closed
-- by an anubandha.  A pratyhra names a class as the stretch from a sound
-- to a marker; the formation rule is 1.1.71 dir antyena sahet.  The line
-- is a *pāṭha*, a recitation, and one sound in it is recited TWICE — ha,
-- in sūtra 5 (ha ya va ra Ṭ) and again in sūtra 14 (ha L) — which is why
-- the tradition must say which ha a given pratyhra takes.  *Dvipha*,
-- "twice-recited", is the grammarians' idiom for that (the phenomenon
-- itself: stras 5 and 14).
--
-- WHAT THIS FILE IS ABOUT.  `PratyaharaLaghava_TheMarkerCountIsForcedBy-
-- TheAntichain.agda` (absent from this repository) proves the lower bound: classes ending at one marker
-- form a ⊆-chain, so a ⊆-antichain of width w forces w distinct markers.
-- `markersDistinct` gives markers ≥ width(F) and no more, and a Haskell
-- computation reports width 14 over the 294 classes the iva-stra line can name against
-- width 11 over the ~30 the grammar uses — three markers unforced by the
-- antichain argument.
--
-- WHAT IS PROVED HERE.  The bound is NOT tight, and the gap is exactly the
-- resource `PratyaharaLaghava`'s model does not have.  On an abstract
-- three-sound inventory with the five-class family
--
--     F = { {s₁}, {s₁ s₂}, {s₁ s₂ s₃}, {s₃}, {s₂ s₃} }
--
--   §2  `विस्तारो-द्वयम्` — width(F) = 2: no three members of F are
--       pairwise ⊆-incomparable.  So the antichain bound says: 2 markers.
--   §4  `द्विःपाठं-विना-न-सिध्यति` — EXHAUSTIVE over all 120 arrangements
--       of s₁ s₂ s₃ M₁ M₂: not one names all five classes.  Two markers do
--       not suffice when every sound is recited once.  The bound is not
--       attained.
--   §5  `त्रिभिः-सिध्यति` — three markers do, recited once each:
--       s₃ M₁ s₂ M₂ s₁ M₃.  So the rep-free cost is exactly 3, not 2.
--   §6  `द्विःपाठेन-सिध्यति` — TWO markers suffice the moment a sound may
--       be recited twice: s₃ s₂ s₁ M₁ s₂ s₃ M₂ names all five.  The bound
--       is attained, on the same family, by the same two markers.
--
-- Together: width(F) = 2, and the minimum marker count is 3 without
-- dvipha and 2 with it.  A bound proved in a model where each sound has
-- ONE position measures a different quantity from the one Pini paid.
--
-- WHY THE EXHAUSTION IS COMPLETE (the WLOG, stated because §4 enumerates
-- permutations of exactly five tokens and a reader should not have to
-- trust that).  Let L be any line naming all of F with at most two markers
-- and each sound recited once.  F contains a class meeting each of s₁ s₂
-- s₃, so all three sounds occur in L.  width(F) = 2 with `markersDistinct`
-- forces two distinct markers, so exactly two occur.  Recited-once makes
-- every occurrence unique.  Hence L is a permutation of {s₁ s₂ s₃ M₁ M₂}
-- up to renaming the two markers, and §4 checks all 120 of them.  §3 also
-- checks that the enumeration really has length 120.
--
-- CONVENTION, and it is load-bearing exactly once.  `klass s m` takes the
-- prefix before the FIRST occurrence of m, then the suffix from the LAST
-- occurrence of s inside it — the nearest preceding recitation, which is
-- what makes ha-in-stra-14 reachable at all.  Where every sound is
-- recited once, this agrees with `Sivasutra.from`/`between`'s first-
-- occurrence search, so §4's negative result does not depend on the
-- choice; §6's positive one does, and says so.
--
-- No postulates, no holes, --safe.  Every claim below is `refl`: the
-- enumeration and the class extractor compute.
------------------------------------------------------------------------

module Dvihpatha_TheAntichainBoundIsAttainedOnlyIfASoundMayBeListedTwice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map ; foldr ; length)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing) renaming (rec to mbRec)
open import Cubical.Data.Nat using (ℕ)

------------------------------------------------------------------------
-- §1  Sounds, markers, and the pratyhra extractor.
------------------------------------------------------------------------

data Sym : Type where
  s₁ s₂ s₃  : Sym          -- three abstract sounds
  M₁ M₂ M₃  : Sym          -- three anubandha occurrences

eqSym : Sym → Sym → Bool
eqSym s₁ s₁ = true
eqSym s₂ s₂ = true
eqSym s₃ s₃ = true
eqSym M₁ M₁ = true
eqSym M₂ M₂ = true
eqSym M₃ M₃ = true
eqSym _  _  = false

sounds : List Sym
sounds = s₁ ∷ s₂ ∷ s₃ ∷ []

markers : List Sym
markers = M₁ ∷ M₂ ∷ M₃ ∷ []

-- A class is recorded by which sounds it meets: markers are boundaries and
-- never members, so this drops them with no separate skip step.
data Sig : Type where
  sg : Bool → Bool → Bool → Sig

anyL : {A : Type} → (A → Bool) → List A → Bool
anyL f []       = false
anyL f (x ∷ xs) = f x or anyL f xs

allL : {A : Type} → (A → Bool) → List A → Bool
allL f []       = true
allL f (x ∷ xs) = f x and allL f xs

occurs : Sym → List Sym → Bool
occurs y xs = anyL (eqSym y) xs

sig : List Sym → Sig
sig xs = sg (occurs s₁ xs) (occurs s₂ xs) (occurs s₃ xs)

eqB : Bool → Bool → Bool
eqB true  b = b
eqB false b = not b

eqSig : Sig → Sig → Bool
eqSig (sg a b c) (sg d e f) = eqB a d and (eqB b e and eqB c f)

-- the stretch strictly before the first occurrence of m; nothing if absent
prefixBefore : Sym → List Sym → Maybe (List Sym)
prefixBefore m []       = nothing
prefixBefore m (x ∷ xs) =
  if eqSym x m
  then just []
  else mbRec nothing (λ r → just (x ∷ r)) (prefixBefore m xs)

-- the stretch from the LAST occurrence of s; nothing if absent
suffixFromLast : Sym → List Sym → Maybe (List Sym)
suffixFromLast s []       = nothing
suffixFromLast s (x ∷ xs) =
  mbRec (if eqSym x s then just (x ∷ xs) else nothing) just (suffixFromLast s xs)

klass : Sym → Sym → List Sym → Maybe Sig
klass s m line =
  mbRec nothing
        (λ p → mbRec nothing (λ q → just (sig q)) (suffixFromLast s p))
        (prefixBefore m line)

names : List Sym → Sig → Bool
names line t =
  anyL (λ s → anyL (λ m → mbRec false (λ u → eqSig u t) (klass s m line)) markers) sounds

------------------------------------------------------------------------
-- §2  The family, and its ⊆-antichain width is two.
--
--   F = { {s₁}, {s₁ s₂}, {s₁ s₂ s₃}, {s₃}, {s₂ s₃} }
--
-- Two chains: {s₁} ⊂ {s₁ s₂} ⊂ {s₁ s₂ s₃} and {s₃} ⊂ {s₂ s₃}.  The check
-- below is the width claim itself and not a picture of it: over all 125
-- ordered triples from F, any triple of pairwise distinct members has a
-- comparable pair.  So no antichain of size three exists, and
-- `markersDistinct` (PratyaharaLaghava §TWO) forces exactly two markers
-- and no more.
------------------------------------------------------------------------

family : List Sig
family =  sg true  false false            -- {s₁}
       ∷  sg true  true  false            -- {s₁ s₂}
       ∷  sg true  true  true             -- {s₁ s₂ s₃}
       ∷  sg false false true             -- {s₃}
       ∷  sg false true  true             -- {s₂ s₃}
       ∷ []

impl : Bool → Bool → Bool
impl a b = not a or b

sub : Sig → Sig → Bool
sub (sg a b c) (sg d e f) = impl a d and (impl b e and impl c f)

comparable : Sig → Sig → Bool
comparable p q = sub p q or sub q p

विस्तारो-द्वयम् : allL (λ p → allL (λ q → allL (λ r →
                    if (not (eqSig p q) and (not (eqSig p r) and not (eqSig q r)))
                    then (comparable p q or (comparable p r or comparable q r))
                    else true) family) family) family
                  ≡ true
विस्तारो-द्वयम् = refl

-- and the width is not one: two members are genuinely incomparable
द्वयं-न-एकम् : comparable (sg true true false) (sg false true true) ≡ false
द्वयं-न-एकम् = refl

------------------------------------------------------------------------
-- §3  Every arrangement of the five tokens.
------------------------------------------------------------------------

insertAll : Sym → List Sym → List (List Sym)
insertAll x []       = (x ∷ []) ∷ []
insertAll x (y ∷ ys) = (x ∷ y ∷ ys) ∷ map (y ∷_) (insertAll x ys)

concatMapL : {A B : Type} → (A → List B) → List A → List B
concatMapL f = foldr (λ x acc → f x ++ acc) []

perms : List Sym → List (List Sym)
perms []       = [] ∷ []
perms (x ∷ xs) = concatMapL (insertAll x) (perms xs)

tokens : List Sym
tokens = s₁ ∷ s₂ ∷ s₃ ∷ M₁ ∷ M₂ ∷ []

-- the enumeration is complete: 5! lines, none omitted
पूर्णा-गणना : length (perms tokens) ≡ 120
पूर्णा-गणना = refl

represents : List Sym → Bool
represents line = allL (names line) family

------------------------------------------------------------------------
-- §4  Recited once, two anubandhas do not suffice.  The bound is not
--     attained, and this is the whole content of the file.
------------------------------------------------------------------------

द्विःपाठं-विना-न-सिध्यति : allL (λ l → not (represents l)) (perms tokens) ≡ true
द्विःपाठं-विना-न-सिध्यति = refl

------------------------------------------------------------------------
-- §5  Recited once, three anubandhas do.  So the cost without dvipha
--     is exactly three, one above the antichain bound.
------------------------------------------------------------------------

त्रिपाठः : List Sym
त्रिपाठः = s₃ ∷ M₁ ∷ s₂ ∷ M₂ ∷ s₁ ∷ M₃ ∷ []

त्रिभिः-सिध्यति : represents त्रिपाठः ≡ true
त्रिभिः-सिध्यति = refl

------------------------------------------------------------------------
-- §6  Recited twice, two anubandhas suffice — s₂ and s₃ each said again,
--     which is the ha of stras 5 and 14 in the small.  Same family, same
--     two markers, and now the bound is attained.
------------------------------------------------------------------------

द्विःपाठः : List Sym
द्विःपाठः = s₃ ∷ s₂ ∷ s₁ ∷ M₁ ∷ s₂ ∷ s₃ ∷ M₂ ∷ []

द्विःपाठेन-सिध्यति : represents द्विःपाठः ≡ true
द्विःपाठेन-सिध्यति = refl

-- and it is the second recitation that does it: the line's own prefix,
-- which is §6 with the repeated sounds removed, is one of the 120 and so
-- fails by §4.  Named here so the difference is a term and not a remark.
लुप्तद्विःपाठः : List Sym
लुप्तद्विःपाठः = s₃ ∷ s₂ ∷ s₁ ∷ M₁ ∷ M₂ ∷ []

लोपे-न-सिध्यति : represents लुप्तद्विःपाठः ≡ false
लोपे-न-सिध्यति = refl

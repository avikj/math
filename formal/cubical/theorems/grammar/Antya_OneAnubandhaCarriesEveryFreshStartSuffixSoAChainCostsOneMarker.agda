{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Antya — one anubandha carries every fresh-start suffix of its stretch.
-- A whole ⊆-chain of classes costs ONE marker, for chains of any length,
-- over any alphabet.  The reason under Dvipha's exhaustion.
--
-- SOURCE.  Pini, *Adhyy* 1.1.71, dir antyena sahet: the initial
-- (di), taken together with the final (antya) which is an it, denotes
-- itself and what lies between.  The marker is the *antya*.  This file is
-- about how much ONE antya can denote.
--
-- WHAT CALLED THIS FILE.  `Dvihpatha_TheAntichainBoundIsAttainedOnlyIf-
-- ASoundMayBeListedTwice.agda` (absent from this repository) settles a five-class family by checking all
-- 120 arrangements: ⊆-width two, cost three recited-once, cost two once a
-- sound may be recited twice.  That is an instance and it is decided, but
-- an exhaustion says nothing about a sixth class or a fourth sound.  The
-- general fact it is an instance of is here, and it needs no enumeration:
--
--   §3  `स्वच्छादिः-अन्त्येन` — for any alphabet A with a boolean equality
--       reflexive on the diagonal, any stretch written `p ++ s ∷ q` and
--       any marker m fresh in that stretch:  if s does not recur in q,
--       then `klass s m` returns exactly `s ∷ q`.
--
--   So EVERY suffix of the stretch whose first sound does not recur later
--   in the stretch is a class of the single marker m.  A stretch with n
--   such positions gives n classes on one antya, and they are nested by
--   construction — each is a suffix of the next — which is
--   `PratyaharaLaghava.sharedEnd→comparable` arriving again from the other
--   side.  A ⊆-chain of length n costs one marker, not n.
--
--   §4  the two hypotheses are each load-bearing, shown by a term:
--       recurrence of s inside q moves the answer to a later block
--       (`स्वच्छत्वं-आवश्यकम्`), and a marker occurring earlier truncates
--       the stretch (`अन्त्यस्य-स्वच्छत्वम्`).  Neither is decoration.
--
--   §5  the general extractor at A := Dvipha's Sym IS Dvipha's
--       extractor, pointwise (`समानम्`), so §3 applies to the checked
--       instance and does not merely resemble it.  §6 reads that instance
--       back through §3: the two-marker twice-recited line is two stretches
--       carrying a 3-chain and a 2-chain, and §3 predicts all five classes
--       with no enumeration.
--
-- WHAT THIS SETTLES, and it is the point of the file.  With repetition
-- unrestricted, a family covered by w chains is named by w markers: lay
-- each chain's stretch down in order, close it with its own antya, and §3
-- delivers that chain's whole nesting from that one antya.  Since sounds
-- may recur across stretches and §3 asks only for freshness WITHIN a
-- stretch, the stretches never interfere.  With Dilworth's theorem,
-- chain-cover number equals ⊆-width, and `PratyaharaLaghava.markersDistinct`
-- gives the matching lower bound.  So the antichain bound is exactly the
-- answer when repetition is free, and the entire content of the
-- iva-stra problem is the economy of repetition.  Pini's line recites
-- one sound twice.
--
-- DUPLICATION, declared.  `prefixBefore` / `suffixFromLast` / `klass` are
-- restated here over an abstract alphabet rather than imported, because
-- Dvipha's are monomorphic in its own `Sym`.  §5 proves the two agree
-- pointwise, so this is a generalisation and not a fork.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module Antya_OneAnubandhaCarriesEveryFreshStartSuffixSoAChainCostsOneMarker where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_ ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing) renaming (rec to mbRec)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)

open import Dvihpatha_TheAntichainBoundIsAttainedOnlyIfASoundMayBeListedTwice
  using (Sym ; s₁ ; s₂ ; s₃ ; M₁ ; M₂ ; M₃ ; eqSym ; द्विःपाठः)
  renaming ( prefixBefore   to prefixBefore⋆
           ; suffixFromLast to suffixFromLast⋆
           ; klass          to klass⋆
           ; sig            to sig⋆ )

private
  variable
    A : Type₀

------------------------------------------------------------------------
-- §1  Two Bool facts, so the case splits below are terms and not appeals.
------------------------------------------------------------------------

or-false₁ : (a b : Bool) → (a or b) ≡ false → a ≡ false
or-false₁ false b _ = refl
or-false₁ true  b p = ⊥rec (true≢false p)

or-false₂ : (a b : Bool) → (a or b) ≡ false → b ≡ false
or-false₂ false b p = p
or-false₂ true  b p = ⊥rec (true≢false p)

------------------------------------------------------------------------
-- §2  The extractor over an abstract alphabet.  `mem` tests the element
--     against the target in the SAME orientation the extractor uses, so no
--     symmetry of the boolean equality is ever needed — and indeed the
--     only property assumed anywhere below is reflexivity on the diagonal.
------------------------------------------------------------------------

module Extractor (eq : A → A → Bool) where

  anyL : (A → Bool) → List A → Bool
  anyL f []       = false
  anyL f (x ∷ xs) = f x or anyL f xs

  -- does the target y occur in xs?
  mem : A → List A → Bool
  mem y xs = anyL (λ x → eq x y) xs

  -- the stretch strictly before the first occurrence of m
  prefixBefore : A → List A → Maybe (List A)
  prefixBefore m []       = nothing
  prefixBefore m (x ∷ xs) =
    if eq x m
    then just []
    else mbRec nothing (λ r → just (x ∷ r)) (prefixBefore m xs)

  -- the stretch from the LAST occurrence of s: the nearest preceding
  -- recitation, which is what makes a twice-recited sound reachable at all
  suffixFromLast : A → List A → Maybe (List A)
  suffixFromLast s []       = nothing
  suffixFromLast s (x ∷ xs) =
    mbRec (if eq x s then just (x ∷ xs) else nothing) just (suffixFromLast s xs)

  klass : A → A → List A → Maybe (List A)
  klass s m line =
    mbRec nothing
          (λ p → suffixFromLast s p)
          (prefixBefore m line)

------------------------------------------------------------------------
-- §3  The theorem.  Only reflexivity of `eq` on the diagonal is assumed.
------------------------------------------------------------------------

module Reason (eq : A → A → Bool) (eq-refl : (x : A) → eq x x ≡ true) where

  open Extractor eq public

  -- a target absent from a stretch has no last occurrence in it
  नास्ति-अन्तिमः : (s : A) (q : List A) → mem s q ≡ false → suffixFromLast s q ≡ nothing
  नास्ति-अन्तिमः s []      _ = refl
  नास्ति-अन्तिमः s (y ∷ q) h =
      cong (mbRec (if eq y s then just (y ∷ q) else nothing) just)
           (नास्ति-अन्तिमः s q (or-false₂ (eq y s) (mem s q) h))
    ∙ cong (λ b → if b then just (y ∷ q) else nothing)
           (or-false₁ (eq y s) (mem s q) h)

  -- FRESH START.  If s does not recur to the right of the marked position,
  -- the nearest-preceding search lands exactly there — whatever stands to
  -- the left, however many times s was recited earlier.
  स्वच्छादेः-पश्चात् : (s : A) (p q : List A) → mem s q ≡ false
                    → suffixFromLast s (p ++ s ∷ q) ≡ just (s ∷ q)
  स्वच्छादेः-पश्चात् s []      q h =
      cong (mbRec (if eq s s then just (s ∷ q) else nothing) just)
           (नास्ति-अन्तिमः s q h)
    ∙ cong (λ b → if b then just (s ∷ q) else nothing) (eq-refl s)
  स्वच्छादेः-पश्चात् s (x ∷ p) q h =
      cong (mbRec (if eq x s then just (x ∷ (p ++ s ∷ q)) else nothing) just)
           (स्वच्छादेः-पश्चात् s p q h)

  -- FRESH MARKER.  If m does not occur inside the stretch, the first-
  -- occurrence search for m cuts exactly at the antya that closes it.
  अन्त्ये-छेदः : (m : A) (p r : List A) → mem m p ≡ false
              → prefixBefore m (p ++ m ∷ r) ≡ just p
  अन्त्ये-छेदः m []      r _ =
    cong (λ b → if b then just [] else mbRec nothing (λ w → just (m ∷ w)) (prefixBefore m r))
         (eq-refl m)
  अन्त्ये-छेदः m (x ∷ p) r h =
      cong (λ b → if b then just []
                  else mbRec nothing (λ w → just (x ∷ w)) (prefixBefore m (p ++ m ∷ r)))
           (or-false₁ (eq x m) (mem m p) h)
    ∙ cong (mbRec nothing (λ w → just (x ∷ w)))
           (अन्त्ये-छेदः m p r (or-false₂ (eq x m) (mem m p) h))

  -- THE STATEMENT.  Any stretch, split anywhere at a sound that does not
  -- recur later in it, closed by an antya fresh to it: the pratyhra is
  -- exactly the suffix.  One antya, every fresh-start position, no bound
  -- on how many.  The classes so named are suffixes of one stretch, hence
  -- ⊆-nested — a chain of any length on ONE marker.
  स्वच्छादिः-अन्त्येन : (s m : A) (p q r : List A)
                     → mem s q ≡ false
                     → mem m (p ++ s ∷ q) ≡ false
                     → klass s m ((p ++ s ∷ q) ++ m ∷ r) ≡ just (s ∷ q)
  स्वच्छादिः-अन्त्येन s m p q r hs hm =
      cong (mbRec nothing (λ w → suffixFromLast s w))
           (अन्त्ये-छेदः m (p ++ s ∷ q) r hm)
    ∙ स्वच्छादेः-पश्चात् s p q hs

------------------------------------------------------------------------
-- §4  Both hypotheses are load-bearing, and here is why, as terms rather
--     than as a caution.  Instantiated at Dvipha's alphabet.
------------------------------------------------------------------------

eqSym-refl : (x : Sym) → eqSym x x ≡ true
eqSym-refl s₁ = refl
eqSym-refl s₂ = refl
eqSym-refl s₃ = refl
eqSym-refl M₁ = refl
eqSym-refl M₂ = refl
eqSym-refl M₃ = refl

open Reason eqSym eqSym-refl

-- Drop freshness of the start: s₂ recurs later in the stretch, and the
-- class is the LATER block, not the one the split names.  The theorem does
-- not merely fail to apply; the answer moves.
स्वच्छत्वं-आवश्यकम् : klass s₂ M₁ (s₂ ∷ s₁ ∷ s₂ ∷ s₃ ∷ M₁ ∷ [])
                    ≡ just (s₂ ∷ s₃ ∷ [])
स्वच्छत्वं-आवश्यकम् = refl

-- Drop freshness of the antya: M₁ already stands inside the stretch, and
-- the cut happens at the earlier occurrence, truncating it.
अन्त्यस्य-स्वच्छत्वम् : klass s₁ M₁ (s₁ ∷ M₁ ∷ s₂ ∷ s₃ ∷ M₁ ∷ [])
                      ≡ just (s₁ ∷ [])
अन्त्यस्य-स्वच्छत्वम् = refl

------------------------------------------------------------------------
-- §5  The general extractor at this alphabet IS Dvipha's, pointwise.
--     So §3 governs the checked instance rather than resembling it.
------------------------------------------------------------------------

समानम्-अन्तिमः : (s : Sym) (xs : List Sym) → suffixFromLast s xs ≡ suffixFromLast⋆ s xs
समानम्-अन्तिमः s []       = refl
समानम्-अन्तिमः s (x ∷ xs) =
  cong (mbRec (if eqSym x s then just (x ∷ xs) else nothing) just) (समानम्-अन्तिमः s xs)

समानम्-छेदः : (m : Sym) (xs : List Sym) → prefixBefore m xs ≡ prefixBefore⋆ m xs
समानम्-छेदः m []       = refl
समानम्-छेदः m (x ∷ xs) =
  cong (λ w → if eqSym x m then just [] else mbRec nothing (λ r → just (x ∷ r)) w)
       (समानम्-छेदः m xs)

------------------------------------------------------------------------
-- §6  Dvipha's twice-recited line, read through §3 instead of through
--     the enumeration.  The line is
--
--         s₃ s₂ s₁ M₁ s₂ s₃ M₂
--
--     two stretches: `s₃ s₂ s₁` closed by M₁, and `s₃ s₂ s₁ M₁ s₂ s₃`
--     closed by M₂.  The first has three fresh-start positions, the second
--     two — because s₂ and s₃ were recited again, which is exactly what
--     makes their earlier occurrences stop being fresh and their later
--     ones start being.  Three classes plus two classes, on two antyas:
--     a 3-chain and a 2-chain, which is the family Dvipha names.
--
--     Each line below is §3 applied with p, q, r read off the line; the
--     `refl`s are the hypotheses discharged by computation.
------------------------------------------------------------------------

-- first stretch, three fresh starts, one antya M₁
कक्ष्या-प्रथमा-त्रिपदा-आदौ : klass s₃ M₁ द्विःपाठः ≡ just (s₃ ∷ s₂ ∷ s₁ ∷ [])
कक्ष्या-प्रथमा-त्रिपदा-आदौ = स्वच्छादिः-अन्त्येन s₃ M₁ [] (s₂ ∷ s₁ ∷ []) (s₂ ∷ s₃ ∷ M₂ ∷ []) refl refl

कक्ष्या-प्रथमा-द्विपदा : klass s₂ M₁ द्विःपाठः ≡ just (s₂ ∷ s₁ ∷ [])
कक्ष्या-प्रथमा-द्विपदा = स्वच्छादिः-अन्त्येन s₂ M₁ (s₃ ∷ []) (s₁ ∷ []) (s₂ ∷ s₃ ∷ M₂ ∷ []) refl refl

कक्ष्या-प्रथमा-एकपदा : klass s₁ M₁ द्विःपाठः ≡ just (s₁ ∷ [])
कक्ष्या-प्रथमा-एकपदा = स्वच्छादिः-अन्त्येन s₁ M₁ (s₃ ∷ s₂ ∷ []) [] (s₂ ∷ s₃ ∷ M₂ ∷ []) refl refl

-- second stretch, two fresh starts, one antya M₂.  The earlier recitations
-- of s₂ and s₃ sit in `p` and are simply passed over: §3 asks nothing of p.
कक्ष्या-द्वितीया-द्विपदा : klass s₂ M₂ द्विःपाठः ≡ just (s₂ ∷ s₃ ∷ [])
कक्ष्या-द्वितीया-द्विपदा = स्वच्छादिः-अन्त्येन s₂ M₂ (s₃ ∷ s₂ ∷ s₁ ∷ M₁ ∷ []) (s₃ ∷ []) [] refl refl

कक्ष्या-द्वितीया-एकपदा : klass s₃ M₂ द्विःपाठः ≡ just (s₃ ∷ [])
कक्ष्या-द्वितीया-एकपदा = स्वच्छादिः-अन्त्येन s₃ M₂ (s₃ ∷ s₂ ∷ s₁ ∷ M₁ ∷ s₂ ∷ []) [] [] refl refl

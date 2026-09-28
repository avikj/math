{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheSharedPreambleIsACommonPrefixNotACommonSet
--
-- `interactive/TraceLibrary.hs` (absent from this repository) computes the shared helper preamble of its
-- trace records as `foldr1 lcp` — the longest common PREFIX.
--
-- Why the prefix and not the intersection is the right meet, checked:
--
--   * the common prefix IS the greatest common prefix (§2), so `lcp` is
--     a meet and not a heuristic;
--   * the common SET is not a preamble at all (§3) — two records can
--     share every declaration and have empty common prefix, and any
--     ordering of the shared set fails to be a prefix of one of them.
--
-- That second half is what makes the choice forced rather than
-- conservative: a preamble is a sequence whose later lemmas may cite
-- earlier ones, so a set of declarations is not a preamble until it is
-- ordered, and no single ordering serves two records that disagree.
--
-- The declaration names below —
-- `addZero`, `addSuc` — are that file's own, and `addZero : (a : ℕ) →
-- (a + zero) ≡ a` is the lemma its header says every record carries.
--
-- ADJACENT AND NOT MERGED.  `Anuvrtti` proves that a
-- measure sensitive to inheritance does not descend to the rule SET, and
-- §3 here is the same shape one level down — order carrying what the set
-- does not.  They are different statements about different objects and
-- neither derives the other: Anuvrtti is about a cost failing to factor
-- through `asSet`; §3 is about a common set failing to BE a preamble.
------------------------------------------------------------------------

module TheSharedPreambleIsACommonPrefixNotACommonSet where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  Declarations, preambles, and being a prefix
------------------------------------------------------------------------

data Decl : Type where
  addZero addSuc : Decl

private
  isAddZero : Decl → Type
  isAddZero addZero = Unit
  isAddZero addSuc  = ⊥

addZero≢addSuc : ¬ (addZero ≡ addSuc)
addZero≢addSuc p = transport (cong isAddZero p) tt

Preamble : Type
Preamble = List Decl

Prefix : Preamble → Preamble → Type
Prefix []       _        = Unit
Prefix (_ ∷ _)  []       = ⊥
Prefix (x ∷ xs) (y ∷ ys) = (x ≡ y) × Prefix xs ys

------------------------------------------------------------------------
-- 2.  The longest common prefix is a meet
------------------------------------------------------------------------

lcp : Preamble → Preamble → Preamble
lcp []              _               = []
lcp (_ ∷ _)         []              = []
lcp (addZero ∷ xs) (addZero ∷ ys)   = addZero ∷ lcp xs ys
lcp (addSuc  ∷ xs) (addSuc  ∷ ys)   = addSuc  ∷ lcp xs ys
lcp (addZero ∷ _)  (addSuc  ∷ _)    = []
lcp (addSuc  ∷ _)  (addZero ∷ _)    = []

lcpPrefixLeft : (xs ys : Preamble) → Prefix (lcp xs ys) xs
lcpPrefixLeft []              _               = tt
lcpPrefixLeft (_ ∷ _)         []              = tt
lcpPrefixLeft (addZero ∷ xs) (addZero ∷ ys)   = refl , lcpPrefixLeft xs ys
lcpPrefixLeft (addSuc  ∷ xs) (addSuc  ∷ ys)   = refl , lcpPrefixLeft xs ys
lcpPrefixLeft (addZero ∷ _)  (addSuc  ∷ _)    = tt
lcpPrefixLeft (addSuc  ∷ _)  (addZero ∷ _)    = tt

lcpPrefixRight : (xs ys : Preamble) → Prefix (lcp xs ys) ys
lcpPrefixRight []              _              = tt
lcpPrefixRight (_ ∷ _)         []             = tt
lcpPrefixRight (addZero ∷ xs) (addZero ∷ ys)  = refl , lcpPrefixRight xs ys
lcpPrefixRight (addSuc  ∷ xs) (addSuc  ∷ ys)  = refl , lcpPrefixRight xs ys
lcpPrefixRight (addZero ∷ _)  (addSuc  ∷ _)   = tt
lcpPrefixRight (addSuc  ∷ _)  (addZero ∷ _)   = tt

-- and it is the GREATEST such: any common prefix is a prefix of it
lcpGreatest :
  (r xs ys : Preamble) → Prefix r xs → Prefix r ys → Prefix r (lcp xs ys)
lcpGreatest []       _               _               _ _ = tt
lcpGreatest (_ ∷ _)  []              _               p _ = p
lcpGreatest (_ ∷ _)  (_ ∷ _)         []              _ q = q
lcpGreatest (addZero ∷ r) (addZero ∷ xs) (addZero ∷ ys) (_ , p) (_ , q) =
  refl , lcpGreatest r xs ys p q
lcpGreatest (addSuc ∷ r)  (addSuc ∷ xs)  (addSuc ∷ ys)  (_ , p) (_ , q) =
  refl , lcpGreatest r xs ys p q
lcpGreatest (addZero ∷ _) (addSuc ∷ _)   _              (e , _) _ =
  ⊥.rec (addZero≢addSuc e)
lcpGreatest (addSuc ∷ _)  (addZero ∷ _)  _              (e , _) _ =
  ⊥.rec (addZero≢addSuc (sym e))
lcpGreatest (addZero ∷ _) (addZero ∷ _)  (addSuc ∷ _)   _ (e , _) =
  ⊥.rec (addZero≢addSuc e)
lcpGreatest (addSuc ∷ _)  (addSuc ∷ _)   (addZero ∷ _)  _ (e , _) =
  ⊥.rec (addZero≢addSuc (sym e))

------------------------------------------------------------------------
-- 3.  The common SET is not a preamble
--
-- Two records carrying exactly the same two declarations, in opposite
-- orders.  Their common prefix is empty, and neither ordering of the
-- shared pair is a prefix of both.
------------------------------------------------------------------------

recordOne recordTwo : Preamble
recordOne = addZero ∷ addSuc ∷ []
recordTwo = addSuc ∷ addZero ∷ []

commonPrefixIsEmpty : lcp recordOne recordTwo ≡ []
commonPrefixIsEmpty = refl

neitherOrderingServesBoth :
    (¬ Prefix recordOne recordTwo)
  × (¬ Prefix recordTwo recordOne)
neitherOrderingServesBoth =
    (λ p → addZero≢addSuc (p .fst))
  , (λ p → addZero≢addSuc (sym (p .fst)))

------------------------------------------------------------------------
-- 4.  The reading
--
-- §2 says `foldr1 lcp` is not a conservative guess: it computes the
-- greatest object of the right kind.  §3 says the tempting alternative —
-- take the declarations both records share — is not an object of that
-- kind at all, because a preamble is a SEQUENCE and a set has to be
-- ordered before it can be one.  Two records sharing every declaration
-- can share no prefix.
------------------------------------------------------------------------

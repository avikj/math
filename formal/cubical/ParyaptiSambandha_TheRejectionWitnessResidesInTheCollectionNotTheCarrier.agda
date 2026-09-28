{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ParyaptiSambandha_TheRejectionWitnessResidesInTheCollectionNotTheCarrier
--
--
-- **paryāpti-sambandha** — the relation of complete occurrence — is
-- Navya-Nyya's answer to a question about WHERE a property resides.
-- Number beyond unity (sakhy: dvitva, tritva) does not reside in each
-- member of a collection distributively; "this pot is two" is false of
-- every pot.  It resides in the collection TAKEN AS A WHOLE, and the
-- relation by which it does so is parypti.  The apparatus naming the
-- slots — pratiyogin (counterpositive: WHAT is absent), anuyogin
-- (locus), avacchedaka (delimitor: under which qualification) — is
-- Gagea, *Tattvacintmai*, c. 1325.  The parypti treatment of
-- number is developed by Raghuntha iromai, *Padrthatattvanirpaa*,
-- c. 1500, and by Gaddhara after him.
--
-- ────────────────────────────────────────────────────────────────────
-- RELATED MODULES, none re-derived here
--
--   `formal/cubical/NaturalMachine/Abhava.agda`, `notes/NO_BARE_ABSENCES.md` (absent from this repository)
--       — abhāva with pratiyogin; the absence tower; `dec-collapses`.
--   `formal/cubical/AbhavaAvacchedaka.agda`
--       — the avacchedaka as a genuine dependent binder, load-bearing.
--   `notes/EVERY_OBSTRUCTION_HERE_IS_EXACT.md` (absent from this repository)
--       — **withdraws** Abhava's reading: `¬-always-stable` needs no
--         hypothesis, so the absence tower is two-tall for every `A`,
--         and decidability lands on the PRATIYOGIN, not on the absence.
--   `NaturalMachine.WhereTheTowerCanStillBeThree` §5
--       — hence the live question is Σ-SHAPED pratiyogins: "a decidable
--         Σ is stable, so the floor's stability is exactly a SEARCH
--         question."
--   `NaturalMachine.CountingIsWhatDecidableEqualityBuys…`
--       — proves `Perm xs ys → count a xs ≡ count a ys`, and states that
--         the converse "must BUILD a permutation … and that search is
--         where finiteness and decidability do real work."
--
-- This file answers, on ONE
-- object: for a Σ-shaped pratiyogin, WHAT BOUNDS THE SEARCH?
--
-- ────────────────────────────────────────────────────────────────────
-- THE OBJECT (frontier: combinatorics of sub-multiset matching with
-- residue — why the residue is sound)
--
-- `xs ⊑ ys` — every element of the multiset `xs` is matched to a
-- DISTINCT occurrence in `ys`.  A *residue test* rejects candidates
-- cheaply: map both sides into a commutative monoid by a homomorphism
-- and compare.  The received account of why such a test is sound is a
-- collision estimate (fingerprinting: a hash can only cause a false
-- ACCEPT, and here is the bound).
--
-- **§1 says the estimate is buying nothing.**  Soundness is the
-- homomorphism property and only that: `⊑-sound` takes NO decidable
-- equality, NO finiteness of the carrier, NO injectivity of the residue,
-- and NO order on the monoid — the order it produces is the ALGEBRAIC
-- one and it hands back the QUOTIENT as an explicit witness.  Every
-- estimate in that literature is buying COMPLETENESS.
--
-- **§1b prices that, and the price is sharp.**  If the residue monoid is
-- a GROUP, the quotient always exists, so `residue-rejects` is VACUOUS —
-- a group-valued residue can never reject a containment, only an
-- equality of residues.  So the received "the fingerprint rejects, hence
-- no match" is, for every group-valued fingerprint, a rejection of a
-- DIFFERENT absence: its pratiyogin is a residue class, not an element.
-- Soundness's whole content is therefore *which* monoid, and this is
-- checked, not asserted.
--
-- **§2–§4 say where the cost actually sits.**  The counterpositive of a
-- rejection — `Σ[ a ∈ A ] count a ys < count a xs` — is Σ-shaped and
-- ranges over the whole carrier `A`, which may be infinite and is not
-- assumed searchable.  `paryāpti` proves that Σ has the same inhabitants
-- as the one delimited to membership in `xs`.  The unbounded existential
-- over the carrier collapses to a bounded one over the collection; only
-- then is it decidable, and only then is Markov's principle for it
-- DISCHARGED rather than assumed (§4).
--
-- One sentence: **soundness of the residue costs nothing; extracting a
-- witness from its failure costs exactly the delimitor.**
------------------------------------------------------------------------

module ParyaptiSambandha_TheRejectionWitnessResidesInTheCollectionNotTheCarrier where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ)
open import Cubical.Data.Nat.Order
  using (_≤_ ; _<_ ; zero-≤ ; suc-≤-suc ; ≤-trans ; ¬-<-zero ; ¬m<m ; <Dec)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty as Empty using (⊥ ; ⊥*)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary
  using (¬_ ; Dec ; yes ; no ; Discrete ; Stable ; Dec→Stable ; mapDec)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 0.  The relation: sub-multiset containment, by matching each element
--     of `xs` to a DISTINCT occurrence in `ys`.
--
--     `Remove a ys ys'` — `ys'` is `ys` with one occurrence of `a`
--     deleted.  No decidable equality anywhere: the occurrence is
--     EXHIBITED, never found.
------------------------------------------------------------------------

module _ {A : Type ℓ} where

  data Remove (a : A) : List A → List A → Type ℓ where
    rHere  : {ys : List A} → Remove a (a ∷ ys) ys
    rThere : {y : A} {ys ys' : List A}
           → Remove a ys ys' → Remove a (y ∷ ys) (y ∷ ys')

  data _⊑_ : List A → List A → Type ℓ where
    ⊑nil  : {ys : List A} → [] ⊑ ys
    ⊑cons : {x : A} {xs ys ys' : List A}
          → Remove x ys ys' → xs ⊑ ys' → (x ∷ xs) ⊑ ys

------------------------------------------------------------------------
-- 1.  SOUNDNESS IS THE HOMOMORPHISM PROPERTY, AND NOTHING ELSE.
--
--     Read the hypotheses of this module: a commutative monoid and a map
--     `A → Carrier`.  No `Discrete A`, no finiteness, no order (the
--     order is the algebraic one, produced), no injectivity.
------------------------------------------------------------------------

record CommMonoid (ℓ'' : Level) : Type (ℓ-suc ℓ'') where
  field
    Carrier : Type ℓ''
    ε       : Carrier
    _·_     : Carrier → Carrier → Carrier
    ·assoc  : (x y z : Carrier) → (x · y) · z ≡ x · (y · z)
    ·comm   : (x y : Carrier) → x · y ≡ y · x
    ·unitl  : (x : Carrier) → ε · x ≡ x

module Residue {A : Type ℓ} (M : CommMonoid ℓ') (φ : A → CommMonoid.Carrier M) where
  open CommMonoid M

  -- the residue: the free-commutative-monoid fold.  This IS the
  -- homomorphism hypothesis, discharged by construction.
  Φ : List A → Carrier
  Φ []       = ε
  Φ (x ∷ xs) = φ x · Φ xs

  -- deleting one occurrence factors the residue by that element.
  Remove-Φ : {a : A} {ys ys' : List A} → Remove a ys ys' → Φ ys ≡ φ a · Φ ys'
  Remove-Φ rHere = refl
  Remove-Φ {a = a} (rThere {y = y} {ys' = ys'} r) =
      cong (φ y ·_) (Remove-Φ r)
    ∙ sym (·assoc (φ y) (φ a) (Φ ys'))
    ∙ cong (_· Φ ys') (·comm (φ y) (φ a))
    ∙ ·assoc (φ a) (φ y) (Φ ys')

  -- SOUNDNESS, with the quotient exhibited.
  ⊑-sound : {xs ys : List A} → xs ⊑ ys → Σ[ m ∈ Carrier ] (Φ xs · m ≡ Φ ys)
  ⊑-sound {ys = ys} ⊑nil = Φ ys , ·unitl (Φ ys)
  ⊑-sound {xs = x ∷ xs} (⊑cons {x = x} r sub) =
    let q = ⊑-sound sub
    in fst q
     , ·assoc (φ x) (Φ xs) (fst q) ∙ cong (φ x ·_) (snd q) ∙ sym (Remove-Φ r)

  -- The contrapositive: a residue that does not divide REFUTES the
  -- embedding.  This is the whole of "why the residue is sound".
  residue-rejects : {xs ys : List A}
    → ¬ (Σ[ m ∈ Carrier ] (Φ xs · m ≡ Φ ys)) → ¬ (xs ⊑ ys)
  residue-rejects nd sub = nd (⊑-sound sub)

  --------------------------------------------------------------------
  -- 1b.  AND HERE IS WHAT SOUNDNESS COSTS WHEN THE TARGET IS A GROUP:
  --      everything.  If every element is invertible, the quotient
  --      ALWAYS exists, so `residue-rejects` is vacuous — a
  --      group-valued residue can never reject a containment.
  --
  --      It can still reject EQUALITY of the two residues.  But that is
  --      a DIFFERENT ABSENCE with a different pratiyogin: a residue
  --      class, not an element of `A`.  Reading a group-valued
  --      fingerprint's rejection as a rejection of containment is
  --      exactly the mislocation parypti names.
  --------------------------------------------------------------------

  module _ (inv : Carrier → Carrier)
           (·invl : (x : Carrier) → inv x · x ≡ ε) where

    group-residue-never-rejects :
      (xs ys : List A) → Σ[ m ∈ Carrier ] (Φ xs · m ≡ Φ ys)
    group-residue-never-rejects xs ys =
        (inv (Φ xs) · Φ ys)
      , sym (·assoc (Φ xs) (inv (Φ xs)) (Φ ys))
      ∙ cong (_· Φ ys) (·comm (Φ xs) (inv (Φ xs)))
      ∙ cong (_· Φ ys) (·invl (Φ xs))
      ∙ ·unitl (Φ ys)

------------------------------------------------------------------------
-- 2.  THE COUNTING RESIDUE, AND THE PARYPTI THEOREM.
--
--     From here on `Discrete A` is a hypothesis, and it is the ONLY
--     thing that changes between §1 and §2–§4.
------------------------------------------------------------------------

module Counting {A : Type ℓ} (_≟_ : Discrete A) where

  bump : A → A → ℕ → ℕ
  bump a x n with a ≟ x
  ... | yes _ = suc n
  ... | no  _ = n

  count : A → List A → ℕ
  count a []       = zero
  count a (x ∷ xs) = bump a x (count a xs)

  -- Membership is defined by RECURSION on the list, not as an indexed
  -- family.  An indexed `_∈_` would force `searchList` below to match a
  -- constructor whose index is `a ∷ xs` against `x ∷ l`, which needs
  -- injectivity of `_∷_` — unavailable in Cubical Agda, and the module
  -- would typecheck with a warning and fail to compute under transport.
  -- The recursive definition has no such step.
  _∈_ : A → List A → Type ℓ
  a ∈ []       = ⊥* {ℓ = ℓ}
  a ∈ (x ∷ xs) = (a ≡ x) ⊎ (a ∈ xs)

  -- THE PARYPTI STEP.  A positive count is not a property of the
  -- carrier: it LOCATES the element in the collection.
  paryāpti : (a : A) (xs : List A) → zero < count a xs → a ∈ xs
  paryāpti a []       h = Empty.rec (¬-<-zero h)
  paryāpti a (x ∷ xs) h with a ≟ x
  ... | yes p = inl p
  ... | no  _ = inr (paryāpti a xs h)

  -- the excess: the counterpositive of a rejection, per element.
  Excess : List A → List A → A → Type₀
  Excess xs ys a = count a ys < count a xs

  excess→pos : (xs ys : List A) (a : A) → Excess xs ys a → zero < count a xs
  excess→pos xs ys a h = ≤-trans (suc-≤-suc (zero-≤ {n = count a ys})) h

  ----------------------------------------------------------------------
  -- The two Σ's, and the theorem that they have the same inhabitants.
  --
  --   Undelimited : Σ over the CARRIER `A`.
  --   Delimited   : the same Σ, delimited by membership in the
  --                 COLLECTION `xs` — the avacchedaka.
  ----------------------------------------------------------------------

  Undelimited : List A → List A → Type ℓ
  Undelimited xs ys = Σ[ a ∈ A ] Excess xs ys a

  Delimited : List A → List A → Type ℓ
  Delimited xs ys = Σ[ a ∈ A ] ((a ∈ xs) × Excess xs ys a)

  delimit : (xs ys : List A) → Undelimited xs ys → Delimited xs ys
  delimit xs ys (a , e) = a , paryāpti a xs (excess→pos xs ys a e) , e

  undelimit : (xs ys : List A) → Delimited xs ys → Undelimited xs ys
  undelimit xs ys (a , _ , e) = a , e

------------------------------------------------------------------------
-- 3.  BOUNDED SEARCH: the delimited Σ is decidable, and the bound is the
--     COLLECTION.  `searchList` never mentions the size of `A` — it
--     recurses on the list.
------------------------------------------------------------------------

  searchList : {P : A → Type ℓ'} → ((a : A) → Dec (P a)) → (l : List A)
             → Dec (Σ[ a ∈ A ] ((a ∈ l) × P a))
  searchList d []            = no (λ z → Empty.rec* (fst (snd z)))
  searchList {P = P} d (x ∷ l) with d x
  ... | yes px = yes (x , inl refl , px)
  ... | no ¬px with searchList {P = P} d l
  ...   | yes (a , m , pa) = yes (a , inr m , pa)
  ...   | no ¬found = no (λ { (a , inl p , pa) → ¬px (subst P p pa)
                            ; (a , inr m , pa) → ¬found (a , m , pa) })

  ExcessDec : (xs ys : List A) (a : A) → Dec (Excess xs ys a)
  ExcessDec xs ys a = <Dec (count a ys) (count a xs)

  -- decidable, with the search bounded by `xs`.
  Delimited-dec : (xs ys : List A) → Dec (Delimited xs ys)
  Delimited-dec xs ys = searchList (ExcessDec xs ys) xs

  -- and hence the undelimited one is too — THROUGH the paryāpti step,
  -- not by searching the carrier.
  Undelimited-dec : (xs ys : List A) → Dec (Undelimited xs ys)
  Undelimited-dec xs ys =
    mapDec (undelimit xs ys) (λ nd u → nd (delimit xs ys u)) (Delimited-dec xs ys)

------------------------------------------------------------------------
-- 4.  MARKOV'S PRINCIPLE FOR THIS PRATIYOGIN IS DISCHARGED, NOT ASSUMED.
--
--     `notes/EVERY_OBSTRUCTION_HERE_IS_EXACT.md` (absent from this repository): the absence `¬A` is
--     always stable, and what is at issue is recoverability of the
--     COUNTERPOSITIVE.  `WhereTheTowerCanStillBeThree` §5: for a
--     Σ-shaped counterpositive that is exactly a search question.
--     Here is the search, and here is what bounds it.
------------------------------------------------------------------------

  markov-discharged : (xs ys : List A) → Stable (Undelimited xs ys)
  markov-discharged xs ys = Dec→Stable (Undelimited-dec xs ys)

------------------------------------------------------------------------
-- 5.  THE JOIN BACK TO §1, at the per-element counting residue, and the
--     refutation the witness carries.
------------------------------------------------------------------------

  bump-swap : (b y a : A) (n : ℕ) → bump b y (bump b a n) ≡ bump b a (bump b y n)
  bump-swap b y a n with b ≟ y | b ≟ a
  ... | yes _ | yes _ = refl
  ... | yes _ | no  _ = refl
  ... | no  _ | yes _ = refl
  ... | no  _ | no  _ = refl

  Remove-count : {a : A} (b : A) {ys ys' : List A}
    → Remove a ys ys' → count b ys ≡ bump b a (count b ys')
  Remove-count b rHere = refl
  Remove-count {a = a} b (rThere {y = y} {ys' = ys'} r) =
    cong (bump b y) (Remove-count b r) ∙ bump-swap b y a (count b ys')

  bump-cong : (b x : A) {m n : ℕ} → m ≤ n → bump b x m ≤ bump b x n
  bump-cong b x h with b ≟ x
  ... | yes _ = suc-≤-suc h
  ... | no  _ = h

  -- SOUNDNESS of the per-element counting residue (the §1 statement at
  -- `M = (ℕ , + , 0)`, proved directly because it is shorter than the
  -- instantiation).
  count-sound : {xs ys : List A} → xs ⊑ ys → (a : A) → count a xs ≤ count a ys
  count-sound ⊑nil a = zero-≤
  count-sound {xs = x ∷ xs} (⊑cons {x = x} r sub) a =
    subst (bump a x (count a xs) ≤_) (sym (Remove-count a r))
          (bump-cong a x (count-sound sub a))

  -- and therefore an excess element is a REFUTATION carrying its own
  -- counterpositive: not "no embedding", but "no embedding, counterposited
  -- on `a`, delimited by multiplicity".
  excess-refutes : (xs ys : List A) → Undelimited xs ys → ¬ (xs ⊑ ys)
  excess-refutes xs ys (a , e) sub = ¬m<m (≤-trans e (count-sound sub a))

------------------------------------------------------------------------
-- 6.  NON-VACUITY.  Nothing above is empty: a concrete rejection with
--     its witness, and a concrete embedding.
------------------------------------------------------------------------

module Witness where
  open Counting discreteℕ

  xs ys : List ℕ
  xs = 1 ∷ 1 ∷ []
  ys = 1 ∷ 2 ∷ []

  counts : (count 1 xs ≡ 2) × (count 1 ys ≡ 1)
  counts = refl , refl

  -- the counterpositive, named: `1`, delimited by multiplicity.
  excess : Undelimited xs ys
  excess = 1 , (0 , refl)

  -- it lies in the collection, by `paryāpti` and not by searching ℕ.
  excess-in-xs : Delimited xs ys
  excess-in-xs = delimit xs ys excess

  no-embedding : ¬ (xs ⊑ ys)
  no-embedding = excess-refutes xs ys excess

  -- and `_⊑_` is inhabited, so the refutation above is not about an
  -- empty relation.
  yes-embedding : (1 ∷ []) ⊑ ys
  yes-embedding = ⊑cons rHere ⊑nil

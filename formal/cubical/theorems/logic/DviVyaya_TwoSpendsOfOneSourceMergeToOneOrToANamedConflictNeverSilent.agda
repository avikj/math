{-# OPTIONS --cubical --safe #-}

-- द्विव्यय — "double expenditure" (dvi = two, vyaya = spending/outgoing).
-- The compound names the object exactly: two spends of one exclusive
-- source.  English gloss follows the underscore per the file-naming rule.
--
-- WHAT THIS DISCHARGES.
--
-- It discharges the LOCAL half of the exclusive-resource frontier
-- (docs/build/ExclusiveResourceOrdering_ResearchDesign.md (absent from this repository) §2.2, Candidate B):
-- once two individually-valid spends of one source are in ONE merged view,
-- the double-spend is NEVER SILENT.  `verdict` is a TOTAL, decidable function
-- returning either
--   · Exclusive  — all held spends of the source are identified (≤ 1 distinct), or
--   · Conflict   — a NAMED pair of distinct held spends (a typed avaktavya,
--                  Saptabhangi.क्रम-सह-भेदः: the saha pair surfaced, not voted on).
-- And the alarm is merge-monotone: a Conflict in EITHER view survives the
-- join-semilattice union (`conflict-++ˡ/ʳ`).  So the substrate's own merge,
-- not a global order, discharges detection.
--
-- ON THE MODEL.  If a spend is modelled as
-- `Spend src = Σ[snk] (spend src ≡ snk) = singl (spend src)`, it is ALWAYS
-- contractible (एकसूत्र: isContr (singl x)); so its `Exclusive` is
-- unconditionally true and `MergeExhibitsConflict` is inhabited by `inl` for
-- the wrong reason — it is the graph of a function, not the set of SUBMITTED
-- valid spends.  The faithful model is a Discrete set of submitted spends
-- (equality = content-address equality, decidable); double-spend is that set
-- failing to be a proposition.

module DviVyaya_TwoSpendsOfOneSourceMergeToOneOrToANamedConflictNeverSilent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; Discrete)
open import Cubical.Data.Empty using (⊥*) renaming (rec* to ⊥*rec)

private variable ℓ : Level

-- A is the type of SUBMITTED, individually-valid spend transactions of one
-- fixed source.  Validity is local and already discharged (Carrier recheck);
-- equality is decidable because a transaction is content-addressed.
module _ {A : Type ℓ} (discA : Discrete A) where

  -- membership in a held view (a list of submitted valid spends), as a
  -- COMPUTED predicate — no indexed family, so no reliance on ∷-injectivity,
  -- hence cubical-clean under --safe.  `here` = inl refl; `there` = inr.
  _∈_ : A → List A → Type ℓ
  x ∈ []       = ⊥*
  x ∈ (y ∷ xs) = (x ≡ y) ⊎ (x ∈ xs)

  ¬∈[] : {x : A} → ¬ (x ∈ [])
  ¬∈[] e = ⊥*rec e

  -- the two verdicts, over a held view
  Exclusive : List A → Type ℓ
  Exclusive xs = (x y : A) → x ∈ xs → y ∈ xs → x ≡ y

  Conflict : List A → Type ℓ
  Conflict xs = Σ[ x ∈ A ] Σ[ y ∈ A ] ((x ∈ xs) × (y ∈ xs) × (¬ (x ≡ y)))

  -- THE LOCAL THEOREM: the verdict is TOTAL.  A held view is decidably either
  -- exclusive or a named distinct pair — the double-spend is never silent.
  verdict : (xs : List A) → Exclusive xs ⊎ Conflict xs
  verdict [] = inl (λ x y p q → ⊥*rec p)
  verdict (x ∷ []) = inl e
    where
      mem-x : (m : A) → m ∈ (x ∷ []) → m ≡ x
      mem-x m (inl p) = p
      mem-x m (inr e) = ⊥*rec e
      e : Exclusive (x ∷ [])
      e a b pa pb = mem-x a pa ∙ sym (mem-x b pb)
  verdict (x ∷ (r ∷ rest)) with verdict (r ∷ rest)
  ... | inr (a , b , pa , pb , a≢b) = inr (a , b , inr pa , inr pb , a≢b)
  ... | inl exc with discA x r
  ...   | yes p = inl e
    where
      allx : (m : A) → m ∈ (x ∷ (r ∷ rest)) → m ≡ x
      allx m (inl q) = q
      allx m (inr q) = exc m r q (inl refl) ∙ sym p
      e : Exclusive (x ∷ (r ∷ rest))
      e a b pa pb = allx a pa ∙ sym (allx b pb)
  ...   | no ¬p = inr (x , r , inl refl , inr (inl refl) , ¬p)

  -- the alarm is MERGE-MONOTONE: a conflict in either view survives the union.
  ∈-++ˡ : {x : A} {xs ys : List A} → x ∈ xs → x ∈ (xs ++ ys)
  ∈-++ˡ {xs = []}     e       = ⊥*rec e
  ∈-++ˡ {xs = z ∷ xs} (inl p) = inl p
  ∈-++ˡ {xs = z ∷ xs} (inr q) = inr (∈-++ˡ q)

  ∈-++ʳ : {x : A} (xs : List A) {ys : List A} → x ∈ ys → x ∈ (xs ++ ys)
  ∈-++ʳ []       q = q
  ∈-++ʳ (z ∷ xs) q = inr (∈-++ʳ xs q)

  conflict-++ˡ : {xs : List A} (ys : List A) → Conflict xs → Conflict (xs ++ ys)
  conflict-++ˡ ys (a , b , pa , pb , a≢b) = a , b , ∈-++ˡ pa , ∈-++ˡ pb , a≢b

  conflict-++ʳ : (xs : List A) {ys : List A} → Conflict ys → Conflict (xs ++ ys)
  conflict-++ʳ xs (a , b , pa , pb , a≢b) = a , b , ∈-++ʳ xs pa , ∈-++ʳ xs pb , a≢b

  -- the merged view is itself decidably exclusive-or-conflict: the union
  -- never yields a silent double-spend.
  mergeVerdict : (xs ys : List A) → Exclusive (xs ++ ys) ⊎ Conflict (xs ++ ys)
  mergeVerdict xs ys = verdict (xs ++ ys)

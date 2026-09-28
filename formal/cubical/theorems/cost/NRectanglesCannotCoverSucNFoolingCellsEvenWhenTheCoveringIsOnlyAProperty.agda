{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NRectanglesCannotCoverSucNFoolingCellsEvenWhenTheCoveringIsOnlyAProperty
--
-- ON THE NAME.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository), and grepped
-- invented.**  The pigeonhole step and the fooling-set method are not
-- structures I can trace to a source in this corpus's traditions, and
-- attaching a  label to them would assert a provenance nobody
-- checked — the mirror of the scrubbing the naming rule corrects.  Jaina
-- enumerative mathematics (*Anuyogadvra*, *Sthnga*) is combinatorial
-- and adjacent.
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT FINDING.
--
-- `NRectanglesCannotCoverSucNFoolingCells` is titled as an impossibility
-- about COVERING, and covering is naturally a PROPERTY: a cell is
-- covered when SOME rectangle of the family is sound and contains it.
-- What the theorem there actually takes is different and stronger —
--
--     (pick : Fin (suc n) → Fin n)
--     → ((i : …) → Sound (rects (pick i)))
--     → ((i : …) → Covers (rects (pick i)) (r i) (c i))
--
-- — i.e. a cover ALREADY EQUIPPED with a choice of which rectangle
-- serves each cell.  That is structure handed to the theorem, not a
-- hypothesis about the family, and the module's §"SYĀT — THE CLAIM, EXACTLY"
-- does not mention it: it disclaims upper bounds, r_e, d_e, raw width
-- and the min-cover/max-fooling equality, and says nothing about the
-- shape of its own covering hypothesis.
--
-- **THE GAP IS REAL BUT IT IS NOT A HOLE — IT IS A PRICE, AND THE PRICE
-- IS FINITE CHOICE.**  Two repairs, both here:
--
--   1.  Untruncated.  If the hypothesis is `(i) → Σ[ k ] (Sound × Covers)`
--       then `pick i = fst (h i)` and the rest is projection.  FREE —
--       a Π of Σ already contains its own choice function.
--   2.  Truncated, which is the honest reading of "is covered".  If the
--       hypothesis is `(i) → ∥ Σ[ k ] (Sound × Covers) ∥₁` then no
--       `pick` can be projected out, because the conclusion for a single
--       cell is not a proposition.  It goes through anyway, and what
--       pays for it is `finChoiceFin` — choice over a FINITE index into
--       a propositional truncation, proved here by induction on `n` with
--       `fsplit`.  The final goal being `⊥`, a proposition, is what lets
--       the truncation be eliminated at the end.
--
-- **AND THAT IS THE DIAGNOSTIC FROM ecb432c2 AND 53a06cc9 GIVING ITS
-- THIRD ANSWER.**  Ask what joins the two sides.  An implication assumed
-- has no inverse, so the converse is a search (53a06cc9).  A path given
-- has one, so it is free (ecb432c2).  Here the two sides are joined by a
-- TRUNCATION, and the answer is neither: it is free for a finite index
-- and unavailable in general.  Finiteness is doing the work, and it is
-- the first time on this line that anything has needed finiteness for a
-- reason other than the pigeonhole.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   finChoiceFin     ((i : Fin n) → ∥ B i ∥₁) → ∥ ((i : Fin n) → B i) ∥₁
--   CoveredBy        covering as a property: a truncated Σ
--   cannotCoverSigma      the untruncated repair, by projection
--   cannotCoverTruncated  the truncated one, through `finChoiceFin`
--
-- Neither restates the old theorem: both END at it.  `pick`, `sound`
-- and `covers` are constructed from the hypothesis and handed to
-- `nRectanglesCannotCoverSucNFoolingCells` unchanged.
------------------------------------------------------------------------

module NRectanglesCannotCoverSucNFoolingCellsEvenWhenTheCoveringIsOnlyAProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; fsplit ; ¬Fin0)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Empty as ⊥ using (⊥ ; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open import AFoolingPairForcesTwoRectangles
  using (Rect ; Sound ; Covers)
open import AFoolingSetForcesDistinctRectangles
  using (Fooling)
open import NRectanglesCannotCoverSucNFoolingCells
  using (nRectanglesCannotCoverSucNFoolingCells)

------------------------------------------------------------------------
-- 1.  Choice over a finite index, into a truncation
--
-- Induction on the BOUND, not on the element: `fsplit` does the case
-- analysis and `subst` transports along the path it returns, which is
-- the standing idiom here for avoiding a match in an index position.
------------------------------------------------------------------------

assembleFin :
  {n : ℕ} (B : Fin (suc n) → Type)
  → B fzero → ((j : Fin n) → B (fsuc j)) → (i : Fin (suc n)) → B i
assembleFin B b0 g i with fsplit i
... | inl p       = subst B p b0
... | inr (j , p) = subst B p (g j)

finChoiceFin :
  (n : ℕ) (B : Fin n → Type)
  → ((i : Fin n) → ∥ B i ∥₁) → ∥ ((i : Fin n) → B i) ∥₁
finChoiceFin zero    B h = ∣ (λ i → ⊥.rec (¬Fin0 i)) ∣₁
finChoiceFin (suc n) B h =
  PT.rec2 isPropPropTrunc
    (λ b0 g → ∣ assembleFin B b0 g ∣₁)
    (h fzero)
    (finChoiceFin n (λ j → B (fsuc j)) (λ j → h (fsuc j)))

------------------------------------------------------------------------
-- 2.  Covering as a property, and both repairs
------------------------------------------------------------------------

module _ (Row Col : Type) (M : Row → Col → Bool) where

  ServedBy :
    (n : ℕ) (rects : Fin n → Rect Row Col M) (x : Row) (y : Col) → Type
  ServedBy n rects x y =
    Σ[ k ∈ Fin n ]
      (Sound Row Col M (rects k) × Covers Row Col M (rects k) x y)

  CoveredBy :
    (n : ℕ) (rects : Fin n → Rect Row Col M) (x : Row) (y : Col) → Type
  CoveredBy n rects x y = ∥ ServedBy n rects x y ∥₁

  ----------------------------------------------------------------------
  -- 2a.  Untruncated: the choice function is already in the hypothesis
  ----------------------------------------------------------------------

  cannotCoverSigma :
    (n : ℕ) (r : Fin (suc n) → Row) (c : Fin (suc n) → Col)
    → Fooling Row Col M (Fin (suc n)) r c
    → (rects : Fin n → Rect Row Col M)
    → ((i : Fin (suc n)) → ServedBy n rects (r i) (c i))
    → ⊥
  cannotCoverSigma n r c fool rects h =
    nRectanglesCannotCoverSucNFoolingCells Row Col M n r c fool rects
      (λ i → fst (h i))
      (λ i → fst (snd (h i)))
      (λ i → snd (snd (h i)))

  ----------------------------------------------------------------------
  -- 2b.  Truncated: finite choice pays for the missing `pick`
  ----------------------------------------------------------------------

  cannotCoverTruncated :
    (n : ℕ) (r : Fin (suc n) → Row) (c : Fin (suc n) → Col)
    → Fooling Row Col M (Fin (suc n)) r c
    → (rects : Fin n → Rect Row Col M)
    → ((i : Fin (suc n)) → CoveredBy n rects (r i) (c i))
    → ⊥
  cannotCoverTruncated n r c fool rects h =
    PT.rec isProp⊥
      (cannotCoverSigma n r c fool rects)
      (finChoiceFin (suc n) (λ i → ServedBy n rects (r i) (c i)) h)

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AFigureWithoutItsInputDecidesNothing
--
-- `interactive/ObstructionCensus.hs` (absent from this repository) prints published figures next to
-- recomputed ones as a regression guard, and then says exactly why that
-- guard is weaker than it looks:
--
--   "a disagreement between a bracket and its number is not evidence of
--    a regression in `triage`, it is evidence that the log moved …
--    a count without its input is the same defect as a constant without
--    its scaling."
--
-- Its input, `interactive/machine.log`, is excluded by `.gitignore:16` — no
-- clone has it, no reader reproduces it, and it grows whenever the
-- engine runs.  §2 is that sentence as a theorem, and §3 is the exact
-- amount the guard recovers once the input IS shared, which is less than
-- one might assume.
--
-- ────────────────────────────────────────────────────────────────────
--
-- NOT the container-versus-pin finding again
-- about which TOOLCHAIN produced an exit code.  This is about an INPUT
-- the reader does not have, which is a different failure: there the
-- verifier was wrong, here the verifier is fine and the datum is
-- private.
--
-- NOT a claim that untracked inputs should be tracked.  A log that grows
-- on every run is not obviously a repository artefact, and nothing below
-- says what to do about it.
------------------------------------------------------------------------

module AFigureWithoutItsInputDecidesNothing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  A report is a function from an input to a figure
------------------------------------------------------------------------

Report : Type
Report = ℕ → ℕ

asPublished asChanged : Report
asPublished n = n
asChanged   n = suc n

reportsDiffer : ¬ (asPublished ≡ asChanged)
reportsDiffer p = znots (funExt⁻ p 0)

------------------------------------------------------------------------
-- 2.  With the input unknown, the figure decides nothing — both ways
--
-- The reader sees a number.  It is consistent with the report being
-- unchanged and with the report having changed, and so is its negation.
------------------------------------------------------------------------

-- the SAME figure, from two DIFFERENT reports, at inputs the reader
-- cannot see: 1 = asPublished 1 = asChanged 0
sameFigureFromDifferentReports :
  (asPublished 1 ≡ asChanged 0) × (¬ (asPublished ≡ asChanged))
sameFigureFromDifferentReports = refl , reportsDiffer

-- DIFFERENT figures, from ONE report, at inputs the reader cannot see
differentFiguresFromOneReport :
  Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ] (¬ (asPublished x ≡ asPublished y))
differentFiguresFromOneReport = 0 , 1 , znots

-- so no observation of the figure alone settles whether the report
-- changed: agreement is compatible with change, and disagreement is
-- compatible with no change
theFigureAloneSettlesNothing :
    ((asPublished 1 ≡ asChanged 0)  × (¬ (asPublished ≡ asChanged)))
  × (Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ] (¬ (asPublished x ≡ asPublished y)))
theFigureAloneSettlesNothing =
  sameFigureFromDifferentReports , differentFiguresFromOneReport

------------------------------------------------------------------------
-- 3.  With the input shared, exactly one direction is recovered
--
-- A MISMATCH at a common input refutes report-identity.  A MATCH does
-- not establish it.  So pinning the input turns the guard into a
-- one-sided test, which is what a regression guard actually is.
------------------------------------------------------------------------

mismatchAtSharedInputRefutes :
  (f g : Report) (x : ℕ) → ¬ (f x ≡ g x) → ¬ (f ≡ g)
mismatchAtSharedInputRefutes f g x fx≢gx p = fx≢gx (funExt⁻ p x)

matchAtSharedInputEstablishesNothing :
  Σ[ f ∈ Report ] Σ[ g ∈ Report ] Σ[ x ∈ ℕ ]
    ((f x ≡ g x) × (¬ (f ≡ g)))
matchAtSharedInputEstablishesNothing =
  (λ _ → 0) , (λ n → n) , 0 , refl , (λ p → znots (funExt⁻ p 1))

------------------------------------------------------------------------
-- 4.  The reading
--
-- §2: an untracked input makes the published-versus-recomputed
-- comparison uninformative in BOTH directions, which is stronger than
-- "the guard is weak" — it is not a guard at all.
--
-- §3: sharing the input buys a one-sided test.  Mismatch refutes;
-- match establishes nothing.  That is the correct shape for a regression
-- guard and it is worth saying, because the natural summary — "the
-- numbers agree, so nothing changed" — is the half §3's second theorem
-- refutes.
--
-- Both halves are about the same object the census module already names:
-- the input.  Its own remedy, printing the input's identity and line
-- count before any figure, is exactly what moves a report from §2 to §3.
------------------------------------------------------------------------

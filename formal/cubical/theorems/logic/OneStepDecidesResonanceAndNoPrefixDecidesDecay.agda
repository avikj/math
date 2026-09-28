{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OneStepDecidesResonanceAndNoPrefixDecidesDecay
--
-- `interactive/QuestionMachine.hs` (absent from this repository) opens by saying "Agda holds the theorems;
-- this holds the run. Every function here has a checked counterpart …
-- Nothing is measured: the output is a replay of statements that are
-- already proved."  One of its functions is not a replay, and the two
-- halves of why are proved here.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT `KFlow` STATES
--
-- `KFlow`, signatures and proof bodies:
--
--   Contracting f = (n : ℕ) → 0 < n → f n < n
--   decay      : (f) → Contracting f → (n) → Σ[ k ] iterate f k n ≡ 0
--   Stationary f n = f n ≡ n
--   resonance  : (f) (n) → Stationary f n → (k) → iterate f k n ≡ n
--
-- Every one of those is conditional on a GLOBAL property of `f`.  The
-- shelf's `flowVerdict` takes no such hypothesis: it computes 64 iterates
-- and branches on two finite tests, `any (== 0)` and `and (zipWith (==)
-- xs (drop 1 xs))`, with "branching" as the catch-all.  So it is not a
-- replay of `KFlow`; it is a finite approximation of a statement `KFlow`
-- proves under hypotheses the run cannot check.
--
-- ────────────────────────────────────────────────────────────────────
-- THE TWO HALVES, AND THEY GO OPPOSITE WAYS
--
-- §1  RESONANCE: one comparison decides it.  `Stationary f n` is
--     literally `iterate f 1 n ≡ n`, so the test is sound AND complete,
--     and 63 of the shelf's 64 comparisons are redundant.  (`KFlow`
--     already proves the forward direction; the converse is what makes
--     the finite test legitimate and is what is added here.)
--
-- §2  DECAY: no prefix decides it.  For EVERY prefix length N there is a
--     contracting `f` and a start whose orbit is nowhere 0 within N and
--     is 0 at N+1.  So `any (== 0)` over a prefix is sound and
--     INCOMPLETE, and the "otherwise ⟹ branching" catch-all is unsound:
--     the same witness is labelled branching while it decays.
------------------------------------------------------------------------

module OneStepDecidesResonanceAndNoPrefixDecidesDecay where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz)
open import Cubical.Data.Nat.Order using (_<_ ; ≤-refl ; ¬-<-zero)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import KFlow
  using (𝒦 ; iterate ; Contracting ; Stationary ; resonance)

------------------------------------------------------------------------
-- 1.  Resonance: one comparison is the whole test
------------------------------------------------------------------------

-- the forward direction is KFlow's `resonance`; this is the converse,
-- and it is what licenses testing at all
oneStepIsStationary :
  (f : 𝒦) (n : ℕ) → iterate f 1 n ≡ n → Stationary f n
oneStepIsStationary f n p = p

-- so a single observed equality already gives the whole orbit
oneStepGivesTheWholeOrbit :
  (f : 𝒦) (n : ℕ) → iterate f 1 n ≡ n → (k : ℕ) → iterate f k n ≡ n
oneStepGivesTheWholeOrbit f n p = resonance f n (oneStepIsStationary f n p)

------------------------------------------------------------------------
-- 2.  Decay: no prefix length decides it
--
-- `dec` is the predecessor, which is contracting.  Started at `suc N`
-- its orbit is 1 after N steps and 0 after N+1.
------------------------------------------------------------------------

dec : ℕ → ℕ
dec zero    = zero
dec (suc n) = n

decIsContracting : Contracting dec
decIsContracting zero    p = ⊥.rec (¬-<-zero p)
decIsContracting (suc m) _ = ≤-refl

stillOneAfterN : (N : ℕ) → iterate dec N (suc N) ≡ 1
stillOneAfterN zero    = refl
stillOneAfterN (suc M) = stillOneAfterN M

zeroAtN : (N : ℕ) → iterate dec N N ≡ 0
zeroAtN zero    = refl
zeroAtN (suc M) = zeroAtN M

zeroOneStepLater : (N : ℕ) → iterate dec (suc N) (suc N) ≡ 0
zeroOneStepLater N = zeroAtN N

-- the witness, for every prefix length
noPrefixDecidesDecay :
  (N : ℕ) →
    (¬ (iterate dec N (suc N) ≡ 0))          -- nothing seen within N
  × (iterate dec (suc N) (suc N) ≡ 0)        -- yet it decays at N+1
  × Contracting dec                          -- and it is genuinely decaying
noPrefixDecidesDecay N =
    (λ p → snotz (sym (stillOneAfterN N) ∙ p))
  , zeroOneStepLater N
  , decIsContracting

------------------------------------------------------------------------
-- 3.  What the two halves say together
--
-- The finite resonance test is exact — and 63 of the shelf's 64
-- comparisons buy nothing, because `f n ≡ n` already gives the orbit.
-- The finite decay test is sound and incomplete at every length, so the
-- branch that fires when it fails cannot be "branching": failure to see
-- a zero within N is compatible with a contracting map.
--
-- The repair is not a bigger prefix.  §2 is quantified over N, so no
-- constant fixes it; what fixes it is checking the HYPOTHESIS `KFlow`
-- actually assumes — `Contracting f` — which `decIsContracting`
-- discharges in one line for this witness.  A run cannot check that for
-- an arbitrary `f`, which is the honest reason the shelf's verdict is a
-- report and not a replay.
------------------------------------------------------------------------

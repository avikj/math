{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OracleCharge
--
-- Reading `BARRIER.md` (absent from this repository) §3 Problem 2 — the
-- oracle model separating VALUE queries from FUNCTIONAL-EQUATION queries
-- — against `ChargeCriterion`.  The prediction there was "they should be
-- the same distinction stated twice; if they are not, the difference is
-- the finding."  They are the same distinction, and the identification
-- is a theorem, not a reading:
--
--   **A functional-equation comparison cannot be parity-neutral.**
--
-- A value query reads val σ n at an argument n of the method's choosing,
-- and `ChargeCriterion` classified these: a value-query set separates the
-- gauge pair iff it contains an odd-Ω argument.  A method can choose to
-- stay neutral.
--
-- A functional-equation query — the interface entropy decrement consumes,
-- λ(pn) = −λ(n) used as a constraint — compares val at n and at p·n.
-- But Ω(p·n) = Ω(n) + 1, so THE TWO ENDS OF AN FE COMPARISON ALWAYS LIE
-- IN OPPOSITE PARITY SECTORS: whichever sector n is in, pn is in the
-- other.  A method with FE access cannot stay neutral even if it wants
-- to — any query set closed under a single FE comparison contains an
-- odd-Ω argument, hence (by `ChargeCriterion.odd⇒separator`) admits a
-- separator.
--
-- WHY THIS IS THE MECHANISM AND NOT A COINCIDENCE.  Multiplication by a
-- prime is a DEGREE-ONE SHIFT of the Ω-grading, and parity is the
-- truncation of that grading (`ChargeGrading`, Delta 15 §15.7).  T15.27
-- there says a degree-δ operation changes parity by δ mod 2, and
-- `parity-moving-shifts` says an odd shift moves the parity of EVERY
-- sector it touches — "no observer refinement can prevent it, because
-- the shift is what moves."  δ = 1 is odd.  That checked statement, two
-- modules old, is why the FE interface carries charge: the interface's
-- one primitive is an odd shift.
--
-- So three things said in three places are one thing:
--
--   BARRIER.md (absent from this repository)   "entropy decrement ∉ WL by the interface it consumes"
--   GAUGE.md (absent from this repository)     "parity-sensitive conclusions require coupling to
--                 something outside the neutral sector"
--   ChargeGrading/ChargeCriterion (here): the FE primitive is a degree-1
--                 shift; degree-1 shifts are parity-moving; parity-moving
--                 queries are exactly the separating ones.
--
-- What was DEFINITIONAL in BARRIER.md (absent from this repository) ("outside WL by construction")
-- becomes STRUCTURAL here: the FE interface does not happen to sit
-- outside the neutral class, it CANNOT sit inside it.
-- W3 asks whether value queries can SIMULATE FE queries;
-- this is the half
-- of W3 that can be had exactly: the two interfaces differ in charge,
-- provably, so a simulation would have to manufacture charge from
-- neutral readings, and `no-decision` says post-processing alone cannot.
--
-- Contents (no holes, no postulates, --safe):
--
--   FEPair                     the two ends of an FE comparison
--   fe-flips-parity            Ω(p·n) has the opposite parity of Ω(n)
--   fe-crosses-sectors         hence one end is always odd —
--                              as a decided disjunction, not a case split
--                              left to the reader
--   fe-has-charge              an FE comparison anywhere in the query set
--                              yields HasOdd
--   fe⇒separator               …and hence a constructed separator
--   value-can-hide             contrast: a nonempty pure-value query set
--                              with no separator (probe-6 re-exported in
--                              this vocabulary)
--   fe-ratio-is-the-sign       the ratio the FE constraint propagates IS
--                              σ(p) — charge-one data on the nose
--
------------------------------------------------------------------------

module OracleCharge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false ; notnot)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator
open import ChargeCriterion

------------------------------------------------------------------------
-- §1  The functional-equation interface.
--
-- One FE comparison touches the pair (n , p·n).  In the factor-multiset
-- presentation p·n is literally p ∷ n, which is why the parity fact is
-- one line: the interface's primitive is the constructor of the grading.
------------------------------------------------------------------------

fe-mult : ℕ → Number → Number
fe-mult p n = p ∷ n

-- The two ends of an FE comparison, as a query fragment.
FEPair : ℕ → Number → List Number
FEPair p n = n ∷ fe-mult p n ∷ []

------------------------------------------------------------------------
-- §2  The parity mechanics.
------------------------------------------------------------------------

-- Ω(p·n) = Ω(n) + 1, so the sign flips.  Definitional.
fe-flips-parity : (p : ℕ) (n : Number)
                → sgn (Ω (fe-mult p n)) ≡ not (sgn (Ω n))
fe-flips-parity p n = refl

-- Hence the comparison always crosses sectors: whichever parity n has,
-- exactly one end of the pair is odd.  Decided, not asserted.
fe-crosses-sectors : (p : ℕ) (n : Number)
                   → (sgn (Ω n) ≡ false) ⊎ (sgn (Ω (fe-mult p n)) ≡ false)
fe-crosses-sectors p n with sgn (Ω n) | (λ (e : sgn (Ω n) ≡ true) → e)
fe-crosses-sectors p n | false | _ = inl refl
fe-crosses-sectors p n | true  | _ = inr refl

------------------------------------------------------------------------
-- §3  Consequence: FE access is charged access.
--
-- Any query set containing both ends of one FE comparison has an odd
-- query, and therefore admits a constructed separator for the gauge
-- pair.  A method consuming the FE interface is on the charged side of
-- `charge-criterion` BY THE INTERFACE, before it computes anything.
------------------------------------------------------------------------

fe-has-charge : (p : ℕ) (n : Number) → HasOdd (FEPair p n)
fe-has-charge p n with fe-crosses-sectors p n
... | inl oddN  = inl oddN
... | inr oddPN = inr (inl oddPN)

fe⇒separator : (p : ℕ) (n : Number) → Separates (FEPair p n)
fe⇒separator p n = odd⇒separator (FEPair p n) (fe-has-charge p n)

------------------------------------------------------------------------
-- §4  The contrast that makes it an asymmetry of interfaces.
--
-- Value queries CAN be confined to the neutral sector — probe-6 from
-- `ChargeCriterion` is a nonempty value-query set with provably no
-- separator.  FE queries cannot be so confined: §3.  That asymmetry is
-- the oracle-model distinction of BARRIER.md (absent from this repository) §3 Problem 2, derived
-- rather than defined.
------------------------------------------------------------------------

value-can-hide : Σ[ qs ∈ List Number ] ((¬ (Separates qs)) × (¬ (qs ≡ [])))
value-can-hide = probe-6 , probe-6-cannot , nonempty
  where
    isNil : List Number → Bool
    isNil []      = true
    isNil (_ ∷ _) = false
    nonempty : ¬ (probe-6 ≡ [])
    nonempty e = true≢false (sym (cong isNil e))

------------------------------------------------------------------------
-- §5  What the FE constraint actually transports.
--
-- The relation λ(pn) = −λ(n) propagates the RATIO val σ (p·n) / val σ n,
-- and that ratio is σ(p) itself — charge-one data, the sign at a single
-- prime.  So the FE interface is not merely "somewhere charged": its
-- transported datum is the generator of the charged sector.  This is the
-- exact sense in which entropy decrement "accesses a's functional
-- equation" (BARRIER.md (absent from this repository)): each use reads one prime's sign.
------------------------------------------------------------------------

fe-ratio-is-the-sign : (σ : Signs) (p : ℕ) (n : Number)
                     → val σ (fe-mult p n) ≡ σ p · val σ n
fe-ratio-is-the-sign σ p n = refl

-- …and for the gauge pair specifically: on σ₊ the ratio is +1, on the
-- flip it is −1, at every prime and every n.  The FE interface separates
-- the pair by ONE comparison, anywhere.
fe-ratio-separates : (p : ℕ) (n : Number)
                   → (val σ₊ (fe-mult p n) ≡ val σ₊ n)
                   × (val (flip σ₊) (fe-mult p n) ≡ not (val (flip σ₊) n))
fe-ratio-separates p n = refl , refl

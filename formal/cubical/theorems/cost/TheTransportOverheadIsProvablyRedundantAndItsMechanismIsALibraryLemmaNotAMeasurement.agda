{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheTransportOverheadIsProvablyRedundantAndItsMechanismIsALibraryLemmaNotAMeasurement
--
-- ON THE NAME.  **No tradition term is claimed and none is invented.**
-- Univalence, `ua` and transport are Voevodsky's and the cubical
-- library's — the substrate this repository is checked in, which
-- `CLAUDE.md` (absent from this repository) explicitly exempts from the framing rule ("tools are not
-- frames").  There is no Indian source for this statement and inventing
-- a  label would assert a provenance nobody checked.  Checked
-- before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository) (CURRENT header)
-- grepped first.
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT.  `TransportCost` says:
--
--   "two separate questions remain, and **both are decided by execution
--    rather than by proof** … (2) NO.  Native is flat in the number of
--    chained operations; the transported term is quadratic, **because
--    transport across `ua e` *is* `e⁻¹ ∘ f ∘ (e × e)`** — a full round
--    trip through ℕ per operation, and `valueC`/`digitsC` are unary."
--
-- **The sentence after "because" is not an explanation of a
-- measurement.  It is `Cubical.Foundations.Univalence.transportUAop₂`,
-- a library lemma, verbatim:**
--
--   transportUAop₂ : (e : A ≃ B) (f : A → A → A) (x y : B)
--     → transport (λ i → ua e i → ua e i → ua e i) f x y
--       ≡ equivFun e (f (invEq e x) (invEq e y))
--
-- So the mechanism was never measured; it was already proved, upstream,
-- and the module cites it while calling the result execution-decided.
-- `CLAUDE.md` (absent from this repository)'s rule applies exactly: *"No claim of the form 'measured
-- slope ≈ x' survives if the slope is derivable."*  §2 below derives the
-- structure the slope comes from.
--
-- **AND THE BUILD STATUS MATTERS, so it is stated with its command.**
-- On the CONTAINER, `TransportCost.agda` does not typecheck at all:
--
--   cd formal/cubical && agda -i . NaturalMachine/TransportCost.agda
--   → TRANSPORTCOST_EXIT=42
--
-- because it opens `NaturalMachine`, hence `Transport`,
-- whose first error is `Transport.agda:46,50-65` — the same upstream
-- `solveℕ!` import that fails the two aggregate gates.  So **its
-- `refl`s cannot be re-verified here**, and its answer to question (1)
-- ("YES.  Every `refl` below forces evaluation and typechecks") is not
-- currently checkable on this toolchain.  That is a fact about the
-- container, NOT a doubt about the claim, and NOT that module's fault.
-- **This module therefore depends on none of it** — nothing below
-- imports `NaturalMachine`, and everything below is checked.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED, for an ARBITRARY equivalence and binary operation
--
--   T                   the transported operation
--   step                = `transportUAop₂`, named here so the mechanism
--                         is a hypothesis-free theorem in this file too
--   iterN / iterT       `n` chained operations, native and transported,
--                         against a fixed right argument
--   theRoundTripsAreRedundant
--                       `iterT n (e .fst a) ≡ e .fst (iterN n a)`
--
-- **THAT LAST IS THE DERIVATION THE MEASUREMENT WAS STANDING IN FOR.**
-- Each transported step provably inserts `invEq e ∘ e .fst` around an
-- argument that was already in `A`'s image.  On VALUES that composite is
-- the identity — which is why the theorem holds and why the two agree.
-- On TERMS it is not removed, because nothing removes it: `retEq` is a
-- path, and a path is not a reduction.  So `n` chained operations carry
-- exactly `n` provably-redundant round trips, one per step, and the
-- quadratic in the audited note is that `n` multiplied by the cost of
-- one round trip in a UNARY representation.  Nothing was measured to
-- get here.
------------------------------------------------------------------------

module TheTransportOverheadIsProvablyRedundantAndItsMechanismIsALibraryLemmaNotAMeasurement where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; retEq)
open import Cubical.Foundations.Univalence using (ua ; transportUAop₂)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

module _ {A B : Type} (e : A ≃ B) (f : A → A → A) (a₁ : A) where

  ------------------------------------------------------------------
  -- 1.  The transported operation, and its mechanism
  ------------------------------------------------------------------

  T : B → B → B
  T = transport (λ i → ua e i → ua e i → ua e i) f

  step : (x y : B) → T x y ≡ e .fst (f (invEq e x) (invEq e y))
  step = transportUAop₂ e f

  ------------------------------------------------------------------
  -- 2.  n chained operations, both sides
  ------------------------------------------------------------------

  iterN : ℕ → A → A
  iterN zero    a = a
  iterN (suc n) a = f (iterN n a) a₁

  iterT : ℕ → B → B
  iterT zero    b = b
  iterT (suc n) b = T (iterT n b) (e .fst a₁)

  ------------------------------------------------------------------
  -- 3.  Every round trip the transported chain performs is redundant
  --
  -- The two `retEq`s are the round trips: each cancels ON VALUES, by a
  -- PATH.  A path is not a reduction, so nothing here removes them from
  -- the term — which is precisely why the chain costs what the audited
  -- note measured.
  ------------------------------------------------------------------

  theRoundTripsAreRedundant :
    (n : ℕ) (a : A) → iterT n (e .fst a) ≡ e .fst (iterN n a)
  theRoundTripsAreRedundant zero    a = refl
  theRoundTripsAreRedundant (suc n) a =
      cong (λ z → T z (e .fst a₁)) (theRoundTripsAreRedundant n a)
    ∙ step (e .fst (iterN n a)) (e .fst a₁)
    ∙ cong (λ z → e .fst (f z (invEq e (e .fst a₁)))) (retEq e (iterN n a))
    ∙ cong (λ z → e .fst (f (iterN n a) z)) (retEq e a₁)

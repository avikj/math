{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- निवृत्ति-क्षेत्रम् — the return locus.  Tonight's twelve queue
-- discharges were one theorem wearing five costumes.  This module
-- proves the theorem once, in general, and hangs the costumes on it.
--
-- Setting: a quotient q : A → B and a candidate return s : B → A.
-- The probes all asked "does s ∘ q fix w?" — पुनरागमन, pointwise.
--
-- THE LAW, two halves:
--
--   I.  If q ∘ s ≡ id — s is a true section, a zero-defect return —
--       then the fixed points of s ∘ q are EXACTLY the image of s:
--       the canonical representatives, Pigala's alphabet, the
--       residues that name themselves.  Return on the whole alphabet.
--
--   II. If instead the loop is positively priced — the composite
--       multiplies by suc m ≥ 2, as hull's census does — there is no
--       section, and the return locus collapses to zero alone
--       (proved in Nirdharana_Hull_ReturnSunyeEva.noReturn).
--
-- Instances checked below: aksara/parity (alphabet {laghu, guru} —
-- the retraction is definitional) and ones/sum (alphabet = the
-- all-ones words; sum ∘ ones ≡ id by induction).  The hull instance
-- is the other half, priced, in its own module.  Together: an edge
-- returns on its zero-cost locus and nowhere else — sūtra १६ stated
-- with both of its faces, as one two-line lemma each way.
------------------------------------------------------------------------

module Ratri.Nirdharana_TheReturnLocusIsTheSectionsImageOrZeroAlone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

------------------------------------------------------------------------
-- I · the general law, both inclusions, four lines total.

module Return (q : A → B) (s : B → A) (sect : (b : B) → q (s b) ≡ b) where

  -- every canonical representative returns …
  image-returns : (b : B) → s (q (s b)) ≡ s b
  image-returns b = cong s (sect b)

  -- … and everything that returns is canonical (trivially: it is s of
  -- its own summary).  So fix (s ∘ q) = im s, on the nose.
  returns-are-image : (w : A) → s (q w) ≡ w → Σ B (λ b → s b ≡ w)
  returns-are-image w p = q w , p

------------------------------------------------------------------------
-- II · instance: Piṅgala.  parity ∘ aksara ≡ id definitionally, so the
-- return locus of aksara ∘ parity is the syllable alphabet — the same
-- fact Nirdharana_PingalaPrastara_… proved from the ℕ side.

open import PingalaPrastara using (Syllable; laghu; guru; aksara; parity)

parity-sections-aksara : (u : Syllable) → parity (aksara u) ≡ u
parity-sections-aksara laghu = refl
parity-sections-aksara guru  = refl

module PingalaReturn = Return parity aksara parity-sections-aksara

------------------------------------------------------------------------
-- III · instance: the swarm's summary.  sum ∘ ones ≡ id by induction,
-- so the return locus of ones ∘ sum is exactly the all-ones words —
-- which is why [2] could not return (Anirdharita_S13OptionSpread_…).

open import OptionSpread using (sum; ones)

sum-sections-ones : (n : ℕ) → sum (ones n) ≡ n
sum-sections-ones zero    = refl
sum-sections-ones (suc n) = cong suc (sum-sections-ones n)

module SwarmReturn = Return sum ones sum-sections-ones

-- The alphabet, exhibited: every n returns as its all-ones word.
allOnesReturn : (n : ℕ) → ones (sum (ones n)) ≡ ones n
allOnesReturn = SwarmReturn.image-returns

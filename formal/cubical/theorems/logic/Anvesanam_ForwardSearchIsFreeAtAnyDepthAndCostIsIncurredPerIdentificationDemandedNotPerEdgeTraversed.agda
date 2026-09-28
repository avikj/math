{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अन्वेषणम् — अग्रे गमनं मुक्तम्; व्ययः तादात्म्ये, न पदे ।
--
-- (going forward is free; the cost is at identification, not at the step.)
--
-- ────────────────────────────────────────────────────────────────────
-- THE ROUTING CONSEQUENCE OF THE OTHER FILES, ASSEMBLED.  A search over a
-- graph of maps normally pays per EDGE.  Here it does not, and the three
-- facts that say so are already terms:
--
--   · `Lekha_…agda` §३ — the full trail of `n` steps, every intermediate
--     and every witness, is CONTRACTIBLE at every `n`.  Depth is free.
--   · `LosslessReturn_…agda` §२ — out and back in the CODOMAIN is free at
--     any loss: take a lossy edge, pick any preimage, return, and you are
--     exactly where you started.
--   · `LosslessReturn_…agda` §३ — out and back in the DOMAIN is not
--     available at all when a bit is destroyed.
--
-- §२ below is the statement those three make together: **an arbitrarily
-- deep forward exploration, carrying its whole trail, costs nothing; and
-- what costs is a demanded return to the THING.**  So the frontier of a
-- search here is not the set of nodes reached.  It is the set of
-- identifications owed.
--
-- SCOPE.  `अन्वेषणम्` is the trail of ONE deterministic map `step : A → A`
-- iterated n times, which has exactly one run, so its contractibility is
-- the uniqueness of that run.  A search over a graph (several edges out
-- of a node, a choice at each step) is NOT formalised here, and nothing
-- below says that branching exploration is free.
--
-- AND THE ROUTER'S CORRECTNESS CONDITION, which is `Anupalabdhi_…agda`
-- read at a search: a router that reports "unreachable" because it did
-- not find a route has produced no term.  Absence of a route is a Π over
-- the whole field, not a failed traversal, so the only verdicts a search
-- may return are a route, a written defect, or UNDECIDED.  That is what
-- `interactive/Lopa_…hs` already does by counting UNDECIDED separately rather
-- than guessing, on the stated ground that a verdict guessed is worse
-- than a verdict withheld.
------------------------------------------------------------------------

module Anvesanam_ForwardSearchIsFreeAtAnyDepthAndCostIsIncurredPerIdentificationDemandedNotPerEdgeTraversed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isContrΣ)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; isContrUnit*)

private variable ℓ : Level

module _ {A : Type ℓ} (step : A → A) where

------------------------------------------------------------------------
-- १ · अन्वेषणम् — a forward exploration of depth n from a, carrying every
--     intermediate and every witness that it IS the intermediate.
------------------------------------------------------------------------

  अन्वेषणम् : ℕ → A → Type ℓ
  अन्वेषणम् zero    a = Unit*
  अन्वेषणम् (suc n) a = Σ[ p ∈ singl (step a) ] अन्वेषणम् n (p .fst)

------------------------------------------------------------------------
-- २ · अग्रे-गमनं-मुक्तम् — AND IT IS FREE AT EVERY DEPTH.
--
-- Not cheap, not amortized: contractible.  The exploration and its
-- entire audit trail contribute zero degrees of freedom, for every `n`,
-- with no hypothesis on `A` or on `step` — however much `step` destroys.
--
-- So depth is not what a search here pays for.  What it pays for is
-- named in the header and is the other binding entirely.
------------------------------------------------------------------------

  अग्रे-गमनं-मुक्तम् : (n : ℕ) (a : A) → isContr (अन्वेषणम् n a)
  अग्रे-गमनं-मुक्तम् zero    a = isContrUnit*
  अग्रे-गमनं-मुक्तम् (suc n) a =
    isContrΣ (isContrSingl (step a)) (λ p → अग्रे-गमनं-मुक्तम् n (p .fst))

------------------------------------------------------------------------
-- ३ · शेषः — what a search still owes.
--
-- §२ says nothing about whether any particular target is REACHED; it
-- prices the exploration, not the answer.  Reachability is a fibre
-- question, its three verdicts are `Tantutrayam_…agda` (absent from this repository)'s, and its empty
-- case is `Anupalabdhi_…agda`'s Π over the whole field.  A search that
-- conflates "I explored and did not arrive" with "there is no route" has
-- produced the one verdict this corpus has no witness for.
------------------------------------------------------------------------

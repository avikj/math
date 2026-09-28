{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem
--
--
--   "A certified rewrite carries: boundary-semantics preservation,
--    complexity improvement (peak semantic width / Pareto), state
--    migration, provenance."
--
-- Four components, listed.  A compiler applies rewrites in sequence, so
-- the question the list does not answer is whether the certificate
-- COMPOSES — and if it does, which component costs anything.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   Certified d e     the four components as one Σ: the boundary
--                     semantics agree, the cost vector strictly
--                     improves, the state migrates, provenance is
--                     carried
--   composeCertified  certified rewrites compose
--   noSelfRewrite     and no system is a certified rewrite of itself,
--                     so a rewrite sequence never marks time
--
-- **THREE OF THE FOUR COMPOSE FOR FREE.**  Boundary preservation is a
-- path and paths compose; migration is a function and functions
-- compose; provenance is a list and lists append.  Only COMPLEXITY
-- IMPROVEMENT needs a theorem — transitivity of strict Pareto
-- domination — and that theorem already exists in this corpus, proved
-- on the DARWIN §5.2 stratum line for an unrelated purpose
-- (`⊏-trans` in `ANonEmptyArchiveHasANonEmptyStratum`, where it was
-- needed because a maximal element of the tail might be beaten by the
-- head).  `noSelfRewrite` is likewise `⊏-irrefl` from that module.
--
-- So the two notes are joined by a lemma neither asked for: §5.2's
-- parent selection and §39–47's compiler need the SAME fact about the
-- Pareto order, and it was proved once.
--
-- ────────────────────────────────────────────────────────────────────
-- ON THE COST CONVENTION, because it is a live hazard on this line.
-- The cost vector is compared with `StrictlyDominatedBy`, which is the
-- BENEFIT reading — higher is better.  §39–47's "complexity" is a cost,
-- lower is better, so applying this to it requires the flip, and the
-- flip is SOUND BUT NOT FAITHFUL: it needs a cap above every cost ever
-- compared, and identifies costs above that cap
-- (`FlippingACostCoordinateIsSoundButNotFaithful`).
--
-- NO NOVELTY.  Composing certificates componentwise is what
-- certificates are for; the content is only the count — three free,
-- one earned.
------------------------------------------------------------------------

module ACertifiedRewriteComposesAndOnlyOneComponentNeedsATheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import TheParetoStratumIsDecidableAndTheFilterIsExact
  using (StrictlyDominatedBy)
open import ANonEmptyArchiveHasANonEmptyStratum
  using (⊏-irrefl ; ⊏-trans)

module _ {Sys B Prov : Type}
         (sem  : Sys → B)
         (cost : Sys → List ℕ)
         (M    : Sys → Type)
  where

  ------------------------------------------------------------------
  -- 1.  The four components
  ------------------------------------------------------------------

  Certified : Sys → Sys → Type
  Certified d e =
      (sem e ≡ sem d)                              -- boundary preserved
    × (StrictlyDominatedBy (cost d) (cost e))        -- strictly improved
    × (M d → M e)                                  -- state migration
    × List Prov                                    -- provenance

  ------------------------------------------------------------------
  -- 2.  They compose — three for free, one by ⊏-trans
  ------------------------------------------------------------------

  composeCertified :
    (d e f : Sys) → Certified d e → Certified e f → Certified d f
  composeCertified d e f (sde , imp₁ , mig₁ , prov₁)
                         (sef , imp₂ , mig₂ , prov₂) =
      sef ∙ sde
    , ⊏-trans (cost d) (cost e) (cost f) imp₁ imp₂
    , (λ m → mig₂ (mig₁ m))
    , prov₁ ++ prov₂

  ------------------------------------------------------------------
  -- 3.  And a rewrite never marks time
  ------------------------------------------------------------------

  noSelfRewrite : (d : Sys) → ¬ Certified d d
  noSelfRewrite d (_ , imp , _ , _) = ⊏-irrefl (cost d) imp

------------------------------------------------------------------------
-- MIGRATION is a bare function with no law — nothing says it
-- preserves the boundary semantics, and a compiler would need
-- exactly that, so the composite's migration is only as meaningful
-- as its components'.
--
-- The law is stated and tested in
-- `MigrationNeedsALawAndTheLawIsNotFree`:
--
--   Lawful obs mig   `obs e (mig m) ≡ obs d m`
--   composeLawful    lawful migrations compose — as free as the three
--                    components that were already free
--   lawTransportsEveryInvariant
--                    ANY function of the observation is preserved, by
--                    one `cong` — so a lawful migration moves no
--                    derived quantity, which is what state migration
--                    must mean for provenance and caches to survive it
--   unlawfulMigrationExists
--                    `not` on `Bool` under the identity observation is
--                    a migration and is NOT lawful
--
-- **THE LAST ONE IS WHY THE COUNT CHANGES.**  Everything else here
-- composed for free and it would be easy to read migration the same
-- way.  A bare function is exactly a migration with no guarantee, and
-- the witness is one line.  So §39–47's four components are better
-- counted as THREE FREE, ONE EARNED (complexity, by `⊏-trans`), AND
-- ONE UNDER-SPECIFIED — migration, which needs the law added before it
-- means anything.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The law is added to the record in
-- `TheLawBelongsInTheRecordAndTheCertificateComposesAlongAChain`.
-- The Σ above is unchanged: the five-component `LCertified` is a
-- separate definition there, and this record continues to admit
-- certificates with a lawless migration.
--
-- That module also settles the question this one could not ask, since
-- it had no `obs`: the law is INDEPENDENT of the other four components.
-- `anUnlawfulFourComponentCertificate` is an element of THIS `Certified`
-- — `refl` semantics, strictly improving cost, a migration, provenance —
-- whose migration is `not` and therefore destroys every observation.
-- So requiring the law removes certificates; it does not merely name
-- what four components already forced.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- **`FREE`, IN THE COUNT ABOVE, MEANS TWO INCOMPARABLE THINGS.**
-- DERIVABLE-FREE: boundary preservation composes by `∙`, migration by
-- function composition — a real obligation with a one-symbol proof.
-- VACUOUSLY FREE: provenance has NO condition anywhere, so `++`
-- composes it because nothing constrains it.  At 28e9a0a4,
-- `provenanceMayBeDiscarded` proves the sharp form — `(s , i , m , _)`
-- ↦ `(s , i , m , [])` is a certificate for the SAME pair — so no
-- downstream theorem can recover a step from provenance.
--
-- So "three free, one earned" is better read as: two discharged, one
-- earned (`⊏-trans`), one under-specified (migration), one inert
-- (provenance) — four components, four verdicts.
------------------------------------------------------------------------

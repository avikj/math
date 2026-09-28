{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- VacuityIsExactlyEmptinessAndTheEquivalenceCostsAUniverseLift
--
-- ON THE NAME.  **No tradition term is claimed and none is invented.**
-- Consistency models, happens-before and causal delivery are
-- distributed-systems objects with no Indian source I can establish,
-- and a fabricated  label would assert a provenance nobody
-- checked.  Checked before naming: `.claude/hooks/priority-ledger.txt` (absent from this repository)
-- (CURRENT header) and `.claude/hooks/european-frame.txt` (absent from this repository); no row
-- applies and the frame check's scope requires Indian material, of
--
-- ────────────────────────────────────────────────────────────────────
-- THE AUDIT.  Target: `AnEmptyDependencyRelationMakesCausalDeliveryVacuous`,
-- §3.2.  That module proves two things and draws the wrong pair of
-- conclusions from them:
--
--   §2  emptyDeclarationIsRespectedByEveryOrder : empty hb → every order
--       respects hb; and its instance `theConcurrentOrderIsAdmissible`
--       at the order `λ _ _ → ⊥`.
--   §3  oneDeclaredEdgeExcludesTheConcurrentOrder : one edge refutes
--       `Respects (λ _ _ → ⊥)`.
--
-- and comments on §3: *"So §2 is not a fact about causal delivery; it is
-- a fact about the relation being empty."*
--
-- **THE CONCLUSION IS RIGHT AND THE THEOREM UNDER IT IS WEAKER THAN THE
-- ONE ALREADY IN THE MODULE.**  §3 excludes ONE order from ONE edge.
-- The statement that actually says "vacuity is a fact about emptiness"
-- is the universally quantified converse
--
--     (every order respects hb) → hb is empty
--
-- and it is **free from §2's own instance, read backwards**: apply the
-- vacuity hypothesis at the order `λ _ _ → ⊥`, which is admissible
-- precisely when nothing is declared.  The module contained both halves
-- of a biimplication and published only the weaker consequence of one.
--
-- Applying the test that has been earning its keep on this line: take
-- the prose claim at its strong reading and try to INSTANTIATE it.
-- "The emptiness is doing all the work" at strength means *exactly*
-- emptiness — an iff — and §3 does not give it.
--
-- WHAT IS PROVED
--
--   vacuousToEmpty / emptyToVacuous
--                    the biimplication, both directions, one line each.
--   isPropEmptyHB    emptiness is a proposition (`isProp¬` pointwise).
--   VacuousP, isPropVacuousP
--                    vacuity RESTRICTED to hProp-valued orders is a
--                    proposition, and the restriction does not cost the
--                    theorem: the witnessing order `λ _ _ → ⊥` is
--                    itself a proposition, so both directions survive.
--   vacuityIsExactlyEmptiness
--                    `Lift EmptyHB ≃ VacuousP`, by `propBiimpl→Equiv`.
--
-- **AND THE LIFT IS THE CONTENT, NOT PACKAGING.**  `EmptyHB` quantifies
-- over WRITES and lives in `Type₀`.  Vacuity quantifies over ORDERS —
-- a universe of relations — and therefore lives one level up, in
-- `Type₁`, whatever h-level it has.  v0.5's `propBiimpl→Equiv` takes
-- both arguments at the SAME level (`A B C D : Type ℓ` in
-- `Cubical.Foundations.Equiv`), so the equivalence is stated with an
-- explicit `Lift`.  That is not a technicality: **"vacuity" and
-- "emptiness" are not statements of the same kind**, one being a fact
-- about a relation and the other a fact about every relation on it,
-- and the universe gap is where that difference is recorded.
------------------------------------------------------------------------

module VacuityIsExactlyEmptinessAndTheEquivalenceCostsAUniverseLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ ; isOfHLevelLift ; hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Equiv using (_≃_ ; propBiimpl→Equiv)
open import Cubical.Data.Empty as ⊥ using (⊥ ; isProp⊥)
open import Cubical.Relation.Nullary using (¬_ ; isProp¬)

open import AnEmptyDependencyRelationMakesCausalDeliveryVacuous
  using (Respects ; emptyDeclarationIsRespectedByEveryOrder)

module _ (Write : Type) (hb : Write → Write → Type) where

  ------------------------------------------------------------------
  -- 1.  The two sides
  ------------------------------------------------------------------

  EmptyHB : Type
  EmptyHB = (a b : Write) → ¬ hb a b

  Vacuous : Type₁
  Vacuous = (ord : Write → Write → Type) → Respects Write hb ord

  ------------------------------------------------------------------
  -- 2.  The biimplication.  The forward half is the audited module's
  --     §2; the backward half is its §2's own instance, read backwards,
  --     and is what §3 should have said.
  ------------------------------------------------------------------

  emptyToVacuous : EmptyHB → Vacuous
  emptyToVacuous empty ord =
    emptyDeclarationIsRespectedByEveryOrder Write hb empty ord

  vacuousToEmpty : Vacuous → EmptyHB
  vacuousToEmpty vac a b h = vac (λ _ _ → ⊥) a b h

  ------------------------------------------------------------------
  -- 3.  h-levels, and the restriction that buys one
  ------------------------------------------------------------------

  isPropEmptyHB : isProp EmptyHB
  isPropEmptyHB = isPropΠ λ a → isPropΠ λ b → isProp¬ (hb a b)

  -- vacuity over PROPOSITION-valued orders.  `Respects` is unchanged;
  -- only the range of `ord` is narrowed, and the narrowing is free
  -- because the order that witnesses §2's backward half is `⊥`, which
  -- is a proposition.
  VacuousP : Type₁
  VacuousP =
    (ord : Write → Write → hProp ℓ-zero)
    → Respects Write hb (λ a b → ⟨ ord a b ⟩)

  isPropVacuousP : isProp VacuousP
  isPropVacuousP =
    isPropΠ λ ord → isPropΠ λ a → isPropΠ λ b → isPropΠ λ _ → snd (ord a b)

  emptyToVacuousP : EmptyHB → VacuousP
  emptyToVacuousP empty ord a b h = ⊥.rec (empty a b h)

  vacuousPToEmpty : VacuousP → EmptyHB
  vacuousPToEmpty vac a b h = vac (λ _ _ → (⊥ , isProp⊥)) a b h

  ------------------------------------------------------------------
  -- 4.  And therefore an equivalence — across one universe level
  ------------------------------------------------------------------

  vacuityIsExactlyEmptiness : Lift {j = ℓ-suc ℓ-zero} EmptyHB ≃ VacuousP
  vacuityIsExactlyEmptiness =
    propBiimpl→Equiv
      (isOfHLevelLift 1 isPropEmptyHB)
      isPropVacuousP
      (λ e → emptyToVacuousP (lower e))
      (λ v → lift (vacuousPToEmpty v))

------------------------------------------------------------------------
-- 5.  What this changes about reading SEED83 §3.2
--
-- The note says a corpus with no declared dependencies "cannot be run
-- causally-consistent by tuning `sync`; it lacks the metadata for the
-- model to have content."  §4 above is the exact form of that: the
-- delivery constraint and the emptiness of the dependency relation are
-- the SAME statement, not merely one implying the other.  So there is
-- no intermediate regime in which the constraint is weak-but-present —
-- it is either empty and inert, or inhabited and biting.
--
-- What that does NOT settle, and is a different theorem: whether the
-- constraint biting on SOME orders makes it useful, i.e. how the
-- strength of the discipline grows with the number of recorded edges.
-- `oneDeclaredEdgeExcludesTheConcurrentOrder` is the first point of that
-- curve and nothing on this line computes a second.
------------------------------------------------------------------------

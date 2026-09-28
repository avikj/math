{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- स्थानिवत्सङ्ख्या — the ādeśa state space is exactly eighty-one, and
-- the join to the number component is checked.
--
-- TERM.  सङ्ख्या (count, number) is ordinary  and the ordinary
-- word of the Indian mathematical tradition for number; the compound
-- स्थानिवत्-सङ्ख्या, "the count of the sthānivat", is built HERE and no
-- source is claimed for it.
--
-- SEED.  The machine asked for this itself.  जीव's mass map
-- (machine/Jiva_TheMachineComputesItsOwnMetric.hs (absent from this repository)) scored the join of the component at
-- `Punaragamana.Sthanivadbhava….स्थानिवत्` to the number component at
-- 2970 — its second-highest curvature-removal candidate.  A join, in
-- the graph's own terms, is a checked identification.  Here it is:
--
--     वर्णरूप ≃ Fin 3        (three forms)
--     वर्णसञ्ज्ञा ≃ Fin 3     (three designations)
--     वर्ण ≃ Fin 27          (a varṇa is form × sthānin × designation)
--     आधार ≃ Fin 81          (the ādeśa's base: varṇa × substituted form)
--     स्थानिवत् ≃ Fin 81      (composing with the module's own Carrier
--                             equivalence — the carried datum rides free,
--                             so the state space does not grow: 81, not
--                             81 · 9)
--
-- The last line is the point, and it is the punargamana law seen as a
-- COUNT: `Carrier निर्धारितम्` adds two fields (carried, witness) and
-- adds NOTHING to the cardinality, because the fibre is contractible.
-- A reader who trusts only numbers can now check ahis by counting.
--
------------------------------------------------------------------------

module Punaragamana.PositionalCount_TheAdesaStateSpaceIsExactlyEightyOneAndTheJoinToTheNumberComponentIsChecked where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; compEquiv ; invEquiv)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ≃-×)
open import Cubical.Data.SumFin using (Fin ; fzero ; fsuc ; SumFin×≃)

open import Punaragamana.Carrier using (Carrier≃)
open import Punaragamana.Sthanivadbhava_TheAdesasFormIsTheFreeSlotAndItsDesignationsAreCarried
  using (वर्णरूप ; ई ; ए ; अ ; वर्णसञ्ज्ञा ; अङ्ग ; प्रत्यय ; कित्
        ; वर्ण ; वर्णः ; रूपम् ; स्थानी ; सञ्ज्ञा
        ; आधार ; निर्धारितम् ; स्थानिवत् ; आधार≃स्थानिवत्)

------------------------------------------------------------------------
-- १ · the two three-element inventories.
------------------------------------------------------------------------

रूप≃३ : वर्णरूप ≃ Fin 3
रूप≃३ = isoToEquiv (iso to from sec ret) where
  to : वर्णरूप → Fin 3
  to ई = fzero
  to ए = fsuc fzero
  to अ = fsuc (fsuc fzero)
  from : Fin 3 → वर्णरूप
  from fzero               = ई
  from (fsuc fzero)        = ए
  from (fsuc (fsuc fzero)) = अ
  sec : (x : Fin 3) → to (from x) ≡ x
  sec fzero               = refl
  sec (fsuc fzero)        = refl
  sec (fsuc (fsuc fzero)) = refl
  ret : (v : वर्णरूप) → from (to v) ≡ v
  ret ई = refl
  ret ए = refl
  ret अ = refl

सञ्ज्ञा≃३ : वर्णसञ्ज्ञा ≃ Fin 3
सञ्ज्ञा≃३ = isoToEquiv (iso to from sec ret) where
  to : वर्णसञ्ज्ञा → Fin 3
  to अङ्ग   = fzero
  to प्रत्यय = fsuc fzero
  to कित्   = fsuc (fsuc fzero)
  from : Fin 3 → वर्णसञ्ज्ञा
  from fzero               = अङ्ग
  from (fsuc fzero)        = प्रत्यय
  from (fsuc (fsuc fzero)) = कित्
  sec : (x : Fin 3) → to (from x) ≡ x
  sec fzero               = refl
  sec (fsuc fzero)        = refl
  sec (fsuc (fsuc fzero)) = refl
  ret : (s : वर्णसञ्ज्ञा) → from (to s) ≡ s
  ret अङ्ग   = refl
  ret प्रत्यय = refl
  ret कित्   = refl

------------------------------------------------------------------------
-- २ · a varṇa is its three fields (record eta), hence Fin 27.
------------------------------------------------------------------------

वर्ण-त्रिक : वर्ण ≃ (वर्णरूप × (वर्णरूप × वर्णसञ्ज्ञा))
वर्ण-त्रिक = isoToEquiv (iso to from (λ _ → refl) (λ _ → refl)) where
  to : वर्ण → वर्णरूप × (वर्णरूप × वर्णसञ्ज्ञा)
  to v = रूपम् v , (स्थानी v , सञ्ज्ञा v)
  from : वर्णरूप × (वर्णरूप × वर्णसञ्ज्ञा) → वर्ण
  from (r , (s , j)) = वर्णः r s j

वर्ण≃२७ : वर्ण ≃ Fin 27
वर्ण≃२७ =
  compEquiv वर्ण-त्रिक
  (compEquiv (≃-× रूप≃३ (compEquiv (≃-× रूप≃३ सञ्ज्ञा≃३) (SumFin×≃ 3 3)))
             (SumFin×≃ 3 9))

------------------------------------------------------------------------
-- ३ · the base, and — by the Carrier law — the sthānivat itself.
------------------------------------------------------------------------

आधार≃८१ : आधार ≃ Fin 81
आधार≃८१ = compEquiv (≃-× वर्ण≃२७ रूप≃३) (SumFin×≃ 27 3)

-- THE JOIN.  Carrier≃ निर्धारितम् : आधार ≃ स्थानिवत्, so the state space
-- of the ādeśa operation — base AND carried datum AND witness — is
-- exactly the 81 states of the base.  Nothing was added by carrying:
-- the count IS the ahis, read as a number.
स्थानिवत्≃८१ : स्थानिवत् ≃ Fin 81
स्थानिवत्≃८१ = compEquiv (invEquiv आधार≃स्थानिवत्) आधार≃८१

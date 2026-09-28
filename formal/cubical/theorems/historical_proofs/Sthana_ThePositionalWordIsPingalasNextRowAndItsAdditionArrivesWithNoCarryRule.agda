{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- स्थानम् — स्थानात् स्थानं दशगुणं स्यात् ।
-- (sthnt sthna daagua syt: "from place to place let it be
--  ten-fold" — the place-value rule.)
--
-- THE TERM, ITS TEXT AND ITS DATE.  `स्थान` (sthāna, "place") in the
-- place-value sense is stated by ryabhaa, *ryabhaya*, Gaitapda 2
-- (499 CE): *sthnt sthna daagua syt*.  The metrical material is
-- Piṅgala, *छन्दःशास्त्रम्* ८.२४–२८ (~300 BCE): the प्रस्तार and its
-- next-row rule.
--
------------------------------------------------------------------------
-- WHAT THIS MODULE IS.  A SECOND CAUSEWAY, ROUTED, NOT BUILT.
--
-- `machine/Setubandha_TheCheckedIdentificationsAreEdgesAndTheIsolatedNodes
-- AreTheFrontier.hs` (absent from this repository) reports the largest component of this corpus's
-- identification graph: 10 nodes, diameter 3, hub `ℕ` at degree 7.  Among
-- its pairs at DISTANCE 2 is
--
--       Pingala.छन्दस्  ──[ Pingala.छन्दस्≡ℕ ]──  ℕ
--                       ──[ Digits.ℕ≡CanWord ]──  CanWord
--
-- and the two banks had never been joined: nothing in this corpus puts
-- Piṅgala's प्रस्तार and a base-b positional numeral in one statement.
-- `Setubandha_ThePrastarasNextRow…` (absent from this repository) walked the OTHER distance-2 route out
-- of छन्दस्, through `ℕ` to `Tally`.  This file walks this one, reusing
-- that route's own lemma rather than reproving it, so the two causeways
-- share a span.
--
-- NOTHING BELOW IS CONSTRUCTED BY HAND.  No induction over छन्दस्, no
-- case split on लघु/गुरु, no digit recursion, no carry lemma.  The one
-- definition that looks like a construction — `अङ्कानुक्रम` — repackages
-- two things `Digits` already proved (`sucw`,
-- `canonical-sucw`) into the pair type they were about; it introduces no
-- mathematics, and it exists only so that the theorem below has a
-- right-hand side to name.
--
-- THE FOUR THINGS THE ROUTE CARRIES.
--
--   १  अङ्कानुक्रम — Piṅgala's next-row rule, transported along the
--      composite, IS schoolbook increment-with-carry in base b, for every
--      b ≥ 2 simultaneously.  `Digits.agda` spends ~150 lines on `sucw`
--      and `value-sucw`; `Pingala.agda` never mentions a digit.  The
--      identification is `substComposite` of two checked transports.
--
--   २  A MONOID, MOVED AS ONE NODE.  `Digits.agda` defines NO addition
--      on `CanWord` — only the odometer.  Here `CanWord` acquires an
--      addition, an identity, associativity, both unit laws and `isSet`
--      in a single `subst MonoidStr`, because the whole structure travels
--      as one object.  Moving the carrier and re-proving the laws would
--      be the recomputation this construction exists to refuse.
--
--   ३  THE OPERATION IS THE RIGHT ONE.  The transported `_·_` is not an
--      abstract stand-in: `संकलन-मूल्य` says it is "read both words, add
--      the values, re-digit", and `मूल्य-संकलन` says `valueC` is a
--      homomorphism for it.  So it really is base-b addition — obtained
--      without ever writing the addition-with-carry algorithm.
--
--   ४  THE THIRD BANK.  Composing with `FreeMonoid.ℕ-Monoid≡Tally-Monoid`
--      identifies base-b positional addition with tally concatenation, as
--      monoids, in one `∙`.
------------------------------------------------------------------------

open import Cubical.Data.Nat using (ℕ)

module Sthana_ThePositionalWordIsPingalasNextRowAndItsAdditionArrivesWithNoCarryRule
  (k : ℕ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq)
open import Cubical.Foundations.Univalence using (ua ; transportUAop₁ ; transportUAop₂)
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (zero ; suc ; _+_)
open import Cubical.Data.Sigma using (Σ≡Prop ; ΣPathP ; _,_ ; fst ; snd)
open import Cubical.Algebra.Monoid.Base using (Monoid ; MonoidStr)

open import Mula.Pingala
  using (छन्दस् ; अनुक्रम ; छन्दस्≡ℕ ; transport-अनुक्रम-is-suc)
open import FreeMonoid
  using (Tally ; Tally-Monoid ; ℕ-Monoid ; ℕ-Monoid≡Tally-Monoid)
open import Digits k

------------------------------------------------------------------------
-- ० · THE ROUTE.  Two checked edges, composed.  This is the only new
--     path in the file and `_∙_` builds it.
------------------------------------------------------------------------

छन्दस्≡CanWord : छन्दस् ≡ CanWord
छन्दस्≡CanWord = छन्दस्≡ℕ ∙ ℕ≡CanWord

------------------------------------------------------------------------
-- १ · THE SECOND HALF OF THE ROUTE, made explicit.
--
--     `Digits.agda` proves `value-sucw`: the odometer computes the
--     successor.  Read across `ua ℕ≃CanWord` that says exactly: the
--     transport of `suc` IS the odometer.  This is a re-reading of a
--     theorem already checked there, not a new one.
------------------------------------------------------------------------

-- Repackaging only: `sucw` and `canonical-sucw` are both `Digits.agda`'s.
अङ्कानुक्रम : CanWord → CanWord
अङ्कानुक्रम (w , c) = sucw w , canonical-sucw w c

transport-suc-is-अङ्कानुक्रम :
  transport (λ i → ℕ≡CanWord i → ℕ≡CanWord i) suc ≡ अङ्कानुक्रम
transport-suc-is-अङ्कानुक्रम = funExt lemma
  where
    lemma : (x : CanWord)
          → transport (λ i → ℕ≡CanWord i → ℕ≡CanWord i) suc x ≡ अङ्कानुक्रम x
    lemma (w , c) =
        transportUAop₁ ℕ≃CanWord suc (w , c)
      ∙ Σ≡Prop isPropCanonical
          ( cong digits (sym (value-sucw w))
          ∙ digits-value (sucw w) (canonical-sucw w c) )

------------------------------------------------------------------------
-- २ · THE ROUTED THEOREM.
--
--     प्रस्तारस्य अग्रिमा पङ्क्तिः स्थानक्रमेण एकयुक्तिः ।
--     Pigala's next row is increment-with-carry in base b, for every
--     b ≥ 2.  `substComposite` is the statement that routing composes;
--     with it the two halves meet and no induction is performed.
------------------------------------------------------------------------

अनुक्रम-is-अङ्कानुक्रम :
  transport (λ i → छन्दस्≡CanWord i → छन्दस्≡CanWord i) अनुक्रम ≡ अङ्कानुक्रम
अनुक्रम-is-अङ्कानुक्रम =
    substComposite (λ A → A → A) छन्दस्≡ℕ ℕ≡CanWord अनुक्रम
  ∙ cong (subst (λ A → A → A) ℕ≡CanWord) transport-अनुक्रम-is-suc
  ∙ transport-suc-is-अङ्कानुक्रम

------------------------------------------------------------------------
-- ३ · A WHOLE STRUCTURE THAT CROSSES, WITH EVERY LAW IT HAS.
--
--     `Monoid ℓ = Σ[ A ∈ Type ℓ ] MonoidStr A`.  Transporting the
--     STRUCTURE along the carrier path moves operation, identity,
--     associativity, both unit laws and `isSet` together, because they
--     are fields of one record.  This is the model module's `Magma`
--     trick with the hand-rolled magma replaced by the library's monoid:
--     the same move, and it now carries four more laws for the same
--     `subst`.
------------------------------------------------------------------------

CanWord-Monoid : Monoid ℓ-zero
CanWord-Monoid = CanWord , subst MonoidStr ℕ≡CanWord (snd ℕ-Monoid)

-- The two banks, joined as monoids.  The second component is forced:
-- the structure was DEFINED as the transport, so `toPathP refl` closes it.
स्थानमार्गः : ℕ-Monoid ≡ CanWord-Monoid
स्थानमार्गः = ΣPathP (ℕ≡CanWord , toPathP refl)

शून्य : CanWord
शून्य = MonoidStr.ε (snd CanWord-Monoid)

संकलन : CanWord → CanWord → CanWord
संकलन = MonoidStr._·_ (snd CanWord-Monoid)

संकलन-साहचर्य : (x y z : CanWord)
              → संकलन x (संकलन y z) ≡ संकलन (संकलन x y) z
संकलन-साहचर्य = MonoidStr.·Assoc (snd CanWord-Monoid)

संकलन-शून्य-दक्षिणे : (x : CanWord) → संकलन x शून्य ≡ x
संकलन-शून्य-दक्षिणे = MonoidStr.·IdR (snd CanWord-Monoid)

संकलन-शून्य-वामे : (x : CanWord) → संकलन शून्य x ≡ x
संकलन-शून्य-वामे = MonoidStr.·IdL (snd CanWord-Monoid)

-- `Digits.agda` proves `isSetCanWord` directly; here it is again, and it
-- was not proved again — it rode across inside the record.
isSetCanWord-routed : isSet CanWord
isSetCanWord-routed = MonoidStr.is-set (snd CanWord-Monoid)

------------------------------------------------------------------------
-- ४ · THE OPERATION IS BASE-b ADDITION, AND NOT MERELY SOME OPERATION.
--
--     A transported structure is worthless if the transported operation
--     cannot be recognised.  It can:  `संकलन` is "read both words, add
--     the values, re-digit", and `valueC` is a homomorphism for it.
--     Neither statement is proved by digit recursion; both fall out of
--     the same path, read at its `_·_` field.
------------------------------------------------------------------------

संकलन-is-transported-+ :
  transport (λ i → ℕ≡CanWord i → ℕ≡CanWord i → ℕ≡CanWord i) _+_ ≡ संकलन
संकलन-is-transported-+ = fromPathP (λ i → MonoidStr._·_ (snd (स्थानमार्गः i)))

संकलन-मूल्य : (x y : CanWord) → संकलन x y ≡ digitsC (valueC x + valueC y)
संकलन-मूल्य x y =
    cong (λ f → f x y) (sym संकलन-is-transported-+)
  ∙ transportUAop₂ ℕ≃CanWord _+_ x y

मूल्य-संकलन : (x y : CanWord) → valueC (संकलन x y) ≡ valueC x + valueC y
मूल्य-संकलन x y =
    cong valueC (संकलन-मूल्य x y)
  ∙ value-digits (valueC x + valueC y)

------------------------------------------------------------------------
-- ५ · THE THIRD BANK, in one `∙`.
--
--     Base-b positional addition and tally concatenation are the same
--     monoid.  `FreeMonoid` proved its half; this file proved its own;
--     the composite is a path in `Monoid ℓ-zero` and required no third
--     argument.
------------------------------------------------------------------------

स्थान-तल्ली : CanWord-Monoid ≡ Tally-Monoid
स्थान-तल्ली = sym स्थानमार्गः ∙ ℕ-Monoid≡Tally-Monoid

CanWord≡Tally : CanWord ≡ Tally
CanWord≡Tally = cong ⟨_⟩ स्थान-तल्ली


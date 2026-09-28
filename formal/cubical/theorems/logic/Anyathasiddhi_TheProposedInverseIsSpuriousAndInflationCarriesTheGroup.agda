{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अन्यथासिद्धिः — the proposed antecedent is spurious, and the cause is
-- another.
--
-- THE TERM, ITS TEXT AND ITS DATE.  `अन्यथासिद्ध` (anyathāsiddha,
-- "established otherwise") is the Nyya-Vaieika technical term for a
-- factor that stands next to an effect, is proposed as its कारण, and is
-- excluded — because what it contributes is already accounted for
-- elsewhere.  The doctrine is stated with its fivefold classification
-- (पञ्चविध-अन्यथासिद्धि) in Annaṃbhaṭṭa, *Tarkasaṃgraha* with his own
-- *Dīpikā*, c. 1600 CE, on the कारण section; the notion is Navya-Nyāya and
-- is worked in Gaṅgeśa, *Tattvacintāmaṇi*, c. 1325 CE, whose कारणतावाद is
-- where the exclusion tests are argued.
--
-- AND THE SCHOOL IS NAMED BEFORE THE TERM IS USED, per CLAUDE.md (absent from this repository): this is
-- Nyya vocabulary, not Jaina.  A Jaina logician would not describe the
-- situation this way at all — for anekāntavāda the two candidate readings
-- of "the map back" would be two nayas to be indexed and held together,
-- and `Tantujala_…agda` is where this corpus does that.  Nyāya's move here
-- is the opposite one and it is the right one HERE, because the question
-- has a determinate answer: one of the two maps is the inverse and the
-- other provably is not.
--
------------------------------------------------------------------------
-- WHAT THIS MODULE IS.
--
-- `interactive/AnulomaPratiloma_…hs` proposes candidate inverse pairs by
-- matching type signatures inside one module and puts the round trip to
-- the kernel.  On `InflationVersusSubgroup` it proposed
--
--     infl : H2 → H4      ⇄      res : H4 → H2
--
-- and the kernel denied it.  This module says what the denial is worth,
-- in three parts.
--
--   १  THE PAIR IS REFUTED, AND THE HOST ALREADY PROVED WHY.  `res` is
--      identically `k0` (`res-is-zero`, InflationVersusSubgroup §4), so
--      `res ∘ infl` collapses both classes.  §१ below is one line and it
--      cites the host's own theorem.  Restriction to N ≤ ℤ/4 of a class
--      inflated from the quotient is zero: that is the mathematics, and it
--      is the whole point of the module that defined the two maps.
--
--   २  THE EDGE IS NEVERTHELESS REAL.  `infl` IS an equivalence — its
--      inverse is `res⁺`, defined here, which is not `res` and is not
--      restriction along anything.  So the refuted pair licenses no verdict
--      on the types: H2 ≃ H4 holds.  A machine that reported "not an
--      equivalence" from a failed round trip would have reported a falsehood
--      about the objects while reporting a truth about the pair, and those
--      are two different claims.
--
--   ३  THE EDGE CARRIES A GROUP.  H4 = H¹(ℤ/4, ℤ/2) has no operation in
--      the host module.  §३ gives it one, as the transport of the pointwise
--      sum on H2 = H¹(ℤ/2, ℤ/2), together with its associativity, in one
--      `subst` and with no case split on H4 — the `Setubandha_…agda`
--      pattern.  §४ then checks that the transported operation is the
--      pointwise sum of realizations, which is what makes the sentence
--      "inflation is a group isomorphism" true here rather than asserted.
------------------------------------------------------------------------

module Anyathasiddhi_TheProposedInverseIsSpuriousAndInflationCarriesTheGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; transportUAop₂)
open import Cubical.Foundations.Transport using (substSubst⁻)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; ΣPathP)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import InflationVersusSubgroup
  using ( Z4 ; z0 ; z1 ; z2 ; z3 ; Z2 ; e0 ; e1 ; _+2_
        ; proj ; incl
        ; H4 ; h0 ; hχ ; H2 ; k0 ; kι
        ; real4 ; real2 ; infl ; res ; res-is-zero
        ; k0≢kι ; h0≢hχ ; infl-is-inflation )

------------------------------------------------------------------------
-- १ · THE PROPOSAL IS REFUTED, BY THE HOST'S OWN THEOREM.
--
--     The machine asked for `res (infl c) ≡ c` for every c.  Taking
--     c = kι, `res-is-zero` gives k0, and the host proves k0 ≢ kι.
--
--     Note what is refuted: the PAIR.  Nothing here says anything about
--     whether H2 and H4 are equivalent, and §२ shows they are.
------------------------------------------------------------------------

res-is-not-a-retraction : ¬ ((c : H2) → res (infl c) ≡ c)
res-is-not-a-retraction ρ = k0≢kι (sym (res-is-zero (infl kι)) ∙ ρ kι)

-- The same failure read on the other side, so the refutation is not
-- an artefact of which composite was chosen: `infl ∘ res` is constant.
res-is-not-a-section : ¬ ((h : H4) → infl (res h) ≡ h)
res-is-not-a-section σ = h0≢hχ (sym (cong infl (res-is-zero hχ)) ∙ σ hχ)

------------------------------------------------------------------------
-- २ · THE REAL INVERSE, AND THE EDGE.
--
--     `res⁺` is not restriction.  It is the inverse of inflation, which on
--     this model exists because H¹(N,V) → H¹(G,V) is not the map in play:
--     inflation goes from the QUOTIENT's cohomology, and here the quotient
--     Γ = G/N and the subgroup N happen to be abstractly isomorphic, which
--     is exactly the coincidence that made the machine's signature match
--     fire.  The signature match was right about the arrows and wrong about
--     the maps.
------------------------------------------------------------------------

res⁺ : H4 → H2
res⁺ h0 = k0
res⁺ hχ = kι

infl-iso : Iso H2 H4
Iso.fun      infl-iso = infl
Iso.inv      infl-iso = res⁺
Iso.rightInv infl-iso h0 = refl
Iso.rightInv infl-iso hχ = refl
Iso.leftInv  infl-iso k0 = refl
Iso.leftInv  infl-iso kι = refl

H2≃H4 : H2 ≃ H4
H2≃H4 = isoToEquiv infl-iso

H2≡H4 : H2 ≡ H4
H2≡H4 = ua H2≃H4

-- `res⁺` really is another map: it disagrees with `res` at hχ, and that
-- single disequality is the whole of §१ restated as a separation of the
-- two candidate backward maps.
res⁺≢res : ¬ (res⁺ hχ ≡ res hχ)
res⁺≢res p = k0≢kι (sym (p ∙ res-is-zero hχ))

------------------------------------------------------------------------
-- ३ · WHAT CROSSES.  H¹(Γ,V) is a group under pointwise addition of
--     homomorphisms; two elements, so the table is two lines.  H4 has no
--     operation in the host module and acquires one here by transport,
--     with its associativity, in one `subst` — no case split on H4 occurs
--     anywhere below.
------------------------------------------------------------------------

_+H_ : H2 → H2 → H2
k0 +H y  = y
kι +H k0 = kι
kι +H kι = k0

+H-assoc : (a b c : H2) → (a +H b) +H c ≡ a +H (b +H c)
+H-assoc k0 b  c  = refl
+H-assoc kι k0 c  = refl
+H-assoc kι kι k0 = refl
+H-assoc kι kι kι = refl

-- (carrier , operation) as ONE object; the law rides on the pair.
Magma : Type₁
Magma = Σ[ A ∈ Type₀ ] (A → A → A)

Assoc : Magma → Type₀
Assoc (A , op) = (a b c : A) → op (op a b) c ≡ op a (op b c)

_+H4_ : H4 → H4 → H4
_+H4_ = subst (λ A → A → A → A) H2≡H4 _+H_

मार्गः : Path Magma (H2 , _+H_) (H4 , _+H4_)
मार्गः = ΣPathP (H2≡H4 , toPathP refl)

+H4-assoc : Assoc (H4 , _+H4_)
+H4-assoc = subst Assoc मार्गः +H-assoc

------------------------------------------------------------------------
-- ४ · THE TRANSPORTED OPERATION IS THE RIGHT ONE.
--
--     §३ produces an associative operation on H4 by fiat of transport;
--     that alone would be a checkmark and not a causeway.  This is the
--     content: the transported sum realizes as the pointwise sum of the
--     corresponding characters ℤ/4 → ℤ/2.  With §२ that is the statement
--     that inflation is an isomorphism OF GROUPS
--
--         H¹(G/N, V)  ≅  H¹(G, V)
--
--     on this model, and the only case split performed is on H2 (two
--     cases in `+H4-realizes`, via `res⁺`), never on H4's structure.
------------------------------------------------------------------------

-- The transported operation, unfolded once: `transportUAop₂` is the
-- library's statement that a binary operation moved along `ua` is the
-- conjugate of the original.
+H4-unfold : (x y : H4) → x +H4 y ≡ infl (res⁺ x +H res⁺ y)
+H4-unfold = transportUAop₂ H2≃H4 _+H_

-- Realization is a homomorphism from (H2 , +H) to pointwise sums, by four
-- lines on H2.  This is the only computation in the file.
real2-+H : (a b : H2) (x : Z2) → real2 (a +H b) x ≡ real2 a x +2 real2 b x
real2-+H k0 b  x = refl
real2-+H kι k0 e0 = refl
real2-+H kι k0 e1 = refl
real2-+H kι kι e0 = refl
real2-+H kι kι e1 = refl

+H4-realizes : (x y : H4) (g : Z4)
             → real4 (x +H4 y) g ≡ real4 x g +2 real4 y g
+H4-realizes x y g =
    cong (λ z → real4 z g) (+H4-unfold x y)
  ∙ infl-is-inflation (res⁺ x +H res⁺ y) g
  ∙ real2-+H (res⁺ x) (res⁺ y) (proj g)
  ∙ cong₂ _+2_ (sym (infl-is-inflation (res⁺ x) g))
               (sym (infl-is-inflation (res⁺ y) g))
  ∙ cong₂ (λ u v → real4 u g +2 real4 v g)
          (Iso.rightInv infl-iso x) (Iso.rightInv infl-iso y)

------------------------------------------------------------------------
-- ५ · THE SCOPE, EXACTLY, stated so nothing is read into it.
--
--   * That inflation is an isomorphism in general.  It is not.  The
--     inflation–restriction sequence is exact at H¹ with cokernel governed
--     by H¹(N,V)^Γ, and on this model that term vanishes because `res` is
--     zero — which is why the isomorphism holds HERE.  Nothing above
--     generalises and the host module's §3 says the same.
--   * That `res` is the wrong map to have defined.  It is the right map;
--     it is the only canonical map attached to a subgroup, and the host
--     module exists to say so.  What is refuted is the machine's proposal
--     that it inverts `infl`.
--   * That the Nyāya doctrine of अन्यथासिद्धि has any formal counterpart
--     below.  The term names the move; the checks are cubical type theory.
------------------------------------------------------------------------

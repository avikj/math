{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- विनिमयः · the exchange conjugates the split torus to its inverse
--
-- Prime-Pair Atlas Delta 17 (owner transmission D0017, held in git
-- history at zzz/collab/upstream/raw/D0017-prime-pair-atlas-delta-17.txt (absent from this repository)),
-- verbatim:
--
--   "17.3 Weyl group
--    The normalizer of the split torus has Weyl group Z/2, represented by
--    exchange p<->q.
--    T17.5 Exchange conjugates t to t^-1: tau diag(t^-1,t) tau^-1 = diag(t,t^-1).
--    C17.6 Binary pair exchange is the rank-one Weyl reflection of the
--    split torus."
--   "17.4 One-leg sign reflection is not the Weyl reflection
--    J2(p,q)=(p,-q) changes product pq -> -pq, hence Q -> -Q.
--    C17.7 Two involutions must remain distinct:
--      - Weyl/exchange: preserves split norm Q;
--      - one-leg sign reflection: swaps positive/negative norm sectors ..."
--
-- notes/DELTA17_SPLIT_TORUS_AUDIT.md (absent from this repository) (main): "§17.2–17.5 torus/Weyl.
-- T17.3, T17.5, T17.8 are not formalised." and its seed "PROVE: T17.5,
-- the Weyl conjugation, as a 2×2 matrix identity over ℤ. Cheap
-- (M2Unimodular.agda already has the toolkit)".
--
-- WHAT IS PROVED, in Gamma0Partner's 2×2 integer matrices (M = R⁴,
-- `mul`, `dia`):
--
--   τ · dia u t · τ ≡ dia t u          for ALL u t   (T17.5: τ is its own
--                                       inverse, so this is τ D τ⁻¹; with
--                                       u = t⁻¹ it is the transmission's line,
--                                       and no inverse is needed to state it)
--   τ · τ ≡ I                           (the Weyl group is ℤ/2)
--   Jʳ · dia u t · Jʳ ≡ dia u t           (the one-leg reflection centralises
--                                       the torus: it is NOT the Weyl element)
--   Jʳ · Jʳ ≡ I,  τ · Jʳ ≢ Jʳ · τ           (the two involutions are distinct and
--                                       do not commute; τ Jʳ = −Jʳ τ)
--   Q (τ v) ≡ Q v,  Q (Jʳ v) ≡ − Q v     (C17.7: exchange preserves the split
--                                       norm Q(p,q) = 4pq, one-leg reflection
--                                       negates it)
--
-- All identities are entrywise ring identities discharged by the
-- commutative-ring solver, exactly as M2Unimodular's adjugate identities.
-- Nothing is claimed about SO⁺(1,1) ≅ G_m or the hyperbolic parameter η.
------------------------------------------------------------------------

module VinimayaWeyl_TheExchangeConjugatesTheSplitTorusToItsInverseAndTheOneLegReflectionCommutesWithItSoTheTwoInvolutionsStayDistinct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc) renaming (_·_ to _·ℤ_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver.Reflection

open import Gamma0Partner using (R ; M ; mul ; dia)
open import M2Unimodular using (idm)

open CommRingStr (ℤCommRing .snd)

-- the exchange p ↔ q, and the one-leg sign reflection (p, q) ↦ (p, −q)
τ : M
τ = (0r , 1r , 1r , 0r)

Jʳ : M
Jʳ = (1r , 0r , 0r , - 1r)

-- The ring identities are proved over an arbitrary commutative ring and
-- instantiated at ℤ: the solver does not read ℤ's numerals directly.
module Identities {ℓ} (S : CommRing ℓ) where
  open CommRingStr (S .snd) renaming (_·_ to _*_ ; _+_ to _⊕_ ; -_ to ⊖_ ; 0r to O ; 1r to 𝟙)
  -- entries of τ · dia u t · τ
  e11 : (u t : fst S) → (O * u ⊕ 𝟙 * O) * O ⊕ (O * O ⊕ 𝟙 * t) * 𝟙 ≡ t
  e11 _ _ = solve! S
  e12 : (u t : fst S) → (O * u ⊕ 𝟙 * O) * 𝟙 ⊕ (O * O ⊕ 𝟙 * t) * O ≡ O
  e12 _ _ = solve! S
  e21 : (u t : fst S) → (𝟙 * u ⊕ O * O) * O ⊕ (𝟙 * O ⊕ O * t) * 𝟙 ≡ O
  e21 _ _ = solve! S
  e22 : (u t : fst S) → (𝟙 * u ⊕ O * O) * 𝟙 ⊕ (𝟙 * O ⊕ O * t) * O ≡ u
  e22 _ _ = solve! S
  -- entries of J · dia u t · J
  j11 : (u t : fst S) → (𝟙 * u ⊕ O * O) * 𝟙 ⊕ (𝟙 * O ⊕ O * t) * O ≡ u
  j11 _ _ = solve! S
  j12 : (u t : fst S) → (𝟙 * u ⊕ O * O) * O ⊕ (𝟙 * O ⊕ O * t) * (⊖ 𝟙) ≡ O
  j12 _ _ = solve! S
  j21 : (u t : fst S) → (O * u ⊕ (⊖ 𝟙) * O) * 𝟙 ⊕ (O * O ⊕ (⊖ 𝟙) * t) * O ≡ O
  j21 _ _ = solve! S
  j22 : (u t : fst S) → (O * u ⊕ (⊖ 𝟙) * O) * O ⊕ (O * O ⊕ (⊖ 𝟙) * t) * (⊖ 𝟙) ≡ t
  j22 _ _ = solve! S
  -- the split norm under the two involutions
  qτ : (p q : fst S) → (𝟙 ⊕ 𝟙 ⊕ 𝟙 ⊕ 𝟙) * ((O * p ⊕ 𝟙 * q) * (𝟙 * p ⊕ O * q)) ≡ (𝟙 ⊕ 𝟙 ⊕ 𝟙 ⊕ 𝟙) * (p * q)
  qτ _ _ = solve! S
  qJ : (p q : fst S) → (𝟙 ⊕ 𝟙 ⊕ 𝟙 ⊕ 𝟙) * ((𝟙 * p ⊕ O * q) * (O * p ⊕ (⊖ 𝟙) * q)) ≡ ⊖ ((𝟙 ⊕ 𝟙 ⊕ 𝟙 ⊕ 𝟙) * (p * q))
  qJ _ _ = solve! S

open Identities ℤCommRing

-- T17.5, for every u and t (u = t⁻¹ is the transmission's instance)
weyl : (u t : R) → mul (mul τ (dia u t)) τ ≡ dia t u
weyl u t i = e11 u t i , e12 u t i , e21 u t i , e22 u t i

-- the one-leg reflection centralises the torus
oneLeg : (u t : R) → mul (mul Jʳ (dia u t)) Jʳ ≡ dia u t
oneLeg u t i = j11 u t i , j12 u t i , j21 u t i , j22 u t i

-- both are involutions
τ² : mul τ τ ≡ idm
τ² = refl

Jʳ² : mul Jʳ Jʳ ≡ idm
Jʳ² = refl

-- and they do not commute: τ Jʳ = −(Jʳ τ)
τJʳʳ : mul τ Jʳ ≡ (0r , - 1r , 1r , 0r)
τJʳʳ = refl

Jʳτ : mul Jʳ τ ≡ (0r , 1r , - 1r , 0r)
Jʳτ = refl

τJʳʳ≢Jʳτ : ¬ (mul τ Jʳ ≡ mul Jʳ τ)
τJʳʳ≢Jʳτ p = negsuc≢pos (cong (fst ∘ snd) p)
  where
  negsuc≢pos : ¬ (negsuc 0 ≡ pos 1)
  negsuc≢pos q = subst P q tt
    where
    P : ℤ → Type
    P (pos _)    = ⊥
    P (negsuc _) = Unit

-- C17.7: the split norm Q(p, q) = 4pq is preserved by exchange and
-- negated by the one-leg reflection
Q : R × R → R
Q (p , q) = (1r + 1r + 1r + 1r) · (p · q)

act : M → R × R → R × R
act (a , b , c , e) (p , q) = (a · p + b · q , c · p + e · q)

Q-τ : (v : R × R) → Q (act τ v) ≡ Q v
Q-τ (p , q) = qτ p q

Q-Jʳ : (v : R × R) → Q (act Jʳ v) ≡ - Q v
Q-Jʳ (p , q) = qJ p q

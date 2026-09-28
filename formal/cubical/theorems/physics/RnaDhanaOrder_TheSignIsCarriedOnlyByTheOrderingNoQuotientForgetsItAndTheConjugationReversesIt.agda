{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ऋण-धन-क्रमः — the order on signed magnitude.  Brahmagupta's ṛṇa (debt)
-- and dhana (asset) ARE the two signs; the sign of an integer is the datum
-- an ORDERING carries, that no quotient forgets *to*, and that the sign
-- conjugation reverses.  This is the crystal's Order-edge fact
-- (runtime/CRYSTAL.md (absent from this repository) §1) and POSITIVITY_HAS_A_PLACE's "the ordering is the
-- avacchedaka (limitor)", made elementary and exact over ℤ.
--
-- THE CONVERGENCE (the reading).
-- One theorem in six vocabularies, each a face of "sign is preserved by no
-- averaging":
--   • positivity is a point of Sper K, chart-free only because |Sper ℚ|=1
--                          (POSITIVITY_HAS_A_PLACE; Artin–Schreier 1927)
--   • Galois conjugation swaps the orderings ⟹ (Iso;Order) unlicensed
--   • the runtime carries sign on exactly one of eleven edges, Order, and
--     no path through a Quotient delivers it        (runtime/CRYSTAL.md (absent from this repository) §1)
--   • the sieve's parity charge (−1,…,−1) is invisible to every averaging
--                                                              (TARGET.md (absent from this repository))
--
-- CHECKED over ℤ (Cubical.Data.Int):
--   §1  the sign conjugation neg (−_) is an involution — the Iso edge.
--   §2  neg PRESERVES the quotient abs:  abs (− n) ≡ abs n.  (Iso;Quotient)
--       is licensed — an isomorphism composes with a quotient.
--   §3  neg REVERSES the order sign:  sign (− n) ≡ flip (sign n).  So
--       (Iso;Order) is NOT the identity on sign: the conjugation swaps the
--       ordering, exactly the one edge pair the crystal refuses.
--   §4  sign does NOT factor through abs (the quotient that forgets sign):
--       ¬ Σ[ s ∈ (ℕ → Sign) ] (∀ n → s (abs n) ≡ sign n).
--   §5  the abs-fibre over a positive value is the two-point {n, −n}, split
--       by sign — sign is exactly what the quotient forgets, and it is an
--       order datum, so only an Order edge recovers it.
--
-- Sources: Brahmagupta, Brhmasphuasiddhnta 18 (628), the
-- a/dhana sign rules; Artin–Schreier 1927 (formally real fields).
------------------------------------------------------------------------

module RnaDhanaOrder_TheSignIsCarriedOnlyByTheOrderingNoQuotientForgetsItAndTheConjugationReversesIt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ; pos; negsuc; -_; abs)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- ऋण / शून्य / धन — debt, void, asset: Brahmagupta's three signs.
data Sign : Type where
  rna   : Sign     -- ṛṇa   · negative
  sunya : Sign     -- śūnya · zero
  dhana : Sign     -- dhana · positive

sign : ℤ → Sign
sign (pos zero)    = sunya
sign (pos (suc _)) = dhana
sign (negsuc _)    = rna

-- viparyaya — the reversal: ṛṇa ↔ dhana, śūnya fixed.
flip : Sign → Sign
flip rna   = dhana
flip sunya = sunya
flip dhana = rna

------------------------------------------------------------------------
-- §1 · The Iso edge: the sign conjugation is an involution.
neg-involution : (n : ℤ) → - (- n) ≡ n
neg-involution (pos zero)    = refl
neg-involution (pos (suc _)) = refl
neg-involution (negsuc _)    = refl

------------------------------------------------------------------------
-- §2 · (Iso ; Quotient) is licensed: neg preserves abs.
neg-preserves-abs : (n : ℤ) → abs (- n) ≡ abs n
neg-preserves-abs (pos zero)    = refl
neg-preserves-abs (pos (suc _)) = refl
neg-preserves-abs (negsuc _)    = refl

------------------------------------------------------------------------
-- §3 · (Iso ; Order) is NOT the identity on sign: neg reverses it.
neg-reverses-sign : (n : ℤ) → sign (- n) ≡ flip (sign n)
neg-reverses-sign (pos zero)    = refl
neg-reverses-sign (pos (suc _)) = refl
neg-reverses-sign (negsuc _)    = refl

------------------------------------------------------------------------
-- the two nonzero signs are distinct (a Sign is not a Bool: it is the
-- three-verdict codomain a/nya/dhana, never a two-valued collapse).
private
  tag : Sign → Bool
  tag dhana = true
  tag _     = false

rna≢dhana : ¬ (rna ≡ dhana)
rna≢dhana p = true≢false (sym (cong tag p))

------------------------------------------------------------------------
-- §4 · sign does NOT factor through abs.  No reader s of the magnitude
-- alone can reproduce the sign: the two integers ±1 share a magnitude and
-- differ in sign, so s(1) would have to be both dhana and a.
signNotThroughAbs :
  ¬ (Σ[ s ∈ (ℕ → Sign) ] ((n : ℤ) → s (abs n) ≡ sign n))
signNotThroughAbs (s , e) =
  rna≢dhana (sym (e (negsuc zero)) ∙ e (pos (suc zero)))

------------------------------------------------------------------------
-- §5 · the abs-fibre over a positive magnitude is the two-point {n, −n},
-- carrying the same quotient value and separated exactly by sign.
absFibreIsSplitBySign :
  (abs (pos (suc zero)) ≡ abs (negsuc zero))
  × (¬ (sign (pos (suc zero)) ≡ sign (negsuc zero)))
absFibreIsSplitBySign = refl , λ p → rna≢dhana (sym p)

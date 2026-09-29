{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CongruenceLiftsAreGradePreserving
--
-- The shared engine under every cost lemma, isolated. A derivation can be
-- lifted under any one-hole context (`suc _`, `add _ z`, `add z _`) by
-- applying the matching congruence step to each of its steps, and this lift
-- PRESERVES LENGTH. Consequence: a derivation assembled by structural
-- recursion over a term's syntax has length equal to the number of redexes
-- it eliminates — which is why `winding-cost`, `addClosed`, and `mulPeel`
-- all come out linear in the size they traverse. One engine, all cases.
------------------------------------------------------------------------

module CongruenceLiftsAreGradePreserving where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Kernel.RewriteCertificate

len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

private
  s : ℕ → ℕ
  s k = suc k

underSuc : {a b : Tm} → Derivation a b → Derivation (suc a) (suc b)
underSuc (done x)        = done (suc x)
underSuc (then-step p d) = then-step (suc-step p) (underSuc d)

underAddL : {a b : Tm} → Derivation a b → (z : Tm) → Derivation (add a z) (add b z)
underAddL (done x)        z = done (add x z)
underAddL (then-step p d) z = then-step (add-left p z) (underAddL d z)

underAddR : (z : Tm) → {a b : Tm} → Derivation a b → Derivation (add z a) (add z b)
underAddR z (done x)        = done (add z x)
underAddR z (then-step p d) = then-step (add-right z p) (underAddR z d)

len-underSuc : {a b : Tm} (d : Derivation a b) → len (underSuc d) ≡ len d
len-underSuc (done _)        = refl
len-underSuc (then-step _ d) = cong s (len-underSuc d)

len-underAddL : {a b : Tm} (d : Derivation a b) (z : Tm) → len (underAddL d z) ≡ len d
len-underAddL (done _)        z = refl
len-underAddL (then-step _ d) z = cong s (len-underAddL d z)

len-underAddR : (z : Tm) {a b : Tm} (d : Derivation a b) → len (underAddR z d) ≡ len d
len-underAddR z (done _)        = refl
len-underAddR z (then-step _ d) = cong s (len-underAddR z d)

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WindingCostIsUnarySize
--
-- Ledger entry K, made a term. The canonical transport that reaches
-- "standpoint n" over the successor structure — reducing (var + n) to
-- sucⁿ var, with n written in the kernel's own UNARY representation —
-- costs exactly n+1 steps. Cost = unary symbolic size, linear. No search:
-- the length is the winding number.
--
-- This is H (transport along the successor loop is the integer winding)
-- read in the unary `Tm`: the exponential the classical (binary) measure
-- reports lives only in the unary→succinct compression (`eval`, the
-- forgetful projection), not in this reduction.
------------------------------------------------------------------------

module WindingCostIsUnarySize where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Kernel.RewriteCertificate

-- the symbolic (unary) representation of n : a suc-tower of height n
unary : ℕ → Tm
unary zero    = zero
unary (suc n) = suc (unary n)

-- n-fold successor applied to a term
iterSuc : ℕ → Tm → Tm
iterSuc zero    t = t
iterSuc (suc n) t = suc (iterSuc n t)

-- derivation length : the number of steps carried
len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

-- lift a derivation under one successor, applying suc-step to each step;
-- length preserved exactly.
underSuc : {a b : Tm} → Derivation a b → Derivation (suc a) (suc b)
underSuc (done x)        = done (suc x)
underSuc (then-step s d) = then-step (suc-step s) (underSuc d)

len-underSuc : {a b : Tm} (d : Derivation a b) → len (underSuc d) ≡ len d
len-underSuc (done _)        = refl
len-underSuc (then-step _ d) = cong suc (len-underSuc d)

-- THE WINDING to standpoint n : reduce (var + n) to sucⁿ var, n in unary.
addTower : (n : ℕ) → Derivation (add var (unary n)) (iterSuc n var)
addTower zero    = then-step (add-zero var) (done var)
addTower (suc m) = then-step (add-suc var (unary m)) (underSuc (addTower m))

-- COST = UNARY SIZE : the winding costs exactly n+1 steps, linear in the
-- unary symbolic size of the input. Checked, --safe.
winding-cost-is-unary-size : (n : ℕ) → len (addTower n) ≡ suc n
winding-cost-is-unary-size zero    = refl
winding-cost-is-unary-size (suc m) =
  cong (λ (k : ℕ) → suc k) (len-underSuc (addTower m) ∙ winding-cost-is-unary-size m)

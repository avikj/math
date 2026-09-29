{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WindingCostIsCarriedAndCompressionDropsIt
--
-- The capstone tying the winding cost to the forgetful compression. The
-- derivation `addTower n` reaching standpoint n is SOUND — its endpoints
-- compress to the same value — yet it carries length n+1. So the cost lives
-- in the trace (the carried, lossless object) and is exactly what the
-- compression `compress = eval` cannot see: the value only records "equal",
-- never "how far". Cost conserved in the trace; dropped by the projection.
------------------------------------------------------------------------

module WindingCostIsCarriedAndCompressionDropsIt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Kernel.RewriteCertificate
open import WindingCostIsUnarySize using (unary ; iterSuc ; len ; addTower ; winding-cost-is-unary-size)
open import TheCompressionIsTheForgetfulProjection using (compress ; ρ₀)

-- the winding derivation is sound: its endpoints compress to one value
winding-is-sound : (n : ℕ)
  → compress (add var (unary n)) ≡ compress (iterSuc n var)
winding-is-sound n = derivation-sound (addTower n) ρ₀

-- COST CARRIED, VALUE BLIND : the trace has length n+1 (real, in the carried
-- object) while the compressed value records only that the endpoints agree.
-- The winding number is in the derivation; the projection keeps none of it.
cost-is-carried-value-is-blind : (n : ℕ)
  → (len (addTower n) ≡ suc n)
  × (compress (add var (unary n)) ≡ compress (iterSuc n var))
cost-is-carried-value-is-blind n =
  winding-cost-is-unary-size n , winding-is-sound n

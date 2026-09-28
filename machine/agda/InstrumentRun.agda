{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InstrumentRun — the self-improving instrument as a NATIVE BINARY.
--
-- The --safe cubical core proves the self-improvement object converges
-- (SelfImprovingCrystal: the run reaches a fixed point, meaning held to
-- identity by bisim).  This module is an IO membrane (a `mukha`) that runs
-- an ILLUSTRATIVE instance of the same shape — a measure that strictly
-- descends to its fixed point — and prints the witness.  It is NOT linked
-- to SelfImprovingCrystal: it shows that compiled Agda executes a
-- descending run, not that the cubical object converges.
--
-- Self-contained (Agda.Builtin only) so `agda -c` compiles it through
-- GHC/MAlonzo to a standalone executable with no library entanglement.
------------------------------------------------------------------------

module InstrumentRun where

open import Agda.Builtin.Nat using (Nat ; zero ; suc)
open import Agda.Builtin.String using (String ; primStringAppend)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

-- A concrete self-improvement policy: a measure strictly descends,
-- fixed point at 0.  ("measure", not "defect": nothing is defective — it is
-- just a monotone quantity.  The cubical core generalises to any run whose
-- measure does not increase; here a strictly-descending one so the fixed
-- point is genuinely reached and the execution is non-trivial.)
descend : Nat → Nat
descend zero    = zero
descend (suc n) = n

-- run the policy k steps
iterate : Nat → Nat → Nat
iterate zero    x = x
iterate (suc k) x = iterate k (descend x)

atFixedPoint : Nat → Bool
atFixedPoint zero    = true
atFixedPoint (suc _) = false

bool : Bool → String
bool b = if b then "true" else "false"

infixr 5 _++_
_++_ : String → String → String
_++_ = primStringAppend

-- The witness, COMPUTED (not constant): from measure 100, 100 steps reach
-- the fixed point; 50 steps do not — so the run is genuinely executing.
witness : String
witness =
  "self-improving instrument — concrete run\n" ++
  "  policy: measure n -> n-1 (strictly descending), fixed point 0\n" ++
  "  from measure 100, after 100 steps at fixed point = " ++ bool (atFixedPoint (iterate 100 100)) ++ "\n" ++
  "  from measure 100, after  50 steps at fixed point = " ++ bool (atFixedPoint (iterate 50 100)) ++ "\n" ++
  "  => a descending run executed (illustrative; not the cubical object).\n"

postulate putStr' : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC putStr' = TIO.putStr #-}

main : IO ⊤
main = putStr' witness

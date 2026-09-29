{-# OPTIONS --cubical --safe --no-import-sorts #-}
module AbhijnanaProbes.P003 where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
-- the index of a 0-parameter fibre is a LITERAL lifted out of the source
-- line (, ), so the constructors have to be in scope
-- or the probe dies [NotInScope] and the death is the instrument's, not
-- the corpus's.
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
import DependentOptimizationFibration as M
import DependentOptimizationFibration as F

_ : (b : _) → fiber M.semantics b ≡ F.SemanticFiber b
_ = λ b → refl

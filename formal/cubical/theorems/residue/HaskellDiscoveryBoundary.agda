{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- The deterministic five-round output of interactive/MathMachine.hs (absent from this repository), promoted
-- from strings to a typed arithmetic object.
--
-- Haskell emits its live discoveries as a temporary Agda module.  That
-- module must prove by refl that its AST is `expectedDiscoveries`, then
-- transports `expectedDiscoveriesSound` below onto the generated output.
-- Thus the smoke run is not certified because seven lines look plausible:
-- every generated equation denotes a universally quantified equality of
-- naturals, and the Agda kernel checks all seven proofs.
--
-- This is a bounded bridge, not a certificate for arbitrary rounds or
-- invented symbols; finite fingerprints are never treated as proofs here.
------------------------------------------------------------------------

module HaskellDiscoveryBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; +-zero ; ·-comm ; 0≡m·0)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

infixl 20 _+T_ _·T_

data HaskellTerm : Type₀ where
  var   : ℕ → HaskellTerm
  zeroT : HaskellTerm
  sucT  : HaskellTerm → HaskellTerm
  _+T_  : HaskellTerm → HaskellTerm → HaskellTerm
  _·T_  : HaskellTerm → HaskellTerm → HaskellTerm

Environment : Type₀
Environment = ℕ → ℕ

evaluate : Environment → HaskellTerm → ℕ
evaluate ρ (var n)  = ρ n
evaluate ρ zeroT    = zero
evaluate ρ (sucT t) = suc (evaluate ρ t)
evaluate ρ (l +T r) = evaluate ρ l + evaluate ρ r
evaluate ρ (l ·T r) = evaluate ρ l · evaluate ρ r

Equation : Type₀
Equation = HaskellTerm × HaskellTerm

Sound : Equation → Type₀
Sound (l , r) = (ρ : Environment) → evaluate ρ l ≡ evaluate ρ r

data AllSound : List Equation → Type₀ where
  all[]  : AllSound []
  _all∷_ : {e : Equation} {es : List Equation}
         → Sound e → AllSound es → AllSound (e ∷ es)

infixr 20 _all∷_

x y z : HaskellTerm
x = var 0
y = var 1
z = var 2

-- This order is Haskell's `Data.Map` key order, exactly what the emitter
-- serialises.  A change in generation, canonicalisation, proof admission,
-- or ordering changes the generated AST and breaks the refl bridge.

-- Note which are refl and which are not.  Four of the eight are
-- definitional in cubical ℕ (0+n, suc n+m, 0·n, 1+n all reduce).  THREE
-- OF THE OTHER FOUR ARE NOT: n ≡ n+0 and n ≡ 1·n need +-zero, and
-- commutativity needs +-comm.  So the bridge
-- carries a discovery whose soundness is a THEOREM rather than a
-- computation.
expectedDiscoveries : List Equation
expectedDiscoveries =
    (x , sucT zeroT ·T x)
  ∷ (x , x +T zeroT)
  ∷ (x , zeroT +T x)
  ∷ (x +T y , y +T x)
  ∷ (sucT x +T y , sucT (x +T y))
  ∷ (sucT x +T y , sucT (y +T x))
  ∷ (zeroT , zeroT ·T x)
  ∷ (sucT x , sucT zeroT +T x)
  ∷ []

-- The four the machine found FIRST, kept in its order.  Which are refl and
-- which are not is the interesting part and is marked at each.

sound-1 : Sound (x , sucT zeroT ·T x)          -- n ≡ 1 · n   NOT refl
sound-1 ρ = sym (+-zero (ρ 0))                 -- 1·n reduces to n+0

sound-2 : Sound (x , x +T zeroT)               -- n ≡ n + 0   NOT refl
sound-2 ρ = sym (+-zero (ρ 0))

sound-3 : Sound (x , zeroT +T x)               -- n ≡ 0 + n   refl
sound-3 ρ = refl

sound-4 : Sound (x +T y , y +T x)              -- COMMUTATIVITY  NOT refl
sound-4 ρ = +-comm (ρ 0) (ρ 1)

sound-5 : Sound (sucT x +T y , sucT (x +T y))  -- refl
sound-5 ρ = refl

sound-6 : Sound (sucT x +T y , sucT (y +T x))  -- NOT refl
sound-6 ρ = cong suc (+-comm (ρ 0) (ρ 1))

sound-7 : Sound (zeroT , zeroT ·T x)           -- 0 ≡ 0 · n
sound-7 ρ = 0≡m·0 (ρ 0) ∙ sym (·-comm zero (ρ 0))

sound-8 : Sound (sucT x , sucT zeroT +T x)     -- refl
sound-8 ρ = refl

expectedDiscoveriesSound : AllSound expectedDiscoveries
expectedDiscoveriesSound =
  sound-1 all∷ sound-2 all∷ sound-3 all∷ sound-4 all∷
  sound-5 all∷ sound-6 all∷ sound-7 all∷ sound-8 all∷ all[]

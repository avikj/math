{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ForgetfulCompressionPricesTheDrop
--
-- Ledger entry L, made a term. `eval`/`derivation-sound` is the forgetful
-- projection: it lands in ℕ (a set), so it collapses distinct routes to one
-- meaning. Here the collapse is exhibited AND priced: the kernel's own two
-- histories between the same endpoints have EQUAL image under the semantics,
-- yet PROVABLY DIFFERENT length (2 vs 4). So the route/cost the compression
-- drops is real and is not recoverable from the meaning — the classical
-- "cost" lives in exactly this forgetting, not in the carried computation.
------------------------------------------------------------------------

module ForgetfulCompressionPricesTheDrop where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; injSuc ; znots)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)

len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

-- the two routes have length 2 and 4, definitionally
len-direct : len direct-history ≡ suc (suc zero)
len-direct = refl

len-detour : len detour-history ≡ suc (suc (suc (suc zero)))
len-detour = refl

2≢4 : ¬ (suc (suc zero) ≡ suc (suc (suc (suc zero))))
2≢4 p = znots (injSuc (injSuc p))

-- the route is genuinely dropped: distinct length, but the forgetful
-- semantics cannot tell them apart (ℕ is a set).
route-length-differs : ¬ (len direct-history ≡ len detour-history)
route-length-differs = 2≢4

meaning-agrees : (ρ : Env)
  → derivation-sound direct-history ρ ≡ derivation-sound detour-history ρ
meaning-agrees ρ =
  isSetℕ (eval seed ρ) (eval target₀ ρ)
    (derivation-sound direct-history ρ) (derivation-sound detour-history ρ)

-- L, packaged: the compression collapses (meaning agrees) a distinction that
-- is real in the calculus (length differs). The drop is priced, not free.
the-drop-is-real-and-priced :
    (¬ (len direct-history ≡ len detour-history))
  × ((ρ : Env) → derivation-sound direct-history ρ ≡ derivation-sound detour-history ρ)
the-drop-is-real-and-priced = route-length-differs , meaning-agrees

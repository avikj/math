{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheCompressionIsTheForgetfulProjection
--
-- The bridge between WindingCostIsUnarySize, ForgetfulCompressionPricesTheDrop
-- and the fibre law. `eval` at a fixed environment is the compression from a
-- term (a derivation-carrying, structured object) down to its value. It is a
-- forgetful map, and its INPUT-side fibre — the terms that reach a given
-- value — is exhibited non-contractible: over `a + b` the compression
-- identifies the structured sum `a + b` with the bare value `unary (a+b)`,
-- two provably distinct terms. That collapsed structure is exactly what the
-- forgetful projection drops. The winding (unary) value agrees with the
-- computed value (`eval-unary`), so the drop is the additive/derivation
-- structure, not the number.
------------------------------------------------------------------------

module TheCompressionIsTheForgetfulProjection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; snotz)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; Σ-contractSnd)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
open import WindingCostIsUnarySize using (unary)

-- a fixed environment; `unary n` is closed, so its value is env-independent
ρ₀ : Env
ρ₀ = env 0 0 0 0 0 0

-- THE COMPRESSION : a structured term to its value
compress : Tm → ℕ
compress t = eval t ρ₀

-- the unary (winding) term evaluates to its index : winding value = number
eval-unary : (n : ℕ) → compress (unary n) ≡ n
eval-unary zero    = refl
eval-unary (suc n) = cong suc (eval-unary n)

-- a structured sum evaluates to the sum
eval-add-unary : (a b : ℕ) → compress (add (unary a) (unary b)) ≡ a + b
eval-add-unary a b = cong₂ _+_ (eval-unary a) (eval-unary b)

-- THE FIBRE of the compression over a value : the terms that reach it.
-- This is the input-binding of the fibre law for `compress`.
Fib : ℕ → Type₀
Fib n = Σ[ t ∈ Tm ] (compress t ≡ n)

sum-in-fibre value-in-fibre : (a b : ℕ) → Fib (a + b)
sum-in-fibre   a b = add (unary a) (unary b) , eval-add-unary a b
value-in-fibre a b = unary (a + b)           , eval-unary (a + b)

-- the two are distinct terms (one is an `add`, the other never is)
isAddTag : Tm → ℕ
isAddTag (add _ _) = suc zero
isAddTag _         = zero

tag-unary : (n : ℕ) → isAddTag (unary n) ≡ zero
tag-unary zero    = refl
tag-unary (suc n) = refl

structured≢value : (a b : ℕ)
  → ¬ (fst (sum-in-fibre a b) ≡ fst (value-in-fibre a b))
structured≢value a b p = snotz (cong isAddTag p ∙ tag-unary (a + b))

-- THE DROP, NAMED : the compression's fibre over a+b contains two provably
-- distinct terms. The forgetful projection is not an equivalence; what it
-- forgets is the additive structure, while agreeing on the value.
compression-forgets-structure : (a b : ℕ)
  → Σ[ x ∈ Fib (a + b) ] Σ[ y ∈ Fib (a + b) ] (¬ (fst x ≡ fst y))
compression-forgets-structure a b =
  sum-in-fibre a b , value-in-fibre a b , structured≢value a b

-- THE CARRIED SIDE IS FREE : bind the OUTPUT and the fibre Σ[n] (compress t ≡ n)
-- = singl (compress t) is contractible, so carrying the value costs nothing.
-- With compression-forgets-structure (the costly input binding) this is the
-- full fibre law on the kernel's own compression: free to carry the value,
-- non-trivial to recover the structure.
carried-side-is-free : (Σ[ t ∈ Tm ] Σ[ n ∈ ℕ ] (compress t ≡ n)) ≃ Tm
carried-side-is-free = Σ-contractSnd (λ t → isContrSingl (compress t))

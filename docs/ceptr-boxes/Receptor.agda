{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Receptor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; znots)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

-- a receptor: at every state, for every signal on its carrier, a
-- successor, a receipt that the transition is the one its expectation
-- prescribes, and the rest of the unfolding.
record ISC {ℓ : Level} (S : Type ℓ) (Q : S → Type ℓ)
           (E : (s : S) → Q s → S → Type ℓ) (s : S) : Type ℓ where
  coinductive
  field
    respond : (q : Q s) → Σ[ s' ∈ S ] (E s q s' × ISC S Q E s')
open ISC

-- 1 · the receptor whose one expectation is a receipt: the successor
--     must be the prescribed one.  The receptor is the successor it wraps.

DetISC : ℕ → Type
DetISC = ISC ℕ (λ _ → Unit) (λ s _ s' → suc s ≡ s')

counter : (n : ℕ) → DetISC n
respond (counter n) _ = suc n , refl , counter (suc n)

-- the coinductive spine of the contraction: along any receipt the
-- canonical behaviour deforms onto any behaviour.
uniqueP : (s₀ s₁ : ℕ) (p : suc s₀ ≡ s₁) (e : DetISC s₁)
  → PathP (λ i → DetISC (p i)) (counter (suc s₀)) e
respond (uniqueP s₀ s₁ p e i) tt = σ i , sq i , uniqueP (suc s₀) b σ r i
  where
  b : ℕ
  b = fst (respond e tt)
  q : suc s₁ ≡ b
  q = fst (snd (respond e tt))
  r : DetISC b
  r = snd (snd (respond e tt))
  σ : suc (suc s₀) ≡ b
  σ = cong suc p ∙ q
  sq : PathP (λ i → suc (p i) ≡ σ i) refl q
  sq = isSet→isSet' isSetℕ refl q (cong suc p) σ

-- THE COLLAPSE.  Once the event is a receipt, the space of behaviours
-- is a point at every state: determinism is contractibility, and the
-- successor is its centre.
deterministicCollapse : (n : ℕ) → isContr (DetISC n)
deterministicCollapse n = counter n , contract
  where
  contract : (e : DetISC n) → counter n ≡ e
  respond (contract e i) tt = p i , (λ j → p (i ∧ j)) , uniqueP n b p r i
    where
    b : ℕ
    b = fst (respond e tt)
    p : suc n ≡ b
    p = fst (snd (respond e tt))
    r : DetISC b
    r = snd (snd (respond e tt))

-- 2 · the same carrier, a free expectation: any successor is licensed.
--     Receptivity opens the space: the receptor that stands still and
--     the one that steps are distinct behaviours.

FreeISC : ℕ → Type
FreeISC = ISC ℕ (λ _ → Unit) (λ _ _ _ → Unit)

stayer : (n : ℕ) → FreeISC n
respond (stayer n) _ = n , tt , stayer n

stepper : (n : ℕ) → FreeISC n
respond (stepper n) _ = suc n , tt , stepper (suc n)

receptivityIsStrictlyWider : ¬ isContr (FreeISC zero)
receptivityIsStrictlyWider c =
  znots (cong (λ e → fst (respond e tt)) (isContr→isProp c (stayer zero) (stepper zero)))

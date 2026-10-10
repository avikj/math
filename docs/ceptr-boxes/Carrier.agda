{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Carrier where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)

-- a receptor, as a guarded coalgebra: at every state, for every signal
-- the environment can put on the carrier, a successor, a receipt that
-- the transition is the one its expectation prescribes, and the rest
-- of the unfolding.
record ISC {ℓ : Level} (S : Type ℓ) (Q : S → Type ℓ)
           (E : (s : S) → Q s → S → Type ℓ) (s : S) : Type ℓ where
  coinductive
  field
    respond : (q : Q s) → Σ[ s' ∈ S ] (E s q s' × ISC S Q E s')
open ISC

-- a semantic datum: a value together with its type.  There is no bare int.
Point : (ℓ : Level) → Type (ℓ-suc ℓ)
Point ℓ = Σ[ A ∈ Type ℓ ] A

point : {ℓ : Level} {A : Type ℓ} → A → Point ℓ
point {A = A} a = A , a

-- the general carrier: a signal at s is any transformation out of s's
-- type, into any type whatsoever.  The carrier is the universe.
Question : {ℓ : Level} → Point ℓ → Type (ℓ-suc ℓ)
Question {ℓ} s = Σ[ B ∈ Type ℓ ] (fst s → B)

target : {ℓ : Level} (s : Point ℓ) → Question s → Point ℓ
target s (B , f) = B , f (snd s)

-- the expectation: the successor is the signal's own result.
Event : {ℓ : Level} (s : Point ℓ) → Question s → Point ℓ → Type (ℓ-suc ℓ)
Event s q s' = target s q ≡ s'

Receptor : {ℓ : Level} → Point ℓ → Type (ℓ-suc ℓ)
Receptor {ℓ} = ISC (Point ℓ) Question Event

-- receiving on the general carrier is total: every signal of every
-- type is answered, with its receipt, and the receptor continues.
receive : {ℓ : Level} (s : Point ℓ) → Receptor s
respond (receive s) q = target s q , refl , receive (target s q)

-- one signal, by computation
step : {ℓ : Level} {A B : Type ℓ} (a : A) (f : A → B)
  → fst (respond (receive (point a)) (B , f)) ≡ point (f a)
step a f = refl

-- two signals in sequence compose
twoSteps : {ℓ : Level} {A B C : Type ℓ} (a : A) (f : A → B) (g : B → C)
  → target (target (point a) (B , f)) (C , g) ≡ point (g (f a))
twoSteps a f g = refl

-- fractal nesting: a receptor is instantiated in the space of another
-- receptor, one universe up; there is no top.
nest : {ℓ : Level} → Point ℓ → Point (ℓ-suc ℓ)
nest {ℓ} s = Point ℓ , s

outer : {ℓ : Level} (s : Point ℓ) → Receptor (nest s)
outer s = receive (nest s)

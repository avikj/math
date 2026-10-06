{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module InteractionLedger where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-assoc ; +-comm)
open import Cubical.Data.Nat.Properties using (+-zero)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; ≤-+k ; ≤SumLeft)

-- The runtime has more than one cost receiver. This event alphabet keeps
-- the interaction count and fresh term-heap allocation in one explicit
-- trace, without pretending either component is semantic meaning.
data Event : Type where
  dupSupEqual dupSupDifferent : Event
  dupLamUsed dupLamErased : Event
  dupNode : ℕ → Event
  appSup appMatSup andSup orSup : Event
  andZero andOne orZero orOne : Event

record Charge : Type where
  constructor charge
  field
    interactions : ℕ
    heapWords    : ℕ

open Charge public

-- These are the direct source-level local charges from HVM4. Constructors
-- allocate through helpers; the values here include those helper words.
localCharge : Event → Charge
localCharge dupSupEqual     = charge 1 0
localCharge dupSupDifferent = charge 1 4
localCharge dupLamUsed      = charge 1 5
localCharge dupLamErased    = charge 1 3
localCharge (dupNode a)     = charge 1 (2 · a)
localCharge appSup           = charge 1 3
localCharge appMatSup        = charge 1 5
localCharge andSup           = charge 1 3
localCharge orSup            = charge 1 3
localCharge andZero          = charge 1 0
localCharge andOne           = charge 1 0
localCharge orZero           = charge 1 0
localCharge orOne            = charge 1 0

_⊞_ : Charge → Charge → Charge
charge i h ⊞ charge j k = charge (i + j) (h + k)

infixl 6 _⊞_

zeroCharge : Charge
zeroCharge = charge zero zero

charge-assoc : (a b c : Charge) → (a ⊞ b) ⊞ c ≡ a ⊞ (b ⊞ c)
charge-assoc (charge i h) (charge j k) (charge l m) =
  cong₂ (λ x y → charge x y) (sym (+-assoc i j l)) (sym (+-assoc h k m))

data Trace : ℕ → Type where
  done : Trace zero
  step : (e : Event) {n : ℕ} → Trace n → Trace (suc n)

ledger : {n : ℕ} → Trace n → Charge
ledger done = zeroCharge
ledger (step e rest) = localCharge e ⊞ ledger rest

interactionTotal : {n : ℕ} → Trace n → ℕ
interactionTotal done = zero
interactionTotal (step e rest) = suc (interactionTotal rest)

heapTotal : {n : ℕ} → Trace n → ℕ
heapTotal t = heapWords (ledger t)

-- Every event is one interaction. Thus the interaction receiver is exactly
-- the trace index, independently of event kind and allocation.
interactionTotal-is-length : {n : ℕ} (t : Trace n)
  → interactionTotal t ≡ n
interactionTotal-is-length done = refl
interactionTotal-is-length (step e rest) =
  cong suc (interactionTotal-is-length rest)

-- The two receivers compose componentwise. This is the ledger law used when
-- concatenating an upstream boundary reduction with a continuation reduction.
append : {m n : ℕ} → Trace m → Trace n → Trace (m + n)
append done ys = ys
append (step e xs) ys = step e (append xs ys)

ledger-append : {m n : ℕ} (xs : Trace m) (ys : Trace n)
  → ledger (append xs ys) ≡ ledger xs ⊞ ledger ys
ledger-append done ys = sym (cong (λ z → zeroCharge ⊞ z) (ledger-zero-left ys))
  where
  ledger-zero-left : {k : ℕ} (t : Trace k) → zeroCharge ⊞ ledger t ≡ ledger t
  ledger-zero-left done = refl
  ledger-zero-left (step e rest) =
    cong (λ z → localCharge e ⊞ z) (ledger-zero-left rest)
ledger-append (step e xs) ys =
  cong (λ z → localCharge e ⊞ z) (ledger-append xs ys)
  ∙ sym (charge-assoc (localCharge e) (ledger xs) (ledger ys))

-- Prefix lower bounds are receiver-specific. A semantic theorem can use
-- this exact additive ledger after supplying a correspondence from its
-- transitions to Event; the present theorem does not invent that mapping.
heap-monotone-prefix : {m n : ℕ} (xs : Trace m) (ys : Trace n)
  → heapWords (ledger xs) ≤ heapWords (ledger (append xs ys))
heap-monotone-prefix xs ys =
  subst (λ z → heapWords (ledger xs) ≤ heapWords z)
    (sym (ledger-append xs ys))
    (heap-prefix xs ys)
  where
  heap-prefix : {m n : ℕ} (xs : Trace m) (ys : Trace n)
    → heapWords (ledger xs) ≤ heapWords (ledger xs ⊞ ledger ys)
  heap-prefix xs ys =
    ≤SumLeft {n = heapWords (ledger xs)} {k = heapWords (ledger ys)}

-- A concrete mixed trace: unequal-label sharing, short-circuit erasure, and
-- application distribution. Its two receivers are computed by reduction.
exampleTrace : Trace 3
exampleTrace = step dupSupDifferent (step andZero (step appSup done))

example-interactions : interactionTotal exampleTrace ≡ 3
example-interactions = refl

example-heap : heapTotal exampleTrace ≡ 7
example-heap = refl

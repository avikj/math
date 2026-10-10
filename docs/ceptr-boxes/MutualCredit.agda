{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module MutualCredit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; invEq ; retEq)
open import Cubical.Data.Int using (ℤ ; pos ; _+_ ; _-_ ; +Comm ; +Assoc ; minusPlus ; plusMinus ; isEquivAddℤ ; pos0+)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List using (List ; [] ; _∷_)

-- two accounts: the only two states a transaction changes.
Accounts : Type
Accounts = ℤ × ℤ

-- a mutual-credit transaction: the spender goes down, the receiver up,
-- by the same amount.  Credits are issued in the act; nothing is minted.
transfer : ℤ → Accounts → Accounts
transfer t (a , b) = (a - t , b + t)

-- the currency supply is always zero: the sum is conserved by every
-- transaction, for every amount and every starting state.
supply : Accounts → ℤ
supply (a , b) = a + b

zeroSum : (t : ℤ) (x : Accounts) → supply (transfer t x) ≡ supply x
zeroSum t (a , b) =
    sym (+Assoc a (- t) (b + t))
  ∙ cong (a +_) (+Assoc (- t) b t ∙ cong (_+ t) (+Comm (- t) b) ∙ minusPlus t b)
  where open import Cubical.Data.Int using (-_)

-- a transaction is reversible: it is transport along an identification
-- of the account space with itself, so it destroys nothing.
undo : ℤ → Accounts → Accounts
undo t (a , b) = (a + t , b - t)

undo-transfer : (t : ℤ) (x : Accounts) → undo t (transfer t x) ≡ x
undo-transfer t (a , b) i = minusPlus t a i , plusMinus t b i

transfer-undo : (t : ℤ) (x : Accounts) → transfer t (undo t x) ≡ x
transfer-undo t (a , b) i = plusMinus t a i , minusPlus t b i

transferEquiv : ℤ → Accounts ≃ Accounts
transferEquiv t = isoToEquiv (iso (transfer t) (undo t) (transfer-undo t) (undo-transfer t))

-- each party's balance is the replay of its own chain of signed amounts
-- (spent negative, received positive): no global ledger is consulted.
balance : List ℤ → ℤ
balance []       = pos 0
balance (t ∷ ts) = balance ts + t

-- the countersigned record: one entry, two chains.  Both chains move
-- or neither does — a transaction that leaves the spender unchanged
-- was for nothing.
bothMove : (t : ℤ) (x : Accounts) → fst (transfer t x) ≡ fst x → t ≡ pos 0
bothMove t (a , b) p =
    sym (retEq e t)
  ∙ cong (invEq e) (sym (s ∙ +Comm a t) ∙ pos0+ a)
  ∙ retEq e (pos 0)
  where
  e : ℤ ≃ ℤ
  e = (λ n → n + a) , isEquivAddℤ a
  s : a ≡ a + t
  s = sym (minusPlus t a) ∙ cong (_+ t) p

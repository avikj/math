{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- EveryDerivationIsInvertible
--
-- Ledger entries A and C, made a term. Because `reverse` is a `Step`
-- constructor, every `Derivation a b` runs backwards: `revD` builds the
-- reversed derivation `Derivation b a` by reversing each step and
-- reassembling in the opposite order.  The reversal is GRADE-PRESERVING:
-- reversing a route costs exactly what the route cost (`len-revD`).  It is
-- an inverse only up to MEANING (`revD-sound`): as data, `d ++ revD d` has
-- length 2·len d and is not `done`, and `revD (revD d)` is not `d`
-- (`reverse (reverse s)` is a different constructor application).  So the
-- calculus is a category with formal reverses, a groupoid only after its
-- meaning is taken; see Kernel/Syat_… and Kernel/VyayaResidue_….
------------------------------------------------------------------------

module EveryDerivationIsInvertible where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc ; +-zero ; isSetℕ)

open import Kernel.RewriteCertificate

len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

-- concatenation of derivations, strictly associative/unital as data
_++_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done _        ++ e = e
then-step s d ++ e = then-step s (d ++ e)

len-++ : {a b c : Tm} (d : Derivation a b) (e : Derivation b c)
       → len (d ++ e) ≡ len d + len e
len-++ (done _)        e = refl
len-++ (then-step _ d) e = cong suc (len-++ d e)

-- THE REVERSED DERIVATION : every derivation runs backwards.
revD : {a b : Tm} → Derivation a b → Derivation b a
revD (done x)        = done x
revD (then-step s d) = revD d ++ then-step (reverse s) (done _)

-- GRADE-PRESERVING : the inverse has exactly the same length. Reversing a
-- route costs what the route cost — no information created or destroyed.
len-revD : {a b : Tm} (d : Derivation a b) → len (revD d) ≡ len d
len-revD (done _) = refl
len-revD (then-step s d) =
    len-++ (revD d) (then-step (reverse s) (done _))
  ∙ cong (_+ suc zero) (len-revD d)
  ∙ +-suc (len d) zero
  ∙ cong suc (+-zero (len d))

-- SEMANTICALLY (ONLY) THE INVERSE : the reversed derivation's meaning is the
-- inverse path. Robust because meaning lands in ℕ (a set): the two paths
-- eval b ρ ≡ eval a ρ are forced equal.
revD-sound : {a b : Tm} (d : Derivation a b) (ρ : Env)
           → derivation-sound (revD d) ρ ≡ sym (derivation-sound d ρ)
revD-sound {a} {b} d ρ =
  isSetℕ (eval b ρ) (eval a ρ)
    (derivation-sound (revD d) ρ) (sym (derivation-sound d ρ))

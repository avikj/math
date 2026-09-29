{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Syat_TheBlindnessIsAPropertyOfTheCodomain
--              AndCostFailsInversionRatherThanTruncation
--
-- TERM, AND THE SCHOOL IS JAINA, NAMED BEFORE THE TERM IS USED.
--
-- स्यात् · syāt -- the qualifier that prefixes every bhaṅga of the
-- saptabhaṅgī.  Optative of √अस्, used as an indeclinable, and it does NOT
-- mean "maybe": the Jaina logicians insist each qualified predication is
-- निश्चय · niścaya, determinate, asserted under a stated उपाधि · upādhi.
-- The apparatus is laid out in Samantabhadra's *ptamms* (~6th c.) and
-- developed by Akalaka (~8th c.) and Vidynanda; the governing rule taken
-- here is the older one, that a naya asserting itself by denying the
-- others becomes a  · durnaya.  No first use is established.
--
------------------------------------------------------------------------
-- THE BLINDNESS IS A PROPERTY OF THE CODOMAIN.
--
-- `Sesa_⟦` proves `every-semantic-criterion-is-blind`:
--
--     syt: FROM A 0-TRUNCATED STANDPOINT, no criterion selects.
--
-- The h-level
-- of the CRITERION is unrestricted in `Sesa_`'s statement, but the h-level
-- of the CODOMAIN is what does the work, and it is fixed at 0 by ℕ.
-- The general form is supplied beside it.
--
------------------------------------------------------------------------
-- AND THE OBVIOUS REPAIR DOES NOT WORK, WHICH IS THE SHARPER HALF.
--
-- If truncation is the obstruction, raise it: interpret into a groupoid
-- and let parallel derivations have distinct meanings.  §2 says that fails
-- for a second and independent reason.  Any measure that respects the
-- groupoid structure must send `rev d` to the inverse of `d`, hence a
-- round trip to the identity.  Lghava sends a round trip to TWICE the
-- cost.  So cost is a functor on the CATEGORY and not on the GROUPOID:
-- the obstruction to seeing it is INVERSION, not truncation, and raising
-- h-level does not reach it.
--
-- `Avirodha_…` states the structure -- strictly a category, weakly a
-- groupoid, and the gap between them is the ea.  §2 measures that gap:
-- it is exactly `len d + len d`.
--
------------------------------------------------------------------------
-- THE SEPARATION IS BY INVERSION, NOT h-LEVEL.
--
-- No model landing in a genuine groupoid separates the kernel's two
-- histories -- none exists, at any h-level.
--
-- §3 proves it.  `detour-history` is `s ; reverse s ; direct-history`, and
-- EVERY semantics sends `reverse` to `sym`, so that round trip is the
-- identity in any groupoid whatsoever.  The proof uses `assoc`, `rCancel`
-- and `lUnit` and mentions no h-level anywhere.
--
-- Truncation is what identifies parallel
-- derivations in general; it is NOT what identifies THOSE TWO.  Those two
-- are identified by inversion, which §2 already names as the deeper
-- obstruction -- and `Sesa_`'s exhibited proof-relevance, `len` 2 against
-- 4, is therefore visible to no functorial semantics at any level.  The
-- pair was chosen to differ by a round trip, which is exactly the
-- difference no semantics can see.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--   §1  blindness-is-a-property-of-the-codomain -- the parametric form.
--   §2  ⊕-len, rev-len, round-trip -- reversal is free to the law and
--       costs double to the walker.
--   §3  no-semantics-separates-them -- and therefore raising h-level buys
--       nothing on the corpus's own pair.
------------------------------------------------------------------------

module Kernel.Syat_TheBlindnessIsAPropertyOfTheCodomainAndCostFailsInversionRatherThanTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc ; +-zero)

open import Cubical.Foundations.GroupoidLaws using (assoc ; rCancel ; lUnit)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel using (direct-history ; detour-history)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- §1.  WHAT THE BLINDNESS PROOF ACTUALLY EATS.
--
-- The codomain, the interpretation and its soundness are all parameters.
-- Nothing about ℕ survives, nothing about `eval`, nothing about the six
-- constructors.  One hypothesis is consumed and it is `isSet X`.
------------------------------------------------------------------------

blindness-is-a-property-of-the-codomain :
  {X : Type ℓ} → isSet X
  → (⟦_⟧ : Tm → Env → X)
  → (sound : {a b : Tm} → Derivation a b → (ρ : Env) → ⟦ a ⟧ ρ ≡ ⟦ b ⟧ ρ)
  → {a b : Tm} {C : Type ℓ'}
  → (φ : ((ρ : Env) → ⟦ a ⟧ ρ ≡ ⟦ b ⟧ ρ) → C)
  → (d e : Derivation a b) → φ (sound d) ≡ φ (sound e)
blindness-is-a-property-of-the-codomain setX ⟦_⟧ sound φ d e =
  cong φ (funExt (λ ρ → setX _ _ (sound d ρ) (sound e ρ)))

------------------------------------------------------------------------
-- §2.  AND RAISING THE H-LEVEL DOES NOT REACH IT.  A round trip is the
--      identity to anything that respects inversion, and twice the cost
--      to lghava.
------------------------------------------------------------------------

len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = zero
len (then-step _ d) = suc (len d)

_⊕_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done _        ⊕ e = e
then-step p d ⊕ e = then-step p (d ⊕ e)

rev : {a b : Tm} → Derivation a b → Derivation b a
rev (done x)        = done x
rev (then-step p d) = rev d ⊕ then-step (reverse p) (done _)

⊕-len : {a b c : Tm} (d : Derivation a b) (e : Derivation b c)
      → len (d ⊕ e) ≡ len d + len e
⊕-len (done _)        e = refl
⊕-len (then-step _ d) e = cong suc (⊕-len d e)

-- reversal is free to the law: the same number of steps, both ways.
rev-len : {a b : Tm} (d : Derivation a b) → len (rev d) ≡ len d
rev-len (done x)        = refl
rev-len (then-step p d) =
    ⊕-len (rev d) (then-step (reverse p) (done _))
  ∙ +-suc (len (rev d)) zero
  ∙ cong suc (+-zero (len (rev d)))
  ∙ cong suc (rev-len d)

-- and costs double to the walker.  Any groupoid-functorial measure sends
-- this to the identity; lghava sends it to `len d + len d`.
round-trip : {a b : Tm} (d : Derivation a b) → len (d ⊕ rev d) ≡ len d + len d
round-trip d = ⊕-len d (rev d) ∙ cong (len d +_) (rev-len d)

------------------------------------------------------------------------
-- §3.  AND ON THE CORPUS'S OWN PAIR, H-LEVEL BUYS NOTHING.
--
-- Take ANY type at ANY h-level, any interpretation of terms in it, and any
-- assignment of paths to steps that sends `reverse` to `sym` -- which every
-- semantics must, since that is what makes it a semantics.  Then
-- `detour-history` and `direct-history` get the SAME path.  They differ by
-- `s ; reverse s`, and a round trip is the identity in any groupoid.
--
-- No `isSet` appears below.
------------------------------------------------------------------------

module _ {X : Type ℓ} (P : Tm → X)
         (st : {a b : Tm} → Step a b → P a ≡ P b)
         (st-rev : {a b : Tm} (p : Step a b) → st (reverse p) ≡ sym (st p))
         where

  D : {a b : Tm} → Derivation a b → P a ≡ P b
  D (done _)        = refl
  D (then-step p d) = st p ∙ D d

  no-semantics-separates-them : D detour-history ≡ D direct-history
  no-semantics-separates-them =
      cong (λ q → st s ∙ (q ∙ D direct-history)) (st-rev s)
    ∙ assoc (st s) (sym (st s)) (D direct-history)
    ∙ cong (_∙ D direct-history) (rCancel (st s))
    ∙ sym (lUnit (D direct-history))
    where s = add-suc var zero

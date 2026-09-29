{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Ubhayataḥ — from both sides.
--
-- TERM.  उभयतः, on both sides / in both directions.  An ordinary adverb,
-- chosen here; no source is claimed and nothing below is anyone's theorem.
--
-- THE OMISSION.  `Kernel.RewriteCertificate.Step` lifts a successor out of the
-- RIGHT operand:
--
--     add-suc : Step (add x (suc y)) (suc (add x y))
--
-- and has no rule doing the same on the left.  `Baddha_…` proved what that
-- costs: a successor in a left operand whose sibling carries a variable can
-- never reach the front, and the count of such successors is conserved by
-- every rule.  `Visranti_…` then showed the same fact operationally — `nf`
-- inspects its RIGHT argument and never its left, so a left-trapped
-- successor is never examined.
--
-- THE FIRST THING TO NOTICE IS ABOUT THE KERNEL'S OWN DESIGN, and it is
-- visible only once both rules are written down.  The omitted rule is FREE:
--
--     add-suc-left-sound : eval (add (suc x) y) ρ ≡ eval (suc (add x y)) ρ
--     add-suc-left-sound = refl
--
-- because ℕ's addition recurses on its LEFT argument, so `suc a + b`
-- reduces to `suc (a + b)` definitionally.  The rule the kernel DID include
-- is the expensive one: `add-suc`'s soundness is discharged by `+-suc`, a
-- library lemma, and appears in `step-sound` as the only clause that needs
-- one.  So the calculus omitted the free rule and kept the costly one, and
-- the omission is what makes it sequential.  The price was paid on the
-- wrong side.
--
-- WHAT IS PROVED HERE.
--
--   §2  the omitted rule is sound, by `refl`;
--   §3  in the extended calculus the pair `Baddha_…` separated is joined,
--       in ONE step: `add (suc var) yvar → suc (add var yvar)`;
--   §4  so `Baddha_…`'s trapped count is NOT conserved by the extension —
--       exhibited, 1 against 0 — which is the precise sense in which the
--       extension buys something.  What it buys is exactly what that count
--       measured, and nothing else was measuring it.
--
-- THE READING THIS EXISTS FOR.  A rule set that inspects one operand and
-- never the other is a SEQUENTIAL one, in the sense the semantics-of-
-- programs literature made exact: Kahn–Plotkin's sequentiality index and
-- Berry–Curien's sequential algorithms turn on which argument a computation
-- must demand first, and Colson's theorems on primitive recursive
-- algorithms turn on their being unable to release the argument they
-- fixated on.  `Step` is right-obstinate in that sense, and `Baddha_…`'s
-- number is the cost of the obstinacy, counted.  Adding the left rule makes
-- the operator examinable from either side — the miniature of what
-- Brookes–Geva's parallel `query` does to `valof` — and the gain over the
-- sequential rule set is measured by a quantity that was already a theorem
-- before anyone asked the question.
--
-- Named as the frame this speaks to: the distinction they drew is the one
-- the omitted rule turns on.
------------------------------------------------------------------------

module NaturalMachine.Ubhayatah_TheOmittedLeftRuleIsFreeAndItsAbsenceIsExactlyTheTrappedCount where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ) renaming (zero to nzero ; suc to nsuc)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
open import NaturalMachine.Baddha_TheTrappedSuccessorIsAThirdConservationLawAndItRefutesTheCompleteInvariantConjecture
  using (trapped)

------------------------------------------------------------------------
-- §1.  THE CALCULUS WITH BOTH SIDES.
------------------------------------------------------------------------

data Step² : Tm → Tm → Type₀ where
  base         : {x y : Tm} → Step x y → Step² x y
  add-suc-left : (x y : Tm) → Step² (add (suc x) y) (suc (add x y))

data Derivation² : Tm → Tm → Type₀ where
  done²      : (x : Tm) → Derivation² x x
  then-step² : {x y z : Tm} → Step² x y → Derivation² y z → Derivation² x z

------------------------------------------------------------------------
-- §2.  THE OMITTED RULE IS SOUND, AND IT IS FREE.
--
-- `refl`.  ℕ's addition recurses on the left, so `suc a + b` IS
-- `suc (a + b)`.  Compare `Kernel.RewriteCertificate.step-sound`, where the
-- `add-suc` clause is the one that must call `+-suc`.
------------------------------------------------------------------------

add-suc-left-sound : (x y : Tm) (ρ : Env)
                   → eval (add (suc x) y) ρ ≡ eval (suc (add x y)) ρ
add-suc-left-sound x y ρ = refl

step²-sound : {a b : Tm} → Step² a b → (ρ : Env) → eval a ρ ≡ eval b ρ
step²-sound (base p)           ρ = step-sound p ρ
step²-sound (add-suc-left x y) ρ = add-suc-left-sound x y ρ

derivation²-sound : {a b : Tm} → Derivation² a b → (ρ : Env) → eval a ρ ≡ eval b ρ
derivation²-sound (done² t)        ρ = refl
derivation²-sound (then-step² p d) ρ = step²-sound p ρ ∙ derivation²-sound d ρ

------------------------------------------------------------------------
-- §3.  THE SEPARATED PAIR IS JOINED, IN ONE STEP.
------------------------------------------------------------------------

private
  A B : Tm
  A = add (suc var) yvar
  B = suc (add var yvar)

the-untrapping : Derivation² A B
the-untrapping = then-step² (add-suc-left var yvar) (done² B)

------------------------------------------------------------------------
-- §4.  SO THE TRAPPED COUNT IS NOT CONSERVED, AND THAT IS THE GAIN.
--
-- `Baddha_…` proves `trapped` invariant under every `Step`.  Here is a
-- `Step²` that moves it, so no analogous theorem holds for the extension —
-- and the quantity that fails to be conserved is precisely the one that
-- measured what the sequential rule set could not reach.
------------------------------------------------------------------------

trapped-A : trapped A ≡ nsuc nzero
trapped-A = refl

trapped-B : trapped B ≡ nzero
trapped-B = refl

no-step²-conservation :
  ((a b : Tm) → Step² a b → trapped a ≡ trapped b) → ⊥
no-step²-conservation conserved =
  snotz (sym trapped-A ∙ conserved A B (add-suc-left var yvar))

-- Stated the other way, as the thing gained: in the sequential calculus
-- this pair is unjoinable (`Baddha_….not-derivable`); with the free rule it
-- is one step apart.
what-the-omission-cost : Derivation² A B
what-the-omission-cost = the-untrapping

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Naya_EvalIsOneStandpointAndASecondOneProvesTheInduction
--              RuleIsStrictlyStrongerThanTheRewriteClosure
--
-- TERM, AND THE SCHOOL IS JAINA, NAMED BEFORE THE TERM IS USED.
--
-- नय · naya -- a standpoint: a determination of an object from one aspect,
-- valid within its scope and never exhausting the object.  Umsvti's
-- *Tattvrthastra* gives the list, and I give the words rather than the
-- number because the recensions disagree on the numbering (vetmbara 1.34
-- against Digambara 1.33) and because a stra's number propagates through
-- citation while its words appear only where someone opened the text:
--
--     नैगमसंग्रहव्यवहारर्जुसूत्रशब्दसमभिरूढैवंभूता नयाः
--     naigama-sagraha-vyavahra-justra-abda-samabhirha-evabht nay
--
-- Siddhasena Divkara, *Sanmatitarka*, reduces them to two roots,
-- dravyrthika and paryyrthika; Mallavdin's *Dvdaranayacakra*
-- (~6th c.) runs twelve of them against each other.  The governing rule is
-- that a naya asserting itself by DENYING the others becomes a दुर्नय ·
-- durnaya.
--
-- `eval` INTO ℕ IS ONE STANDPOINT AMONG MANY, not THE semantics.
-- `Ankapasa_…` builds
--
--     ⟦_⟧ : Tm → TEnv → Type₀     zero ↦ ⊥, suc ↦ Unit ⊎ −, add ↦ ⊎
--
-- a UNIVERSE-valued semantics of this same calculus, in which every `Step`
-- constructor becomes an equivalence and `reverse` becomes `invEquiv`; it
-- proves `counting-semantics-cannot-see-it` against
-- `univalent-semantics-does-see-it`, and names the diagnosis नय-निरोधः.
-- It reaches the fact from the akapa side.
--
-- THE MATHEMATICAL CONTENT, bracketed by the two standpoints:
--   * `Ankapasa_`'s model VALIDATES commutativity -- `add ↦ ⊎` and
--     `⊎-swap-≃` -- and separates it from the identity.  §3 below REFUTES
--     it: no derivation exists at all.  Non-triviality and underivability
--     are different theorems and neither implies the other.
--   * Nothing in `Ankapasa_` bears on left-unitality or on induction, and
--     §4 is untouched by it.
--   * TOGETHER the two bracket the fact, which neither does alone:
--     commutativity of `add` IS NOT DERIVABLE, and once added IT IS NOT
--     TRIVIAL.  That is two nayas on one object, arrived at separately,
--     neither reducible to the other -- which is the doctrine, not a
--     consolation.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--
--   §1  A second model: the free-monoid-like structure W with `p`, which
--       is right-unital and successor-compatible -- so BOTH axioms hold,
--       by `refl` -- and is neither commutative nor left-unital.
--   §2  Soundness at that standpoint, all six `Step` constructors.
--   §3  not-commutative, not-left-unital.  Two underivabilities, neither
--       reachable from ℕ, both of statements TRUE in ℕ.
--   §4  THE GAP, AS A THEOREM.  `leftZero-cert` is an induction
--       certificate for `0 + x = x`; `induction-sound` discharges it at
--       every environment; and §3 says no derivation exists.  Therefore
--       THE INDUCTION RULE IS STRICTLY STRONGER THAN THE REWRITE CLOSURE,
--       and the kernel can certify theorems it cannot install, since
--       `NativeOperation.checked` demands a `Derivation`.
------------------------------------------------------------------------

module Kernel.Naya_EvalIsOneStandpointAndASecondOneProvesTheInductionRuleIsStrictlyStrongerThanTheRewriteClosure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Sigma using (_×_ ; _,_)
import Cubical.Data.Empty as E

open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  THE SECOND STANDPOINT.
--
-- The two axioms constrain `add` only where the right argument is `zero`
-- or a `suc`.  At an opaque right argument they say nothing at all, and ℕ
-- silently fills that freedom with commutativity.  Here it is filled
-- differently: a marker is dropped between the two sides.
------------------------------------------------------------------------

data Atom : Type₀ where
  aX aY aZ aU aV aW aS aM : Atom

W : Type₀
W = List Atom

-- right-unital and successor-compatible by construction; the third clause
-- overlaps the second and fires only at a head that is not `aS`.
p : W → W → W
p a []       = a
p a (aS ∷ b) = aS ∷ p a b
p a (c ∷ b)  = a ++ (aM ∷ c ∷ b)

⟦_⟧ : Tm → W
⟦ var ⟧     = aX ∷ []
⟦ yvar ⟧    = aY ∷ []
⟦ zvar ⟧    = aZ ∷ []
⟦ uvar ⟧    = aU ∷ []
⟦ vvar ⟧    = aV ∷ []
⟦ wvar ⟧    = aW ∷ []
⟦ zero ⟧    = []
⟦ suc t ⟧   = aS ∷ ⟦ t ⟧
⟦ add l r ⟧ = p ⟦ l ⟧ ⟦ r ⟧

------------------------------------------------------------------------
-- §2.  SOUNDNESS AT THIS STANDPOINT.  Both axioms hold by `refl`, which is
--      the check that this is a model of the same theory and not a
--      different one dressed up.
------------------------------------------------------------------------

step-model : {a b : Tm} → Step a b → ⟦ a ⟧ ≡ ⟦ b ⟧
step-model (add-zero x)    = refl
step-model (add-suc x y)   = refl
step-model (suc-step q)    = cong (aS ∷_) (step-model q)
step-model (add-left q z)  = cong (λ w → p w ⟦ z ⟧) (step-model q)
step-model (add-right z q) = cong (p ⟦ z ⟧) (step-model q)
step-model (reverse q)     = sym (step-model q)

derivation-model : {a b : Tm} → Derivation a b → ⟦ a ⟧ ≡ ⟦ b ⟧
derivation-model (done _)        = refl
derivation-model (then-step q d) = step-model q ∙ derivation-model d

------------------------------------------------------------------------
-- §3.  TWO UNDERIVABILITIES ℕ CANNOT REACH.  Both statements are TRUE at
--      every environment, so `Vyabhicara_…`'s instrument has no grip on
--      either; this standpoint decides both.
------------------------------------------------------------------------

hd : W → Atom
hd []      = aM
hd (a ∷ _) = a

isX : Atom → Bool
isX aX = true
isX _  = false

not-commutative : Derivation (add var yvar) (add yvar var) → E.⊥
not-commutative d = true≢false (cong isX (cong hd (derivation-model d)))

not-left-unital : Derivation (add zero var) var → E.⊥
not-left-unital d = true≢false (sym (cong isX (cong hd (derivation-model d))))

------------------------------------------------------------------------
-- §4.  THE GAP, AS A THEOREM.
--
-- `0 + x = x` is certifiable by the kernel's own induction apparatus and
-- true at every environment -- and underivable.  So `induction-sound` is
-- not redundant machinery: it proves what the rewrite closure cannot.  And
-- because `NativeOperation.checked` demands a `Derivation`, this theorem
-- CANNOT ENTER THE LIBRARY.  The kernel certifies more than it can learn.
------------------------------------------------------------------------

leftZero-cert : InductionCertificate (add zero var) var
InductionCertificate.base leftZero-cert = then-step (add-zero zero) (done zero)
InductionCertificate.step leftZero-cert =
  hyp-then (lift-step (add-suc zero var))
    (hyp-then (hyp-suc hypothesis) (hyp-done (suc var)))

leftZero-holds-everywhere : (ρ : Env) → eval (add zero var) ρ ≡ eval var ρ
leftZero-holds-everywhere = induction-sound leftZero-cert

-- the two halves side by side, so the statement is one object.
induction-is-strictly-stronger :
  ((ρ : Env) → eval (add zero var) ρ ≡ eval var ρ)
  × (Derivation (add zero var) var → E.⊥)
induction-is-strictly-stronger = leftZero-holds-everywhere , not-left-unital

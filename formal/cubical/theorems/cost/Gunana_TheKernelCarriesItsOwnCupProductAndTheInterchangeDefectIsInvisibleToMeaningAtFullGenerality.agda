{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- गुणन — the product.  The kernel carries its own cup product, and the
-- interchange defect is the located exchange content.
--
-- WHAT THIS IS.  The congruence rules add-left and add-right are not
-- bookkeeping: they are the two whiskerings of a HORIZONTAL COMPOSITION,
-- and this file assembles it — for derivations d : x ⇝ y and
-- e : u ⇝ v, a derivation d ⊗ e : add x u ⇝ add y v — proving:
--
--   §2  Units are definitional on the left and one lemma on the right:
--       done ⊗ e is a whiskering by reduction, d ⊗ done by ⊕-unitr.
--   §3  The grade is multiplicatively additive:
--       dairghya (d ⊗ e) ≡ dairghya d + dairghya e — the product prices
--       as the sum of its factors, exactly as a cup product grades.
--   §4  THE INTERCHANGE DEFECT.  The product can be scheduled left-first
--       or right-first.  The two schedules are DISTINCT AS DATA — a
--       one-step witness pair is separated by reading the head
--       constructor — and INDISTINGUISHABLE IN MEANING AT FULL
--       GENERALITY: for every d, e and every environment, the two
--       interpretations are equal by one appeal to the set-ness of the
--       domain, no case analysis.  This is the Eckmann–Hilton defect of
--       the kernel, exhibited and priced: the exchange content of the
--       calculus is exactly the difference between the two schedules,
--       it is real at the chain level, and it is the first thing the
--       meaning quotients.
--
-- Read against the corpus: abstract 13's order-two loop is this defect
-- seen in the universe; README §23's commuting square is this defect
-- seen as concurrency; and the kernel verdict
-- — the product exists unlinearized ∥ linearization kills the grade,
-- syād-asti-nāsti in succession — is its exact position: the cup
-- product lives at the graded level, and the bilinear completion that
-- geometry enjoys is priced by Laghava as the grade's death.
--
------------------------------------------------------------------------

module Gunana_TheKernelCarriesItsOwnCupProductAndTheInterchangeDefectIsInvisibleToMeaningAtFullGenerality where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Nat using (isSetℕ)
import Cubical.Data.Nat as N
open import Cubical.Data.Empty using (⊥)

open import Kernel.RewriteCertificate
open import Viparyasa_TheTransposeIsAContravariantGradePreservingDaggerAndTheGradeForbidsItFromEverBeingAnInverse
  using (_⊕_ ; ⊕-unitr ; dairghya ; dairghya-⊕)

private
  variable
    x y u v z : Tm

------------------------------------------------------------------------
-- १ · The two whiskerings, lifted from steps to derivations.
------------------------------------------------------------------------

vāmāṅga : Derivation x y → (z : Tm) → Derivation (add x z) (add y z)
vāmāṅga (done x)        z = done (add x z)
vāmāṅga (then-step s d) z = then-step (add-left s z) (vāmāṅga d z)

dakṣiṇāṅga : (z : Tm) → Derivation x y → Derivation (add z x) (add z y)
dakṣiṇāṅga z (done x)        = done (add z x)
dakṣiṇāṅga z (then-step s d) = then-step (add-right z s) (dakṣiṇāṅga z d)

------------------------------------------------------------------------
-- २ · The product, left-first, and its right-first sibling.
------------------------------------------------------------------------

_⊗_ : Derivation x y → Derivation u v → Derivation (add x u) (add y v)
_⊗_ {x} {y} {u} {v} d e = vāmāṅga d u ⊕ dakṣiṇāṅga y e

_⊗'_ : Derivation x y → Derivation u v → Derivation (add x u) (add y v)
_⊗'_ {x} {y} {u} {v} d e = dakṣiṇāṅga x e ⊕ vāmāṅga d v

-- Units.  The left unit is definitional; the right unit is ⊕-unitr.
uniqueness-vāma : (e : Derivation u v) → (done x ⊗ e) ≡ dakṣiṇāṅga x e
uniqueness-vāma e = refl

uniqueness-dakṣiṇa : (d : Derivation x y) → (d ⊗ done u) ≡ vāmāṅga d u
uniqueness-dakṣiṇa {u = u} d = ⊕-unitr (vāmāṅga d u)

------------------------------------------------------------------------
-- ३ · The product grades additively.
------------------------------------------------------------------------

mātrā-vāma : (d : Derivation x y) (z : Tm)
           → dairghya (vāmāṅga d z) ≡ dairghya d
mātrā-vāma (done _)        z = refl
mātrā-vāma (then-step s d) z = cong N.suc (mātrā-vāma d z)

mātrā-dakṣiṇa : (z : Tm) (e : Derivation u v)
              → dairghya (dakṣiṇāṅga z e) ≡ dairghya e
mātrā-dakṣiṇa z (done _)        = refl
mātrā-dakṣiṇa z (then-step s e) = cong N.suc (mātrā-dakṣiṇa z e)

guṇana-mātrā : (d : Derivation x y) (e : Derivation u v)
             → dairghya (d ⊗ e) ≡ dairghya d N.+ dairghya e
guṇana-mātrā {x} {y} {u} {v} d e =
  dairghya-⊕ (vāmāṅga d u) (dakṣiṇāṅga y e)
  ∙ cong₂ N._+_ (mātrā-vāma d u) (mātrā-dakṣiṇa y e)

------------------------------------------------------------------------
-- ४ · The interchange defect: distinct as data, invisible to meaning.
------------------------------------------------------------------------

-- The one-step witness pair, on two independent registers.
d₁ : Derivation (add var zero) var
d₁ = then-step (add-zero var) (done var)

e₁ : Derivation (add yvar zero) yvar
e₁ = then-step (add-zero yvar) (done yvar)

-- A discriminator reading the head constructor of the first step.
vāmaśiras : Step x y → Bool
vāmaśiras (add-left _ _) = true
vāmaśiras _              = false

śiraḥ : Derivation x y → Bool
śiraḥ (done _)        = false
śiraḥ (then-step s _) = vāmaśiras s

-- The two schedules of one product are distinct derivations.
vinimaya-bheda : (d₁ ⊗ e₁) ≡ (d₁ ⊗' e₁) → ⊥
vinimaya-bheda p = true≢false (cong śiraḥ p)

-- And the meaning cannot see the difference — for EVERY pair of
-- derivations and every environment, with no case analysis: both
-- schedules interpret into an identity type over a set, and one appeal
-- to its set-ness closes the square.  The exchange content of the
-- kernel is exactly what this one stroke quotients.
vinimaya-artha : (d : Derivation x y) (e : Derivation u v) (ρ : Env)
               → derivation-sound (d ⊗ e) ρ ≡ derivation-sound (d ⊗' e) ρ
vinimaya-artha d e ρ =
  isSetℕ _ _ (derivation-sound (d ⊗ e) ρ) (derivation-sound (d ⊗' e) ρ)

------------------------------------------------------------------------
-- ५ · The residue is a permutation.  The two schedules do not merely
-- have equal meaning: they have equal length, an equal count of
-- left-whiskered steps, and an equal count of right-whiskered steps —
-- the same multiset of step kinds, differing in ORDER alone.  What the
-- interchange defect withholds from the meaning is exactly a
-- transposition of independent steps, which is the corpus's dropped
-- bit (abstract 13) appearing as the content of scheduling.
------------------------------------------------------------------------

vāmagaṇanā : Derivation x y → N.ℕ
vāmagaṇanā (done _)                     = N.zero
vāmagaṇanā (then-step (add-left _ _) d) = N.suc (vāmagaṇanā d)
vāmagaṇanā (then-step _ d)              = vāmagaṇanā d

gaṇanā-⊕ : (d : Derivation x y) (e : Derivation y z)
         → vāmagaṇanā (d ⊕ e) ≡ vāmagaṇanā d N.+ vāmagaṇanā e
gaṇanā-⊕ (done _) e = refl
gaṇanā-⊕ (then-step (add-left s w) d) e = cong N.suc (gaṇanā-⊕ d e)
gaṇanā-⊕ (then-step (add-zero _) d)   e = gaṇanā-⊕ d e
gaṇanā-⊕ (then-step (add-suc _ _) d)  e = gaṇanā-⊕ d e
gaṇanā-⊕ (then-step (suc-step _) d)   e = gaṇanā-⊕ d e
gaṇanā-⊕ (then-step (add-right _ _) d) e = gaṇanā-⊕ d e
gaṇanā-⊕ (then-step (reverse _) d)    e = gaṇanā-⊕ d e

-- Every step of a left whiskering is left-headed; of a right
-- whiskering, none is.
gaṇanā-vāmāṅga : (d : Derivation x y) (z : Tm)
               → vāmagaṇanā (vāmāṅga d z) ≡ dairghya d
gaṇanā-vāmāṅga (done _)        z = refl
gaṇanā-vāmāṅga (then-step s d) z = cong N.suc (gaṇanā-vāmāṅga d z)

gaṇanā-dakṣiṇāṅga : (z : Tm) (e : Derivation u v)
                  → vāmagaṇanā (dakṣiṇāṅga z e) ≡ N.zero
gaṇanā-dakṣiṇāṅga z (done _)        = refl
gaṇanā-dakṣiṇāṅga z (then-step s e) = gaṇanā-dakṣiṇāṅga z e

-- Both schedules carry exactly |d| left-whiskered steps…
order-eva-bhedaḥ : (d : Derivation x y) (e : Derivation u v)
                 → vāmagaṇanā (d ⊗ e) ≡ vāmagaṇanā (d ⊗' e)
order-eva-bhedaḥ {x} {y} {u} {v} d e =
  gaṇanā-⊕ (vāmāṅga d u) (dakṣiṇāṅga y e)
  ∙ cong₂ N._+_ (gaṇanā-vāmāṅga d u) (gaṇanā-dakṣiṇāṅga y e)
  ∙ N.+-zero (dairghya d)
  ∙ sym (gaṇanā-vāmāṅga d v)
  ∙ sym (cong₂ N._+_ (gaṇanā-dakṣiṇāṅga x e) refl)
  ∙ sym (gaṇanā-⊕ (dakṣiṇāṅga x e) (vāmāṅga d v))

-- …and equal length: the right-first schedule is graded additively too,
-- so the multiset of step kinds is invariant and only the order moves.
guṇana-mātrā' : (d : Derivation x y) (e : Derivation u v)
              → dairghya (d ⊗' e) ≡ dairghya d N.+ dairghya e
guṇana-mātrā' {x} {y} {u} {v} d e =
  dairghya-⊕ (dakṣiṇāṅga x e) (vāmāṅga d v)
  ∙ cong₂ N._+_ (mātrā-dakṣiṇa x e) (mātrā-vāma d v)
  ∙ N.+-comm (dairghya e) (dairghya d)

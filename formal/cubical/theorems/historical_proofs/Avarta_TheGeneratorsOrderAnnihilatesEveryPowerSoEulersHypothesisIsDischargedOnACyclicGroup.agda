{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- आवर्तः — जनकस्य आवर्तः सर्वां घातं नाशयति ।
--
-- (the turning: the generator's own order annihilates every power of it,
--  so RSA's single hypothesis is discharged where RSA actually lives.)
--
-- ────────────────────────────────────────────────────────────────────
-- THE HYPOTHESIS RSA RESTS ON, DISCHARGED ON A CYCLIC GROUP.
--
-- `Bijamula_TheRSAPrivateKeyIsThePulverizersWitnessAndDecryptionIs
-- PingalasExponentiation.agda` (absent from this repository) isolates RSA to one fact and says so
-- exactly:
--
--     "SO THE ONLY NUMBER THEORY IN RSA IS `pow x φ ≡ ε`.  Everything
--      else is Pigala's fold and ryabhaa's witness, both already
--      checked."
--
-- §न proves that fact in the one case where it is one line — and that
-- case is not a toy.  `BijamulaKrida_…agda` establishes the ground:
-- (ℤ/n)ˣ for a semiprime is a product of two CYCLIC groups, so a cyclic
-- factor is one CRT component of a real decryption, and it is where the
-- exponentiation computes at all.  So discharging the hypothesis on a
-- cyclic group discharges it exactly where that lane says RSA lives.
--
-- WHY IT IS ONE LINE.  In a cyclic group every element is a power of the
-- generator, and Pigala's two exponent laws are already proved in the
-- sibling module.  `घात (घात g k) n` reassociates to `घात (घात g n) k`
-- through commutativity of ℕ-multiplication, the hypothesis collapses the
-- inner term to ε, and `घात-ε` finishes.  Lagrange is not needed here
-- because a cyclic group's element orders divide the generator's order by
-- the arithmetic of exponents rather than by counting cosets — which is
-- the whole reason this case is separable from the general one.
--
-- The theorem is stated for a group GIVEN as cyclic.
--
-- ────────────────────────────────────────────────────────────────────
-- ON THE NAME.  आवर्त — a turning, a revolution, a whirl; ordinary
-- , used here in its plain sense for a group that comes back to
-- where it started.  The compound in the title is built here.  घात (exponentiation as a
-- fold) is Piṅgala's procedure, छन्दःशास्त्रम् ८ (~300 BCE), and the
-- kuṭṭaka whose witness supplies e·d ≡ φ·k+1 is Āryabhaṭa's,
--    (499).
-- The group theory is not Indian and is not dressed as Indian.
------------------------------------------------------------------------

module Avarta_TheGeneratorsOrderAnnihilatesEveryPowerSoEulersHypothesisIsDischargedOnACyclicGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_)
open import Cubical.Data.Nat.Properties using (·-comm)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Bijamula_TheRSAPrivateKeyIsThePulverizersWitnessAndDecryptionIsPingalasExponentiation
  using (CMonoid ; घात ; घात-ε ; घात-गुणः ; बीजमूल-सिद्धि)

private
  variable
    ℓ : Level

module _ {M : Type ℓ} (CM : CMonoid M) where
  open CMonoid CM

  ------------------------------------------------------------------------
  -- १ · आवर्तः — a cyclic group, as the data that makes it one: a
  --     generator, its order, and the fact that every element is a power
  --     of it.  Stated as a record of hypotheses rather than assumed of
  --     the ambient monoid, so §२ says exactly what it needs.
  ------------------------------------------------------------------------

  आवर्तः : M → ℕ → Type ℓ
  आवर्तः g n = (घात CM g n ≡ ε) × ((x : M) → Σ[ k ∈ ℕ ] (घात CM g k ≡ x))
    where open import Cubical.Data.Sigma using (_×_)

  ------------------------------------------------------------------------
  -- २ · यूलर-सिद्धिः — THE HYPOTHESIS, DISCHARGED.
  --
  --     Every element of a cyclic group is annihilated by the generator's
  --     own order.  No counting, no cosets: the element is `घात g k`, and
  --     `घात (घात g k) n ≡ घात (घात g n) k` by the commutativity of
  --     ℕ-multiplication inside Piṅgala's second exponent law.
  ------------------------------------------------------------------------

  जनक-आवर्तः : (g : M) (n : ℕ) → घात CM g n ≡ ε
             → (k : ℕ) → घात CM (घात CM g k) n ≡ ε
  जनक-आवर्तः g n gn≡ε k =
      sym (घात-गुणः CM g k n)                    -- घात (घात g k) n ≡ घात g (k·n)
    ∙ cong (घात CM g) (·-comm k n)                -- ≡ घात g (n·k)
    ∙ घात-गुणः CM g n k                           -- ≡ घात (घात g n) k
    ∙ cong (λ z → घात CM z k) gn≡ε                -- ≡ घात ε k
    ∙ घात-ε CM k                                  -- ≡ ε

  -- and therefore of EVERY element, once every element is known to be a
  -- power of the generator
  यूलर-सिद्धिः : (g : M) (n : ℕ) → आवर्तः g n → (x : M) → घात CM x n ≡ ε
  यूलर-सिद्धिः g n (gn≡ε , surj) x =
    cong (λ z → घात CM z n) (sym (snd (surj x)))
    ∙ जनक-आवर्तः g n gn≡ε (fst (surj x))

  ------------------------------------------------------------------------
  -- ३ · बीजमूल-सिद्धिः-निरुपाधिका — RSA correctness with NO Euler
  --     hypothesis, on a cyclic group.
  --
  --     The sibling's theorem takes `घात x φ ≡ ε` as an argument.  Here
  --     it is supplied by §२, so what remains to be given is exactly
  --     Āryabhaṭa's witness — e·d ≡ φ·k+1 — and nothing else.  That is the
  --     sentence "the only number theory in RSA is pow x φ ≡ ε" turned
  --     around: on this ground there is none left, and the whole of RSA is
  --     Pigala's fold plus the pulverizer's witness.
  ------------------------------------------------------------------------

  बीजमूल-सिद्धिः-निरुपाधिका
    : (g : M) (φ : ℕ) → आवर्तः g φ
    → (x : M) (e d k : ℕ) → e · d ≡ φ · k + 1
    → घात CM (घात CM x e) d ≡ x
  बीजमूल-सिद्धिः-निरुपाधिका g φ cyc x e d k witness =
    बीजमूल-सिद्धि CM x e d φ k witness (यूलर-सिद्धिः g φ cyc x)

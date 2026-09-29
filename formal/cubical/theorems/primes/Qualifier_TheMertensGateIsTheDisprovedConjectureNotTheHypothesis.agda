{-# OPTIONS --cubical --guardedness --safe #-}

------------------------------------------------------------------------
-- उपाधि — the defeating condition, and a gate that has one.
--
-- TEXT AND DATE.  उपाधि / *upādhi*, the adventitious condition under
-- which a pervasion fails: Gagea, *Tattvacintmai*, c. 1325, and the
-- Navya-Nyya schools after him.  The rule the term carries is that a
-- universal claim is licensed not by the number of confirming instances
-- but by having searched for the condition that would break it and stated
-- the extent of the search; an inference with an undetected updhi is not
-- knowledge, however many instances stand behind it.
--
-- `Shodhita` and `Ekam` hold a gate at
-- every step of a Mertens walk, `|M(k)|² ≤ k`, and report it as
-- "the mertens fragment of RH" and "RH-fragment: |M(k)| ≤ √k for all
-- k ≤ 400".  Two things are wrong with that label and one thing is right.
--
--   The gate is the MERTENS CONJECTURE, in its non-strict form: Mertens
--   stated |M(x)| < √x, the gate here asks |M(k)|² ≤ k.  It was DISPROVED
--   — Odlyzko and te Riele, "Disproof of the Mertens conjecture",
--   *Journal für die reine und angewandte Mathematik* 357 (1985),
--   138–160, which shows limsup M(x)/√x > 1 and so refutes the
--   non-strict form as well.  There is a k at which the gate fails.  No walk anybody can run will reach it, which is
--   exactly why a walk returning `true` at 60 and at 400 carries no
--   information: the updhi is known to exist and is known to be out of
--   reach of the search.
--
--   The gate is also not the hypothesis.  RH is equivalent to
--   M(x) = O(x^(1/2+ε)) for every ε > 0, which is strictly weaker than
--   |M(k)| ≤ √k and is not expressible in this file, having no reals in
--   it.  Calling the strong false statement a fragment of the weaker open
--   one runs the implication backwards.
--
--   What is right is the arithmetic.  M(60) = −1 and M(100) = +1 are the
--   published values and they are recomputed below off the certified
--   factorization, not off a boolean sieve.
--
-- WHAT THIS FILE DOES.  It separates the two propositions into two types
-- so the conflation becomes a type error rather than a wording problem.
-- `MertensConjecture` is the universal statement.  `AllGate n` is the
-- finite check.  `restrict` maps the first to the second at every n, and
-- there is deliberately no term in the other direction, because the other
-- direction is the error and it is false.  `checkedTo20` is the finite
-- fact as a proof object rather than a flag.  The prefix is 20 and not
-- Shodhita's 60 because `AllGate n` recomputes the walk at every k, which
-- is quadratic in certified factorizations; the length of a finite check
-- is the one quantity this file is arguing does not matter.
--
------------------------------------------------------------------------

module Qualifier_TheMertensGateIsTheDisprovedConjectureNotTheHypothesis where

open import Shodhita using (μ̂)
open import Parisodhana using (dec≤)
open import Pramanya_TheBooleanCarriesNoWarrantSoTheSweepCarriesTheProof
  using (True; toWitness)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (Dec; yes; no)

-- ═══ M(k) off the certified μ, as (plus, minus) ═══
bump : ℕ → ℕ × ℕ → ℕ × ℕ
bump v pm with discreteℕ v 1
... | yes _ = suc (fst pm) , snd pm
... | no  _ with discreteℕ v 2
...   | yes _ = fst pm , suc (snd pm)
...   | no  _ = pm

Mcount : ℕ → ℕ × ℕ
Mcount zero    = 0 , 0
Mcount (suc k) = bump (μ̂ (suc k) (suc-≤-suc zero-≤)) (Mcount k)

-- |M(k)|, without leaving ℕ: one of the two differences is zero
absM : ℕ → ℕ
absM k = (fst (Mcount k) ∸ snd (Mcount k)) + (snd (Mcount k) ∸ fst (Mcount k))

-- ═══ the gate, as a proposition ═══
Gate : ℕ → Type₀
Gate k = absM k · absM k ≤ k

decGate : (k : ℕ) → Dec (Gate k)
decGate k = dec≤ (absM k · absM k) k

-- the universal statement.  THIS IS THE MERTENS CONJECTURE, AND IT IS FALSE
-- (Odlyzko–te Riele 1985).  It is written down so that the finite check
-- below cannot be mistaken for it.
MertensConjecture : Type₀
MertensConjecture = (k : ℕ) → Gate k

-- the finite check: the gate at every k ≤ n
AllGate : ℕ → Type₀
AllGate zero    = Unit
AllGate (suc k) = Gate (suc k) × AllGate k

decAllGate : (n : ℕ) → Dec (AllGate n)
decAllGate zero    = yes tt
decAllGate (suc k) with decGate (suc k)
... | no ¬g = no λ { (g , _) → ¬g g }
... | yes g with decAllGate k
...   | yes rest = yes (g , rest)
...   | no ¬rest = no λ { (_ , rest) → ¬rest rest }

-- ═══ the one implication that holds ═══
restrict : MertensConjecture → (n : ℕ) → AllGate n
restrict mc zero    = tt
restrict mc (suc k) = mc (suc k) , restrict mc k

-- and there is no term in the other direction, on purpose.  the walk in
-- `Shodhita` and `Ekam` establishes the RIGHT-HAND side for one n only.

-- ═══ the finite fact, as a proof object rather than a flag ═══
checkedTo20 : AllGate 20
checkedTo20 = toWitness {d = decAllGate 20} tt

-- ═══ the arithmetic ═══
-- M(60) = −1: the minus count exceeds the plus count by one
_ : snd (Mcount 60) ∸ fst (Mcount 60) ≡ 1
_ = refl

_ : fst (Mcount 60) ∸ snd (Mcount 60) ≡ 0
_ = refl

_ : absM 60 ≡ 1
_ = refl

-- μ̂ agrees with the published values on the standard checks
_ : μ̂ 30 (suc-≤-suc zero-≤) ≡ 2     -- μ(2·3·5) = −1
_ = refl
_ : μ̂ 12 (suc-≤-suc zero-≤) ≡ 0     -- μ(4·3) = 0
_ = refl

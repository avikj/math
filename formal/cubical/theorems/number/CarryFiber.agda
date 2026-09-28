{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CarryFiber
--
-- A precisely stated obstruction to transporting the R0032 chart.
--
-- proves: for the rank-one Smith cell the complete transporter is a
-- REGULAR D∞-torsor, charted by (U₀₀, det U) : Z × {±1}; the retained
-- proof-relevant payload for that stratum is exactly `Z × Bool`.
--
-- The successor seed asks for the general stratum.  The curriculum layer
-- (runtime/curriculum, `test_curriculum.py` (absent from this repository)) meanwhile asserts that
-- POSITIONAL NOTATION costs exactly three choices — a finite quotient
-- (the base), a torsor (endianness) and a cocycle (the carry) — i.e. the
-- same "one integer and one sign, plus a carry" vocabulary.
--
-- This module shows the two vocabularies do NOT glue: the carry stratum
-- admits no uniform torsor chart at all, for ANY structure group.
--
-- The object.  Fix width 2 and the redundant binary alphabet {0,1,2}
-- (the alphabet a carry normalisation acts on: a digit 2 is exactly a
-- pending carry).  Let  value (a,b) = a + 2b  and let the descent fibre
-- over n be  Fib n = Σ w. value w ≡ n.  Then
--
--     Fib 1 is contractible,          (one representation:  1 = 1 + 2·0)
--     Fib 2 has two distinct points   (2 = 2 + 2·0  and  2 = 0 + 2·1),
--
-- so `Fib 1 ≃ Fib 2` is absurd.  A regular G-torsor structure on every
-- inhabited fibre would give, for each inhabited n, an equivalence
-- Fib n ≃ G (choose the base point); composing at n = 1 and n = 2 gives
-- exactly that absurdity.  Hence:
--
--   * no group G — in particular not D∞, and no payload type G — in
--     particular not `Z × Bool` — charts the carry fibres uniformly;
--   * fibre cardinality is a non-constant invariant of the carry
--     descent, whereas it is constant for a torsor.  R0032's payload
--     theorem is stratum-local and does not extend along the carry.
--
-- This is the model-side form of
-- machinery/formation_sufficiency.py (absent from this repository)'s "minimality need not transport":
-- the old chart survives restriction, not extension.
--
-- Everything below is a finite exhaustive verification (9 words) plus
-- two library lemmas; no postulates, no holes.
------------------------------------------------------------------------

module CarryFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Empty as Empty
open Empty using (⊥)

------------------------------------------------------------------------
-- 1. the redundant binary alphabet and the width-two value map
------------------------------------------------------------------------

data Digit : Type₀ where
  d0 d1 d2 : Digit

wt : Digit → ℕ
wt d0 = 0
wt d1 = 1
wt d2 = 2

Word : Type₀
Word = Digit × Digit

-- little-endian:  value (a , b) = a + 2·b
value : Word → ℕ
value (a , b) = wt a + (wt b + wt b)

-- the fibre of the descent over a value
Fib : ℕ → Type₀
Fib n = Σ[ w ∈ Word ] (value w ≡ n)

------------------------------------------------------------------------
-- 2. numeral codes:  the only way a natural number literal is refuted
------------------------------------------------------------------------

Is1 : ℕ → Type₀
Is1 zero = ⊥
Is1 (suc zero) = Unit
Is1 (suc (suc _)) = ⊥

DCode : Digit → Type₀
DCode d0 = ⊥
DCode d1 = ⊥
DCode d2 = Unit

------------------------------------------------------------------------
-- 3. Fib 1 is contractible  (exhaustive over the nine words)
------------------------------------------------------------------------

pt1 : Fib 1
pt1 = (d1 , d0) , refl

wordPath1 : (a b : Digit) → value (a , b) ≡ 1 → Path Word (d1 , d0) (a , b)
wordPath1 d0 d0 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d1 d0 _ = refl
wordPath1 d2 d0 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d0 d1 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d1 d1 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d2 d1 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d0 d2 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d1 d2 p = Empty.rec (subst Is1 (sym p) tt)
wordPath1 d2 d2 p = Empty.rec (subst Is1 (sym p) tt)

isContrFib1 : isContr (Fib 1)
isContrFib1 = pt1 , λ { ((a , b) , p) →
  Σ≡Prop (λ w → isSetℕ (value w) 1) (wordPath1 a b p) }

------------------------------------------------------------------------
-- 4. Fib 2 has two distinct points
------------------------------------------------------------------------

carryRep noCarryRep : Fib 2
carryRep   = (d2 , d0) , refl     -- 2 = 2 + 2·0   (the pending carry)
noCarryRep = (d0 , d1) , refl     -- 2 = 0 + 2·1   (the normal form)

carry≢normal : carryRep ≡ noCarryRep → ⊥
carry≢normal e = subst DCode (cong (λ z → fst (fst z)) e) tt

------------------------------------------------------------------------
-- 5. the obstruction
------------------------------------------------------------------------

-- Fibre cardinality is not constant along the carry descent.
Fib1≃Fib2→⊥ : (Fib 1 ≃ Fib 2) → ⊥
Fib1≃Fib2→⊥ e =
  carry≢normal (isContr→isProp (isOfHLevelRespectEquiv 0 e isContrFib1)
                               carryRep noCarryRep)

-- A regular G-torsor structure on every inhabited fibre yields, after a
-- choice of base point, exactly this datum.  So no such structure exists,
-- for any G in any universe.
no-uniform-chart : {ℓ : Level} {G : Type ℓ}
                 → ((n : ℕ) → Fib n → (Fib n ≃ G)) → ⊥
no-uniform-chart {G = G} h =
  Fib1≃Fib2→⊥ (compEquiv (h 1 pt1) (invEquiv (h 2 carryRep)))

-- The R0032 payload, named.  `Z × Bool` is the trace type R0032 fixes for
-- the rank-one Smith stratum; it does not chart the carry stratum.
no-Int×Bool-chart : ((n : ℕ) → Fib n → (Fib n ≃ (ℤ × Bool))) → ⊥
no-Int×Bool-chart = no-uniform-chart

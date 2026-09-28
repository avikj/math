{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- HeadDepthMerge
--
-- The quantity  e_b(q) = v_q(b^ord_q(b) − 1)
-- is computed by two separate organs under three names —
--
--   * CYCLOTOMIC_SENSOR's head depth (the sensor state (d,e)),
--   * HEAD_DEPTH_BLINDNESS Thm W3's Fermat blindness depth
--       (b fails to refute q^a  ⟺  e_b(q) ≥ a),
--   * EXPOSED_SET Cor W2's Wieferich condition (e_2(q) ≥ 2),
--
-- This module is the merged organ:
-- the note's "1048 triples, zero disagreements" table is a CHECKED TERM
-- (finite exhaustive verification is proof, CLAUDE.md (absent from this repository)).
--
-- One definition (headDepth); every other predicate below is a
-- threshold reading of it.
--
-- STRONG BLINDNESS. 
-- W3 pins FERMAT blindness exactly; the strong (Miller–Rabin)
-- test refutes more; is the strong-blindness depth also e_b(q), or is
-- there a correction term?  Answer: EQUALITY, no correction.  For n =
-- q^a (q odd prime) the unit group is cyclic, so (i) the Fermat liars
-- form the cyclic subgroup H of order q−1 (W3's proof); (ii) for b ∈ H
-- with ord(b) = 2^j·u (u odd), u divides the odd part d of n−1 (since
-- u ∣ q−1 ∣ n−1), so b^d has order 2^j; (iii) if j = 0 then b^d = 1,
-- else b^{d·2^{j−1}} is the unique involution of a cyclic group, which
-- is −1, and j ≤ v₂(q−1) ≤ v₂(n−1) puts that index inside the
-- Miller–Rabin window.  Hence every Fermat liar for an odd prime power
-- is a strong liar: strong blindness = Fermat blindness = (a ≤ e_b(q)).
-- (This is Monier/Rabin-era liar bookkeeping.  The certificate over the
-- 1048-triple range is `strongTheorem` below.)
--
-- Wieferich becomes an instance: the only known Wieferich primes 1093
-- and 3511 are certified as the e ≥ 2 threshold events, with their
-- neighbours certified below threshold.
--
-- Everything computes through Agda.Builtin.Nat primitives (GMP-backed
-- in the checker), so the kernel evaluates 2^1754 mod 3511² without
-- noticing.  --safe throughout; no postulates, no holes.
------------------------------------------------------------------------

module HeadDepthMerge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Agda.Builtin.Nat using (_==_; _<_; div-helper; mod-helper; _*_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_; not)
open import Cubical.Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Fast arithmetic on builtin ℕ

_%%_ : ℕ → ℕ → ℕ
n %% zero  = n
n %% suc m = mod-helper 0 m n m

_//_ : ℕ → ℕ → ℕ
n // zero  = 0
n // suc m = div-helper 0 m n m

eqBool : Bool → Bool → Bool
eqBool x y = if x then y else not y

-- a ≤ e as a Bool
_≤?_ : ℕ → ℕ → Bool
a ≤? e = a < suc e

power : ℕ → ℕ → ℕ
power b zero    = 1
power b (suc n) = b * power b n

-- modular exponentiation by squaring; fuel bounds the bit length
powMod : ℕ → ℕ → ℕ → ℕ → ℕ
powMod zero    m b e = 1 %% m
powMod (suc f) m b e =
  if e == 0 then 1 %% m
  else (let h = powMod f m ((b * b) %% m) (e // 2)
        in if e %% 2 == 1 then (b * h) %% m else h)

-- multiplicative order of b modulo q (fuel q suffices for q prime)
ordFrom : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
ordFrom zero    q b acc k = 0
ordFrom (suc f) q b acc k =
  if acc == 1 then k else ordFrom f q b ((acc * b) %% q) (suc k)

ord : ℕ → ℕ → ℕ
ord q b = ordFrom q q b (b %% q) 1

-- q-adic valuation, capped by fuel; v(0) saturates to the fuel (acts
-- as ∞ against every threshold a ≤ 40 used here)
vCap : ℕ → ℕ → ℕ → ℕ
vCap zero    q n = 0
vCap (suc f) q n =
  if n == 0 then suc f
  else (if n %% q == 0 then suc (vCap f q (n // q)) else 0)

------------------------------------------------------------------------
-- THE quantity, defined once

-- e_b(q) = v_q(b^{ord_q(b)} − 1): the cyclotomic head depth
headDepth : ℕ → ℕ → ℕ
headDepth q b = vCap 40 q (power b (ord q b) ∸ 1)

------------------------------------------------------------------------
-- The three readings, as threshold readings of headDepth's rivals

-- reading 2: base b fails to refute q^a by the Fermat test
fermatBlind : ℕ → ℕ → ℕ → Bool
fermatBlind q a b =
  let n = power q a in powMod 40 n b (n ∸ 1) == 1

-- reading 3: Wieferich condition = threshold e_2(q) ≥ 2
wieferich : ℕ → Bool
wieferich q = 2 ≤? headDepth q 2

-- the strong (Miller–Rabin) reading: b is a strong liar for q^a
mrChain : ℕ → ℕ → ℕ → Bool
mrChain n zero    x = false
mrChain n (suc k) x =
  if x == n ∸ 1 then true else mrChain n k ((x * x) %% n)

strongBlind : ℕ → ℕ → ℕ → Bool
strongBlind q a b =
  let n  = power q a
      s  = vCap 40 2 (n ∸ 1)
      d  = (n ∸ 1) // power 2 s
      x₀ = powMod 40 n b d
  in if x₀ == 1 then true else mrChain n s x₀

------------------------------------------------------------------------
-- The certified range: q ≤ 23 odd prime, 2 ≤ b < 3q with q ∤ b,
-- 1 ≤ a ≤ 4 — the note's exact 1048 triples

range : ℕ → ℕ → List ℕ
range x zero    = []
range x (suc n) = x ∷ range (suc x) n

allList : (ℕ → Bool) → List ℕ → Bool
allList f []       = true
allList f (x ∷ xs) = f x and allList f xs

oddPrimes : List ℕ
oddPrimes = 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ []

overTriples : (ℕ → ℕ → ℕ → Bool) → Bool
overTriples P =
  allList
    (λ q → allList
      (λ b → if b %% q == 0 then true
             else allList (λ a → P q a b) (range 1 4))
      (range 2 (3 * q ∸ 2)))
    oddPrimes

-- Theorem W3, kernel form: Fermat blindness on q^a ⟺ a ≤ e_b(q),
-- exhaustively over all 1048 triples.
w3Certificate : Bool
w3Certificate = overTriples
  (λ q a b → eqBool (fermatBlind q a b) (a ≤? headDepth q b))

w3Theorem : w3Certificate ≡ true
w3Theorem = refl

-- On the same range, the STRONG test is blind exactly
-- as deep as the Fermat test on odd prime powers — no correction term.
-- General proof in the header/note; kernel certificate here.
strongCertificate : Bool
strongCertificate = overTriples
  (λ q a b → eqBool (strongBlind q a b) (fermatBlind q a b))

strongTheorem : strongCertificate ≡ true
strongTheorem = refl

------------------------------------------------------------------------
-- Corollary W4 instances: the blind bases at depth a form the
-- subgroup of order q−1 in (ℤ/q^a)^× — the note's table, certified

countList : (ℕ → Bool) → List ℕ → ℕ
countList f []       = 0
countList f (x ∷ xs) = (if f x then 1 else 0) + countList f xs

blindCount : ℕ → ℕ → ℕ
blindCount q a =
  countList
    (λ b → if b %% q == 0 then false else a ≤? headDepth q b)
    (range 1 (power q a))

w4-5-2 : blindCount 5 2 ≡ 4
w4-5-2 = refl

w4-5-3 : blindCount 5 3 ≡ 4
w4-5-3 = refl

w4-7-3 : blindCount 7 3 ≡ 6
w4-7-3 = refl

w4-13-3 : blindCount 13 3 ≡ 12
w4-13-3 = refl

------------------------------------------------------------------------
-- Wieferich as the b = 2 threshold instance: both known Wieferich
-- primes certified at e ≥ 2, immediate neighbours certified below

wieferich-1093 : wieferich 1093 ≡ true
wieferich-1093 = refl

wieferich-3511 : wieferich 3511 ≡ true
wieferich-3511 = refl

notWieferich-1091 : wieferich 1091 ≡ false
notWieferich-1091 = refl

notWieferich-3517 : wieferich 3517 ≡ false
notWieferich-3517 = refl

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- HeadDepthTwo
--
-- HEAD_DEPTH_BLINDNESS seed 2, dissolved.
--
-- The seed expected: the two-entry 2-sensor (e₋,e₊) = (v₂(b−1),v₂(b+1))
-- of CYCLOTOMIC_SENSOR eq (2) should correspond to a TWO-parameter
-- blindness statement at q = 2, mirroring Theorem W3's one-parameter
-- statement at odd q.  It does not, and the reason is one parity:
--
--     the Fermat exponent at modulus 2^a is  2^a − 1,  which is ODD.
--
-- CYCLOTOMIC_SENSOR eq (2) reads, for odd b:
--     v₂(b^m − 1) = e₋                    (m odd)
--     v₂(b^m − 1) = e₋ + e₊ + v₂(m) − 1   (m even)
-- and only the odd branch can ever fire on a Fermat exponent of an even
-- modulus.  So e₊ NEVER ENTERS, and the q = 2 analogue of W3 is the
-- one-parameter collapse
--
--   W3₂.  For odd b and a ≥ 1:
--     b Fermat-blind on 2^a  ⟺  e₋(b) ≥ a  ⟺  b ≡ 1 (mod 2^a),
--   hence  e₋(b) = max{ a : b blind on 2^a }:  the blindness depth at 2
--   is the FIRST head entry alone.
--
-- Two one-line proofs, one per organ:
--   (group)  (ℤ/2^a)^× has order 2^{a−1}; blindness makes ord(b) divide
--     both 2^{a−1} and the odd number 2^a − 1, so ord(b) = 1, b ≡ 1.
--     Conversely 1^{2^a−1} = 1.  (No LTE needed at all.)
--   (sensor) blindness ⟺ v₂(b^{2^a−1} − 1) ≥ a ⟺ e₋ ≥ a by the odd
--     branch of eq (2); and e₋ ≥ a ⟺ 2^a ∣ b − 1.
--
-- The strong (Miller–Rabin) reading collapses even harder: n = 2^a has
-- n − 1 odd, so s = v₂(n−1) = 0, the MR window {b^{2^r d} ≡ −1, r < s}
-- is EMPTY, and strong = Fermat by the shape of the definition — before
-- any arithmetic.  (MR as usually stated presupposes n odd; at even n
-- its formula degenerates to the Fermat test.  Certified below anyway.)
--
-- W4's index formula survives VERBATIM at q = 2: the blind bases mod
-- 2^a form the unique subgroup of order q − 1 = 1 (the trivial group),
-- index q^{a−1} = 2^{a−1} = φ(2^a) — only "cyclic" must be dropped from
-- W4's proof, since (ℤ/2^a)^× is not cyclic for a ≥ 3; uniqueness of
-- the trivial subgroup needs no cyclicity.
--
-- So CYCLOTOMIC_SENSOR's p = 2 exception (the length-two head, = the
-- torsion of U₁, Theorem 4 there) does NOT propagate to the blindness
-- organ: the Fermat anatomy at 2 reads Φ₁(b) = b − 1 and is blind to
-- Φ₂(b) = b + 1.  The dissolution witnesses below make this exact:
-- bases 3 and 7 share e₋ = 1, differ in e₊ (2 vs 3), and have
-- identical blindness columns; base 255 has the MAXIMAL second entry
-- e₊ = 8 in range and is still blind only at the vacuous depth a = 1.
--
-- Kernel certificates: all odd b < 256, all 1 ≤ a ≤ 8 (1024 pairs),
-- checked terms by refl — finite exhaustive verification is proof
-- (CLAUDE.md (absent from this repository)).  Style and helpers mirror HeadDepthMerge.agda; the
-- general statements are the one-liners above.
------------------------------------------------------------------------

module HeadDepthTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Agda.Builtin.Nat using (_==_; _<_; div-helper; mod-helper; _*_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_; not)
open import Cubical.Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Fast arithmetic on builtin ℕ (as in HeadDepthMerge)

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

-- 2-adic valuation, capped by fuel; v(0) saturates to the fuel (acts
-- as ∞ against every threshold a ≤ 8 used here — the base b = 1 case)
vCap : ℕ → ℕ → ℕ → ℕ
vCap zero    q n = 0
vCap (suc f) q n =
  if n == 0 then suc f
  else (if n %% q == 0 then suc (vCap f q (n // q)) else 0)

------------------------------------------------------------------------
-- The two-entry 2-sensor, CYCLOTOMIC_SENSOR eq (2): the whole state

eMinus : ℕ → ℕ
eMinus b = vCap 40 2 (b ∸ 1)

ePlus : ℕ → ℕ
ePlus b = vCap 40 2 (b + 1)

------------------------------------------------------------------------
-- The two blindness readings at modulus 2^a

-- base b fails to refute 2^a by the Fermat test
fermatBlindTwo : ℕ → ℕ → Bool
fermatBlindTwo a b =
  let n = power 2 a in powMod 40 n b (n ∸ 1) == 1

-- the strong (Miller–Rabin) reading, written with its full window so
-- that the window's emptiness at even n is certified, not assumed
mrChain : ℕ → ℕ → ℕ → Bool
mrChain n zero    x = false
mrChain n (suc k) x =
  if x == n ∸ 1 then true else mrChain n k ((x * x) %% n)

strongBlindTwo : ℕ → ℕ → Bool
strongBlindTwo a b =
  let n  = power 2 a
      s  = vCap 40 2 (n ∸ 1)
      d  = (n ∸ 1) // power 2 s
      x₀ = powMod 40 n b d
  in if x₀ == 1 then true else mrChain n s x₀

------------------------------------------------------------------------
-- The certified range: all odd b < 256, all 1 ≤ a ≤ 8 — 1024 pairs

range : ℕ → ℕ → List ℕ
range x zero    = []
range x (suc n) = x ∷ range (suc x) n

allList : (ℕ → Bool) → List ℕ → Bool
allList f []       = true
allList f (x ∷ xs) = f x and allList f xs

overPairs : (ℕ → ℕ → Bool) → Bool
overPairs P =
  allList
    (λ b → if b %% 2 == 0 then true
           else allList (λ a → P a b) (range 1 8))
    (range 1 255)

-- W3₂, sensor form: Fermat blindness on 2^a ⟺ a ≤ e₋(b).  The
-- second head entry e₊ appears nowhere on either side.
w3TwoCertificate : Bool
w3TwoCertificate = overPairs
  (λ a b → eqBool (fermatBlindTwo a b) (a ≤? eMinus b))

w3TwoTheorem : w3TwoCertificate ≡ true
w3TwoTheorem = refl

-- W3₂, residue form: the same events are exactly b ≡ 1 (mod 2^a) —
-- the group-theoretic one-liner, kernel-checked on the range
residueCertificate : Bool
residueCertificate = overPairs
  (λ a b → eqBool (fermatBlindTwo a b) ((b %% power 2 a) == 1))

residueTheorem : residueCertificate ≡ true
residueTheorem = refl

-- the strong test collapses to Fermat at every 2^a: n − 1 odd ⟹
-- s = 0 ⟹ the MR window is empty.  Both halves certified: the
-- collapse itself, and its reason v₂(2^a − 1) = 0.
strongCollapseCertificate : Bool
strongCollapseCertificate = overPairs
  (λ a b → eqBool (strongBlindTwo a b) (fermatBlindTwo a b))

strongCollapseTheorem : strongCollapseCertificate ≡ true
strongCollapseTheorem = refl

sZeroCertificate : Bool
sZeroCertificate =
  allList (λ a → vCap 40 2 (power 2 a ∸ 1) == 0) (range 1 8)

sZeroTheorem : sZeroCertificate ≡ true
sZeroTheorem = refl

------------------------------------------------------------------------
-- W4 at q = 2, verbatim: the blind bases mod 2^a are the trivial
-- subgroup — count 1 = "order q − 1" — at every depth 1 ≤ a ≤ 8

countList : (ℕ → Bool) → List ℕ → ℕ
countList f []       = 0
countList f (x ∷ xs) = (if f x then 1 else 0) + countList f xs

blindCountTwo : ℕ → ℕ
blindCountTwo a =
  countList
    (λ b → if b %% 2 == 0 then false else fermatBlindTwo a b)
    (range 1 (power 2 a))

w4TwoCertificate : Bool
w4TwoCertificate = allList (λ a → blindCountTwo a == 1) (range 1 8)

w4TwoTheorem : w4TwoCertificate ≡ true
w4TwoTheorem = refl

------------------------------------------------------------------------
-- Dissolution witnesses: e₊ is invisible to the blindness organ

sameProfile : ℕ → ℕ → Bool
sameProfile b b' =
  allList (λ a → eqBool (fermatBlindTwo a b) (fermatBlindTwo a b'))
          (range 1 8)

-- bases 3 and 7: same first entry (e₋ = 1), different second entries
-- (e₊ = 2 vs 3), identical blindness columns for every a ≤ 8
ePlusInvisible-3-7 :
  ((eMinus 3 == eMinus 7) and
   (not (ePlus 3 == ePlus 7)) and
   sameProfile 3 7) ≡ true
ePlusInvisible-3-7 = refl

-- base 255 ≡ −1 (mod 256): the maximal second entry in range, e₊ = 8,
-- yet blind only at the vacuous depth a = 1 (2 itself is prime), since
-- e₋(255) = 1.  A deep Φ₂-head buys no blindness at all.
ePlus-255 : ePlus 255 ≡ 8
ePlus-255 = refl

eMinus-255 : eMinus 255 ≡ 1
eMinus-255 = refl

deepPlusNotBlind-255 :
  ((fermatBlindTwo 1 255) and
   allList (λ a → not (fermatBlindTwo a 255)) (range 2 7)) ≡ true
deepPlusNotBlind-255 = refl

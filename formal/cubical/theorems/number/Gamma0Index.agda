{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------------
-- Gamma0Index : the index of the divisor-flag congruence group in GLᵣ(ℤ)
--
-- stabilizer
--
--     Γ₀(D) = GLᵣ(ℤ) ∩ D·GLᵣ(ℤ)·D⁻¹ = { A : (dᵢ/dⱼ) ∣ Aᵢⱼ for i > j }
--
-- for a divisor chain D = diag(d₁ ∣ d₂ ∣ … ∣ dᵣ), and R0037
-- computed its INDEX.  The note proves
--
--     [GLᵣ(ℤ) : Γ₀(D)]  =  ∏_p  p^(G_p − E_p) · [ r ; r₁,…,r_k ]_p ,
--
--     G_p = Σ_{i>j} (eᵢ − eⱼ),  eᵢ = v_p(dᵢ),
--     E_p = Σ_{u<t} r_u r_t,    r₁,…,r_k = multiplicities of the distinct eᵢ,
--     [ r ; r₁,…,r_k ]_p = ∏_{s=1}^{r}(p^s−1) / ∏_t ∏_{s=1}^{r_t}(p^s−1)
--                          (the Gaussian multinomial: |GLᵣ(𝔽_p)/P| ).
--
-- This module VERIFIES that formula exhaustively, in the kernel, by counting
-- every matrix over ℤ/n for r = 2, 3, 4 in the cases listed in §4.  Every test
-- is `refl`: the counters below really enumerate n^(r²) matrices (up to 4⁹ =
-- 262144) and the numbers are computed, not asserted.
--
-- Nothing is postulated and nothing is floating point.  The verification is
-- corroboration only: the theorem itself is proved in the note.
------------------------------------------------------------------------------
module Gamma0Index where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_; _·_; _∸_)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Agda.Builtin.Nat using (mod-helper; div-helper; _==_)
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------------
-- 1.  Exact machine arithmetic on ℕ (builtin, so the kernel evaluates fast)
------------------------------------------------------------------------------

ite : {A : Type₀} → Bool → A → A → A
ite true  x _ = x
ite false _ y = y

ind : Bool → ℕ
ind b = ite b 1 0

infixl 7 _%_ _//_

_%_ : ℕ → ℕ → ℕ
n % zero  = 0
n % suc m = mod-helper 0 m n m

-- exact division; every use below divides exactly
_//_ : ℕ → ℕ → ℕ
n // zero  = 0
n // suc m = div-helper 0 m n m

-- `d ∣? x` : does d divide x?   (only used with d ≥ 1)
_∣?_ : ℕ → ℕ → Bool
d ∣? x = (x % d) == 0

-- gcd by Euclid with an explicit fuel bound (structural, hence --safe)
gcdF : ℕ → ℕ → ℕ → ℕ
gcdF zero    a b       = a
gcdF (suc k) a zero    = a
gcdF (suc k) a (suc b) = gcdF k (suc b) (a % suc b)

gcd! : ℕ → ℕ → ℕ
gcd! a b = gcdF (suc (a + b)) a b

-- x is a unit of ℤ/n  ⟺  gcd(x,n) = 1
isU : ℕ → ℕ → Bool
isU n x = gcd! x n == 1

pow : ℕ → ℕ → ℕ
pow p zero    = 1
pow p (suc k) = p · pow p k

-- Σ_{k<m} f k
Σ< : ℕ → (ℕ → ℕ) → ℕ
Σ< zero    f = 0
Σ< (suc k) f = f k + Σ< k f

------------------------------------------------------------------------------
-- 2.  The predicted index, as a function of p and the valuation vector
--
-- `exps` is (v_p d₁ , … , v_p dᵣ), sorted ascending (the divisor chain).
------------------------------------------------------------------------------

lenL : List ℕ → ℕ
lenL []       = 0
lenL (_ ∷ xs) = suc (lenL xs)

sumL : List ℕ → ℕ
sumL []       = 0
sumL (x ∷ xs) = x + sumL xs

-- Σ_{y ∈ ys} (y ∸ x)   (used with ys the tail of a sorted list, so y ≥ x)
minusAll : ℕ → List ℕ → ℕ
minusAll x []       = 0
minusAll x (y ∷ ys) = (y ∸ x) + minusAll x ys

-- G = Σ_{i>j} (eᵢ − eⱼ)
pairGaps : List ℕ → ℕ
pairGaps []       = 0
pairGaps (x ∷ xs) = minusAll x xs + pairGaps xs

-- run-length multiplicities of the (sorted) valuation vector
runsGo : ℕ → ℕ → List ℕ → List ℕ
runsGo v c []       = c ∷ []
runsGo v c (x ∷ xs) = ite (v == x) (runsGo v (suc c) xs) (c ∷ runsGo x 1 xs)

runLens : List ℕ → List ℕ
runLens []       = []
runLens (x ∷ xs) = runsGo x 1 xs

-- E = Σ_{u<t} r_u r_t
crossE : List ℕ → ℕ
crossE []       = 0
crossE (x ∷ xs) = x · sumL xs + crossE xs

-- ∏_{s=1}^{k} (p^s − 1)
qfac : ℕ → ℕ → ℕ
qfac p zero    = 1
qfac p (suc k) = (pow p (suc k) ∸ 1) · qfac p k

qfacProd : ℕ → List ℕ → ℕ
qfacProd p []       = 1
qfacProd p (r ∷ rs) = qfac p r · qfacProd p rs

-- the local index  p^(G−E) · [ r ; r₁,…,r_k ]_p , written as one exact division
idxLocal : ℕ → List ℕ → ℕ
idxLocal p exps =
  (pow p (pairGaps exps) · qfac p (lenL exps))
    // (pow p (crossE (runLens exps)) · qfacProd p (runLens exps))

------------------------------------------------------------------------------
-- 3.  Exhaustive counters over ℤ/n
--
-- `cnt2 n m₂₁`      counts A ∈ GL₂(ℤ/n) with m₂₁ ∣ A₂₁.
-- `cnt3 n m₂₁ m₃₁ m₃₂` and `cnt4 …` likewise.  All masks 1 gives |GLᵣ(ℤ/n)|.
--
-- Determinants are computed mod n with a padding constant large enough that
-- the truncated subtraction never truncates.
------------------------------------------------------------------------------

det2 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
det2 n a b c d = ((a · d) + (n · n) ∸ (b · c)) % n

cnt2 : ℕ → ℕ → ℕ
cnt2 n m21 =
  Σ< n λ a → Σ< n λ b → Σ< n λ c → Σ< n λ d →
    ind (isU n (det2 n a b c d)) · ind (m21 ∣? c)

det3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
det3 n a b c d e f g h i =
  ((a · (e · i)) + ((b · (f · g)) + ((c · (d · h)) + ((n · (n · n)) · 3)))
    ∸ ((c · (e · g)) + ((b · (d · i)) + (a · (f · h))))) % n

cnt3 : ℕ → ℕ → ℕ → ℕ → ℕ
cnt3 n m21 m31 m32 =
  Σ< n λ a → Σ< n λ b → Σ< n λ c →
  Σ< n λ d → Σ< n λ e → Σ< n λ f →
  Σ< n λ g → Σ< n λ h → Σ< n λ i →
    ind (isU n (det3 n a b c d e f g h i))
      · (ind (m21 ∣? d) · (ind (m31 ∣? g) · ind (m32 ∣? h)))

-- 4×4 determinant by cofactor expansion along the first row, all mod n.
det4 : ℕ → ℕ → ℕ → ℕ → ℕ
         → ℕ → ℕ → ℕ → ℕ
         → ℕ → ℕ → ℕ → ℕ
         → ℕ → ℕ → ℕ → ℕ → ℕ
det4 n a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
  ((a11 · det3 n a22 a23 a24 a32 a33 a34 a42 a43 a44)
    + ((a13 · det3 n a21 a22 a24 a31 a32 a34 a41 a42 a44)
      + ((n · n) · 2))
    ∸ ((a12 · det3 n a21 a23 a24 a31 a33 a34 a41 a43 a44)
      + (a14 · det3 n a21 a22 a23 a31 a32 a33 a41 a42 a43))) % n

cnt4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
cnt4 n m21 m31 m41 m32 m42 m43 =
  Σ< n λ a11 → Σ< n λ a12 → Σ< n λ a13 → Σ< n λ a14 →
  Σ< n λ a21 → Σ< n λ a22 → Σ< n λ a23 → Σ< n λ a24 →
  Σ< n λ a31 → Σ< n λ a32 → Σ< n λ a33 → Σ< n λ a34 →
  Σ< n λ a41 → Σ< n λ a42 → Σ< n λ a43 → Σ< n λ a44 →
    ind (isU n (det4 n a11 a12 a13 a14 a21 a22 a23 a24
                       a31 a32 a33 a34 a41 a42 a43 a44))
      · (ind (m21 ∣? a21) · (ind (m31 ∣? a31) · (ind (m41 ∣? a41)
      · (ind (m32 ∣? a32) · (ind (m42 ∣? a42) · ind (m43 ∣? a43))))))

------------------------------------------------------------------------------
-- 4.  Exhaustive verification
--
-- For each divisor chain D = diag(d₁,…,dᵣ), with n = dᵣ/d₁ the level, the test
--
--     cnt n 1…1  ≡  idxLocal p exps  ·  cnt n (ratios)
--
-- says:  |GLᵣ(ℤ/n)| = [GLᵣ(ℤ):Γ₀(D)] · |H|,  where H ⊆ GLᵣ(ℤ/n) is the
-- subgroup cut out by the same divisibility conditions, with the index
-- supplied by the closed formula and nothing else.
-- H is NOT the image of Γ₀(D): GLᵣ(ℤ) reduces only onto the det ±1 part
-- of GLᵣ(ℤ/n).  The ratio still equals the index because H contains the
-- diagonal matrices of every unit determinant, so both GLᵣ(ℤ/n) and H
-- split evenly over the determinant; that step is the note's, not
-- checked here.
------------------------------------------------------------------------------

-- 4a.  r = 2, D = diag(1, p^m).  Index = ψ(p^m) = p^(m−1)(p+1).
--      (This is the classical [SL₂(ℤ):Γ₀(N)] specialisation.)

r2p2m1 : cnt2 2 1 ≡ idxLocal 2 (0 ∷ 1 ∷ []) · cnt2 2 2
r2p2m1 = refl

r2p2m2 : cnt2 4 1 ≡ idxLocal 2 (0 ∷ 2 ∷ []) · cnt2 4 4
r2p2m2 = refl

r2p2m3 : cnt2 8 1 ≡ idxLocal 2 (0 ∷ 3 ∷ []) · cnt2 8 8
r2p2m3 = refl

r2p3m1 : cnt2 3 1 ≡ idxLocal 3 (0 ∷ 1 ∷ []) · cnt2 3 3
r2p3m1 = refl

r2p3m2 : cnt2 9 1 ≡ idxLocal 3 (0 ∷ 2 ∷ []) · cnt2 9 9
r2p3m2 = refl

r2p5m1 : cnt2 5 1 ≡ idxLocal 5 (0 ∷ 1 ∷ []) · cnt2 5 5
r2p5m1 = refl

r2p7m1 : cnt2 7 1 ≡ idxLocal 7 (0 ∷ 1 ∷ []) · cnt2 7 7
r2p7m1 = refl

r2p11m1 : cnt2 11 1 ≡ idxLocal 11 (0 ∷ 1 ∷ []) · cnt2 11 11
r2p11m1 = refl

-- the values themselves, so the reader sees the numbers
ψ4 : idxLocal 2 (0 ∷ 2 ∷ []) ≡ 6
ψ4 = refl

ψ8 : idxLocal 2 (0 ∷ 3 ∷ []) ≡ 12
ψ8 = refl

ψ9 : idxLocal 3 (0 ∷ 2 ∷ []) ≡ 12
ψ9 = refl

-- 4b.  Multiplicativity over coprime levels — the Chinese-remainder half of
--      the theorem, verified rather than assumed.  12 = 4·3, 10 = 2·5.

crtGL12 : cnt2 12 1 ≡ cnt2 4 1 · cnt2 3 1
crtGL12 = refl

crtΓ12 : cnt2 12 12 ≡ cnt2 4 4 · cnt2 3 3
crtΓ12 = refl

crtGL10 : cnt2 10 1 ≡ cnt2 2 1 · cnt2 5 1
crtGL10 = refl

crtΓ10 : cnt2 10 10 ≡ cnt2 2 2 · cnt2 5 5
crtΓ10 = refl

-- hence the composite index really is ψ(12) = 24 = 6·4 and ψ(10) = 18 = 3·6
idx12 : cnt2 12 1 ≡ 24 · cnt2 12 12
idx12 = refl

idx10 : cnt2 10 1 ≡ 18 · cnt2 10 10
idx10 = refl

-- 4c.  r = 3.  Repeated valuations (blocks of size 2) and, at level 4, three
--      distinct valuations — the first case where the p-power prefactor
--      p^(G−E) is not forced to 1 by the Gaussian multinomial alone.

-- D = diag(1,1,2):  exps (0,0,1),  index [3;2,1]₂ = 7
r3a : cnt3 2 1 1 1 ≡ idxLocal 2 (0 ∷ 0 ∷ 1 ∷ []) · cnt3 2 1 2 2
r3a = refl

-- D = diag(1,2,2):  exps (0,1,1),  index [3;1,2]₂ = 7
r3b : cnt3 2 1 1 1 ≡ idxLocal 2 (0 ∷ 1 ∷ 1 ∷ []) · cnt3 2 2 2 1
r3b = refl

-- same two chains at p = 3:  index 13
r3c : cnt3 3 1 1 1 ≡ idxLocal 3 (0 ∷ 0 ∷ 1 ∷ []) · cnt3 3 1 3 3
r3c = refl

r3d : cnt3 3 1 1 1 ≡ idxLocal 3 (0 ∷ 1 ∷ 1 ∷ []) · cnt3 3 3 3 1
r3d = refl

-- D = diag(1,2,4):  exps (0,1,2), G = 4, E = 3, index = 2·[3;1,1,1]₂ = 2·21 = 42
r3e : cnt3 4 1 1 1 ≡ idxLocal 2 (0 ∷ 1 ∷ 2 ∷ []) · cnt3 4 2 4 2
r3e = refl

-- D = diag(1,1,4):  exps (0,0,2), G = 4, E = 2, index = 4·[3;2,1]₂ = 4·7 = 28
r3f : cnt3 4 1 1 1 ≡ idxLocal 2 (0 ∷ 0 ∷ 2 ∷ []) · cnt3 4 1 4 4
r3f = refl

-- D = diag(1,4,4):  exps (0,2,2), G = 4, E = 2, index = 4·[3;1,2]₂ = 4·7 = 28
r3g : cnt3 4 1 1 1 ≡ idxLocal 2 (0 ∷ 2 ∷ 2 ∷ []) · cnt3 4 4 4 1
r3g = refl

gl3at4 : cnt3 4 1 1 1 ≡ 86016
gl3at4 = refl

idx124 : idxLocal 2 (0 ∷ 1 ∷ 2 ∷ []) ≡ 42
idx124 = refl

idx114 : idxLocal 2 (0 ∷ 0 ∷ 2 ∷ []) ≡ 28
idx114 = refl

-- 4d.  r = 4 at p = 2.  [4;2,2]₂ = 35 is the first Gaussian multinomial in the
--      suite that is not of the form (pʳ−1)/(p−1), so this is the sharpest
--      test of the flag-variety factor.

-- D = diag(1,1,1,2):  exps (0,0,0,1),  index [4;3,1]₂ = 15
r4a : cnt4 2 1 1 1 1 1 1 ≡ idxLocal 2 (0 ∷ 0 ∷ 0 ∷ 1 ∷ []) · cnt4 2 1 1 2 1 2 2
r4a = refl

-- D = diag(1,1,2,2):  exps (0,0,1,1),  index [4;2,2]₂ = 35
r4b : cnt4 2 1 1 1 1 1 1 ≡ idxLocal 2 (0 ∷ 0 ∷ 1 ∷ 1 ∷ []) · cnt4 2 1 2 2 2 2 1
r4b = refl

-- D = diag(1,2,2,2):  exps (0,1,1,1),  index [4;1,3]₂ = 15
r4c : cnt4 2 1 1 1 1 1 1 ≡ idxLocal 2 (0 ∷ 1 ∷ 1 ∷ 1 ∷ []) · cnt4 2 2 2 2 1 1 1
r4c = refl

gl4at2 : cnt4 2 1 1 1 1 1 1 ≡ 20160
gl4at2 = refl

idx1122 : idxLocal 2 (0 ∷ 0 ∷ 1 ∷ 1 ∷ []) ≡ 35
idx1122 = refl

------------------------------------------------------------------------------
-- 5.  Degenerate corner: no p divides the level.  Then every eᵢ is equal, the
--     run-length list is the single block (r), G = E = 0, the Gaussian
--     multinomial is 1, and the index is 1 — i.e. Γ₀(D) = GLᵣ(ℤ).
------------------------------------------------------------------------------

triv2 : idxLocal 2 (0 ∷ 0 ∷ []) ≡ 1
triv2 = refl

triv3 : idxLocal 5 (3 ∷ 3 ∷ 3 ∷ []) ≡ 1
triv3 = refl

-- and the formula depends only on the RATIOS dᵢ/dⱼ, as Γ₀(D) itself does:
shiftInv : idxLocal 2 (0 ∷ 1 ∷ 2 ∷ []) ≡ idxLocal 2 (5 ∷ 6 ∷ 7 ∷ [])
shiftInv = refl

------------------------------------------------------------------------------
-- 6.  Independent cross-check against the classical sublattice count.
--
-- Summing the index over ALL divisor chains of a fixed level p^k must give the
-- total number of sublattices of ℤ^r of index p^k, which is classically
--
--     Σ_{i₁+…+i_r = k}  p^(i₂ + 2i₃ + … + (r−1)i_r)
--
-- (the p-part of ζ(s)ζ(s−1)…ζ(s−r+1)).  That identity is proved by a route
-- entirely disjoint from §4's matrix counting, so agreement is real evidence.
------------------------------------------------------------------------------

subLat2 : ℕ → ℕ → ℕ
subLat2 p k = Σ< (suc k) λ i₂ → pow p i₂

subLat3 : ℕ → ℕ → ℕ
subLat3 p k = Σ< (suc k) λ i₃ → Σ< (suc (k ∸ i₃)) λ i₂ → pow p (i₂ + (2 · i₃))

-- r = 2:  cotypes of index p^k are the chains (e₁ ≤ e₂) with e₁+e₂ = k
cot2k1₂ : idxLocal 2 (0 ∷ 1 ∷ []) ≡ subLat2 2 1
cot2k1₂ = refl

cot2k2₂ : idxLocal 2 (0 ∷ 2 ∷ []) + idxLocal 2 (1 ∷ 1 ∷ []) ≡ subLat2 2 2
cot2k2₂ = refl

cot2k3₂ : idxLocal 2 (0 ∷ 3 ∷ []) + idxLocal 2 (1 ∷ 2 ∷ []) ≡ subLat2 2 3
cot2k3₂ = refl

cot2k3₃ : idxLocal 3 (0 ∷ 3 ∷ []) + idxLocal 3 (1 ∷ 2 ∷ []) ≡ subLat2 3 3
cot2k3₃ = refl

-- r = 3
cot3k1₂ : idxLocal 2 (0 ∷ 0 ∷ 1 ∷ []) ≡ subLat3 2 1
cot3k1₂ = refl

cot3k2₂ : idxLocal 2 (0 ∷ 0 ∷ 2 ∷ []) + idxLocal 2 (0 ∷ 1 ∷ 1 ∷ []) ≡ subLat3 2 2
cot3k2₂ = refl

cot3k3₂ :   idxLocal 2 (0 ∷ 0 ∷ 3 ∷ [])
          + (idxLocal 2 (0 ∷ 1 ∷ 2 ∷ []) + idxLocal 2 (1 ∷ 1 ∷ 1 ∷ []))
          ≡ subLat3 2 3
cot3k3₂ = refl

cot3k3₃ :   idxLocal 3 (0 ∷ 0 ∷ 3 ∷ [])
          + (idxLocal 3 (0 ∷ 1 ∷ 2 ∷ []) + idxLocal 3 (1 ∷ 1 ∷ 1 ∷ []))
          ≡ subLat3 3 3
cot3k3₃ = refl

------------------------------------------------------------------------------
-- 7.  A conjecture, and the kernel's counterexample to it.
--
-- The formula is manifestly invariant under the involution
--     e = (e₁,…,e_r)  ↦  e* = (e_r − e_r, e_r − e_{r−1}, …, e_r − e₁),
-- which is the duality A ↦ w₀ A⁻ᵀ w₀ on Γ₀(D).  One might conjecture that this is the
-- ONLY coincidence: that at fixed r and fixed level p^m, normalised chains with
-- equal index are equal or dual.
--
-- FALSIFIER: any p, r, m and two normalised chains
-- e ≠ e′ with e′ ≠ e* and idxLocal p e ≡ idxLocal p e′.
--
-- REFUTED at r = 3, p = 2, m = 4.  (0,1,4)* = (0,3,4) and (0,2,4)* = (0,2,4),
-- so (0,1,4) and (0,2,4) are not dual — yet both have index 672.
------------------------------------------------------------------------------

dual-invariance : idxLocal 2 (0 ∷ 0 ∷ 4 ∷ []) ≡ idxLocal 2 (0 ∷ 4 ∷ 4 ∷ [])
dual-invariance = refl

conjecture-refuted : idxLocal 2 (0 ∷ 1 ∷ 4 ∷ []) ≡ idxLocal 2 (0 ∷ 2 ∷ 4 ∷ [])
conjecture-refuted = refl

-- and it is not an accident of small numbers: for r = 3 the exponent
-- G = Σ_{i>j}(eᵢ−eⱼ) = Σᵢ (2i−1−r) eᵢ = 2(e₃ − e₁) does not see e₂ at all, so
-- the index at a fixed level takes exactly TWO values — whether the interior
-- valuation is at an endpoint or strictly between.
degeneracy-interior : idxLocal 2 (0 ∷ 1 ∷ 4 ∷ []) ≡ 672
degeneracy-interior = refl

degeneracy-endpoint : idxLocal 2 (0 ∷ 0 ∷ 4 ∷ []) ≡ 448
degeneracy-endpoint = refl

-- same refutation at p = 3, and stable under the shift e ↦ e + c
degeneracy-p3 : idxLocal 3 (0 ∷ 1 ∷ 4 ∷ []) ≡ idxLocal 3 (0 ∷ 2 ∷ 4 ∷ [])
degeneracy-p3 = refl

degeneracy-shifted : idxLocal 3 (2 ∷ 3 ∷ 6 ∷ []) ≡ idxLocal 3 (2 ∷ 4 ∷ 6 ∷ [])
degeneracy-shifted = refl

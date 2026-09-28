{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------------
-- Gamma0IndexExponent : the exponent arithmetic of the Γ₀(D) index formula,
--                       proved for EVERY rank and EVERY divisor chain.
--
-- THE CLASSICAL BACKGROUND.  For r = 2 and D = diag(1,N) the statement below
-- specialises to
--
--     [SL₂(ℤ) : Γ₀(N)]  =  N · ∏_{p ∣ N} (1 + 1/p),
--
-- which is entirely classical and is in every modular-forms text (Shimura,
-- *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, §1.6;
-- Diamond–Shurman, *A First Course in Modular Forms*, 2005, §1.2).  The
-- general-rank version
-- is the cotype-count of Birkhoff (1935) / Chinta–Kaplan–Koplewitz (2017).
-- What is claimed is the CERTIFICATE: the fragment below is a checked term
-- rather than prose or a finite table.
--
-- WHAT `Gamma0Index.agda` ALREADY HAS.  That module is
-- `refl` throughout: every one of its statements fixes a concrete p, a
-- concrete valuation vector and a concrete level, and the kernel enumerates
-- matrices.  Its own header says so ("The verification is corroboration only:
-- the theorem itself is proved in the note").  There is no quantified
-- statement anywhere in it.  In particular
--
--   * `shiftInv` fixes ONE shift of ONE vector at ONE prime;
--   * the eight r = 2 rows fix p^m ∈ {2,3,4,5,7,8,9,11};
--   * the non-negativity of the exponent G − E, asserted in
--     GAMMA0_FLAG_INDEX.md (absent from this repository) §5 ("G_p − E_p = Σ_{u<t} r_u r_t (f_t − f_u − 1)
--     ≥ 0"), has no counterpart in the module at all — yet `idxLocal` is
--     defined as an exact division, so without it the definition is not even
--     known to be the intended integer.
--
-- WHAT THIS MODULE PROVES (all quantified; hypotheses are arguments, not
-- comments):
--
--   §3  split       : pairGaps e ≡ crossPairs e + gapExcess e     [every e]
--   §4  crossE-runLens : Sorted e → crossE (runLens e) ≡ crossPairs e
--   §4  E≤G         : Sorted e → crossE (runLens e) ≤ pairGaps e  [every rank]
--       G−E         : Sorted e → pairGaps e ≡ crossE (runLens e) + gapExcess e
--   §5  idxLocal-shift : ∀ p c e → idxLocal p (shift c e) ≡ idxLocal p e
--   §6  psi-local   : ∀ q m → the r = 2 local factor at p = suc q and level
--                     p^(suc m) equals p^m·(p+1) — i.e. ψ(p^k) = p^{k−1}(p+1),
--                     for EVERY prime power, replacing the eight-row table.
--
-- Non-vacuity controls are §8, in the idiom of Sl2DivisorLattice.agda §5′.
-- Two of them show the `Sorted` hypothesis is load-bearing: on an UNSORTED
-- vector both §4 statements are FALSE, and the module proves their negations.
------------------------------------------------------------------------------
module Gamma0IndexExponent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ; zero; suc; _+_; _·_; _∸_; +-zero; +-suc; +-comm; +-assoc;
         ·-comm; ·-suc; ·-identityˡ; ·-identityʳ; ·-assoc; ·-distribʳ;
         inj-m+; injSuc; discreteℕ; snotz; znots)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ≤-refl; ≤-trans; ≤-suc)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Relation.Nullary using (¬_; yes; no)
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.Bool using (Bool; true; false)

open import Gamma0Index
  using (ite; pow; lenL; sumL; minusAll; pairGaps; runsGo; runLens; crossE;
         qfac; qfacProd; idxLocal)

private
  variable
    v x y c k : ℕ
    xs ys : List ℕ

------------------------------------------------------------------------------
-- §1  A ℕ-valued strict-order indicator, and the "all greater" count.
--
-- `gt x y` is the indicator of x < y.  It is defined by recursion rather than
-- through Bool so that every identity below is available definitionally.
------------------------------------------------------------------------------

gt : ℕ → ℕ → ℕ
gt _       zero    = 0
gt zero    (suc _) = 1
gt (suc a) (suc b) = gt a b

-- Σ_{y ∈ ys} gt x y  — the number of entries of ys strictly above x.
gtAll : ℕ → List ℕ → ℕ
gtAll _ []       = 0
gtAll x (y ∷ ys) = gt x y + gtAll x ys

-- E, counted on PAIRS instead of on runs:  #{ i > j : eⱼ < eᵢ }.
crossPairs : List ℕ → ℕ
crossPairs []       = 0
crossPairs (x ∷ xs) = gtAll x xs + crossPairs xs

-- the pairwise excess  Σ_{i>j} ((eᵢ − eⱼ) − [eⱼ < eᵢ])
excessAll : ℕ → List ℕ → ℕ
excessAll _ []       = 0
excessAll x (y ∷ ys) = ((y ∸ x) ∸ gt x y) + excessAll x ys

gapExcess : List ℕ → ℕ
gapExcess []       = 0
gapExcess (x ∷ xs) = excessAll x xs + gapExcess xs

gt-refl : (a : ℕ) → gt a a ≡ 0
gt-refl zero    = refl
gt-refl (suc a) = gt-refl a

gt-< : (a b : ℕ) → a < b → gt a b ≡ 1
gt-< a zero       h = rec (¬-<-zero h)
  where
    ¬-<-zero : {n : ℕ} → n < zero → ⊥
    ¬-<-zero (j , p) = snotz (sym (+-suc j _) ∙ p)
gt-< zero    (suc b) _ = refl
gt-< (suc a) (suc b) h = gt-< a b (<-unsuc h)
  where
    <-unsuc : {m n : ℕ} → suc m < suc n → m < n
    <-unsuc {m} (j , p) = j , injSuc (sym (+-suc j (suc m)) ∙ p)

------------------------------------------------------------------------------
-- §2  Sortedness, carried as a HYPOTHESIS in every signature that needs it.
------------------------------------------------------------------------------

All≥ : ℕ → List ℕ → Type₀
All≥ _ []       = Unit
All≥ v (x ∷ xs) = (v ≤ x) × All≥ v xs

Sorted : List ℕ → Type₀
Sorted []       = Unit
Sorted (x ∷ xs) = All≥ x xs × Sorted xs

All≥-mono : (a b : ℕ) (zs : List ℕ) → a ≤ b → All≥ b zs → All≥ a zs
All≥-mono a b []       _ _        = tt
All≥-mono a b (z ∷ zs) h (p , ps) = ≤-trans h p , All≥-mono a b zs h ps

-- If every entry is STRICTLY above v then all of them are counted by gtAll.
gtAll-full : (a : ℕ) (zs : List ℕ) → All≥ (suc a) zs → gtAll a zs ≡ lenL zs
gtAll-full a []       _        = refl
gtAll-full a (z ∷ zs) (p , ps) =
  cong₂ _+_ (gt-< a z p) (gtAll-full a zs ps)

------------------------------------------------------------------------------
-- §3  THE PAIRWISE SPLIT.  G = E + (excess), for EVERY vector — no hypothesis.
--
--   pairGaps e = Σ_{i>j} (eᵢ − eⱼ)      is the note's G,
--   crossPairs e = #{ i>j : eⱼ < eᵢ }   is the note's E on pairs (§4 below
--                                        identifies it with Σ_{u<t} r_u r_t),
--   gapExcess e = Σ_{i>j} ((eᵢ−eⱼ) − 1) over the pairs that contribute.
------------------------------------------------------------------------------

gt-split : (a b : ℕ) → (b ∸ a) ≡ gt a b + ((b ∸ a) ∸ gt a b)
gt-split zero    zero    = refl
gt-split zero    (suc b) = refl
gt-split (suc a) zero    = refl
gt-split (suc a) (suc b) = gt-split a b

minusAll-split : (a : ℕ) (zs : List ℕ)
               → minusAll a zs ≡ gtAll a zs + excessAll a zs
minusAll-split a []       = refl
minusAll-split a (z ∷ zs) =
    cong₂ _+_ (gt-split a z) (minusAll-split a zs)
  ∙ shuffle (gt a z) ((z ∸ a) ∸ gt a z) (gtAll a zs) (excessAll a zs)
  where
    shuffle : (p q s t : ℕ) → (p + q) + (s + t) ≡ (p + s) + (q + t)
    shuffle p q s t =
        sym (+-assoc p q (s + t))
      ∙ cong (p +_) (+-assoc q s t ∙ cong (_+ t) (+-comm q s) ∙ sym (+-assoc s q t))
      ∙ +-assoc p s (q + t)

-- Theorem (every rank, every vector, sorted or not).
split : (e : List ℕ) → pairGaps e ≡ crossPairs e + gapExcess e
split []       = refl
split (x ∷ xs) =
    cong₂ _+_ (minusAll-split x xs) (split xs)
  ∙ shuffle (gtAll x xs) (excessAll x xs) (crossPairs xs) (gapExcess xs)
  where
    shuffle : (p q s t : ℕ) → (p + q) + (s + t) ≡ (p + s) + (q + t)
    shuffle p q s t =
        sym (+-assoc p q (s + t))
      ∙ cong (p +_) (+-assoc q s t ∙ cong (_+ t) (+-comm q s) ∙ sym (+-assoc s q t))
      ∙ +-assoc p s (q + t)

------------------------------------------------------------------------------
-- §4  THE RUN IDENTIFICATION.  Σ_{u<t} r_u r_t (over the run-length list of a
--     SORTED vector) equals the pair count of §1.  This is the step where
--     sortedness is genuinely used, and §8 exhibits a vector where dropping it
--     makes the statement false.
------------------------------------------------------------------------------

==-refl : (a : ℕ) → (a == a) ≡ true
==-refl zero    = refl
==-refl (suc a) = ==-refl a

==-false : (a b : ℕ) → ¬ (a ≡ b) → (a == b) ≡ false
==-false zero    zero    ne = rec (ne refl)
==-false zero    (suc b) _  = refl
==-false (suc a) zero    _  = refl
==-false (suc a) (suc b) ne = ==-false a b (λ p → ne (cong suc p))

runsGo-eq : (a k : ℕ) (b : ℕ) (zs : List ℕ) → a ≡ b
          → runsGo a k (b ∷ zs) ≡ runsGo a (suc k) zs
runsGo-eq a k b zs p =
    (λ i → runsGo a k (p (~ i) ∷ zs))
  ∙ cong (λ t → ite t (runsGo a (suc k) zs) (k ∷ runsGo a 1 zs)) (==-refl a)

runsGo-neq : (a k : ℕ) (b : ℕ) (zs : List ℕ) → ¬ (a ≡ b)
           → runsGo a k (b ∷ zs) ≡ k ∷ runsGo b 1 zs
runsGo-neq a k b zs ne =
  cong (λ t → ite t (runsGo a (suc k) zs) (k ∷ runsGo b 1 zs)) (==-false a b ne)

-- The run lengths sum to the vector length (no hypothesis).
sumL-runsGo : (a k : ℕ) (zs : List ℕ) → sumL (runsGo a k zs) ≡ k + lenL zs
sumL-runsGo a k []       = refl
sumL-runsGo a k (z ∷ zs) with discreteℕ a z
... | yes p =
        cong sumL (runsGo-eq a k z zs p)
      ∙ sumL-runsGo a (suc k) zs
      ∙ sym (+-suc k (lenL zs))
... | no ne =
        cong sumL (runsGo-neq a k z zs ne)
      ∙ cong (k +_) (sumL-runsGo z 1 zs)

-- THE KEY LEMMA, with both hypotheses in the signature.
runsGo-crossE : (a k : ℕ) (zs : List ℕ) → All≥ a zs → Sorted zs
              → crossE (runsGo a k zs) ≡ k · gtAll a zs + crossPairs zs
runsGo-crossE a k []       _        _        = refl
runsGo-crossE a k (z ∷ zs) (le , as) (bs , ss) with discreteℕ a z
... | yes p =
        cong crossE (runsGo-eq a k z zs p)
      ∙ runsGo-crossE a (suc k) zs as ss
      ∙ sym step
  where
    -- gt a z = 0 because a ≡ z
    gtaz : gt a z ≡ 0
    gtaz = cong (gt a) (sym p) ∙ gt-refl a
    step : k · gtAll a (z ∷ zs) + crossPairs (z ∷ zs)
         ≡ suc k · gtAll a zs + crossPairs zs
    step =
        cong (λ t → k · (t + gtAll a zs) + (gtAll z zs + crossPairs zs)) gtaz
      ∙ cong (λ t → k · t + (gtAll z zs + crossPairs zs)) refl
      ∙ cong (λ t → k · gtAll a zs + (t + crossPairs zs))
             (cong (λ w → gtAll w zs) (sym p))
      ∙ +-assoc (k · gtAll a zs) (gtAll a zs) (crossPairs zs)
      ∙ cong (_+ crossPairs zs) (+-comm (k · gtAll a zs) (gtAll a zs))
... | no ne =
        cong crossE (runsGo-neq a k z zs ne)
      ∙ cong (λ t → k · t + crossE (runsGo z 1 zs)) (sumL-runsGo z 1 zs)
      ∙ cong (λ t → k · (1 + lenL zs) + t) (runsGo-crossE z 1 zs bs ss)
      ∙ sym step
  where
    a<z : a < z
    a<z = ≤-≢→< le (λ p → ne p)
      where
        ≤-≢→< : {m n : ℕ} → m ≤ n → ¬ (m ≡ n) → m < n
        ≤-≢→< {m} {n} (zero  , q) nq = rec (nq q)
        ≤-≢→< {m} {n} (suc l , q) nq = l , +-suc l m ∙ q
    lens : gtAll a zs ≡ lenL zs
    lens = gtAll-full a zs (All≥-mono (suc a) z zs a<z bs)
    step : k · gtAll a (z ∷ zs) + crossPairs (z ∷ zs)
         ≡ k · (1 + lenL zs) + (1 · gtAll z zs + crossPairs zs)
    step =
        cong (λ t → k · (t + gtAll a zs) + (gtAll z zs + crossPairs zs))
             (gt-< a z a<z)
      ∙ cong (λ t → k · (1 + t) + (gtAll z zs + crossPairs zs)) lens
      ∙ cong (λ t → k · (1 + lenL zs) + (t + crossPairs zs))
             (sym (·-identityˡ (gtAll z zs)))

-- THEOREM (every rank).  On a sorted valuation vector the run-length cross
-- term Σ_{u<t} r_u r_t is exactly the number of strictly increasing pairs.
crossE-runLens : (e : List ℕ) → Sorted e → crossE (runLens e) ≡ crossPairs e
crossE-runLens []       _        = refl
crossE-runLens (x ∷ xs) (bs , ss) =
    runsGo-crossE x 1 xs bs ss
  ∙ cong (_+ crossPairs xs) (·-identityˡ (gtAll x xs))

-- THEOREM (every rank).  The exact form of GAMMA0_FLAG_INDEX.md (absent from this repository) §5:
--     G  =  E + Σ_{u<t} r_u r_t (f_t − f_u − 1).
G≡E+excess : (e : List ℕ) → Sorted e
           → pairGaps e ≡ crossE (runLens e) + gapExcess e
G≡E+excess e s = split e ∙ cong (_+ gapExcess e) (sym (crossE-runLens e s))

-- COROLLARY (every rank).  The exponent of the closed form is non-negative,
-- so `idxLocal`'s division by p^E really is a division of a p-power by a
-- smaller one.  This is the assertion §5 of the note makes without proof.
E≤G : (e : List ℕ) → Sorted e → crossE (runLens e) ≤ pairGaps e
E≤G e s = gapExcess e , +-comm (gapExcess e) (crossE (runLens e))
                        ∙ sym (G≡E+excess e s)

------------------------------------------------------------------------------
-- §5  SHIFT INVARIANCE, for every shift, every vector, every p.
--
-- Γ₀(D) depends only on the ratios dᵢ/dⱼ (note §1); the closed form must
-- therefore be invariant under eᵢ ↦ eᵢ + c.  `Gamma0Index.shiftInv` checks
-- ONE instance by `refl`.  Here it is a theorem.
------------------------------------------------------------------------------

shift : ℕ → List ℕ → List ℕ
shift _ []       = []
shift c (x ∷ xs) = (c + x) ∷ shift c xs

∸-shift : (c a b : ℕ) → (c + b) ∸ (c + a) ≡ b ∸ a
∸-shift zero    a b = refl
∸-shift (suc c) a b = ∸-shift c a b

lenL-shift : (c : ℕ) (e : List ℕ) → lenL (shift c e) ≡ lenL e
lenL-shift c []       = refl
lenL-shift c (x ∷ xs) = cong suc (lenL-shift c xs)

minusAll-shift : (c a : ℕ) (zs : List ℕ)
               → minusAll (c + a) (shift c zs) ≡ minusAll a zs
minusAll-shift c a []       = refl
minusAll-shift c a (z ∷ zs) =
  cong₂ _+_ (∸-shift c a z) (minusAll-shift c a zs)

pairGaps-shift : (c : ℕ) (e : List ℕ) → pairGaps (shift c e) ≡ pairGaps e
pairGaps-shift c []       = refl
pairGaps-shift c (x ∷ xs) =
  cong₂ _+_ (minusAll-shift c x xs) (pairGaps-shift c xs)

runsGo-shift : (c a k : ℕ) (zs : List ℕ)
             → runsGo (c + a) k (shift c zs) ≡ runsGo a k zs
runsGo-shift c a k []       = refl
runsGo-shift c a k (z ∷ zs) with discreteℕ a z
... | yes p =
        runsGo-eq (c + a) k (c + z) (shift c zs) (cong (c +_) p)
      ∙ runsGo-shift c a (suc k) zs
      ∙ sym (runsGo-eq a k z zs p)
... | no ne =
        runsGo-neq (c + a) k (c + z) (shift c zs) (λ q → ne (inj-m+ q))
      ∙ cong (k ∷_) (runsGo-shift c z 1 zs)
      ∙ sym (runsGo-neq a k z zs ne)

runLens-shift : (c : ℕ) (e : List ℕ) → runLens (shift c e) ≡ runLens e
runLens-shift c []       = refl
runLens-shift c (x ∷ xs) = runsGo-shift c x 1 xs

-- THEOREM.  The predicted local index is shift-invariant, in full generality.
idxLocal-shift : (p c : ℕ) (e : List ℕ) → idxLocal p (shift c e) ≡ idxLocal p e
idxLocal-shift p c e i =
  ((pow p (pairGaps-shift c e i) · qfac p (lenL-shift c e i))
     Gamma0Index.// (pow p (crossE (runLens-shift c e i))
                      · qfacProd p (runLens-shift c e i)))

------------------------------------------------------------------------------
-- §6  THE r = 2 LOCAL FACTOR, for EVERY prime p and EVERY exponent.
--
-- This is the classical [SL₂(ℤ):Γ₀(N)] local factor ψ(p^k) = p^{k−1}(p+1)
-- (Shimura Prop. 1.43; Diamond–Shurman Ex. 1.2.11).  `Gamma0Index` checks
-- eight instances by `refl`; here it is proved for all of them at once.
--
-- The statement is MULTIPLICATIVE, not a division: it says
--
--     p^G · [numerator of the Gaussian binomial]
--        ≡ (p^{k−1}(p+1)) · p^E · [denominator],
--
-- which is strictly stronger than the quotient form because it does not
-- presuppose that the division is exact.
------------------------------------------------------------------------------

numer : ℕ → List ℕ → ℕ
numer p e = pow p (pairGaps e) · qfac p (lenL e)

denom : ℕ → List ℕ → ℕ
denom p e = pow p (crossE (runLens e)) · qfacProd p (runLens e)

-- (p² − 1) = q(p+1) when p = suc q — the only ∸ fact needed.
sq∸1 : (q : ℕ) → (suc q · (suc q · 1)) ∸ 1 ≡ q · suc (suc q)
sq∸1 q =
    cong (λ t → (suc q · t) ∸ 1) (·-identityʳ (suc q))
  ∙ cong (_∸ 1) (·-suc (suc q) q)
  ∙ sym (·-suc q (suc q) ∙ cong (q +_) (·-suc q q))

-- The two q-factorials that occur at r = 2, in closed form.
qfac-1 : (q : ℕ) → qfac (suc q) 1 ≡ q
qfac-1 q = cong (λ t → (t ∸ 1) · 1) (·-identityʳ (suc q)) ∙ ·-identityʳ q

qfac-2 : (q : ℕ) → qfac (suc q) 2 ≡ (q · suc (suc q)) · q
qfac-2 q = cong₂ _·_ (sq∸1 q) (qfac-1 q)

-- G for the chain diag(1, p^{k}) is k.
pairGaps-r2 : (m : ℕ) → pairGaps (0 ∷ suc m ∷ []) ≡ suc m
pairGaps-r2 m = +-zero (suc m + 0) ∙ +-zero (suc m)

numer-r2 : (q m : ℕ)
         → numer (suc q) (0 ∷ suc m ∷ [])
         ≡ pow (suc q) (suc m) · ((q · suc (suc q)) · q)
numer-r2 q m =
  cong₂ _·_ (cong (pow (suc q)) (pairGaps-r2 m)) (qfac-2 q)

-- E = 1 and the run lengths are (1,1), so the denominator is p·(p−1)².
denom-r2 : (q m : ℕ) → denom (suc q) (0 ∷ suc m ∷ []) ≡ suc q · (q · q)
denom-r2 q m =
  cong₂ _·_ (·-identityʳ (suc q))
            (cong₂ _·_ (qfac-1 q)
                       (cong (_· 1) (qfac-1 q) ∙ ·-identityʳ q))

-- THEOREM.  For every p = suc q ≥ 1 and every k = suc m ≥ 1, the r = 2 local
-- factor of the divisor chain diag(1, p^k) is p^{k−1}(p + 1).
psi-local : (q m : ℕ)
          → numer (suc q) (0 ∷ suc m ∷ [])
          ≡ (pow (suc q) m · suc (suc q)) · denom (suc q) (0 ∷ suc m ∷ [])
psi-local q m =
    numer-r2 q m
  ∙ norm (suc q) (pow (suc q) m) q (suc (suc q))
  ∙ cong ((pow (suc q) m · suc (suc q)) ·_) (sym (denom-r2 q m))
  where
        -- (p·P)·((q·S)·q) ≡ (P·S)·(p·(q·q)) : pure commutative-monoid algebra
        norm : (a b d s : ℕ) → (a · b) · ((d · s) · d) ≡ (b · s) · (a · (d · d))
        norm a b d s =
          (a · b) · ((d · s) · d)
            ≡⟨ cong ((a · b) ·_)
                 (cong (_· d) (·-comm d s) ∙ sym (·-assoc s d d)) ⟩
          (a · b) · (s · (d · d))
            ≡⟨ cong (_· (s · (d · d))) (·-comm a b) ⟩
          (b · a) · (s · (d · d))
            ≡⟨ sym (·-assoc b a (s · (d · d))) ⟩
          b · (a · (s · (d · d)))
            ≡⟨ cong (b ·_) (·-assoc a s (d · d)) ⟩
          b · ((a · s) · (d · d))
            ≡⟨ cong (λ t → b · (t · (d · d))) (·-comm a s) ⟩
          b · ((s · a) · (d · d))
            ≡⟨ cong (b ·_) (sym (·-assoc s a (d · d))) ⟩
          b · (s · (a · (d · d)))
            ≡⟨ ·-assoc b s (a · (d · d)) ⟩
          (b · s) · (a · (d · d)) ∎

------------------------------------------------------------------------------
-- §8  CONTROLS.  Six `refl`/negation controls, in the idiom of
--     Sl2DivisorLattice.agda §5′: the theorems above must not be satisfiable
--     by degenerate data.
------------------------------------------------------------------------------

module Controls where

  -- (1)  The counted quantities are not identically zero.
  control-crossPairs : crossPairs (0 ∷ 1 ∷ 3 ∷ []) ≡ 3
  control-crossPairs = refl

  control-pairGaps : pairGaps (0 ∷ 1 ∷ 3 ∷ []) ≡ 6
  control-pairGaps = refl

  -- (2)  The excess is not identically zero either, so `split` is not the
  --      trivial identity G = E + 0 in disguise.
  control-excess : gapExcess (0 ∷ 1 ∷ 3 ∷ []) ≡ 3
  control-excess = refl

  -- (3)  … and it IS zero when no two distinct valuations are further than a
  --      single step apart, which is the equality case E = G of `E≤G`.
  control-excess-tight : gapExcess (0 ∷ 0 ∷ 1 ∷ []) ≡ 0
  control-excess-tight = refl

  control-equality-case : crossE (runLens (0 ∷ 0 ∷ 1 ∷ []))
                        ≡ pairGaps (0 ∷ 0 ∷ 1 ∷ [])
  control-equality-case = refl

  -- (4)  SORTEDNESS IS LOAD-BEARING.  On the unsorted vector (1,0) the run
  --      decomposition sees two runs, but there is no increasing pair; so
  --      `crossE-runLens` is FALSE without its hypothesis.
  control-sorted-needed
    : ¬ (crossE (runLens (1 ∷ 0 ∷ [])) ≡ crossPairs (1 ∷ 0 ∷ []))
  control-sorted-needed h = snotz h

  -- (5)  … and so is `E≤G`: on (1,0) the exponent G − E would be negative.
  control-E≤G-needs-sorted
    : ¬ (crossE (runLens (1 ∷ 0 ∷ [])) ≡ pairGaps (1 ∷ 0 ∷ []))
  control-E≤G-needs-sorted h = snotz h

  -- (6)  `psi-local` is not vacuous: at p = 3, k = 2 it asserts 12 = ψ(9),
  --      matching `Gamma0Index.ψ9`, and the two sides are genuinely unequal
  --      numbers before the theorem is applied.
  control-psi-9 : numer 3 (0 ∷ 2 ∷ []) ≡ 12 · denom 3 (0 ∷ 2 ∷ [])
  control-psi-9 = psi-local 2 1

  control-psi-8 : numer 2 (0 ∷ 3 ∷ []) ≡ 12 · denom 2 (0 ∷ 3 ∷ [])
  control-psi-8 = psi-local 1 2

  -- and the shift theorem reproduces `Gamma0Index.shiftInv` as an instance
  control-shift : idxLocal 2 (5 ∷ 6 ∷ 7 ∷ []) ≡ idxLocal 2 (0 ∷ 1 ∷ 2 ∷ [])
  control-shift = idxLocal-shift 2 5 (0 ∷ 1 ∷ 2 ∷ [])

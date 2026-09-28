{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- The second half of notes/WALK_INSTALLS_ARE_JUMPS.md (absent from this repository) §(c): the
-- direction (⇐), that a PRIME POWER is a jump point of the capacity
-- function.
--
--   q = p^a  (p prime, a ≥ 1)  ⟹  q ∤ lcm(1 .. q−1).
--
-- `IsPrime` is defined here (cubical v0.5 has no primality anywhere in the
-- library).  Primality of a given numeral is therefore a proof obligation;
-- `isPrime2` and `isPrime3` discharge it for 2 and 3 by finite case
-- analysis; `NaturalMachine.PrimalityDecision.decIsPrime` decides
-- primality in general.
--
-- METHOD, and why no p-adic valuation appears.  A valuation function
-- v_p : ℕ → ℕ is painful in cubical v0.5 (no well-founded division, no
-- decidable divisibility in the library).  It is also unnecessary.  The
-- statement is proved instead by the lcm UNIVERSAL PROPERTY, in the
-- house style of WalkCapacity and WalkStream: to show p^a does not
-- divide the lcm C of [1 .. p^a−1] it suffices to EXHIBIT one common
-- multiple M of that range with p^a ∤ M, because C ∣ M.  The witness is
-- built by induction on the range:
--
--     M = p^(a−1) · V   with   p ∤ V,
--
-- where V accumulates the p-free parts of 1, 2, …, p^a−1.  Then
-- p^a ∣ M would cancel to p ∣ V.  So the only genuinely arithmetic
-- ingredients are (i) Euclid's lemma, obtained gcd-side without Bezout
-- exactly as in WalkForcing (gcd-factorʳ plus the gcd universal
-- property), and (ii) the p-free decomposition j = p^e · u, p ∤ u,
-- produced by a fuel recursion whose case split is supplied by primality
-- itself -- `prime-alt` below turns "p ∣ d or gcd(p,d) = 1" into a
-- constructive disjunction, so no decidability of ∣ is needed anywhere.
--
-- Predicates are recursive type families, and no constructor is matched
-- in an index position, per the constraints recorded in WalkCapacity.

module NaturalMachine.WalkJumps where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.WalkCapacity

------------------------------------------------------------------------
-- Primality (absent from cubical v0.5 entirely)
------------------------------------------------------------------------

-- p is prime: p > 1 and its only divisors are 1 and p.
IsPrime : ℕ → Type
IsPrime p = (1 < p) × ((d : ℕ) → d ∣ p → (d ≡ 1) ⊎ (d ≡ p))

prime-0<  : (p : ℕ) → IsPrime p → 0 < p
prime-0< p pr = ≤-trans ≤-sucℕ (pr .fst)

prime-¬∣1 : (p : ℕ) → IsPrime p → ¬ (p ∣ 1)
prime-¬∣1 p pr p∣1 = ¬m<m (<≤-trans (pr .fst) (m∣sn→m≤sn p∣1))

------------------------------------------------------------------------
-- Small arithmetic helpers
------------------------------------------------------------------------

0<· : (m n : ℕ) → 0 < m → 0 < n → 0 < m · n
0<· zero    n       0<m 0<n = Empty.rec (¬-<-zero 0<m)
0<· (suc m) zero    0<m 0<n = Empty.rec (¬-<-zero 0<n)
0<· (suc m) (suc n) 0<m 0<n = suc-≤-suc zero-≤

pos→suc : (m : ℕ) → 0 < m → Σ[ t ∈ ℕ ] m ≡ suc t
pos→suc m (k , k+1≡m) = k , sym k+1≡m ∙ +-comm k 1

-- a positive multiple of something > 1 strictly exceeds it
lt-self : (c p : ℕ) → 0 < c → 1 < p → c < c · p
lt-self zero    p 0<c 1<p = Empty.rec (¬-<-zero 0<c)
lt-self (suc c) p 0<c 1<p =
  subst2 _<_ (·-identityˡ (suc c)) (·-comm p (suc c)) (<-·sk 1<p)

-- divisibility multiplies componentwise
∣-·-comb : {a b c d : ℕ} → a ∣ c → b ∣ d → (a · b) ∣ (c · d)
∣-·-comb {a} {b} {c} {d} a∣c b∣d =
  ∣-trans (∣-multʳ b a∣c)
          (subst2 _∣_ (·-comm b c) (·-comm d c) (∣-multʳ c b∣d))

------------------------------------------------------------------------
-- Powers
------------------------------------------------------------------------

^-+ : (p k e : ℕ) → p ^ (k + e) ≡ (p ^ k) · (p ^ e)
^-+ p zero    e = sym (·-identityˡ (p ^ e))
^-+ p (suc k) e = cong (p ·_) (^-+ p k e) ∙ ·-assoc p (p ^ k) (p ^ e)

^-∣-mono : (p e f : ℕ) → e ≤ f → (p ^ e) ∣ (p ^ f)
^-∣-mono p e f (k , k+e≡f) =
  subst ((p ^ e) ∣_) (cong (p ^_) k+e≡f)
    (subst ((p ^ e) ∣_) (sym (^-+ p k e)) (∣-right (p ^ k)))

^-pos : (p e : ℕ) → 0 < p → 0 < p ^ e
^-pos p zero    0<p = ≤-refl
^-pos p (suc e) 0<p = 0<· p (p ^ e) 0<p (^-pos p e 0<p)

0<→≢0 : (n : ℕ) → 0 < n → ¬ (n ≡ 0)
0<→≢0 n 0<n n≡0 = ¬-<-zero (subst (0 <_) n≡0 0<n)

^-≤-mono : (p e f : ℕ) → 0 < p → e ≤ f → (p ^ e) ≤ (p ^ f)
^-≤-mono p e f 0<p e≤f =
  m∣n→m≤n (0<→≢0 (p ^ f) (^-pos p f 0<p)) (^-∣-mono p e f e≤f)

-- exponents reflect the order: p^e < p^a forces e < a
^-reflect-< : (p e a : ℕ) → 0 < p → (p ^ e) < (p ^ a) → e < a
^-reflect-< p e a 0<p h with splitℕ-≤ a e
... | inl a≤e = Empty.rec (<-asym h (^-≤-mono p a e 0<p a≤e))
... | inr e<a = e<a

------------------------------------------------------------------------
-- Euclid's lemma, gcd-side (no Bezout), as in WalkForcing
------------------------------------------------------------------------

-- coprime cancellation: gcd(a,b)=1 and a ∣ b·c give a ∣ c.
-- Proof: gcd(ac, bc) = gcd(a,b)·c = c, and a is a common divisor of
-- ac and bc, hence divides that gcd.
coprime-cancel : (a b c : ℕ) → isGCD a b 1 → a ∣ (b · c) → a ∣ c
coprime-cancel a b c g a∣bc =
  subst (a ∣_) gac≡c (gcdIsGCD (a · c) (b · c) .snd a (∣-left c , a∣bc))
  where
  gac≡c : gcd (a · c) (b · c) ≡ c
  gac≡c = gcd-factorʳ a b c ∙ cong (_· c) (isGCD→gcd≡ g) ∙ ·-identityˡ c

-- PRIMALITY AS A CONSTRUCTIVE DISJUNCTION.  For every d, either p ∣ d
-- or p and d are coprime.  This is what replaces decidability of
-- divisibility everywhere below: gcd p d divides p, so by primality it
-- IS 1 or IS p, and no decision procedure is invoked.
prime-alt : (p : ℕ) → IsPrime p → (d : ℕ) → (p ∣ d) ⊎ (isGCD p d 1)
prime-alt p pr d with pr .snd (gcd p d) (gcdIsGCD p d .fst .fst)
... | inl g≡1 = inr (subst (isGCD p d) g≡1 (gcdIsGCD p d))
... | inr g≡p = inl (subst (_∣ d) g≡p (gcdIsGCD p d .fst .snd))

coprime→¬∣ : (p d : ℕ) → IsPrime p → isGCD p d 1 → ¬ (p ∣ d)
coprime→¬∣ p d pr g p∣d = prime-¬∣1 p pr (g .snd p (∣-refl refl , p∣d))

-- Euclid's lemma proper.
prime-∣-· : (p x y : ℕ) → IsPrime p → p ∣ (x · y) → (p ∣ x) ⊎ (p ∣ y)
prime-∣-· p x y pr p∣xy with prime-alt p pr x
... | inl p∣x = inl p∣x
... | inr g   = inr (coprime-cancel p x y g p∣xy)

------------------------------------------------------------------------
-- The p-free decomposition j = p^e · u with p ∤ u
------------------------------------------------------------------------

Strip : ℕ → ℕ → Type
Strip p j =
  Σ[ e ∈ ℕ ] Σ[ u ∈ ℕ ]
    (0 < u) × (((p ^ e) · u) ≡ j) × (¬ (p ∣ u))

-- Fuel recursion; the case split is `prime-alt`, so divisibility never
-- has to be decided.
strip : (p : ℕ) → IsPrime p → (fuel j : ℕ) → 0 < j → j ≤ fuel → Strip p j
strip p pr zero    j 0<j j≤f = Empty.rec (¬-<-zero (<≤-trans 0<j j≤f))
strip p pr (suc f) j 0<j j≤f with prime-alt p pr j
... | inr g    = 0 , j , 0<j , ·-identityˡ j , coprime→¬∣ p j pr g
... | inl p∣j with ∣-untrunc p∣j
...   | (zero  , e0) = Empty.rec (¬-<-zero (subst (0 <_) (sym e0) 0<j))
...   | (suc c , ec) =
        suc (r .fst) , r .snd .fst , r .snd .snd .fst , pf
        , r .snd .snd .snd .snd
  where
  0<sc : 0 < suc c
  0<sc = suc-≤-suc zero-≤

  sc<j : suc c < j
  sc<j = subst (suc c <_) ec (lt-self (suc c) p 0<sc (pr .fst))

  sc≤f : suc c ≤ f
  sc≤f = pred-≤-pred (<≤-trans sc<j j≤f)

  r : Strip p (suc c)
  r = strip p pr f (suc c) 0<sc sc≤f

  pf : ((p ^ suc (r .fst)) · (r .snd .fst)) ≡ j
  pf = sym (·-assoc p (p ^ (r .fst)) (r .snd .fst))
       ∙ cong (p ·_) (r .snd .snd .snd .fst)
       ∙ ·-comm p (suc c)
       ∙ ec

------------------------------------------------------------------------
-- The witness: a common multiple of [1..k] of the form p^b · V, p ∤ V
------------------------------------------------------------------------

CM-mono : (xs : List ℕ) (M N : ℕ) →
          M ∣ N → CommonMultiple xs M → CommonMultiple xs N
CM-mono []       M N M∣N _        = tt
CM-mono (x ∷ xs) M N M∣N (h , hs) = ∣-trans h M∣N , CM-mono xs M N M∣N hs

JumpWitness : ℕ → ℕ → ℕ → Type
JumpWitness p b k =
  Σ[ V ∈ ℕ ]
    (0 < V) × (¬ (p ∣ V)) × CommonMultiple (range1 k) ((p ^ b) · V)

-- THE CONSTRUCTION.  For every k below p^(b+1) there is a common
-- multiple of [1..k] whose p-part is exactly p^b: V accumulates the
-- p-free parts of the range, and the exponent of every member is ≤ b
-- because p^e ∣ j ≤ k < p^(b+1).
build : (p : ℕ) → IsPrime p → (b k : ℕ) → k < p ^ suc b → JumpWitness p b k
build p pr b zero    _     = 1 , ≤-refl , prime-¬∣1 p pr , tt
build p pr b (suc k) sk<pa =
  (V · u) , 0<Vu , ¬p∣Vu , (headDiv , tailDiv)
  where
  0<p : 0 < p
  0<p = prime-0< p pr

  ih : JumpWitness p b k
  ih = build p pr b k (<-trans ≤-refl sk<pa)

  V     = ih .fst
  0<V   = ih .snd .fst
  ¬p∣V  = ih .snd .snd .fst
  cmV   = ih .snd .snd .snd

  st : Strip p (suc k)
  st = strip p pr (suc k) (suc k) (suc-≤-suc zero-≤) ≤-refl

  e     = st .fst
  u     = st .snd .fst
  0<u   = st .snd .snd .fst
  peu   = st .snd .snd .snd .fst
  ¬p∣u  = st .snd .snd .snd .snd

  pe∣sk : (p ^ e) ∣ suc k
  pe∣sk = subst ((p ^ e) ∣_) peu (∣-left u)

  e≤b : e ≤ b
  e≤b = pred-≤-pred
          (^-reflect-< p e (suc b) 0<p
            (≤<-trans (m∣n→m≤n snotz pe∣sk) sk<pa))

  0<Vu : 0 < V · u
  0<Vu = 0<· V u 0<V 0<u

  ¬p∣Vu : ¬ (p ∣ (V · u))
  ¬p∣Vu h with prime-∣-· p V u pr h
  ... | inl x = ¬p∣V x
  ... | inr y = ¬p∣u y

  headDiv : suc k ∣ ((p ^ b) · (V · u))
  headDiv = subst (_∣ ((p ^ b) · (V · u))) peu
              (∣-·-comb (^-∣-mono p e b e≤b) (∣-right V))

  step∣ : ((p ^ b) · V) ∣ ((p ^ b) · (V · u))
  step∣ = subst (((p ^ b) · V) ∣_) (sym (·-assoc (p ^ b) V u)) (∣-left u)

  tailDiv : CommonMultiple (range1 k) ((p ^ b) · (V · u))
  tailDiv = CM-mono (range1 k) ((p ^ b) · V) ((p ^ b) · (V · u)) step∣ cmV

------------------------------------------------------------------------
-- THE THEOREM: a prime power is not covered by the numbers below it
------------------------------------------------------------------------

-- For p prime and a = b+1 ≥ 1: if suc n = p^a (so n = p^a − 1) and C is
-- ANY lcm of the frontier range [1..n], then p^a ∤ C.  Stated by
-- universal property, so no lcm construction is needed.
prime-power-not-covered :
  (p b n C : ℕ) → IsPrime p → suc n ≡ p ^ suc b →
  IsLCM (range1 n) C →
  ¬ ((p ^ suc b) ∣ C)
prime-power-not-covered p b n C pr sn≡ (_ , C-least) pa∣C = ¬p∣V p∣V
  where
  0<p : 0 < p
  0<p = prime-0< p pr

  w : JumpWitness p b n
  w = build p pr b n (subst (n <_) sn≡ ≤-refl)

  V     = w .fst
  ¬p∣V  = w .snd .snd .fst
  cm    = w .snd .snd .snd

  pa∣M : (p ^ suc b) ∣ ((p ^ b) · V)
  pa∣M = ∣-trans pa∣C (C-least ((p ^ b) · V) cm)

  ps : Σ[ t ∈ ℕ ] (p ^ b) ≡ suc t
  ps = pos→suc (p ^ b) (^-pos p b 0<p)

  p∣V : p ∣ V
  p∣V = ∣-cancelʳ (ps .fst)
          (subst2 _∣_ (cong (p ·_) (ps .snd))
                      (·-comm (p ^ b) V ∙ cong (V ·_) (ps .snd))
                      pa∣M)

-- Corollary: the a = 1 case,
-- covering every prime install.
prime-not-covered :
  (p n C : ℕ) → IsPrime p → suc n ≡ p →
  IsLCM (range1 n) C →
  ¬ (p ∣ C)
prime-not-covered p n C pr sn≡p lcmC p∣C =
  prime-power-not-covered p 0 n C pr (sn≡p ∙ sym (·-identityʳ p)) lcmC
    (subst (_∣ C) (sym (·-identityʳ p)) p∣C)

------------------------------------------------------------------------
-- The capacity really jumps there (note §(a), the jump-point reading)
------------------------------------------------------------------------

-- cap(p^a − 1) ≠ cap(p^a): the lcm of [1..p^a−1] and the lcm of
-- [1..p^a] are different numbers.  This is the sense in which p^a is a
-- JUMP POINT of the capacity function.
prime-power-jumps-capacity :
  (p b n C D : ℕ) → IsPrime p → suc n ≡ p ^ suc b →
  IsLCM (range1 n) C → IsLCM (range1 (suc n)) D →
  ¬ (C ≡ D)
prime-power-jumps-capacity p b n C D pr sn≡ lcmC (D-common , _) C≡D =
  prime-power-not-covered p b n C pr sn≡ lcmC
    (subst ((p ^ suc b) ∣_) (sym C≡D) (subst (_∣ D) sn≡ (D-common .fst)))

------------------------------------------------------------------------
-- The theorem fired on concrete prime powers
------------------------------------------------------------------------

isPrime2 : IsPrime 2
isPrime2 = suc-≤-suc (suc-≤-suc zero-≤) , div2
  where
  div2 : (d : ℕ) → d ∣ 2 → (d ≡ 1) ⊎ (d ≡ 2)
  div2 zero                p = Empty.rec (znots (∣-zeroˡ p))
  div2 (suc zero)          p = inl refl
  div2 (suc (suc zero))    p = inr refl
  div2 (suc (suc (suc d))) p =
    Empty.rec (¬-<-zero (pred-≤-pred (pred-≤-pred (m∣sn→m≤sn p))))

¬2∣3 : ¬ (2 ∣ 3)
¬2∣3 p = h (∣-untrunc p)
  where
  h : Σ[ c ∈ ℕ ] c · 2 ≡ 3 → ⊥
  h (zero          , e) = znots e
  h (suc zero      , e) = znots (injSuc (injSuc e))
  h (suc (suc c)   , e) = snotz (injSuc (injSuc (injSuc e)))

isPrime3 : IsPrime 3
isPrime3 = suc-≤-suc (suc-≤-suc zero-≤) , div3
  where
  div3 : (d : ℕ) → d ∣ 3 → (d ≡ 1) ⊎ (d ≡ 3)
  div3 zero                      p = Empty.rec (znots (∣-zeroˡ p))
  div3 (suc zero)                p = inl refl
  div3 (suc (suc zero))          p = Empty.rec (¬2∣3 p)
  div3 (suc (suc (suc zero)))    p = inr refl
  div3 (suc (suc (suc (suc d)))) p =
    Empty.rec (¬-<-zero
      (pred-≤-pred (pred-≤-pred (pred-≤-pred (m∣sn→m≤sn p)))))

-- 2 = 2^1 does not divide lcm(1)      -- the walk's first install
jump-2 : (C : ℕ) → IsLCM (range1 1) C → ¬ (2 ∣ C)
jump-2 C lcmC = prime-not-covered 2 1 C isPrime2 refl lcmC

-- 3 = 3^1 does not divide lcm(1,2)    -- the walk's second install
jump-3 : (C : ℕ) → IsLCM (range1 2) C → ¬ (3 ∣ C)
jump-3 C lcmC = prime-not-covered 3 2 C isPrime3 refl lcmC

-- 4 = 2^2 does not divide lcm(1,2,3)
jump-4 : (C : ℕ) → IsLCM (range1 3) C → ¬ (4 ∣ C)
jump-4 C lcmC = prime-power-not-covered 2 1 3 C isPrime2 refl lcmC

-- 8 = 2^3 does not divide lcm(1,…,7)
jump-8 : (C : ℕ) → IsLCM (range1 7) C → ¬ (8 ∣ C)
jump-8 C lcmC = prime-power-not-covered 2 2 7 C isPrime2 refl lcmC

-- 9 = 3^2 does not divide lcm(1,…,8)
jump-9 : (C : ℕ) → IsLCM (range1 8) C → ¬ (9 ∣ C)
jump-9 C lcmC = prime-power-not-covered 3 1 8 C isPrime3 refl lcmC

-- …and the capacity strictly changes at 4: lcm(1,2,3) ≠ lcm(1,2,3,4).
jump-4-capacity :
  (C D : ℕ) → IsLCM (range1 3) C → IsLCM (range1 4) D → ¬ (C ≡ D)
jump-4-capacity C D = prime-power-jumps-capacity 2 1 3 C D isPrime2 refl

------------------------------------------------------------------------
-- NON-VACUITY of `build`, by definitional computation
------------------------------------------------------------------------

-- The theorems above are stated by universal property, so they hold of
-- ANY C satisfying IsLCM; nothing so far forces `build` to produce a
-- number one can look at.  These are exact symbolic checks (each is a
-- `refl`, i.e. definitional equality decided by the checker, not a
-- floating-point measurement) that the witness M = p^(a−1) · V really
-- is a common multiple of the range with the intended p-part.
--
--   [1..3], p=2, a=2 : V = 1·1·1·3     M = 2·3        = 6
--                      6 is a multiple of 1,2,3 and 4 ∤ 6.
--   [1..7], p=2, a=3 : V = 1·1·3·1·5·3·7 = 315
--                      M = 4·315 = 1260 = 3·lcm(1..7); 8 ∤ 1260.
--   [1..8], p=3, a=2 : V = 1·2·1·4·5·2·7·8 = 4480
--                      M = 3·4480 = 13440 = 16·lcm(1..8); 9 ∤ 13440.
--
-- The witness is a common multiple, deliberately NOT the lcm — the
-- proof needs only C ∣ M, so no minimality is ever required.

3<2^2 : 3 < 2 ^ 2
3<2^2 = ≤-refl

witness-4 : (2 ^ 1) · (build 2 isPrime2 1 3 3<2^2 .fst) ≡ 6
witness-4 = refl

7<2^3 : 7 < 2 ^ 3
7<2^3 = ≤-refl

witness-8 : (2 ^ 2) · (build 2 isPrime2 2 7 7<2^3 .fst) ≡ 1260
witness-8 = refl

8<3^2 : 8 < 3 ^ 2
8<3^2 = ≤-refl

witness-9 : (3 ^ 1) · (build 3 isPrime3 1 8 8<3^2 .fst) ≡ 13440
witness-9 = refl

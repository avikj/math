{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अन्तरालम् — every divisor of the capacity is the lcm of a sensor
-- family below the frontier, so the reachable states are exactly the
-- divisor lattice of the capacity.
--
-- TERM.  अन्तराल — the interior, the space between; here the interior
-- of the lattice between its bottom 1 and its top cap(k), which the
-- source note's table names "interior".
--
-- SOURCE.  notes/WALK_STATE_IS_ITS_LCM.md (absent from this repository) ("The walk's Nerode state is
-- its lcm, and its state space is a divisor lattice"), §2:
--
--   "**Theorem.** The set of lcms achievable by sensor families all of
--   whose addresses lie in `[1,k]` is **exactly** the set of divisors
--   of `cap(k)`."
--
-- The top row (`cap(k)` is achieved) is `capacity-attained` and the
-- bound row (nothing exceeds `cap(k)`) is `capacity`, both in
-- `WalkCapacity`.  This module proves the interior row: every divisor
-- of `cap(k)` is achieved.
--
-- WHAT IS PROVED.
--
--   (T1) fam-admissible : (d k : ℕ) → All (λ x → (0 < x) × (x ≤ k)) (fam d k)
--        where fam d k is the list of members of range1 k dividing d.
--   (T2) fam-common     : (d k : ℕ) → CommonMultiple (fam d k) d
--   (T3) interior       : (k d C : ℕ) → 1 ≤ d → IsLCM (range1 k) C → d ∣ C
--                         → IsLCM (fam d k) d
--        THE THEOREM: every divisor d of the capacity C of frontier k is
--        the lcm of an admissible family of that frontier, namely the
--        divisors of d that lie in [1,k].
--   (T4) reachable-iff-divisor : (k C : ℕ) → IsLCM (range1 k) C →
--          (d : ℕ) → 1 ≤ d →
--          ((d ∣ C) → Σ[ F ∈ List ℕ ] All (λ x → (0 < x) × (x ≤ k)) F × IsLCM F d)
--          × ((Σ[ F ∈ List ℕ ] All (λ x → (0 < x) × (x ≤ k)) F × IsLCM F d) → d ∣ C)
--        the note's Theorem as a two-way implication; (⇐) is
--        WalkCapacity.capacity, (⇒) is (T3).
--   (T5) refl instances at k = 6, cap(6) = 60: fam 12 6 and fam 20 6
--        listed, lcmList (range1 6) ≡ 60, and IsLCM (fam 12 6) 12,
--        IsLCM (fam 20 6) 20 obtained from (T3).
--
-- METHOD.  The note's proof takes the family {p^{b_p}}; this proof
-- takes instead the family of ALL divisors of d in [1,k] and shows it
-- is an lcm-family for d by strong induction on d.  The one new
-- arithmetic fact is L1 (`prime-power-below-frontier`): a prime power
-- dividing cap(k) is at most k, which is WalkJumps.prime-power-not-
-- covered read through the universal property (if p^a > k then cap(k)
-- divides cap(p^a − 1), which p^a does not divide).  The step: strip d
-- at a prime divisor p as p^a · u with p ∤ u; then p^a ∈ fam d k by L1,
-- u ∣ any common multiple by the induction hypothesis (fam u k is a
-- sublist of fam d k, L2), and WalkForcing.coprime-divisors-multiply
-- closes.  No lcm is constructed anywhere; `lcmList` appears only as a
-- witness in L1 and in the instances.
------------------------------------------------------------------------

module Antarala_EveryDivisorOfTheCapacityIsTheLcmOfASensorFamilyBelowTheFrontierSoTheReachableStatesAreExactlyTheDivisorLatticeOfTheCapacity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD using (isGCD)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

open import WalkCapacity
  using (All; _∈_; All→∈; range1; CommonMultiple; IsLCM;
         ∈-range1; capacity; range1-admissible)
open import WalkForcing using (coprime-divisors-multiply)
open import WalkJumps
  using (IsPrime; prime-0<; prime-alt; Strip; strip; ^-pos; 0<→≢0;
         lt-self; pos→suc; prime-power-not-covered)
open import CoprimeSplitting using (coprime-^ˡ; primeDivisor; dec∣)
open import LCMExists using (lcmList; lcmList-isLCM)

------------------------------------------------------------------------
-- १ · the family: divisors of d in the frontier range
------------------------------------------------------------------------

-- keep x if the decision says it divides d
keep : (x : ℕ) {d : ℕ} → Dec (x ∣ d) → List ℕ → List ℕ
keep x (yes _) rest = x ∷ rest
keep x (no  _) rest = rest

-- fam d k = [ x ∈ range1 k | x ∣ d ], built by recursion on k so that
-- every tested x is suc k' and dec∣ has its positivity proof for free
fam : ℕ → ℕ → List ℕ
fam d zero    = []
fam d (suc k) = keep (suc k) (dec∣ (suc k) d (suc-≤-suc zero-≤)) (fam d k)

-- lemmas about keep, by matching on the decision (no `with` needed)
keep-All : (Q : ℕ → Type) (x : ℕ) {d : ℕ} (dec : Dec (x ∣ d)) (rest : List ℕ) →
           Q x → All Q rest → All Q (keep x dec rest)
keep-All Q x (yes _) rest qx qs = qx , qs
keep-All Q x (no  _) rest qx qs = qs

keep-∣ : (x d : ℕ) (dec : Dec (x ∣ d)) (rest : List ℕ) →
         All (_∣ d) rest → All (_∣ d) (keep x dec rest)
keep-∣ x d (yes x∣d) rest qs = x∣d , qs
keep-∣ x d (no  _)   rest qs = qs

keep-∈-tail : (y : ℕ) {d : ℕ} (dec : Dec (y ∣ d)) (rest : List ℕ) {x : ℕ} →
              x ∈ rest → x ∈ keep y dec rest
keep-∈-tail y (yes _) rest m = inr m
keep-∈-tail y (no  _) rest m = m

keep-∈-head : (y : ℕ) {d : ℕ} (dec : Dec (y ∣ d)) (rest : List ℕ) {x : ℕ} →
              x ≡ y → x ∣ d → x ∈ keep y dec rest
keep-∈-head y (yes _)   rest x≡y x∣d = inl x≡y
keep-∈-head y (no ¬y∣d) rest x≡y x∣d = Empty.rec (¬y∣d (subst (_∣ _) x≡y x∣d))

------------------------------------------------------------------------
-- २ · (T1) admissibility and (T2) commonality of the family
------------------------------------------------------------------------

weaken-frontier : (j : ℕ) (ys : List ℕ) →
                  All (λ x → (0 < x) × (x ≤ j)) ys →
                  All (λ x → (0 < x) × (x ≤ suc j)) ys
weaken-frontier j []       _        = tt
weaken-frontier j (y ∷ ys) (p , ps) =
  (p .fst , ≤-suc (p .snd)) , weaken-frontier j ys ps

-- (T1) every member of fam d k is a positive address at most k
fam-admissible : (d k : ℕ) → All (λ x → (0 < x) × (x ≤ k)) (fam d k)
fam-admissible d zero    = tt
fam-admissible d (suc k) =
  keep-All (λ x → (0 < x) × (x ≤ suc k)) (suc k)
    (dec∣ (suc k) d (suc-≤-suc zero-≤)) (fam d k)
    (suc-≤-suc zero-≤ , ≤-refl)
    (weaken-frontier k (fam d k) (fam-admissible d k))

-- (T2) every member of fam d k divides d
fam-common : (d k : ℕ) → CommonMultiple (fam d k) d
fam-common d zero    = tt
fam-common d (suc k) =
  keep-∣ (suc k) d (dec∣ (suc k) d (suc-≤-suc zero-≤)) (fam d k) (fam-common d k)

-- membership: a positive divisor of d at most k is in fam d k
-- (modelled on WalkCapacity.∈-range1)
∈-fam : (x d k : ℕ) → 0 < x → x ≤ k → x ∣ d → x ∈ fam d k
∈-fam x d zero    0<x x≤k x∣d = Empty.rec (¬-<-zero (<≤-trans 0<x x≤k))
∈-fam x d (suc k) 0<x x≤k x∣d with ≤-split x≤k
... | inl x<sk = keep-∈-tail (suc k) (dec∣ (suc k) d (suc-≤-suc zero-≤)) (fam d k)
                   (∈-fam x d k 0<x (pred-≤-pred x<sk) x∣d)
... | inr x≡sk = keep-∈-head (suc k) (dec∣ (suc k) d (suc-≤-suc zero-≤)) (fam d k)
                   x≡sk x∣d

------------------------------------------------------------------------
-- ३ · L2: the family is monotone in d along divisibility
------------------------------------------------------------------------

-- for u ∣ d, a common multiple of fam d k is a common multiple of
-- fam u k (every divisor of u in range is a divisor of d in range)
keep-sub : (x u d m : ℕ) (decu : Dec (x ∣ u)) (decd : Dec (x ∣ d))
           (ru rd : List ℕ) → u ∣ d →
           (All (_∣ m) rd → All (_∣ m) ru) →
           All (_∣ m) (keep x decd rd) → All (_∣ m) (keep x decu ru)
keep-sub x u d m (yes _)   (yes _)    ru rd u∣d ih (h , hs) = h , ih hs
keep-sub x u d m (yes x∣u) (no ¬x∣d)  ru rd u∣d ih hs =
  Empty.rec (¬x∣d (∣-trans x∣u u∣d))
keep-sub x u d m (no _)    (yes _)    ru rd u∣d ih (_ , hs) = ih hs
keep-sub x u d m (no _)    (no _)     ru rd u∣d ih hs = ih hs

CM-fam-sub : (u d k m : ℕ) → u ∣ d →
             CommonMultiple (fam d k) m → CommonMultiple (fam u k) m
CM-fam-sub u d zero    m u∣d _  = tt
CM-fam-sub u d (suc k) m u∣d cm =
  keep-sub (suc k) u d m
    (dec∣ (suc k) u (suc-≤-suc zero-≤)) (dec∣ (suc k) d (suc-≤-suc zero-≤))
    (fam u k) (fam d k) u∣d (CM-fam-sub u d k m u∣d) cm

------------------------------------------------------------------------
-- ४ · L1: a prime power dividing the capacity lies below the frontier
------------------------------------------------------------------------

-- a common multiple of the longer range is one of the shorter range
CM-range1-sub : (k n : ℕ) → k ≤ n → (m : ℕ) →
                CommonMultiple (range1 n) m → CommonMultiple (range1 k) m
CM-range1-sub zero    n k≤n m cm = tt
CM-range1-sub (suc k) n k≤n m cm =
  All→∈ (_∣ m) (range1 n) cm (∈-range1 (suc k) n (suc-≤-suc zero-≤) k≤n)
  , CM-range1-sub k n (≤-trans ≤-sucℕ k≤n) m cm

-- L1.  If p^(suc e) divides an lcm C of [1..k] then p^(suc e) ≤ k.
-- Otherwise k ≤ p^(suc e) − 1 =: t, so C divides lcmList (range1 t)
-- (a common multiple of [1..t] is one of [1..k], and C is least), so
-- p^(suc e) divides lcmList (range1 t) — refuted by WalkJumps.
prime-power-below-frontier :
  (p e k C : ℕ) → IsPrime p → IsLCM (range1 k) C →
  (p ^ suc e) ∣ C → (p ^ suc e) ≤ k
prime-power-below-frontier p e k C pr (_ , C-least) q∣C
  with splitℕ-≤ (p ^ suc e) k
... | inl q≤k = q≤k
... | inr k<q = Empty.rec (prime-power-not-covered p e t D pr (sym st) (lcmList-isLCM (range1 t)) q∣D)
  where
  ps : Σ[ t ∈ ℕ ] (p ^ suc e) ≡ suc t
  ps = pos→suc (p ^ suc e) (^-pos p (suc e) (prime-0< p pr))

  t : ℕ
  t = ps .fst

  st : (p ^ suc e) ≡ suc t
  st = ps .snd

  k≤t : k ≤ t
  k≤t = pred-≤-pred (subst (k <_) st k<q)

  D : ℕ
  D = lcmList (range1 t)

  C∣D : C ∣ D
  C∣D = C-least D (CM-range1-sub k t k≤t D (lcmList-isLCM (range1 t) .fst))

  q∣D : (p ^ suc e) ∣ D
  q∣D = ∣-trans q∣C C∣D

------------------------------------------------------------------------
-- ५ · (T3) THE THEOREM, by strong induction on d through a fuel
------------------------------------------------------------------------

interior-fuel :
  (fuel k d C : ℕ) → d ≤ fuel → 1 ≤ d →
  IsLCM (range1 k) C → d ∣ C → IsLCM (fam d k) d
interior-fuel zero    k d C d≤f 1≤d _    _   =
  Empty.rec (¬-<-zero (≤-trans 1≤d d≤f))
interior-fuel (suc f) k d C d≤f 1≤d lcmC d∣C with ≤-split 1≤d
... | inr 1≡d =
      subst (λ x → IsLCM (fam x k) x) 1≡d (fam-common 1 k , λ m _ → ∣-oneˡ m)
... | inl 1<d = fam-common d k , least
  where
  0<d : 0 < d
  0<d = ≤-trans (suc-≤-suc zero-≤) 1<d

  pd : Σ[ p ∈ ℕ ] (IsPrime p × (p ∣ d))
  pd = primeDivisor d 1<d

  p    = pd .fst
  pp   = pd .snd .fst
  p∣d  = pd .snd .snd

  0<p : 0 < p
  0<p = prime-0< p pp

  st : Strip p d
  st = strip p pp d d 0<d ≤-refl

  -- the step, with the exponent exposed for the case split e = 0 / suc
  step : (m : ℕ) → CommonMultiple (fam d k) m →
         (e u : ℕ) → 0 < u → ((p ^ e) · u) ≡ d → ¬ (p ∣ u) → d ∣ m
  -- e = 0 is impossible: then d = u and p ∣ d = u
  step m cm zero u 0<u peu ¬p∣u =
    Empty.rec (¬p∣u (subst (p ∣_) (sym peu ∙ ·-identityˡ u) p∣d))
  step m cm (suc e) u 0<u peu ¬p∣u =
    subst (_∣ m) peu (coprime-divisors-multiply q u m cop q∣m u∣m)
    where
    q : ℕ
    q = p ^ suc e

    0<q : 0 < q
    0<q = ^-pos p (suc e) 0<p

    -- p ∣ q = p · p^e, so 1 < p ≤ q
    1<q : 1 < q
    1<q = <≤-trans (pp .fst) (m∣n→m≤n (0<→≢0 q 0<q) (∣-left (p ^ e)))

    q∣d : q ∣ d
    q∣d = subst (q ∣_) peu (∣-left u)

    u∣d : u ∣ d
    u∣d = subst (u ∣_) peu (∣-right q)

    -- L1: the prime power lies below the frontier, hence in the family
    q≤k : q ≤ k
    q≤k = prime-power-below-frontier p e k C pp lcmC (∣-trans q∣d d∣C)

    q∣m : q ∣ m
    q∣m = All→∈ (_∣ m) (fam d k) cm (∈-fam q d k 0<q q≤k q∣d)

    -- u is a proper divisor of d, so the induction hypothesis applies
    u<d : u < d
    u<d = subst (u <_) (·-comm u q ∙ peu) (lt-self u q 0<u 1<q)

    u≤f : u ≤ f
    u≤f = pred-≤-pred (<≤-trans u<d d≤f)

    ih : IsLCM (fam u k) u
    ih = interior-fuel f k u C u≤f 0<u lcmC (∣-trans u∣d d∣C)

    u∣m : u ∣ m
    u∣m = ih .snd m (CM-fam-sub u d k m u∣d cm)

    -- p ∤ u gives gcd(p,u) = 1, hence gcd(p^(suc e), u) = 1
    gpu : isGCD p u 1
    gpu with prime-alt p pp u
    ... | inl p∣u = Empty.rec (¬p∣u p∣u)
    ... | inr g   = g

    cop : isGCD q u 1
    cop = coprime-^ˡ p u gpu (suc e)

  least : (m : ℕ) → CommonMultiple (fam d k) m → d ∣ m
  least m cm =
    step m cm (st .fst) (st .snd .fst) (st .snd .snd .fst)
      (st .snd .snd .snd .fst) (st .snd .snd .snd .snd)

-- (T3) every divisor of the capacity is the lcm of its in-range divisors
interior : (k d C : ℕ) → 1 ≤ d → IsLCM (range1 k) C → d ∣ C → IsLCM (fam d k) d
interior k d C 1≤d lcmC d∣C = interior-fuel d k d C ≤-refl 1≤d lcmC d∣C

------------------------------------------------------------------------
-- ६ · (T4) the note's Theorem: reachable states = divisors of cap(k)
------------------------------------------------------------------------

Reachable : ℕ → ℕ → Type
Reachable k d = Σ[ F ∈ List ℕ ] (All (λ x → (0 < x) × (x ≤ k)) F) × IsLCM F d

-- (⇒) is interior, with witness fam d k; (⇐) is WalkCapacity.capacity
reachable-iff-divisor :
  (k C : ℕ) → IsLCM (range1 k) C → (d : ℕ) → 1 ≤ d →
  ((d ∣ C) → Reachable k d) × (Reachable k d → (d ∣ C))
reachable-iff-divisor k C lcmC d 1≤d =
  (λ d∣C → fam d k , fam-admissible d k , interior k d C 1≤d lcmC d∣C)
  , (λ r → capacity (r .fst) k d C (r .snd .snd) lcmC (r .snd .fst))

------------------------------------------------------------------------
-- ७ · (T5) the theorem fired at frontier 6, capacity 60
------------------------------------------------------------------------

-- the capacity of frontier 6 computes to 60 = 2² · 3 · 5
cap6 : lcmList (range1 6) ≡ 60
cap6 = refl

-- the families the theorem builds: the in-range divisors of 12 and 20
fam-12-6 : fam 12 6 ≡ 6 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
fam-12-6 = refl

fam-20-6 : fam 20 6 ≡ 5 ∷ 4 ∷ 2 ∷ 1 ∷ []
fam-20-6 = refl

1≤12 : 1 ≤ 12
1≤12 = suc-≤-suc zero-≤

1≤20 : 1 ≤ 20
1≤20 = suc-≤-suc zero-≤

-- 12 ∣ 60 and 20 ∣ 60, read against the computed capacity
12∣cap6 : 12 ∣ lcmList (range1 6)
12∣cap6 = subst (12 ∣_) (sym cap6) (∣-right 5)

20∣cap6 : 20 ∣ lcmList (range1 6)
20∣cap6 = subst (20 ∣_) (sym cap6) (∣-right 3)

-- {6,4,3,2,1} is an lcm-family for 12 at frontier 6 …
lcm-fam-12 : IsLCM (fam 12 6) 12
lcm-fam-12 = interior 6 12 (lcmList (range1 6)) 1≤12 (lcmList-isLCM (range1 6)) 12∣cap6

-- … and {5,4,2,1} is one for 20
lcm-fam-20 : IsLCM (fam 20 6) 20
lcm-fam-20 = interior 6 20 (lcmList (range1 6)) 1≤20 (lcmList-isLCM (range1 6)) 20∣cap6

-- the two-way statement, instantiated at frontier 6
reachable-6 : (d : ℕ) → 1 ≤ d →
  ((d ∣ 60) → Reachable 6 d) × (Reachable 6 d → (d ∣ 60))
reachable-6 = reachable-iff-divisor 6 60 (subst (IsLCM (range1 6)) cap6 (lcmList-isLCM (range1 6)))

{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- The induction ALONG the walk: WalkStream's single
-- install step, lifted to the whole trajectory.
--
-- Setting.  The walk's state is a pair (S , k): S the list of installed
-- sensors, k the frontier (the address most recently installed).  It
-- starts at ([] , 0) and its only transition is the walk's own policy —
-- read L = lcm S, take q = the least non-divisor of L (≥ 2, the walk's
-- search bound), and move to (q ∷ S , q).  `Reach n S k` says "(S , k)
-- is reachable in exactly n installs"; `Reach` is a RECURSIVE type
-- family over the step count, not an indexed inductive family over
-- lists, because cubical Agda will not unify a constructor in a list
-- index position (the same constraint recorded in WalkCapacity).
--
-- WHAT IS PROVED
--
--   invariant     (i)  : the walk's invariant is preserved by one step.
--                        Invariant = "every installed sensor lies in
--                        [1,k]" AND "any lcm of S is an lcm of
--                        range1 k".  This is `installStream` plus the
--                        frontier-jump lemma below.
--   reach-Inv          : hence every reachable state satisfies it —
--                        the induction along the walk.
--   reach-capacity(ii) : every reachable state's lcm IS an lcm of
--                        range1 (its frontier).  This is the Agda form
--                        of runtime/walk.py (absent from this repository)'s capacity_certificate:
--                        the walk is at the capacity of its own
--                        frontier at every step, not merely at the end.
--   reach-capacity-≡   : the same as an equation between numbers,
--                        lcm S ≡ lcm (1..k), by antisymmetry of ∣.
--   reach-dominates    : the optimality reading — no lossless family
--                        with addresses ≤ k has an lcm the reachable
--                        state's lcm does not already divide-cover
--                        (WalkCapacity.capacity evaluated along the
--                        trajectory).
--   walk-1, walk-2     : the trajectory is INHABITED: the first two
--                        states ([2] , 2) and ([3,2] , 3) are exhibited
--                        with their reachability data, so none of the
--                        above is vacuously true of an empty relation.
--
-- FRONTIER JUMP.  The one new lemma: if L is an lcm of range1 k and q
-- is a least non-divisor of L with 0 < q, then k < q.  (Otherwise q is
-- a member of range1 k, so q ∣ L.)  This is what discharges
-- installStream's hypothesis "all installed sensors lie in [1,q)" from
-- the weaker invariant "all lie in [1,k]" — i.e. it is the reason the
-- single step composes into an induction at all.
--
-- HYPOTHESES:
--
--   * The step relation carries `2 ≤ q` and `IsLCM S L` as explicit
--     hypotheses, exactly as WalkStream does.  `2 ≤ q` is the walk's
--     declared search bound (LeastNonDivisor alone does not give
--     0 < q); `IsLCM S L` is an existence assumption for the lcm, which
--     cubical v0.5 has no module to construct.  So `Reach` describes
--     runs of the walk in which the machine's read of lcm(S) is
--     supplied, rather than proving that read exists.  Both hypotheses
--     are supplied concretely in walk-1 and walk-2, which is why those
--     witnesses are included: they show the hypotheses are satisfiable
--     and not silently empty.
--   * `Reach` is indexed by an exact install count n.  Nothing is lost
--     (Σ over n gives plain reachability).
--
-- Nothing here re-proves WalkStream; the file's content is the
-- frontier-jump lemma, the trajectory, and the induction that carries
-- the step along it.

module WalkInduction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import WalkCapacity
open import WalkForcing using (LeastNonDivisor)
open import WalkStream using (installStream; 2≤→0<)

------------------------------------------------------------------------
-- The trajectory
------------------------------------------------------------------------

-- Reach n S k : the state (sensors S , frontier k) is reachable from
-- the initial state ([] , 0) in exactly n installs, each install being
-- "read an lcm L of the current sensors, install the least non-divisor
-- of L, and move the frontier to it".
Reach : ℕ → List ℕ → ℕ → Type
Reach zero    S k = (S ≡ []) × (k ≡ 0)
Reach (suc n) S k =
  Σ[ S' ∈ List ℕ ] Σ[ k' ∈ ℕ ] Σ[ L ∈ ℕ ]
    Reach n S' k'
    × IsLCM S' L
    × (2 ≤ k)
    × LeastNonDivisor L k
    × (S ≡ k ∷ S')

-- The walk's invariant at a state: every sensor is an address in the
-- frontier range, and the state sits at the capacity of that range.
Inv : List ℕ → ℕ → Type
Inv S k =
  All (λ x → (0 < x) × (x ≤ k)) S
  × ((L : ℕ) → IsLCM S L → IsLCM (range1 k) L)

------------------------------------------------------------------------
-- Frontier jump: the install always overshoots the current frontier
------------------------------------------------------------------------

frontier-jump :
  (k L q : ℕ) → 0 < q →
  IsLCM (range1 k) L → LeastNonDivisor L q →
  k < q
frontier-jump k L q 0<q (L-common , _) (q∤L , _) with splitℕ-≤ q k
... | inl q≤k =
  Empty.rec (q∤L (All→∈ (_∣ L) (range1 k) L-common (∈-range1 q k 0<q q≤k)))
... | inr k<q = k<q

-- [1,k] ⊆ [1,q) once k < q: turns the invariant's bound into exactly
-- the hypothesis installStream wants.
below-frontier :
  (S : List ℕ) (k q : ℕ) → k < q →
  All (λ x → (0 < x) × (x ≤ k)) S →
  All (λ x → (0 < x) × (x < q)) S
below-frontier []       k q k<q _        = tt
below-frontier (y ∷ ys) k q k<q (p , ps) =
  (p .fst , ≤<-trans (p .snd) k<q) , below-frontier ys k q k<q ps

weaken-<≤ :
  (S : List ℕ) (q : ℕ) →
  All (λ x → (0 < x) × (x < q)) S →
  All (λ x → (0 < x) × (x ≤ q)) S
weaken-<≤ []       q _        = tt
weaken-<≤ (y ∷ ys) q (p , ps) =
  (p .fst , <-weaken (p .snd)) , weaken-<≤ ys q ps

------------------------------------------------------------------------
-- (i) INVARIANT PRESERVATION
------------------------------------------------------------------------

-- One install preserves the invariant, with the frontier moved to the
-- installed address.  This is WalkStream's step plus frontier-jump.
invariant-step :
  (S : List ℕ) (k L q : ℕ) →
  2 ≤ q →
  IsLCM S L →
  LeastNonDivisor L q →
  Inv S k →
  Inv (q ∷ S) q
invariant-step S k L q 2≤q lcmS lnd (inRange , atCap) =
  ((0<q , ≤-refl) , weaken-<≤ S q below)
  , λ M lcmM → installStream S L q M 2≤q lcmS lnd below lcmM
  where
  0<q : 0 < q
  0<q = 2≤→0< q 2≤q

  k<q : k < q
  k<q = frontier-jump k L q 0<q (atCap L lcmS) lnd

  below : All (λ x → (0 < x) × (x < q)) S
  below = below-frontier S k q k<q inRange

-- The initial state satisfies the invariant (range1 0 = [], so the
-- capacity clause is the identity).
Inv-init : Inv [] 0
Inv-init = tt , λ L p → p

-- THE INDUCTION ALONG THE WALK: every reachable state satisfies the
-- invariant.
reach-Inv : (n : ℕ) (S : List ℕ) (k : ℕ) → Reach n S k → Inv S k
reach-Inv zero S k (S≡[] , k≡0) =
  subst2 Inv (sym S≡[]) (sym k≡0) Inv-init
reach-Inv (suc n) S k (S' , k' , L , r , lcmS' , 2≤k , lnd , S≡) =
  subst (λ T → Inv T k) (sym S≡)
    (invariant-step S' k' L k 2≤k lcmS' lnd (reach-Inv n S' k' r))

------------------------------------------------------------------------
-- (ii) THE WALK IS AT CAPACITY AT EVERY STEP
------------------------------------------------------------------------

-- Every reachable state's lcm is an lcm of the frontier range: the
-- checked form of the walk's running capacity certificate.
reach-capacity :
  (n : ℕ) (S : List ℕ) (k L : ℕ) →
  Reach n S k → IsLCM S L → IsLCM (range1 k) L
reach-capacity n S k L r = reach-Inv n S k r .snd L

-- Every reachable state's sensors are addresses of its frontier.
reach-frontier :
  (n : ℕ) (S : List ℕ) (k : ℕ) →
  Reach n S k → All (λ x → (0 < x) × (x ≤ k)) S
reach-frontier n S k r = reach-Inv n S k r .fst

-- The same as an equation between numbers: lcm S ≡ lcm (1..k).
reach-capacity-≡ :
  (n : ℕ) (S : List ℕ) (k L C : ℕ) →
  Reach n S k → IsLCM S L → IsLCM (range1 k) C → L ≡ C
reach-capacity-≡ n S k L C r lcmS (C-common , C-least) =
  antisym∣ (L-isLCM .snd C C-common) (C-least L (L-isLCM .fst))
  where
  L-isLCM : IsLCM (range1 k) L
  L-isLCM = reach-capacity n S k L r lcmS

-- OPTIMALITY along the trajectory: no lossless sensor family with
-- addresses ≤ k has an lcm that the reachable state's lcm does not
-- already cover.  (WalkCapacity.capacity, evaluated at the walk.)
reach-dominates :
  (n : ℕ) (S : List ℕ) (k L : ℕ) →
  Reach n S k → IsLCM S L →
  (xs : List ℕ) (M : ℕ) → IsLCM xs M →
  All (λ x → (0 < x) × (x ≤ k)) xs →
  M ∣ L
reach-dominates n S k L r lcmS xs M lcmxs inRange =
  capacity xs k M L lcmxs (reach-capacity n S k L r lcmS) inRange

------------------------------------------------------------------------
-- The trajectory is inhabited: the walk's first two states
------------------------------------------------------------------------

lcm-[] : IsLCM [] 1
lcm-[] = tt , λ m _ → ∣-oneˡ m

¬2∣1 : ¬ (2 ∣ 1)
¬2∣1 p = snotz (injSuc (antisym∣ p (∣-oneˡ 2)))

lnd-1-2 : LeastNonDivisor 1 2
lnd-1-2 = ¬2∣1 , λ r 2≤r r<2 → Empty.rec (¬m<m (≤<-trans 2≤r r<2))

-- first install: from ([] , 0) the machine installs 2.
walk-1 : Reach 1 (2 ∷ []) 2
walk-1 = [] , 0 , 1 , (refl , refl) , lcm-[] , ≤-refl , lnd-1-2 , refl

lcm-[2] : IsLCM (2 ∷ []) 2
lcm-[2] = (∣-refl refl , tt) , λ m c → c .fst

¬3∣2 : ¬ (3 ∣ 2)
¬3∣2 p = snotz (≤0→≡0 (pred-≤-pred (pred-≤-pred (m∣sn→m≤sn p))))

lnd-2-3 : LeastNonDivisor 2 3
lnd-2-3 = ¬3∣2 , below
  where
  below : (r : ℕ) → 2 ≤ r → r < 3 → r ∣ 2
  below r 2≤r r<3 with ≤-split 2≤r
  ... | inl 2<r = Empty.rec (¬m<m (≤<-trans 2<r r<3))
  ... | inr 2≡r = subst (_∣ 2) 2≡r (∣-refl refl)

-- second install: from ([2] , 2) the machine installs 3.
walk-2 : Reach 2 (3 ∷ 2 ∷ []) 3
walk-2 =
  (2 ∷ []) , 2 , 2 , walk-1 , lcm-[2] , suc-≤-suc (suc-≤-suc zero-≤) , lnd-2-3 , refl

-- …and at that state the walk is at capacity: any lcm of [3,2] is an
-- lcm of [3,2,1].  (Instance of reach-capacity; no new content, it is
-- here so the general theorem is seen to fire on a concrete run.)
walk-2-at-capacity : (L : ℕ) → IsLCM (3 ∷ 2 ∷ []) L → IsLCM (range1 3) L
walk-2-at-capacity L = reach-capacity 2 (3 ∷ 2 ∷ []) 3 L walk-2

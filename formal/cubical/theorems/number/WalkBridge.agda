{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- jump points of the capacity function, in increasing order.
--
-- §(c) holds in both directions (WalkForcing + CoprimeSplitting: an
-- install is a prime power; WalkJumps: a prime power is a jump point), and
-- capacity is unconditional (WalkUnconditional, on LCMExists).  This module
-- proves that the walk's install EVENTS coincide with the capacity
-- function's jump POINTS.
--
-- THE ARGUMENT, in four lines of arithmetic and no new machinery.
-- Write cap k = lcm(1..k), and call k a jump when suc k ∤ cap k.
-- Suppose the walk's state has lcm cap m (m ≥ 1) and it installs
-- q = suc j, the least non-divisor of cap m.  Then
--
--   (i)   m ≤ j.  Everything in [1,m] divides cap m, so a non-divisor
--         is beyond the frontier.
--   (ii)  cap j ≡ cap m.  Downward: every r ≤ j with r ≥ 2 divides
--         cap m by MINIMALITY of q, and 1 divides everything, so cap j
--         (the least such) divides cap m.  Upward: monotonicity, from
--         (i).  So the capacity is FLAT across the interval the walk
--         skips -- it skips exactly because nothing happens there.
--   (iii) q ∤ cap m and cap j ≡ cap m give q ∤ cap j: the install point
--         IS a jump point.
--   (iv)  for m ≤ i < j, minimality gives suc i ∣ cap m, and
--         monotonicity gives cap m ∣ cap i, so suc i ∣ cap i: no jump
--         point is skipped.
--
-- (iii) and (iv) together are §(b): the install lands on a jump point
-- and passes over none, so the install stream is the increasing
-- enumeration of the jump points.  (ii) is why -- the flatness of cap on
-- the skipped interval is the whole content, and it is the same fact the
-- computed witness `no-jump-at-6 : cap 6 ≡ cap 5` in WalkUnconditional
-- exhibits at the first place the walk actually skips.
--
-- THE WALK IS ALSO MADE TOTAL HERE.  Every previous theorem in the lane
-- quantified over a hypothesis `LeastNonDivisor L q`, so the walk's step
-- was a relation, not a function.  `leastND` below constructs the least
-- non-divisor of any L ≥ 1 by bounded search -- the bound is L+1, which
-- never divides L -- using the repo's own `dec∣` (CoprimeSplitting) and
-- the positivity of cap proved here.  So `next : ℕ → ℕ` is a function
-- and the walk COMPUTES: `next-5 : next 5 ≡ 7` and its siblings below
-- are `refl`, i.e. the install stream 2, 3, 4, 5, 7 evaluated by the
-- kernel.  Exact symbolic computation, hence proof (CLAUDE.md (absent from this repository)), not
-- measurement.
--
-- WHERE THE COMPUTATION STOPS, and why that is the theorem again.  The
-- witnesses stop at `next 5`.  This is not an accident of the evaluator:
-- the search decides
-- `s ∣ cap m` for each candidate s, and a unary divisibility test on
-- cap m costs Θ(cap m), so a step costs Θ(cap m · (next m − m)) — and
-- cap m is e^ψ(m).  The walk's STORAGE law is also its naive RUNTIME
-- law, so the capacity theorem is exactly the obstruction to executing
-- the walk far by evaluation.  The cost is
-- read off the definitions.  Getting
-- past m ≈ 8 needs binary naturals, not a bigger machine.
--
-- Predicates are recursive type families and no constructor is matched
-- in an index position, per WalkCapacity's recorded constraints.

module WalkBridge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import WalkCapacity
  using (All ; _∈_ ; All→∈ ; range1 ; IsLCM ; CommonMultiple ; ∈-range1)
open import LCMExists
  using (lcmList ; lcmList-isLCM ; All-∣-trans)
open import WalkUnconditional using (cap)
open import WalkForcing using (LeastNonDivisor)
open import WalkStream using (range1-common)
open import CoprimeSplitting using (dec∣)

------------------------------------------------------------------------
-- The three facts about `cap` that everything below is made of.
------------------------------------------------------------------------

-- every address in [1,k] divides cap k
cap-covers : (r k : ℕ) → 0 < r → r ≤ k → r ∣ cap k
cap-covers r k 0<r r≤k =
  All→∈ (_∣ cap k) (range1 k) (lcmList-isLCM (range1 k) .fst)
        (∈-range1 r k 0<r r≤k)

-- and cap k is the least such: the universal property, in usable form
cap-least : (k N : ℕ) → ((r : ℕ) → 0 < r → r ≤ k → r ∣ N) → cap k ∣ N
cap-least k N h = lcmList-isLCM (range1 k) .snd N (range1-common k N h)

-- hence monotone under divisibility
cap-mono : (a b : ℕ) → a ≤ b → cap a ∣ cap b
cap-mono a b a≤b =
  cap-least a (cap b) (λ r 0<r r≤a → cap-covers r b 0<r (≤-trans r≤a a≤b))

------------------------------------------------------------------------
-- cap is positive.  Needed to make the walk's step TOTAL (the bounded
-- search below needs a nonzero modulus), and not available from
-- LCMExists, which deliberately assumes no positivity anywhere.  The
-- witness is the product of the frontier range: it is a common multiple,
-- so cap divides it, and it is nonzero, so cap is.
------------------------------------------------------------------------

0<-from-≢0 : (n : ℕ) → ¬ (n ≡ 0) → 0 < n
0<-from-≢0 zero    h = Empty.rec (h refl)
0<-from-≢0 (suc n) _ = suc-≤-suc zero-≤

·-pos : (a b : ℕ) → 0 < a → 0 < b → 0 < (a · b)
·-pos zero    b       0<a _   = Empty.rec (¬-<-zero 0<a)
·-pos (suc a) zero    _   0<b = Empty.rec (¬-<-zero 0<b)
·-pos (suc a) (suc b) _   _   = suc-≤-suc zero-≤

prod : List ℕ → ℕ
prod []       = 1
prod (x ∷ xs) = x · prod xs

prod-pos : (xs : List ℕ) → All (λ x → 0 < x) xs → 0 < prod xs
prod-pos []       _        = suc-≤-suc zero-≤
prod-pos (x ∷ xs) (p , ps) = ·-pos x (prod xs) p (prod-pos xs ps)

prod-common : (xs : List ℕ) → CommonMultiple xs (prod xs)
prod-common []       = tt
prod-common (x ∷ xs) =
  ∣-left (prod xs) , All-∣-trans xs (∣-right x) (prod-common xs)

lcmList-pos : (xs : List ℕ) → All (λ x → 0 < x) xs → 0 < lcmList xs
lcmList-pos xs pos = 0<-from-≢0 (lcmList xs) nonzero
  where
  L∣P : lcmList xs ∣ prod xs
  L∣P = lcmList-isLCM xs .snd (prod xs) (prod-common xs)

  nonzero : ¬ (lcmList xs ≡ 0)
  nonzero e =
    ¬-<-zero (subst (0 <_)
      (sym (∣-zeroˡ (subst (_∣ prod xs) e L∣P)))
      (prod-pos xs pos))

range1-pos : (k : ℕ) → All (λ x → 0 < x) (range1 k)
range1-pos zero    = tt
range1-pos (suc k) = suc-≤-suc zero-≤ , range1-pos k

cap-pos : (k : ℕ) → 0 < cap k
cap-pos k = lcmList-pos (range1 k) (range1-pos k)

------------------------------------------------------------------------
-- Jump points of the capacity function.
--
-- `Jump k` reads "suc k is a jump point", i.e. cap grows from k to
-- suc k.  Indexing by the PREDECESSOR keeps subtraction out of every
-- statement below; `predℕ` appears nowhere.
------------------------------------------------------------------------

Jump : ℕ → Type
Jump k = ¬ (suc k ∣ cap k)

-- a jump really is a strict increase of the capacity, not merely a
-- non-divisibility: the two readings agree.
Jump→cap≢ : (k : ℕ) → Jump k → ¬ (cap (suc k) ≡ cap k)
Jump→cap≢ k jk e =
  jk (subst (suc k ∣_) e (cap-covers (suc k) (suc k) (suc-≤-suc zero-≤) ≤-refl))

cap≢→Jump : (k : ℕ) → ¬ (cap (suc k) ≡ cap k) → Jump k
cap≢→Jump k ne d = ne (antisym∣ down (cap-mono k (suc k) ≤-sucℕ))
  where
  down : cap (suc k) ∣ cap k
  down = cap-least (suc k) (cap k) h
    where
    h : (r : ℕ) → 0 < r → r ≤ suc k → r ∣ cap k
    h r 0<r r≤sk with ≤-split r≤sk
    ... | inr r≡sk = subst (_∣ cap k) (sym r≡sk) d
    ... | inl r<sk = cap-covers r k 0<r (pred-≤-pred r<sk)

------------------------------------------------------------------------
-- THE BRIDGE.  The walk's state has lcm cap m; it installs q = suc j.
------------------------------------------------------------------------

module _ (m j : ℕ) (1≤m : 1 ≤ m) (lnd : LeastNonDivisor (cap m) (suc j)) where

  private
    q∤ : ¬ (suc j ∣ cap m)
    q∤ = lnd .fst

    below : (r : ℕ) → 2 ≤ r → r < suc j → r ∣ cap m
    below = lnd .snd

  -- (i) the install is strictly beyond the current frontier
  install-beyond : m ≤ j
  install-beyond with splitℕ-≤ m j
  ... | inl m≤j = m≤j
  ... | inr j<m = Empty.rec (q∤ (cap-covers (suc j) m (suc-≤-suc zero-≤) j<m))

  -- (ii) the capacity is FLAT across the skipped interval
  frontier-flat : cap j ≡ cap m
  frontier-flat = antisym∣ down (cap-mono m j install-beyond)
    where
    down : cap j ∣ cap m
    down = cap-least j (cap m) h
      where
      h : (r : ℕ) → 0 < r → r ≤ j → r ∣ cap m
      h r 0<r r≤j with ≤-split 0<r
      ... | inr 1≡r = subst (_∣ cap m) 1≡r (∣-oneˡ (cap m))
      ... | inl 1<r = below r 1<r (suc-≤-suc r≤j)

  -- (iii) the install point IS a jump point
  install-is-jump : Jump j
  install-is-jump d = q∤ (subst (suc j ∣_) frontier-flat d)

  -- (iv) and no jump point was passed over
  no-jump-skipped : (i : ℕ) → m ≤ i → i < j → ¬ Jump i
  no-jump-skipped i m≤i i<j notJump =
    notJump (∣-trans (below (suc i) (suc-≤-suc (≤-trans 1≤m m≤i))
                            (suc-≤-suc i<j))
                     (cap-mono m i m≤i))

  ------------------------------------------------------------------
  -- (v) and the state's lcm after the install is cap (suc j): the walk
  -- is again exactly at the capacity of its new frontier, so the whole
  -- argument re-enters at m := suc j.  This is what makes the induction
  -- along the walk go through, and it is stated numerically (three
  -- clauses = "cap (suc j) is the lcm of {q} ∪ old state") so no list
  -- of sensors appears.
  ------------------------------------------------------------------

  install-lcm-covers : suc j ∣ cap (suc j)
  install-lcm-covers = cap-covers (suc j) (suc j) (suc-≤-suc zero-≤) ≤-refl

  install-lcm-extends : cap m ∣ cap (suc j)
  install-lcm-extends = cap-mono m (suc j) (≤-suc install-beyond)

  install-lcm-least : (N : ℕ) → suc j ∣ N → cap m ∣ N → cap (suc j) ∣ N
  install-lcm-least N sj∣N capm∣N = cap-least (suc j) N h
    where
    h : (r : ℕ) → 0 < r → r ≤ suc j → r ∣ N
    h r 0<r r≤sj with ≤-split r≤sj
    ... | inr r≡sj = subst (_∣ N) (sym r≡sj) sj∣N
    ... | inl r<sj =
      ∣-trans (subst (r ∣_) frontier-flat
                (cap-covers r j 0<r (pred-≤-pred r<sj)))
              capm∣N

------------------------------------------------------------------------
-- THE WALK'S STEP IS A FUNCTION.  Bounded search for the least
-- non-divisor; the bound is L+1, which never divides L ≥ 1.
------------------------------------------------------------------------

findND : (L s n : ℕ) → 2 ≤ s →
         ((r : ℕ) → 2 ≤ r → r < s → r ∣ L) →
         ¬ ((s + n) ∣ L) →
         Σ[ q ∈ ℕ ] (2 ≤ q) × LeastNonDivisor L q
findND L s zero 2≤s bel ¬b =
  s , 2≤s , (subst (λ z → ¬ (z ∣ L)) (+-zero s) ¬b , bel)
findND L s (suc n) 2≤s bel ¬b
  with dec∣ s L (≤-trans (suc-≤-suc zero-≤) 2≤s)
... | no  s∤L = s , 2≤s , (s∤L , bel)
... | yes s∣L = findND L (suc s) n (≤-suc 2≤s) bel' ¬b'
  where
  bel' : (r : ℕ) → 2 ≤ r → r < suc s → r ∣ L
  bel' r 2≤r r<ss with ≤-split (pred-≤-pred r<ss)
  ... | inl r<s = bel r 2≤r r<s
  ... | inr r≡s = subst (_∣ L) (sym r≡s) s∣L

  ¬b' : ¬ ((suc s + n) ∣ L)
  ¬b' = subst (λ z → ¬ (z ∣ L)) (+-suc s n) ¬b

leastND : (L : ℕ) → 0 < L → Σ[ q ∈ ℕ ] (2 ≤ q) × LeastNonDivisor L q
leastND zero     0<L = Empty.rec (¬-<-zero 0<L)
leastND (suc L') _   = findND (suc L') 2 L' ≤-refl vac ¬bound
  where
  vac : (r : ℕ) → 2 ≤ r → r < 2 → r ∣ suc L'
  vac r 2≤r r<2 = Empty.rec (¬m<m (≤<-trans 2≤r r<2))

  ¬bound : ¬ ((2 + L') ∣ suc L')
  ¬bound d = ¬m<m (m∣sn→m≤sn d)

-- THE WALK'S STEP.  next m is the sensor the walk installs when its
-- state's lcm is cap m.
next : ℕ → ℕ
next m = leastND (cap m) (cap-pos m) .fst

next-2≤ : (m : ℕ) → 2 ≤ next m
next-2≤ m = leastND (cap m) (cap-pos m) .snd .fst

next-lnd : (m : ℕ) → LeastNonDivisor (cap m) (next m)
next-lnd m = leastND (cap m) (cap-pos m) .snd .snd

------------------------------------------------------------------------
-- §(b), assembled: `next m` is the LEAST JUMP POINT beyond m, and the
-- walk re-enters at it.
------------------------------------------------------------------------

pred-form : (q : ℕ) → 2 ≤ q → Σ[ j ∈ ℕ ] q ≡ suc j
pred-form zero    2≤q = Empty.rec (¬-<-zero 2≤q)
pred-form (suc j) _   = j , refl

walk-step :
  (m : ℕ) → 1 ≤ m →
  Σ[ j ∈ ℕ ]
      (next m ≡ suc j)                                  -- the install
    × (m ≤ j)                                           -- (i)  beyond
    × (cap j ≡ cap m)                                   -- (ii) flat
    × (Jump j)                                          -- (iii) it jumps
    × ((i : ℕ) → m ≤ i → i < j → ¬ Jump i)              -- (iv) none skipped
walk-step m 1≤m = j , q≡sj , install-beyond m j 1≤m lnd
                          , frontier-flat m j 1≤m lnd
                          , install-is-jump m j 1≤m lnd
                          , no-jump-skipped m j 1≤m lnd
  where
  j    : ℕ
  j    = pred-form (next m) (next-2≤ m) .fst
  q≡sj : next m ≡ suc j
  q≡sj = pred-form (next m) (next-2≤ m) .snd
  lnd  : LeastNonDivisor (cap m) (suc j)
  lnd  = subst (LeastNonDivisor (cap m)) q≡sj (next-lnd m)

------------------------------------------------------------------------
-- §(b) GLOBALLY: the install STREAM, and that it enumerates every jump
-- point in increasing order and nothing else.
--
-- `walk-step` is local -- one install.  Iterating it from the walk's
-- initial state (lcm = cap 1 = 1) gives the stream, and four statements
-- pin it down completely:
--
--   install-mono         strictly increasing
--   install-is-jump!     every term is a jump point
--   install-exhaustive   nothing strictly between consecutive terms is
--   below-first          and nothing below the first term is either
--
-- Together: the map n ↦ install n is the increasing enumeration of
-- { k : Jump k } shifted by one (install n = suc of the jump index), so
-- the walk's install events ARE the jump points, in order.
------------------------------------------------------------------------

install : ℕ → ℕ
install zero    = next 1
install (suc n) = next (install n)

install-2≤ : (n : ℕ) → 2 ≤ install n
install-2≤ zero    = next-2≤ 1
install-2≤ (suc n) = next-2≤ (install n)

install-1≤ : (n : ℕ) → 1 ≤ install n
install-1≤ n = ≤-trans (suc-≤-suc zero-≤) (install-2≤ n)

-- the walk-step data at stage n, packaged once
private
  stepAt : (n : ℕ) →
    Σ[ j ∈ ℕ ]
        (install (suc n) ≡ suc j)
      × (install n ≤ j)
      × (cap j ≡ cap (install n))
      × (Jump j)
      × ((i : ℕ) → install n ≤ i → i < j → ¬ Jump i)
  stepAt n = walk-step (install n) (install-1≤ n)

-- strictly increasing
install-mono : (n : ℕ) → install n < install (suc n)
install-mono n =
  subst (install n <_) (sym (stepAt n .snd .fst))
        (suc-≤-suc (stepAt n .snd .snd .fst))

-- every install is a jump point (named by its predecessor, as `Jump` is)
install-is-jump! : (n : ℕ) →
  Σ[ j ∈ ℕ ] (install (suc n) ≡ suc j) × Jump j
install-is-jump! n =
  stepAt n .fst
  , stepAt n .snd .fst
  , stepAt n .snd .snd .snd .snd .fst

-- and nothing strictly between two consecutive installs is a jump
install-exhaustive : (n i : ℕ) →
  install n ≤ i → suc i < install (suc n) → ¬ Jump i
install-exhaustive n i m≤i si<inst =
  stepAt n .snd .snd .snd .snd .snd i m≤i
    (pred-≤-pred (subst (suc i <_) (stepAt n .snd .fst) si<inst))

-- the base: 0 is not a jump point (1 divides everything), so the walk
-- misses nothing below its first install either.
not-jump-0 : ¬ Jump 0
not-jump-0 jk = jk (∣-oneˡ (cap 0))

below-first : (i : ℕ) → suc i < install 0 → ¬ Jump i
below-first zero    _        = not-jump-0
below-first (suc i) si<inst  =
  step1 .snd .snd .snd .snd .snd (suc i) (suc-≤-suc zero-≤) si<j
  where
  step1 = walk-step 1 ≤-refl

  si<j : suc i < step1 .fst
  si<j = pred-≤-pred (subst (suc (suc i) <_) (step1 .snd .fst) si<inst)

------------------------------------------------------------------------
-- IT COMPUTES.  The install stream, evaluated by the kernel.  `next`
-- goes through a bounded search whose every divisibility test is
-- decided by `dec∣`, so these are not definitional accidents: each is
-- the walk actually taking a step.
--
-- 2, 3, 4, 5, 7, 8, 9 -- the prime powers in increasing order, which is
-- §(c) of the note firing on the stream §(b) identifies.  Note 6 is
-- absent: `next 5 ≡ 7` is the walk SKIPPING a non-jump, the case (ii)
-- and (iv) above exist to handle, and it is the same fact as
-- WalkUnconditional's computed `no-jump-at-6 : cap 6 ≡ cap 5`.
------------------------------------------------------------------------

next-1 : next 1 ≡ 2
next-1 = refl

next-2 : next 2 ≡ 3
next-2 = refl

next-3 : next 3 ≡ 4
next-3 = refl

next-4 : next 4 ≡ 5
next-4 = refl

next-5 : next 5 ≡ 7
next-5 = refl

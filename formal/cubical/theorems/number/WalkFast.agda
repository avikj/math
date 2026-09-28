{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- WalkFast
--
-- THE THEOREM REPLACES THE COMPUTATION.  This is CLAUDE.md (absent from this repository)'s central
-- rule applied to the walk's own execution, and it is the first place in
-- the walk lane where a proved theorem buys a superexponential speedup
-- rather than merely recording one.
--
-- `WalkBridge` makes the walk's step a total function
--
--     next m = least q ≥ 2 with q ∤ cap m ,          cap m = lcm(1..m),
--
-- and it RUNS: next 1..5 = 2,3,4,5,7 by refl.  Then it stops, for a
-- derived reason —
-- the search decides `s ∣ cap m` per candidate, a unary divisibility
-- test on cap m costs Θ(cap m), and cap m = e^{ψ(m)}.  The walk's
-- storage law is its naive runtime law.
--
-- But `WalkPrimePowers` proved that the installs are exactly the prime
-- powers in increasing order.  So the expensive predicate
--
--     q ∤ cap m          (an object of size e^{ψ(m)})
--
-- can be traded for the cheap one
--
--     q is a prime power (an object of size m)
--
-- and `next-characterised` below is the exchange rate: to know `next m`,
-- exhibit a prime power q > m and refute prime-power-hood for the finitely
-- many r strictly between.  Both halves are decidable at size ~q by
-- `decIsPrimePower`, built here from `primeDivisor` and `strip`.
--
-- `next-characterised`, `decIsPrimePower`, and the decision procedure's
-- own non-vacuity (`test-9 : IsPrimePower 9`, obtained by the kernel
-- evaluating `decIsPrimePower 9`) are here.  The payoff instances are in
-- `WalkFastInstance`:
--
--     next-8  : next 8  ≡ 9
--     next-9  : next 9  ≡ 11
--     next-10 : next 10 ≡ 11
--
-- with `cap m` never evaluated.  The `with`-abstraction in
-- `next-characterised` is not what forces the evaluation: applying it at
-- m = 8 exhausts the heap, and so does replacing the `with` by an
-- antisymmetry argument whose own case split is on VARIABLES; both are
-- rescued by the same change, a `let` with no type signature.
--
-- WHAT ACTUALLY FORCES THE EVALUATION is in the conversion checker.
-- The goal type `next 8 ≡ 9` contains one occurrence of `next 8`;
-- instantiating any lemma of this file at m := 8 contributes a SECOND,
-- independently elaborated occurrence, and putting the two side by side
-- runs the walk on cap 8.  A metavariable is solved by assignment and
-- never by reduction, so handing the proof the goal's OWN `next 8` is
-- free; building a second one is not.  Hence `WalkFastInstance`
-- packages everything the walk knows into one value, binds it with a
-- signature-free `let` (a signature is itself a second elaboration of
-- `next 8`, and loses), and lets the goal supply `next m` as a meta.
--
-- CONSEQUENCE FOR THIS FILE, and it is a real one.
-- `next-characterised` below is cheap to PROVE, because m is a
-- variable, and useless to APPLY at a numeral, because its conclusion
-- `next m ≡ q` writes `next m` a second time.  It is kept because it is
-- the statement the surrounding notes quote; the applicable form is
-- `WalkFastInstance.conclude`, which takes the walk's answer as a plain
-- variable `n`.  Anyone building a further instance should start there
-- and not here.
------------------------------------------------------------------------

module WalkFast where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import WalkUnconditional using (cap)
open import WalkJumps
  using (IsPrime ; prime-0< ; prime-¬∣1 ; Strip ; strip)
open import CoprimeSplitting
  using ( IsPrimePower ; leastNonDivisor-isPrimePower
        ; primeDivisor ; two-primes→¬prime-power )
open import WalkBridge
  using (next ; next-2≤ ; next-lnd ; walk-step ; Jump)
open import WalkPrimePowers
  using (prime-power-is-jump ; pos-form ; ^-pos)

------------------------------------------------------------------------
-- 1.  `next m` is the least prime power above m.
------------------------------------------------------------------------

-- every install is a prime power: §(c)(⇒) applied to the step's own
-- certificate.  No ordering theorem is used.
next-isPP : (m : ℕ) → IsPrimePower (next m)
next-isPP m =
  leastNonDivisor-isPrimePower (cap m) (next m) (next-2≤ m) (next-lnd m)

module _ (m : ℕ) (1≤m : 1 ≤ m) where
  private
    W = walk-step m 1≤m

    j : ℕ
    j = W .fst

    next≡ : next m ≡ suc j
    next≡ = W .snd .fst

    m≤j : m ≤ j
    m≤j = W .snd .snd .fst

    skip : (i : ℕ) → m ≤ i → i < j → ¬ Jump i
    skip = W .snd .snd .snd .snd .snd

  next-> : m < next m
  next-> = subst (m <_) (sym next≡) (suc-≤-suc m≤j)

  -- nothing strictly between m and next m is a prime power
  next-least : (q : ℕ) → m < q → q < next m → ¬ IsPrimePower q
  next-least q m<q q<n ipp =
    skip i m≤i i<j (prime-power-is-jump i (subst IsPrimePower q≡si ipp))
    where
    pf : Σ[ i ∈ ℕ ] q ≡ suc i
    pf = pos-form q (<-weaken (≤<-trans 1≤m m<q))

    i : ℕ
    i = pf .fst

    q≡si : q ≡ suc i
    q≡si = pf .snd

    m≤i : m ≤ i
    m≤i = pred-≤-pred (subst (m <_) q≡si m<q)

    i<j : i < j
    i<j = pred-≤-pred (subst2 _<_ q≡si next≡ q<n)

-- THE EXCHANGE RATE.  To pin down `next m` you never touch cap m: you
-- exhibit a prime power beyond m and refute the finitely many numbers in
-- between.  Everything here has size ~q; cap m has size e^{ψ(m)}.
next-characterised :
  (m q : ℕ) → 1 ≤ m →
  IsPrimePower q → m < q →
  ((r : ℕ) → m < r → r < q → ¬ IsPrimePower r) →
  next m ≡ q
next-characterised m q 1≤m ippq m<q none with q ≟ next m
... | eq e    = sym e
... | lt q<n  = Empty.rec (next-least m 1≤m q m<q q<n ippq)
... | gt n<q  = Empty.rec (none (next m) (next-> m 1≤m) n<q (next-isPP m))

------------------------------------------------------------------------
-- 2.  Prime-power-hood is decidable, at size n.
--
--  n ≥ 2:  take a prime divisor p (bounded search), strip n at p to get
--          n = p^e · u with p ∤ u.  Then n is a prime power iff u = 1;
--          if u > 1 it has a prime divisor r ≠ p, and two distinct
--          primes divide n, which CoprimeSplitting already refutes.
------------------------------------------------------------------------

decPP≥2 : (n : ℕ) → 1 < n → Dec (IsPrimePower n)
decPP≥2 n 1<n = go (primeDivisor n 1<n)
  where
  0<n : 0 < n
  0<n = <-weaken 1<n

  go : Σ[ p ∈ ℕ ] (IsPrime p × (p ∣ n)) → Dec (IsPrimePower n)
  go (p , pp , p∣n) = go2 (strip p pp n n 0<n ≤-refl)
    where
    -- the two branches, taken as an argument rather than by `with`:
    -- u = 1 makes n = p^(e+1); u > 1 supplies a second prime.
    go3 : (e u : ℕ) → 0 < u → ((p ^ suc e) · u) ≡ n → ¬ (p ∣ u)
        → ((2 ≤ u) ⊎ (u < 2)) → Dec (IsPrimePower n)
    go3 e u 0<u peu ¬p∣u (inr u<2) =
      yes (p , suc e , pp , suc-≤-suc zero-≤ , pe≡n)
      where
      u≡1 : u ≡ 1
      u≡1 = ≤-antisym (pred-≤-pred u<2) 0<u

      pe≡n : (p ^ suc e) ≡ n
      pe≡n = sym (·-identityʳ (p ^ suc e))
           ∙ cong ((p ^ suc e) ·_) (sym u≡1)
           ∙ peu
    go3 e u 0<u peu ¬p∣u (inl 2≤u) =
      no (two-primes→¬prime-power n p r pp pr p≢r p∣n r∣n)
      where
      pd : Σ[ r ∈ ℕ ] (IsPrime r × (r ∣ u))
      pd = primeDivisor u 2≤u

      r : ℕ
      r = pd .fst

      pr : IsPrime r
      pr = pd .snd .fst

      r∣u : r ∣ u
      r∣u = pd .snd .snd

      u∣n : u ∣ n
      u∣n = subst (u ∣_) peu (∣-right (p ^ suc e))

      r∣n : r ∣ n
      r∣n = ∣-trans r∣u u∣n

      p≢r : ¬ (p ≡ r)
      p≢r e' = ¬p∣u (subst (_∣ u) (sym e') r∣u)

    -- e = 0 means n = u and p ∤ u, contradicting p ∣ n
    go2 : Strip p n → Dec (IsPrimePower n)
    go2 (zero , u , 0<u , peu , ¬p∣u) =
      Empty.rec (¬p∣u (subst (p ∣_) (sym (sym (·-identityˡ u) ∙ peu)) p∣n))
    go2 (suc e , u , 0<u , peu , ¬p∣u) =
      go3 e u 0<u peu ¬p∣u (splitℕ-≤ 2 u)

decIsPrimePower : (n : ℕ) → Dec (IsPrimePower n)
decIsPrimePower zero = no bad
  where
  bad : ¬ IsPrimePower 0
  bad (p , a , pp , 0<a , pa≡0) =
    ¬-<-zero (subst (0 <_) pa≡0 (^-pos p a (prime-0< p pp)))
decIsPrimePower (suc zero) = no bad
  where
  bad : ¬ IsPrimePower 1
  bad (p , a , pp , 0<a , pa≡1) =
    prime-¬∣1 p pp (subst (p ∣_) pa≡1 p∣pa)
    where
    pf : Σ[ b ∈ ℕ ] a ≡ suc b
    pf = pos-form a 0<a

    p∣pa : p ∣ (p ^ a)
    p∣pa = subst (λ x → p ∣ (p ^ x)) (sym (pf .snd)) (∣-left (p ^ (pf .fst)))
decIsPrimePower (suc (suc m)) =
  decPP≥2 (suc (suc m)) (suc-≤-suc (suc-≤-suc zero-≤))

------------------------------------------------------------------------
-- 3.  Turning a decision into a proof or a refutation BY COMPUTATION.
--     `refuteDec (decIsPrimePower 33) tt` type-checks exactly when the
--     kernel evaluates the decision to `no`; the `tt` is the evaluation.
------------------------------------------------------------------------

IsYes IsNo : {A : Type₀} → Dec A → Type₀
IsYes (yes _) = Unit
IsYes (no  _) = ⊥
IsNo  (yes _) = ⊥
IsNo  (no  _) = Unit

acceptDec : {A : Type₀} (d : Dec A) → IsYes d → A
acceptDec (yes p) _ = p
acceptDec (no  _) e = Empty.rec e

refuteDec : {A : Type₀} (d : Dec A) → IsNo d → ¬ A
refuteDec (yes _) e = Empty.rec e
refuteDec (no ¬p) _ = ¬p

-- the finitely many numbers strictly between m and suc (m + d)
noneIn : (m d : ℕ) →
         ((i : ℕ) → i < d → ¬ IsPrimePower (suc (m + i))) →
         (r : ℕ) → m < r → r < suc (m + d) → ¬ IsPrimePower r
noneIn m d h r m<r r<b = subst (λ z → ¬ IsPrimePower z) (sym r≡) (h t t<d)
  where
  t : ℕ
  t = m<r .fst

  r≡ : r ≡ suc (m + t)
  r≡ = sym (m<r .snd) ∙ +-suc t m ∙ cong suc (+-comm t m)

  t<d : t < d
  t<d = <-k+-cancel (pred-≤-pred (subst (_< suc (m + d)) r≡ r<b))


test-9 : IsPrimePower 9
test-9 = acceptDec (decIsPrimePower 9) tt

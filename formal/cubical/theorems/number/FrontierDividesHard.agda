{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FrontierDividesHard
--
-- Half (a) of the universal property `FrontierDivides` names:
--
--     frontier-divides-hard :
--       0 < m → m ≤ k → m ∣ prodOf (frontierList k)
--
-- Together with `FrontierDivides.frontier-divides` (the other half) this
-- is the universal property of `prodOf (frontierList k)` as the lcm of
-- 1 … k, which CLAUDE.md (absent from this repository) requires be stated that way because cubical
-- v0.5 has no LCM module.
--
-- ────────────────────────────────────────────────────────────────────
-- THE ASSEMBLY
--
-- Strong induction on m, peeled one prime at a time:
--
--   m > 1  ⟹  p prime with p ∣ m                    CoprimeSplitting
--   m = p^a · m'  with  p ∤ m'                       PFreePart
--   a ≤ logOf p k                                    ExponentBound
--   (p , logOf p k) ∈ frontierList k                 FrontierMember
--   p^a ∣ p^(logOf p k) ∣ prodOf (frontierList k)    §1, §2 below
--   m' ∣ prodOf (frontierList k)                     induction, m' < m
--   isGCD (p^a) m' 1                                 PrimeCofactorCoprime
--   ⟹ (p^a · m') ∣ prodOf                            FinCardinality.gauss
------------------------------------------------------------------------

module FrontierDividesHard where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using (_∣_ ; ∣-refl ; ∣-trans ; ∣-left ; ∣-right ; ∣-oneˡ ; m∣n→m≤n)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import FinCardinality using (gauss)
open import WalkJumps using (IsPrime)
open import FrontierCount using (Entry ; prodOf)
open import FrontierList using (frontierList ; logOf)
open import FrontierMember using (Mem ; frontier-member)
open import ExponentBound using (exponent-bounded ; ^-pos ; x<p·x)
open import PFreePart using (pFreePart)
open import PrimeCofactorCoprime using (prime-power-∤-coprime)
open import CoprimeSplitting using (primeDivisor)

------------------------------------------------------------------------
-- 1.  An entry divides the product of the list it is in
------------------------------------------------------------------------

entry-∣-prod : (p i : ℕ) (es : List Entry)
             → Mem (p , i) es → (p ^ i) ∣ prodOf es
entry-∣-prod p i []             m = Empty.rec m
entry-∣-prod p i ((q , j) ∷ es) m = go m
  where
  go : (((p , i) ≡ (q , j)) ⊎ Mem (p , i) es)
     → (p ^ i) ∣ ((q ^ j) · prodOf es)
  go (inl e) =
    subst (λ z → (fst z ^ snd z) ∣ ((q ^ j) · prodOf es)) (sym e)
          (∣-left (prodOf es))
  go (inr r) = ∣-trans (entry-∣-prod p i es r) (∣-right (q ^ j))

------------------------------------------------------------------------
-- 2.  Powers divide upward
------------------------------------------------------------------------

^-∣ : (p a b : ℕ) → a ≤ b → (p ^ a) ∣ (p ^ b)
^-∣ p a b (d , q) = subst (λ z → (p ^ a) ∣ (p ^ z)) q (climb d)
  where
  climb : (e : ℕ) → (p ^ a) ∣ (p ^ (e + a))
  climb zero    = ∣-refl refl
  climb (suc e) = ∣-trans (climb e) (∣-right p)

------------------------------------------------------------------------
-- 3.  Small arithmetic the peel needs
------------------------------------------------------------------------

private
  0<p-of : {p : ℕ} → 1 < p → 0 < p
  0<p-of 1<p = ≤-trans ≤-sucℕ 1<p

  -- 1 < p and 0 < p^e give 1 < p^(suc e), since p^(suc e) = p · p^e ≥ p
  1<pow : (p e : ℕ) → 1 < p → 1 < (p ^ (suc e))
  1<pow p e 1<p = <≤-trans 1<p step
    where
    step : p ≤ (p ^ (suc e))
    step = subst2 _≤_ (·-identityˡ p) (·-comm (p ^ e) p)
                  (≤-·k {k = p} (^-pos p e (0<p-of 1<p)))

  m≢0 : (n : ℕ) → 0 < n → ¬ (n ≡ 0)
  m≢0 n 0<n q = ¬-<-zero (subst (0 <_) q 0<n)

  -- 0 < a · b forces 0 < b
  posSnd : (a b : ℕ) → 0 < (a · b) → 0 < b
  posSnd a zero    0<ab = Empty.rec (¬-<-zero (subst (0 <_) (sym (0≡m·0 a)) 0<ab))
  posSnd a (suc b) _    = suc-≤-suc zero-≤

------------------------------------------------------------------------
-- 4.  THE HARD HALF, by fuelled strong induction on m
------------------------------------------------------------------------

hard-fuel : (fuel k m : ℕ) → 0 < m → m ≤ k → m ≤ fuel
          → m ∣ prodOf (frontierList k)
hard-fuel zero k m 0<m m≤k m≤f =
  Empty.rec (¬-<-zero (<≤-trans 0<m m≤f))
hard-fuel (suc f) k m 0<m m≤k m≤f = small (splitℕ-≤ m 1)
  where
  P : ℕ
  P = prodOf (frontierList k)

  small : ((m ≤ 1) ⊎ (1 < m)) → m ∣ P
  small (inl m≤1) = subst (_∣ P) (sym m≡1) (∣-oneˡ P)
    where
    m≡1 : m ≡ 1
    m≡1 = ≤-antisym m≤1 0<m
  small (inr 1<m) = peel (primeDivisor m 1<m)
    where
    peel : Σ[ p ∈ ℕ ] (IsPrime p × (p ∣ m)) → m ∣ P
    peel (p , pp , p∣m) = split (pFreePart p m (pp .fst) 0<m)
      where
      p≤k : p ≤ k
      p≤k = ≤-trans (m∣n→m≤n (m≢0 m 0<m) p∣m) m≤k

      -- the frontier entry for p, and everything below it
      entry∣ : (p ^ (logOf p k)) ∣ P
      entry∣ = entry-∣-prod p (logOf p k) (frontierList k)
                 (frontier-member p k pp p≤k)

      split : Σ[ a ∈ ℕ ] Σ[ m' ∈ ℕ ] ((m ≡ (p ^ a) · m') × (¬ (p ∣ m')))
            → m ∣ P
      split (a , m' , m≡ , p∤m') = subst (_∣ P) (sym m≡) product∣
        where
        0<m' : 0 < m'
        0<m' = posSnd (p ^ a) m' (subst (0 <_) m≡ 0<m)

        pa∣m : (p ^ a) ∣ m
        pa∣m = subst ((p ^ a) ∣_) (sym m≡) (∣-left m')

        a≤log : a ≤ logOf p k
        a≤log = exponent-bounded p k m a (pp .fst) 0<m m≤k pa∣m

        pa∣P : (p ^ a) ∣ P
        pa∣P = ∣-trans (^-∣ p a (logOf p k) a≤log) entry∣

        -- a ≡ 0 would make m' ≡ m, and then p ∤ m' contradicts p ∣ m
        m'<m : m' < m
        m'<m = shrink a refl
          where
          shrink : (e : ℕ) → e ≡ a → m' < m
          shrink zero e≡a =
            Empty.rec (p∤m' (subst (p ∣_) m'≡m p∣m))
            where
            m'≡m : m ≡ m'
            m'≡m = m≡ ∙ cong (λ z → (p ^ z) · m') (sym e≡a) ∙ ·-identityˡ m'
          shrink (suc e) e≡a =
            subst (m' <_) (sym m≡)
              (subst (λ z → m' < ((p ^ z) · m')) e≡a
                (x<p·x (p ^ (suc e)) m' (1<pow p e (pp .fst)) 0<m'))

        m'∣P : m' ∣ P
        m'∣P = hard-fuel f k m' 0<m'
                 (≤-trans (<-weaken m'<m) m≤k)
                 (pred-≤-pred (<≤-trans m'<m m≤f))

        product∣ : ((p ^ a) · m') ∣ P
        product∣ = gauss (p ^ a) m' P
                     (prime-power-∤-coprime p m' a pp p∤m')
                     pa∣P m'∣P

------------------------------------------------------------------------
-- 5.  THE STATEMENT
------------------------------------------------------------------------

frontier-divides-hard :
  (k m : ℕ) → 0 < m → m ≤ k → m ∣ prodOf (frontierList k)
frontier-divides-hard k m 0<m m≤k = hard-fuel m k m 0<m m≤k ≤-refl

------------------------------------------------------------------------
-- 6.  It runs.  prodOf (frontierList 8) = 840, and every m ≤ 8 divides
--     it — including 8, 7, 6 and 5, which is the content.
------------------------------------------------------------------------

eight-divides : 8 ∣ prodOf (frontierList 8)
eight-divides = frontier-divides-hard 8 8 (suc-≤-suc zero-≤) ≤-refl

seven-divides : 7 ∣ prodOf (frontierList 8)
seven-divides = frontier-divides-hard 8 7 (suc-≤-suc zero-≤) (1 , refl)

six-divides : 6 ∣ prodOf (frontierList 8)
six-divides = frontier-divides-hard 8 6 (suc-≤-suc zero-≤) (2 , refl)

five-divides : 5 ∣ prodOf (frontierList 8)
five-divides = frontier-divides-hard 8 5 (suc-≤-suc zero-≤) (3 , refl)

------------------------------------------------------------------------
-- 7.  The universal property, both halves.
--
--   (a)  every m ≤ k divides prodOf (frontierList k)        here
--   (b)  prodOf (frontierList k) divides every common multiple
--                                                  FrontierDivides §2
--
-- So `prodOf (frontierList k)` IS lcm(1 … k), stated by its universal
-- property because this lane has no LCM module — which is what
-- CLAUDE.md (absent from this repository) asks for, and it is now a theorem rather than a `refl` at
-- k = 8.
------------------------------------------------------------------------

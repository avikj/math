{-# OPTIONS --cubical --guardedness --safe #-}

------------------------------------------------------------------------
-- कुट्टक-समाप्ति — the pulveriser, and the fact that it stops.
--
-- TEXT AND DATE.  कुट्टक / *kuṭṭaka*, the pulveriser, and वल्ली / *vallī*,
-- the creeper of quotients: Āryabhaṭa, *Āryabhaṭīya*, Gaṇitapāda 32–33,
-- 499 CE; the vall worked out in Bhskara I, *ryabhayabhya*, 629 CE.
-- The instruction the method is named for is *śeṣaṃ rakṣa* — keep the
-- remainder — and recurse on it.
--
-- `Kuttaka` generates the vallī with a fuel constant
-- (`valli 200 137 60`) and proves nothing about it; every claim in that
-- module is `refl` on closed numerals.  It is the one module in the
-- machine named for a descent law and the one module whose descent is
-- not shown to descend.  This file removes the fuel: `valli` and
-- `kuttaka` are defined by well-founded recursion on the remainder, so
-- termination is the definition being accepted rather than a constant
-- chosen large enough.  `kuttaka` returns the last nonzero remainder
-- together with proofs that it divides both inputs, so the divisor and
-- its certificate are one object.
--
------------------------------------------------------------------------

module KuttakaSamapti_TheValliTerminatesWithoutFuel where

open import Prakriti using (divides)
open import Bhaga using (eucl)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Induction.WellFounded

-- ═══ a divisor of b and of the remainder is a divisor of a ═══
combine : (d q b r a : ℕ) → divides d b → divides d r
        → q · b + r ≡ a → divides d a
combine d q b r a (c₁ , e₁) (c₂ , e₂) e =
  q · c₁ + c₂ ,
  ( sym (·-distribʳ (q · c₁) c₂ d)
  ∙ cong (_+ (c₂ · d)) (sym (·-assoc q c₁ d) ∙ cong (q ·_) e₁)
  ∙ cong ((q · b) +_) e₂
  ∙ e )

module _ where
  open WFI (<-wellfounded)

  -- ═══ the vall, with no fuel ═══
  -- the recursion is on the second argument; `eucl` hands back r < d, and
  -- that inequality IS the descent.
  VGoal : ℕ → Type₀
  VGoal b = ℕ → List ℕ

  vstep : (b : ℕ) → ((b' : ℕ) → b' < b → VGoal b') → VGoal b
  vstep zero    _   _ = []
  vstep (suc m) rec a =
    let (q , r , r<sm , _) = eucl a (suc m) (suc-≤-suc zero-≤)
    in q ∷ rec r r<sm (suc m)

  valli : ℕ → ℕ → List ℕ
  valli a b = induction vstep b a

  -- ═══ the descent, carrying its certificate ═══
  -- the divisor and the two proofs that it divides come out together, so
  -- there is no second induction to keep in step with the first.
  KGoal : ℕ → Type₀
  KGoal b = (a : ℕ) → Σ[ d ∈ ℕ ] divides d a × divides d b

  kstep : (b : ℕ) → ((b' : ℕ) → b' < b → KGoal b') → KGoal b
  kstep zero    _   a = a , (1 , ·-identityˡ a) , (0 , refl)
  kstep (suc m) rec a =
    let (q , r , r<sm , e) = eucl a (suc m) (suc-≤-suc zero-≤)
        (d , d∣sm , d∣r)   = rec r r<sm (suc m)
    in d , combine d q (suc m) r a d∣sm d∣r e , d∣sm

  kuttaka : (a b : ℕ) → Σ[ d ∈ ℕ ] divides d a × divides d b
  kuttaka a b = induction kstep b a

  antya : ℕ → ℕ → ℕ
  antya a b = fst (kuttaka a b)

  -- the certificates, projected
  antya∣a : (a b : ℕ) → divides (antya a b) a
  antya∣a a b = fst (snd (kuttaka a b))

  antya∣b : (a b : ℕ) → divides (antya a b) b
  antya∣b a b = snd (snd (kuttaka a b))

-- ═══ pressed: ryabhaa's own pair, and the stra's numbers ═══
-- 137 = 2·60+17, 60 = 3·17+9, 17 = 1·9+8, 9 = 1·8+1, 8 = 8·1+0
_ : valli 137 60 ≡ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 8 ∷ []
_ = refl

_ : antya 137 60 ≡ 1
_ = refl

_ : antya 60 24 ≡ 12
_ = refl

_ : valli 60 24 ≡ 2 ∷ 2 ∷ []
_ = refl

-- and the certificate is a real quotient, not a flag: 24 = 2 · 12
_ : fst (antya∣b 60 24) ≡ 2
_ = refl

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- PairComposition
--
-- Brahmagupta's law, in the split (leg) coordinates of the pair field.
--
-- A pair is (u , v) : ℕ × ℕ with product u · v.  Working in legs
-- deliberately avoids ℕ-subtraction: over the split form the
-- Brahmagupta identity
--
--   (u₁² - v₁²-type norm) · (u₂² - ...) = (composed norm)
--
-- degenerates to the interchange law of multiplication, and BOTH
-- compositions — the straight one and the twisted one — carry the
-- product multiplicatively.  That is the "two composites" phenomenon:
-- one product, two lawful factorizations of the composed pair.
--
--   compose  (u₁,v₁) (u₂,v₂) = (u₁·u₂ , v₁·v₂)
--   compose' (u₁,v₁) (u₂,v₂) = (u₁·v₂ , v₁·u₂)
--
--   prod (compose  p q) ≡ prod p · prod q      (prodComp)
--   prod (compose' p q) ≡ prod p · prod q      (prodComp')
--
-- THE SEPARATOR.  The pairs with both legs prime are NOT a submonoid
-- of either composition: composing prime pairs manufactures composite
-- legs.  Checked witness: (3,5) ∘ (5,7) = (15,35), and a decidable
-- trial-division tester certifies isPrime 15 ≡ false, isPrime 35 ≡
-- false, while 3, 5, 7 test true — all by refl.
--
-- SEED (proved in PairCompositionSeed): for u₁,v₁,u₂,v₂ ≥ 2 every composed
-- leg is a product of two factors ≥ 2, hence composite; so no
-- composite of two ≥2-legged pairs is ever a prime pair.  Primality
-- is exactly the condition of falling out of every proper
-- composition.
--
-- Adjacent known result (notes/REPORT.md (absent from this repository),
-- Lemma 1.3): the integral isometry group of q(S,D)=S²−D² is {±I} — the
-- pair field has no
-- symmetries to move pairs around.  This module is the complementary
-- positive fact: what the pair field DOES have is a composition, and
-- the primes are precisely what escapes it.
------------------------------------------------------------------------

module PairComposition where

-- `comp` is the cubical homogeneous-composition primitive, re-exported
-- along several import paths (hiding it at one site does not clear the
-- name), so the pair composition below is called `compose`/`compose'`.
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

------------------------------------------------------------------------
-- §1  Pairs in leg coordinates, and the two compositions
------------------------------------------------------------------------

Pair : Type₀
Pair = ℕ × ℕ

prod : Pair → ℕ
prod (u , v) = u · v

-- Straight composition: legs multiply legwise.
compose : Pair → Pair → Pair
compose (u₁ , v₁) (u₂ , v₂) = (u₁ · u₂ , v₁ · v₂)

-- Twisted composition: legs multiply crosswise.
compose' : Pair → Pair → Pair
compose' (u₁ , v₁) (u₂ , v₂) = (u₁ · v₂ , v₁ · u₂)

------------------------------------------------------------------------
-- §2  The product law: both compositions are multiplicative
------------------------------------------------------------------------

-- The interchange (medial) law, a pure ·-assoc/·-comm shuffle.
interchange : (a b c d : ℕ) → (a · b) · (c · d) ≡ (a · c) · (b · d)
interchange a b c d =
    sym (·-assoc a b (c · d))
  ∙ cong (a ·_) (·-assoc b c d
                ∙ cong (_· d) (·-comm b c)
                ∙ sym (·-assoc c b d))
  ∙ ·-assoc a c (b · d)

-- Brahmagupta, straight: the composed pair carries the product of
-- the products.
prodComp : (p q : Pair) → prod (compose p q) ≡ prod p · prod q
prodComp (u₁ , v₁) (u₂ , v₂) = interchange u₁ u₂ v₁ v₂

-- Brahmagupta, twisted: so does the crosswise composition — the
-- "two composites of one product" in split form.
prodComp' : (p q : Pair) → prod (compose' p q) ≡ prod p · prod q
prodComp' (u₁ , v₁) (u₂ , v₂) =
    interchange u₁ v₂ v₁ u₂
  ∙ cong ((u₁ · v₁) ·_) (·-comm v₂ u₂)

------------------------------------------------------------------------
-- §3  The separator: a decidable primality tester
------------------------------------------------------------------------

-- divH c d n : with countdown c inside a block of size (suc d),
-- true iff (suc d) divides (n + (suc d) ∸ (suc c))-style alignment;
-- entered at divH zero d n it decides (suc d) ∣ n.  Total by
-- structural recursion on n.
private
  divH : ℕ → ℕ → ℕ → Bool
  divH zero    d zero    = true
  divH (suc _) d zero    = false
  divH zero    d (suc n) = divH d d n
  divH (suc c) d (suc n) = divH c d n

-- divides d n : d ∣ n, decided.  (divides 0 n is unused below; it
-- answers true only on n ≡ 0, which is the correct convention.)
divides : ℕ → ℕ → Bool
divides zero    zero    = true
divides zero    (suc _) = false
divides (suc d) n       = divH zero d n

-- noDiv k n : no divisor in {2, …, k} divides n.
private
  noDiv : ℕ → ℕ → Bool
  noDiv zero          n = true
  noDiv (suc zero)    n = true
  noDiv (suc (suc k)) n = not (divides (suc (suc k)) n) and noDiv (suc k) n

-- isPrime n : n ≥ 2 and no d with 2 ≤ d ≤ n−1 divides n.
isPrime : ℕ → Bool
isPrime zero          = false
isPrime (suc zero)    = false
isPrime (suc (suc k)) = noDiv (suc k) (suc (suc k))

------------------------------------------------------------------------
-- §4  The tester on the witnesses, by refl
------------------------------------------------------------------------

isPrime3 : isPrime 3 ≡ true
isPrime3 = refl

isPrime5 : isPrime 5 ≡ true
isPrime5 = refl

isPrime7 : isPrime 7 ≡ true
isPrime7 = refl

------------------------------------------------------------------------
-- §5  Not a submonoid: the checked witness
------------------------------------------------------------------------

-- Two prime pairs …
p35 : Pair
p35 = (3 , 5)

p57 : Pair
p57 = (5 , 7)

-- … whose composite is (15 , 35) …
compWitness : compose p35 p57 ≡ (15 , 35)
compWitness = refl

-- … and BOTH legs of the composite are composite.  The prime pairs
-- fall out of the composition monoid at the very first step.
notPrime15 : isPrime 15 ≡ false
notPrime15 = refl

notPrime35 : isPrime 35 ≡ false
notPrime35 = refl

-- The twisted composite (3·7 , 5·5) = (21 , 25) escapes too: neither
-- composition ever returns to the prime locus from ≥2-legged pairs.
compose'Witness : compose' p35 p57 ≡ (21 , 25)
compose'Witness = refl

notPrime21 : isPrime 21 ≡ false
notPrime21 = refl

notPrime25 : isPrime 25 ≡ false
notPrime25 = refl

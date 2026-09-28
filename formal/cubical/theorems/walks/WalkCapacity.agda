{-# OPTIONS --cubical --safe --no-import-sorts #-}

-- The walk's CAPACITY theorem (companion: WalkForcing).
--
-- Statement (WALK_FORCING_LAW.md (absent from this repository), "resolution of the costed fiber"):
--   any lossless sensor family whose addresses are all <= k has lcm
--   dividing lcm(1..k).
-- Hence e^psi(k) is the CAPACITY of frontier k -- the largest prefix any
-- family of that frontier can cover -- and the least section attains it
-- at every frontier (the walk's running self-certificate).
--
-- DESIGN NOTE (why this is stated by universal property).  Cubical v0.5
-- has no LCM module, and that absence improved the statement: capacity
-- is not about a particular construction of lcm, it is about the
-- universal property.  We quantify over ANY C that is an lcm of the
-- frontier range and ANY L that is an lcm of the family; the theorem
-- then needs no arithmetic at all, only membership plus the two
-- universal properties.  A construction-free capacity law.
--
-- Predicates are recursive type families rather than inductive ones:
-- indexed inductive families over lists need injectivity of _::_, which
-- cubical Agda does not provide.

module WalkCapacity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥)

-- list predicates, recursively (cubical-friendly)
All : (ℕ → Type) → List ℕ → Type
All Q []       = Unit
All Q (x ∷ xs) = Q x × All Q xs

_∈_ : ℕ → List ℕ → Type
x ∈ []       = ⊥
x ∈ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ ys)

All→∈ : (Q : ℕ → Type) (xs : List ℕ) {x : ℕ} → All Q xs → x ∈ xs → Q x
All→∈ Q (y ∷ ys) (q , _)  (inl p) = subst Q (sym p) q
All→∈ Q (y ∷ ys) (_ , qs) (inr m) = All→∈ Q ys qs m

-- the frontier range [1 .. k]
range1 : ℕ → List ℕ
range1 zero    = []
range1 (suc k) = suc k ∷ range1 k

-- common multiples and the lcm universal property, as predicates
CommonMultiple : List ℕ → ℕ → Type
CommonMultiple xs m = All (_∣ m) xs

IsLCM : List ℕ → ℕ → Type
IsLCM xs L = CommonMultiple xs L × ((m : ℕ) → CommonMultiple xs m → L ∣ m)

-- every address in [1,k] is a member of the frontier range
∈-range1 : (x k : ℕ) → 0 < x → x ≤ k → x ∈ range1 k
∈-range1 x zero    0<x x≤k = Empty.rec (¬-<-zero (<≤-trans 0<x x≤k))
∈-range1 x (suc k) 0<x x≤k with ≤-split x≤k
... | inl x<sk = inr (∈-range1 x k 0<x (pred-≤-pred x<sk))
... | inr x≡sk = inl x≡sk

-- THE CAPACITY THEOREM: a family of frontier <= k has lcm dividing the
-- lcm of the whole frontier range.  Membership + two universal
-- properties; no arithmetic.
capacity :
  (xs : List ℕ) (k : ℕ) (L C : ℕ) →
  IsLCM xs L → IsLCM (range1 k) C →
  All (λ x → (0 < x) × (x ≤ k)) xs →
  L ∣ C
capacity xs k L C (_ , L-least) (C-common , _) inRange =
  L-least C (mapAll xs inRange)
  where
  mapAll : (ys : List ℕ) → All (λ x → (0 < x) × (x ≤ k)) ys → All (_∣ C) ys
  mapAll []       _        = tt
  mapAll (y ∷ ys) (p , ps) =
    All→∈ (_∣ C) (range1 k) C-common (∈-range1 y k (p .fst) (p .snd))
    , mapAll ys ps

-- ATTAINMENT.  The bound above is a supremum, not merely an upper bound:
-- the frontier range is itself an admissible family of frontier k, so a
-- family achieving C exists.  Without this, `capacity` would only say
-- "no family exceeds C"; with it, C is the capacity.
range1-admissible : (k : ℕ) → All (λ x → (0 < x) × (x ≤ k)) (range1 k)
range1-admissible zero    = tt
range1-admissible (suc k) =
  ((k , +-comm k 1) , ≤-refl) , weaken k (range1 k) (range1-admissible k)
  where
  weaken : (j : ℕ) (ys : List ℕ) →
           All (λ x → (0 < x) × (x ≤ j)) ys →
           All (λ x → (0 < x) × (x ≤ suc j)) ys
  weaken j []       _        = tt
  weaken j (y ∷ ys) (p , ps) =
    (p .fst , ≤-suc (p .snd)) , weaken j ys ps

-- capacity is ATTAINED: some admissible family of frontier k has lcm
-- exactly C.  Stated existentially so the content is the witness, not a
-- reflexivity: `capacity` says no admissible family exceeds C, this says
-- one reaches it, and together they make C the capacity rather than a
-- bound.  The witness is the frontier range itself.
capacity-attained :
  (k C : ℕ) → IsLCM (range1 k) C →
  Σ[ F ∈ List ℕ ] (All (λ x → (0 < x) × (x ≤ k)) F) × IsLCM F C
capacity-attained k C isC = range1 k , range1-admissible k , isC

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ResidueGlue
--
-- The non-coprime gluing law of notes/MATHEMATICS_THAT_LEARNS.md (absent from this repository)
-- (`glue-remainders 4 6`, retired Python) made checkable at its
-- smallest honest instance:
--
--   m = 4, n = 6, gcd = 2, lcm = 12, working on Z/24.
--
-- Two jewels of Indra's net -- the residue-mod-4 view and the
-- residue-mod-6 view of a point of Z/24 -- reflect each other only
-- through their overlap:
--
--   (a) COMPATIBILITY.  For every x : Z/24 the two readings agree
--       after restriction to Z/gcd = Z/2:
--       pi42 (r4 x) == pi62 (r6 x).                   [compatibility]
--
--   (b) HIDDEN FIBER.  Perfect agreement of the views does not
--       reconstruct the point: 0 and 12 have equal joint readings
--       (0,0) yet are distinct in Z/24.  Reconstruction and
--       compatibility are different operations; the fiber of size
--       gcd = 2 stays hidden.        [collision, zero!=twelve,
--                                     hiddenFiber]
--
--   (c) EXACT RECONSTRUCTION AT THE LCM.  On Z/12 = Z/lcm the joint
--       reading is injective -- the two views determine the point
--       exactly up to lcm, never further.       [jointReading12-inj]
--
-- Everything is finite and closed, so every law is decided by
-- computation: the quantifiers are discharged by a boolean sweep
-- (allFin) whose truth is a single refl, then reflected into paths.
-- No holes, no postulates, imports from Cubical.* only.
--
-- NOTE ON THE REPRESENTATION OF Fin.  Fin is defined by recursion on
-- N,
--
--   Fin zero = empty, Fin (suc n) = Maybe (Fin n),
--
-- rather than as the indexed inductive family
--
--   data Fin : N -> Type where fz : Fin (suc n); fs : Fin n -> Fin (suc n)
--
-- Pattern matching on that family at a *literal* index (Fin 4, Fin 6)
-- forces the unifier to use injectivity of `suc` on the index, which
-- Cubical Agda does not support (UnsupportedIndexedMatch), so such
-- functions would not compute when applied to transports.  With the
-- recursive definition every index is out of the picture: all matching
-- is on Maybe, which is unindexed.  The pattern synonyms fz/fs keep the
-- notation.
------------------------------------------------------------------------

module ResidueGlue where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe; nothing; just)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Fin by recursion on ℕ: unindexed, so every pattern match below is a
-- plain match on Maybe and Cubical Agda supports all of them.

Fin : ℕ → Type₀
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern fz    = nothing
pattern fs x  = just x

toℕ : {n : ℕ} → Fin n → ℕ
toℕ {suc n} fz     = zero
toℕ {suc n} (fs x) = suc (toℕ x)

toℕ-inj : {n : ℕ} (x y : Fin n) → toℕ x ≡ toℕ y → x ≡ y
toℕ-inj {suc n} fz     fz     _ = refl
toℕ-inj {suc n} fz     (fs y) p = Empty.rec (znots p)
toℕ-inj {suc n} (fs x) fz     p = Empty.rec (snotz p)
toℕ-inj {suc n} (fs x) (fs y) p = cong just (toℕ-inj x y (injSuc p))

------------------------------------------------------------------------
-- Boolean equality on ℕ, sound and complete — the reflection engine.

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ-sound : (m n : ℕ) → eqℕ m n ≡ true → m ≡ n
eqℕ-sound zero    zero    _ = refl
eqℕ-sound zero    (suc n) p = Empty.rec (false≢true p)
eqℕ-sound (suc m) zero    p = Empty.rec (false≢true p)
eqℕ-sound (suc m) (suc n) p = cong suc (eqℕ-sound m n p)

eqFin : {n : ℕ} → Fin n → Fin n → Bool
eqFin x y = eqℕ (toℕ x) (toℕ y)

eqFin-sound : {n : ℕ} (x y : Fin n) → eqFin x y ≡ true → x ≡ y
eqFin-sound x y p = toℕ-inj x y (eqℕ-sound (toℕ x) (toℕ y) p)

eqFin-complete : {n : ℕ} (x y : Fin n) → x ≡ y → eqFin x y ≡ true
eqFin-complete x y p =
  subst (λ z → eqFin x z ≡ true) p (eqℕ-refl (toℕ x))

------------------------------------------------------------------------
-- Boolean connective lemmas.

and-left : (a b : Bool) → a and b ≡ true → a ≡ true
and-left true  b _ = refl
and-left false b p = Empty.rec (false≢true p)

and-right : (a b : Bool) → a and b ≡ true → b ≡ true
and-right true  b p = p
and-right false b p = Empty.rec (false≢true p)

implb : Bool → Bool → Bool
implb false _ = true
implb true  b = b

implb-elim : (a b : Bool) → implb a b ≡ true → a ≡ true → b ≡ true
implb-elim true  b p _ = p
implb-elim false b _ q = Empty.rec (false≢true q)

------------------------------------------------------------------------
-- Exhaustion: a boolean sweep over Fin n, with its elimination rule.
-- One refl on the sweep yields the pointwise law at every point.

allFin : {n : ℕ} → (Fin n → Bool) → Bool
allFin {zero}  f = true
allFin {suc n} f = f fz and allFin (λ x → f (fs x))

allFin-elim : {n : ℕ} (f : Fin n → Bool) → allFin f ≡ true
            → (x : Fin n) → f x ≡ true
allFin-elim {suc n} f p fz     = and-left (f fz) (allFin (λ x → f (fs x))) p
allFin-elim {suc n} f p (fs x) =
  allFin-elim (λ y → f (fs y)) (and-right (f fz) (allFin (λ y → f (fs y))) p) x

------------------------------------------------------------------------
-- The two views.  Residues are computed by iterating the cyclic
-- successor of ℤ/4 and ℤ/6 — an exact mod, no division needed.

cyc4 : Fin 4 → Fin 4
cyc4 fz                = fs fz
cyc4 (fs fz)           = fs (fs fz)
cyc4 (fs (fs fz))      = fs (fs (fs fz))
cyc4 (fs (fs (fs fz))) = fz

cyc6 : Fin 6 → Fin 6
cyc6 fz                          = fs fz
cyc6 (fs fz)                     = fs (fs fz)
cyc6 (fs (fs fz))                = fs (fs (fs fz))
cyc6 (fs (fs (fs fz)))           = fs (fs (fs (fs fz)))
cyc6 (fs (fs (fs (fs fz))))      = fs (fs (fs (fs (fs fz))))
cyc6 (fs (fs (fs (fs (fs fz))))) = fz

res4 : ℕ → Fin 4          -- res4 k = k mod 4
res4 zero    = fz
res4 (suc k) = cyc4 (res4 k)

res6 : ℕ → Fin 6          -- res6 k = k mod 6
res6 zero    = fz
res6 (suc k) = cyc6 (res6 k)

-- The two readings of a point of ℤ/24 (24 = m·n, the ambient cycle on
-- which the non-coprime story is honest: 24 ≠ lcm(4,6)).
r4 : Fin 24 → Fin 4
r4 x = res4 (toℕ x)

r6 : Fin 24 → Fin 6
r6 x = res6 (toℕ x)

-- Restriction of each view to the overlap ℤ/gcd(4,6) = ℤ/2.
π₄₂ : Fin 4 → Fin 2
π₄₂ fz                = fz
π₄₂ (fs fz)           = fs fz
π₄₂ (fs (fs fz))      = fz
π₄₂ (fs (fs (fs fz))) = fs fz

π₆₂ : Fin 6 → Fin 2
π₆₂ fz                          = fz
π₆₂ (fs fz)                     = fs fz
π₆₂ (fs (fs fz))                = fz
π₆₂ (fs (fs (fs fz)))           = fs fz
π₆₂ (fs (fs (fs (fs fz))))      = fz
π₆₂ (fs (fs (fs (fs (fs fz))))) = fs fz

------------------------------------------------------------------------
-- (a) COMPATIBILITY: the two jewels agree on their overlap, at every
-- one of the 24 points.  The sweep is one refl; reflection makes it a
-- path for each x.

compatible? : Fin 24 → Bool
compatible? x = eqFin (π₄₂ (r4 x)) (π₆₂ (r6 x))

compatSweep : allFin compatible? ≡ true
compatSweep = refl

compatibility : (x : Fin 24) → π₄₂ (r4 x) ≡ π₆₂ (r6 x)
compatibility x =
  eqFin-sound (π₄₂ (r4 x)) (π₆₂ (r6 x))
              (allFin-elim compatible? compatSweep x)

------------------------------------------------------------------------
-- (b) HIDDEN FIBER: the joint reading identifies 0 and 12, which are
-- distinct in ℤ/24.  Agreement of all views is not reconstruction —
-- the kernel (multiples of lcm = 12) has 24/12 = 2 elements.

jointReading : Fin 24 → Fin 4 × Fin 6
jointReading x = r4 x , r6 x

zero24 : Fin 24
zero24 = fz

twelve24 : Fin 24
twelve24 = fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))

collision : jointReading zero24 ≡ jointReading twelve24
collision = refl

zero≢twelve : ¬ zero24 ≡ twelve24
zero≢twelve p = znots (cong toℕ p)

-- The two facts packaged: a genuine failure of injectivity on ℤ/24.
hiddenFiber : Σ (Fin 24 × Fin 24)
                (λ p → (jointReading (fst p) ≡ jointReading (snd p))
                     × (¬ fst p ≡ snd p))
hiddenFiber = (zero24 , twelve24) , collision , zero≢twelve

------------------------------------------------------------------------
-- (c) EXACT RECONSTRUCTION AT THE LCM: on ℤ/12 the joint reading is
-- injective.  144 implications, swept by one refl, reflected into an
-- injectivity proof.  Together with (b): the pair of views determines
-- a point exactly modulo lcm(4,6) = 12, and not one step further.

jointReading12 : Fin 12 → Fin 4 × Fin 6
jointReading12 x = res4 (toℕ x) , res6 (toℕ x)

eqJoint12 : Fin 12 → Fin 12 → Bool
eqJoint12 x y = eqFin (res4 (toℕ x)) (res4 (toℕ y))
            and eqFin (res6 (toℕ x)) (res6 (toℕ y))

injSweep : allFin (λ x → allFin (λ y → implb (eqJoint12 x y) (eqFin x y)))
         ≡ true
injSweep = refl

jointReading12-inj : (x y : Fin 12)
                   → jointReading12 x ≡ jointReading12 y → x ≡ y
jointReading12-inj x y p =
  eqFin-sound x y
    (implb-elim (eqJoint12 x y) (eqFin x y)
      (allFin-elim (λ y' → implb (eqJoint12 x y') (eqFin x y'))
                   (allFin-elim
                     (λ x' → allFin (λ y' → implb (eqJoint12 x' y') (eqFin x' y')))
                     injSweep x)
                   y)
      (cong₂ _and_
        (eqFin-complete (res4 (toℕ x)) (res4 (toℕ y)) (cong fst p))
        (eqFin-complete (res6 (toℕ x)) (res6 (toℕ y)) (cong snd p))))

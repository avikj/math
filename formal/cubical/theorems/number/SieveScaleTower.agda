{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SieveScaleTower
--
-- DELTA 14, PROGRAM 14.75 — THE SCALE TOWER `O_z`, FINITE AND CONCRETE,
-- WITH THE HOMOTOPY FIBRES OF ITS CHARGE-FORGETTING OBSERVATIONS.
--
-- Delta 14 §G asks for an inverse tower
--
--     … → O_{n+1} → O_n → … → O_0
--
-- of "what is visible below scale z", with forgetting maps, and for the
-- homotopy fibres of the observations to be computed.  P14.39 warns
-- that adjacent lifts need not compose to a global lift.
--
-- This file builds the tower for `SieveFiber`'s model
-- (X = 30) at the four horizons z = 0, 2, 3, 5, i.e. at the four
-- initial segments of the primes below √30.  It is FINITE on purpose:
-- no inverse limit is constructed (§6).
--
--
-- THE TOWER
--
--     O₀ = Unit        o₀ n = tt                     nothing visible
--     O₁ = ℕ           o₁ n = v₂ n
--     O₂ = ℕ × ℕ       o₂ n = (v₂ n , v₃ n)
--     O₃ = ℕ × ℕ × ℕ   o₃ n = (v₂ n , v₃ n , v₅ n)   = SieveFiber.q
--
-- with `π` dropping the last coordinate.  Every square commutes by
-- `refl` (§2): the tower is strict, not merely coherent.
--
--
-- WHAT IS CHECKED (all exhaustive over the 30-element domain)
--
--   §2  `tower-commutes-*`, `o₃≡q`   the squares, and that the top of
--                                    the tower IS SieveFiber's `q`.
--   §3  `fibre₀ᵇ … fibre₃ᵇ`          THE HOMOTOPY FIBRES OF THE
--                                    OBSERVATIONS OVER THE TRIVIAL
--                                    STATE, as explicit lists:
--                                      z=0 : all 30
--                                      z=2 : the 15 odd numbers
--                                      z=3 : the 10 numbers coprime to 6
--                                      z=5 : the 8 numbers coprime to 30
--                                    Finite, strictly shrinking, and
--                                    never of constant size — which is
--                                    the tower form of `SieveFiber`'s
--                                    sizes 8/4/1 finding.
--       `25∉fibre₃`, `3∉fibre₂`      the shrinkage is STRICT, with
--                                    witnesses: 25 falls out at z=5,
--                                    3 falls out at z=3.
--
--   §4  `noChargeDescent₀ … ₂`       CHARGE-FORGETTING: the charge fails
--                                    to descend at EVERY level, not just
--                                    at the top.  1 and 7 are
--                                    indistinguishable at every horizon
--                                    of this tower and have opposite
--                                    charge.
--
--   §5  `level2ResidualNotABit`      THE RESIDUAL BIT IS A PROPERTY OF
--       `level1ResidualNotABit`      THE TOP OF THE TOWER ONLY.  At
--                                    z=3 the rough part of 25 is 25,
--                                    with Ω = 2; at z=2 the rough part
--                                    of 15 is 15, with Ω = 2.  So
--                                    "ε ∈ Bool" is horizon-relative, in
--                                    exactly the way `CLAUDE.md` (absent from this repository)'s
--                                    HOLOGRAM §7 corollary warns about.
--                                    the same relativity in X at fixed
--                                    z; this is the z-direction of it,
--                                    at fixed X.
--
--   §6  `s₃₂`, `s₂₁`, `sec-*`        P14.39, HONOURED.  Each forgetting
--       `liftNotObservational`       map HAS a section (append 0), and
--       `composedLiftNotObservational`  the sections compose.  They are
--                                    still not lifts of the OBSERVATION:
--                                    `s₃₂ (o₂ 25) = (0,0,0) ≠ (0,0,2) =
--                                    o₃ 25`.  Structural lifting at each
--                                    adjacent stage buys nothing about
--                                    the integers being observed, and
--                                    that is the concrete shape P14.39's
--                                    warning takes here.
--
--   §7  `tower*NoMonodromy`          EVERY LEVEL IS A SET, so Program
--                                    14.76's verdict applies at every
--                                    level of the tower and not only at
--                                    its top.  There is no z at which a
--                                    loop appears.
--
--
------------------------------------------------------------------------

module SieveScaleTower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; true≢false ; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import PerspectiveCore using (MonodromyOf)
open import SetBaseNoMonodromy using (setNoMonodromy)
open import SieveFiber as SF
  using ( ltᵇ ; eqᵇ ; eqᵇ→≡ ; eqBool ; _∈_ ; allOf ; allOf-sound ; memberOf
        ; domain ; stripF ; Ω ; charge ; q ; isSetVis ; Vis ; 1∈ ; 7∈ )

private
  variable
    ℓ : Level

  orSplit : (x y : Bool) → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
  orSplit true  y p = inl refl
  orSplit false y p = inr p

  memberOf→∈ : (xs : List ℕ) (n : ℕ) → memberOf xs n ≡ true → n ∈ xs
  memberOf→∈ []       n p = ⊥.rec (false≢true p)
  memberOf→∈ (x ∷ xs) n p with orSplit (eqᵇ x n) (memberOf xs n) p
  ... | inl s = inl (sym (eqᵇ→≡ x n s))
  ... | inr s = inr (memberOf→∈ xs n s)

------------------------------------------------------------------------
-- §1  The four levels and the four observations
------------------------------------------------------------------------

O₀ : Type
O₀ = Unit

O₁ : Type
O₁ = ℕ

O₂ : Type
O₂ = ℕ × ℕ

O₃ : Type
O₃ = ℕ × ℕ × ℕ

-- The successive strippings, exactly `SieveFiber.visRough`'s, exposed
-- one prime at a time so the intermediate stages become objects.
va : ℕ → ℕ × ℕ
va n = stripF n 2 n

vb : ℕ → ℕ × ℕ
vb n = stripF n 3 (snd (va n))

vc : ℕ → ℕ × ℕ
vc n = stripF n 5 (snd (vb n))

o₀ : ℕ → O₀
o₀ _ = tt

o₁ : ℕ → O₁
o₁ n = fst (va n)

o₂ : ℕ → O₂
o₂ n = fst (va n) , fst (vb n)

o₃ : ℕ → O₃
o₃ n = fst (va n) , fst (vb n) , fst (vc n)

-- What the sieve has not yet resolved at each horizon.
rough₁ : ℕ → ℕ
rough₁ n = snd (va n)

rough₂ : ℕ → ℕ
rough₂ n = snd (vb n)

rough₃ : ℕ → ℕ
rough₃ n = snd (vc n)

------------------------------------------------------------------------
-- §2  The forgetting maps, and that the tower is strict
------------------------------------------------------------------------

π₁₀ : O₁ → O₀
π₁₀ _ = tt

π₂₁ : O₂ → O₁
π₂₁ (x , _) = x

π₃₂ : O₃ → O₂
π₃₂ (x , y , _) = x , y

tower-commutes-10 : (n : ℕ) → π₁₀ (o₁ n) ≡ o₀ n
tower-commutes-10 n = refl

tower-commutes-21 : (n : ℕ) → π₂₁ (o₂ n) ≡ o₁ n
tower-commutes-21 n = refl

tower-commutes-32 : (n : ℕ) → π₃₂ (o₃ n) ≡ o₂ n
tower-commutes-32 n = refl

-- The top of the tower is `SieveFiber`'s quotient map itself.
o₃≡q : (n : ℕ) → o₃ n ≡ q n
o₃≡q n = refl

------------------------------------------------------------------------
-- §3  THE HOMOTOPY FIBRES, COMPUTED
--
-- The fibre of the observation over the trivial state, at each horizon,
-- as an explicit list verified against the observation by exhaustion.
------------------------------------------------------------------------

Fibre₁ : O₁ → Type
Fibre₁ v = Σ[ n ∈ ℕ ] ((n ∈ domain) × (o₁ n ≡ v))

Fibre₂ : O₂ → Type
Fibre₂ v = Σ[ n ∈ ℕ ] ((n ∈ domain) × (o₂ n ≡ v))

Fibre₃ : O₃ → Type
Fibre₃ v = Σ[ n ∈ ℕ ] ((n ∈ domain) × (o₃ n ≡ v))

-- z = 0: nothing is visible, so the fibre is the whole domain.
fibre₀ᵇ : allOf domain (λ n → memberOf domain n) ≡ true
fibre₀ᵇ = refl

-- z = 2: the 15 odd numbers.
fibre₁List : List ℕ
fibre₁List = 1 ∷ 3 ∷ 5 ∷ 7 ∷ 9 ∷ 11 ∷ 13 ∷ 15 ∷ 17 ∷ 19
           ∷ 21 ∷ 23 ∷ 25 ∷ 27 ∷ 29 ∷ []

chkFibre₁ : ℕ → Bool
chkFibre₁ n = eqBool (eqᵇ (o₁ n) 0) (memberOf fibre₁List n)

fibre₁ᵇ : allOf domain chkFibre₁ ≡ true
fibre₁ᵇ = refl

-- z = 3: the 10 numbers coprime to 6.
fibre₂List : List ℕ
fibre₂List = 1 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ 25 ∷ 29 ∷ []

eq₂ : O₂ → O₂ → Bool
eq₂ (x , y) (x' , y') = eqᵇ x x' and eqᵇ y y'

chkFibre₂ : ℕ → Bool
chkFibre₂ n = eqBool (eq₂ (o₂ n) (0 , 0)) (memberOf fibre₂List n)

fibre₂ᵇ : allOf domain chkFibre₂ ≡ true
fibre₂ᵇ = refl

-- z = 5: the 8 numbers coprime to 30.  This is `SieveFiber.fiberAt-1`
-- re-derived through the tower's own observation, which is how the
-- tower is checked to have `q` on top rather than merely to resemble it.
fibre₃List : List ℕ
fibre₃List = 1 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ 29 ∷ []

eq₃ : O₃ → O₃ → Bool
eq₃ (x , y , z) (x' , y' , z') = eqᵇ x x' and (eqᵇ y y' and eqᵇ z z')

chkFibre₃ : ℕ → Bool
chkFibre₃ n = eqBool (eq₃ (o₃ n) (0 , 0 , 0)) (memberOf fibre₃List n)

fibre₃ᵇ : allOf domain chkFibre₃ ≡ true
fibre₃ᵇ = refl

-- STRICTNESS, with witnesses.  25 survives to z = 3 and dies at z = 5;
-- 3 survives to z = 2 and dies at z = 3.  So the tower really coarsens
-- at every stage, and the fibre sizes 30 ⊃ 15 ⊃ 10 ⊃ 8 are strict.
25∈fibre₂ : Fibre₂ (0 , 0)
25∈fibre₂ = 25 , memberOf→∈ domain 25 refl , refl

25∉fibre₃ : ¬ (o₃ 25 ≡ (0 , 0 , 0))
25∉fibre₃ p = false≢true (cong (λ v → eqᵇ (snd (snd v)) 0) p)

3∈fibre₁ : Fibre₁ 0
3∈fibre₁ = 3 , memberOf→∈ domain 3 refl , refl

3∉fibre₂ : ¬ (o₂ 3 ≡ (0 , 0))
3∉fibre₂ p = false≢true (cong (λ v → eqᵇ (snd v) 0) p)

------------------------------------------------------------------------
-- §4  CHARGE-FORGETTING AT EVERY LEVEL
--
-- `SieveFiber.noChargeDescent` says the charge does not factor through
-- the TOP of the tower.  A fortiori it factors through no level, and
-- the same pair 1 ∼ 7 witnesses it at each: 1 and 7 are
-- indistinguishable at every horizon in this tower, and their charges
-- differ.
------------------------------------------------------------------------

noChargeDescent₀ :
  ¬ (Σ[ c ∈ (O₀ → Bool) ] ({n : ℕ} → n ∈ domain → c (o₀ n) ≡ charge n))
noChargeDescent₀ (c , agree) = false≢true (sym (agree 1∈) ∙ agree 7∈)

noChargeDescent₁ :
  ¬ (Σ[ c ∈ (O₁ → Bool) ] ({n : ℕ} → n ∈ domain → c (o₁ n) ≡ charge n))
noChargeDescent₁ (c , agree) = false≢true (sym (agree 1∈) ∙ agree 7∈)

noChargeDescent₂ :
  ¬ (Σ[ c ∈ (O₂ → Bool) ] ({n : ℕ} → n ∈ domain → c (o₂ n) ≡ charge n))
noChargeDescent₂ (c , agree) = false≢true (sym (agree 1∈) ∙ agree 7∈)

noChargeDescent₃ :
  ¬ (Σ[ c ∈ (O₃ → Bool) ] ({n : ℕ} → n ∈ domain → c (o₃ n) ≡ charge n))
noChargeDescent₃ (c , agree) = false≢true (sym (agree 1∈) ∙ agree 7∈)

------------------------------------------------------------------------
-- §5  THE RESIDUAL BIT IS A PROPERTY OF THE TOP LEVEL ONLY
--
-- `SieveFiber.roughSplit` proves that at z = 5 the rough part of every
-- n ≤ 30 is 1 or a single prime, so ε ∈ Bool.  One level down it is
-- false, and here is the witness rather than the assertion.
------------------------------------------------------------------------

level2ResidualNotABit :
  Σ[ n ∈ ℕ ] ((n ∈ domain) × (ltᵇ 1 (Ω (rough₂ n)) ≡ true))
level2ResidualNotABit = 25 , memberOf→∈ domain 25 refl , refl

level1ResidualNotABit :
  Σ[ n ∈ ℕ ] ((n ∈ domain) × (ltᵇ 1 (Ω (rough₁ n)) ≡ true))
level1ResidualNotABit = 15 , memberOf→∈ domain 15 refl , refl

-- …and at the top it IS one, on the same two witnesses, so the contrast
-- is between the levels and not between the numbers.
level3ResidualIsSmall :
  (ltᵇ 1 (Ω (rough₃ 25)) ≡ false) × (ltᵇ 1 (Ω (rough₃ 15)) ≡ false)
level3ResidualIsSmall = refl , refl

------------------------------------------------------------------------
-- §6  P14.39: ADJACENT LIFTS, AND WHAT THEY DO NOT BUY
--
-- Each forgetting map has a section — append a zero valuation — and the
-- sections compose.  Neither fact lifts an OBSERVATION: applying the
-- assembled section to what is visible at a coarse horizon does not
-- return what is visible at a fine one, because the section invents
-- `v = 0` where the integer has `v = 2`.
--
-- This is not a proof of P14.39 (which is a general warning about
-- towers); it is the concrete instance of it in this tower, and it is
-- the reason no inverse limit is built below.
------------------------------------------------------------------------

s₃₂ : O₂ → O₃
s₃₂ (x , y) = x , y , 0

s₂₁ : O₁ → O₂
s₂₁ x = x , 0

sec-32 : (v : O₂) → π₃₂ (s₃₂ v) ≡ v
sec-32 v = refl

sec-21 : (v : O₁) → π₂₁ (s₂₁ v) ≡ v
sec-21 v = refl

-- The composite is a section of the composite forgetting map.
sec-31 : (v : O₁) → π₂₁ (π₃₂ (s₃₂ (s₂₁ v))) ≡ v
sec-31 v = refl

-- And it is not an observational lift.
liftNotObservational : ¬ (s₃₂ (o₂ 25) ≡ o₃ 25)
liftNotObservational p = true≢false (cong (λ v → eqᵇ (snd (snd v)) 0) p)

composedLiftNotObservational : ¬ (s₃₂ (s₂₁ (o₁ 15)) ≡ o₃ 15)
composedLiftNotObservational p =
  true≢false (cong (λ v → eqᵇ (fst (snd v)) 0) p)

------------------------------------------------------------------------
-- §7  EVERY LEVEL OF THE TOWER IS A SET
--
-- Hence Program 14.76's verdict (`SetBaseNoMonodromy.setNoMonodromy`)
-- applies at every horizon: there is no z at which a nontrivial loop
-- appears for a charge family to be transported along.  The tower does
-- not supply the sheet exchange that C14.25 demands.
------------------------------------------------------------------------

isSetO₀ : isSet O₀
isSetO₀ = isSetUnit

isSetO₁ : isSet O₁
isSetO₁ = isSetℕ

isSetO₂ : isSet O₂
isSetO₂ = isSet× isSetℕ isSetℕ

isSetO₃ : isSet O₃
isSetO₃ = isSetVis

tower₀NoMonodromy :
  (F : O₀ → Type ℓ) (v : O₀) (p : v ≡ v) → MonodromyOf F v p → ⊥
tower₀NoMonodromy = setNoMonodromy isSetO₀

tower₁NoMonodromy :
  (F : O₁ → Type ℓ) (v : O₁) (p : v ≡ v) → MonodromyOf F v p → ⊥
tower₁NoMonodromy = setNoMonodromy isSetO₁

tower₂NoMonodromy :
  (F : O₂ → Type ℓ) (v : O₂) (p : v ≡ v) → MonodromyOf F v p → ⊥
tower₂NoMonodromy = setNoMonodromy isSetO₂

tower₃NoMonodromy :
  (F : O₃ → Type ℓ) (v : O₃) (p : v ≡ v) → MonodromyOf F v p → ⊥
tower₃NoMonodromy = setNoMonodromy isSetO₃

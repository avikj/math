{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SieveFiber
--
-- THE SIEVE FIBRE AT THE √X HORIZON, AND WHAT DOES AND DOES NOT
-- DESCEND ALONG IT.
--
-- This is the experiment named in `collab/upstream/raw/U0006.txt` (absent from this repository)
-- (the human owner's relayed proposal, §"The first Cubical Agda
-- experiment I'd actually run is tiny"), run as checked Agda for the
-- first time.  The proposal, in its own words:
--
--   "Take integers n ≤ X, represent each by its divisibility
--    information below √X, quotient integers having identical visible
--    state, and attach the residual bit ε_X(n) ∈ {0,1}.  Then formally
--    characterize the fiber q⁻¹(q(n)).  Ask whether (q(n), ε_X(n)) is
--    an informationally complete representation of factorization
--    charge.  Then remove ε.  The resulting failure of reconstruction
--    is our finite parity obstruction, represented as an actual fiber
--    rather than prose."
--
-- and the master question it poses:
--
--   "does the arithmetic quotient map admit a section?"
--
-- THE MODEL.  X = 30.  The primes at or below ⌊√30⌋ = 5 are 2, 3, 5.
-- The VISIBLE STATE of n is its exact valuation vector there,
--
--     q n = (v₂ n , v₃ n , v₅ n)  :  Vis,
--
-- computed here by actual repeated division, not by a table.  The
-- ROUGH PART `rough n` is what survives the stripping, and
-- ε n = (rough n ≠ 1) is the residual bit.
--
-- WHAT IS CHECKED (every `refl` below is a finite exhaustive
-- verification over the 30-element domain, performed by the
-- typechecker; §"Exact / certified symbolic computation is proof",
-- CLAUDE.md (absent from this repository)):
--
--   §4  `roughSplit`      ε REALLY IS ONE BIT.  For every n ≤ 30 the
--                         rough part is 1 or a single prime > 5.  This
--                         is the √X horizon fact — two primes above √X
--                         already exceed X — and it is what makes the
--                         residual datum a Bool rather than an integer.
--
--   §5  `factorises`      n = smooth n · rough n.
--       `fiberAt-1`       THE FIBRE, EXPLICITLY.
--       `fiberAt-2`         q⁻¹(0,0,0) ∩ [1,30] = {1,7,11,13,17,19,23,29}
--       `fiberAt-3`         q⁻¹(1,0,0) ∩ [1,30] = {2,14,22,26} = 2·{1,7,11,13}
--                           q⁻¹(1,1,1) ∩ [1,30] = {30}
--                         — a smooth representative together with its
--                         large-prime multiples that still fit under X.
--                         Sizes 8, 4, 1: the fibre is NOT of constant
--                         size and in particular never uniformly 2.
--                         The shape is q⁻¹(v) = {s} ∪ {s·p : √X < p ≤ X/s}
--                         for s = σ v, so #q⁻¹(v) = 1 + #{p : √X < p ≤ X/s}
--                         — which is 1 whenever s > ∈X.
--
--   §6  `chargeFactors`   THE POSITIVE ANSWER.  Liouville charge
--                         Ω(n) mod 2 factors through (q n , ε n):
--                           charge n = odd(v₂+v₃+v₅) ⊕ ε n.
--                         So (visible state, one bit) IS informationally
--                         complete FOR THE CHARGE.
--
--   §7  `noChargeDescent` THE NEGATIVE ANSWER.  Charge does NOT factor
--       `noChargeDescentQuot`  through q alone: 1 and 7 share the
--                         visible state (0,0,0) and have opposite
--                         charge.  Stated twice — once for a bare
--                         function on `Vis`, once for a function out of
--                         the actual set quotient `Dom / ∼`, so the
--                         obstruction is exhibited on the HIT the
--                         proposal asked for.
--
--   §8  `hasSection`      THE SECTION QUESTION, ANSWERED — AND
--       `noChargePreservingSection`  RE-POSED.  q DOES admit a section:
--                         σ(a,b,c) = 2^a·3^b·5^c picks the smooth point
--                         of each fibre, lands in the domain, satisfies
--                         q ∘ σ ∘ q = q, and always has ε = 0.  But NO
--                         section is charge-preserving.  The obstruction
--                         is therefore not to sectioning q; it is to
--                         sectioning q compatibly with charge.
--
--   §9  `noReconstruction`         AND THE BIT DOES NOT FIX IT.  7 and
--       `noReconstructionWithBit`  11 have the same visible state AND
--                         the same ε, so (q , ε) is not injective: it
--                         is complete for the CHARGE and not for the
--                         STATE.  This corrects the proposal's step 5,
--                         which asks for informational completeness
--                         without separating those two readings.
--
--   §10 `noFullPattern`   STEP 7 (k AFFINE FORMS) DOES NOT START HERE.
--       `jointFibreAt1`   For k = 2 with the forms (n , n+2), NO joint
--       `patternsAt1`     fibre at X = 30 realises all four residual
--                         patterns — the joint fibres have at most two
--                         elements.  The 2^k charge structure is not a
--                         property of a small finite fibre; it is a
--                         statement about the joint distribution as
--                         X → ∞, and the required X grows with k.
--
-- PRIOR ART IN THIS CORPUS, consumed and credited:
--     the fiberwise criterion for (q,c) to be an equivalence, and the
--     mod-6 witness 1 ∼ 7.  This file supplies the arithmetic model
--     that audit stated in prose and declared out of reach only in its
--     two extreme cases (indicator-only sieve; fully smooth numbers).
--     The √X-horizon model is the middle case, and it is the one the
--     owner named.
--   `formal/cubical/ProjectionChargeAudit.agda` — `noChargeDescent`
--     for the indiscrete relation on `Bool`.  §7 below is the same
--     argument with a real sieve map in place of the toy relation.
--   `formal/cubical/PMNoSection.agda` — the `allVec`/`sound` idiom for
--     letting the typechecker do a finite exhaustion.  `allOf`/
--     `allOf-sound` below is that idiom over an explicit list.
------------------------------------------------------------------------

module SieveFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_ ; isSetℕ)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; _⊕_ ; if_then_else_
        ; true≢false ; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; eq/)
open import Cubical.Data.Empty as ⊥ using (⊥)

------------------------------------------------------------------------
-- §1  Boolean arithmetic that computes
--
-- Everything below must normalise on closed numerals, because the
-- proofs ARE normalisation.  So the comparisons and the division are
-- written here, structurally, rather than imported: `Cubical.Data.Nat.Mod`
-- routes through `+induction`, and this file's whole method depends on
-- `refl` reducing.
------------------------------------------------------------------------

ltᵇ : ℕ → ℕ → Bool
ltᵇ zero    (suc _) = true
ltᵇ _       zero    = false
ltᵇ (suc m) (suc n) = ltᵇ m n

eqᵇ : ℕ → ℕ → Bool
eqᵇ zero    zero    = true
eqᵇ zero    (suc _) = false
eqᵇ (suc _) zero    = false
eqᵇ (suc m) (suc n) = eqᵇ m n

-- fuel-bounded division and remainder.  `d ≡ 0` cannot loop: the fuel
-- runs out.  For `d ≥ 1` the fuel `n` is always sufficient.
divF : ℕ → ℕ → ℕ → ℕ
divF zero    d n = zero
divF (suc f) d n = if ltᵇ n d then zero else suc (divF f d (n ∸ d))

modF : ℕ → ℕ → ℕ → ℕ
modF zero    d n = n
modF (suc f) d n = if ltᵇ n d then n else modF f d (n ∸ d)

infixl 7 _div_ _rem_

_div_ : ℕ → ℕ → ℕ
n div d = divF n d n

_rem_ : ℕ → ℕ → ℕ
n rem d = modF n d n

pow : ℕ → ℕ → ℕ
pow b zero    = 1
pow b (suc k) = b · pow b k

isOdd : ℕ → Bool
isOdd zero    = false
isOdd (suc n) = not (isOdd n)

------------------------------------------------------------------------
-- §2  Exhaustive verification over an explicit finite domain
--
-- The `PMNoSection` idiom: a Boolean check whose `refl` the typechecker
-- must normalise, plus a soundness lemma turning it into a statement
-- about every element.  Nothing is trusted except Agda's evaluator.
------------------------------------------------------------------------

-- Membership as a RECURSIVE FAMILY, not an indexed datatype: cubical
-- Agda declines to use constructor injectivity of `_∷_` for indexed
-- unification, so `here`/`there` matching would not compute.  A `⊎`
-- tower does the same job with ordinary case analysis.
infix 4 _∈_

_∈_ : ℕ → List ℕ → Type
n ∈ []       = ⊥
n ∈ (x ∷ xs) = (n ≡ x) ⊎ (n ∈ xs)

here : {n : ℕ} {xs : List ℕ} → n ∈ (n ∷ xs)
here = inl refl

there : {n m : ℕ} {xs : List ℕ} → n ∈ xs → n ∈ (m ∷ xs)
there = inr

allOf : List ℕ → (ℕ → Bool) → Bool
allOf []       f = true
allOf (x ∷ xs) f = f x and allOf xs f

private
  andL : (x y : Bool) → x and y ≡ true → x ≡ true
  andL true  y p = refl
  andL false y p = p

  andR : (x y : Bool) → x and y ≡ true → y ≡ true
  andR true  y     p = p
  andR false true  p = refl
  andR false false p = p

  orSplit : (x y : Bool) → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
  orSplit true  y p = inl refl
  orSplit false y p = inr p

allOf-sound : (xs : List ℕ) (f : ℕ → Bool)
            → allOf xs f ≡ true → {n : ℕ} → n ∈ xs → f n ≡ true
allOf-sound (x ∷ xs) f p {n} (inl e) =
  subst (λ z → f z ≡ true) (sym e) (andL (f x) (allOf xs f) p)
allOf-sound (x ∷ xs) f p     (inr m) =
  allOf-sound xs f (andR (f x) (allOf xs f) p) m

-- Boolean equality tests, and their reflection into paths.
eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool true  false = false
eqBool false true  = false

eqBool→≡ : (x y : Bool) → eqBool x y ≡ true → x ≡ y
eqBool→≡ true  true  p = refl
eqBool→≡ false false p = refl
eqBool→≡ true  false p = ⊥.rec (false≢true p)
eqBool→≡ false true  p = ⊥.rec (false≢true p)

eqᵇ→≡ : (m n : ℕ) → eqᵇ m n ≡ true → m ≡ n
eqᵇ→≡ zero    zero    p = refl
eqᵇ→≡ zero    (suc n) p = ⊥.rec (false≢true p)
eqᵇ→≡ (suc m) zero    p = ⊥.rec (false≢true p)
eqᵇ→≡ (suc m) (suc n) p = cong suc (eqᵇ→≡ m n p)

------------------------------------------------------------------------
-- §3  The model:  X = 30, horizon primes 2, 3, 5
------------------------------------------------------------------------

X : ℕ
X = 30

-- The visible sieve state: the exact valuations below √X.
Vis : Type
Vis = ℕ × ℕ × ℕ

isSetVis : isSet Vis
isSetVis = isSet× isSetℕ (isSet× isSetℕ isSetℕ)

eqVis : Vis → Vis → Bool
eqVis (a , b , c) (a' , b' , c') = eqᵇ a a' and (eqᵇ b b' and eqᵇ c c')

eqVis→≡ : (u v : Vis) → eqVis u v ≡ true → u ≡ v
eqVis→≡ (a , b , c) (a' , b' , c') p i =
  eqᵇ→≡ a a' pa i , eqᵇ→≡ b b' pb i , eqᵇ→≡ c c' pc i
  where
  pa = andL (eqᵇ a a') (eqᵇ b b' and eqᵇ c c') p
  rest = andR (eqᵇ a a') (eqᵇ b b' and eqᵇ c c') p
  pb = andL (eqᵇ b b') (eqᵇ c c') rest
  pc = andR (eqᵇ b b') (eqᵇ c c') rest

-- Strip the prime p out of n, returning (vₚ n , n / p^{vₚ n}).
stripF : ℕ → ℕ → ℕ → ℕ × ℕ
stripF zero    p n = zero , n
stripF (suc f) p n =
  if eqᵇ (n rem p) zero
    then (suc (fst rec) , snd rec)
    else (zero , n)
  where
  rec : ℕ × ℕ
  rec = stripF f p (n div p)

-- The visible state and the rough part, in one pass.
visRough : ℕ → Vis × ℕ
visRough n = (fst a , fst b , fst c) , snd c
  where
  a = stripF n 2 n
  b = stripF n 3 (snd a)
  c = stripF n 5 (snd b)

-- THE QUOTIENT MAP: n ↦ its divisibility information below √X.
q : ℕ → Vis
q n = fst (visRough n)

-- What the sieve does not see.
rough : ℕ → ℕ
rough n = snd (visRough n)

-- THE RESIDUAL BIT.
ε : ℕ → Bool
ε n = not (eqᵇ (rough n) 1)

-- The smooth representative of a visible state; §8's section.
σ : Vis → ℕ
σ (a , b , c) = pow 2 a · (pow 3 b · pow 5 c)

smooth : ℕ → ℕ
smooth n = σ (q n)

-- Ω(n), the number of prime factors with multiplicity, by trial
-- division.  Defined INDEPENDENTLY of the sieve decomposition — that
-- independence is what makes §6 a theorem rather than a definition.
omegaF : ℕ → ℕ → ℕ → ℕ
omegaF zero    d n = zero
omegaF (suc f) d n =
  if ltᵇ n 2 then zero
  else if ltᵇ n (d · d) then 1
  else if eqᵇ (n rem d) zero then suc (omegaF f d (n div d))
  else omegaF f (suc d) n

Ω : ℕ → ℕ
Ω n = omegaF (n + n) 2 n

-- The factorization charge: λ(n) = (−1)^{charge n}.
charge : ℕ → Bool
charge n = isOdd (Ω n)

-- The domain [1, X].
domain : List ℕ
domain = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10
       ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 20
       ∷ 21 ∷ 22 ∷ 23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ 29 ∷ 30 ∷ []

memberOf : List ℕ → ℕ → Bool
memberOf []       n = false
memberOf (x ∷ xs) n = eqᵇ x n or memberOf xs n

-- The three witnesses every negative result below turns on.
1∈ : 1 ∈ domain
1∈ = here

7∈ : 7 ∈ domain
7∈ = there (there (there (there (there (there here)))))

11∈ : 11 ∈ domain
11∈ = there (there (there (there (there (there (there (there
        (there (there here)))))))))

------------------------------------------------------------------------
-- §4  ε really is one bit
--
-- At the √X horizon the unresolved factorization tail is 1 or a single
-- prime, because two primes above √X already exceed X.  Checked, for
-- X = 30, on every n in the domain.  Without this the "residual bit"
-- would not be a bit.
--
-- The general form is proved, as a checked term, in
-- `NaturalMachine/RoughSplit.agda`:
--
--   roughSplitSqrt : (X n : ℕ) → 0 < n → n ≤ X
--                  → ((p : ℕ) → IsPrime p → p ∣ n → isqrt X < p)
--                  → (n ≡ 1) ⊎ IsPrime n
--
-- with `isqrt X` constructed there as the largest s with s · s ≤ X.
-- That module imports nothing from this one.
------------------------------------------------------------------------

chkRough : ℕ → Bool
chkRough n = eqᵇ (rough n) 1 or (eqᵇ (Ω (rough n)) 1 and ltᵇ 5 (rough n))

roughOneOrLargePrimeᵇ : allOf domain chkRough ≡ true
roughOneOrLargePrimeᵇ = refl

roughSplit : {n : ℕ} → n ∈ domain
           → (rough n ≡ 1) ⊎ ((Ω (rough n) ≡ 1) × (ltᵇ 5 (rough n) ≡ true))
roughSplit {n} m with orSplit (eqᵇ (rough n) 1)
                              (eqᵇ (Ω (rough n)) 1 and ltᵇ 5 (rough n))
                              (allOf-sound domain chkRough roughOneOrLargePrimeᵇ m)
... | inl s = inl (eqᵇ→≡ (rough n) 1 s)
... | inr s = inr ( eqᵇ→≡ (Ω (rough n)) 1
                      (andL (eqᵇ (Ω (rough n)) 1) (ltᵇ 5 (rough n)) s)
                  , andR (eqᵇ (Ω (rough n)) 1) (ltᵇ 5 (rough n)) s )

------------------------------------------------------------------------
-- §5  The fibre, explicitly
------------------------------------------------------------------------

chkFactor : ℕ → Bool
chkFactor n = eqᵇ n (smooth n · rough n)

factorisesᵇ : allOf domain chkFactor ≡ true
factorisesᵇ = refl

factorises : {n : ℕ} → n ∈ domain → n ≡ smooth n · rough n
factorises {n} m = eqᵇ→≡ n (smooth n · rough n)
                     (allOf-sound domain chkFactor factorisesᵇ m)

-- q⁻¹(0,0,0) ∩ [1,30] = {1} ∪ {p prime : 5 < p ≤ 30}.
fibre000 : List ℕ
fibre000 = 1 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ 29 ∷ []

chkFibre000 : ℕ → Bool
chkFibre000 n = eqBool (eqVis (q n) (0 , 0 , 0)) (memberOf fibre000 n)

fiberAt-1 : allOf domain chkFibre000 ≡ true
fiberAt-1 = refl

-- q⁻¹(1,0,0) ∩ [1,30] = 2 · {1,7,11,13} — the smooth representative
-- times the rough numbers that still fit under X.  The fibre shrinks
-- as the smooth part grows; it is never of constant size, and in
-- particular never of size 2.
fibre100 : List ℕ
fibre100 = 2 ∷ 14 ∷ 22 ∷ 26 ∷ []

chkFibre100 : ℕ → Bool
chkFibre100 n = eqBool (eqVis (q n) (1 , 0 , 0)) (memberOf fibre100 n)

fiberAt-2 : allOf domain chkFibre100 ≡ true
fiberAt-2 = refl

-- q⁻¹(1,1,1) ∩ [1,30] = {30}: a SINGLETON fibre.  Together with the
-- 8-element fibre above this refutes, for this model, the hypothesis of
-- equivalence iff every fibre has exactly two elements on which ε is a
-- bijection.  Here the fibres have 8, 4 and 1 elements, and on the
-- singleton ε is constantly `false`.  So the pair map is not an
-- equivalence, and its failure is not a near miss.
fibre111 : List ℕ
fibre111 = 30 ∷ []

chkFibre111 : ℕ → Bool
chkFibre111 n = eqBool (eqVis (q n) (1 , 1 , 1)) (memberOf fibre111 n)

fiberAt-3 : allOf domain chkFibre111 ≡ true
fiberAt-3 = refl

-- The fibre through n, as an actual type.
Fibre : Vis → Type
Fibre v = Σ[ n ∈ ℕ ] ((n ∈ domain) × (q n ≡ v))

-- Two elements of one fibre, exhibited.  This is the object the
-- proposal asked for in place of prose.
1∈Fibre000 : Fibre (0 , 0 , 0)
1∈Fibre000 = 1 , 1∈ , refl

7∈Fibre000 : Fibre (0 , 0 , 0)
7∈Fibre000 = 7 , 7∈ , refl

11∈Fibre000 : Fibre (0 , 0 , 0)
11∈Fibre000 = 11 , 11∈ , refl

------------------------------------------------------------------------
-- §6  THE POSITIVE RESULT
--
-- Visible state + one bit is informationally complete for the charge.
------------------------------------------------------------------------

chargeFromVis : Vis → Bool → Bool
chargeFromVis (a , b , c) e = isOdd (a + b + c) ⊕ e

chkCharge : ℕ → Bool
chkCharge n = eqBool (charge n) (chargeFromVis (q n) (ε n))

chargeFactorsᵇ : allOf domain chkCharge ≡ true
chargeFactorsᵇ = refl

chargeFactors : {n : ℕ} → n ∈ domain → charge n ≡ chargeFromVis (q n) (ε n)
chargeFactors {n} m = eqBool→≡ (charge n) (chargeFromVis (q n) (ε n))
                        (allOf-sound domain chkCharge chargeFactorsᵇ m)

------------------------------------------------------------------------
-- §7  THE NEGATIVE RESULT: remove ε and charge stops descending
--
-- 1 and 7 have the same visible state and opposite charge.  Twice:
-- as a bare factorisation through `Vis`, and through the set quotient
-- the proposal asked to be built.
------------------------------------------------------------------------

noChargeDescent :
  ¬ (Σ[ c̄ ∈ (Vis → Bool) ] ({n : ℕ} → n ∈ domain → c̄ (q n) ≡ charge n))
noChargeDescent (c̄ , agree) = false≢true (sym (agree 1∈) ∙ agree 7∈)

-- The same statement on the actual quotient type.
Dom : Type
Dom = Σ[ n ∈ ℕ ] (n ∈ domain)

_∼_ : Dom → Dom → Type
x ∼ y = q (fst x) ≡ q (fst y)

Sieve : Type
Sieve = Dom / _∼_

-- The visible state DOES descend — by construction, which is the
-- content-free half of the story.
visOn : Sieve → Vis
visOn = SQ.rec isSetVis (λ x → q (fst x)) (λ x y r → r)

-- The charge does not.
noChargeDescentQuot :
  ¬ (Σ[ c̄ ∈ (Sieve → Bool) ]
       ((x : Dom) → c̄ SQ.[ x ] ≡ charge (fst x)))
noChargeDescentQuot (c̄ , agree) =
  false≢true (sym (agree (1 , 1∈))
              ∙ cong c̄ (eq/ (1 , 1∈) (7 , 7∈) refl)
              ∙ agree (7 , 7∈))

------------------------------------------------------------------------
-- §8  THE SECTION QUESTION
--
-- "Does the arithmetic quotient map admit a section?"  YES, and that
-- is why the question has to be re-posed.  σ picks the smooth point of
-- each fibre; it lands in the domain, it is a genuine section of q,
-- and its residual bit is always 0.  What fails is not sectioning but
-- CHARGE-COMPATIBLE sectioning.
------------------------------------------------------------------------

chkSection : ℕ → Bool
chkSection n = eqVis (q (σ (q n))) (q n)
               and (memberOf domain (σ (q n)) and not (ε (σ (q n))))

hasSectionᵇ : allOf domain chkSection ≡ true
hasSectionᵇ = refl

-- q ∘ σ ∘ q ≡ q on the domain: σ is a section of q over its image.
hasSection : {n : ℕ} → n ∈ domain → q (σ (q n)) ≡ q n
hasSection {n} m =
  eqVis→≡ (q (σ (q n))) (q n)
    (andL (eqVis (q (σ (q n))) (q n))
          (memberOf domain (σ (q n)) and not (ε (σ (q n))))
          (allOf-sound domain chkSection hasSectionᵇ m))

-- …and no section of q respects the charge.  Note that this does not
-- mention σ: it rules out EVERY candidate, because 1 and 7 send the
-- same visible state to the same value while demanding opposite
-- charges.  This is the finite parity obstruction in its sharpest
-- available form for this model.
noChargePreservingSection :
  ¬ (Σ[ s ∈ (Vis → ℕ) ]
       ({n : ℕ} → n ∈ domain → charge (s (q n)) ≡ charge n))
noChargePreservingSection (s , agree) =
  false≢true (sym (agree 1∈) ∙ agree 7∈)

------------------------------------------------------------------------
-- §9  …AND THE BIT DOES NOT RESTORE THE STATE
--
-- (q , ε) is complete for the charge (§6) and incomplete for the
-- integer: 7 and 11 agree in both coordinates.  So "informationally
-- complete representation of factorization charge" is TRUE read as
-- charge and FALSE read as state, and the proposal's step 5 has to
-- choose.
------------------------------------------------------------------------

private
  7≢11 : ¬ (7 ≡ 11)
  7≢11 p = true≢false (cong (eqᵇ 7) p)

noReconstruction :
  ¬ (Σ[ s ∈ (Vis → ℕ) ] ({n : ℕ} → n ∈ domain → s (q n) ≡ n))
noReconstruction (s , agree) = 7≢11 (sym (agree 7∈) ∙ agree 11∈)

noReconstructionWithBit :
  ¬ (Σ[ s ∈ (Vis → Bool → ℕ) ]
       ({n : ℕ} → n ∈ domain → s (q n) (ε n) ≡ n))
noReconstructionWithBit (s , agree) = 7≢11 (sym (agree 7∈) ∙ agree 11∈)

-- The same failure, stated on the fibre object: two distinct points of
-- one fibre that agree on the residual bit.
pairMapNotInjective :
  Σ[ x ∈ Fibre (0 , 0 , 0) ] Σ[ y ∈ Fibre (0 , 0 , 0) ]
    ((ε (fst x) ≡ ε (fst y)) × (¬ (fst x ≡ fst y)))
pairMapNotInjective = 7∈Fibre000 , 11∈Fibre000 , refl , 7≢11

------------------------------------------------------------------------
-- §10  STEP 7 OF THE PROPOSAL, AND WHY IT DOES NOT START HERE
--
-- The proposal's last step: "generalize from one integer to k affine
-- forms, where the fiber should acquire the 2^k charge structure we've
-- already found."  The k = 2 instance of that, with the twin-prime pair
-- of forms (n , n+2), is checked here — and it comes out NEGATIVE at
-- this scale.
--
-- The joint visible state is (q n , q (n+2)) and the joint residual is
-- (ε n , ε (n+2)) ∈ 2².  For the fibre to "acquire 2² charge structure"
-- in any sense stronger than "the target has four elements", some joint
-- fibre must actually REALISE all four patterns.  `noFullPattern` says
-- no joint fibre at X = 30 does.  The reason is not subtle and is the
-- point: realising four patterns needs a joint fibre with at least four
-- elements, i.e. four n in [1,28] sharing both visible states, and at
-- X = 30 the joint fibres have at most two elements.
--
-- So the 2^k structure is not a property of a finite fibre at small X.
-- It is a statement about the joint distribution as X → ∞, and the X
-- needed grows with k.  Whatever step 7 is, it is not this computation
-- at this scale.
------------------------------------------------------------------------

domain28 : List ℕ
domain28 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10
         ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 20
         ∷ 21 ∷ 22 ∷ 23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ []

anyOf : List ℕ → (ℕ → Bool) → Bool
anyOf []       f = false
anyOf (x ∷ xs) f = f x or anyOf xs f

-- n and m have the same joint visible state for the forms (n , n+2).
sameJoint : ℕ → ℕ → Bool
sameJoint n m = eqVis (q n) (q m) and eqVis (q (n + 2)) (q (m + 2))

-- Is the residual pattern (a , b) realised somewhere in n's joint fibre?
hasPattern : ℕ → Bool → Bool → Bool
hasPattern n a b =
  anyOf domain28
    (λ m → sameJoint n m and (eqBool (ε m) a and eqBool (ε (m + 2)) b))

chkNoFull : ℕ → Bool
chkNoFull n =
  not (hasPattern n false false
       and (hasPattern n false true
            and (hasPattern n true false and hasPattern n true true)))

-- No joint fibre at X = 30 realises all four residual patterns.
noFullPattern : allOf domain28 chkNoFull ≡ true
noFullPattern = refl

-- The machinery is not vacuous: the patterns it does find, it finds.
-- n = 1 lies in the joint fibre {1 , 19}; (ε 1 , ε 3) = (false , false)
-- and (ε 19 , ε 21) = (true , true) are both realised there, and the
-- two mixed patterns are not.
jointFibreOf1 : List ℕ
jointFibreOf1 = 1 ∷ 19 ∷ []

chkJointFibre1 : ℕ → Bool
chkJointFibre1 m = eqBool (sameJoint 1 m) (memberOf jointFibreOf1 m)

jointFibreAt1 : allOf domain28 chkJointFibre1 ≡ true
jointFibreAt1 = refl

patternsAt1 : ( (hasPattern 1 false false ≡ true)
              × (hasPattern 1 true true   ≡ true) )
            × ( (hasPattern 1 false true  ≡ false)
              × (hasPattern 1 true false  ≡ false) )
patternsAt1 = (refl , refl) , (refl , refl)

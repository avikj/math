{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ChargePolynomialFinite
--
-- Theorem A §1.1 with the exact instance
-- tables of §1.5 and the verification inventory of §5; Theorem B §2.1
-- with the exhaustive three-case table of §2.2 and the SCOPE FENCE of
-- §2.4.1.  Source: D0026 §5.5 (divisor-lattice characteristic
-- polynomial) and §5.9 (Chen-envelope prime projector).
--
-- WHY THIS ROUTE AND NOT A VOCABULARY EXTENSION.
-- `interactive/patches/S4-certificate-vocabulary.md` (absent from this repository) §3.4 finds that
-- Ω, ω, μ² are *not* a vocabulary problem for the
-- Natural Machine.  Ω(n) = 1 + Ω(n / lpf(n)) has an argument that is not
-- a subterm of the left-hand side, so LPO cannot orient it at all
-- (`orient` returns `Nothing`), the bounded BFS has no structural
-- descent to follow, and adding `Omega` as a `Tm` constructor buys
-- nothing because no `Step` could ever fire on it.  S4 §3.4's
-- recommendation is option (ii): serve the D0026 §5 consumers by FINITE
-- INSTANCES checked by exhaustive `refl`, which `CLAUDE.md` (absent from this repository) rates as
-- proof outright ("a finite exhaustive verification ... produces
-- mathematical objects, not measurements").  That is what is below.
--
------------------------------------------------------------------------
-- THE ENCODING CHOICE, AND ITS COST — read this before the code
------------------------------------------------------------------------
--
-- S4 §3.4 rules out a general recursive Ω/ω/μ² *as machine vocabulary*.
-- Independently, a general recursive definition in Agda would have to be
-- either fuel-bounded (and then its correctness is a separate theorem) or
-- well-founded on a non-structural measure (and then it is a different
-- project).  The honest encoding for a finite certificate is therefore:
--
--     A NUMBER IS PRESENTED BY ITS FACTORIZATION TABLE.
--
--     Fact = List (ℕ × ℕ), where the entry `(p , e)` denotes the prime
--     power p^(1+e).  Storing the exponent MINUS ONE makes positivity
--     structural rather than a side condition, which is what lets §6's
--     classification lemma be a plain induction on the list.
--
-- On that presentation Ω, ω and μ² are *not* recursions on factorization
-- at all — they are a fold, a length, and a flat test:
--
--     Ω f = Σ exponents,   ω f = length f,   μ² f = [all exponents = 1].
--
-- THE COST, stated plainly.  The table is an INPUT.  Writing
-- `f360 = (2 , 2) ∷ (3 , 1) ∷ (5 , 0) ∷ []` asserts that 360 factors as
-- 2³·3²·5, and a reader must not be asked to take that on trust.  §3
-- therefore discharges the assertion four ways, all by kernel reduction:
--
--   (i)   `value f360 ≡ 360`         — the table multiplies out (refl);
--   (ii)  every base is prime        — exhaustive trial division (refl);
--   (iii) the bases are distinct     — (refl);
--   (iv)  Ω agrees with an INDEPENDENT trial-division Ω, imported from
--         `SieveFiber`, on every divisor of the table.
--
-- (i)–(iv) certify the tables.  So the precise reading of everything
-- below is: **these are theorems about factorization tables, together
-- with a four-way check that the three tables used are correct tables
-- for 12, 30 and 360.**
--
-- ℕ VERSUS ℤ.  Ω, ω, μ², `value` and every exhaustion flag live in ℕ.
-- The charge polynomial does not: μ takes the value −1, κ_r(30) = −1,
-- and the Chen functional evaluates to −1 outside the envelope, which is
-- precisely the content of §2.4.1's failure table.  So Φ, κ and `chen`
-- are ℤ-valued, over `Cubical.Data.Int`.  Only `ℤ`, `pos`, `negsuc`,
-- `_+_` and `_·_` are imported from it; negation and subtraction are
-- defined here (`negℤ`, `_∸ℤ_`) so that the module depends on as little
-- library naming as possible and so that every closed term visibly
-- reduces.
--
------------------------------------------------------------------------
-- CONTENTS
------------------------------------------------------------------------
--
--   §1  Bool, exhaustion    `allL` / `allL-sound`: the `PMNoSection`
--                           idiom (via `SieveFiber`) generalized from
--                           `List ℕ` to any `List A`, so that a Boolean
--                           `refl` becomes a statement about EVERY
--                           element rather than about a flag.
--
--   §2  Fact, Ω, ω, μ², μ   the factorization-table encoding, `value`,
--       splits, divisorsOf  and the complete enumeration of divisor
--                           SPLITS (d , n/d) — pairs, not divisors,
--                           because the Mbius sum needs the cofactor.
--
--   §3  f12 f30 f360        the three certified tables, with the four
--       value-*, wf-*       discharges (i)–(iv) of the header:
--       splits-multiply-*   value; well-formedness (prime, distinct);
--       Ω-agrees-*          every split multiplies back to n; and Ω
--                           against SieveFiber's independent trial
--                           division on all 6 / 8 / 24 divisors.
--
--   §4  Φraw, Φclosed       Theorem A as an IDENTITY, not a value: for
--       Φ-identity-*        each (n , t) the raw Mbius divisor sum
--       Φ-value-*           Σ_{d|n} μ(n/d) t^Ω(d) is computed
--       κVec-*              independently of the closed form and the two
--                           are shown equal by refl; the note's
--                           evaluation checksum is then a separate refl
--                           on the raw sum.  Instances are exactly the
--                           note's §5 inventory: Φ₁₂(2)=2, Φ₁₂(3)=12,
--                           Φ₃₀(2)=1, Φ₃₀(3)=8, Φ₃₆₀(2)=8,
--                           Φ₃₆₀(3)=216, Φ₃₆₀(5)=8000.  The coefficient
--                           vectors κ(12) = (0,1,−2,1),
--                           κ(30) = (−1,3,−3,1),
--                           κ(360) = (0,0,0,−1,3,−3,1) are certified as
--                           lists, again from the raw sum.
--
--   §5  ΦsumRaw ΦsumClosed  the fixed-charge PARTITION OF UNITY
--       pou-360-2           Σ_{d|n} Φ_d(t) = t^Ω(n), at the note's two
--       pou-12-3            checksums: Σ_{d|360} Φ_d(2) = 64 = 2^6 and
--                           Σ_{d|12} Φ_d(3) = 27 = 3^3.  Both are
--                           certified twice, once through the raw
--                           Mbius sums and once through the closed
--                           form, and the two are shown equal.
--
--   §6  classify1 classify2 Theorem B, and this is the one part that is
--       chen, primeInd      GENERAL rather than instance-wise.  Inside
--       chen-envelope       the encoding, "1 ≤ Ω(N) ≤ 2" is a statement
--                           about an exponent multiset, so the note's
--                           §2.2 three-row table is not an appeal to
--                           unique factorization but an INDUCTION on the
--                           list: Ω f = 1 forces f = [(p,1)], and
--                           Ω f = 2 forces f = [(p,2)] or [(p,1),(q,1)].
--                           `chen-envelope` then holds for every f in
--                           the envelope, for all primes, not for a
--                           sample.
--
--   §7  chen-fails-at-*     THE SCOPE FENCE, CERTIFIED.  §2.4.1 says a
--       chen-accidental-*   single stray p²q or pqr silently subtracts
--       chen-*-instance     one from the count and that the envelope
--                           check "is not optional hygiene; it is the
--                           theorem".  So the failure table is proved,
--                           not written: N = 1 gives +2, p²q gives −1,
--                           pqr gives −1 (all three general in the
--                           primes), each with an explicit refutation of
--                           agreement with the prime indicator; and
--                           p^(3+k) gives 0 = the indicator, flagged as
--                           the ACCIDENTAL agreement the note calls it.
--                           The two negative rows are then re-certified
--                           at the concrete integers already carried by
--                           this module: 12 = 2²·3 and 30 = 2·3·5.
--
------------------------------------------------------------------------
-- PRIOR ART IN THIS REPOSITORY
------------------------------------------------------------------------
--
--   `SieveFiber` — HAS a computable Ω already, by
--     fuel-bounded trial division over ℕ, together with the
--     `allOf`/`allOf-sound` exhaustion idiom (itself credited there to
--     `PMNoSection`).  It is REUSED here, not re-derived: §3's check
--     (iv) is exactly that import, and it is what makes the factorization
--     tables checked rather than asserted.  SieveFiber's own domain is
--     [1,30] at the √X horizon; it computes no ω, no μ, no divisor sum
--     and no characteristic polynomial, so nothing below duplicates it.
--   `ChargeGradedPeeling` — Ω as a dependent index on the
--     X = 30 domain, with `peelDrops : Ω(peel n) + 1 = Ω(n)`.  That is
--     the *grading* lane; it consumes SieveFiber's Ω for the same reason
--     this module does.  Disjoint content.
--   `ChargeCriterion` — the parity barrier as a decidable
--     test on odd-Ω queries.  Uses Ω abstractly, over an axiomatized
--     `Number`; proves nothing about divisor sums.  Disjoint.
--   `ChenTwoChargeProjector` — despite the name, this is
--     support geometry: `Charge = {one, two}`, commuting projections, and
--     a countermodel showing two cofinal faces need not meet.  The
--     present module is the arithmetic content the name
--     suggests and that module deliberately does not carry: μ² − (ω−1).
--     They are complementary and neither subsumes the other.
--   `ChargeGrading` — Ω as the ℕ-grading in the abstract
--     (Delta 15 §§15.6–15.7).  Disjoint.
--     a lens poset, with ω(N) counting the prime frontier.  Same lattice,
--     different functional (minimal sufficient charts, not μ * t^Ω).  It
--     is the closest prior art in the corpus and it does not overlap.
--   `interactive/patches/S4-certificate-vocabulary.md` (absent from this repository) §3.4 — the finding
--     quoted above.
--
------------------------------------------------------------------------
-- RIGOR BOUNDARY
------------------------------------------------------------------------
--
--   CERTIFIED, instance-wise, at exactly these n and nowhere else:
--     Theorem A (identity + evaluation) at n = 12, 30, 360;
--       t = 2 and 3 for n = 12 and n = 30, and t = 2, 3, 5 for n = 360.
--       These are precisely the entries the source note tabulates.
--     coefficient vectors κ at n = 12, 30, 360.
--     partition of unity at (n , t) = (360 , 2) and (12 , 3), and
--       nowhere else.
--
--   CERTIFIED, generally, but INSIDE THE ENCODING:
--     the envelope classification (§6) and hence Theorem B for every
--       factorization table with 1 ≤ Ω ≤ 2 — this quantifies over all
--       primes, not over a sample;
--     the failure rows of §2.4.1 for every p, q, r and every exponent
--       3 + k.
------------------------------------------------------------------------

module ChargePolynomialFinite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _∸_ ; snotz ; znots ; injSuc)
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Int
  using (ℤ ; pos ; negsuc)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_
        ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

-- The independent arithmetic, imported rather than re-derived.  `Ωtrial`
-- is SieveFiber's fuel-bounded trial-division Ω; `pow`, `eqᵇ`, `ltᵇ` and
-- `_rem_` are its computable primitives, written there structurally on
-- purpose so that `refl` reduces (see its §1).
open import SieveFiber
  using (eqᵇ ; eqᵇ→≡ ; ltᵇ ; pow ; _rem_)
  renaming (Ω to Ωtrial)

------------------------------------------------------------------------
-- §1  Exhaustion: a Boolean refl, promoted to a statement about every
--     element.
--
-- SieveFiber has this for `List ℕ`.  Everything below quantifies over
-- lists of factorizations and of split PAIRS, so it is restated here at
-- an arbitrary element type.  The `_∈L_` membership is a recursive
-- family rather than an indexed datatype for the reason SieveFiber
-- gives: cubical Agda declines constructor injectivity of `_∷_` for
-- indexed unification, so `here`/`there` matching would not compute.
------------------------------------------------------------------------

private
  andL : (x y : Bool) → x and y ≡ true → x ≡ true
  andL true  y p = refl
  andL false y p = p

  andR : (x y : Bool) → x and y ≡ true → y ≡ true
  andR true  y     p = p
  andR false true  p = refl
  andR false false p = p

  ⊎rec : {A B C : Type₀} → (A → C) → (B → C) → A ⊎ B → C
  ⊎rec g h (inl a) = g a
  ⊎rec g h (inr b) = h b

infix 4 _∈L_

_∈L_ : {A : Type₀} → A → List A → Type₀
x ∈L []       = ⊥
x ∈L (y ∷ ys) = (x ≡ y) ⊎ (x ∈L ys)

hereL : {A : Type₀} {x : A} {xs : List A} → x ∈L (x ∷ xs)
hereL = inl refl

thereL : {A : Type₀} {x y : A} {xs : List A} → x ∈L xs → x ∈L (y ∷ xs)
thereL = inr

allL : {A : Type₀} → List A → (A → Bool) → Bool
allL []       g = true
allL (x ∷ xs) g = g x and allL xs g

allL-sound : {A : Type₀} (xs : List A) (g : A → Bool)
           → allL xs g ≡ true → {x : A} → x ∈L xs → g x ≡ true
allL-sound (y ∷ ys) g p {x} (inl e) =
  subst (λ z → g z ≡ true) (sym e) (andL (g y) (allL ys g) p)
allL-sound (y ∷ ys) g p     (inr m) =
  allL-sound ys g (andR (g y) (allL ys g) p) m

mapL : {A B : Type₀} → (A → B) → List A → List B
mapL g []       = []
mapL g (x ∷ xs) = g x ∷ mapL g xs

concatMapL : {A B : Type₀} → (A → List B) → List A → List B
concatMapL g []       = []
concatMapL g (x ∷ xs) = g x ++ concatMapL g xs

-- [0 , 1 , … , n], increasing, so that κ below is indexed the way the
-- source note's §1.5 vectors are indexed (r = 0 upward).
countUp : ℕ → ℕ → List ℕ
countUp s zero    = s ∷ []
countUp s (suc k) = s ∷ countUp (suc s) k

range : ℕ → List ℕ
range n = countUp 0 n

------------------------------------------------------------------------
-- §2  The factorization-table encoding
--
-- `(p , e) : ℕ × ℕ` denotes the prime power p^(1+e).  The "minus one"
-- is what makes §6 an induction instead of an induction plus a side
-- condition; it is the only cleverness in the encoding and it is paid
-- for by having to write `(2 , 2)` where a reader expects `2³`.
------------------------------------------------------------------------

Fact : Type₀
Fact = List (ℕ × ℕ)

-- The integer the table names.
value : Fact → ℕ
value []             = 1
value ((p , e) ∷ f)  = pow p (suc e) ·ℕ value f

-- Ω: prime factors with multiplicity — a fold, not a recursion on n.
Ω : Fact → ℕ
Ω []             = 0
Ω ((p , e) ∷ f)  = suc e +ℕ Ω f

-- ω: distinct prime factors — a length.
ω : Fact → ℕ
ω []            = 0
ω ((p , e) ∷ f) = suc (ω f)

-- μ²: the squarefree indicator — a flat test on the exponent vector.
μ² : Fact → ℕ
μ² []                   = 1
μ² ((p , zero)  ∷ f)    = μ² f
μ² ((p , suc _) ∷ f)    = 0

-- Integers, with negation and subtraction defined here so that every
-- closed term below visibly reduces and the library surface stays at
-- {ℤ , pos , negsuc , _+_ , _·_}.
negℤ : ℤ → ℤ
negℤ (pos zero)    = pos zero
negℤ (pos (suc n)) = negsuc n
negℤ (negsuc n)    = pos (suc n)

infixl 6 _∸ℤ_
_∸ℤ_ : ℤ → ℤ → ℤ
x ∸ℤ y = x +ℤ negℤ y

infixr 8 _^ℤ_
_^ℤ_ : ℤ → ℕ → ℤ
t ^ℤ zero    = pos 1
t ^ℤ (suc k) = t ·ℤ (t ^ℤ k)

sumℤ : List ℤ → ℤ
sumℤ []       = pos 0
sumℤ (x ∷ xs) = x +ℤ sumℤ xs

-- μ: multiplicative, −1 per distinct prime, 0 on a repeated one.
μ : Fact → ℤ
μ []                = pos 1
μ ((p , zero)  ∷ f) = negℤ (μ f)
μ ((p , suc _) ∷ f) = pos 0

-- Prepend p^k, dropping the entry when k = 0 — so a table never carries
-- an exponent-zero entry and `ω` stays a length.
consP : ℕ → ℕ → Fact → Fact
consP p zero    f = f
consP p (suc k) f = (p , k) ∷ f

-- All (j , a ∸ j) for j = 0 … a.
splitsExp : ℕ → List (ℕ × ℕ)
splitsExp a = mapL (λ j → (j , a ∸ j)) (range a)

-- THE DIVISOR SPLITS: every pair (d , n/d).  The Mbius sum needs the
-- cofactor, so pairs are enumerated rather than divisors.
splits : Fact → List (Fact × Fact)
splits []            = ([] , []) ∷ []
splits ((p , e) ∷ f) =
  concatMapL
    (λ jk → mapL (λ de → ( consP p (fst jk) (fst de)
                         , consP p (snd jk) (snd de) ))
                 (splits f))
    (splitsExp (suc e))

divisorsOf : Fact → List Fact
divisorsOf f = mapL fst (splits f)

------------------------------------------------------------------------
-- §3  The three tables, and the four discharges of the encoding cost
------------------------------------------------------------------------

-- 12 = 2²·3,  30 = 2·3·5,  360 = 2³·3²·5.
f12 f30 f360 : Fact
f12  = (2 , 1) ∷ (3 , 0) ∷ []
f30  = (2 , 0) ∷ (3 , 0) ∷ (5 , 0) ∷ []
f360 = (2 , 2) ∷ (3 , 1) ∷ (5 , 0) ∷ []

-- (i) the tables multiply out to the integers they name.
value-12  : value f12  ≡ 12
value-12  = refl

value-30  : value f30  ≡ 30
value-30  = refl

value-360 : value f360 ≡ 360
value-360 = refl

-- (ii)+(iii) the bases are distinct primes.  Primality by exhaustive
-- trial division over every candidate divisor in [2 , n−1]; this is a
-- finite exhaustive verification, i.e. proof.
noFactorUpTo : ℕ → ℕ → Bool
noFactorUpTo n zero            = true
noFactorUpTo n (suc zero)      = true
noFactorUpTo n (suc (suc k))   =
  not (eqᵇ (n rem suc (suc k)) 0) and noFactorUpTo n (suc k)

isPrimeᵇ : ℕ → Bool
isPrimeᵇ n = ltᵇ 1 n and noFactorUpTo n (n ∸ 1)

bases : Fact → List ℕ
bases []            = []
bases ((p , e) ∷ f) = p ∷ bases f

memberᵇ : ℕ → List ℕ → Bool
memberᵇ n []       = false
memberᵇ n (x ∷ xs) = eqᵇ n x or memberᵇ n xs

distinctᵇ : List ℕ → Bool
distinctᵇ []       = true
distinctᵇ (x ∷ xs) = not (memberᵇ x xs) and distinctᵇ xs

wellFormedᵇ : Fact → Bool
wellFormedᵇ f = distinctᵇ (bases f) and allL (bases f) isPrimeᵇ

wf-12 : wellFormedᵇ f12 ≡ true
wf-12 = refl

wf-30 : wellFormedᵇ f30 ≡ true
wf-30 = refl

wf-360 : wellFormedᵇ f360 ≡ true
wf-360 = refl

-- Promoted out of the flag: every base of every table really is prime.
bases-prime-360 : {p : ℕ} → p ∈L bases f360 → isPrimeᵇ p ≡ true
bases-prime-360 =
  allL-sound (bases f360) isPrimeᵇ
    (andR (distinctᵇ (bases f360)) (allL (bases f360) isPrimeᵇ) wf-360)

-- (iv-a) every enumerated split really is a factorization of n.  This is
-- the check that `splits` is the divisor enumeration and not some other
-- list: d · (n/d) = n, for all 6 / 8 / 24 of them.
chkSplit : Fact → (Fact × Fact) → Bool
chkSplit f de = eqᵇ (value (fst de) ·ℕ value (snd de)) (value f)

splits-multiply-12 : allL (splits f12) (chkSplit f12) ≡ true
splits-multiply-12 = refl

splits-multiply-30 : allL (splits f30) (chkSplit f30) ≡ true
splits-multiply-30 = refl

splits-multiply-360 : allL (splits f360) (chkSplit f360) ≡ true
splits-multiply-360 = refl

-- and as a statement about each split rather than about a flag:
split-factorizes-360 : {de : Fact × Fact} → de ∈L splits f360
                     → value (fst de) ·ℕ value (snd de) ≡ value f360
split-factorizes-360 m =
  eqᵇ→≡ _ _ (allL-sound (splits f360) (chkSplit f360) splits-multiply-360 m)

-- (iv-b) THE INDEPENDENCE CHECK.  `Ω` above is a fold over a table;
-- `Ωtrial` is SieveFiber's trial division on the integer.  They are
-- written by different means and agree on every divisor of every table.
-- This is the note's own standard — "each computed twice: raw divisor
-- sum and closed form" — applied one level lower, to Ω itself.
chkΩ : Fact → Bool
chkΩ d = eqᵇ (Ωtrial (value d)) (Ω d)

Ω-agrees-12 : allL (divisorsOf f12) chkΩ ≡ true
Ω-agrees-12 = refl

Ω-agrees-30 : allL (divisorsOf f30) chkΩ ≡ true
Ω-agrees-30 = refl

Ω-agrees-360 : allL (divisorsOf f360) chkΩ ≡ true
Ω-agrees-360 = refl

Ω-independent-360 : {d : Fact} → d ∈L divisorsOf f360 → Ωtrial (value d) ≡ Ω d
Ω-independent-360 m = eqᵇ→≡ _ _ (allL-sound (divisorsOf f360) chkΩ Ω-agrees-360 m)

-- The three tables' invariants, for the reader (note §1.5): Ω, ω, and
-- the repeated-prime excess R = Ω − ω of the two-charge split.
Triple : Type₀
Triple = ℕ × ℕ × ℕ

invariants-12  : Path Triple (Ω f12  , ω f12  , Ω f12  ∸ ω f12 ) (3 , 2 , 1)
invariants-12  = refl

invariants-30  : Path Triple (Ω f30  , ω f30  , Ω f30  ∸ ω f30 ) (3 , 3 , 0)
invariants-30  = refl

invariants-360 : Path Triple (Ω f360 , ω f360 , Ω f360 ∸ ω f360) (6 , 3 , 3)
invariants-360 = refl

------------------------------------------------------------------------
-- §4  Theorem A as an identity
--
--     Φ_n(t) = Σ_{d|n} μ(n/d) t^Ω(d)   (raw, the definition)
--            = t^(Ω−ω) (t−1)^ω          (closed, the theorem)
--
-- The two sides are computed by disjoint code paths — `Φraw` never
-- mentions ω and `Φclosed` never mentions `splits` — so each
-- `Φ-identity-*` below certifies the IDENTITY, and the separate
-- `Φ-value-*` then records the note's checksum for the raw sum.  A
-- module that only checked the closed form's value would be certifying
-- an arithmetic evaluation, not a theorem.
------------------------------------------------------------------------

Φraw : Fact → ℤ → ℤ
Φraw f t = sumℤ (mapL (λ de → μ (snd de) ·ℤ (t ^ℤ Ω (fst de))) (splits f))

Φclosed : Fact → ℤ → ℤ
Φclosed f t = (t ^ℤ (Ω f ∸ ω f)) ·ℤ ((t ∸ℤ pos 1) ^ℤ ω f)

-- n = 12 = 2²·3.   Φ₁₂(t) = t³ − 2t² + t = t(t−1)².
Φ-identity-12-2 : Φraw f12 (pos 2) ≡ Φclosed f12 (pos 2)
Φ-identity-12-2 = refl

Φ-value-12-2 : Φraw f12 (pos 2) ≡ pos 2
Φ-value-12-2 = refl

Φ-identity-12-3 : Φraw f12 (pos 3) ≡ Φclosed f12 (pos 3)
Φ-identity-12-3 = refl

Φ-value-12-3 : Φraw f12 (pos 3) ≡ pos 12
Φ-value-12-3 = refl

-- n = 30 = 2·3·5.  Φ₃₀(t) = t³ − 3t² + 3t − 1 = (t−1)³.
Φ-identity-30-2 : Φraw f30 (pos 2) ≡ Φclosed f30 (pos 2)
Φ-identity-30-2 = refl

Φ-value-30-2 : Φraw f30 (pos 2) ≡ pos 1
Φ-value-30-2 = refl

Φ-identity-30-3 : Φraw f30 (pos 3) ≡ Φclosed f30 (pos 3)
Φ-identity-30-3 = refl

Φ-value-30-3 : Φraw f30 (pos 3) ≡ pos 8
Φ-value-30-3 = refl

-- n = 360 = 2³·3²·5.  Φ₃₆₀(t) = t⁶ − 3t⁵ + 3t⁴ − t³ = t³(t−1)³.
Φ-identity-360-2 : Φraw f360 (pos 2) ≡ Φclosed f360 (pos 2)
Φ-identity-360-2 = refl

Φ-value-360-2 : Φraw f360 (pos 2) ≡ pos 8
Φ-value-360-2 = refl

Φ-identity-360-3 : Φraw f360 (pos 3) ≡ Φclosed f360 (pos 3)
Φ-identity-360-3 = refl

Φ-value-360-3 : Φraw f360 (pos 3) ≡ pos 216
Φ-value-360-3 = refl

Φ-identity-360-5 : Φraw f360 (pos 5) ≡ Φclosed f360 (pos 5)
Φ-identity-360-5 = refl

Φ-value-360-5 : Φraw f360 (pos 5) ≡ pos 8000
Φ-value-360-5 = refl

-- Fixed-charge kernels κ_r(n) = Σ_{d|n , Ω(d)=r} μ(n/d), read off the
-- raw sum (never off the closed form's binomial expression), indexed
-- r = 0 upward exactly as the note's §5 inventory lists them.
κ : Fact → ℕ → ℤ
κ f r = sumℤ (mapL (λ de → if eqᵇ (Ω (fst de)) r then μ (snd de) else pos 0)
                   (splits f))

κVec : Fact → List ℤ
κVec f = mapL (κ f) (range (Ω f))

κVec-12 : κVec f12 ≡ pos 0 ∷ pos 1 ∷ negsuc 1 ∷ pos 1 ∷ []
κVec-12 = refl

κVec-30 : κVec f30 ≡ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ []
κVec-30 = refl

κVec-360 : κVec f360
         ≡ pos 0 ∷ pos 0 ∷ pos 0 ∷ negsuc 0 ∷ pos 3 ∷ negsuc 2 ∷ pos 1 ∷ []
κVec-360 = refl

------------------------------------------------------------------------
-- §5  The fixed-charge partition of unity,  Σ_{d|n} Φ_d(t) = t^Ω(n)
--
-- This is what makes κ_r consumable (note §1.4): it turns the
-- fixed-charge condition Ω(n) = r into a divisor sum.  Certified at the
-- note's two checksums, each computed twice — through the raw Möbius
-- sums and through the closed form — with the two shown equal.
------------------------------------------------------------------------

ΦsumRaw : Fact → ℤ → ℤ
ΦsumRaw f t = sumℤ (mapL (λ d → Φraw d t) (divisorsOf f))

ΦsumClosed : Fact → ℤ → ℤ
ΦsumClosed f t = sumℤ (mapL (λ d → Φclosed d t) (divisorsOf f))

-- Σ_{d|360} Φ_d(2) = 64 = 2^Ω(360) = 2⁶.
pou-360-2-raw : ΦsumRaw f360 (pos 2) ≡ pos 64
pou-360-2-raw = refl

pou-360-2-closed : ΦsumClosed f360 (pos 2) ≡ pos 64
pou-360-2-closed = refl

pou-360-2-agree : ΦsumRaw f360 (pos 2) ≡ ΦsumClosed f360 (pos 2)
pou-360-2-agree = refl

pou-360-2-charge : ΦsumRaw f360 (pos 2) ≡ pos 2 ^ℤ Ω f360
pou-360-2-charge = refl

-- Σ_{d|12} Φ_d(3) = 27 = 3^Ω(12) = 3³.
pou-12-3-raw : ΦsumRaw f12 (pos 3) ≡ pos 27
pou-12-3-raw = refl

pou-12-3-closed : ΦsumClosed f12 (pos 3) ≡ pos 27
pou-12-3-closed = refl

pou-12-3-agree : ΦsumRaw f12 (pos 3) ≡ ΦsumClosed f12 (pos 3)
pou-12-3-agree = refl

pou-12-3-charge : ΦsumRaw f12 (pos 3) ≡ pos 3 ^ℤ Ω f12
pou-12-3-charge = refl

------------------------------------------------------------------------
-- §6  Theorem B — the Chen-envelope prime projector, GENERALLY
--
--     1_P(N) = μ²(N) − (ω(N) − 1)      for all N with 1 ≤ Ω(N) ≤ 2.
--
-- The note proves this by an exhaustive three-case table and remarks
-- that "the envelope has exactly three shapes; a finite table is a
-- complete proof".  In the factorization-table encoding that remark
-- becomes an actual induction: the classification of exponent multisets
-- of total weight 1 and 2 is `classify1` / `classify2` below, proved by
-- case analysis on a list, using no arithmetic beyond `injSuc`.  So §6
-- is general in the primes — it is not three instances.
------------------------------------------------------------------------

chen : Fact → ℤ
chen f = pos (μ² f) ∸ℤ (pos (ω f) ∸ℤ pos 1)

primeInd : Fact → ℤ
primeInd f = if eqᵇ (Ω f) 1 then pos 1 else pos 0

Ω≡0→nil : (f : Fact) → Ω f ≡ 0 → f ≡ []
Ω≡0→nil []            _ = refl
Ω≡0→nil ((p , e) ∷ f) h = ⊥.rec (snotz h)

-- Ω = 1 forces a single prime to the first power.
classify1 : (f : Fact) → Ω f ≡ 1 → Σ[ p ∈ ℕ ] (f ≡ ((p , 0) ∷ []))
classify1 []                    h = ⊥.rec (znots h)
classify1 ((p , zero)    ∷ f)   h =
  p , cong (λ g → (p , 0) ∷ g) (Ω≡0→nil f (injSuc h))
classify1 ((p , suc e)   ∷ f)   h = ⊥.rec (snotz (injSuc h))

-- Ω = 2 forces p² or pq.  These are the note's rows two and three.
classify2 : (f : Fact) → Ω f ≡ 2
          → (Σ[ p ∈ ℕ ] (f ≡ ((p , 1) ∷ [])))
          ⊎ (Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] (f ≡ ((p , 0) ∷ (q , 0) ∷ [])))
classify2 []                          h = ⊥.rec (znots h)
classify2 ((p , zero) ∷ f)            h =
  inr (p , fst c , cong (λ g → (p , 0) ∷ g) (snd c))
  where
  c : Σ[ q ∈ ℕ ] (f ≡ ((q , 0) ∷ []))
  c = classify1 f (injSuc h)
classify2 ((p , suc zero) ∷ f)        h =
  inl (p , cong (λ g → (p , 1) ∷ g) (Ω≡0→nil f (injSuc (injSuc h))))
classify2 ((p , suc (suc e)) ∷ f)     h = ⊥.rec (snotz (injSuc (injSuc h)))

-- The three rows of note §2.2, each a kernel reduction and each general
-- in the primes involved.
chen-prime : (p : ℕ) → chen ((p , 0) ∷ []) ≡ primeInd ((p , 0) ∷ [])
chen-prime p = refl

chen-square : (p : ℕ) → chen ((p , 1) ∷ []) ≡ primeInd ((p , 1) ∷ [])
chen-square p = refl

chen-semiprime : (p q : ℕ)
               → chen ((p , 0) ∷ (q , 0) ∷ []) ≡ primeInd ((p , 0) ∷ (q , 0) ∷ [])
chen-semiprime p q = refl

transportChen : {f g : Fact} → f ≡ g
              → chen g ≡ primeInd g → chen f ≡ primeInd f
transportChen e h = cong chen e ∙ h ∙ sym (cong primeInd e)

-- THEOREM B, on the whole envelope.
chen-envelope : (f : Fact) → (Ω f ≡ 1) ⊎ (Ω f ≡ 2) → chen f ≡ primeInd f
chen-envelope f (inl h) =
  transportChen (snd c) (chen-prime (fst c))
  where
  c : Σ[ p ∈ ℕ ] (f ≡ ((p , 0) ∷ []))
  c = classify1 f h
chen-envelope f (inr h) =
  ⊎rec (λ z → transportChen (snd z) (chen-square (fst z)))
       (λ z → transportChen (snd (snd z)) (chen-semiprime (fst z) (fst (snd z))))
       (classify2 f h)

-- The envelope rows again at concrete integers, so the general statement
-- is anchored: 2 (prime), 4 = 2² (square), 6 = 2·3 (semiprime).
f2 f4 f6 : Fact
f2 = (2 , 0) ∷ []
f4 = (2 , 1) ∷ []
f6 = (2 , 0) ∷ (3 , 0) ∷ []

envelope-values : Path Triple (value f2 , value f4 , value f6) (2 , 4 , 6)
envelope-values = refl

chen-2 : chen f2 ≡ pos 1
chen-2 = refl

chen-4 : chen f4 ≡ pos 0
chen-4 = refl

chen-6 : chen f6 ≡ pos 0
chen-6 = refl

------------------------------------------------------------------------
-- §7  THE SCOPE FENCE, CERTIFIED
--
-- Note §2.4.1: "A single stray p²q or pqr in E silently subtracts one
-- from the count.  The envelope check is not optional hygiene; it is the
-- theorem."  A fence that is only written down is a comment.  Below it
-- is proved: each failure row is computed, and disagreement with the
-- prime indicator is exhibited as a refutation, not asserted.
------------------------------------------------------------------------

private
  -- Two discriminators, so that the refutations below depend on no
  -- library lemma about ℤ at all.
  signᵇ : ℤ → Bool
  signᵇ (pos _)    = true
  signᵇ (negsuc _) = false

  mag : ℤ → ℕ
  mag (pos n)    = n
  mag (negsuc _) = 0

  negsuc≢pos : (m n : ℕ) → ¬ (negsuc m ≡ pos n)
  negsuc≢pos m n h = false≢true (cong signᵇ h)

  pos2≢pos0 : ¬ (pos 2 ≡ pos 0)
  pos2≢pos0 h = snotz (cong mag h)

-- N = 1: the functional reads +2 where the indicator reads 0.
chen-at-one : chen [] ≡ pos 2
chen-at-one = refl

primeInd-at-one : primeInd [] ≡ pos 0
primeInd-at-one = refl

chen-fails-at-one : ¬ (chen [] ≡ primeInd [])
chen-fails-at-one = pos2≢pos0

-- N = p²q:  μ² = 0, ω = 2, so the functional reads −1.  General in p, q.
chen-at-p²q : (p q : ℕ) → chen ((p , 1) ∷ (q , 0) ∷ []) ≡ negsuc 0
chen-at-p²q p q = refl

primeInd-at-p²q : (p q : ℕ) → primeInd ((p , 1) ∷ (q , 0) ∷ []) ≡ pos 0
primeInd-at-p²q p q = refl

chen-fails-at-p²q : (p q : ℕ)
                  → ¬ (chen ((p , 1) ∷ (q , 0) ∷ [])
                       ≡ primeInd ((p , 1) ∷ (q , 0) ∷ []))
chen-fails-at-p²q p q h = negsuc≢pos 0 0 (sym (chen-at-p²q p q) ∙ h)

-- N = pqr:  μ² = 1, ω = 3, so the functional again reads −1.
chen-at-pqr : (p q r : ℕ) → chen ((p , 0) ∷ (q , 0) ∷ (r , 0) ∷ []) ≡ negsuc 0
chen-at-pqr p q r = refl

primeInd-at-pqr : (p q r : ℕ)
                → primeInd ((p , 0) ∷ (q , 0) ∷ (r , 0) ∷ []) ≡ pos 0
primeInd-at-pqr p q r = refl

chen-fails-at-pqr : (p q r : ℕ)
                  → ¬ (chen ((p , 0) ∷ (q , 0) ∷ (r , 0) ∷ [])
                       ≡ primeInd ((p , 0) ∷ (q , 0) ∷ (r , 0) ∷ []))
chen-fails-at-pqr p q r h = negsuc≢pos 0 0 (sym (chen-at-pqr p q r) ∙ h)

-- N = p^(3+k):  both sides are 0.  The note is explicit that this
-- AGREEMENT IS ACCIDENTAL — it is not evidence that the fence can be
-- moved, and it is recorded here in exactly that spirit.
chen-accidental-at-primePower :
  (p k : ℕ) → chen ((p , suc (suc k)) ∷ []) ≡ primeInd ((p , suc (suc k)) ∷ [])
chen-accidental-at-primePower p k = refl

chen-accidental-is-zero :
  (p k : ℕ) → chen ((p , suc (suc k)) ∷ []) ≡ pos 0
chen-accidental-is-zero p k = refl

-- And the two negative rows at the concrete integers this module already
-- carries: 12 = 2²·3 is a p²q, 30 = 2·3·5 is a pqr.  So the same three
-- tables that certify Theorem A also witness Theorem B's fence.
chen-12-instance : chen f12 ≡ negsuc 0
chen-12-instance = refl

chen-fails-at-12 : ¬ (chen f12 ≡ primeInd f12)
chen-fails-at-12 h = negsuc≢pos 0 0 (sym chen-12-instance ∙ h)

chen-30-instance : chen f30 ≡ negsuc 0
chen-30-instance = refl

chen-fails-at-30 : ¬ (chen f30 ≡ primeInd f30)
chen-fails-at-30 h = negsuc≢pos 0 0 (sym chen-30-instance ∙ h)

-- Both live strictly outside the envelope — Ω = 3 — which is the
-- hypothesis `chen-envelope` requires and which these two do not meet.
outside-envelope-12 : Ω f12 ≡ 3
outside-envelope-12 = refl

outside-envelope-30 : Ω f30 ≡ 3
outside-envelope-30 = refl

-- Lemma B2, the half of the fence that points the other way: a prime has
-- Ω = 1 and therefore always lies in the envelope, so intersecting any
-- family with the envelope condition discards no primes.  In this
-- encoding that is exactly `classify1` read backwards, and it is the
-- statement that makes the note's B3/B4 counts FULL counts.
primes-are-in-envelope : (p : ℕ) → (Ω ((p , 0) ∷ []) ≡ 1) ⊎ (Ω ((p , 0) ∷ []) ≡ 2)
primes-are-in-envelope p = inl refl

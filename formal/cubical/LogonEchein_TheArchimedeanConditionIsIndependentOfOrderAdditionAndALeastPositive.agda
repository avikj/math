{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- LogonEchein_TheArchimedeanConditionIsIndependentOfOrderAdditionAndALeastPositive
--
-- NAMING, STATED FIRST BECAUSE CLAUDE.md (absent from this repository)'s FILE-NAMING NOTE 2 REQUIRES IT.
--
-- The mathematics in this module originates with Eudoxus of Cnidus, as
-- transmitted in Euclid, *Elements* Book V, definition 4:
--
--   λόγον ἔχειν πρὸς ἄλληλα μεγέθη λέγεται, ἃ δύναται
--   πολλαπλασιαζόμενα ἀλλήλων ὑπερέχειν.
--   "Magnitudes are said to have a ratio to one another which are
--    capable, when multiplied, of exceeding one another."
--
-- The file therefore leads with the source's own term for the object,
-- λόγον ἔχειν / *logon echein*, "to have a ratio", transliterated.  Greek,
-- not , because Greek is the source language here.
--
-- What is claimed of Eudoxus: definition V.4 is his, it states a condition
-- on *which magnitudes are admitted*, and it is the hypothesis under which
-- Elements X.1 and the double-reduction proofs of Archimedes terminate.
--
------------------------------------------------------------------------
-- THE TRANSMISSION, NAMED.
--
-- Archimedes' *Ἔφοδος* / *Method of Mechanical Theorems*, addressed to
-- Eratosthenes, survives in one witness.  A 10th-century Byzantine
-- parchment copy was scraped, cut, refolded and overwritten as a Greek
-- Orthodox euchologion; the overwriting scribe signs and dates the new
-- book 14 April 1229.  Johan Ludvig Heiberg identified the undertext in
-- the Metochion of the Holy Sepulchre, Constantinople, in 1906, read what
-- he could with a magnifying glass and photographs, and published the
-- *Method* in 1906–1913.  The book then left the record; four pages
-- acquired forged Byzantine-style evangelist portraits at some point in
-- the 20th century.  It reappeared at Christie's New York, sold 29 October
-- 1998, and was deposited at the Walters Art Museum, Baltimore, where
-- multispectral and synchrotron X-ray fluorescence imaging, 1999–2008,
-- recovered text Heiberg could not read, including the part of Method
-- prop. 14 in which Archimedes compares collections that are both
-- infinite.
--
-- The *Method*'s own preface states the division this module depends on:
-- the mechanical procedure supplies the result, and *does not demonstrate
-- it* (οὐκ ἀποδεδειγμένον); the demonstration is the separate
-- double-reduction argument.  Two stages, not one, and the second is where
-- definition V.4 is consumed.
--
------------------------------------------------------------------------
-- THE OTHER DIRECTION.
--
-- Baudhyana *ulbastra*, c. 800 BCE.  1.9 (the square on the diagonal:
-- *drghacaturarasykay rajju prvamn tiryagmn ca yatpthagbhte
-- kurutastadubhaya karoti*) is an exact statement about areas.  2.12 gives
-- the *dvikara*, the side of the square of twice the area: *prama
-- tṛtīyena vardhayet tacca caturthenātmacatustriṃśonena* — increase the
-- measure by its third, and that third by its own fourth less the
-- thirty-fourth part of that, i.e. 1 + 1/3 + 1/(3·4) − 1/(3·4·34) =
-- 577/408.  The circle-squaring rules (*caturaśrāt parimaṇḍalam*, 2.9–2.10)
-- are of the same form: a construction and a stated numerical rule.
--
-- Plainly: **the ulbastras as transmitted do not state an exhaustion
-- argument.**  There is no sequence indexed by a step count, no bound on a
-- residual, and no reductio.  A one-shot rational rule with no error term
-- is not a double reduction, and reading one into it would be the
-- invented lineage note 2 forbids.  (This corpus already carries
-- `Dvikarani.agda` on 2.12.)
--
-- Jyehadeva, *Gaita-yukti-bh*, Malayalam, c. 1530, giving *yukti* for
-- results of Nlakaha's *Tantrasagraha* (1501).  Here the answer changes
-- and it changes on one specific point.  The *sakalita* derivations obtain
-- the sums of like powers with the residual explicitly identified as of
-- lower order for large index, and the *paridhi* series is given together
-- with the *antya-saskra*, the end-correction, in successive refinements
-- whose comparison is itself argued.  That is an **error term with a
-- stated criterion**, which the Greek exhaustion arguments do not produce:
-- a double reduction returns equality and returns no bound on the residual
-- of the n-th inscribed figure.
--
-- Plainly, and both halves are facts: the *Yuktibh* does not run the
-- double-reduction schema and does not state definition V.4's admission
-- condition; and it does state, quantitatively, what a double reduction
-- discards.
--
------------------------------------------------------------------------
-- WHAT IS CHECKED.
--
-- Definition V.4 read as a rule of a system:
--
--   R1  comparison is total (trichotomy);
--   R2  double reduction: ¬(x ⊏ y) → ¬(y ⊏ x) → x ≡ y;
--   R3  λόγον ἔχειν: for 𝟘 ⊏ x, some n ⊙ x exceeds y;
--   R4  addition is strictly monotone and cancellative;
--   R5  a least positive magnitude exists.
--
-- The lexicographically ordered pair monoid ℕ × ℕ satisfies R1, R2, R4, R5
-- and refutes R3.  Hence R3 is independent of the rest, and no ordering,
-- restriction, or precedence relation among R1, R2, R4, R5 can produce it.
--
-- The two magnitudes: Ω = (1 , 0) and ε = (0 , 1).  ε is positive and is
-- the least positive magnitude; no multiple of it reaches Ω.
--
-- Positive control, so the failure is located rather than blamed on the
-- construction: within a single level, R3 holds.
--
-- Euclid's magnitudes
-- admit taking a lesser from a greater (common notion 3, used throughout
-- Book V).  §9 checks that **this witness does not**: ε ⊏ Ω, and yet no z
-- satisfies ε ⊕ z ≡ Ω.  So `logon-echein-is-independent` is independence
-- over ordered commutative *monoids*, and that is all it is.
--
------------------------------------------------------------------------

module LogonEchein_TheArchimedeanConditionIsIndependentOfOrderAdditionAndALeastPositive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; snotz)
open import Cubical.Data.Nat.Properties using (inj-+m ; +-comm)
open import Cubical.Data.Nat.Order
  using ( _<_ ; _≤_ ; ¬-<-zero ; ¬m<m ; ≤-refl ; ≤<-trans ; <≤-trans
        ; <-+k ; ≤-+-≤ ; Trichotomy ; lt ; eq ; gt ; _≟_ )
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The magnitude system
------------------------------------------------------------------------

-- A magnitude is a pair: a level and an offset within that level.
Mag : Type₀
Mag = ℕ × ℕ

𝟘 Ω ε : Mag
𝟘 = 0 , 0
Ω = 1 , 0
ε = 0 , 1

infix 4 _⊏_
infixl 6 _⊕_

-- Lexicographic order, level dominant.
_⊏_ : Mag → Mag → Type₀
x ⊏ y = (fst x < fst y) ⊎ ((fst x ≡ fst y) × (snd x < snd y))

-- Componentwise addition.  No exchange rate between the levels: this is
-- the whole point, and it is what makes ε and Ω incommensurable.
_⊕_ : Mag → Mag → Mag
x ⊕ y = (fst x + fst y) , (snd x + snd y)

-- Repeated addition, which is the "multiplied" (πολλαπλασιαζόμενα) of
-- definition V.4.
_⊙_ : ℕ → Mag → Mag
zero  ⊙ x = 𝟘
suc n ⊙ x = x ⊕ (n ⊙ x)

------------------------------------------------------------------------
-- 2.  R2 — double reduction holds
--
-- This is the schema Archimedes closes with: the magnitude is neither
-- greater nor less, therefore equal.  It is checked here, in full, in the
-- structure that refutes R3 — which is the content of the module.
------------------------------------------------------------------------

double-reduction : (x y : Mag) → ¬ (x ⊏ y) → ¬ (y ⊏ x) → x ≡ y
double-reduction x y nxy nyx with fst x ≟ fst y
... | lt p = ⊥-rec (nxy (inl p))
... | gt p = ⊥-rec (nyx (inl p))
... | eq p with snd x ≟ snd y
...   | lt q = ⊥-rec (nxy (inr (p , q)))
...   | gt q = ⊥-rec (nyx (inr (sym p , q)))
...   | eq q = ΣPathP (p , q)

------------------------------------------------------------------------
-- 3.  R4 — addition is strictly monotone and cancellative
------------------------------------------------------------------------

⊕-strict-mono : (x y z : Mag) → x ⊏ y → (x ⊕ z) ⊏ (y ⊕ z)
⊕-strict-mono x y z (inl p)       = inl (<-+k p)
⊕-strict-mono x y z (inr (p , q)) = inr (cong (_+ fst z) p , <-+k q)

⊕-cancel : (x y z : Mag) → (x ⊕ z) ≡ (y ⊕ z) → x ≡ y
⊕-cancel x y z p =
  ΣPathP ( inj-+m (cong fst p) , inj-+m (cong snd p) )

------------------------------------------------------------------------
-- 4.  R5 — ε is the least positive magnitude
------------------------------------------------------------------------

-- Both members of the exotic pair are genuine positive magnitudes, and
-- they are comparable.  Without these three the failure of R3 in §5 would
-- be a statement about a degenerate pair rather than about the order.
ε-positive : 𝟘 ⊏ ε
ε-positive = inr (refl , ≤-refl)

Ω-positive : 𝟘 ⊏ Ω
Ω-positive = inl ≤-refl

ε-⊏-Ω : ε ⊏ Ω
ε-⊏-Ω = inl ≤-refl

ε-least-positive : (x : Mag) → 𝟘 ⊏ x → (ε ⊏ x) ⊎ (ε ≡ x)
ε-least-positive x (inl p)       = inl (inl p)
ε-least-positive x (inr (q , r)) with 1 ≟ snd x
... | lt p = inl (inr (q , p))
... | eq p = inr (ΣPathP (q , p))
... | gt p = ⊥-rec (¬m<m (≤<-trans r p))

------------------------------------------------------------------------
-- 5.  R3 fails — the exotic pair
--
-- Every multiple of ε stays at level 0.  Ω sits at level 1.  Nothing at
-- level 0 exceeds it, whatever its offset.
------------------------------------------------------------------------

-- Multiples of a level-0 magnitude stay at level 0, with offset scaling.
scale-level0 : (n b : ℕ) → n ⊙ (0 , b) ≡ (0 , n · b)
scale-level0 zero    b = refl
scale-level0 (suc n) b = cong ((0 , b) ⊕_) (scale-level0 n b)

-- No magnitude at level 0 exceeds Ω.
level0-never-exceeds-Ω : (m : ℕ) → ¬ (Ω ⊏ (0 , m))
level0-never-exceeds-Ω m (inl p)       = ¬-<-zero p
level0-never-exceeds-Ω m (inr (q , _)) = snotz q

-- Elements V def. 4 fails for the pair (ε , Ω): ε is positive, yet no
-- multiple of ε exceeds Ω.  ε and Ω do not have a ratio to one another.
logon-echein-fails : ¬ (Σ ℕ (λ n → Ω ⊏ (n ⊙ ε)))
logon-echein-fails (n , h) =
  level0-never-exceeds-Ω (n · 1) (subst (Ω ⊏_) (scale-level0 n 1) h)

------------------------------------------------------------------------
-- 6.  Positive control — R3 holds within one level
--
-- The failure is exactly the passage between levels, not a defect of the
-- construction.  Restricted to level 0, definition V.4 is satisfied.
------------------------------------------------------------------------

≤-·suc : (m k : ℕ) → m ≤ m · suc k
≤-·suc zero    k = ≤-refl
≤-·suc (suc m) k = ≤-+-≤ (k , +-comm k 1) (≤-·suc m k)

logon-echein-within-level0 :
  (b c : ℕ) → Σ ℕ (λ n → (0 , c) ⊏ (n ⊙ (0 , suc b)))
logon-echein-within-level0 b c =
  suc c ,
  subst ((0 , c) ⊏_) (sym (scale-level0 (suc c) (suc b)))
    (inr (refl , <≤-trans ≤-refl (≤-·suc (suc c) b)))

------------------------------------------------------------------------
-- 7.  The independence statement, packaged
--
-- R1, R2, R4, R5 all hold; R3 does not.  Therefore R3 is not derivable
-- from them, and no precedence relation among them yields it.  A rule
-- that restricts the domain of the others cannot be replaced by an
-- ordering of the others.
------------------------------------------------------------------------

logon-echein-is-independent :
    ((m n : ℕ) → Trichotomy m n)
  × ((x y : Mag) → ¬ (x ⊏ y) → ¬ (y ⊏ x) → x ≡ y)
  × ((x y z : Mag) → x ⊏ y → (x ⊕ z) ⊏ (y ⊕ z))
  × ((x y z : Mag) → (x ⊕ z) ≡ (y ⊕ z) → x ≡ y)
  × ((x : Mag) → 𝟘 ⊏ x → (ε ⊏ x) ⊎ (ε ≡ x))
  × (¬ (Σ ℕ (λ n → Ω ⊏ (n ⊙ ε))))
logon-echein-is-independent =
    _≟_
  , double-reduction
  , ⊕-strict-mono
  , ⊕-cancel
  , ε-least-positive
  , logon-echein-fails

------------------------------------------------------------------------
-- 8.  TWO CLAIMS REFUTED HERE
--
-- CLAIM A:
--   "A totally ordered, cancellative magnitude system with a least
--    positive element is Archimedean — repeated addition of the least
--    positive element eventually passes any magnitude."
--
-- It is true in ℕ, which is why it is tempting.  It is false, and the two
-- terms that kill it are `ε-least-positive` (ε *is* the least positive
-- magnitude) and `logon-echein-fails` (no multiple of ε reaches Ω), which
-- hold simultaneously in the same structure.  Packaged:
------------------------------------------------------------------------

claim-A-refuted :
    ((x : Mag) → 𝟘 ⊏ x → (ε ⊏ x) ⊎ (ε ≡ x))
  × (¬ (Σ ℕ (λ n → Ω ⊏ (n ⊙ ε))))
claim-A-refuted = ε-least-positive , logon-echein-fails

------------------------------------------------------------------------
-- CLAIM B:
--   "Double reduction is what carries an exhaustion proof; the
--    Archimedean condition is bookkeeping in front of it."
--
-- Also false, and killed by the same structure: `double-reduction` is a
-- checked term here, and `logon-echein-fails` holds beside it.  Double
-- reduction returns equality whenever both strict comparisons are refuted;
-- it supplies nothing that refutes them.  In this structure the two
-- comparisons Ω ⊏ n ⊙ ε are never refuted-and-refuted, they are simply
-- never established, and the proof does not start.
------------------------------------------------------------------------

claim-B-refuted :
    ((x y : Mag) → ¬ (x ⊏ y) → ¬ (y ⊏ x) → x ≡ y)
  × (¬ (Σ ℕ (λ n → Ω ⊏ (n ⊙ ε))))
claim-B-refuted = double-reduction , logon-echein-fails

------------------------------------------------------------------------
-- 9.  CLAIM C, REFUTED HERE
--
--   "ℕ × ℕ lex is a magnitude system in Euclid's sense, so §7 refutes the
--    classification for magnitudes."
--
-- Euclid takes a lesser magnitude from a greater throughout Book V
-- (common notion 3).  This witness does not admit that operation: ε ⊏ Ω
-- is checked above, and there is no z with ε ⊕ z ≡ Ω, because ε already
-- carries an offset that addition can never remove.
------------------------------------------------------------------------

no-difference-of-ε-from-Ω : ¬ (Σ Mag (λ z → (ε ⊕ z) ≡ Ω))
no-difference-of-ε-from-Ω (z , p) = snotz (cong snd p)

-- Together with ε-⊏-Ω this is the refutation: a lesser magnitude, a
-- greater magnitude, and no difference between them.
claim-C-refuted : (ε ⊏ Ω) × (¬ (Σ Mag (λ z → (ε ⊕ z) ≡ Ω)))
claim-C-refuted = ε-⊏-Ω , no-difference-of-ε-from-Ω

-- §7 is independence over ordered commutative monoids.
------------------------------------------------------------------------

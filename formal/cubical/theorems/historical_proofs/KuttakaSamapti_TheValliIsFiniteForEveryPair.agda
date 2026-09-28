{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- कुट्टक-समाप्तिः — वल्ली सर्वयुग्मे परिमिता ।
-- KuttakaSamapti — the vallī is finite, for every pair.
--
-- SOURCE AND DATE.  ĀRYABHAṬA, आर्यभटीयम्, गणितपादः ३२–३३ (499 CE): the
-- कुट्टक, the pulverizer, for the linear indeterminate equation; the
-- procedure spelled out step by step by BHĀSKARA I, आर्यभटीयभाष्यम् (629 CE).
-- Its rule is one sentence — divide, KEEP THE REMAINDER AND RECURSE ON IT,
-- and write each quotient into the ,ī—— the column.
--
-- THE SOURCE.  ryabhaa states the
-- procedure, and it terminates.
-- What the source supplies is the MEASURE, which
-- is the whole content of such a theorem: the thing kept at each step is the
-- remainder, and a remainder is smaller than what one divided by.  "शेषं रक्ष,
-- तत्रैव पुनरावर्तस्व" (AHIMSA_SUTRA_VISTARA §16, §17) is a descent as much as
-- it is an algorithm.  This module supplies the theorem that measure carries.
-- The European restatements of the same descent are later and are not named
-- here as its origin.
--
-- WHY THIS FILE EXISTS.  `Kuttaka.agda` proves the pulverizer's ARITHMETIC:
-- given a `Run a b g`, back-substitution up the vall yields x, y with
-- a·x + b·y ≡ g, and g divides a and b and is divisible by every common
-- divisor.  Its own header says how termination is handled, verbatim:
--
--     "Termination is carried by the evidence — the run IS Āryabhaṭa's
--      vallī, a checked trace — so no well-founded recursion is needed."
--
-- That is exact, and it is half the statement.  A `Run` is EVIDENCE THAT A
-- DESCENT HAPPENED, so every theorem in `Kuttaka.agda` is conditional on
-- someone handing over such evidence, and `Kuttaka.example` — the vallī of
-- (7,5) — is the only pair in this repository for which anyone ever did.
-- `CakravalaDescent.KuttakaCoprime.runToCoprime` inherits the same
-- conditionality: it turns a run into the Bézout pair the cakravāla's
-- cancellation consumes, for pairs a run is supplied for.
--
-- WHAT IS PROVED HERE.
-- Nothing below uses a ring solver.
--
--   वल्ली            the descent as evidence, over ℕ, CARRYING ITS MEASURE:
--                   each division step records `r < b` alongside
--                   `a ≡ q·b + r`.  `Kuttaka.Run` deliberately omits the
--                   ordering ("No r<b needed", its gcd section) because its
--                   theorems do not want it.  The ordering is exactly what
--                   termination does want, so it is put back here.
--   कुट्टक-समाप्तिः    TERMINATION.  For EVERY pair (a, b) of naturals a vallī
--                   exists, by well-founded recursion on b — Āryabhaṭa's own
--                   measure, not one imported for the occasion, since the
--                   recursive call is on the remainder and the remainder is
--                   what is smaller.  The proof COMPUTES: it is the
--                   pulverizer, not an existence argument about it.
--   दैर्घ्य-सीमा       THE BOUND, DERIVED.  The vallī of (a, b) has at most b
--                   rows.  Not measured, not fitted, not "observed to be
--                   short": an induction on the vall whose only input is the
--                   `r < b` each row carries.
--   शेष-वल्ली        THE REMAINDER OF A BOUNDED RUN.  A run given f rows of
--                   fuel either finishes — handing back a whole vallī — or
--                   STATES THE PAIR IT DID NOT REACH, with the partial column
--                   that got there.  The type has two constructors and no
--                   third, so a truncated run CANNOT fail to report its
--                   remainder.  The discipline the corpus learned on
--                   Mdhava's series (a truncated series with a quantified
--                   remainder is an algorithm; without it, a curiosity) is
--                   here made unavoidable by typing rather than remembered.
--   पर्याप्तम्        THE FUEL IS ENOUGH.  With f = b the bounded run always
--                   lands in the finished constructor.  A cap with a proof
--                   that it is never reached is a bound; a cap without one is
--                   an unwritten defect.
--   सेतुः            THE BRIDGE.  A ℕ vallī IS a `Kuttaka.Run` over ℤ, so
--                   every theorem in `Kuttaka.agda` becomes unconditional:
--   बेजु-सर्वत्र      for EVERY pair of naturals there are x, y with
--                   pos a · x + pos b · y ≡ pos g, with g the terminal value,
--   महत्तम-सर्वत्र    and g divides both and is divisible by every common
--                   divisor — the gcd, for every pair, constructively.
------------------------------------------------------------------------

module KuttakaSamapti_TheValliIsFiniteForEveryPair where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; ·-comm)
open import Cubical.Data.Nat.Order
  using (_<_ ; _≤_ ; <-wellfounded ; ≤-trans ; ≤-refl ; suc-≤-suc ; zero-≤
        ; pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.Nat.Mod
  using (mod< ; ≡remainder+quotient ; remainder_/_ ; quotient_/_)
open import Cubical.Induction.WellFounded
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.List using (List ; [] ; _∷_)

open import Cubical.Data.Int using (ℤ ; pos)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Properties using (pos+ ; pos·pos)

open import Kuttaka
  using (Run ; stop ; div ; bezout ; gcdDivides ; gcdGreatest ; _∣_)

------------------------------------------------------------------------
-- १ · वल्ली — the descent as evidence, carrying its measure.
--
-- One constructor per division of the pulverizer.  `विश्रामः` is the row
-- where the remainder has become 0 and the column stops; `छेदः` is one
-- division a = q·b + r, and it records BOTH the equation and `r < b`.
--
-- The ordering is the only difference from `Kuttaka.Run`, and it is the
-- whole subject of this file.
------------------------------------------------------------------------

data वल्ली : ℕ → ℕ → ℕ → Type where
  विश्रामः : (g : ℕ) → वल्ली g 0 g
  छेदः     : (a b q r g : ℕ)
           → r < b                  -- शेषो न्यूनः — the measure
           → a ≡ q · b + r          -- छेदः — the division
           → वल्ली b r g
           → वल्ली a b g

------------------------------------------------------------------------
-- २ · कुट्टक-समाप्तिः — TERMINATION.  A vallī exists for every pair.
--
-- Well-founded recursion on b.  That measure is the source's own: the rule
-- says to recurse on the remainder, and "the remainder is smaller than the
-- divisor" is the only fact the recursion needs.
------------------------------------------------------------------------

private
  -- the division `Cubical.Data.Nat.Mod` performs, put in the shape
  -- a ≡ q·b + r that a row of the vallī wants.
  छेद-समीकरणम् : (n a : ℕ)
              → a ≡ (quotient a / suc n) · suc n + (remainder a / suc n)
  छेद-समीकरणम् n a =
      sym (≡remainder+quotient (suc n) a)
    ∙ +-comm (remainder a / suc n) (suc n · (quotient a / suc n))
    ∙ cong (_+ (remainder a / suc n)) (·-comm (suc n) (quotient a / suc n))

  पदम् : (b : ℕ)
       → ((b' : ℕ) → b' < b → (x : ℕ) → Σ[ g ∈ ℕ ] वल्ली x b' g)
       → (a : ℕ) → Σ[ g ∈ ℕ ] वल्ली a b g
  पदम् zero    _   a = a , विश्रामः a
  पदम् (suc n) rec a =
    let r       = remainder a / suc n
        q       = quotient  a / suc n
        r<b     = mod< n a
        (g , v) = rec r r<b (suc n)
    in  g , छेदः a (suc n) q r g r<b (छेद-समीकरणम् n a) v

कुट्टक-समाप्तिः : (a b : ℕ) → Σ[ g ∈ ℕ ] वल्ली a b g
कुट्टक-समाप्तिः a b = WFI.induction <-wellfounded पदम् b a

-- the terminal value of the descent; §6 proves it is the gcd.
अन्त्यम् : ℕ → ℕ → ℕ
अन्त्यम् a b = fst (कुट्टक-समाप्तिः a b)

------------------------------------------------------------------------
-- ३ · दैर्घ्यम् — the length of the column, and THE BOUND, derived.
--
-- The vall of (a, b) has at most b rows.  The proof reads off the `r < b`
-- that §1 makes every row carry: the sub-column has at most r rows, and
-- r + 1 ≤ b.  Nothing is measured and nothing is fitted.
------------------------------------------------------------------------

दैर्घ्यम् : {a b g : ℕ} → वल्ली a b g → ℕ
दैर्घ्यम् (विश्रामः _)           = 0
दैर्घ्यम् (छेदः _ _ _ _ _ _ _ v) = suc (दैर्घ्यम् v)

दैर्घ्य-सीमा : {a b g : ℕ} (v : वल्ली a b g) → दैर्घ्यम् v ≤ b
दैर्घ्य-सीमा (विश्रामः _)                = zero-≤
दैर्घ्य-सीमा (छेदः a b q r g r<b _ v) =
  ≤-trans (suc-≤-suc (दैर्घ्य-सीमा v)) r<b

-- the column itself — the quotients, top to bottom.  §17 of
-- AHIMSA_SUTRA_VISTARA: "वल्ली न सोपानम् — फलम्", the vallī is not a
-- staircase but the fruit; it is kept, not discarded.
सूचिः : {a b g : ℕ} → वल्ली a b g → List ℕ
सूचिः (विश्रामः _)             = []
सूचिः (छेदः _ _ q _ _ _ _ v)   = q ∷ सूचिः v

------------------------------------------------------------------------
-- ४ · शेष-वल्ली — a BOUNDED run, and what it did not reach.
--
-- This is §8 of AHIMSA_SUTRA_VISTARA carried into the engine: "यत् शेषं वदति
-- तत् न सङ्क्षिपति" — what states its remainder does not collapse.
--
-- `शेष-वल्ली a b` has exactly two constructors, which is §6's two paths and
-- no third: either the run FINISHED, and hands over the whole vall, or it
-- ran out, and must name the pair it stopped on together with the partial
-- column that got there.  There is no way to report a truncated run without
-- its remainder, because the type has no constructor for one.
------------------------------------------------------------------------

-- a partial column: the same rows, with no requirement that it bottoms out.
data पूर्व-वल्ली : ℕ → ℕ → ℕ → ℕ → Type where
  आरम्भः : (a b : ℕ) → पूर्व-वल्ली a b a b
  पदे    : (a b q r a' b' : ℕ)
         → r < b
         → a ≡ q · b + r
         → पूर्व-वल्ली b r a' b'
         → पूर्व-वल्ली a b a' b'

data शेष-वल्ली (a b : ℕ) : Type where
  समाप्तः : (g : ℕ) → वल्ली a b g → शेष-वल्ली a b
  अपूर्णः  : (a' b' : ℕ) → पूर्व-वल्ली a b a' b' → 0 < b' → शेष-वल्ली a b

private
  -- prefix one division onto whatever the sub-run reported.  Written as its
  -- own function rather than a `with`, so that §5 can case-split on the
  -- sub-run without fighting a with-abstraction.
  अनुबन्धः : (a b q r : ℕ) → r < b → a ≡ q · b + r
           → शेष-वल्ली b r → शेष-वल्ली a b
  अनुबन्धः a b q r lt eq (समाप्तः g v) =
    समाप्तः g (छेदः a b q r g lt eq v)
  अनुबन्धः a b q r lt eq (अपूर्णः a' b' pre 0<b') =
    अपूर्णः a' b' (पदे a b q r a' b' lt eq pre) 0<b'

-- the runner.  `f` is the fuel — the cap — and when it is exhausted the run
-- reports where it stopped rather than looping or lying.
चालनम् : (f a b : ℕ) → शेष-वल्ली a b
चालनम् f       a zero    = समाप्तः a (विश्रामः a)
चालनम् zero    a (suc n) = अपूर्णः a (suc n) (आरम्भः a (suc n)) (suc-≤-suc zero-≤)
चालनम् (suc f) a (suc n) =
  अनुबन्धः a (suc n) (quotient a / suc n) (remainder a / suc n)
          (mod< n a) (छेद-समीकरणम् n a)
          (चालनम् f (suc n) (remainder a / suc n))

------------------------------------------------------------------------
-- ५ · पर्याप्तम् — THE FUEL IS ENOUGH, which is what §3's bound is FOR.
--
-- With f ≥ b the bounded run always finishes.  So `b` is a BOUND — a number
-- carrying a proof that it is never reached — and not a GUESS, a number
-- carrying a hope.  That distinction is the whole difference between this
-- and `machine/Nalanda.hs` (absent from this repository)'s `n > 400`.
------------------------------------------------------------------------

समाप्तम्? : {a b : ℕ} → शेष-वल्ली a b → Type
समाप्तम्? (समाप्तः _ _)    = Unit
समाप्तम्? (अपूर्णः _ _ _ _) = ⊥

private
  अनुबन्ध-रक्षति : (a b q r : ℕ) (lt : r < b) (eq : a ≡ q · b + r)
               → (s : शेष-वल्ली b r)
               → समाप्तम्? s → समाप्तम्? (अनुबन्धः a b q r lt eq s)
  अनुबन्ध-रक्षति a b q r lt eq (समाप्तः g v)      _ = tt
  अनुबन्ध-रक्षति a b q r lt eq (अपूर्णः _ _ _ _)  h = h

पर्याप्तम् : (f a b : ℕ) → b ≤ f → समाप्तम्? (चालनम् f a b)
पर्याप्तम् f       a zero    _  = tt
पर्याप्तम् zero    a (suc n) le = ⊥rec (¬-<-zero le)
पर्याप्तम् (suc f) a (suc n) le =
  अनुबन्ध-रक्षति a (suc n) (quotient a / suc n) (remainder a / suc n)
              (mod< n a) (छेद-समीकरणम् n a)
              (चालनम् f (suc n) (remainder a / suc n))
              (पर्याप्तम् f (suc n) (remainder a / suc n)
                        (≤-trans (pred-≤-pred (mod< n a)) (pred-≤-pred le)))

-- and so the cap `b` never fires: stated as the vall the bounded run
-- produces when it is given exactly the fuel §3 says it needs.
सीमायां-समाप्तिः : (a b : ℕ) → समाप्तम्? (चालनम् b a b)
सीमायां-समाप्तिः a b = पर्याप्तम् b a b ≤-refl

------------------------------------------------------------------------
-- ६ · सेतुः — THE BRIDGE.  A ℕ vallī IS a `Kuttaka.Run` over ℤ.
--
-- With it, every theorem in `Kuttaka.agda` loses its hypothesis: what was
-- "given a run" becomes "for every pair of naturals".
------------------------------------------------------------------------

private
  सेतु-समीकरणम् : (a b q r : ℕ) → a ≡ q · b + r
               → pos a ≡ pos q ·ℤ pos b +ℤ pos r
  सेतु-समीकरणम् a b q r eq =
      cong pos eq
    ∙ pos+ (q · b) r
    ∙ cong (_+ℤ pos r) (pos·pos q b)

सेतुः : {a b g : ℕ} → वल्ली a b g → Run (pos a) (pos b) (pos g)
सेतुः (विश्रामः g)                  = stop (pos g)
सेतुः (छेदः a b q r g _ eq v) =
  div (pos a) (pos b) (pos q) (pos r) (pos g) (सेतु-समीकरणम् a b q r eq) (सेतुः v)

-- THE KUAKA, UNCONDITIONALLY.  For every pair of naturals, coefficients.
बेजु-सर्वत्र : (a b : ℕ)
          → Σ[ x ∈ ℤ ] Σ[ y ∈ ℤ ]
              (pos a ·ℤ x +ℤ pos b ·ℤ y ≡ pos (अन्त्यम् a b))
बेजु-सर्वत्र a b =
  bezout (pos a) (pos b) (pos (अन्त्यम् a b)) (सेतुः (snd (कुट्टक-समाप्तिः a b)))

-- and the terminal value is the greatest common divisor, for every pair.
महत्तम-भाजकः : (a b : ℕ)
            → (pos (अन्त्यम् a b) ∣ pos a) × (pos (अन्त्यम् a b) ∣ pos b)
महत्तम-भाजकः a b =
  gcdDivides (pos a) (pos b) (pos (अन्त्यम् a b)) (सेतुः (snd (कुट्टक-समाप्तिः a b)))

महत्तमः : (a b : ℕ) (d : ℤ) → d ∣ pos a → d ∣ pos b → d ∣ pos (अन्त्यम् a b)
महत्तमः a b d =
  gcdGreatest (pos a) (pos b) (pos (अन्त्यम् a b)) d
              (सेतुः (snd (कुट्टक-समाप्तिः a b)))

------------------------------------------------------------------------
-- ७ · अ-रिक्तता — non-vacuity, at the sūtra's own numbers.
--
-- AHIMSA_SUTRA_VISTARA §17 works the kuaka on (137, 60) and prints its
-- vall: 2 3 1 1 8.  The kernel is asked for the same column, from
-- `कुट्टक-समाप्तिः` and not from a hand-built run, so this checks that the
-- termination proof COMPUTES the algorithm rather than merely asserting a
-- vall is out there somewhere.
------------------------------------------------------------------------

वल्ली-१३७-६० : सूचिः (snd (कुट्टक-समाप्तिः 137 60)) ≡ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 8 ∷ []
वल्ली-१३७-६० = refl

अन्त्यम्-१३७-६० : अन्त्यम् 137 60 ≡ 1
अन्त्यम्-१३७-६० = refl

-- and `Kuttaka.example`'s pair, whose run that module supplies by hand:
-- here the same column is produced rather than written down.
वल्ली-७-५ : सूचिः (snd (कुट्टक-समाप्तिः 7 5)) ≡ 1 ∷ 2 ∷ 2 ∷ []
वल्ली-७-५ = refl

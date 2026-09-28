{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AsiddhavatRegime — the two regimes are different devices, at the site
-- where the difference is visible.
--
-- THE TWO STRAS, checked against sources 2026-08-19 rather than recalled.
-- Pini, Adhyy, c. 500 BCE:
--
--   8.2.1  पूर्वत्रासिद्धम्   any SUBSEQUENT rule is asiddha with respect to
--          any rule that PRECEDES it, so the tripd applies strictly in
--          the order enumerated.  One-way, backwards blindness.
--
--   6.4.22 असिद्धवदत्राभात्  heads 6.4.22–6.4.129: a change by any rule of
--          that section counts as NOT HAVING TAKEN EFFECT when applying
--          any OTHER rule of the same section.  Mutual invisibility; the
--          rules apply AS IF SIMULTANEOUSLY.
--
-- `Asiddhatva.agda` proves the first buys TERMINATION.
-- `NaturalMachine/AsiddhatvaBreaksFactoring.agda` proves the simultaneous
-- device buys INFORMATION (its header attributes that to 8.2.1; the
-- correction is appended there).  What neither shows is that the choice
-- CHANGES THE ANSWER.  This does, at one site, with both regimes computed
-- from the same rule set rather than written down.
--
-- THE SITE is `tat + jalam`, pada-final t before j.  Three rules of the
-- tripd offer at that one position, and under simultaneity none of them
-- sees the others:
--
--   8.2.39  झलां जशोऽन्ते      jhaL → jaŚ at pada-end        t ↦ d
--   8.4.40  स्तोः श्चुना श्चुः   stu → ścu in contact with ścu  t ↦ c, d ↦ j
--   8.4.53  झलां जश् झशि       jhaL → jaŚ before jhaŚ        t ↦ d
--
-- ORDERED:      8.2.39 fires, then 8.4.40 acts on ITS output.  t → d → j.
--               `tajjalam`, which is the attested form.
-- SIMULTANEOUS: all three see t; 1.4.2 विप्रतिषेधे परं कार्यम् takes the
--               latest, 8.4.53, and the pass stops.  t → d.  `tadjalam`,
--               which  does not have.
--
-- So the regime decides the form.  पूर्वत्रासिद्धम् is load-bearing rather
-- than presentational, and it is the ORDERED device — which is independent
-- evidence for the attribution corrected in AsiddhatvaBreaksFactoring,
-- reached from the rules rather than from the stra text.
--
-- This is the checked form of the measurement in `machine/Astadhyayi.hs` (absent from this repository)
-- (`regimeTests`), whose `asiddhavatPass` found it first.
--
-- No postulates, no holes, --safe.  Both regimes are folds over one
-- `act` table; nothing below states an answer.
------------------------------------------------------------------------

module AsiddhavatRegime where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; foldl)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  The site: the pada-final consonant, with `j` following throughout.
------------------------------------------------------------------------

data Antya : Type where
  t d j c : Antya

data Sutra : Type where
  s8-2-39 s8-4-40 s8-4-53 : Sutra

-- the stra's position, which 1.4.2 reads
sthana : Sutra → ℕ
sthana s8-2-39 = 8239
sthana s8-4-40 = 8440
sthana s8-4-53 = 8453

-- what each stra does here, or nothing
act : Sutra → Antya → Maybe Antya
act s8-2-39 t = just d      -- jhaL t → jaŚ d, at pada-end
act s8-4-40 t = just c      -- stu t → ścu c, before j
act s8-4-40 d = just j      -- stu d → ścu j, before j
act s8-4-53 t = just d      -- jhaL t → jaŚ d, before jhaŚ j
act _       _ = nothing

-- the tripd in the order Pini enumerates it
krama-order : List Sutra
krama-order = s8-2-39 ∷ s8-4-40 ∷ s8-4-53 ∷ []

------------------------------------------------------------------------
-- 2.  क्रम — each rule acts on what the previous ones produced (8.2.1).
------------------------------------------------------------------------

apply1 : Antya → Sutra → Antya
apply1 x s with act s x
... | just y  = y
... | nothing = x

krama : Antya → Antya
krama x = foldl apply1 x krama-order

------------------------------------------------------------------------
-- 3.  सह — every rule is offered the SAME input (6.4.22), and where two
--     offers collide 1.4.2 विप्रतिषेधे परं कार्यम् takes the later sūtra.
------------------------------------------------------------------------

_<ᵇ_ : ℕ → ℕ → Bool
zero  <ᵇ zero  = false
zero  <ᵇ suc _ = true
suc _ <ᵇ zero  = false
suc m <ᵇ suc n = m <ᵇ n

-- every rule's offer against the UNMODIFIED form
offers : Antya → List (Sutra × Antya)
offers x = go krama-order
  where
    go : List Sutra → List (Sutra × Antya)
    go [] = []
    go (s ∷ ss) with act s x
    ... | just y  = (s , y) ∷ go ss
    ... | nothing = go ss

-- 1.4.2: among colliding offers, the one sitting later in the text
best : List (Sutra × Antya) → Maybe (Sutra × Antya)
best [] = nothing
best (p ∷ ps) with best ps
... | nothing = just p
... | just q  = if sthana (fst p) <ᵇ sthana (fst q) then just q else just p

saha : Antya → Antya
saha x with best (offers x)
... | just (_ , y) = y
... | nothing      = x

------------------------------------------------------------------------
-- 4.  The regimes disagree, and the ordered one is the attested .
--
-- Nothing here states an answer: both sides are folds over `act`.
------------------------------------------------------------------------

-- 8.2.39 fires, then 8.4.40 acts on its output: t → d → j.  `tajjalam`.
krama-gives-j : krama t ≡ j
krama-gives-j = refl

-- all three see t; 1.4.2 takes 8.4.53, and the pass stops.  `tadjalam`.
saha-gives-d : saha t ≡ d
saha-gives-d = refl

isJ : Antya → Bool
isJ j = true
isJ _ = false

j≢d : ¬ (j ≡ d)
j≢d p = true≢false (cong isJ p)

-- so the device is load-bearing, not presentational
regimes-differ : ¬ (krama t ≡ saha t)
regimes-differ = j≢d

-- and they agree wherever at most one rule ever offers
agree-where-uncontested : krama c ≡ saha c
agree-where-uncontested = refl

------------------------------------------------------------------------
-- 5.  WHY THE SIMULTANEOUS PASS STOPS SHORT, stated as the offers.
--
-- Under सह the three offers against t are 8.2.39 ↦ d, 8.4.40 ↦ c and
-- 8.4.53 ↦ d.  They collide at one position, so exactly one survives, and
-- 1.4.2 picks the latest.  Under क्रम, 8.2.39's output d is then a fresh
-- input that 8.4.40 can read — which is precisely what asiddhatva forbids
-- between the quarters and permits within the sequence.
------------------------------------------------------------------------

three-offers : offers t ≡ (s8-2-39 , d) ∷ (s8-4-40 , c) ∷ (s8-4-53 , d) ∷ []
three-offers = refl

-- and after the first, only one remains — the ordered regime's second step
one-offer-after : offers d ≡ (s8-4-40 , j) ∷ []
one-offer-after = refl

------------------------------------------------------------------------
-- 6.  AND THE OBVIOUS NEXT CLAIM IS FALSE, so it is recorded rather than
--     left implied.
--
-- Having proved the regimes differ, the tempting extension is that the
-- simultaneous one is defective — that it fails to terminate, or cannot
-- reach the attested form at all.  Neither holds here.  ITERATE सह and it
-- converges, and it converges to the SAME form क्रम gives:
--
--     saha t = d ,  saha d = j ,  saha j = j
--
-- So the difference between the devices at this site is a difference
-- between ONE PASS and a fixpoint, not between reaching the answer and
-- failing to.  That matters for what may be said about 6.4.22: its block
-- applies once, and the single application is where its content lies.  A
-- claim that simultaneity "cannot get there" would be false.
--
-- What survives from §4 is exact and narrower than it sounded: A SINGLE
-- SIMULTANEOUS PASS over these rules does not give the attested form,
-- while the ordered regime does so in one traversal.  पूर्वत्रासिद्धम् is
-- still load-bearing — the tripādī is traversed once, not iterated — but
-- the reason is that ordering buys the right answer IN ONE PASS, not that
-- simultaneity is incapable.
------------------------------------------------------------------------

saha-once  : saha t ≡ d
saha-once  = refl

saha-twice : saha (saha t) ≡ j
saha-twice = refl

saha-fixed : saha (saha (saha t)) ≡ saha (saha t)
saha-fixed = refl

-- iterated, the simultaneous regime reaches exactly what the ordered one
-- reaches in a single traversal
saha-converges-to-krama : saha (saha t) ≡ krama t
saha-converges-to-krama = refl

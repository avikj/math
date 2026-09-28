{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- वरणम् — भास्करस्य m-वरणस्य गवाक्षः, साधितः, न मापितः ।
-- Varaṇa — the width of Bhāskara's m-choice window, DERIVED.
--
-- SOURCE AND DATE.  The वरण — the choice rule — is BHĀSKARA II's contribution
-- to the चक्रवालम् over Jayadeva: among the m satisfying the one congruence
-- k | (a + b·m), take one minimising |m² − D|.  बीजगणितम्, 1150 CE; the cycle
-- itself is Jayadeva's, ~950, surviving through Udayadivākara's सुन्दरी, 1073.
-- The congruence whose solutions m form the class is solved by RYABHAA's
-- कुट्टक, आर्यभटीयम् गणितपादः ३२–३३, 499.  Nothing below claims Bhāskara stated
-- the theorem in this file; he stated the rule, and this is what the rule
-- costs to execute.
--
-- WHY THIS FILE EXISTS.  `machine/Nalanda.hs` (absent from this repository), `chooseM`, enumerates the
-- residue class m = r + t·n only over
--
--     t ∈ [t₀ − 2 .. t₀ + 2],       t₀ = (⌊√D⌋ − r) div n
--
-- and its comment justifies the truncation like this, verbatim:
--
--     "the minimiser is adjacent to sqrt D, so a short window around it is
--      exhaustive rather than sampled -- the window is checked in `selfTest`
--      by re-running with a wider one and comparing."
--
-- The first clause is the theorem and the second is a measurement standing
-- in for it.
--
-- WHAT IS PROVED.  No postulates, no holes, --safe.
-- No ring solver, no square roots, no absolute value, no
-- subtraction: every "distance from D" is carried as an explicit witness E on
-- the correct side of the equation, in the style `CakravalaBound.agda` uses
-- and for the same reason.
--
--   वरण-अधः      BELOW THE ROOT, LARGER IS BETTER.  If c ≤ lo and both sit
--                below D (c² + E_c ≡ D, lo² + E_lo ≡ D) then E_lo ≤ E_c.
--   वरण-ऊर्ध्वम्   ABOVE THE ROOT, SMALLER IS BETTER.  If hi ≤ c and both sit
--                above D (D + E_hi ≡ hi², D + E_c ≡ c²) then E_hi ≤ E_c.
--   श्रेणी-अन्तरम्  THE CLASS HAS NO MEMBER STRICTLY INSIDE THE BRACKET.  The
--                class members are r + t·n; from t₀ < t follows
--                (r + t₀·n) + n ≤ r + t·n.  So between the last member at or
--                below ⌊√D⌋ and the next one there is nothing.
--   गवाक्षः       THE WINDOW IS ±1.  Given a bracketing pair lo ≤ √D ≤ hi with
--                hi ≡ lo + n, EVERY candidate outside {lo, hi} has cost at
--                least one of E_lo, E_hi.  Two candidates are therefore
--                exhaustive, and `chooseM`'s five are three more than the
--                argument needs — which is fine, and is now a stated margin
--                rather than an unexamined one.
------------------------------------------------------------------------

module Varana_TheChoiceWindowIsDerivedNotFitted where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-comm ; +-assoc ; ·-comm ; inj-m+)
open import Cubical.Data.Nat.Order
  using (_<_ ; _≤_ ; ≤-trans ; ≤-·k ; ≤-k+ ; suc-≤-suc ; ≤-refl ; ≤-k+-cancel)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_)

------------------------------------------------------------------------
-- ० · two order facts cubical does not ship in this shape.
------------------------------------------------------------------------

private
  ≤-k·' : {m n : ℕ} (k : ℕ) → m ≤ n → k · m ≤ k · n
  ≤-k·' {m} {n} k h = subst2 _≤_ (·-comm m k) (·-comm n k) (≤-·k {k = k} h)

  -- squaring is monotone.
  वर्ग-क्रमः : {m n : ℕ} → m ≤ n → m · m ≤ n · n
  वर्ग-क्रमः {m} {n} h = ≤-trans (≤-·k {k = m} h) (≤-k·' n h)

  -- from P ≤ Q and Q + X ≡ P + Y conclude X ≤ Y.  (The same lemma
  -- `CakravalaBound.agda` builds; that module is not imported.)
  विनिमयः : (P Q X Y : ℕ) → P ≤ Q → Q + X ≡ P + Y → X ≤ Y
  विनिमयः P Q X Y (c , hc) e = c , inj-m+ {m = P} step
    where
    assoc1 : P + (c + X) ≡ Q + X
    assoc1 = +-assoc P c X ∙ cong (_+ X) (+-comm P c) ∙ cong (_+ X) hc

    step : P + (c + X) ≡ P + Y
    step = assoc1 ∙ e

------------------------------------------------------------------------
-- १ · वरण-अधः — below the root, the larger candidate is the better one.
--
-- lo² + E_lo ≡ D and c² + E_c ≡ D with c ≤ lo.  Then c² ≤ lo², and the two
-- equations shift the inequality onto the costs the other way round.
------------------------------------------------------------------------

वरण-अधः : (D lo c Elo Ec : ℕ)
        → c ≤ lo
        → lo · lo + Elo ≡ D
        → c · c + Ec ≡ D
        → Elo ≤ Ec
वरण-अधः D lo c Elo Ec c≤lo hlo hc =
  विनिमयः (c · c) (lo · lo) Elo Ec (वर्ग-क्रमः c≤lo) (hlo ∙ sym hc)

------------------------------------------------------------------------
-- २ · वरण-ऊर्ध्वम् — above the root, the smaller candidate is the better one.
--
-- D + E_hi ≡ hi² and D + E_c ≡ c² with hi ≤ c.  Then hi² ≤ c², so
-- D + E_hi ≤ D + E_c, and D cancels.
------------------------------------------------------------------------

वरण-ऊर्ध्वम् : (D hi c Ehi Ec : ℕ)
          → hi ≤ c
          → D + Ehi ≡ hi · hi
          → D + Ec  ≡ c · c
          → Ehi ≤ Ec
वरण-ऊर्ध्वम् D hi c Ehi Ec hi≤c hhi hcc =
  ≤-k+-cancel {k = D} (subst2 _≤_ (sym hhi) (sym hcc) (वर्ग-क्रमः hi≤c))

------------------------------------------------------------------------
-- ३ · श्रेणी-अन्तरम् — the class has no member strictly inside the bracket.
------------------------------------------------------------------------

श्रेणी-अन्तरम् : (r n t₀ t : ℕ) → suc t₀ ≤ t → r + (suc t₀) · n ≤ r + t · n
श्रेणी-अन्तरम् r n t₀ t h = ≤-k+ (≤-·k {k = n} h)

-- and the next class member after `r + t₀·n` is exactly `n` further on.
श्रेणी-पदम् : (r n t₀ : ℕ) → r + (suc t₀) · n ≡ (r + t₀ · n) + n
श्रेणी-पदम् r n t₀ =
    cong (r +_) (+-comm n (t₀ · n))
  ∙ +-assoc r (t₀ · n) n

------------------------------------------------------------------------
-- ४ · गवाक्षः — THE WINDOW IS ±1.
--
-- Given a bracketing pair — lo at or below √D with cost E_lo, hi at or above
-- √D with cost E_hi — every candidate c outside {lo, hi}, on whichever side,
-- with its cost stated on the correct side of D, is beaten by one of them.
--
-- Read as the statement about `chooseM`: enumerating t₀ and t₀+1 loses
-- nothing, so the ±2 in the source is a margin of three and not a hope.
------------------------------------------------------------------------

गवाक्षः : (D lo hi c Elo Ehi Ec : ℕ)
       → lo · lo + Elo ≡ D
       → D + Ehi ≡ hi · hi
       → ((c ≤ lo) × (c · c + Ec ≡ D)) ⊎ ((hi ≤ c) × (D + Ec ≡ c · c))
       → (Elo ≤ Ec) ⊎ (Ehi ≤ Ec)
गवाक्षः D lo hi c Elo Ehi Ec hlo hhi (inl (c≤lo , hc)) =
  inl (वरण-अधः D lo c Elo Ec c≤lo hlo hc)
गवाक्षः D lo hi c Elo Ehi Ec hlo hhi (inr (hi≤c , hc)) =
  inr (वरण-ऊर्ध्वम् D hi c Ehi Ec hi≤c hhi hc)

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- वज्राभ्यासः — the cross product of two consecutive turns is 1, and from that
-- alone the next turn's admissible multipliers are EXACTLY the class of −m.
--
-- SOURCE AND DATE.  वज्राभ्यास ("thunderbolt multiplication") is BHĀSKARA II's
-- own word for the crosswise product of two pairs; लीलावती and बीजगणितम्, 1150
-- CE.  The चक्रवालम् is JAYADEVA's, ~950, surviving through Udayadivākara's
-- , 1073.  The  that solves the congruence
-- is ĀRYABHAṬA's, आर्यभटीयम् गणितपादः ३२–३३, 499.  Nothing below claims any of
-- them stated the theorem in this file; what is claimed is that the quantity
-- this file turns on is the crosswise product they named, taken between a
-- turn of the wheel and its successor.  प्रत्यावृत्तिः is this repository's
-- label, introduced by
-- `GunakaKsepa_TheWheelsStateIsBoundedAndSelfPropagating`, not a source term.
--
-- No pulverizer run is
-- needed: gcd(b', k') = 1 is a CONSEQUENCE of the step's own three exact
-- divisions, with both Bézout coefficients written out of a, b, a', b'.
--
-- THE MECHANISM, in one line each.
--
--   वज्राभ्यासः  k·(a·b' − b·a') = a·(k·b') − b·(k·a') = a(a+bm) − b(am+Db)
--              = a² − D·b² = k = k·1, and k cancels.  So consecutive turns
--              of the wheel have crosswise product exactly 1 — an equality,
--              not a divisibility, and it needs no choice rule, no
--              minimality, no ordering.
--
--   सह-प्रथमता   (a·b' − b·a')² = 1 expands, with k' = a'² − D·b'² substituted
--              for a'², into
--                  (b·b)·k' + v·b' ≡ 1,   v = a²b' + D·b²·b' − 2·a·b·a',
--              in which the D-terms cancel identically.  That IS the Bézout
--              pair for (k', b').  No pulverizer, no gcd, no primality.
--
--   श्रेणी      with that pair, `CakravalaDescent.coprimeCancel` turns
--              प्रत्यावृत्तिः — that −m solves the next congruence — into the
--              two-way statement:
--                  k' ∣ (a' + b'·m')   ⟺   k' ∣ (m + m').
--              The admissible multipliers of the next turn are exactly the
--              residue class of −m modulo k'.
--
-- WHAT THAT BUYS, EXACTLY.  The next turn's CLASS is a function of (m, k')
-- alone, and |k'| = |m² − D| / |k| is a function of (m, |k|, D).  So the
-- whole of the next state is determined by the current one AS SOON AS the
-- minimisation over that class picks a unique member.
--
-- WHAT IT DOES NOT BUY, and this is not a hedge — it is a checked negative.
-- The minimisation does NOT always pick a unique member.
-- `Dvaidha_TheVaranaTiesExactlyWhenDIsASumOfTwoSquares` (absent from this repository) exhibits the tie, in
-- the kernel, at D = 58 turn 1 — on a class that IS the −m mod k' this file
-- proves — and characterises exactly when a tie can occur.  So after this
-- file the gap between the state box and determinism is one thing and not
-- two, that thing is not a missing lemma but a genuine branch in the rule,
-- and it has an instance.
--
-- WHAT IS PROVED.  --safe, no postulates, no holes.
-- Stated over ℤ rather than an arbitrary CommRing only because the ring
-- solver wants a concrete ring; nothing below uses more than commutativity
-- and the cancellation hypothesis that `CakravalaDescent.cakravalaStep`
-- already takes.
------------------------------------------------------------------------

module VajraAbhyasa_TheCrossProductIsOneAndTheNextClassIsExactlyMinusM where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.CommRing using (CommRingStr)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

open import Composition using (module Form)
open import CakravalaDescent using (module Descent)
open import GunakaKsepa_TheWheelsStateIsBoundedAndSelfPropagating
  using (प्रत्यावृत्तिः)

open CommRingStr (snd ℤCommRing) using (_·_ ; _+_ ; _-_ ; -_ ; 1r ; ·IdR)
open Form ℤCommRing using (N)
open Descent ℤCommRing using (_∣_ ; Coprime ; coprimeCancel ; cakravalaStep)

------------------------------------------------------------------------
-- १ · वज्राभ्यासः — THE CROSS PRODUCT OF TWO CONSECUTIVE TURNS IS ONE.
--
-- Given a² − D·b² = k and the two exact divisions k·a' = a·m + D·b,
-- k·b' = a + b·m, the crosswise product a·b' − b·a' is exactly 1.
--
-- Note what is NOT used: k' does not appear, the choice rule does not
-- appear, and no ordering or minimality is involved.  This is a fact about
-- Brahmagupta's composition with the trivial triple (m, 1, m² − D) and
-- nothing else — the composite pair and the pair it came from are a
-- unimodular pair, always.
------------------------------------------------------------------------

वज्राभ्यासः : (D a b m k a' b' : ℤ)
           → ((x y : ℤ) → k · x ≡ k · y → x ≡ y)   -- k cancels
           → N D a b ≡ k
           → a · m + D · b ≡ k · a'
           → a + b · m     ≡ k · b'
           → a · b' - b · a' ≡ 1r
वज्राभ्यासः D a b m k a' b' cancel nab ea eb =
  cancel (a · b' - b · a') 1r
    ( विभागः
    ∙ cong₂ _-_ (cong (a ·_) (sym eb)) (cong (b ·_) (sym ea))
    ∙ सारः
    ∙ nab
    ∙ sym (·IdR k) )
  where
  विभागः : k · (a · b' - b · a') ≡ a · (k · b') - b · (k · a')
  विभागः = solve! ℤCommRing

  -- a·(a + b·m) − b·(a·m + D·b)  ≡  a·a − D·(b·b),  which IS `N D a b`.
  सारः : a · (a + b · m) - b · (a · m + D · b) ≡ a · a - D · (b · b)
  सारः = solve! ℤCommRing

------------------------------------------------------------------------
-- २ · सह-प्रथमता — THE NEXT PAIR'S COPRIMALITY, WITH BOTH COEFFICIENTS
-- WRITTEN OUT.
--
-- `Coprime` in `CakravalaDescent` is deliberately not "no common factor" —
-- it is the two Bézout coefficients themselves, because that is what the
-- cancellation can compute with.  Here they are:
--
--     u = b·b        v = a²·b' + D·b²·b' − 2·a·b·a'
--
-- and u·k' + v·b' ≡ 1 is the square of §1 with k' = a'² − D·b'² substituted
-- back in; the two D-terms cancel identically, which is why D does not have
-- to be anything in particular.
--
-- THE PULVERIZER IS NOT NEEDED HERE: the wheel's own previous coordinates
-- are the certificate for gcd(b', k') = 1.
------------------------------------------------------------------------

सह-प्रथमता : (D a b a' b' k' : ℤ)
          → a · b' - b · a' ≡ 1r
          → N D a' b' ≡ k'
          → Coprime k' b'
सह-प्रथमता D a b a' b' k' hvaj nab' = b · b , v , path
  where
  v : ℤ
  v = ((a · a) · b' + (D · (b · b)) · b') - ((a · b) · a' + (a · b) · a')

  -- the whole content, as one ring identity: with a'² − D·b'² in place of
  -- k', the left side IS (a·b' − b·a')².
  तादात्म्यम् : (b · b) · (a' · a' - D · (b' · b')) + v · b'
             ≡ (a · b' - b · a') · (a · b' - b · a')
  तादात्म्यम् = solve! ℤCommRing

  path : (b · b) · k' + v · b' ≡ 1r
  path = cong (λ w → (b · b) · w + v · b') (sym nab')
       ∙ तादात्म्यम्
       ∙ cong₂ _·_ hvaj hvaj
       ∙ ·IdR 1r

------------------------------------------------------------------------
-- ३ · श्रेणी — THE CLASS, BOTH WAYS.
--
-- §3a is free: if m' ≡ −m then m' solves the congruence, because −m does
-- (प्रत्यावृत्तिः) and the difference is b'·(m + m').
--
-- §3b is the direction that needs §2: from k' ∣ b'·(m + m') and the Bézout
-- pair, k' ∣ (m + m').  Without §2 the class could a priori be larger — the
-- solutions could be a class modulo a proper divisor of k' — and then the
-- next multiplier would not be a function of the state even with ties ruled
-- out.
------------------------------------------------------------------------

श्रेणी-प्रवेशः : (b' k' m m' a' b : ℤ)
             → a' + b' · (- m) ≡ k' · (- b)
             → k' ∣ (m + m')
             → k' ∣ (a' + b' · m')
श्रेणी-प्रवेशः b' k' m m' a' b hr (t , ht) =
  ((- b) + b' · t)
  , ( पृथक्करणम्
    ∙ cong₂ _+_ hr (cong (b' ·_) ht)
    ∙ संयोगः )
  where
  पृथक्करणम् : a' + b' · m' ≡ (a' + b' · (- m)) + b' · (m + m')
  पृथक्करणम् = solve! ℤCommRing

  संयोगः : k' · (- b) + b' · (k' · t) ≡ k' · ((- b) + b' · t)
  संयोगः = solve! ℤCommRing

श्रेणी-निर्गमः : (b' k' m m' a' b : ℤ)
             → Coprime k' b'
             → a' + b' · (- m) ≡ k' · (- b)
             → k' ∣ (a' + b' · m')
             → k' ∣ (m + m')
श्रेणी-निर्गमः b' k' m m' a' b cop hr (c , hc) =
  coprimeCancel k' b' (m + m') cop
    ( (c + b)
    , ( पृथक्करणम्
      ∙ cong₂ _-_ hc hr
      ∙ संयोगः ) )
  where
  पृथक्करणम् : b' · (m + m') ≡ (a' + b' · m') - (a' + b' · (- m))
  पृथक्करणम् = solve! ℤCommRing

  संयोगः : k' · c - k' · (- b) ≡ k' · (c + b)
  संयोगः = solve! ℤCommRing

------------------------------------------------------------------------
-- ४ · श्रेणी-निर्णयः — THE JOIN.
--
-- One theorem, taking exactly the hypotheses the algorithm's own situation
-- supplies — the norm, the three exact divisions, and cancellation by k —
-- and returning: the next turn's admissible multipliers are EXACTLY the
-- residue class of −m modulo k'.
------------------------------------------------------------------------

श्रेणी-निर्णयः : (D a b m k a' b' k' : ℤ)
            → ((x y : ℤ) → k · x ≡ k · y → x ≡ y)   -- k cancels
            → N D a b ≡ k
            → a · m + D · b ≡ k · a'
            → a + b · m     ≡ k · b'
            → m · m - D     ≡ k · k'
            → (m' : ℤ)
            → (k' ∣ (m + m') → k' ∣ (a' + b' · m'))
            × (k' ∣ (a' + b' · m') → k' ∣ (m + m'))
श्रेणी-निर्णयः D a b m k a' b' k' cancel nab ea eb ek m' =
    श्रेणी-प्रवेशः b' k' m m' a' b hr
  , श्रेणी-निर्गमः b' k' m m' a' b cop hr
  where
  hr : a' + b' · (- m) ≡ k' · (- b)
  hr = प्रत्यावृत्तिः D a b m k a' b' k' cancel ea eb ek

  nab' : N D a' b' ≡ k'
  nab' = cakravalaStep D a b m k a' b' k' cancel nab ea eb ek

  cop : Coprime k' b'
  cop = सह-प्रथमता D a b a' b' k'
          (वज्राभ्यासः D a b m k a' b' cancel nab ea eb) nab'

------------------------------------------------------------------------
-- ५ · त्रयोदशम् — D = 13, BHĀSKARA'S OWN WORKED EXAMPLE, IN THE KERNEL.
--
-- The same turn `CakravalaDescent.StepAtThirteen` certifies: from the
-- trivial triple 3² − 13·1² = −4 with m = 1,
--
--     a' = (3·1 + 13·1)/(−4) = −4     b' = (3 + 1·1)/(−4) = −1
--     k' = (1 − 13)/(−4) = 3
--
-- and then, computed rather than asserted:
--
--   वज्राभ्यासः-१३   3·(−1) − 1·(−4) = 1                       (§1)
--   सह-प्रथमता-१३    1·3 + 2·(−1) = 1, i.e. u = b² = 1, v = 2  (§2)
--   श्रेणी-१३        the next multiplier the reactor takes is 2, and
--                   3 ∣ (1 + 2) — it is in the class of −m, as §4 forces.
--
-- (Cubical's ℤ product is unary, so these are stated at turn 0 where the
-- numbers are one digit.  `CakravalaNat.agda` records the same constraint
-- and the same reason.)
------------------------------------------------------------------------

module त्रयोदशम् where

  वज्राभ्यासः-१३ : pos 3 · negsuc 0 - pos 1 · negsuc 3 ≡ pos 1
  वज्राभ्यासः-१३ = refl

  -- u = b·b = 1 and v = a²b' + D·b²·b' − 2·a·b·a' = −9 − 13 + 24 = 2.
  सह-प्रथमता-१३ : pos 1 · pos 3 + pos 2 · negsuc 0 ≡ pos 1
  सह-प्रथमता-१३ = refl

  -- the class of −m mod k' at this turn is {m' : 3 ∣ (1 + m')}, and the
  -- reactor's next multiplier is 2.
  श्रेणी-१३ : pos 1 + pos 2 ≡ pos 3 · pos 1
  श्रेणी-१३ = refl

  -- and it does satisfy the congruence the next turn actually poses,
  -- a' + b'·m' = −4 + (−1)·2 = −6 = 3·(−2).
  सङ्गतिः-१३ : negsuc 3 + negsuc 0 · pos 2 ≡ pos 3 · negsuc 1
  सङ्गतिः-१३ = refl

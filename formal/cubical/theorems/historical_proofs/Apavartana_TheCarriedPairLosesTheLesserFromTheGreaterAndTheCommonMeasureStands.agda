{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- अपवर्तनम् — वहितं युग्मम् अधिकात् न्यूनं जहाति, अपवर्तकश्च तिष्ठति ।
-- (apavartana: the carried pair loses the lesser out of the greater, and
--  its common measure stands.)
--
-- THE TERM, THE TEXT, THE DATE.  अपवर्तन (apavartana) is the reduction of a
-- pair by a common divisor, and with it the fact the pulveriser runs on: a
-- common divisor of two magnitudes divides their sum AND their difference, so
-- the subtractive step preserves it in both directions.  The कुट्टक the
-- reduction serves is ĀRYABHAṬA, *आर्यभटीयम्*, गणितपादः ३२–३३ (499 CE), worked
-- out step by step in BHĀSKARA I, *आर्यभटीयभाष्यम्* (629 CE); the apavartana
-- step itself is stated in BRAHMAGUPTA, *ब्राह्मस्फुटसिद्धान्तः* 18 (628 CE) and
-- worked in BHĀSKARA II, ** (1150 CE).  This citation is taken from
--
-- them here.  NOT that any of them stated the subtractive form: the  of
-- गणितपाद ३२–३३ is a DIVISION procedure (quotients written into the वल्ली),
-- and what is formalised below is the subtractive column that produces those
-- quotients — the same distinction `KuttakaValli_TheSideIsAFreeSlot…` in the
-- `loss` library records as its SECOND DEFECT.  "The greater loses the lesser, the lesser
-- stands" is the movement their pair undergoes, and its common measure
-- is what their procedure keeps.
--
------------------------------------------------------------------------
-- WHY THIS FILE EXISTS — THE FOURTH LAW.
--
-- The `loss` library has three carrier instances, and each says what
-- the CARRIED datum DOES under the step, as an equation in the carried datum
-- alone:
--
--   भावना          क्षेप MULTIPLIES         (भावना-क्षेपः)
--   प्रस्तार        rank SUCCEEDS           (उद्दिष्ट-वृद्धि)
--   अन्त्यसंस्कार   coarseness SCALES by minus the newly-omitted partial
--                  numerator                (मान-अनुपातः)
--
-- The kuṭṭaka instance has base = the three slots (पक्षः / परिमाणम् / शेषः),
-- carried = the pair of magnitudes via उत्थान, and Φ = the subtractive वल्ली
-- step — and it DOES NOT STATE WHAT THE CARRIED PAIR DOES UNDER THE STEP.
-- `वल्ली-वाम` and `वल्ली-दक्षिण` there come close and stop short: they read the
-- next pair out of the BASE's fields (d and k), not out of the pair.  That is
-- the missing fourth law, and §3 below is it:
--
--     अपवर्तन-नियमः : carried (वल्ली-कुट्टक c)  ≡  अन्तरकरण (carried c)
--
-- for EVERY carrier point c, not only descended ones — so the carried pair
-- runs its own recursion, and §3's `अपवर्तन-नियमः-पुनः` says the n-step run of
-- the carrier is the n-step run of `अन्तरकरण` on the pair, with the base never
-- consulted.  What the pair does, in one sentence and three unconditional
-- equations (§2): the greater loses the lesser, the lesser stands, and equals
-- stand.
--
-- The law needs a theorem the कुट्टक module does not have.  It proves the round
-- trip `उत्थान-भेद` (pair → record → pair) and NOT the other one; without
-- `भेद-उत्थान` (record → pair → record, §1 here) the next pair is not known to
-- be a function of the pair at all, and the law cannot even be stated.
--
-- §4 is the arithmetic content the law does not give: the pair's set of common
-- measures is invariant under `अन्तरकरण` in BOTH directions (∣-योग forward,
-- ∣-अन्तर backward), hence under n steps.  §5 runs it: for (48,18) the ten-step
-- orbit lands on (6,6), and both directions of §4 turn that computation into a
-- two-way certificate — म measures 48 and 18 exactly when म measures 6.
--
------------------------------------------------------------------------
-- WHERE THE INVARIANCE ALREADY LIVES.
--
-- The invariance of §4 is in this corpus already.  `Gurutama` (∣-योग, and
-- the descent's result divides both inputs),
-- `GurutamaSiddha` (∣-अन्तर, महत्, सिद्धः — the FULL gcd theorem for the fuelled
-- descent, for every pair), `Apavartana_TwoPresentationsOfDividesAnd…` (absent from this repository) (the
-- difference law crossing between the truncated and untruncated presentations)
-- and `KuttakaSamapti_TheValliIsFiniteForEveryPair` (termination, and the
-- greatest-common-divisor property over ℤ) are all already in this directory
-- and all predate this module; §5's corollaries are stated for TWO NAMED
-- PAIRS ONLY.
--
-- What is new is the SHAPE: the step law of the carrier, stated as an equation
-- in the carried datum, which is the form the other three instances have and
-- this one did not.  §4 is here because a law that says only "the pair moves"
-- and not "and this is what survives the move" would be the weaker half.
--
------------------------------------------------------------------------
-- SELF-CONTAINMENT — REDEFINED, AND SAID.
--
-- This module imports NOTHING from `fibre/src` and nothing from this
-- directory.  `Carrier`, `descend`, `Φ-carrier`, `त्रिक्`, `उत्थान`, `गभीर`,
-- `भेद`, `उत्थान-भेद`, `वल्ली` and `_∣_` are REDEFINED here, character for
-- character where that was possible, so that the two lanes' checks are
-- independent.  They are duplicates and are named as duplicates:
--
--   Carrier, descend, ascend, Φ-carrier  ← Loss.Carrier
--   त्रिक्, उत्थान, गभीर, भेद, उत्थान-भेद, वल्ली
--                                        ← Loss.KuttakaValli_…
--                                          (and त्रिक् is `विवेक` of this
--                                           directory's `LosslessReturn.agda`,
--                                           under a different name)
--   _∣_, ∣-योग                            ← Gurutama (untruncated Σ form; the
--                                          library's `Cubical.Data.Nat.
--                                          Divisibility._∣_` is its
--                                          propositional truncation)
--   ∣-अन्तर                                ← GurutamaSiddha (reproved here by a
--                                          different induction, on the
--                                          quotient rather than on ∸)
--
-- The duplication is deliberate and it is a cost, not a virtue.  It is paid so
-- that a reader checking THIS file has to trust one toolchain invocation and
-- no cross-library build order.
--
------------------------------------------------------------------------
-- DEFECTS.
--
-- 1. THE STEP IS SUBTRACTIVE, NOT DIVISIVE.  `वल्ली` below is anthyphairesis:
--    (a,b) ↦ (a−b, b).  The वल्ली of the *आर्यभटीयम्* is the column of
--    QUOTIENTS.  Everything below that says वल्ली means the column of
--    subtractions that produces them.  `KuttakaSamapti_…` in this directory
--    has the division form.
--
-- 2. THE सम CASE IS A FIXED POINT BY CONVENTION, AND THE CLOSED FORM SPLITS
--    THERE.  Off the diagonal, `अन्तरकरण` is the unordered-pair map
--    {a,b} ↦ {a⊔b − a⊓b, a⊓b}.  ON the diagonal that map would give (0,d) and
--    `अन्तरकरण` gives (d,d), because a total endomorphism has to encode "stop"
--    as a fixed point.  So `अन्तरकरण` is NOT that map, and §2 states three
--    equations rather than one for exactly this reason.  The two disagree on
--    the diagonal and nowhere else; that is a statement about the encoding of
--    termination, not about the arithmetic.
--
-- 3. TERMINATION.  §3's n-step law holds for every n; §5's two runs are `refl` — the
--    machine executes them.  `KuttakaSamapti_TheValliIsFiniteForEveryPair`
--    has the termination theorem.
--
-- 4. `_∣_` HERE IS THE UNTRUNCATED Σ, so it is not a proposition, and two
--    proofs that म measures न need not be equal.  §4's statements are
--    therefore about EXHIBITED quotients, not about a subsingleton of
--    evidence.  `Apavartana_TwoPresentations…` (absent from this repository) §4 in this directory is where
--    that difference is the mathematics; here it is only a choice, made to
--    match `Gurutama` and to keep the file free of the truncation eliminator.
------------------------------------------------------------------------

module Apavartana_TheCarriedPairLosesTheLesserFromTheGreaterAndTheCommonMeasureStands where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_)
open import Cubical.Data.Nat.Properties
  using (+-assoc ; inj-m+ ; m+n≡0→m≡0×n≡0 ; ·-distribʳ)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)

private
  variable
    A B : Type

------------------------------------------------------------------------
-- §0 · THE SUBSTRATE, REDEFINED.  See SELF-CONTAINMENT above: every
-- declaration in this section is a duplicate of one in `Loss.Carrier`
-- or in `Loss.KuttakaValli_…`, and none of them is new.
------------------------------------------------------------------------

record Carrier (f : A → B) : Type where
  constructor carry
  field
    base    : A
    carried : B
    witness : f base ≡ carried

open Carrier public

module _ (f : A → B) where

  -- no pattern match: the carrier's square closes by refl only because this
  -- does not case-split (`Loss.Carrier`, implementation fact 2)
  descend : A → Carrier f
  descend a = carry a (f a) refl

  ascend : Carrier f → A
  ascend c = base c

Φ-carrier : (f : A → B) (Φ : A → A) → Carrier f → Carrier f
Φ-carrier f Φ c = descend f (Φ (ascend f c))

पुनरावृत्ति : (A → A) → ℕ → A → A
पुनरावृत्ति Φ zero    x = x
पुनरावृत्ति Φ (suc n) x = Φ (पुनरावृत्ति Φ n x)

-- त्रिक् — the three slots of one row of the descent.  पक्षः is the
-- constructor (which side the excess fell on), परिमाणम् is d, शेषः is the
-- excess.  सम carries no excess because there is none.
data त्रिक् : Type where
  सम    : (d : ℕ)   → त्रिक्
  वाम   : (d k : ℕ) → त्रिक्
  दक्षिण : (d k : ℕ) → त्रिक्

-- उत्थान — the pair, read back out of the row.  This is the f of the law.
उत्थान : त्रिक् → ℕ × ℕ
उत्थान (सम d)      = d , d
उत्थान (वाम d k)   = d + suc k , d
उत्थान (दक्षिण d k) = d , d + suc k

गभीर : त्रिक् → त्रिक्
गभीर (सम d)      = सम (suc d)
गभीर (वाम d k)   = वाम (suc d) k
गभीर (दक्षिण d k) = दक्षिण (suc d) k

-- भेद — the row, built from the pair.  Decisionless: it falls by structure,
-- and at zero the side that outlasted names itself.
भेद : ℕ → ℕ → त्रिक्
भेद zero    zero    = सम zero
भेद zero    (suc b) = दक्षिण zero b
भेद (suc a) zero    = वाम zero a
भेद (suc a) (suc b) = गभीर (भेद a b)

गभीर-उत्थान : (t : त्रिक्)
            → उत्थान (गभीर t) ≡ (suc (fst (उत्थान t)) , suc (snd (उत्थान t)))
गभीर-उत्थान (सम d)      = refl
गभीर-उत्थान (वाम d k)   = refl
गभीर-उत्थान (दक्षिण d k) = refl

उत्थान-भेद : (a b : ℕ) → उत्थान (भेद a b) ≡ (a , b)
उत्थान-भेद zero    zero    = refl
उत्थान-भेद zero    (suc b) = refl
उत्थान-भेद (suc a) zero    = refl
उत्थान-भेद (suc a) (suc b) =
    गभीर-उत्थान (भेद a b)
  ∙ cong (λ p → (suc (fst p) , suc (snd p))) (उत्थान-भेद a b)

-- वल्ली — the step, written with no comparison, because पक्षः already says
-- which way to subtract.  At सम the algorithm has terminated and the step is
-- the identity: see DEFECT 2.
वल्ली : त्रिक् → त्रिक्
वल्ली (सम d)      = सम d
वल्ली (वाम d k)   = भेद (suc k) d
वल्ली (दक्षिण d k) = भेद d (suc k)

------------------------------------------------------------------------
-- §1 · THE MISSING ROUND TRIP.
--
-- `उत्थान-भेद` (above, duplicated from the kuṭṭaka module) says pair → row →
-- pair is the identity.  The OTHER direction — row → pair → row — is not in
-- that module in any form, and without it nothing below can be stated: the
-- next pair is a function of the current pair only because the current pair
-- reconstructs the current row.
--
-- Each of the three lemmas is an induction on the shared magnitude d, and
-- each is exactly `गभीर` climbing back up the spine one head at a time.
------------------------------------------------------------------------

भेद-सम : (d : ℕ) → भेद d d ≡ सम d
भेद-सम zero    = refl
भेद-सम (suc d) = cong गभीर (भेद-सम d)

भेद-वाम : (d k : ℕ) → भेद (d + suc k) d ≡ वाम d k
भेद-वाम zero    k = refl
भेद-वाम (suc d) k = cong गभीर (भेद-वाम d k)

भेद-दक्षिण : (d k : ℕ) → भेद d (d + suc k) ≡ दक्षिण d k
भेद-दक्षिण zero    k = refl
भेद-दक्षिण (suc d) k = cong गभीर (भेद-दक्षिण d k)

भेद-उत्थान : (t : त्रिक्) → भेद (fst (उत्थान t)) (snd (उत्थान t)) ≡ t
भेद-उत्थान (सम d)      = भेद-सम d
भेद-उत्थान (वाम d k)   = भेद-वाम d k
भेद-उत्थान (दक्षिण d k) = भेद-दक्षिण d k

------------------------------------------------------------------------
-- §2 · अन्तरकरण — THE STEP, AS A MAP OF PAIRS.
--
-- The name is a compound BUILT HERE (अन्तर, difference, + करण, making).  The
-- object is: run the pair down into its row, step the row, read
-- the pair back.  §3 is the theorem that this is the same thing as stepping
-- the carrier.
--
-- The three equations are unconditional and exhaustive — every pair of
-- naturals has exactly one of the three forms — and together they are the
-- whole answer to "what does the carried pair DO under the step":
--
--     THE GREATER LOSES THE LESSER.  THE LESSER STANDS.  EQUALS STAND.
------------------------------------------------------------------------

अन्तरकरण : ℕ × ℕ → ℕ × ℕ
अन्तरकरण p = उत्थान (वल्ली (भेद (fst p) (snd p)))

अन्तरकरण-सम : (d : ℕ) → अन्तरकरण (d , d) ≡ (d , d)
अन्तरकरण-सम d = cong (λ t → उत्थान (वल्ली t)) (भेद-सम d)

-- the greater on the left: (d + suc k , d) ↦ (suc k , d)
अन्तरकरण-वाम : (d k : ℕ) → अन्तरकरण (d + suc k , d) ≡ (suc k , d)
अन्तरकरण-वाम d k =
    cong (λ t → उत्थान (वल्ली t)) (भेद-वाम d k)
  ∙ उत्थान-भेद (suc k) d

-- the greater on the right: (d , d + suc k) ↦ (d , suc k)
अन्तरकरण-दक्षिण : (d k : ℕ) → अन्तरकरण (d , d + suc k) ≡ (d , suc k)
अन्तरकरण-दक्षिण d k =
    cong (λ t → उत्थान (वल्ली t)) (भेद-दक्षिण d k)
  ∙ उत्थान-भेद d (suc k)

------------------------------------------------------------------------
-- §3 · THE FOURTH LAW.
--
-- कुट्टक = Carrier उत्थान: base = the row, carried = the pair.  The step lifts
-- by `Φ-carrier`, and the carrier square is `refl` — that is the law of
-- `Loss.Carrier` and is not re-proved here.  What IS proved here is
-- the thing the कुट्टक module never states: the carried pair's next value is a
-- function OF THE CARRIED PAIR, and the function is `अन्तरकरण`.
--
-- Stated for an arbitrary carrier point, not only a descended one.  For a
-- descended point it is `cong` on §1 alone; the general case additionally
-- transports along the point's own witness, which is what makes the statement
-- about the carrier rather than about the base.
------------------------------------------------------------------------

कुट्टक : Type
कुट्टक = Carrier उत्थान

अवतरण : त्रिक् → कुट्टक
अवतरण = descend उत्थान

आरोहः : कुट्टक → त्रिक्
आरोहः = ascend उत्थान

वल्ली-कुट्टक : कुट्टक → कुट्टक
वल्ली-कुट्टक = Φ-carrier उत्थान वल्ली

-- the law, on a descended point
अपवर्तन-नियमः-अवतरणे : (t : त्रिक्)
                     → carried (वल्ली-कुट्टक (अवतरण t)) ≡ अन्तरकरण (carried (अवतरण t))
अपवर्तन-नियमः-अवतरणे t = cong (λ u → उत्थान (वल्ली u)) (sym (भेद-उत्थान t))

-- THE LAW.  Every carrier point, descended or not.
अपवर्तन-नियमः : (c : कुट्टक) → carried (वल्ली-कुट्टक c) ≡ अन्तरकरण (carried c)
अपवर्तन-नियमः c =
    अपवर्तन-नियमः-अवतरणे (base c)
  ∙ cong अन्तरकरण (witness c)

-- …and therefore the carried pair runs its OWN recursion: n steps of the
-- carrier, read at the carried slot, are n steps of `अन्तरकरण` on the pair,
-- with the base never consulted.  This is the statement the three sibling
-- instances have and this one did not.
अपवर्तन-नियमः-पुनः : (n : ℕ) (c : कुट्टक)
                   → carried (पुनरावृत्ति वल्ली-कुट्टक n c)
                   ≡ पुनरावृत्ति अन्तरकरण n (carried c)
अपवर्तन-नियमः-पुनः zero    c = refl
अपवर्तन-नियमः-पुनः (suc n) c =
    अपवर्तन-नियमः (पुनरावृत्ति वल्ली-कुट्टक n c)
  ∙ cong अन्तरकरण (अपवर्तन-नियमः-पुनः n c)

------------------------------------------------------------------------
-- §4 · WHAT SURVIVES THE MOVE — अपवर्तन PROPER.
--
-- `_∣_` is the untruncated Σ (DEFECT 4), duplicated from `Gurutama`.  `∣-योग`
-- is `Gurutama`'s; `∣-अन्तर` is `GurutamaSiddha`'s theorem reproved by a
-- different induction — on the quotient, with `inj-m+` doing the cancelling —
-- so that this file needs neither ∸ nor the propositional truncation.
------------------------------------------------------------------------

_∣_ : ℕ → ℕ → Type
म ∣ न = Σ[ q ∈ ℕ ] (q · म ≡ न)

∣-योग : {म x y : ℕ} → म ∣ x → म ∣ y → म ∣ (x + y)
∣-योग {म} (qx , px) (qy , py) =
  (qx + qy) , sym (·-distribʳ qx qy म) ∙ cong₂ _+_ px py

-- वियोग — the cancellation.  Induction on the FIRST quotient: at zero the
-- remaining quotient is the answer outright; at zero on the other side the
-- whole sum is zero, so y is zero and zero measures it; otherwise one copy of
-- म is cancelled off both sides and the induction proceeds.
वियोग : (म y q p : ℕ) → q · म + y ≡ p · म → Σ[ r ∈ ℕ ] (r · म ≡ y)
वियोग म y zero     p        eq = p , sym eq
वियोग म y (suc q) zero      eq = zero , sym (snd (m+n≡0→m≡0×n≡0 eq))
वियोग म y (suc q) (suc p)   eq =
  वियोग म y q p (inj-m+ (+-assoc म (q · म) y ∙ eq))

∣-अन्तर : {म x y : ℕ} → म ∣ (x + y) → म ∣ x → म ∣ y
∣-अन्तर {म} {x} {y} (p , pp) (q , qq) =
  वियोग म y q p (cong (_+ y) qq ∙ sym pp)

-- साधारण म p — म is a common measure of the pair p.
साधारण : ℕ → ℕ × ℕ → Type
साधारण म p = (म ∣ fst p) × (म ∣ snd p)

-- FORWARD: the step cannot create a common measure that was not there.
अपवर्तन-रक्षा : (म : ℕ) (p : ℕ × ℕ) → साधारण म p → साधारण म (अन्तरकरण p)
अपवर्तन-रक्षा म (a , b) h = लक्ष्य (भेद a b) (subst (साधारण म) (sym (उत्थान-भेद a b)) h)
  where
    लक्ष्य : (t : त्रिक्) → साधारण म (उत्थान t) → साधारण म (उत्थान (वल्ली t))
    लक्ष्य (सम d)      hh = hh
    लक्ष्य (वाम d k)   (h₁ , h₂) =
      subst (साधारण म) (sym (उत्थान-भेद (suc k) d)) (∣-अन्तर h₁ h₂ , h₂)
    लक्ष्य (दक्षिण d k) (h₁ , h₂) =
      subst (साधारण म) (sym (उत्थान-भेद d (suc k))) (h₁ , ∣-अन्तर h₂ h₁)

-- BACKWARD: the step cannot destroy one either.
अपवर्तन-प्रत्यागमः : (म : ℕ) (p : ℕ × ℕ) → साधारण म (अन्तरकरण p) → साधारण म p
अपवर्तन-प्रत्यागमः म (a , b) h =
  subst (साधारण म) (उत्थान-भेद a b) (लक्ष्य (भेद a b) h)
  where
    लक्ष्य : (t : त्रिक्) → साधारण म (उत्थान (वल्ली t)) → साधारण म (उत्थान t)
    लक्ष्य (सम d)      hh = hh
    लक्ष्य (वाम d k)   hh =
      let (h₁ , h₂) = subst (साधारण म) (उत्थान-भेद (suc k) d) hh
      in ∣-योग h₂ h₁ , h₂
    लक्ष्य (दक्षिण d k) hh =
      let (h₁ , h₂) = subst (साधारण म) (उत्थान-भेद d (suc k)) hh
      in h₁ , ∣-योग h₁ h₂

-- …and so over the whole run, in both directions.
अपवर्तन-रक्षा-पुनः : (म : ℕ) (n : ℕ) (p : ℕ × ℕ)
                   → साधारण म p → साधारण म (पुनरावृत्ति अन्तरकरण n p)
अपवर्तन-रक्षा-पुनः म zero    p h = h
अपवर्तन-रक्षा-पुनः म (suc n) p h =
  अपवर्तन-रक्षा म (पुनरावृत्ति अन्तरकरण n p) (अपवर्तन-रक्षा-पुनः म n p h)

अपवर्तन-प्रत्यागमः-पुनः : (म : ℕ) (n : ℕ) (p : ℕ × ℕ)
                        → साधारण म (पुनरावृत्ति अन्तरकरण n p) → साधारण म p
अपवर्तन-प्रत्यागमः-पुनः म zero    p h = h
अपवर्तन-प्रत्यागमः-पुनः म (suc n) p h =
  अपवर्तन-प्रत्यागमः-पुनः म n p
    (अपवर्तन-प्रत्यागमः म (पुनरावृत्ति अन्तरकरण n p) h)

------------------------------------------------------------------------
-- §5 · IT RUNS.
--
-- Every equation in this section holds by `refl`, so Agda executes them.
-- The corollaries are for THESE TWO PAIRS and no others — see "WHERE THE
-- INVARIANCE ALREADY LIVES" and DEFECT 3.
------------------------------------------------------------------------

गणना-प्रथमम् : अन्तरकरण (137 , 60) ≡ (77 , 60)
गणना-प्रथमम् = refl

गणना-अन्तः : पुनरावृत्ति अन्तरकरण 20 (137 , 60) ≡ (1 , 1)
गणना-अन्तः = refl

गणना-षट् : पुनरावृत्ति अन्तरकरण 10 (48 , 18) ≡ (6 , 6)
गणना-षट् = refl

-- the carrier's run and the pair's run agree — §3 applied to a computed orbit
गणना-कुट्टक : carried (पुनरावृत्ति वल्ली-कुट्टक 20 (अवतरण (भेद 137 60)))
            ≡ पुनरावृत्ति अन्तरकरण 20 (137 , 60)
गणना-कुट्टक =
    अपवर्तन-नियमः-पुनः 20 (अवतरण (भेद 137 60))
  ∙ cong (पुनरावृत्ति अन्तरकरण 20) (उत्थान-भेद 137 60)

-- A TWO-WAY CERTIFICATE FOR ONE PAIR.  §4 in both directions, carried along
-- the ten steps §5 computes: म measures 48 and 18 exactly when म measures 6.
अष्टचत्वारिंशत्-अष्टादश-अपवर्तकः : (म : ℕ) → साधारण म (48 , 18) → म ∣ 6
अष्टचत्वारिंशत्-अष्टादश-अपवर्तकः म h =
  fst (subst (साधारण म) गणना-षट् (अपवर्तन-रक्षा-पुनः म 10 (48 , 18) h))

अष्टचत्वारिंशत्-अष्टादश-साधारणः : (म : ℕ) → म ∣ 6 → साधारण म (48 , 18)
अष्टचत्वारिंशत्-अष्टादश-साधारणः म h =
  अपवर्तन-प्रत्यागमः-पुनः म 10 (48 , 18) (subst (साधारण म) (sym गणना-षट्) (h , h))

-- and for (137,60) the orbit lands on (1,1), so every common measure of the
-- two measures 1.
सप्तत्रिंशदधिकशत-षष्टि-अपवर्तकः : (म : ℕ) → साधारण म (137 , 60) → म ∣ 1
सप्तत्रिंशदधिकशत-षष्टि-अपवर्तकः म h =
  fst (subst (साधारण म) गणना-अन्तः (अपवर्तन-रक्षा-पुनः म 20 (137 , 60) h))

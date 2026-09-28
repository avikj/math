{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- MatraVrtta_TheLeastVarnaIsFixedByTheMatraCountAndNoLeastPatternIs
--
-- ON THE NAME.  The object is the *mtr-vtta*: a metre fixed by its
-- total duration in mtr rather than by its syllable count.  Pigala,
-- *Chandaḥśāstra* (c. 300–200 BCE), ch. 8, fixes the two per-syllable
-- weights — laghu = 1 mātrā, guru = 2 — and the six *pratyaya* on the
-- resulting patterns.  Virahāṅka, *Vṛttajātisamuccaya* (c. 600–800 CE),
-- ch. 6, states the addition rule for mtr-vtta explicitly; Halyudha,
-- *Mtasajvan* (10th c.), writes the array out.  The Syllable/Pattern/
-- mora/matraOf/varna vocabulary below is imported, not redefined, from
-- `PingalaPrastara`, whose header carries the same citations in full.
-- No term is invented and nothing here is a claim about what those texts
-- proved: the two theorems in §3 are this corpus's, about their object.
--
-- Grepped before writing (`notes/`): Chandastra 12, ryabhaya 17,
-- Bjagaita 9, mtrmeru 10, prastra 13, laghu 6, guru 7, mtr 11,
-- Conics 1, symptma 1.  `mtrvtta` 0 in notes/ and 0 repo-wide, so the
-- object is named here for the first time; `Metre n` in `PingalaPrastara`
-- is that object under an English gloss and is what is reused.
--
-- ────────────────────────────────────────────────────────────────────
-- THE ITEM.  Fix the total mtr count `m` of a pattern.  Two questions:
--
--   (A)  What is the least number of syllables (vara) among patterns of
--        duration `m`?
--   (B)  WHICH pattern of duration `m` has that least syllable count?
--
-- (A) is answered by `m` alone and the answer is unique.  (B) is not
-- answered by `m` at all, and the failure is not a gap in technique: at
-- `m = 3` the two least patterns are laghu-guru and guru-laghu, which are
-- each other's retrograde, so any chooser that respects retrogradation —
-- a symmetry of BOTH statistics, proved below as `rev-least` — has no
-- value to take.
--
-- WHAT SPLITS.  `varna` is not a function of `matraOf` (`noDecoder-instance`,
-- §3.1): two laghu have the duration of one guru.  So the duration forgets
-- the syllable count outright.  But the LEAST syllable count survives, and
-- the reason it survives is an h-level fact and nothing about metre:
-- `IsLeast e n` has its attainment clause under `∥_∥₁` (it must, or it
-- would carry a chosen pattern), and the uniqueness proof `leastUnique`
-- gets past that truncation only because its goal `m ≡ n` is a proposition
-- (`isSetℕ`), so `PT.rec2` applies.  Had the goal been the WITNESS — a
-- pattern, which is structure — the same argument is blocked.  §3.2 shows
-- it is not merely blocked but false-under-symmetry.
--
-- This is the step `NaturalMachine.TheOpenPigeonhole…` isolates for
-- `isEquiv obs`, met again on a different object; that module is cited,
-- not used, and nothing of it is amended.
--
-- APOLLONIUS, named because the distinction is his and predates every
-- Indian source cited above.  *Conics* (c. 200 BCE) classifies a section
-- by its *symptma*, the area relation its ordinate satisfies against a
-- fixed diameter, and Book I.11–13 establishes it before any coordinate
-- system exists to state it in.  The *symptma* is what survives change of
-- diameter; the particular diameter is a choice.  That is the shape of §3
-- and the mathematics of the distinction is Apollonius's, not this
-- corpus's and not an Indian source's — hence no  label is
-- attached to the general layer in §1, which carries the English name
-- only (CLAUDE.md (absent from this repository) file-naming note 2).  Books V–VII of the *Conics*
-- survive only in the Arabic of Thbit ibn Qurra and the Ban Ms
-- (Baghdad, 9th c.); Book VIII is lost.  Named because that is the
-- transmission chain, and because the grep above found Thbit ibn Qurra
-- and the Banū Mūsā at 0 occurrences repo-wide against Apollonius at 8 —
-- the author cited, the transmitters not.
--
-- WHAT IS PROVED
--   §1  Formation             a general (histories, endpoints, ev, cost)
--       noDecoder             cost is not a function of the endpoint, from
--                             any two same-endpoint different-cost histories
--       isPropIsLeast         "n is the least cost at e" is a proposition
--       leastUnique           …and therefore determines n uniquely — the
--                             `PT.rec2`-into-`isSetℕ` step
--       σ-preserves-least     a symmetry of ev and c acts on least witnesses
--       noEquivariantLeastChoice
--                             …so an equivariant chooser is a fixed point of
--                             that action, and dies where there is none
--   §2  the mtr-vtta instance, with `rev` (retrogradation) as symmetry
--   §3.1 varna is not a function of matraOf              (two laghu = one guru)
--   §3.2 least varna at mtr 3 is 2 and is unique;
--        no retrograde-equivariant chooser of a least pattern exists
--   §3.3 the claim I formed and killed: least witnesses are NOT essentially
--        unique (`leastPatternsAt3-notUnique`), and the located reason is
--        that their type is not a proposition (`leastPatternsAt3-notProp`)
--        while `IsLeast` is (`leastNumberAt3-isProp`)
--   §3.4 both negated types are inhabitable on other formations, so neither
--        negation is vacuous by typing
--
-- `--guardedness` is carried from `PingalaPrastara` and is infective.
------------------------------------------------------------------------

module MatraVrtta_TheLeastVarnaIsFixedByTheMatraCountAndNoLeastPatternIs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp× ; isPropΠ)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties
  using (znots ; snotz ; injSuc ; isSetℕ ; +-zero ; +-comm ; +-assoc)
open import Cubical.Data.Nat.Order using (_≤_ ; isProp≤ ; ≤-antisym ; ≤-refl ; zero-≤ ; suc-≤-suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; rev)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Bool.Properties using (true≢false ; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)
open import Cubical.Relation.Nullary using (¬_)

open import PingalaPrastara
  using (Syllable ; laghu ; guru ; Pattern ; mora ; matraOf ; varna)

------------------------------------------------------------------------
-- §1.  Formations.
--
-- A formation is histories `W`, endpoints `E`, an accumulation `ev` that
-- forgets the history, and a cost `c` on histories.  No  term is
-- claimed for this layer; the distinction it makes is Apollonius's (see
-- the header) and inventing a label would assert a provenance nobody
-- checked.
------------------------------------------------------------------------

module Formation {W E : Type} (ev : W → E) (c : W → ℕ) where

  -- A history realising endpoint `e` at cost `n`.
  Witness : E → ℕ → W → Type
  Witness e n w = (ev w ≡ e) × (c w ≡ n)

  ------------------------------------------------------------------
  -- 1.1  The endpoint does not carry the cost.
  ------------------------------------------------------------------

  Decoder : Type
  Decoder = Σ[ d ∈ (E → ℕ) ] ((w : W) → d (ev w) ≡ c w)

  noDecoder : (u v : W) → ev u ≡ ev v → ¬ (c u ≡ c v) → ¬ Decoder
  noDecoder u v same differ (d , decodes) =
    differ (sym (decodes u) ∙ cong d same ∙ decodes v)

  ------------------------------------------------------------------
  -- 1.2  …but the LEAST cost does, and it is an h-level fact that it does.
  --
  -- The attainment clause is truncated deliberately.  Untruncated it
  -- would carry a chosen history, and §3.2 shows that datum is not
  -- available from the endpoint.
  ------------------------------------------------------------------

  IsLeast : E → ℕ → Type
  IsLeast e n = ∥ (Σ[ w ∈ W ] Witness e n w) ∥₁
              × ((w : W) → ev w ≡ e → n ≤ c w)

  isPropIsLeast : (e : E) (n : ℕ) → isProp (IsLeast e n)
  isPropIsLeast e n =
    isProp× isPropPropTrunc (isPropΠ λ w → isPropΠ λ _ → isProp≤)

  -- The step the module is named for.  `PT.rec2` is legal here for one
  -- reason and one only: the goal `m ≡ n` lies in ℕ, which is a set, so
  -- the goal is a proposition.  Both anonymous minimisers may therefore be
  -- named at once, and neither name escapes.
  leastUnique : (e : E) (m n : ℕ) → IsLeast e m → IsLeast e n → m ≡ n
  leastUnique e m n (attainedM , leastM) (attainedN , leastN) =
    PT.rec2 (isSetℕ m n) compare attainedM attainedN
    where
      compare : (Σ[ w ∈ W ] Witness e m w) → (Σ[ v ∈ W ] Witness e n v) → m ≡ n
      compare (w , evw , cw) (v , evv , cv) =
        ≤-antisym (subst (m ≤_) cv (leastM v evv))
                  (subst (n ≤_) cw (leastN w evw))

  ------------------------------------------------------------------
  -- 1.3  A symmetry of the formation acts on least witnesses, so a chooser
  --      that respects the symmetry must land on a fixed point of it.
  ------------------------------------------------------------------

  module Symmetry (σ : W → W)
                  (σ-ev : (w : W) → ev (σ w) ≡ ev w)
                  (σ-c  : (w : W) → c (σ w) ≡ c w) where

    σ-preserves-least : (e : E) (n : ℕ) (w : W) → Witness e n w → Witness e n (σ w)
    σ-preserves-least e n w (evw , cw) = (σ-ev w ∙ evw) , (σ-c w ∙ cw)

    -- A rule assigning, to each endpoint-and-least-cost, a least history,
    -- invariantly under the symmetry.
    EquivariantLeastChoice : Type
    EquivariantLeastChoice =
      Σ[ pick ∈ (E → ℕ → W) ]
        ( ((e : E) (n : ℕ) → IsLeast e n → Witness e n (pick e n))
        × ((e : E) (n : ℕ) → σ (pick e n) ≡ pick e n) )

    equivariantChoiceIsAFixedPoint :
      EquivariantLeastChoice
      → (e : E) (n : ℕ) → IsLeast e n
      → Σ[ w ∈ W ] (Witness e n w × (σ w ≡ w))
    equivariantChoiceIsAFixedPoint (pick , correct , fixed) e n isLeast =
      pick e n , correct e n isLeast , fixed e n

    noEquivariantLeastChoice :
        (e : E) (n : ℕ) → IsLeast e n
      → ((w : W) → Witness e n w → ¬ (σ w ≡ w))
      → ¬ EquivariantLeastChoice
    noEquivariantLeastChoice e n isLeast noFixed choice =
      let (w , witness , isFixed) = equivariantChoiceIsAFixedPoint choice e n isLeast
      in noFixed w witness isFixed

------------------------------------------------------------------------
-- §2.  The mtr-vtta instance.
--
-- Histories are patterns, the endpoint is the mtr count, the cost is
-- the vara count, and the symmetry is retrogradation: reading the vtta
-- backwards preserves both statistics.
------------------------------------------------------------------------

matraOf-++ : (p q : Pattern) → matraOf (p ++ q) ≡ matraOf p + matraOf q
matraOf-++ []      q = refl
matraOf-++ (s ∷ p) q =
  cong (mora s +_) (matraOf-++ p q) ∙ +-assoc (mora s) (matraOf p) (matraOf q)

varna-++ : (p q : Pattern) → varna (p ++ q) ≡ varna p + varna q
varna-++ []      q = refl
varna-++ (s ∷ p) q = cong suc (varna-++ p q)

matraOf-rev : (p : Pattern) → matraOf (rev p) ≡ matraOf p
matraOf-rev []      = refl
matraOf-rev (s ∷ p) =
    matraOf-++ (rev p) (s ∷ [])
  ∙ cong (_+ (mora s + 0)) (matraOf-rev p)
  ∙ cong (matraOf p +_) (+-zero (mora s))
  ∙ +-comm (matraOf p) (mora s)

varna-rev : (p : Pattern) → varna (rev p) ≡ varna p
varna-rev []      = refl
varna-rev (s ∷ p) =
    varna-++ (rev p) (s ∷ [])
  ∙ cong (_+ 1) (varna-rev p)
  ∙ +-comm (varna p) 1

open Formation matraOf varna public
open Formation.Symmetry matraOf varna rev matraOf-rev varna-rev public

-- Retrogradation is a symmetry of the whole formation, so demanding that a
-- chooser respect it is not an arbitrary side condition.
rev-least : (m n : ℕ) (p : Pattern) → Witness m n p → Witness m n (rev p)
rev-least = σ-preserves-least

------------------------------------------------------------------------
-- §3.  The split, on this instance.
------------------------------------------------------------------------

private
  -- one guru and two laghu have the same duration and different vara
  ekaGuru dviLaghu : Pattern
  ekaGuru  = guru ∷ []
  dviLaghu = laghu ∷ laghu ∷ []

  laghuGuru guruLaghu : Pattern
  laghuGuru = laghu ∷ guru ∷ []
  guruLaghu = guru ∷ laghu ∷ []

  -- a Bool-valued discriminator on the head syllable, to separate the two
  headIsGuru : Pattern → Bool
  headIsGuru (guru ∷ _) = true
  headIsGuru _          = false

  laghuGuru≢guruLaghu : ¬ (laghuGuru ≡ guruLaghu)
  laghuGuru≢guruLaghu p = false≢true (cong headIsGuru p)

  guruLaghu≢laghuGuru : ¬ (guruLaghu ≡ laghuGuru)
  guruLaghu≢laghuGuru p = true≢false (cong headIsGuru p)

  ¬2≡1 : ¬ (2 ≡ 1)
  ¬2≡1 p = snotz (injSuc p)

  ¬0≡3 : ¬ (0 ≡ 3)
  ¬0≡3 = znots

  ¬1≡3 : ¬ (1 ≡ 3)
  ¬1≡3 p = znots (injSuc p)

  ¬2≡3 : ¬ (2 ≡ 3)
  ¬2≡3 p = znots (injSuc (injSuc p))

  ¬4≡3 : ¬ (4 ≡ 3)
  ¬4≡3 p = snotz (injSuc (injSuc (injSuc p)))

------------------------------------------------------------------------
-- 3.1  RYABHAA'S SIDE.  The duration does not carry the syllable count:
--      substituting two laghu for one guru is invisible to `matraOf` and
--      changes `varna`.  So the trace is not recoverable from the endpoint.
------------------------------------------------------------------------

sameMatra : matraOf dviLaghu ≡ matraOf ekaGuru
sameMatra = refl

differentVarna : ¬ (varna dviLaghu ≡ varna ekaGuru)
differentVarna = ¬2≡1

varnaIsNotAFunctionOfMatra : ¬ Decoder
varnaIsNotAFunctionOfMatra = noDecoder dviLaghu ekaGuru sameMatra differentVarna

------------------------------------------------------------------------
-- 3.2  BHSKARA'S SIDE, and its exact limit.
--
--   the NUMBER descends from the endpoint (leastVarnaAt3-unique)
--   the WITNESS does not (noRetrogradeChooser)
------------------------------------------------------------------------

-- Every pattern of duration 3 has at least two syllables.
twoIsALowerBound : (p : Pattern) → matraOf p ≡ 3 → 2 ≤ varna p
twoIsALowerBound []                  q = ⊥rec (¬0≡3 q)
twoIsALowerBound (laghu ∷ [])        q = ⊥rec (¬1≡3 q)
twoIsALowerBound (guru  ∷ [])        q = ⊥rec (¬2≡3 q)
twoIsALowerBound (s ∷ t ∷ p)         q = suc-≤-suc (suc-≤-suc zero-≤)

leastVarnaAt3 : IsLeast 3 2
leastVarnaAt3 = ∣ laghuGuru , refl , refl ∣₁ , twoIsALowerBound

-- The number is fixed by the mtr count alone.  This is `leastUnique`,
-- whose only non-formal step is `PT.rec2` into `isSetℕ`.
leastVarnaAt3-unique : (n : ℕ) → IsLeast 3 n → n ≡ 2
leastVarnaAt3-unique n isLeast = leastUnique 3 n 2 isLeast leastVarnaAt3

-- The witness is not.  First, there are exactly two of them.
twoLeastPatterns : (p : Pattern) → Witness 3 2 p → (p ≡ laghuGuru) ⊎ (p ≡ guruLaghu)
twoLeastPatterns []                          (_ , v) = ⊥rec (znots v)
twoLeastPatterns (s ∷ [])                    (_ , v) = ⊥rec (znots (injSuc v))
twoLeastPatterns (laghu ∷ laghu ∷ [])        (m , _) = ⊥rec (¬2≡3 m)
twoLeastPatterns (laghu ∷ guru  ∷ [])        _       = inl refl
twoLeastPatterns (guru  ∷ laghu ∷ [])        _       = inr refl
twoLeastPatterns (guru  ∷ guru  ∷ [])        (m , _) = ⊥rec (¬4≡3 m)
twoLeastPatterns (s ∷ t ∷ u ∷ p)             (_ , v) = ⊥rec (snotz (injSuc (injSuc v)))

-- …and they are each other's retrograde, so neither is retrograde-fixed.
noLeastPatternIsRetrogradeFixed : (p : Pattern) → Witness 3 2 p → ¬ (rev p ≡ p)
noLeastPatternIsRetrogradeFixed p w fixed with twoLeastPatterns p w
... | inl q = guruLaghu≢laghuGuru (sym (cong rev q) ∙ fixed ∙ q)
... | inr q = laghuGuru≢guruLaghu (sym (cong rev q) ∙ fixed ∙ q)

-- The refutation of the transfer.  A rule that assigns a least pattern to
-- each duration, invariantly under retrogradation, does not exist.
noRetrogradeChooser : ¬ EquivariantLeastChoice
noRetrogradeChooser =
  noEquivariantLeastChoice 3 2 leastVarnaAt3 noLeastPatternIsRetrogradeFixed

------------------------------------------------------------------------
-- 3.3  THE CLAIM I FORMED, AND ITS DEATH.
--
-- Writing §1.2 I formed this: *since `IsLeast e n` is a proposition and
-- `leastUnique` gets the number past the truncation, the whole
-- minimisation descends to the endpoint — the least witness too, because
-- least witnesses at one endpoint all have the same cost, and cost is what
-- distinguishes histories.*  The second half is false, and it is false for
-- a reason that is visible without any symmetry argument: cost is NOT what
-- distinguishes histories.
--
-- The two checks below are the refutation.  The first kills the essential-
-- uniqueness claim outright.  The second says exactly which hypothesis of
-- `PT.rec` fails, so the failure is located rather than merely exhibited:
-- the goal in the witness case is not a proposition, and that is the same
-- boundary `NaturalMachine.TheOpenPigeonhole…` reports for `isEquiv obs`
-- against `X ≃ Y`.
------------------------------------------------------------------------

-- CONTRAST, the surviving half: the least-cost NUMBER question is
-- proposition-valued, so `PT.rec2` applies to it and `leastUnique` runs.
leastNumberAt3-isProp : (n : ℕ) → isProp (IsLeast 3 n)
leastNumberAt3-isProp = isPropIsLeast 3

-- REFUTED (a): least witnesses at one endpoint are not essentially unique.
leastPatternsAt3-notUnique :
  ¬ ((p q : Pattern) → Witness 3 2 p → Witness 3 2 q → p ≡ q)
leastPatternsAt3-notUnique allEqual =
  laghuGuru≢guruLaghu
    (allEqual laghuGuru guruLaghu (refl , refl) (refl , refl))

-- REFUTED (b), located: the least-cost WITNESS question is not
-- proposition-valued, so the step that carried the number cannot carry it.
leastPatternsAt3-notProp : ¬ isProp (Σ[ p ∈ Pattern ] Witness 3 2 p)
leastPatternsAt3-notProp isP =
  laghuGuru≢guruLaghu
    (cong fst (isP (laghuGuru , refl , refl) (guruLaghu , refl , refl)))

------------------------------------------------------------------------
-- 3.4  THE NEGATIONS ARE NOT VACUOUS.
--
-- A `¬ T` whose `T` is uninhabitable by construction says nothing.  Both
-- negated types above are inhabitable, exhibited on formations where the
-- endpoint does carry what is asked of it.
------------------------------------------------------------------------

private
  -- `Decoder` is inhabited when the endpoint IS the cost, so §3.1 negates a
  -- real statement about `matraOf` and not a mis-stated type.
  module VarnaOnVarna = Formation {W = Pattern} {E = ℕ} varna varna

  decoderExists : VarnaOnVarna.Decoder
  decoderExists = (λ n → n) , (λ p → refl)

  -- `EquivariantLeastChoice` is inhabited on a formation with no tie to
  -- break, so §3.2 negates a real statement about the mtr-vtta and not a
  -- type that nothing could satisfy.
  module Trivial  = Formation {W = ℕ} {E = ℕ} (λ n → n) (λ n → n)
  module TrivialS = Trivial.Symmetry (λ n → n) (λ _ → refl) (λ _ → refl)

  trivialLeast : (e : ℕ) → Trivial.IsLeast e e
  trivialLeast e = ∣ e , refl , refl ∣₁ , (λ w q → subst (e ≤_) (sym q) ≤-refl)

  choiceExists : TrivialS.EquivariantLeastChoice
  choiceExists =
      (λ e n → e)
    , (λ e n isLeast → refl , sym (Trivial.leastUnique e n e isLeast (trivialLeast e)))
    , (λ e n → refl)

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- यन्त्र-तन्तुः — यन्त्रं स्व-अर्थ-तन्तौ वसति ।
--
-- (the engine lives in the fiber of its own denotation.)
--
-- `Fiberjala_TheFibreHasThreeVerdictsAndIsContrMergesTwoOfThem` states the
-- criterion: WHICH SIDE OF `f a ≡ b` IS BOUND.  Bind b and you have
-- `singl`, एकम् always and free.  Bind a and you have `fiber`, which is
-- any of the three — रिक्तम्, एकम्, बहु.
--
-- `interactive/MathMachine.hs` (absent from this repository) is a fiber navigator and did not know it.  Its
-- denotation map is ⟦_⟧, terms to meanings, and every organ it has is a
-- response to one of the three verdicts on that map's fibers:
--
--   बहु      many terms, one meaning.  THIS IS WHERE THE ENGINE LIVES.
--            Its rewrite rules move inside one fiber and never leave it
--            (§४ is `Alopa.अलोपः` read as a fiber statement), and लाघव —
--            the size it is trying to reduce — is a function ON the fiber
--            which the base cannot see at all (`Laghava`:
--            no function of the denotation computes the size).  Searching
--            inside a बहु fiber is the whole of what the engine does.
--   रिक्तम्   no term denotes this meaning.  §५ exhibits one: with this
--            vocabulary every term vanishes at the zero environment, so
--            the constant 1 has an EMPTY fiber.  No amount of rewriting
--            reaches it.  This is the exact condition under which
--            inventing a symbol is the only move — and the engine's
--            invention step currently fires on a description-length gain
--            instead, which is a fact about बहु and says nothing about
--            रिक्तम्.
--   एकम्     nothing to search; the datum rides free.
--
-- AND THE SAMPLER BINDS NEITHER SIDE.  The engine's conjecture step draws
-- forty environments and compares.  An environment is a point of `Env`,
-- and `Env` is the DOMAIN of the meanings — neither the a nor the b of
-- the equation whose fiber is being asked about.  So the criterion
-- explains the failure that `Alopa` §८ exhibits: `var 0` and `var 1`
-- agree on every constant environment, infinitely many samples, all
-- confirming, and they are not equal.  More samples cannot help because
-- samples are not on the axis.
--
-- Every declaration below is an instantiation, a `refl`, or one line.
-- `LosslessReturn_TheHandProofWasUnnecessaryAndTransportGivesIt` records
-- the rule this follows: where a joint takes work, the joint is wrong.
------------------------------------------------------------------------

module MachineFiber_TheEngineLivesInTheFiberOfItsDenotation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; znots)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Alopa_TheEngineNeverTouchesTheMeaning
  using (Term ; var ; op ; Env ; eval ; Rule ; lhs ; normalize ; अलोपः)

open import Fiberjala_TheFiberHasThreeVerdictsAndIsContrMergesTwoOfThem
  using (रिक्तम् ; एकम् ; बहु ; वहनम् ; प्रतिबिम्बम् ; वहनम्-सदा-एकम् ; प्रतिबिम्बम्-तन्तुः)

------------------------------------------------------------------------
-- १ · अर्थः — the engine's denotation map, and it is the one that matters
------------------------------------------------------------------------

अर्थ : Type₀
अर्थ = Env → ℕ

⟦_⟧ : Term → अर्थ
⟦ t ⟧ ρ = eval ρ t

------------------------------------------------------------------------
-- २ · कस्मिन् पक्षे बद्धम् — the criterion, at this map
--
-- A rule carries its certificate, so it binds the MEANING side: what is
-- being asserted is "there is a meaning, and it is this one".  Free, by
-- Tantujala, with no hypothesis about terms, meanings, or the engine.
------------------------------------------------------------------------

नियम-बन्धः : (r : Rule) → isContr (वहनम् ⟦_⟧ (lhs r))
नियम-बन्धः r = वहनम्-सदा-एकम् ⟦_⟧ (lhs r)

-- The conjecture binds the other side: it asks which TERMS have a given
-- meaning.  That is the fiber, and it is any of the three.
अनुमान-बन्धः : (m : अर्थ) → प्रतिबिम्बम् ⟦_⟧ m ≡ fiber ⟦_⟧ m
अनुमान-बन्धः = प्रतिबिम्बम्-तन्तुः ⟦_⟧

------------------------------------------------------------------------
-- ३ · बहु — where the engine lives, exhibited
------------------------------------------------------------------------

वाम दक्षिण : Term
वाम    = op (var 0) (var 1)
दक्षिण  = op (var 1) (var 0)

समानार्थौ : ⟦ वाम ⟧ ≡ ⟦ दक्षिण ⟧
समानार्थौ = funExt (λ ρ → +-comm (ρ 0) (ρ 1))

private
  आदिः-शून्यः : Term → Bool
  आदिः-शून्यः (op (var zero) _) = true
  आदिः-शून्यः _                  = false

भिन्नौ : ¬ (वाम ≡ दक्षिण)
भिन्नौ p = true≢false (cong आदिः-शून्यः p)

-- two distinct terms, one meaning: the fiber over ⟦ वाम ⟧ has two points
यन्त्रस्य-वासः : बहु ⟦_⟧ ⟦ वाम ⟧
यन्त्रस्य-वासः =
    (वाम , refl)
  , (दक्षिण , sym समानार्थौ)
  , λ p → भिन्नौ (cong fst p)

------------------------------------------------------------------------
-- ४ · अलोपः, read as a fiber statement
--
-- The run does not leave the fiber it started in.  This is not a new
-- theorem: it is `Alopa.अलोपः` with `funExt` in front of it, which is the
-- honest amount of work a correct joint takes.
------------------------------------------------------------------------

क्रमः-तन्तौ-तिष्ठति :
    (n : ℕ) (rs : List Rule) (t : Term) → fiber ⟦_⟧ ⟦ t ⟧
क्रमः-तन्तौ-तिष्ठति n rs t =
  normalize n rs t , funExt (λ ρ → अलोपः n rs ρ t)

------------------------------------------------------------------------
-- ५ · रिक्तम् — a meaning this vocabulary cannot reach, and the proof
--     that no rewriting will ever reach it
------------------------------------------------------------------------

शून्य-परिस्थितिः : Env
शून्य-परिस्थितिः _ = 0

सर्वं-शून्ये-लीयते : (t : Term) → eval शून्य-परिस्थितिः t ≡ 0
सर्वं-शून्ये-लीयते (var _)  = refl
सर्वं-शून्ये-लीयते (op a b) =
  cong₂ _+_ (सर्वं-शून्ये-लीयते a) (सर्वं-शून्ये-लीयते b)

एकः : अर्थ
एकः _ = 1

-- the fiber over the constant 1 is EMPTY: no term of this vocabulary
-- denotes it, so no rule, no rewriting and no search inside the term
-- space can produce it.  Only a new symbol can.
अप्राप्यम् : रिक्तम् ⟦_⟧ एकः
अप्राप्यम् (t , p) = znots (sym (सर्वं-शून्ये-लीयते t) ∙ funExt⁻ p शून्य-परिस्थितिः)

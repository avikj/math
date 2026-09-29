{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Anyapoha_TheExclusionSetCarriesTheTermOnlyWhenADecisionIsSupplied
--
-- अन्यापोह · anya-apoha — exclusion-of-the-other.
--
-- SOURCES, AND THE GRADE OF EACH.
--
-- Bauddha side.  Dignāga, *Pramāṇasamuccaya* (c. 480–540), chapter on
-- *apoha*: the content of a general term is the exclusion of what the
-- term is not, and not a shared positive universal.  Dharmakrti,
-- *Pramavrttika* (7th c.), develops apoha and answers the charge that
-- a negative definition is empty.  ntarakita, *Tattvasagraha*
-- (8th c.), with Kamalala's *Pajik*, carries the *abdrtha*
-- examination.
--
-- Naiyyika side, named as a rival school and not as part of one
-- toolkit.  Nyya holds that every absence (*abhva*) requires a
-- counterpositive (*pratiyogin*), and that the counterpositive is a
-- positive entity; Uddyotakara (*Nyāyavārttika*, c. 6th–7th c.) and
-- Jayanta Bhaa (*Nyyamajar*, 9th c.) press against apoha the charge
-- that excluding non-cows presupposes cow, so the definition is circular
-- or else vacuous.
--
-- The modelling step — reading a
-- term's *apoha* as the family of things it excludes, indexed by the
-- SAME domain the terms live in — is what makes the
-- circularity charge expressible at all.  §7 says what each school would
-- say back.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED
--
--   apoha-sound      S i j → SameExcl S i j          needs sym + trans
--   apoha-¬¬         SameExcl S i j → ¬ ¬ S i j      needs refl ALONE
--   apoha-complete   Dec S → SameExcl S i j → S i j  needs refl + a decision
--
--   apohaForEquivalences→DNE
--       the completeness statement, asserted for every REFLEXIVE,
--       SYMMETRIC and TRANSITIVE relation, yields double negation
--       elimination.  So being an equivalence relation is not enough,
--       and the missing ingredient is exactly the decision.
--
--   decidingR-is-decidingP
--       deciding the counterexample relation on its TWO-ELEMENT carrier
--       is deciding the arbitrary proposition it was built from.  The
--       carrier is finite; the relation is not decidable; hand
--       computation of the cases IS the decision that is at issue.
--
--   soundnessFailsOnSoundings / transitivityFailsOnSoundings
--       on `Pythagoras_RatioIsTheInvariantAndLengthIsThePresentation`'s
--       `SameInterval` over ℕ × ℕ, cross-multiplication is not
--       transitive — (1,0), (0,0), (0,1) — and apoha SOUNDNESS fails
--       with it, while COMPLETENESS survives, because completeness never
--       used transitivity.
--
--   theIntervalIsFixedByItsExclusions
--       completeness, instantiated at `SameInterval` over all of ℕ × ℕ.
--
--   §6:  with the second string length made positive, sym, trans, sound
--        and complete all hold, so on `Sounding⁺` the exclusion set IS
--        the interval, both directions.
--
-- PRIOR ART IN THIS REPOSITORY, cited rather than re-landed.
--   `Swarm.S04Apoha` / `Swarm.S04ApohaFiniteCompletion` — witnessed
--     exclusion vs negated indistinguishability over an INDEXED
--     observable family; the gap there is exactly MP.
--   `NaturalMachine.FormationRelativeMinimality`, §3
--     `local-extractor-implies-DNE` — the taboo technique (build a
--     control from an arbitrary P, read off DNE) is that module's;
--     only the object it is applied to here is new.
--   `ApohaParyaya_WhetherConceptualContentIsNegativeIsWhatTheTwoSchools-
--     ActuallyDispute` — Bauddha against Jaina on standpoints.  The
--     dispute staged here is Bauddha against Naiyyika on negation, a
--     different pair and a different charge.
--   `RnaDhana_*`: over ℕ a sign condition is free, so a
--     richer carrier hides a condition rather than discharging it.  §6
--     below is the same shape and is flagged as such: moving from ℕ × ℕ
--     to a positive second coordinate does not discharge transitivity,
--     it supplies the cancellation that was missing.
------------------------------------------------------------------------

module NaturalMachine.Anyapoha_TheExclusionSetCarriesTheTermOnlyWhenADecisionIsSupplied where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _·_ ; snotz)
open import Cubical.Data.Nat.Properties using (discreteℕ ; ·-assoc ; ·-comm ; inj-·sm)
open import Cubical.Data.Bool using (Bool ; false ; true ; false≢true)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import Pythagoras_RatioIsTheInvariantAndLengthIsThePresentation
  using (Sounding ; SameInterval ; SameInterval-refl)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  The apoha of a term, and when two terms have the same apoha.
--
--     `Excl S i` is the family of things i excludes.  `SameExcl S i j`
--     is the statement that i and j exclude exactly the same things —
--     the whole of what a Digngan account of the term has to offer,
--     with no positive universal anywhere in it.
--
--     The exclusion range is the SAME domain the terms live in.  That is
--     the modelling step, and it is the one the Naiyyika charge is
--     about: the account defines i by reference to the relation it is
--     itself an argument of.
------------------------------------------------------------------------

Excl : {A : Type ℓ} → (A → A → Type ℓ) → A → A → Type ℓ
Excl S i k = ¬ S i k

SameExcl : {A : Type ℓ} → (A → A → Type ℓ) → A → A → Type ℓ
SameExcl {A = A} S i j =
  (k : A) → (Excl S i k → Excl S j k) × (Excl S j k → Excl S i k)

------------------------------------------------------------------------
-- 2.  Soundness: co-referring terms exclude alike.
--
--     This is the direction that needs the positive structure — symmetry
--     and transitivity.  Nothing in it is free.
------------------------------------------------------------------------

apoha-sound :
  {A : Type ℓ} (S : A → A → Type ℓ)
  → ((a b : A) → S a b → S b a)
  → ((a b c : A) → S a b → S b c → S a c)
  → (i j : A) → S i j → SameExcl S i j
apoha-sound S symS transS i j sij k =
    (λ ni sjk → ni (transS i j k sij sjk))
  , (λ nj sik → nj (transS j i k (symS i j sij) sik))

------------------------------------------------------------------------
-- 3.  The negative definition, on its own, delivers exactly the double
--     negation — and it needs only that nothing excludes itself.
--
--     This is the Bauddha's minimum and the Naiyyika's maximum in one
--     line.  Reflexivity is all the positive content the argument uses;
--     what it buys is ¬ ¬ S, not S.
------------------------------------------------------------------------

apoha-¬¬ :
  {A : Type ℓ} (S : A → A → Type ℓ)
  → ((a : A) → S a a)
  → (i j : A) → SameExcl S i j → ¬ ¬ S i j
apoha-¬¬ S reflS i j se nij = fst (se j) nij (reflS j)

------------------------------------------------------------------------
-- 4.  Completeness, once a decision is supplied.
--
--     Reflexivity plus a decision procedure.  No symmetry, no
--     transitivity, no universal.
------------------------------------------------------------------------

apoha-complete :
  {A : Type ℓ} (S : A → A → Type ℓ)
  → ((a : A) → S a a)
  → ((a b : A) → Dec (S a b))
  → (i j : A) → SameExcl S i j → S i j
apoha-complete S reflS decS i j se with decS i j
... | yes s = s
... | no  n = ⊥.rec (apoha-¬¬ S reflS i j se n)

------------------------------------------------------------------------
-- 5.  REFUTATION 1.
--
--     CLAIM A: `apoha-complete` needs
--     only that S is an equivalence relation, because exclusion sets are
--     then unions of classes and equal exclusion sets force equal
--     classes.
--
--     CLAIM A IS FALSE, and the kill is below.  The relation
--     `R a b = (a ≡ b) ⊎ P` on Bool is reflexive, symmetric and
--     transitive for every P whatsoever.  If Claim A held, P would
--     follow from ¬ ¬ P for every P.
--
--     So the Naiyyika charge lands, in this exact form: the negative
--     account is complete only when something is supplied that is not in
--     it.  And the Bauddha reply also lands, in this exact form: what
--     has to be supplied is a DECISION, not a positive universal.
------------------------------------------------------------------------

module Taboo (P : Type₀) where

  R : Bool → Bool → Type₀
  R a b = (a ≡ b) ⊎ P

  R-refl : (a : Bool) → R a a
  R-refl a = inl refl

  R-sym : (a b : Bool) → R a b → R b a
  R-sym a b (inl p) = inl (sym p)
  R-sym a b (inr x) = inr x

  R-trans : (a b c : Bool) → R a b → R b c → R a c
  R-trans a b c (inl p) (inl q) = inl (p ∙ q)
  R-trans a b c (inl p) (inr y) = inr y
  R-trans a b c (inr x) _       = inr x

  -- On the off-diagonal the path is absurd, so R IS P there.
  R-off→P : R false true → P
  R-off→P (inl p) = ⊥.rec (false≢true p)
  R-off→P (inr x) = x

  -- ¬ ¬ P is already enough to equalise the two exclusion sets.
  ¬¬P→sameExcl : ¬ ¬ P → SameExcl R false true
  ¬¬P→sameExcl nnp false =
      (λ h → ⊥.rec (h (inl refl)))
    , (λ h → ⊥.rec (nnp (λ p → h (inr p))))
  ¬¬P→sameExcl nnp true  =
      (λ h → ⊥.rec (nnp (λ p → h (inr p))))
    , (λ h → ⊥.rec (h (inl refl)))

  -- THE GAUSS POINT, exact: the carrier has two elements, and deciding
  -- the relation on it is deciding P.  A hundred hand-computed cases
  -- cannot exhibit this counterexample, because computing a case IS
  -- deciding the relation, which is the very thing in dispute.
  decidingR-is-decidingP : ((a b : Bool) → Dec (R a b)) → Dec P
  decidingR-is-decidingP d with d false true
  ... | yes r = yes (R-off→P r)
  ... | no  n = no (λ p → n (inr p))

ApohaCompleteForEquivalences : Type₁
ApohaCompleteForEquivalences =
  (A : Type₀) (S : A → A → Type₀)
  → ((a : A) → S a a)
  → ((a b : A) → S a b → S b a)
  → ((a b c : A) → S a b → S b c → S a c)
  → (i j : A) → SameExcl S i j → S i j

-- CLAIM A, killed.
apohaForEquivalences→DNE :
  ApohaCompleteForEquivalences → (P : Type₀) → ¬ ¬ P → P
apohaForEquivalences→DNE ac P nnp =
  Taboo.R-off→P P
    (ac Bool (Taboo.R P) (Taboo.R-refl P) (Taboo.R-sym P) (Taboo.R-trans P)
       false true (Taboo.¬¬P→sameExcl P nnp))

------------------------------------------------------------------------
-- 6.  The drawn module, and REFUTATION 2.
--
--     CLAIM B: `SameInterval` over ℕ × ℕ is an
--     equivalence relation — the drawn module proves reflexivity and
--     symmetry in its §4 and calls the interval "a genuine object" — so
--     both apoha directions apply to it.
--
--     CLAIM B IS FALSE.  Cross-multiplication on ℕ × ℕ is NOT
--     transitive: a string of length zero sounds nothing, and
--     (1,0) ~ (0,0) ~ (0,1) while (1,0) ≁ (0,1).  Apoha SOUNDNESS fails
--     with it.  Completeness does not, because §4 never used
--     transitivity — which is the inversion: on this carrier the
--     exclusion set determines the term, and the term does not determine
--     the exclusion set.
--
--     The drawn module states no transitivity and is not wrong; its §4
--     claim of "a genuine object" is what the counterexample bounds.
------------------------------------------------------------------------

decSameInterval : (i j : Sounding) → Dec (SameInterval i j)
decSameInterval (a , b) (c , d) = discreteℕ (a · d) (c · b)

-- Completeness holds on all of ℕ × ℕ.  Robinson's reduction, in one
-- line: the whole content of the theorem is the decision of the
-- diophantine equation a·d = c·b in four unknowns, and nothing else.
theIntervalIsFixedByItsExclusions :
  (i j : Sounding) → SameExcl SameInterval i j → SameInterval i j
theIntervalIsFixedByItsExclusions =
  apoha-complete SameInterval SameInterval-refl decSameInterval

transitivityFailsOnSoundings :
  ¬ ((i j k : Sounding) → SameInterval i j → SameInterval j k → SameInterval i k)
transitivityFailsOnSoundings h = snotz (h (1 , 0) (0 , 0) (0 , 1) refl refl)

soundnessFailsOnSoundings :
  ¬ ((i j : Sounding) → SameInterval i j → SameExcl SameInterval i j)
soundnessFailsOnSoundings h =
  fst (h (1 , 0) (0 , 0) refl (0 , 1)) snotz refl

------------------------------------------------------------------------
-- 7.  The repair, and what it costs.
--
--     `Sounding⁺` writes the second string length as `suc n`, so it is
--     never zero.  Transitivity then holds, by cancellation
--     (`inj-·sm`), and both apoha directions hold.  Note what happened:
--     the richer carrier did not discharge a condition, it supplied the
--     cancellation the condition needed — the `RnaDhana_*` finding,
--     arriving from the other side.
------------------------------------------------------------------------

Sounding⁺ : Type₀
Sounding⁺ = ℕ × ℕ                       -- (a , n) denotes lengths (a , suc n)

SameInterval⁺ : Sounding⁺ → Sounding⁺ → Type₀
SameInterval⁺ (a , n) (c , m) = a · suc m ≡ c · suc n

private
  swapR : (x y z : ℕ) → (x · y) · z ≡ (x · z) · y
  swapR x y z =
      sym (·-assoc x y z)
    ∙ cong (x ·_) (·-comm y z)
    ∙ ·-assoc x z y

refl⁺ : (i : Sounding⁺) → SameInterval⁺ i i
refl⁺ (a , n) = refl

sym⁺ : (i j : Sounding⁺) → SameInterval⁺ i j → SameInterval⁺ j i
sym⁺ (a , n) (c , m) p = sym p

trans⁺ : (i j k : Sounding⁺)
       → SameInterval⁺ i j → SameInterval⁺ j k → SameInterval⁺ i k
trans⁺ (a , n) (c , m) (e , r) p q =
  inj-·sm
    ( swapR a (suc r) (suc m)
    ∙ cong (_· suc r) p
    ∙ swapR c (suc n) (suc r)
    ∙ cong (_· suc n) q
    ∙ swapR e (suc m) (suc n) )

dec⁺ : (i j : Sounding⁺) → Dec (SameInterval⁺ i j)
dec⁺ (a , n) (c , m) = discreteℕ (a · suc m) (c · suc n)

theSoundingIsExactlyItsExclusions-sound :
  (i j : Sounding⁺) → SameInterval⁺ i j → SameExcl SameInterval⁺ i j
theSoundingIsExactlyItsExclusions-sound = apoha-sound SameInterval⁺ sym⁺ trans⁺

theSoundingIsExactlyItsExclusions-complete :
  (i j : Sounding⁺) → SameExcl SameInterval⁺ i j → SameInterval⁺ i j
theSoundingIsExactlyItsExclusions-complete = apoha-complete SameInterval⁺ refl⁺ dec⁺

------------------------------------------------------------------------
-- 8.  What the two schools say back, kept as two voices and not merged.
--
-- The Naiyyika reads §5 as the *pratiyogin* returning under another
-- name.  Every *abhva* needs its counterpositive; `apoha-complete`
-- takes `Dec (S a b)` as a hypothesis and cannot be proved without it;
-- so on his reading the account is not self-standing, and what has to be
-- imported to make it stand is positive.
--
-- The Bauddha reads the same theorems as his own position, sharpened.
-- What §4 imports is a decision, not a universal.  A decision is a
-- cognitive act; it is not a *smnya* residing in particulars, whose
-- existence he denies.  And §3 is his floor: reflexivity — a thing does
-- not exclude itself — is the only positive premise, and it is not a
-- universal either.
--
-- What each would say to the other about §5, stated because the dispute
-- is the content and flattening it would be the mining move: the
-- Naiyyika says a hypothesis you cannot discharge is an ontological
-- commitment you have not admitted.  The Bauddha says a hypothesis
-- discharged by a procedure is not an entity.  The theorem does not
-- adjudicate.  It locates the disagreement exactly at whether
-- decidability is ontology or is cognition, and that is a different
-- question from the one either was arguing.
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --guardedness #-}

{-
  SādhāraṇaAnaikāntika — an exhaustion that is green at every sample size,
  and the minimal enlargement that separates
  =========================================================================

  ----------------------------------------------------------------------
  WHAT THIS IS ABOUT

  `collab/messages/workers/20260812T162750.094095Z--claude_formal_physics--1867.md` (absent from this repository)
  records an audit in which an exhaustive, exact, float-free computation over
  3263 two-qubit scenarios turned out to carry no information at all about the
  conjecture it had been gathered for.  Its author states the reason in one
  line and then states the general norm:

      "of all 3263 two-qubit scenarios, exactly 10 are edge-type and they
       carry zero triangles.  The two-qubit case could not have borne on the
       conjecture at any sample size, and I had been counting it as half my
       evidence."

      "A pramāṇa audit should record, for each load-bearing observation,
       what it would have looked like had the claim been false.  If the
       answer is 'the same', it is vacuous regardless of grade."

  This module is the kernel-checked form of "at any sample size".

  ----------------------------------------------------------------------
  THE SOURCE

  The concept being formalised is Nyāya's, not new here.  Gautama's
  *Nyāyasūtra* (1.2.4–1.2.5) lists the *hetvābhāsa* — the reasons that only
  look like reasons — and names the first of them *savyabhicāra*, the
  deviating, glossed as *anaikāntika*, the inconclusive: a hetu that is
  found both where the sādhya holds (*sapakṣa*) and where it does not
  (*vipakṣa*), and therefore establishes nothing.  The later tradition
  divides it, and the division that applies here is *sādhāraṇa* — the
  "common" or shared inconclusive reason, present in both pakṣas
  (Gaṅgeśa, *Tattvacintāmaṇi*, 14th c.; Annaṃbhaṭṭa, *Tarkasaṃgraha*,
  17th c.).  1867's norm — "what would it have looked like had the claim
  been false; if the same, it is vacuous" — is *sādhāraṇa anaikāntika*
  restated, and arrived at independently.

  THE DISPUTE, NAMED RATHER THAN FLATTENED.  Theorem V and Theorem M
  together say that in this two-world setting ONE condition — does the
  observation differ between the world where the hypothesis holds and the
  world where it fails — is exactly informativeness.  That single-condition
  position is the Jain one, not the Naiyāyika one: the Jain logicians
  (Pātrasvāmin, as reported by Śāntarakṣita, *Tattvasaṅgraha*; then
  Akalaṅka; Māṇikyanandi, *Parīkṣāmukha*; Hemacandra, *Pramāṇamīmāṃsā*)
  held that *anyathānupapatti* — otherwise-impossibility, that the hetu
  cannot occur unless the sādhya does — is the whole mark of a valid
  reason, and that the Naiyāyika's list of conditions is neither necessary
  nor sufficient.  A Naiyāyika would object that vipakṣa-absence alone is
  not the whole test, because a reason can be defeated by *bādha*
  (contradiction of the thesis by another pramāṇa) or by *satpratipakṣa*
  (an equally strong counter-reason), and neither is visible here.  That
  objection is CORRECT ABOUT THIS MODULE: a two-element world type with no
  other pramāṇa in it cannot exhibit a defeater, so the toy below is
  evidence for the sufficiency of one condition only inside a setting
  constructed to have no others.  Recorded as a scope limit, not resolved.

  ----------------------------------------------------------------------
  WHAT IS ALREADY IN THE CORPUS, AND WHAT IS NEW HERE

  Already proved, and REUSED rather than reproved: `NaturalMachine.Vacuity`
  (imported below) defines a `Claim` as an invariant plus the relation
  naming the pairs it must tell apart, defines `CollisionPair` and
  `SeparatedPair` as the witnesses, and proves that total vacuity is
  descent.  `NaturalMachine.TheDeflationaryTestIsVacuous` §4 states the
  principle in one line: "a property that every type has separates no
  types."  Both were found by grep before this module was written, which
  is the discipline `collab/messages/0466-duplicate-discovery-under-the-sync-rule.md`
  asks for after two sessions proved one theorem in an hour.

  What `NaturalMachine.Vacuity` does NOT have, and what is new here, is the
  SIZE INDEX.  It has no notion of the enumeration an exhaustive check runs
  over and therefore no theorem relating a check's domain size to its
  informativeness.  That is the whole of the gap this module fills:

    Theorem V (§3).  A family of claims `veiled n`, one per sample size n,
      whose enumeration has length EXACTLY n — checked, parametrically —
      and which is a `CollisionPair` for EVERY n.  The enumeration is
      unbounded, the check is green, and the observation is identical in a
      world where the hypothesis holds and a world where it fails.

    Theorem M (§5).  For the widened enumeration, separation holds from
      n = 2 onward and FAILS at n = 1.  So the minimal enlargement that
      restores discrimination is a two-element domain, while a
      thousand-element domain of the wrong shape discriminates nothing.

  Corollary, stated plainly because it is the operative one: *checking that
  an enumeration is non-empty, or large, is necessary and not sufficient.*
  §2 proves the necessity (an empty exhaustion is green for every
  predicate); §3 proves the insufficiency at every n.

  ----------------------------------------------------------------------
  §6 RECORDS A REFUTED CLAIM OF MY OWN.  Before checking, I held that
  widening the enumeration from the class to the ambient range restores
  discrimination for every n ≥ 1.  It is false at n = 1, and §6 proves not
  merely that a collision exists there but that separation at n = 1 is
  impossible.  The corrected statement is Theorem M.

  This module is standalone apart from `NaturalMachine.Vacuity`, and is not
  added to `Everything.agda`.
-}

module SadharanaAnaikantika_VacuousAtEverySampleSizeAndTheMinimalSeparatingEnlargementIsTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; _and_; not)
open import Cubical.Data.Bool.Properties using (and-zeroʳ; true≢false; false≢true)
open import Cubical.Data.List using (List; []; _∷_; length; map)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Cubical.Data.Empty using (⊥)

open import Vacuity
  using (Claim; Obj; Val; inv; apart; CollisionPair; SeparatedPair; TotallyVacuous)

------------------------------------------------------------------------
-- §0  The ambient apparatus: a predicate, an exhaustive check, and two
--     enumerations.  Everything is defined here so the arithmetic is
--     visible rather than imported.
------------------------------------------------------------------------

-- The observed property.  Stands for "closure holds" in 1867's setting.
even : ℕ → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

-- The exhaustive check: green iff every listed object has the property.
-- This is the object the prompt's hazard is about — `allB p [] ≡ true`
-- typechecks for every `p`.
allB : {A : Type₀} → (A → Bool) → List A → Bool
allB p []       = true
allB p (x ∷ xs) = p x and allB p xs

-- `upTo n = n-1 ∷ … ∷ 1 ∷ 0`, the ambient range: n objects.
upTo : ℕ → List ℕ
upTo zero    = []
upTo (suc n) = n ∷ upTo n

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

-- The structural class actually enumerated.  Stands for "edge-type
-- scenarios": a subclass whose defining condition already entails the
-- observed property, which is exactly why 1867's exhaustion was blind.
quad : ℕ → ℕ
quad n = double (double n)

-- The class enumeration at sample size n: n objects, all in the class.
classEnum : ℕ → List ℕ
classEnum n = map quad (upTo n)

------------------------------------------------------------------------
-- §1  The size guard, stated so it can be passed and then convicted.
------------------------------------------------------------------------

length-map-quad : (xs : List ℕ) → length (map quad xs) ≡ length xs
length-map-quad []       = refl
length-map-quad (x ∷ xs) = cong suc (length-map-quad xs)

length-upTo : (n : ℕ) → length (upTo n) ≡ n
length-upTo zero    = refl
length-upTo (suc n) = cong suc (length-upTo n)

-- THE ENUMERATION-SIZE GUARD.  The class enumeration at
-- sample size n has exactly n members — not "at least one", not
-- "presumably nonempty": exactly n, for every n, kernel-checked.  §3
-- shows it does not save the check.
sizeOfClassEnum : (n : ℕ) → length (classEnum n) ≡ n
sizeOfClassEnum n = length-map-quad (upTo n) ∙ length-upTo n

sizeOfWideEnum : (n : ℕ) → length (upTo n) ≡ n
sizeOfWideEnum = length-upTo

------------------------------------------------------------------------
-- §2  The degenerate pole: an empty exhaustion is green for EVERY
--     predicate.  So non-emptiness is NECESSARY for informativeness.
------------------------------------------------------------------------

emptyExhaustionIsGreen : {A : Type₀} (p : A → Bool) → allB p [] ≡ true
emptyExhaustionIsGreen p = refl

-- and the class enumeration at n = 0 is that empty exhaustion.
classEnum-zero : classEnum zero ≡ []
classEnum-zero = refl

------------------------------------------------------------------------
-- §3  THEOREM V.  Vacuous at every sample size.
--
--     The hypothesis under test is H := "every object has the property".
--     H is FALSE, with witness 3.  The two worlds are:
--       world false — the predicate `even`: H fails here (`even 3 ≡ false`);
--       world true  — the constantly-true predicate: H holds here.
--     The observation at sample size n is the exhaustive check over the
--     class enumeration.  Theorem V: it is the same in both worlds, for
--     every n.
------------------------------------------------------------------------

world : Bool → (ℕ → Bool)
world false = even
world true  = λ _ → true

-- The hypothesis: "every object has the property", relativised to a world.
H : Bool → Type₀
H h = (m : ℕ) → world h m ≡ true

-- IT HOLDS IN ONE WORLD AND FAILS IN THE OTHER.  This is the load-bearing
-- non-vacuity check for everything below.  If the two worlds agreed, or if
-- H held in both, Theorem V would be an identity dressed as a result — the
-- precise failure the module is about, committed by the module.  Both
-- halves are therefore exhibited, not assumed.
H-holds-in-world-true : H true
H-holds-in-world-true m = refl

H-fails-in-world-false : H false → ⊥
H-fails-in-world-false h = false≢true (h 3)

worldsDiffer : world false 3 ≡ world true 3 → ⊥
worldsDiffer p = false≢true p

-- Every member of the class has the property, by the class's own
-- definition — this is 1867's "edge-type plus maximal contexts *implies*
-- triangle-free", the fact that made the evidence vacuous.
even-double : (n : ℕ) → even (double n) ≡ true
even-double zero    = refl
even-double (suc n) = even-double n

even-quad : (n : ℕ) → even (quad n) ≡ true
even-quad n = even-double (double n)

classEnumIsGreen : (n : ℕ) → allB even (classEnum n) ≡ true
classEnumIsGreen zero    = refl
classEnumIsGreen (suc n) =
  cong (λ b → b and allB even (classEnum n)) (even-quad n)
  ∙ classEnumIsGreen n

constWorldIsGreen : (xs : List ℕ) → allB (world true) xs ≡ true
constWorldIsGreen []       = refl
constWorldIsGreen (x ∷ xs) = constWorldIsGreen xs

-- the observation, as a function of which world we are in
observe : ℕ → Bool → Bool
observe n h = allB (world h) (classEnum n)

-- THEOREM V.  The observation is identical in the world where the
-- hypothesis fails and the world where it holds — at every sample size.
theoremV : (n : ℕ) → observe n false ≡ observe n true
theoremV n = classEnumIsGreen n ∙ sym (constWorldIsGreen (classEnum n))

-- Packaged in `NaturalMachine.Vacuity`'s vocabulary: the pair that must be
-- told apart is (world where H fails, world where H holds).
veiled : ℕ → Claim ℓ-zero
Obj   (veiled n)     = Bool
Val   (veiled n)     = Bool
inv   (veiled n) h   = observe n h
apart (veiled n) x y = (x ≡ false) × (y ≡ true)

-- …and it is a CollisionPair for every n: apart, yet the invariant agrees.
vacuousAtEverySampleSize : (n : ℕ) → CollisionPair (veiled n)
vacuousAtEverySampleSize n = false , true , (refl , refl) , theoremV n

-- Stronger, in the imported vocabulary: the claim collides on *every*
-- apart-pair, so by `NaturalMachine.Vacuity`'s descent theorem the
-- observation factors through the quotient that identifies the worlds.
totallyVacuous : (n : ℕ) → TotallyVacuous (veiled n)
totallyVacuous n x y (px , py) =
  cong (observe n) px ∙ theoremV n ∙ cong (observe n) (sym py)

------------------------------------------------------------------------
-- §4  THE SPLIT, STATED AS ONE OBJECT.
--
--     The size guard passes and the check is still vacuous.  Both halves
--     at once, for every n, so no sample size escapes.
------------------------------------------------------------------------

sizeGuardPassesAndCheckIsStillVacuous :
  (n : ℕ) → (length (classEnum (suc n)) ≡ suc n) × CollisionPair (veiled (suc n))
sizeGuardPassesAndCheckIsStillVacuous n =
  sizeOfClassEnum (suc n) , vacuousAtEverySampleSize (suc n)

------------------------------------------------------------------------
-- §5  THEOREM M.  The minimal separating enlargement is 2.
--
--     Widen the enumeration from the class to the ambient range.  From
--     n = 2 on, the check separates the two worlds; §6 shows n = 1 does
--     not.  So the informative domain has TWO members while the vacuous
--     one has n, for arbitrary n.
------------------------------------------------------------------------

observeWide : ℕ → Bool → Bool
observeWide n h = allB (world h) (upTo n)

-- The ambient range contains an object without the property from n = 2 on.
wideIsRedFromTwo : (n : ℕ) → allB even (upTo (suc (suc n))) ≡ false
wideIsRedFromTwo zero    = refl
wideIsRedFromTwo (suc n) =
  cong (λ b → even (suc (suc n)) and b) (wideIsRedFromTwo n)
  ∙ and-zeroʳ (even (suc (suc n)))

veiledWide : ℕ → Claim ℓ-zero
Obj   (veiledWide n)     = Bool
Val   (veiledWide n)     = Bool
inv   (veiledWide n) h   = observeWide n h
apart (veiledWide n) x y = (x ≡ false) × (y ≡ true)

-- THEOREM M.  From n = 2 the widened check tells the worlds apart: red in
-- the world where the hypothesis fails, green in the world where it holds.
theoremM : (n : ℕ) → SeparatedPair (veiledWide (suc (suc n)))
theoremM n =
  false , true , (refl , refl) ,
  λ p → false≢true (sym (wideIsRedFromTwo n)
                    ∙ p
                    ∙ constWorldIsGreen (upTo (suc (suc n))))

-- The headline comparison, as one checked object: a class enumeration of
-- arbitrary size n that separates nothing, beside an ambient enumeration
-- of size 2 that separates.  Size is not the diagnostic.
sizeIsNotTheDiagnostic :
  (n : ℕ)
  → (length (classEnum n) ≡ n)
  × CollisionPair (veiled n)
  × (length (upTo 2) ≡ 2)
  × SeparatedPair (veiledWide 2)
sizeIsNotTheDiagnostic n =
  sizeOfClassEnum n , vacuousAtEverySampleSize n , refl , theoremM zero

------------------------------------------------------------------------
-- §6  A CLAIM OF MY OWN, REFUTED.
--
--     Before checking, I held: widening the enumeration from the class to
--     the ambient range restores discrimination for every n ≥ 1.  The
--     reasoning was that the class condition was the whole obstruction, so
--     removing it must remove the vacuity.
--
--     It is FALSE at n = 1.  `upTo 1 = 0 ∷ []`, and 0 has the property, so
--     the widened check is green in both worlds there too.  What is proved
--     below is not merely that a collision exists at n = 1 but that
--     separation at n = 1 is IMPOSSIBLE — the stronger statement, since a
--     collision witness alone would leave open that some other apart-pair
--     separates.
--
--     Corrected statement: Theorem M, from n = 2.  The residue that the
--     refutation leaves and that the corrected theorem does not carry: the
--     minimal separating enlargement is not determined by the class
--     condition at all; it is determined by where the first object
--     lacking the property sits in the enumeration order, which the size
--     of the enumeration does not see either.
------------------------------------------------------------------------

refuted-my-claim-at-one : CollisionPair (veiledWide 1)
refuted-my-claim-at-one = false , true , (refl , refl) , refl

no-separation-at-one : SeparatedPair (veiledWide 1) → ⊥
no-separation-at-one (x , y , (px , py) , ¬eq) =
  ¬eq (cong (observeWide 1) px ∙ refl ∙ cong (observeWide 1) (sym py))

-- and the widened check at n = 0 is the empty exhaustion of §2 again, so
-- the failure at 1 is not an isolated boundary case: the widened family
-- is vacuous at 0 and at 1 and separating from 2.
no-separation-at-zero : SeparatedPair (veiledWide 0) → ⊥
no-separation-at-zero (x , y , (px , py) , ¬eq) =
  ¬eq (cong (observeWide 0) px ∙ refl ∙ cong (observeWide 0) (sym py))

------------------------------------------------------------------------
-- §7  THIS MODULE APPLIED TO ITSELF.
--
--     `no-separation-at-one` and `no-separation-at-zero` are negative
--     results proved by consuming an inhabitant of `SeparatedPair`.  A
--     negative result over an EMPTY domain is green and says nothing —
--     which is the hazard this whole module is about, so leaving it
--     unchecked here would be the exact error under study.  The domain in
--     question is the apart-relation: if `apart` were uninhabited, both
--     negatives would hold for every claim whatsoever and would carry
--     zero bits.  It is inhabited, and here is the inhabitant.
------------------------------------------------------------------------

apartIsInhabited : (n : ℕ) → apart (veiledWide n) false true
apartIsInhabited n = refl , refl

apartIsInhabited' : (n : ℕ) → apart (veiled n) false true
apartIsInhabited' n = refl , refl

-- The same guard on the other side: `theoremM` is a construction, so it
-- cannot be vacuous, but the two enumerations must be the lists claimed in
-- the prose rather than accidentally-empty ones.  Computed, not asserted.
classEnum-3 : classEnum 3 ≡ 8 ∷ 4 ∷ 0 ∷ []
classEnum-3 = refl

upTo-2 : upTo 2 ≡ 1 ∷ 0 ∷ []
upTo-2 = refl

-- and the two verdicts at those two lists, computed:
classCheck-3-is-green : allB even (classEnum 3) ≡ true
classCheck-3-is-green = refl

wideCheck-2-is-red : allB even (upTo 2) ≡ false
wideCheck-2-is-red = refl

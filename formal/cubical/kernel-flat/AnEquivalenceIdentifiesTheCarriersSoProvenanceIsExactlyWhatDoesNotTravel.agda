{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AnEquivalenceIdentifiesTheCarriersSoProvenanceIsExactlyWhatDoesNotTravel
--
-- TERM.  संक्रमण · saṃkramaṇa -- a crossing over, a passing from one place
-- to another.  It is used here because it is the
-- word `interactive/`'s running machine already uses for this exact act,
-- and the second word below, व्यय · vyaya (expenditure, what is spent), is
-- that machine's word for the other half.
--
------------------------------------------------------------------------
-- THREE FACTS THE MACHINE (`interactive/`) STATES, WHICH ARE THE FILE'S DESIGN:
--
--   1. A TRANSPORT THAT SUCCEEDS STILL HAS A COST, AND THE MACHINE STATES
--      IT.  `saptabhangi.samkramana` returns a bijection with both round
--      trips run on all 8 positions of each side -- 16 checks, "no case
--      omitted, no case sampled" -- and calls it "an identification, in
--      Voevodsky's sense: a thing held, not a fact cited".  And in the same
--      answer, under `vyaya`, what did NOT travel: the two modules' glosses,
--      which differ, "the positions correspond; the accounts of WHY the
--      eighth exists do not, AND THE EQUIVALENCE DOES NOT CARRY THAT
--      DIFFERENCE."  A successful transport is not a free one.
--
--   2. IDENTIFICATION IS GRADED, IN THREE, AND THE COARSEST IS NEARLY
--      EMPTY.  `interactive/StandpointStore.hs` lines 36-42:
--          सत्य  satya  -- inhabited or not.  Coarsest.
--          अर्थ  artha  -- the set of witness labels.
--          मूल   mūla   -- the same labels FROM THE SAME SOURCES.
--      and the store, asked to relate two representations, answered
--      `satyaikya` and said why it reports that as a COUNT and not as an
--      index: "truth-value agreement is nearly universal and therefore
--      nearly contentless."
--
--   3. THERE IS NO THIRD ROAD.  Every answer that machine gives is a
--      sakramaa or a doa-lekha naming its losses one by one, and asked
--      whether the two representations may be identified it returned a
--      doa-lekha, twice, differently -- `syad-avaktavyam` under saha and
--      `syan-nasti` under krama.  Not a boolean either time.
--
-- SO THE CONTENT OF THIS FILE IS THE MIDDLE FACT, AND IT IS EXACT IN TYPE
-- THEORY.  The three grades are three strengths of identification:
--
--     Satya A B   =  ∥ A ∥₁ ≃ ∥ B ∥₁        both inhabited, or neither
--     Artha A B   =  A ≃ B                   the carriers identified
--     Mula  pA pB e = (a : A) → pB (e a) ≡ pA a    and the SOURCES agree
--
-- `ua` and `transport` deliver ARTHA.  §3 proves satya is strictly weaker
-- than artha, and §4 proves ARTHA IS STRICTLY WEAKER THAN MLA -- one
-- equivalence, two provenance maps that disagree.  That gap is `vyaya`, and
-- it is the machine's finding turned into a term:
--
--     AN EQUIVALENCE IDENTIFIES THE CARRIERS AND SETTLES NOTHING ABOUT
--     WHERE EITHER SIDE GOT ITS COPY.
--
-- which is why a peer-to-peer transport must CARRY its provenance
-- separately or lose it silently, and why the retained object is the triple
-- (a , e , b) and not b.
--
--   §1  the three grades, and the two implications that do hold, both free.
--   §2  transport COMPUTES -- `uaβ` -- and the round trip is exhibited in
--       both directions, so the identification is held and not cited.
--   §3  SATYA ⊊ ARTHA.  Unit and Bool: both inhabited, not equivalent.
--   §4  ARTHA ⊊ MLA.  The theorem.  One equivalence, two sources.
--   §5  THE RETAINED TRIPLE, and that its middle component is not
--       recoverable from its ends -- so a peer that stores only the value
--       has not stored the transport.
--   §6  NO THIRD ROAD.  `Uttara` has two constructors and the interaction
--       is total; there is no `Maybe`, no error, and no silent case.
--   §7  the fixed-representation encounter is the identity instance, so
--       `TheEncounterOfTwoPeers…` is this file at `e = idEquiv`.
------------------------------------------------------------------------

module AnEquivalenceIdentifiesTheCarriersSoProvenanceIsExactlyWhatDoesNotTravel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_ ; equivFun ; invEq ; idEquiv ; invEquiv ; secEq ; retEq
        ; isEquiv ; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; ~uaβ)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; rec)
open import Cubical.Data.Unit using (Unit ; tt ; isContrUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; notEquiv ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)

open import Kernel.RewriteCertificate using (Tm)
open import HidingAndHardnessAreOneFibreSoTwoWitnessesForbidExtraction
  using (extraction-from-an-existence-forces-uniqueness)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- §1.  THE THREE GRADES.
--
-- Read as the machine reads them: what two peers may be said to agree
-- about.  `Satya` is the weakest thing worth saying and is nearly always
-- true; `Artha` is what `ua` transports along; `Mula` additionally pins
-- that the two sides got their copies from corresponding places.
------------------------------------------------------------------------

Satya : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Satya A B = ∥ A ∥₁ ≃ ∥ B ∥₁

Artha : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Artha A B = A ≃ B

-- The provenance square.  `pA`, `pB` say where each side's element came
-- from; `Mula` says the identification respects that.
Mula : {A : Type ℓ} {B : Type ℓ'} {G : Type ℓ''}
  → (A → G) → (B → G) → Artha A B → Type (ℓ-max ℓ ℓ'')
Mula {A = A} pA pB e = (a : A) → pB (equivFun e a) ≡ pA a

-- MŪLA ⇒ ARTHA is by construction: `Mula` is a field OVER an `Artha`, and
-- that is not an accident of the encoding -- there is nothing for sources
-- to correspond along until the carriers are identified.
mula-carries-its-artha :
  {A : Type ℓ} {B : Type ℓ'} {G : Type ℓ''}
  (pA : A → G) (pB : B → G) (e : Artha A B) → Mula pA pB e → Artha A B
mula-carries-its-artha pA pB e _ = e

-- ARTHA ⇒ SATYA, and it costs nothing: an equivalence descends to the
-- truncations because both sides are propositions.
artha-gives-satya : {A : Type ℓ} {B : Type ℓ'} → Artha A B → Satya A B
artha-gives-satya e =
  propBiimpl→Equiv squash₁ squash₁
    (rec squash₁ (λ a → ∣ equivFun e a ∣₁))
    (rec squash₁ (λ b → ∣ invEq e b ∣₁))

------------------------------------------------------------------------
-- §2.  TRANSPORT COMPUTES, AND THE ROUND TRIP IS EXHIBITED.
--
-- The machine's phrase for this is the right one: an identification is a
-- THING HELD, not a fact cited.  `uaβ` is univalence's β-rule computing --
-- the path manufactured from the equivalence transports BY that
-- equivalence's function, and the equation is proved, not postulated.
------------------------------------------------------------------------

cross : {A B : Type ℓ} → Artha A B → A → B
cross e a = transport (ua e) a

the-crossing-computes :
  {A B : Type ℓ} (e : Artha A B) (a : A) → cross e a ≡ equivFun e a
the-crossing-computes e a = uaβ e a

back : {A B : Type ℓ} → Artha A B → B → A
back e b = transport (sym (ua e)) b

the-return-computes :
  {A B : Type ℓ} (e : Artha A B) (b : B) → back e b ≡ invEq e b
the-return-computes e b = ~uaβ e b

-- Both round trips, which is what makes it an identification rather than a
-- one-way conversion trusted at the boundary.
there-and-back : {A B : Type ℓ} (e : Artha A B) (a : A) → back e (cross e a) ≡ a
there-and-back e a =
  the-return-computes e (cross e a)
  ∙ cong (invEq e) (the-crossing-computes e a)
  ∙ retEq e a

back-and-there : {A B : Type ℓ} (e : Artha A B) (b : B) → cross e (back e b) ≡ b
back-and-there e b =
  the-crossing-computes e (back e b)
  ∙ cong (equivFun e) (the-return-computes e b)
  ∙ secEq e b

------------------------------------------------------------------------
-- §3.  SATYA IS STRICTLY WEAKER THAN ARTHA.
--
-- Both inhabited is not identified.  This is why the store reports
-- truth-value agreement as a COUNT rather than as its index: it is nearly
-- universal, hence nearly contentless.
------------------------------------------------------------------------

satya-unit-bool : Satya Unit Bool
satya-unit-bool =
  propBiimpl→Equiv squash₁ squash₁ (λ _ → ∣ true ∣₁) (λ _ → ∣ tt ∣₁)

artha-unit-bool-fails : Artha Unit Bool → ⊥
artha-unit-bool-fails e = true≢false (sym (snd c true) ∙ snd c false)
  where
  c : isContr Bool
  c = isOfHLevelRespectEquiv 0 e isContrUnit

satya-does-not-give-artha :
  ({A : Type₀} {B : Type₀} → Satya A B → Artha A B) → ⊥
satya-does-not-give-artha f = artha-unit-bool-fails (f satya-unit-bool)

------------------------------------------------------------------------
-- §4.  ARTHA IS STRICTLY WEAKER THAN MLA.  THE THEOREM.
--
-- One equivalence -- the identity, the least contentious one there is --
-- and two peers recording different sources for the same element.  The
-- equivalence is silent about the disagreement, and no equivalence could
-- speak to it, because the sources are not data on the carrier.
--
-- This is the machine's `vyaya` in a type: the answer transported, and the
-- glosses did not, and the equivalence does not carry that difference.
------------------------------------------------------------------------

-- Peer A says every element came from source `true`; peer B says `false`.
sourceA sourceB : Bool → Bool
sourceA _ = true
sourceB _ = false

the-carriers-are-identified : Artha Bool Bool
the-carriers-are-identified = idEquiv Bool

-- and the sources are not.
the-sources-disagree : Mula sourceA sourceB the-carriers-are-identified → ⊥
the-sources-disagree m = true≢false (sym (m true))

-- THE STATEMENT.  There is no function taking an identification of carriers
-- to an agreement of sources.  Not "none is known" -- the type is empty,
-- because §4's witness inhabits its domain and refutes its codomain.
artha-does-not-give-mula :
  ({A B : Type₀} {G : Type₀} (pA : A → G) (pB : B → G) (e : Artha A B)
     → Mula pA pB e)
  → ⊥
artha-does-not-give-mula f =
  the-sources-disagree (f sourceA sourceB the-carriers-are-identified)

-- Read at the peers, which is the reading this file exists for: two nodes
-- may hold provably the same object, cross freely in both directions, and
-- still disagree about where it came from -- with the disagreement invisible
-- to every transport between them.  PROVENANCE IS NOT CARRIED.  It is
-- carried ALONGSIDE, or it is gone.
provenance-must-be-carried-alongside :
  Σ[ e ∈ Artha Bool Bool ] (Mula sourceA sourceB e → ⊥)
provenance-must-be-carried-alongside =
  the-carriers-are-identified , the-sources-disagree

------------------------------------------------------------------------
-- §5.  THE RETAINED TRIPLE.
--
-- The important object is not `b` but `(a , e , b)`.
-- Here is why in one line: the ends do not determine the middle.  A peer
-- that stored the value and dropped the equivalence has not stored a
-- transport, and cannot reconstruct one: `Bool` has two self-equivalences,
-- so even KNOWING that a route exists does not hand you the route.
------------------------------------------------------------------------

record Samkramana (A B : Type ℓ) : Type ℓ where
  constructor _⟨_⟩_
  field
    from : A
    via  : Artha A B
    to   : B

  -- and the crossing is the one the equivalence says it is.
  faithful : Type ℓ
  faithful = cross via from ≡ to

open Samkramana public

carry : {A B : Type ℓ} (e : Artha A B) (a : A) → Samkramana A B
carry e a = a ⟨ e ⟩ cross e a

carrying-is-faithful :
  {A B : Type ℓ} (e : Artha A B) (a : A) → faithful (carry e a)
carrying-is-faithful e a = refl

-- THE ENDS DO NOT DETERMINE THE MIDDLE, and the sharp form is that even
-- KNOWING a route exists does not give you one.  `HidingAndHardness…` §6:
-- extraction from an existence forces the witness to be unique.  Routes
-- between two representations are not unique -- `Bool` has two -- so the
-- extraction fails, and a peer holding `∥ Artha A B ∥₁` holds strictly less
-- than a peer holding the equivalence.
routes-are-not-unique : (idEquiv Bool ≡ notEquiv) → ⊥
routes-are-not-unique p = true≢false (cong (λ q → equivFun q true) p)

the-existence-of-a-route-does-not-give-the-route :
  isEquiv (∣_∣₁ {A = Artha Bool Bool}) → ⊥
the-existence-of-a-route-does-not-give-the-route e =
  routes-are-not-unique
    (extraction-from-an-existence-forces-uniqueness e (idEquiv Bool) notEquiv)

-- So storing the value and dropping the equivalence is not a compression of
-- the transport.  It is the loss of it, and §4 already said the provenance
-- went with it.
the-triple-is-the-object :
  Σ[ e ∈ Artha Bool Bool ] Σ[ e' ∈ Artha Bool Bool ] ((e ≡ e') → ⊥)
the-triple-is-the-object = idEquiv Bool , notEquiv , routes-are-not-unique

------------------------------------------------------------------------
-- §6.  NO THIRD ROAD.
--
-- The machine's contract, in a type: an answer is a transport or a written
-- defect, and the defect names what did not cross.  Two constructors, no
-- `Maybe`, no error value, no silent case -- so a caller cannot receive a
-- refusal that failed to say what it cost.
------------------------------------------------------------------------

record Dosalekha (A B : Type ℓ) : Type ℓ where
  constructor dosa
  field
    nasta : A                           -- what did NOT cross, named
    hetu  : Artha A B → ⊥               -- and why: no identification exists

data Uttara (A B : Type ℓ) : Type ℓ where
  samkramana : Samkramana A B → Uttara A B
  dosalekha  : Dosalekha A B  → Uttara A B

-- Totality with two roads and no third: given an element and a decision
-- about whether an identification exists, an answer always exists, and it
-- is one of exactly the two.
answer :
  {A B : Type ℓ} (a : A)
  → (Artha A B) ⊎ ((Artha A B) → ⊥) → Uttara A B
answer a (inl e) = samkramana (carry e a)
answer a (inr r) = dosalekha (dosa a r)

-- and every answer is one or the other, by the type having two
-- constructors: there is nowhere for a third to be.
no-third-road :
  {A B : Type ℓ} (u : Uttara A B)
  → (Σ[ s ∈ Samkramana A B ] (u ≡ samkramana s))
  ⊎ (Σ[ d ∈ Dosalekha A B ]  (u ≡ dosalekha d))
no-third-road (samkramana s) = inl (s , refl)
no-third-road (dosalekha d)  = inr (d , refl)

------------------------------------------------------------------------
-- §7.  THE FIXED-REPRESENTATION CASE IS THE IDENTITY INSTANCE.
--
-- `TheEncounterOfTwoPeers…` has both peers holding `Tm`.  That is this file
-- at `e = idEquiv`, which is why nothing there mentions transport: the
-- transport was there, and it was trivial, and a trivial transport is
-- exactly the one whose `vyaya` is invisible.
------------------------------------------------------------------------

the-shared-representation-is-the-identity : Artha Tm Tm
the-shared-representation-is-the-identity = idEquiv Tm

the-identity-crossing-moves-nothing :
  (t : Tm) → cross the-shared-representation-is-the-identity t ≡ t
the-identity-crossing-moves-nothing t =
  the-crossing-computes the-shared-representation-is-the-identity t

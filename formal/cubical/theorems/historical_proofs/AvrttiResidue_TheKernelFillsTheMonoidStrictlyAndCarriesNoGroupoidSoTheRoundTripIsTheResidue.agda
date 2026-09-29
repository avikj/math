{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- आवृत्तिशेषः — the remainder of the turning-back.
--
-- TERM.  आवृत्ति (āvṛtti), repetition / a turning back over the same
-- ground, and शेष (śeṣa), what is left over.  Both are used in their
-- ordinary technical senses.  शेष in the sense this file uses — the remainder is kept and is
-- the material of the next step — is Āryabhaṭa, Āryabhaṭīya, गणितपाद
-- 32ℓ33 (499 CE), the kuaka; the mathematics below is not his.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT THIS SETTLES.
--
-- Three files in this repository state one fact about the kernel and
-- none of them cites another:
--
--   Yantra_…            the computer is a GROUPOID: `A ≃ A` fills the
--                       monoid interface AND the inverse field, and every
--                       law holds by `equivEq refl` — strictly.
--   Avirodha_…          the kernel is "strictly a category, weakly a
--                       groupoid", and "the gap between the two is the
--                       śeṣa" — but the weakness is exhibited only by
--                       `the-round-trip-is-not-nothing`, an observation
--                       about `len`, not a statement in the path type.
--   Asesa_…             `Meaning a b` is a PROPOSITION, so the fibre of
--                       soundness over any meaning is the WHOLE
--                       derivation type, and soundness is refutably not
--                       an equivalence at the kernel's own seed.
--
-- A remark about `len` is weaker than it looks: `len` is a function of
-- the derivation, so "the round trip has positive length" leaves open
-- that SOME OTHER inverse — not `rev` — might close it on the nose.
-- §3 removes that.  It quantifies over every function whatsoever:
--
--     the-kernel-carries-no-inverse :
--       (inv : Derivation A A → Derivation A A)
--       → ((d : Derivation A A) → d ⊕ inv d ≡ done A) → ⊥
--
-- so the failure is a property OF THE KERNEL'S COMPOSITION, not a defect
-- of the particular `rev` that Avirodha_ happens to define.
--
-- §4 puts the two sides on ONE interface, `MonoidMachine` imported from
-- `Yantra_…` rather than restated, so the comparison is between the same
-- record and not between two spellings of it:
--
--     equivalences-carry-an-inverse : (A : Type ℓ) → GroupoidOver (एकत्वम् A)
--     the-kernel-carries-none       : ¬ GroupoidOver आवृत्तिः
--
-- SAME INTERFACE.  One side fills it; the other provably cannot.  That
-- difference is the whole of what the kernel keeps and `_≃_` throws away,
-- and by `Asesa_…` it is invisible to meaning: the two derivations that
-- separate the fibre have EQUAL meanings, because the meaning type is a
-- proposition and has no two positions in it.
--
------------------------------------------------------------------------

module AvrttiResidue_TheKernelFillsTheMonoidStrictlyAndCarriesNoGroupoidSoTheRoundTripIsTheResidue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using ( _≃_ ; idEquiv ; compEquiv ; invEquiv
        ; compEquivIdEquiv ; compEquivEquivId ; compEquiv-assoc
        ; invEquiv-is-rinv ; invEquiv-is-linv )
open import Cubical.Data.Nat using (ℕ ; snotz ; _+_)
import Cubical.Data.Nat as N
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
  using (Tm ; var ; zero ; add ; Step ; add-zero ; reverse
        ; Derivation ; done ; then-step)
open import Kernel.Residue_TheDerivationCarriesNoMeaningAtAllSoAllOfItIsRemainderAndNoSemanticCriterionSelectsTheShortOne
  using (len)
open import Kernel.Interaction_TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation
  using (_⊕_)
open import Kernel.Avirodha_TheKernelIsAReversibleGroupoidWhoseJoinIsConflictFreeSoConsensusOnMeaningIsVacuous
  using (⊕-assoc ; ⊕-unitˡ ; ⊕-unitʳ)
open import Machine_TheComputerIsTheGroupoidOfProofsOfTransportNotTheMonoidOfIrreversibleSteps
  using (MonoidMachine)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  THE INVERSE, AS A STRUCTURE OVER A GIVEN MONOID.
--
-- Not a fresh record.  `Yantra_…`'s `GroupoidMachine` bundles its monoid
-- as a field, which makes "does THIS monoid admit an inverse?" awkward to
-- ask.  Asking it is the whole business here, so the inverse is indexed
-- by the monoid it would extend.
------------------------------------------------------------------------

GroupoidOver : {Op : Type ℓ} → MonoidMachine Op → Type ℓ
GroupoidOver {Op = Op} M =
  Σ[ inv ∈ (Op → Op) ]
    ( ((x : Op) → MonoidMachine.seq M x (inv x) ≡ MonoidMachine.noop M)
    × ((x : Op) → MonoidMachine.seq M (inv x) x ≡ MonoidMachine.noop M) )

------------------------------------------------------------------------
-- §2  THE KERNEL'S DERIVATIONS FILL THE MONOID INTERFACE — STRICTLY.
--
-- Every field is `Avirodha_…`'s term, unchanged.  Nothing is reproved;
-- the point of the record is that the SAME interface is offered to both
-- sides in §4, so what §3 excludes is excluded on it.
------------------------------------------------------------------------

A : Tm
A = add var zero

आवृत्तिः : MonoidMachine (Derivation A A)
आवृत्तिः = record
  { seq   = _⊕_
  ; noop  = done A
  ; unitL = ⊕-unitˡ
  ; unitR = ⊕-unitʳ
  ; assoc = ⊕-assoc }

------------------------------------------------------------------------
-- §3  AND CARRY NO INVERSE — FOR EVERY CANDIDATE, NOT ONLY FOR `rev`.
--
-- The measure first: concatenation adds lengths.  This is the lemma the
-- `len` remark in `Avirodha_…` needed and did not have; with it, the
-- refutation quantifies over all of `Derivation A A → Derivation A A`.
------------------------------------------------------------------------

len-⊕ :
  {a b c : Tm} (d : Derivation a b) (e : Derivation b c)
  → len (d ⊕ e) ≡ len d + len e
len-⊕ (done _)        e = refl
len-⊕ (then-step p d) e = cong N.suc (len-⊕ d e)

-- One step of the kernel, and its reversal.  `add-zero var : Step (add
-- var zero) var`, so this goes out and comes back: a derivation from `A`
-- to `A` that is not `done A`.
सोपानम् : Step A var
सोपानम् = add-zero var

आवृत्तम् : Derivation A A
आवृत्तम् = then-step सोपानम् (then-step (reverse सोपानम्) (done A))

-- and its length is not zero — the round trip is not nothing.
आवृत्तस्य-मात्रा : len आवृत्तम् ≡ N.suc (N.suc N.zero)
आवृत्तस्य-मात्रा = refl

-- THE EXCLUSION.  No function inverts the kernel's composition, because
-- composition can only ADD length and `done` has none.  The hypothesis is
-- used at exactly one point, and one point is enough.
the-kernel-carries-no-inverse :
  (inv : Derivation A A → Derivation A A)
  → ((d : Derivation A A) → d ⊕ inv d ≡ done A) → ⊥
the-kernel-carries-no-inverse inv law =
  snotz (sym (len-⊕ आवृत्तम् (inv आवृत्तम्)) ∙ cong len (law आवृत्तम्))

------------------------------------------------------------------------
-- §4  THE TWO SIDES, ON ONE INTERFACE.
--
-- `A ≃ A` fills the inverse field; the kernel's derivations cannot.  The
-- monoid structure is the same record in both cases, so this is a
-- comparison and not an analogy.
------------------------------------------------------------------------

एकत्वम् : (X : Type ℓ) → MonoidMachine (X ≃ X)
एकत्वम् X = record
  { seq   = compEquiv
  ; noop  = idEquiv X
  ; unitL = compEquivIdEquiv
  ; unitR = compEquivEquivId
  ; assoc = λ p q r → sym (compEquiv-assoc p q r) }

equivalences-carry-an-inverse : (X : Type ℓ) → GroupoidOver (एकत्वम् X)
equivalences-carry-an-inverse X =
  invEquiv , invEquiv-is-rinv , invEquiv-is-linv

the-kernel-carries-none : ¬ GroupoidOver आवृत्तिः
the-kernel-carries-none (inv , rinv , _) =
  the-kernel-carries-no-inverse inv rinv

------------------------------------------------------------------------
-- §5  WHAT THE DIFFERENCE IS.
--
-- `_≃_` composes and inverts and keeps nothing: `invEquiv-is-rinv` says
-- the round trip IS the no-op, on the nose, so an equivalence groupoid
-- cannot record that a route was taken.  `Derivation` composes and cannot
-- invert: every route it takes is still in the term, and §3 says no
-- function can remove it.
--
-- That surplus is exactly the object `Asesa_…` shows the semantics cannot
-- see.  `Meaning a b` is a proposition; the fibre of soundness over any
-- meaning is the whole derivation type; the two routes that separate it
-- have equal meanings by `isSetℕ`.  So the kernel carries a distinction
-- that is real in the term, invisible in the value, and — by §3 —
-- irremovable by any post-processing of the term.
--
-- The interface consequence, stated because it is mechanical and not a
-- reading: a wire that returns the MEANING returns the part that is
-- provably a proposition, and a wire that does not return the DERIVATION
-- drops the part that is provably everything.
------------------------------------------------------------------------

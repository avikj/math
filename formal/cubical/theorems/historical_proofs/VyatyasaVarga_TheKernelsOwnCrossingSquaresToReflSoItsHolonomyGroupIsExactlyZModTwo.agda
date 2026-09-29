{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- व्यत्यास-वर्ग — the crossing's square.
--
-- TERMS.  व्यत्यास · vyatyāsa — interchange, transposition; carried from
-- `Vyatyasa_…`, which states its own limits.   · varga — square.
-- वर्ग is a technical term throughout Indian mathematics; Brahmagupta's
-- *Brāhmasphuṭasiddhānta* (628) uses वर्गप्रकृति (varga-prakṛti,
-- "square-nature") for x² − D·y² = 1.  IT IS USED HERE ONLY IN ITS
-- ORDINARY ARITHMETICAL SENSE — the square of one element under its own
-- composition — and NOT for वर्गप्रकृति.  No text is claimed for the
-- application below and no author is credited with anything proved here.
--
------------------------------------------------------------------------
-- WHY THIS IS ONE FILE AND NOT A RESTATEMENT.
--
-- Three files in this corpus stand around this question and none of them
-- answers it.
--
--   `Ankapasa_…` §4 gives the kernel a univalent semantics and
--     proves that its ONE commutation at `add var var` —
--     `comm-loop : Derivation⁺ (add var var) (add var var)`, a genuine
--     kernel derivation — is a NONTRIVIAL loop in the universe, invisible
--     to `eval` because `isSetℕ`.  It never asks the loop's ORDER.
--
--   `Vyatyasa_…` §4 proves σ² = id and `ua`-triviality of the doubled
--     crossing — but for TWO CROSSINGS IT BUILDS BY HAND in the semantics,
--     on `Tri A = A ⊎ (A ⊎ A)`, and it says so: "the two crossings below
--     are built directly in the SEMANTICS … the syntax that would express
--     them is a congruence rule and an associator the kernel DOES NOT
--     HAVE."  So its negative is about ITS OWN σ₁, σ₂, not about the
--     kernel's derivation.
--
--   `Paryaya_…` §3 proves EXACTLY the ℤ/2 statement — for `swap01` on ℕ,
--     "the corpus's own checked loop at its hub node".  `swap01-Equiv` is
--     an equivalence someone wrote down; it is not the image of a
--     derivation.  The proof shape below (`equivEq ∘ funExt`, then
--     `sym uaCompEquiv ∙ cong ua ∙ uaIdEquiv`) is Paryaya's and is reused
--     here rather than reinvented; the credit for the shape is its.
--
-- WHAT IS NEW HERE IS THE SUBJECT, and it is the one the physics reading
-- turns on: the order of the crossing THE KERNEL ITSELF INSTALLS.  §2 and
-- §3 compute it, and §4 states it:
--
--   THE KERNEL'S OWN CROSSING HAS ORDER EXACTLY TWO IN Ω(Type, ⟦add var
--   var⟧ σ₁).  Not one — that is Ankapasa's negative, imported.  And
--   dividing two — that is §3.
--
-- CONSEQUENCE, and it is a denial.  In the braid group Bₙ the generators
-- have INFINITE order; σ² = 1 is precisely the relation collapsing Bₙ onto
-- Sₙ, and non-abelian anyonic statistics live in the monodromy σ².  §5
-- discharges the hypothesis of infinite order against §3 directly: the
-- kernel's crossing CANNOT be a braid generator.  Vyatyasa named the
-- obstruction — `⊎` is symmetric monoidal and its symmetry is an
-- involution by construction, so any interpretation of `add` by `⊎`
-- inherits σ² = 1 — and that diagnosis now attaches to the kernel's actual
-- derivation and not only to hand-built crossings.
--
-- No postulates, no holes, --safe.
------------------------------------------------------------------------

module VyatyasaVarga_TheKernelsOwnCrossingSquaresToReflSoItsHolonomyGroupIsExactlyZModTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; idEquiv ; compEquiv ; equivEq)
open import Cubical.Foundations.Univalence using (ua ; uaIdEquiv ; uaCompEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

open import Kernel.RewriteCertificate using (Tm ; var ; add)
open import TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry
  using ( TEnv ; ⟦_⟧ ; Step⁺ ; add-comm ; Derivation⁺ ; done⁺ ; then⁺
        ; derivation⁺-equiv ; σ₁ ; comm-loop ; comm-path
        ; comm-loop-is-a-nontrivial-loop-in-the-universe )

------------------------------------------------------------------------
-- §1  The kernel derivation that crosses TWICE.  It is `comm-loop` with
--     one more `add-comm` in front: no new constructor, no new semantics,
--     nothing built by hand.  This is the object Vyatyasa could not name.
------------------------------------------------------------------------

Ubhaya : Type₀
Ubhaya = ⟦ add var var ⟧ σ₁          -- = Unit ⊎ Unit

व्यत्यास-द्वयम् : Derivation⁺ (add var var) (add var var)
व्यत्यास-द्वयम् = then⁺ (add-comm var var) comm-loop

व्यत्यासः : Ubhaya ≃ Ubhaya
व्यत्यासः = derivation⁺-equiv comm-loop σ₁

------------------------------------------------------------------------
-- §2  Doubling is the identity EQUIVALENCE.  Two cases, each `refl`: the
--     swap is defined by pattern matching, so composing it with itself
--     computes, and `equivEq` lifts the function-level equality to the
--     equivalence because `isEquiv` is a proposition.
------------------------------------------------------------------------

द्वित्वम् : derivation⁺-equiv व्यत्यास-द्वयम् σ₁ ≡ idEquiv Ubhaya
द्वित्वम् = equivEq (funExt lemma)
  where
  lemma : (x : Ubhaya) → equivFun (derivation⁺-equiv व्यत्यास-द्वयम् σ₁) x ≡ x
  lemma (inl tt) = refl
  lemma (inr tt) = refl

-- the same fact stated on the composite of the loop with ITSELF, which is
-- what §3's `uaCompEquiv` needs and is a different term from the above
-- (`derivation⁺-equiv` of a two-step derivation associates the other way).
समुच्चयः : compEquiv व्यत्यासः व्यत्यासः ≡ idEquiv Ubhaya
समुच्चयः = equivEq (funExt lemma)
  where
  lemma : (x : Ubhaya) → equivFun (compEquiv व्यत्यासः व्यत्यासः) x ≡ x
  lemma (inl tt) = refl
  lemma (inr tt) = refl

------------------------------------------------------------------------
-- §3  Therefore the doubled crossing is `refl` AS A PATH.  Proof shape
--     taken from `Paryaya_…` §3 (आवर्तः-वर्गः); subject is the kernel's
--     derivation rather than `swap01`.
------------------------------------------------------------------------

वर्गः : comm-path ∙ comm-path ≡ refl
वर्गः =
  sym (uaCompEquiv व्यत्यासः व्यत्यासः)
  ∙ cong ua समुच्चयः
  ∙ uaIdEquiv

-- and the doubled DERIVATION's own path is `refl` too, by §2 directly.
द्वयस्य-पन्थाः : ua (derivation⁺-equiv व्यत्यास-द्वयम् σ₁) ≡ refl
द्वयस्य-पन्थाः = cong ua द्वित्वम् ∙ uaIdEquiv

------------------------------------------------------------------------
-- §4  ORDER EXACTLY TWO.  Dividing two is §3; not one is Ankapasa's
--     negative, imported rather than restated.
------------------------------------------------------------------------

द्विवर्गः : (comm-path ∙ comm-path ≡ refl) × (comm-path ≡ refl → ⊥)
द्विवर्गः = वर्गः , comm-loop-is-a-nontrivial-loop-in-the-universe

------------------------------------------------------------------------
-- §5  THE DENIAL.  A braid generator has infinite order.  This one does
--     not, and the witness is §3 at the exponent two.
------------------------------------------------------------------------

_^_ : {X : Type₀} → (X ≡ X) → ℕ → (X ≡ X)
p ^ zero  = refl
p ^ suc n = p ∙ (p ^ n)

-- infinite order: no positive power is the identity loop.
अनन्तक्रमः : {X : Type₀} → (X ≡ X) → Type₁
अनन्तक्रमः p = (n : ℕ) → (p ^ suc n ≡ refl) → ⊥

व्यत्यासः-न-अनन्तक्रमः : अनन्तक्रमः comm-path → ⊥
व्यत्यासः-न-अनन्तक्रमः h =
  h 1 (cong (comm-path ∙_) (sym (rUnit comm-path)) ∙ वर्गः)

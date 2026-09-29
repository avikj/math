{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- एकाधिकरण — one locus.
--
-- TERM.  अधिकरण · adhikaraṇa, "locus, substratum" — the place a property
-- resides.  It is a technical term in Nyya (the locus of an absence, with
-- its counterpositive) and in Prva-Mms (the topic-section).
-- It is used here in its ordinary sense, the term at which an operation
-- resides.
--
------------------------------------------------------------------------
-- WHY THIS FILE EXISTS, and it is not a limitation being recorded.
--
-- `Kernel.ControlledGrammar.NativeOperation` carries an OPEN field:
--
--     Control       : Tm → Type₀            -- the caller supplies this
--     control-sound : {t : Tm} → Control t → t ≡ source
--
-- `Control` is arbitrary.  A caller may hand the kernel any predicate on
-- terms whatsoever, including a wildly permissive one, and the kernel
-- accepts it.  `control-sound` is the entire soundness surface.
--
-- The reading this file is written against, and rejects: that the kernel
-- "cannot generalise", that `install`'s default `Control t = (t ≡ lhs)`
-- is a placeholder awaiting a schema, and that the missing schema is a
-- defect.  §1 shows the restriction is not a property of the DEFAULT.  It
-- is forced on EVERY control the field can ever hold, in one line, and it
-- is what makes the open field safe:
--
--     HOWEVER PERMISSIVE THE CALLER'S CONTROL, THE OPERATION HAS AT MOST
--     ONE LOCUS.
--
-- So the design is: maximal caller freedom, zero soundness surface.  The
-- price is that capability grows by ONE TERM per installed theorem and
-- never by a class (§3), and that price is the feature.  A schema is a
-- claim about all its instances whose correctness is checked ONCE,
-- abstractly, after which it fires everywhere unexamined.  The kernel's
-- alternative is `apply-checked`, which TRANSPORTS the certificate to the
-- site: every firing arrives carrying a proof about that firing.
--
-- SUPERSEDED READING.  This paragraph once argued that "cannot generalise"
-- and "cannot be wrong at a site" are one sentence read twice.  They are
-- not: kernel-flat/TheControlCarriesItsInstanceAndLocusSoOneTheoremFiresAtAClass
-- builds `pervading`, whose `apply-checked` transports an INSTANTIATED,
-- WOVEN derivation to every site it fires at (structural `sub-derivation`
-- and `weave-derivation`).  So a schema can fire at a class AND carry a
-- certificate about each firing.  The theorems below (§1–§4) are about
-- `NativeOperation` and remain true; the claim that the restriction is
-- forced by soundness is withdrawn.
--
-- AND THIS IS THE FIBRE LAW CHOOSING ITS BINDING.  `fibre/src/Fibre/
-- Carrier.agda`: for f : A → B, bind the OUTPUT and the fibre is
-- `singl (f a)`, contractible, so the datum rides free — that is the
-- schema, one proof and infinitely many free applications.  Bind the INPUT
-- and the fibre is `fiber f b`, the exact loss — one proof, one site, and
-- you pay again to move.  §2 computes the locus type of an installed
-- operation and it is literally a `singl`: contractible, one point, the
-- source.  The kernel is at the lossy binding on purpose.  `TheWholeDerivationTypeIsOneFibre…`
-- reports the same position from the soundness side.
--
-- WHAT IS PROVED
--   §1  eka-adhikarana      any two loci of one operation are equal, for
--                           ANY Control, no hypothesis on the caller.
--   §2  adhikarana-eka      for `install d` the locus type is contractible
--                           and its centre is the source: EXACTLY one.
--   §3  adhikarana-sruta    a library fires only at sources: if some
--                           operation of a list is enabled at t, then t is
--                           the source of one of them.  Capability is the
--                           list of sources, so n theorems give n loci.
--   §4  na-vyapakam         the denial made concrete: no NativeOperation
--                           fires at both `zero` and `suc zero`.  A schema
--                           would; that is exactly what §1 forbids.
--
------------------------------------------------------------------------

module TheInstalledTheoremHasExactlyOneLocusSoCapabilityGrowsByOneNotByAClass where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; _×_ ; ΣPathP)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate using (Tm ; zero ; suc ; Derivation)
open import Kernel.ControlledGrammar using (NativeOperation ; install)

open NativeOperation

------------------------------------------------------------------------
-- §1.  AT MOST ONE LOCUS, FOR EVERY CONTROL THE FIELD CAN HOLD.
--
-- This is the whole theorem and it is one composite.  Note what it does
-- NOT assume: nothing about `Control`, which is the caller's to choose.
------------------------------------------------------------------------

eka-adhikarana : (op : NativeOperation) (s t : Tm)
               → Control op s → Control op t → s ≡ t
eka-adhikarana op s t cs ct = control-sound op cs ∙ sym (control-sound op ct)

-- The same fact as a statement about the type of loci: it is a
-- subsingleton on the term coordinate.
adhikarana-upasamhara :
  (op : NativeOperation)
  (p q : Σ[ t ∈ Tm ] Control op t) → fst p ≡ fst q
adhikarana-upasamhara op (s , cs) (t , ct) = eka-adhikarana op s t cs ct

------------------------------------------------------------------------
-- §2.  FOR AN INSTALLED THEOREM, EXACTLY ONE — AND IT IS A `singl`.
--
-- `Control (install d) t` is `t ≡ lhs` definitionally, so the locus type
-- is Σ[ t ] (t ≡ lhs).  Reversing each path identifies it with singl lhs,
-- which Prelude proves contractible.  The centre is the source.
------------------------------------------------------------------------

Locus : NativeOperation → Type₀
Locus op = Σ[ t ∈ Tm ] Control op t

-- The locus type of an installed theorem is Σ[ t ] (t ≡ lhs): the
-- singleton with its FREE endpoint on the left.  Contractible, centre the
-- source.  The filler is the same square Prelude uses for isContrSingl,
-- reflected: H i j = p (~ i ∨ j).
adhikarana-eka : {lhs rhs : Tm} (d : Derivation lhs rhs)
               → isContr (Locus (install d))
adhikarana-eka {lhs} d =
  ( (lhs , refl)
  , λ y → ΣPathP ( sym (snd y) , (λ i j → snd y (~ i ∨ j)) ) )

-- and the centre is the source, on the nose
adhikarana-mulam : {lhs rhs : Tm} (d : Derivation lhs rhs)
                 → fst (adhikarana-eka d .fst) ≡ source (install d)
adhikarana-mulam d = refl

------------------------------------------------------------------------
-- §3.  A LIBRARY FIRES ONLY AT ITS SOURCES.
--
-- Capability is therefore the LIST OF SOURCES: n installed theorems give
-- at most n loci, additively.  There is no closure step, no matching, and
-- nothing in the type that could produce a class of terms from a finite
-- library.
------------------------------------------------------------------------

-- RECURSIVE FAMILIES, NOT INDEXED DATA, and this is not a style choice.
-- The indexed version typechecks and then warns: it matches on `_∷_` in an
-- INDEX position, so it relies on injectivity of that constructor, which
-- cubical Agda does not support — the function would not compute when
-- applied to transports.  Written as a family over the list, every clause
-- is a definitional unfolding and nothing is matched in an index.

SomeEnabled : List NativeOperation → Tm → Type₀
SomeEnabled []       t = ⊥
SomeEnabled (op ∷ L) t = Control op t ⊎ SomeEnabled L t

IsSourceOf : List NativeOperation → Tm → Type₀
IsSourceOf []       t = ⊥
IsSourceOf (op ∷ L) t = (t ≡ source op) ⊎ IsSourceOf L t

adhikarana-sruta : (L : List NativeOperation) (t : Tm)
                 → SomeEnabled L t → IsSourceOf L t
adhikarana-sruta (op ∷ L) t (inl c) = inl (control-sound op c)
adhikarana-sruta (op ∷ L) t (inr s) = inr (adhikarana-sruta L t s)

------------------------------------------------------------------------
-- §4.  THE DENIAL, CONCRETE.
--
-- A schema fires at a class of terms.  §1 forbids it, and here is the
-- smallest witness: nothing in this kernel fires at both `zero` and
-- `suc zero`.  `flat` separates the two constructors, so their identity
-- type is empty; §1 then converts a two-locus operation into that path.
------------------------------------------------------------------------

flat : Tm → Bool
flat zero    = true
flat (suc _) = false
flat _       = false

zero≢suczero : ¬ (zero ≡ suc zero)
zero≢suczero p = true≢false (cong flat p)

na-vyapakam : ¬ (Σ[ op ∈ NativeOperation ]
                   (Control op zero × Control op (suc zero)))
na-vyapakam (op , (c₀ , c₁)) = zero≢suczero (eka-adhikarana op zero (suc zero) c₀ c₁)

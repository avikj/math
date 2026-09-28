{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.MMIFailsOnTheRankCone
--
-- Monogamy of mutual information fails on a three-party entropy vector
-- that a linear configuration realises.  This decides the conjecture
-- of `notes/SESA_THE_ALIGNMENT_DEFECT_IS_A_FIBRE_AND_WHEN_IT_
-- IS_MUTUAL_INFORMATION.md` (absent from this repository) §4, whether the linear/rank cone satisfies
-- MMI.  It does not: not at four or five variables but at three, on
-- a one-dimensional space.
--
-- WHAT MMI IS.  For a tripartite entropy vector, monogamy of mutual
-- information (Hayden--Headrick--Maloney, arXiv:1107.2940) is
-- I(A:BC) ≥ I(A:B) + I(A:C), equivalently, in the symmetric form used
-- below,
--
--     h AB + h AC + h BC  ≥  h A + h B + h C + h ABC.
--
-- Every holographic entropy vector satisfies it.  General quantum states
-- do not.  The question was which side the rank cone falls on.
--
-- THE WITNESS, AND WHY IT IS LINEAR.  Take one line L over a field and
-- put U_A = U_B = U_C = L.  For EVERY nonempty S ⊆ {A,B,C} the sum
-- Σ_{i∈S} U_i is L again, so the rank function is `h S = 1` for S
-- nonempty and `h ∅ = 0` — which is `h₀` below.  It is realised by three
-- copies of one bit, X = Y = Z uniform on L.  That is the whole of the
-- linearity claim and it is true by construction: one subspace named
-- three times.
--
-- PROVED AS TERMS: the seven
-- values of `h₀`; monotonicity and submodularity at the instances MMI
-- consumes, so the refutation is not against a nonsense function; and
-- `mmi-fails`, that `rhs ≤ lhs` is uninhabited, the two sides being 4 and
-- 3.
--
-- WHY IT MATTERS TO THE TARGET NOTE.  Its §4 rejected "area = log fibre"
-- as a statement about entanglement entropy because linear rank functions
-- satisfy Ingleton and entropy does not — i.e. the rank cone is too
-- SMALL.  This closes the other direction: the rank cone is not inside
-- the holographic cone either.  The two cones are INCOMPARABLE, not
-- nested, and the `rank T` ↔ RT pairing is shut from both sides.
--
-- NOT NEW AS MATHEMATICS.  That classical and matroidal entropies violate
-- MMI is folklore in the holographic-entropy-cone literature; MMI is the
-- standard example of a holographic inequality with no classical or
-- general-quantum provenance.  What is supplied is the decision the target
-- note asked for, in its own dictionary, with the witness checked.
------------------------------------------------------------------------

module NaturalMachine.MMIFailsOnTheRankCone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; injSuc ; snotz ; +-comm)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Bool using (Bool ; true ; false ; _or_)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; Σ-syntax)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  Three parties as a Bool triple: which of A, B, C is in the subset.
------------------------------------------------------------------------

record Party : Type₀ where
  constructor ⟨_,_,_⟩
  field
    inA inB inC : Bool

∅ A B C AB AC BC ABC : Party
∅   = ⟨ false , false , false ⟩
A   = ⟨ true  , false , false ⟩
B   = ⟨ false , true  , false ⟩
C   = ⟨ false , false , true  ⟩
AB  = ⟨ true  , true  , false ⟩
AC  = ⟨ true  , false , true  ⟩
BC  = ⟨ false , true  , true  ⟩
ABC = ⟨ true  , true  , true  ⟩

------------------------------------------------------------------------
-- 2.  The witness: the rank function of three copies of one line.
--     Every nonempty subset spans the same line, so its rank is 1.
------------------------------------------------------------------------

nonempty : Party → Bool
nonempty ⟨ a , b , c ⟩ = a or (b or c)

h₀ : Party → ℕ
h₀ p = go (nonempty p)
  where
    go : Bool → ℕ
    go true  = 1
    go false = 0

h₀-∅   : h₀ ∅   ≡ 0 ;   h₀-∅   = refl
h₀-A   : h₀ A   ≡ 1 ;   h₀-A   = refl
h₀-B   : h₀ B   ≡ 1 ;   h₀-B   = refl
h₀-C   : h₀ C   ≡ 1 ;   h₀-C   = refl
h₀-AB  : h₀ AB  ≡ 1 ;   h₀-AB  = refl
h₀-AC  : h₀ AC  ≡ 1 ;   h₀-AC  = refl
h₀-BC  : h₀ BC  ≡ 1 ;   h₀-BC  = refl
h₀-ABC : h₀ ABC ≡ 1 ;   h₀-ABC = refl

------------------------------------------------------------------------
-- 3.  It is a genuine polymatroid at the instances MMI consumes, so the
--     refutation is not against a nonsense function.
------------------------------------------------------------------------

-- monotone along the chain A ⊆ AB ⊆ ABC
mono-A-AB   : h₀ A  ≡ h₀ AB  ;  mono-A-AB   = refl
mono-AB-ABC : h₀ AB ≡ h₀ ABC ;  mono-AB-ABC = refl

-- submodular at the instance MMI uses: h AB + h AC ≡ h ABC + h A
submod-instance : h₀ AB + h₀ AC ≡ h₀ ABC + h₀ A
submod-instance = refl

------------------------------------------------------------------------
-- 4.  MMI, and its refutation.
--
--     MMI h  :=  h A + h B + h C + h ABC  ≤  h AB + h AC + h BC
--
--     For h₀ that asserts 4 ≤ 3.
------------------------------------------------------------------------

lhs rhs : ℕ
lhs = h₀ AB + (h₀ AC + h₀ BC)
rhs = h₀ A + (h₀ B + (h₀ C + h₀ ABC))

lhs≡3 : lhs ≡ 3
lhs≡3 = refl

rhs≡4 : rhs ≡ 4
rhs≡4 = refl

-- 4 ≤ 3 is uninhabited: `k + 4 ≡ 3` strips to `k + 1 ≡ 0`.
¬4≤3 : ¬ (4 ≤ 3)
¬4≤3 (k , p) = snotz (injSuc (injSuc (injSuc (sym (+-comm k 4) ∙ p))))

-- MMI for h₀ would be exactly that.
MMI : (Party → ℕ) → Type₀
MMI h = (h A + (h B + (h C + h ABC))) ≤ (h AB + (h AC + h BC))

-- `subst2` is the Prelude's: it transports along both coordinates at once.
mmi-fails : ¬ (MMI h₀)
mmi-fails m = ¬4≤3 (subst2 _≤_ rhs≡4 lhs≡3 m)

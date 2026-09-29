{-# OPTIONS --cubical --safe #-}

------------------------------------------------------------------------
-- शेषशेषलेखःलेखः — the price of all of them.  Compound built here
-- from ordinary  (, all; , price).
--
-- WHY.  Mulyankana priced two of Jiva's five named Bool ⟶ ℕ edges by
-- computing their spectra point by point, and handed the other three
-- forward as ea because bellman is parameterized.  The ea dissolves:
-- over a Bool source the fibre of ANY map decomposes, at every target,
-- as a sum of two path types —
--
--     विभागः :  fiber f b ≃ (f true ≡ b) ⊎ (f false ≡ b)
--
-- with no hypothesis on the target type at all.  Every Bool-sourced
-- edge in the corpus, present and future, parameterized or not, is
-- priced by this one term: the three verdicts fall out by deciding two
-- equalities, and over a discrete target the decision is a computation
-- (निर्णयः below — a trichotomy carrying its evidence, never a flag).
--
-- So the five edges Jiva named are closed:
--   asNat, prime, DSOBellmanFinite.K   — instances, one line each;
--   bellman k v                        — an instance AT EVERY PARAMETER,
--                                        which is what pricing a family
--                                        means and why the point-by-point
--                                        road could never finish.
--
-- The verdict discipline is Avaccheda's (रिक्तम् / एकम् / बहु) and the
-- refusal of a two-valued collapse is Saptabhangi.दुर्नयः; the fibre is
-- Voevodsky's, the admitted substrate.
------------------------------------------------------------------------

module SarvaMulya_EveryBoolSourcedEdgeIsPricedAtOnceTheFibreIsASumOfTwoPathTypes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Relation.Nullary using (¬_ ; Discrete ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)

private
  variable
    ℓ : Level

module _ {B : Type ℓ} (f : Bool → B) (b : B) where

  ----------------------------------------------------------------------
  -- विभागः — the decomposition.  No hypothesis on B.
  ----------------------------------------------------------------------

  विभागः : fiber f b ≃ ((f true ≡ b) ⊎ (f false ≡ b))
  विभागः = isoToEquiv (iso fun inv ri li)
    where
    fun : fiber f b → (f true ≡ b) ⊎ (f false ≡ b)
    fun (true  , p) = inl p
    fun (false , p) = inr p

    inv : (f true ≡ b) ⊎ (f false ≡ b) → fiber f b
    inv (inl p) = true  , p
    inv (inr p) = false , p

    ri : (k : (f true ≡ b) ⊎ (f false ≡ b)) → fun (inv k) ≡ k
    ri (inl p) = refl
    ri (inr p) = refl

    li : (q : fiber f b) → inv (fun q) ≡ q
    li (true  , p) = refl
    li (false , p) = refl

  ----------------------------------------------------------------------
  -- The three verdicts, each from the decomposition's two coordinates.
  ----------------------------------------------------------------------

  रिक्तम् : ¬ (f true ≡ b) → ¬ (f false ≡ b) → ¬ fiber f b
  रिक्तम् nt nf (true  , p) = nt p
  रिक्तम् nt nf (false , p) = nf p

  एकम्-सत्ये : isSet B → (f true ≡ b) → ¬ (f false ≡ b) → isContr (fiber f b)
  एकम्-सत्ये setB p nf = (true , p) , contr
    where
    contr : (q : fiber f b) → (true , p) ≡ q
    contr (true  , q) = ΣPathP (refl , setB _ _ p q)
    contr (false , q) = Empty.rec (nf q)

  एकम्-असत्ये : isSet B → ¬ (f true ≡ b) → (f false ≡ b) → isContr (fiber f b)
  एकम्-असत्ये setB nt p = (false , p) , contr
    where
    contr : (q : fiber f b) → (false , p) ≡ q
    contr (false , q) = ΣPathP (refl , setB _ _ p q)
    contr (true  , q) = Empty.rec (nt q)

  बहु : (f true ≡ b) → (f false ≡ b) → ¬ isContr (fiber f b)
  बहु p q c =
    true≢false (cong fst (sym (snd c (true , p)) ∙ snd c (false , q)))

  ----------------------------------------------------------------------
  -- निर्णयः — over a discrete target the verdict is a computation, and
  -- it is returned WITH its evidence: an empty-fibre witness, or the
  -- contraction, or the two elements a collapse would identify.  Three
  -- positions, no flag (Saptabhangi.दुर्नयः: a two-valued verdict on
  -- three seeds must identify two of them).
  ----------------------------------------------------------------------

  Mulya : Type ℓ
  Mulya = (¬ fiber f b)
        ⊎ (isContr (fiber f b)
        ⊎ (Σ[ q₁ ∈ fiber f b ] Σ[ q₂ ∈ fiber f b ] (¬ q₁ ≡ q₂)))

  निर्णयः : Discrete B → Mulya
  निर्णयः disc with disc (f true) b | disc (f false) b
  ... | no  nt | no  nf = inl (रिक्तम् nt nf)
  ... | yes p  | no  nf = inr (inl (एकम्-सत्ये (Discrete→isSet disc) p nf))
  ... | no  nt | yes q  = inr (inl (एकम्-असत्ये (Discrete→isSet disc) nt q))
  ... | yes p  | yes q  =
        inr (inr ((true , p) , (false , q) ,
                  λ e → true≢false (cong fst e)))

------------------------------------------------------------------------
-- The five named edges, closed.  asNat and bothNat's spectra are in
-- Mulyankana already; here every one of the five — including the
-- parameterized family — is priced by instantiation.
------------------------------------------------------------------------

open import FiniteOccupancyChannelNoGo using (asNat)
open import DSOFinite
  using (bellman ; CostRelation ; Continuation)
open import DSOBellmanFinite using () renaming (K to bellmanK)
open import PointedReindexOrbitObstruction using (prime)

असंख्या-मूल्यम् : (n : ℕ) → Mulya asNat n
असंख्या-मूल्यम् n = निर्णयः asNat n discreteℕ

अग्र-मूल्यम् : (n : ℕ) → Mulya prime n
अग्र-मूल्यम् n = निर्णयः prime n discreteℕ

व्यय-मूल्यम् : (n : ℕ) → Mulya bellmanK n
व्यय-मूल्यम् n = निर्णयः bellmanK n discreteℕ

-- the family: priced at EVERY parameter, which no pointwise receipt
-- could finish.
बेल्मन्-मूल्यम् : (k : CostRelation) (v : Continuation) (n : ℕ)
               → Mulya (bellman k v) n
बेल्मन्-मूल्यम् k v n = निर्णयः (bellman k v) n discreteℕ

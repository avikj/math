{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module SATBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; fiber)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; _or_ ; isSetBool ; true≢false)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥)
import photon as P

-- A clause split across a variable cut is A(left) OR B(right).
-- Its residual is the obligation that B holds when A is false.
-- No choice of a satisfying literal is counted as an extra witness.
clause-to-obligation : (a b : Bool)
  → (a or b) ≡ true → (a ≡ false → b ≡ true)
clause-to-obligation false b h _ = h
clause-to-obligation true b h p = Empty.rec (true≢false p)

obligation-to-clause : (a b : Bool)
  → (a ≡ false → b ≡ true) → (a or b) ≡ true
obligation-to-clause false b h = h refl
obligation-to-clause true b h = refl

-- The theorem is quantified over whole clause families, with no bound
-- on the number of clauses or either assignment carrier. Finite CNF is
-- obtained by taking J finite and L/R to be assignments on disjoint scopes.
module Cut (L R J : Type)
  (leftOK : L → Type) (rightOK : R → Type)
  (A : J → L → Bool) (B : J → R → Bool) where

  Cross : L → R → Type
  Cross l r = (j : J) → (A j l or B j r) ≡ true

  Residual : (J → Bool) → R → Type
  Residual s r = (j : J) → s j ≡ false → B j r ≡ true

  signature : L → (J → Bool)
  signature l j = A j l

  Solution : Type
  Solution = Σ[ l ∈ L ] Σ[ r ∈ R ]
    (leftOK l × (rightOK r × Cross l r))

  BoundarySolution : Type
  BoundarySolution = Σ[ l ∈ L ] Σ[ r ∈ R ]
    (leftOK l × (rightOK r × Residual (signature l) r))

  -- The full assignments and the local proof objects are retained by
  -- this equivalence. Only the crossing-clause proof is rewritten.
  boundaryIso : Iso Solution BoundarySolution
  Iso.fun boundaryIso (l , r , pl , pr , h) =
    l , r , pl , pr , λ j → clause-to-obligation (A j l) (B j r) (h j)
  Iso.inv boundaryIso (l , r , pl , pr , h) =
    l , r , pl , pr , λ j → obligation-to-clause (A j l) (B j r) (h j)
  Iso.rightInv boundaryIso (l , r , pl , pr , h) i =
    l , r , pl , pr ,
    isPropΠ (λ j → isPropΠ (λ _ → isSetBool (B j r) true))
      (λ j → clause-to-obligation (A j l) (B j r)
        (obligation-to-clause (A j l) (B j r) (h j))) h i
  Iso.leftInv boundaryIso (l , r , pl , pr , h) i =
    l , r , pl , pr ,
    isPropΠ (λ j → isSetBool (A j l or B j r) true)
      (λ j → obligation-to-clause (A j l) (B j r)
        (clause-to-obligation (A j l) (B j r) (h j))) h i

  boundary-equivalence : Solution ≃ BoundarySolution
  boundary-equivalence = isoToEquiv boundaryIso

  -- Semantic inclusion of obligation sets, oriented toward the easier
  -- continuation: every obligation in easy is also present in hard.
  FewerObligations : (J → Bool) → (J → Bool) → Type
  FewerObligations easy hard = (j : J) → easy j ≡ false → hard j ≡ false

  dominance : (easy hard : J → Bool)
    → FewerObligations easy hard
    → (r : R) → Residual hard r → Residual easy r
  dominance easy hard included r h j p = h j (included j p)

  -- Representatives are supplied with actual left assignments and a
  -- lawful dominance map. Constructing a minimal family and pricing its
  -- construction are separate operations, not hidden hypotheses of a
  -- claimed runtime bound.
  module Representatives (K : Type) (represent : K → L)
    (valid : (k : K) → leftOK (represent k))
    (select : (l : L) → leftOK l → K)
    (included : (l : L) (pl : leftOK l)
      → FewerObligations (signature (represent (select l pl))) (signature l))
    where

    ReducedSolution : Type
    ReducedSolution = Σ[ k ∈ K ] Σ[ r ∈ R ]
      (rightOK r × Residual (signature (represent k)) r)

    reduce-witness : Solution → ReducedSolution
    reduce-witness (l , r , pl , pr , h) =
      select l pl , r , pr ,
      dominance (signature (represent (select l pl))) (signature l)
        (included l pl) r
        (λ j → clause-to-obligation (A j l) (B j r) (h j))

    reconstruct-witness : ReducedSolution → Solution
    reconstruct-witness (k , r , pr , h) =
      represent k , r , valid k , pr ,
      λ j → obligation-to-clause (A j (represent k)) (B j r) (h j)

    -- This reduction preserves inhabitedness and emptiness in both
    -- directions, not an unqualified equivalence of all assignments.
    empty-to-empty : (Solution → ⊥) → ReducedSolution → ⊥
    empty-to-empty no x = no (reconstruct-witness x)

    empty-from-empty : (ReducedSolution → ⊥) → Solution → ⊥
    empty-from-empty no x = no (reduce-witness x)

    -- The existing universal fibre law gives exactly the extra object
    -- required for a genuinely lossless version of this same reduction.
    retained-reduction : Solution ≃ Σ ReducedSolution (fiber reduce-witness)
    retained-reduction = P.Fibre.lossless reduce-witness

    right-assignment-preserved : (s : Solution)
      → fst (snd (reconstruct-witness (reduce-witness s))) ≡ fst (snd s)
    right-assignment-preserved s = refl

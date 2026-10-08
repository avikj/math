{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Entanglement is the fibre of the product comparison, and a living step
-- is one that refuses to descend to the marginals.
--
-- ONE MAP CARRIES THE WHOLE VOCABULARY.  A joint state of two parts is
-- a type J with two projections p : J → A and q : J → B, and everything
-- the words below name is an officer of the single comparison map
--
--     ⟨p,q⟩ : J → A × B.
--
-- §0 · THE LEDGER IS GENERAL.  For every joint whatsoever, the total
-- space of the entanglement fibres is the joint itself:
-- Σ_{(a,b)} fib_{⟨p,q⟩}(a,b) ≃ J (`fibreSum`), by the same interval trick
-- that proves abstract 25's e_f.  Nothing double-kept, nothing dropped:
-- the fibres carry exactly what the marginals forgot, and summing them
-- back recovers the whole.  Applied to ⟨p,q⟩ this is the purification.
--
-- §1 · INDEPENDENCE IS THE COMPARISON BEING AN EQUIVALENCE, exhibited
-- at the product pole: for J = A × B with the two projections, the
-- comparison is definitionally the identity (Σ-eta), so `idIsEquiv`
-- closes it with no path algebra.
--
-- §2 · ENTANGLEMENT IS THE FIBRE OF THE COMPARISON, and both failures
-- are POINTED AT rather than counted, in the discipline of abstract 18
-- (a blindness is a named identification, not a cardinality argument):
--   fibreEmpty — over the diagonal joint (J = Bool sitting in Bool × Bool
--   as j ↦ (j , j)) the fibre over (true , false) is EMPTY: a pair of
--   marginal readings the whole never realises.  The refutation is two
--   `cong`s and `true≢false`.
--   many — over the joint that outruns its marginals (J = Bool over
--   Unit × Unit) the fibre over the one reading holds TWO NAMED POINTS,
--   distinguished by `cong fst`: a hidden degree of freedom the two
--   marginals jointly cannot see.
--
-- §3 · CONDITIONAL CERTAINTY IS A RECONSTRUCTION, NOT A NUMBER.  On the
-- diagonal joint, either reading determines the other: the recovering
-- function is exhibited and the commuting square is `refl`.  This is
-- H(A|B) = 0 in its fibre form — what abstract 18 calls a
-- reconstruction — and on this joint it holds BOTH ways, so the joint
-- is the graph of a bijection: the pole where every bit of marginal
-- uncertainty is shared.  The two poles (§1 product, §3 graph) bracket
-- the same two-element alphabet.
--
-- §4 · A LIVING STEP IS ONE THAT REFUSES TO DESCEND TO THE MARGINALS.
-- The word LIVING is a definition, not a metaphor, and it is total
-- here: a joint step `step : J → J` DESCENDS along p when some
-- f : A → A closes the square f ∘ p ∼ p ∘ step, and the descent
-- structure is fully characterised — a pair (f , g) simulates the step
-- exactly when each side descends separately (`pairBothWays`, proved in
-- BOTH directions).  Over the full product joint the controlled-not
-- step (a , b) ↦ (a ⊕ b , b) is placed exactly: it descends on the
-- environment side by `refl` (`rightDescentHolds`) and REFUSES on the visible
-- side (`livingStepNoMarginal`) — any candidate f is interrogated at (true , false)
-- and (true , true), where fst agrees and fst ∘ step disagrees, and
-- the collision is `true≢false`.  A fortiori no pair simulates it
-- (`livingStepNoPairMarginal`).  Beside it, (a , b) ↦ (not a , b) descends on
-- BOTH sides by `refl` (`deadStepDescends`, `deadStepDescendsAsPair`): decoherence.  For both
-- steps both verdicts are terms; no case is left to judgement.
--
-- §5 · THE INFORMATION EQUATION, EXACT AND EXPONENTIAL.  The identity
-- I(A;B) = log(|A×B|/|J|) is not cited and no logarithm is taken —
-- following the machine's own refusal of floats (doa 0012: exact
-- objects only, sanna stated in the verse), it is proved in the form
-- the exact object takes: 2^I · |J| = |A|·|B| with I = 1, as an
-- equivalence rather than an equation of reals.  The living step
-- ITSELF is that equivalence: controlled-not is an involution
-- (`livingStepInvolution`), hence an equivalence A × B ≃ A × B (`livingStepEquiv`),
-- and it carries the diagonal joint pointwise, by `refl` per point,
-- onto the slice {parity = false} (`diagonalPlacement`): the reading space
-- splits as (one bit) × (one copy of J), and the factor Bool IS the
-- mutual information, held as a type.  Two corollaries close two more
-- doors: the living step is GLOBALLY LOSSLESS while locally refusing —
-- so life is consultation, not destruction, and irreversibility is not
-- the content of §4; and the bit is not a summary of the fibres but
-- decides them (§6).
--
-- §6 · THE ORACLE DECIDES EVERY DOOR.  In this corpus an oracle
-- separation is a theorem about what a reading consults
-- (`OracleQueries`: a query simulated by post-processing that ignores
-- the oracle carries no charge).  Both poles of §4 are placed on that
-- axis by terms: the dead step is simulated exactly by post-processing
-- that ignores the hidden half — its square closes by `refl` — while
-- the living step is the checked refusal of every such simulation.
-- And the entanglement fibres themselves are oracle-decidable: ONE
-- query to the parity bit decides every fibre of the diagonal joint,
--
--     fib_{diag}(a,b) ≃ (fst (cnot (a,b)) ≡ false)      (`gateDecision`)
--
-- proved as a propositional biimplication between prop fibres (the
-- diagonal is injective into a set, so its fibres are propositions)
-- — the door is not open: each fibre is either contracted or refuted,
-- uniformly, by the bit the living step computes.
--
-- RELATION TO THE CORPUS.  `Tantutrayam_↦` puts
-- the three fibre verdicts over ONE codomain with three maps; here the
-- same three verdicts (contractible / empty / two-point) occur as
-- readings of ONE construction, the product comparison, varying the
-- joint.  `CollapseIffEveryNayaAgrees` is the standpoint-level
-- statement of §2's many: both-inhabited is not identifiable.
-- `OracleQueries.fe-simulated-by-constant` is the shape §6's dead pole
-- instantiates.  Abstract 25's lossless completion applied to ⟨p,q⟩ is
-- §0's `fibreSum`, and its trace-is-fibre discipline is why §5 states the
-- information exponentially instead of numerically.
------------------------------------------------------------------------

module EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (isEquiv ; fiber ; idIsEquiv ; equiv-proof ; _≃_ ; propBiimpl→Equiv)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Functions.Embedding using (injective→hasPropFibers)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false ; isSetBool)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 0 · the comparison map, and the general ledger.
------------------------------------------------------------------------

module _ {J A B : Type ℓ} (p : J → A) (q : J → B) where

  compare : J → A × B
  compare j = (p j , q j)

  -- independence IS this map being an equivalence; entanglement IS its
  -- fibre family.  Both words name the same object from the two sides.
  independence : Type ℓ
  independence = isEquiv compare

  entanglementFibre : A × B → Type ℓ
  entanglementFibre = fiber compare

  -- the ledger: the joint is the sum of its entanglement fibres.
  -- nothing double-kept, nothing dropped — the same interval trick,
  -- λ i → (pth i , j , λ k → pth (i ∧ k)), that proves abstract 25's
  -- e_f, here read as: purifying and then forgetting is the identity.
  fibreSum : Iso (Σ (A × B) entanglementFibre) J
  fibreSum = iso (λ (_ , j , _) → j)
                (λ j → (compare j , j , refl))
                (λ j → refl)
                (λ (ab , j , pth) i → (pth i , j , λ k → pth (i ∧ k)))

------------------------------------------------------------------------
-- 1 · the product pole: the comparison is the identity, definitionally.
------------------------------------------------------------------------

productCompare : Bool × Bool → Bool × Bool
productCompare = compare fst snd

-- Σ-eta makes ⟨fst , snd⟩ definitionally the identity, so independence
-- of the product joint is `idIsEquiv` with nothing to transport.
productIndependent : isEquiv productCompare
productIndependent = idIsEquiv (Bool × Bool)

------------------------------------------------------------------------
-- 2 · the diagonal joint: an EMPTY fibre, named.
------------------------------------------------------------------------

-- J = Bool, both projections the identity: the support {(t,t),(f,f)}.
diagonalCompare : Bool → Bool × Bool
diagonalCompare = compare (λ j → j) (λ j → j)

-- the excluded reading: (true , false) is a pair of marginal readings
-- the whole never realises.  A fibre point would identify true with
-- false through its own base point.
fibreEmpty : ¬ fiber diagonalCompare (true , false)
fibreEmpty (j , pth) = true≢false (sym (cong fst pth) ∙ cong snd pth)

-- so the diagonal joint is entangled: the comparison is no equivalence,
-- because an equivalence has an inhabited fibre over every point.
diagonalNotIndependent : ¬ isEquiv diagonalCompare
diagonalNotIndependent e = fibreEmpty (e .equiv-proof (true , false) .fst)

-- the diagonal is injective into a set, so every entanglement fibre of
-- this joint is a proposition: each door is either open or walled, and
-- §6 decides which, uniformly.
diagonalFibreIsProp : (ab : Bool × Bool) → isProp (fiber diagonalCompare ab)
diagonalFibreIsProp =
  injective→hasPropFibers (isSet× isSetBool isSetBool) (λ pth → cong fst pth)

------------------------------------------------------------------------
-- 3 · the joint that outruns its marginals: a TWO-POINT fibre, named.
------------------------------------------------------------------------

-- J = Bool over the one-point parts: two globally distinct situations
-- whose every marginal reading agrees.
hiddenCompare : Bool → Unit × Unit
hiddenCompare = compare (λ _ → tt) (λ _ → tt)

hiddenTrue hiddenFalse : fiber hiddenCompare (tt , tt)
hiddenTrue  = (true  , refl)
hiddenFalse = (false , refl)

-- the two residents are distinct, by the base point alone.
hiddenDistinct : ¬ hiddenTrue ≡ hiddenFalse
hiddenDistinct pth = true≢false (cong fst pth)

------------------------------------------------------------------------
-- 4 · conditional certainty is a reconstruction: H(A|B) = 0 as a term.
------------------------------------------------------------------------

-- on the diagonal joint, the reading of B determines A: the recovering
-- function is exhibited and the square commutes by refl.  By symmetry
-- of the construction the same term is the other direction, so the
-- joint is the graph of a bijection — the pole where the part's
-- uncertainty is entirely the whole's information.
recover : Bool → Bool
recover b = b

recoverWitness : (j : Bool) → recover (snd (diagonalCompare j)) ≡ fst (diagonalCompare j)
recoverWitness j = refl

------------------------------------------------------------------------
-- 5 · the living step: no marginal endomap simulates it.
------------------------------------------------------------------------

_⊕_ : Bool → Bool → Bool
false ⊕ b = b
true  ⊕ b = not b

-- the controlled-not on the full product joint: the visible part is
-- rewritten by consulting the hidden part.
livingStep : Bool × Bool → Bool × Bool
livingStep (a , b) = (a ⊕ b , b)

-- descent along a projection: some endomap of the part closing the
-- square against the step.  Descent along fst is simulation of the
-- visible half by post-processing that ignores the hidden half — the
-- oracle-free reading, in OracleQueries' sense.
descendsToMarginal descendsOnRight : (Bool × Bool → Bool × Bool) → Type
descendsToMarginal step =
  Σ (Bool → Bool) (λ f → (j : Bool × Bool) → f (fst j) ≡ fst (step j))
descendsOnRight step =
  Σ (Bool → Bool) (λ g → (j : Bool × Bool) → g (snd j) ≡ snd (step j))

descendsAsPair : (Bool × Bool → Bool × Bool) → Type
descendsAsPair step =
  Σ (Bool → Bool) (λ f → Σ (Bool → Bool) (λ g →
    (j : Bool × Bool) → (f (fst j) , g (snd j)) ≡ step j))

-- the descent structure is fully characterised: a pair simulates the
-- step exactly when each side descends separately.  Both directions
-- are terms, so §4's definition leaves no case to judgement.
pairBothWays : (s : Bool × Bool → Bool × Bool)
             → (descendsAsPair s → descendsToMarginal s × descendsOnRight s)
             × (descendsToMarginal s × descendsOnRight s → descendsAsPair s)
pairBothWays s =
  (λ (f , g , h) → (f , λ j → cong fst (h j)) , (g , λ j → cong snd (h j))) ,
  (λ ((f , hf) , (g , hg)) → f , g , λ j i → (hf j i , hg j i))

-- THE THEOREM.  The two interrogating configurations share their
-- visible half and split their hidden half; any simulator must answer
-- both with one value, and the collision is true≢false.
livingStepNoMarginal : ¬ descendsToMarginal livingStep
livingStepNoMarginal (f , h) = true≢false (sym (h (true , false)) ∙ h (true , true))

-- a fortiori, no PAIR of marginal endomaps simulates the living step.
livingStepNoPairMarginal : ¬ descendsAsPair livingStep
livingStepNoPairMarginal yu = livingStepNoMarginal (fst (fst (pairBothWays livingStep) yu))

-- the refusal is LOCATED: the same step descends on the environment
-- side by refl.  The organism's half consults; the environment's half
-- rides untouched.  Life is one-sided, and the side is named.
rightDescentHolds : descendsOnRight livingStep
rightDescentHolds = (λ b → b) , λ j → refl

------------------------------------------------------------------------
-- 6 · beside it, the decoherent step: descent on both sides by refl.
------------------------------------------------------------------------

deadStep : Bool × Bool → Bool × Bool
deadStep (a , b) = (not a , b)

deadStepDescends : descendsToMarginal deadStep
deadStepDescends = not , λ j → refl

deadStepDescendsAsPair : descendsAsPair deadStep
deadStepDescendsAsPair = snd (pairBothWays deadStep) (deadStepDescends , (λ b → b) , λ j → refl)

-- the contrast is the content: same joint, same projections, one step
-- provably inseparable and one separable, and the difference is not a
-- number but a term — whether the square closes.

------------------------------------------------------------------------
-- 7 · the information equation, exact and exponential.
------------------------------------------------------------------------

-- controlled-not is an involution: consulting the same oracle twice
-- undoes the consultation.  Four configurations, four refl.
livingStepInvolution : (j : Bool × Bool) → livingStep (livingStep j) ≡ j
livingStepInvolution (false , false) = refl
livingStepInvolution (false , true)  = refl
livingStepInvolution (true  , false) = refl
livingStepInvolution (true  , true)  = refl

-- so the LIVING step is an EQUIVALENCE of the whole reading space:
-- globally lossless, locally refusing.  Life is consultation, not
-- destruction — the step that no marginal simulates loses nothing.
livingStepEquiv : (Bool × Bool) ≃ (Bool × Bool)
livingStepEquiv = isoToEquiv (iso livingStep livingStep livingStepInvolution livingStepInvolution)

-- and under it the diagonal joint occupies exactly the slice
-- {parity = false}, pointwise by refl: the reading space is (one bit)
-- × (one copy of the joint), which is 2^I · |J| = |A|·|B| with I = 1
-- held as a TYPE — the mutual information in the exact, exponential
-- form, with no logarithm taken and no real number invoked.
diagonalPlacement : (j : Bool) → livingStep (diagonalCompare j) ≡ (false , j)
diagonalPlacement false = refl
diagonalPlacement true  = refl

-- the parity of a doubled coordinate vanishes; the oracle's answer on
-- the diagonal is uniform.
⊕-self : (j : Bool) → j ⊕ j ≡ false
⊕-self false = refl
⊕-self true  = refl

-- THE ORACLE DECIDES EVERY DOOR.  One query to the parity bit — the
-- bit the living step computes — decides every entanglement fibre of
-- the diagonal joint: fibre and answer are equivalent propositions.
-- No fibre is left undetermined; each is contracted or refuted by the
-- same uniform reading.
gateDecision : (ab : Bool × Bool)
             → fiber diagonalCompare ab ≃ (fst (livingStep ab) ≡ false)
gateDecision ab =
  propBiimpl→Equiv (diagonalFibreIsProp ab) (isSetBool _ _)
    (λ (j , pth) → sym (cong (λ x → fst (livingStep x)) pth) ∙ ⊕-self j)
    (answer ab)
  where
  answer : (ab : Bool × Bool)
          → fst (livingStep ab) ≡ false → fiber diagonalCompare ab
  answer (false , false) _ = (false , refl)
  answer (true  , true)  _ = (true  , refl)
  answer (false , true)  e = Empty.rec (true≢false e)
  answer (true  , false) e = Empty.rec (true≢false e)

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- जीव — संश्लेषः तुलनातन्तुः, जीवनं च अवतरणस्य निषेधः ।
--
-- (entanglement is the fibre of the product comparison, and life is
--  the refusal of the descent.)
--
-- ONE MAP CARRIES THE WHOLE VOCABULARY.  A joint state of two parts is
-- a type J with two projections p : J → A and q : J → B, and everything
-- the words below name is an officer of the single comparison map
--
--     ⟨p,q⟩ : J → A × B.
--
-- §० · THE LEDGER IS GENERAL.  For every joint whatsoever, the total
-- space of the entanglement fibres is the joint itself:
-- Σ_{(a,b)} fib_{⟨p,q⟩}(a,b) ≃ J (`संकलनम्`), by the same interval trick
-- that proves abstract 25's e_f.  Nothing double-kept, nothing dropped:
-- the fibres carry exactly what the marginals forgot, and summing them
-- back recovers the whole.  Applied to ⟨p,q⟩ this is the purification.
--
-- §१ · INDEPENDENCE IS THE COMPARISON BEING AN EQUIVALENCE, exhibited
-- at the product pole: for J = A × B with the two projections, the
-- comparison is definitionally the identity (Σ-eta), so `idIsEquiv`
-- closes it with no path algebra.
--
-- §२ · ENTANGLEMENT IS THE FIBRE OF THE COMPARISON, and both failures
-- are POINTED AT rather than counted, in the discipline of abstract 18
-- (a blindness is a named identification, not a cardinality argument):
--   रिक्तम् — over the diagonal joint (J = Bool sitting in Bool × Bool
--   as j ↦ (j , j)) the fibre over (true , false) is EMPTY: a pair of
--   marginal readings the whole never realises.  The refutation is two
--   `cong`s and `true≢false`.
--   बहु — over the joint that outruns its marginals (J = Bool over
--   Unit × Unit) the fibre over the one reading holds TWO NAMED POINTS,
--   distinguished by `cong fst`: a hidden degree of freedom the two
--   marginals jointly cannot see.
--
-- §३ · CONDITIONAL CERTAINTY IS A RECONSTRUCTION, NOT A NUMBER.  On the
-- diagonal joint, either reading determines the other: the recovering
-- function is exhibited and the commuting square is `refl`.  This is
-- H(A|B) = 0 in its fibre form — what abstract 18 calls a
-- reconstruction — and on this joint it holds BOTH ways, so the joint
-- is the graph of a bijection: the pole where every bit of marginal
-- uncertainty is shared.  The two poles (§१ product, §३ graph) bracket
-- the same two-element alphabet.
--
-- §४ · A LIVING STEP IS ONE THAT REFUSES TO DESCEND TO THE MARGINALS.
-- The word LIVING is a definition, not a metaphor, and it is total
-- here: a joint step `step : J → J` DESCENDS along p when some
-- f : A → A closes the square f ∘ p ∼ p ∘ step, and the descent
-- structure is fully characterised — a pair (f , g) simulates the step
-- exactly when each side descends separately (`युगलम्-उभयतः`, proved in
-- BOTH directions).  Over the full product joint the controlled-not
-- step (a , b) ↦ (a ⊕ b , b) is placed exactly: it descends on the
-- environment side by `refl` (`दक्षिण-विलयः`) and REFUSES on the visible
-- side (`जीवति`) — any candidate f is interrogated at (true , false)
-- and (true , true), where fst agrees and fst ∘ step disagrees, and
-- the collision is `true≢false`.  A fortiori no pair simulates it
-- (`जीवति-युगलेऽपि`).  Beside it, (a , b) ↦ (not a , b) descends on
-- BOTH sides by `refl` (`विलयः`, `मृत-युगलम्`): decoherence.  For both
-- steps both verdicts are terms; no case is left to judgement.
--
-- §५ · THE INFORMATION EQUATION, EXACT AND EXPONENTIAL.  The identity
-- I(A;B) = log(|A×B|/|J|) is not cited and no logarithm is taken —
-- following the machine's own refusal of floats (doa 0012: exact
-- objects only, sanna stated in the verse), it is proved in the form
-- the exact object takes: 2^I · |J| = |A|·|B| with I = 1, as an
-- equivalence rather than an equation of reals.  The living step
-- ITSELF is that equivalence: controlled-not is an involution
-- (`जीवन-द्विः`), hence an equivalence A × B ≃ A × B (`सूचना-समीकरणम्`),
-- and it carries the diagonal joint pointwise, by `refl` per point,
-- onto the slice {parity = false} (`कर्ण-स्थानम्`): the reading space
-- splits as (one bit) × (one copy of J), and the factor Bool IS the
-- mutual information, held as a type.  Two corollaries close two more
-- doors: the living step is GLOBALLY LOSSLESS while locally refusing —
-- so life is consultation, not destruction, and irreversibility is not
-- the content of §४; and the bit is not a summary of the fibres but
-- decides them (§६).
--
-- §६ · THE ORACLE DECIDES EVERY DOOR.  In this corpus an oracle
-- separation is a theorem about what a reading consults
-- (`OracleQueries`: a query simulated by post-processing that ignores
-- the oracle carries no charge).  Both poles of §४ are placed on that
-- axis by terms: the dead step is simulated exactly by post-processing
-- that ignores the hidden half — its square closes by `refl` — while
-- the living step is the checked refusal of every such simulation.
-- And the entanglement fibres themselves are oracle-decidable: ONE
-- query to the parity bit decides every fibre of the diagonal joint,
--
--     fib_{diag}(a,b) ≃ (fst (cnot (a,b)) ≡ false)      (`द्वार-निर्णयः`)
--
-- proved as a propositional biimplication between prop fibres (the
-- diagonal is injective into a set, so its fibres are propositions)
-- — the door is not open: each fibre is either contracted or refuted,
-- uniformly, by the bit the living step computes.
--
-- RELATION TO THE CORPUS.  `Tantutrayam_↦` (absent from this repository) puts
-- the three fibre verdicts over ONE codomain with three maps; here the
-- same three verdicts (contractible / empty / two-point) occur as
-- readings of ONE construction, the product comparison, varying the
-- joint.  `Durnaya_CollapseIffEveryNayaAgrees` is the standpoint-level
-- statement of §२'s बहु: both-inhabited is not identifiable.
-- `OracleQueries.fe-simulated-by-constant` is the shape §६'s dead pole
-- instantiates.  Abstract 25's lossless completion applied to ⟨p,q⟩ is
-- §०'s `संकलनम्`, and its trace-is-fibre discipline is why §५ states the
-- information exponentially instead of numerically.
------------------------------------------------------------------------

module Jiva_EntanglementIsTheFibreOfTheProductComparisonAndTheLivingStepRefusesToDescendToTheMarginals where

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
-- ० · the comparison map, and the general ledger.
------------------------------------------------------------------------

module _ {J A B : Type ℓ} (p : J → A) (q : J → B) where

  तुलना : J → A × B
  तुलना j = (p j , q j)

  -- independence IS this map being an equivalence; entanglement IS its
  -- fibre family.  Both words name the same object from the two sides.
  स्वातन्त्र्यम् : Type ℓ
  स्वातन्त्र्यम् = isEquiv तुलना

  संश्लेष-तन्तुः : A × B → Type ℓ
  संश्लेष-तन्तुः = fiber तुलना

  -- the ledger: the joint is the sum of its entanglement fibres.
  -- nothing double-kept, nothing dropped — the same interval trick,
  -- λ i → (pth i , j , λ k → pth (i ∧ k)), that proves abstract 25's
  -- e_f, here read as: purifying and then forgetting is the identity.
  संकलनम् : Iso (Σ (A × B) संश्लेष-तन्तुः) J
  संकलनम् = iso (λ (_ , j , _) → j)
                (λ j → (तुलना j , j , refl))
                (λ j → refl)
                (λ (ab , j , pth) i → (pth i , j , λ k → pth (i ∧ k)))

------------------------------------------------------------------------
-- १ · the product pole: the comparison is the identity, definitionally.
------------------------------------------------------------------------

घट-तुलना : Bool × Bool → Bool × Bool
घट-तुलना = तुलना fst snd

-- Σ-eta makes ⟨fst , snd⟩ definitionally the identity, so independence
-- of the product joint is `idIsEquiv` with nothing to transport.
घटः-स्वतन्त्रः : isEquiv घट-तुलना
घटः-स्वतन्त्रः = idIsEquiv (Bool × Bool)

------------------------------------------------------------------------
-- २ · the diagonal joint: an EMPTY fibre, named.
------------------------------------------------------------------------

-- J = Bool, both projections the identity: the support {(t,t),(f,f)}.
कर्ण-तुलना : Bool → Bool × Bool
कर्ण-तुलना = तुलना (λ j → j) (λ j → j)

-- the excluded reading: (true , false) is a pair of marginal readings
-- the whole never realises.  A fibre point would identify true with
-- false through its own base point.
रिक्तम् : ¬ fiber कर्ण-तुलना (true , false)
रिक्तम् (j , pth) = true≢false (sym (cong fst pth) ∙ cong snd pth)

-- so the diagonal joint is entangled: the comparison is no equivalence,
-- because an equivalence has an inhabited fibre over every point.
कर्णः-न-स्वतन्त्रः : ¬ isEquiv कर्ण-तुलना
कर्णः-न-स्वतन्त्रः e = रिक्तम् (e .equiv-proof (true , false) .fst)

-- the diagonal is injective into a set, so every entanglement fibre of
-- this joint is a proposition: each door is either open or walled, and
-- §६ decides which, uniformly.
कर्ण-तन्तुः-वाक्यम् : (ab : Bool × Bool) → isProp (fiber कर्ण-तुलना ab)
कर्ण-तन्तुः-वाक्यम् =
  injective→hasPropFibers (isSet× isSetBool isSetBool) (λ pth → cong fst pth)

------------------------------------------------------------------------
-- ३ · the joint that outruns its marginals: a TWO-POINT fibre, named.
------------------------------------------------------------------------

-- J = Bool over the one-point parts: two globally distinct situations
-- whose every marginal reading agrees.
गूढ-तुलना : Bool → Unit × Unit
गूढ-तुलना = तुलना (λ _ → tt) (λ _ → tt)

गूढ-सत्यम् गूढ-असत्यम् : fiber गूढ-तुलना (tt , tt)
गूढ-सत्यम्  = (true  , refl)
गूढ-असत्यम् = (false , refl)

-- the two residents are distinct, by the base point alone.
गूढौ-भिन्नौ : ¬ गूढ-सत्यम् ≡ गूढ-असत्यम्
गूढौ-भिन्नौ pth = true≢false (cong fst pth)

------------------------------------------------------------------------
-- ४ · conditional certainty is a reconstruction: H(A|B) = 0 as a term.
------------------------------------------------------------------------

-- on the diagonal joint, the reading of B determines A: the recovering
-- function is exhibited and the square commutes by refl.  By symmetry
-- of the construction the same term is the other direction, so the
-- joint is the graph of a bijection — the pole where the part's
-- uncertainty is entirely the whole's information.
प्रत्यानयनम् : Bool → Bool
प्रत्यानयनम् b = b

प्रत्यानयन-साक्षी : (j : Bool) → प्रत्यानयनम् (snd (कर्ण-तुलना j)) ≡ fst (कर्ण-तुलना j)
प्रत्यानयन-साक्षी j = refl

------------------------------------------------------------------------
-- ५ · the living step: no marginal endomap simulates it.
------------------------------------------------------------------------

_⊕_ : Bool → Bool → Bool
false ⊕ b = b
true  ⊕ b = not b

-- the controlled-not on the full product joint: the visible part is
-- rewritten by consulting the hidden part.
जीवन-पदम् : Bool × Bool → Bool × Bool
जीवन-पदम् (a , b) = (a ⊕ b , b)

-- descent along a projection: some endomap of the part closing the
-- square against the step.  Descent along fst is simulation of the
-- visible half by post-processing that ignores the hidden half — the
-- oracle-free reading, in OracleQueries' sense.
अवतरणम् दक्षिण-अवतरणम् : (Bool × Bool → Bool × Bool) → Type
अवतरणम् step =
  Σ (Bool → Bool) (λ f → (j : Bool × Bool) → f (fst j) ≡ fst (step j))
दक्षिण-अवतरणम् step =
  Σ (Bool → Bool) (λ g → (j : Bool × Bool) → g (snd j) ≡ snd (step j))

युगल-अवतरणम् : (Bool × Bool → Bool × Bool) → Type
युगल-अवतरणम् step =
  Σ (Bool → Bool) (λ f → Σ (Bool → Bool) (λ g →
    (j : Bool × Bool) → (f (fst j) , g (snd j)) ≡ step j))

-- the descent structure is fully characterised: a pair simulates the
-- step exactly when each side descends separately.  Both directions
-- are terms, so §४'s definition leaves no case to judgement.
युगलम्-उभयतः : (s : Bool × Bool → Bool × Bool)
             → (युगल-अवतरणम् s → अवतरणम् s × दक्षिण-अवतरणम् s)
             × (अवतरणम् s × दक्षिण-अवतरणम् s → युगल-अवतरणम् s)
युगलम्-उभयतः s =
  (λ (f , g , h) → (f , λ j → cong fst (h j)) , (g , λ j → cong snd (h j))) ,
  (λ ((f , hf) , (g , hg)) → f , g , λ j i → (hf j i , hg j i))

-- THE THEOREM.  The two interrogating configurations share their
-- visible half and split their hidden half; any simulator must answer
-- both with one value, and the collision is true≢false.
जीवति : ¬ अवतरणम् जीवन-पदम्
जीवति (f , h) = true≢false (sym (h (true , false)) ∙ h (true , true))

-- a fortiori, no PAIR of marginal endomaps simulates the living step.
जीवति-युगलेऽपि : ¬ युगल-अवतरणम् जीवन-पदम्
जीवति-युगलेऽपि yu = जीवति (fst (fst (युगलम्-उभयतः जीवन-पदम्) yu))

-- the refusal is LOCATED: the same step descends on the environment
-- side by refl.  The organism's half consults; the environment's half
-- rides untouched.  Life is one-sided, and the side is named.
दक्षिण-विलयः : दक्षिण-अवतरणम् जीवन-पदम्
दक्षिण-विलयः = (λ b → b) , λ j → refl

------------------------------------------------------------------------
-- ६ · beside it, the decoherent step: descent on both sides by refl.
------------------------------------------------------------------------

मृत-पदम् : Bool × Bool → Bool × Bool
मृत-पदम् (a , b) = (not a , b)

विलयः : अवतरणम् मृत-पदम्
विलयः = not , λ j → refl

मृत-युगलम् : युगल-अवतरणम् मृत-पदम्
मृत-युगलम् = snd (युगलम्-उभयतः मृत-पदम्) (विलयः , (λ b → b) , λ j → refl)

-- the contrast is the content: same joint, same projections, one step
-- provably inseparable and one separable, and the difference is not a
-- number but a term — whether the square closes.

------------------------------------------------------------------------
-- ७ · the information equation, exact and exponential.
------------------------------------------------------------------------

-- controlled-not is an involution: consulting the same oracle twice
-- undoes the consultation.  Four configurations, four refl.
जीवन-द्विः : (j : Bool × Bool) → जीवन-पदम् (जीवन-पदम् j) ≡ j
जीवन-द्विः (false , false) = refl
जीवन-द्विः (false , true)  = refl
जीवन-द्विः (true  , false) = refl
जीवन-द्विः (true  , true)  = refl

-- so the LIVING step is an EQUIVALENCE of the whole reading space:
-- globally lossless, locally refusing.  Life is consultation, not
-- destruction — the step that no marginal simulates loses nothing.
सूचना-समीकरणम् : (Bool × Bool) ≃ (Bool × Bool)
सूचना-समीकरणम् = isoToEquiv (iso जीवन-पदम् जीवन-पदम् जीवन-द्विः जीवन-द्विः)

-- and under it the diagonal joint occupies exactly the slice
-- {parity = false}, pointwise by refl: the reading space is (one bit)
-- × (one copy of the joint), which is 2^I · |J| = |A|·|B| with I = 1
-- held as a TYPE — the mutual information in the exact, exponential
-- form, with no logarithm taken and no real number invoked.
कर्ण-स्थानम् : (j : Bool) → जीवन-पदम् (कर्ण-तुलना j) ≡ (false , j)
कर्ण-स्थानम् false = refl
कर्ण-स्थानम् true  = refl

-- the parity of a doubled coordinate vanishes; the oracle's answer on
-- the diagonal is uniform.
⊕-अन्वयः : (j : Bool) → j ⊕ j ≡ false
⊕-अन्वयः false = refl
⊕-अन्वयः true  = refl

-- THE ORACLE DECIDES EVERY DOOR.  One query to the parity bit — the
-- bit the living step computes — decides every entanglement fibre of
-- the diagonal joint: fibre and answer are equivalent propositions.
-- No fibre is left undetermined; each is contracted or refuted by the
-- same uniform reading.
द्वार-निर्णयः : (ab : Bool × Bool)
             → fiber कर्ण-तुलना ab ≃ (fst (जीवन-पदम् ab) ≡ false)
द्वार-निर्णयः ab =
  propBiimpl→Equiv (कर्ण-तन्तुः-वाक्यम् ab) (isSetBool _ _)
    (λ (j , pth) → sym (cong (λ x → fst (जीवन-पदम् x)) pth) ∙ ⊕-अन्वयः j)
    (उत्तरम् ab)
  where
  उत्तरम् : (ab : Bool × Bool)
          → fst (जीवन-पदम् ab) ≡ false → fiber कर्ण-तुलना ab
  उत्तरम् (false , false) _ = (false , refl)
  उत्तरम् (true  , true)  _ = (true  , refl)
  उत्तरम् (false , true)  e = Empty.rec (true≢false e)
  उत्तरम् (true  , false) e = Empty.rec (true≢false e)

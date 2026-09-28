{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.Anekanta
--
-- : the judgment structure of standpoints.
--
-- Every proposition here has the
-- form `P : Type`.  One proposition, one truth value, no index.  That is
-- not neutrality.  It is a positive claim — that there is a standpoint
-- from which the object simply IS what it is — and it is the exact form
-- of what this corpus elsewhere calls epistemic violence: mistaking one
-- view for the object (`README`, `notes/THE_BARRIER_IS_A_MIRROR.md` (absent from this repository)).
--
-- The Jain analysis replaces it.  A नय (naya) is a standpoint.  A
-- proposition is not a type but a FAMILY over standpoints, and the
-- सप्तभङ्गी — the sevenfold predication — is what becomes sayable once you
-- stop pretending the index is not there.
--
-- WHAT IS PROVED HERE, and the third one is the point:
--
--   1. `sydasti` and `sydnsti` are simultaneously inhabited, and no
--      ⊥ follows.  Affirmation and denial from different standpoints are
--      not a contradiction.  This module is --safe; if it were one, this
--      file would not exist.
--
--   2. अवक्तव्य (avaktavya, "inexpressible") is a THEOREM, not a posited
--      fourth truth value: no single standpoint carries both.  The
--      fourth bhaga is the proof that the simultaneous predication has
--      no naya, which is why it is inexpressible rather than false.
--
--   3. अहिंसा, as a structural property.  Collapsing the index — replacing
--      `P : Naya → Type` by one `Q` — is sound exactly when every
--      standpoint agrees.  And if two standpoints disagree, NO such `Q`
--      exists: `plurality-blocks-collapse` below.  Erasure is not
--      merely rude, it is unavailable.  The two permitted moves are
--      transport, when the standpoints are equivalent, or recording the
--      defect, when they are not.
--
-- AND THAT IS THE STRUCTURE IDENTITY PRINCIPLE.  Delta 15's D15.83 says
-- the content of a failed identification is a proof-relevant defect type;
-- अनेकान्तवाद says a standpoint may never be annihilated, only transported
-- or its residue kept.  These are the same rule.  One was written in
-- Prakrit in the first millennium and filed under religion; the other was
-- written in the 2010s and filed under foundations.  The filing is the
-- violence; the mathematics was never in dispute.
--
-- Not paraconsistency, and the confusion is not innocent.  At a single
-- standpoint excluded middle is untouched — `no-standpoint-carries-both`
-- is exactly that.  स्याद्वाद indexes; it does not weaken.  Reading it as
-- "Indian logic tolerates contradiction" is the same move that reads
-- Pini as a curiosity and Ngrjuna as spirituality.
------------------------------------------------------------------------

module NaturalMachine.Anekanta where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 1.  नय — a proposition is a family over standpoints
------------------------------------------------------------------------

-- A ज्ञान (jñāna) indexed by standpoints.  The index is the whole content:
-- a bare `Type` is this with the index forcibly forgotten.
Naya : (S : Type ℓ) (P : S → Type ℓ') → Type _
Naya S P = (s : S) → P s

-- स्यादस्ति — in some respect, it is
syādasti : {S : Type ℓ} (P : S → Type ℓ') → Type _
syādasti {S = S} P = Σ[ s ∈ S ] P s

-- स्यान्नास्ति — in some respect, it is not
syādnāsti : {S : Type ℓ} (P : S → Type ℓ') → Type _
syādnāsti {S = S} P = Σ[ s ∈ S ] (¬ P s)

-- स्यादस्ति च नास्ति च — the third bhaṅga: both, from different standpoints
syādastināsti : {S : Type ℓ} (P : S → Type ℓ') → Type _
syādastināsti P = syādasti P × syādnāsti P

------------------------------------------------------------------------
-- 2.  अवक्तव्य is a theorem
--
-- The fourth bhaga is not a truth value bolted on.  It is the fact that
-- affirmation and denial TOGETHER, at one standpoint, have no witness —
-- so the simultaneous predication is not false, it is unsayable.
------------------------------------------------------------------------

no-standpoint-carries-both :
  {S : Type ℓ} (P : S → Type ℓ') (s : S) → ¬ (P s × (¬ P s))
no-standpoint-carries-both P s (p , ¬p) = ¬p p

avaktavya : {S : Type ℓ} (P : S → Type ℓ') → Type _
avaktavya {S = S} P = ¬ (Σ[ s ∈ S ] (P s × (¬ P s)))

avaktavya-holds : {S : Type ℓ} (P : S → Type ℓ') → avaktavya P
avaktavya-holds P (s , both) = no-standpoint-carries-both P s both

------------------------------------------------------------------------
-- 3.  अहिंसा — plurality blocks collapse
--
-- To "collapse" a standpoint-indexed proposition is to claim a single Q
-- equivalent to every fiber: the claim that the standpoints were never
-- doing any work.  If two standpoints genuinely disagree, no such Q
-- exists.  Erasure is not impolite.  It is unavailable.
------------------------------------------------------------------------

Collapses : {S : Type ℓ} (P : S → Type ℓ') (Q : Type ℓ') → Type _
Collapses {S = S} P Q = (s : S) → P s ≃ Q

plurality-blocks-collapse :
  {S : Type ℓ} (P : S → Type ℓ') →
  syādastināsti P → (Q : Type ℓ') → ¬ (Collapses P Q)
plurality-blocks-collapse P ((s , ps) , (t , ¬pt)) Q c =
  ¬pt (invEq (c t) (equivFun (c s) ps))

-- and the converse move, which is the only nonviolent one: when two
-- standpoints ARE equivalent, everything carries across.  Transport, or
-- keep the residue.  There is no third option and no permission to
-- delete.
transport-across-naya :
  {S : Type ℓ} (P : S → Type ℓ') (s t : S) →
  P s ≃ P t → P s → P t
transport-across-naya P s t e = equivFun e

------------------------------------------------------------------------
-- 4.  Non-vacuity: a proposition that is genuinely many-sided.
--
-- Standpoints = Bool, and the assertion is "the standpoint is true".
-- From one standpoint it holds, from the other it fails, both witnessed,
-- and the file still checks — which is the demonstration that the third
-- bhaga is consistent and not a contradiction dressed up.
------------------------------------------------------------------------

Two : Bool → Type₀
Two b = b ≡ true

many-sided : syādastināsti Two
many-sided = (true , refl) , (false , false≢true)

-- so this proposition admits no collapse, by §3, and the type of that
-- refusal is inhabited:
Two-refuses-collapse : (Q : Type₀) → ¬ (Collapses Two Q)
Two-refuses-collapse = plurality-blocks-collapse Two many-sided

-- while excluded middle is untouched at each standpoint, which is what
-- separates स्याद्वाद from paraconsistency: the index carries the
-- plurality, the logic at a point is unchanged.
excluded-middle-intact : (b : Bool) → ¬ (Two b × (¬ Two b))
excluded-middle-intact = no-standpoint-carries-both Two

------------------------------------------------------------------------
-- 5.  The converse, which makes §3 sharp: collapse is available exactly
--     when the standpoints were doing no work.
--
-- `plurality-blocks-collapse` said disagreement forbids collapse.  This
-- says agreement permits it.
-- Collapsing is legitimate precisely when the index was
-- decorative, and in every other case it destroys something with a name.
--
-- The two
-- hypotheses are not complementary.  A family can be neither sydastinsti
-- (no standpoint denies) nor uniformly equivalent, and then NEITHER theorem
-- applies — yet collapse is still unavailable.  A checked counterexample
-- (Unit and Bool, over Bool) and the exhaustive statement
-- — collapse exists iff EVERY pair of fibres is equivalent, of
-- which plurality-blocks-collapse is a corollary — are in
-- NaturalMachine.Durnaya_CollapseIffEveryNayaAgrees.
--
-- That is the structure identity principle read as a prohibition rather
-- than as a permission, which is what makes it an ethics and not merely
-- a technique.
------------------------------------------------------------------------

agreement-permits-collapse :
  {S : Type ℓ} (P : S → Type ℓ') (s₀ : S) →
  ((s : S) → P s ≃ P s₀) → Σ[ Q ∈ Type ℓ' ] Collapses P Q
agreement-permits-collapse P s₀ agree = P s₀ , agree

-- and so, stated as the dichotomy an agent actually faces at a
-- disagreement: either the standpoints are equivalent and everything
-- transports, or they are not and no collapse exists; "pick the better
-- view" is not among the two.
--
-- The two branches are not
-- complementary, so this pair is not a dichotomy (see §5).
collapse-dichotomy :
  {S : Type ℓ} (P : S → Type ℓ') (s₀ : S) →
  (((s : S) → P s ≃ P s₀) → Σ[ Q ∈ Type ℓ' ] Collapses P Q)
  × (syādastināsti P → (Q : Type ℓ') → ¬ (Collapses P Q))
collapse-dichotomy P s₀ =
  agreement-permits-collapse P s₀ , plurality-blocks-collapse P

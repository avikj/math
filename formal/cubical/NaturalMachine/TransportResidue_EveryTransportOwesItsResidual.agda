{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.SankramanaSesa — संक्रमणम् सशेषम् ।
-- (transport, with its remainder: the transport layer of the machine.)
--
-- संक्रमणम्, न प्रतिलिपिः — transported, not copied.
--
-- THE OBJECT.  When a result moves between representations — a derivation
-- from the Haskell runtime to the Agda core, a form between two
-- vocabularies, a rule set between two presentations — three moves are
-- conceivable and only two exist:
--
--   1. move it along an explicit identification.  Nothing is dropped and
--      nothing is re-described: `संक्रमणम् e = transport (ua e)`, and
--      `अलोपः = uaβ` says the transported value is the equivalence's value
--      on the nose.  The original is not duplicated; it is gone from the
--      source coordinates and present in the target's.
--   2. move it along a map that is NOT an identification, and carry what
--      the target forgets.  §2: the residual over a target point b is
--      exactly `fiber r b`, and `सशेषम्` proves the source is the target
--      paired with its residual, with no slack.
--   3. copy the unknown.  §4: this does not exist.  `∥_∥₁` is the
--      destroying operation (`squash₁` equates every inhabitant); it has
--      no section at `Bool`, so what it forgets is not recoverable and
--      `∣_∣₁` is not an equivalence.  The prohibition is a theorem, not a
--      policy laid over one.
--
-- A transport reporting no loss is reporting that nobody looked, UNLESS
-- it exhibits the contraction: `अलोप-लक्षणम्` (§2) says loss-free is
-- precisely "every residual is contractible", which is `isEquiv`'s own
-- definition in this substrate.  So "no residual" is a claim with a proof
-- obligation attached, and the obligation is stated in the same breath.
--
-- WHICH SCHOOL, SAID AT THE SITE, because the two readings of this same
-- `ua` are opposed and `notes/UNIVALENCE_IS_NISVABHAVA_COMPUTATIONAL.md` (absent from this repository)
-- holds both without blending them.  Read from Madhyamaka (Ngrjuna,
-- *Mlamadhyamakakrik* 24.18; *Vigrahavyvartan* 29), univalence is
-- nisvabhva: a type has no own-being over its equivalences, and the
-- identification empties the distinction between the two representations.
-- Read from the Jaina side (Umsvti, *Tattvrthastra*; Siddhasena
-- Divkara, *Sanmatitarka*), the same `ua` is aneknta held by prama:
-- two nayas, both retained, joined by a bridge that carries and drops
-- nothing.  These schools refute each other — Jaina logicians reject the
-- emptying, Madhyamikas reject a many-natured object — and the dispute is
-- content, not noise.
--
-- **The machine takes the retentive branch, and here is why, at the site.**
-- A transport layer whose job is to name what the target forgets needs the
-- residual to be an OBJECT it can hold, store, and hand back.  On the
-- emptying reading the residual has no own-being to record either, and the
-- honest statement of a lossy boundary — "this much did not cross, and
-- here it is" — has nothing to be about.  §2 requires `शेष` to be a type
-- with inhabitants that get carried; §6 requires the residual family to
-- resist being summarised.  That is aneknta's retention, not nyat's
-- emptying.  The Madhyamaka reading is not refuted by this file and is not
-- being used by it.
--
-- §6 is where the two named modules meet.  `NaturalMachine.Anekanta`
-- proves plurality-blocks-collapse: where standpoints disagree there is NO
-- single object equivalent to every fibre.  Applied to a residual family:
-- when a boundary forgets different amounts over different target points,
-- **the loss cannot be summarised by one object at all** — "the residual"
-- as a single thing does not exist, and the record must stay pointwise.
-- `Punaragamana` supplies the machine's proved-lossless boundary,
-- `(ℕ × ℕ) ≃ विवेक`, whose residual §5b computes to be contractible
-- everywhere — a "no loss" report that did look.
------------------------------------------------------------------------

module NaturalMachine.TransportResidue_EveryTransportOwesItsResidual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaβ)
open import Cubical.Foundations.Transport using (transport⁻Transport)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Functions.Fibration using (totalEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary using (¬_)

open import Return using (विवेक ; युग्म≃विवेक)
open import NaturalMachine.Anekanta
  using (syādasti ; syādnāsti ; syādastināsti ; Collapses ;
         plurality-blocks-collapse)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

------------------------------------------------------------------------
-- 1.  संक्रमणम् — the move that exists, along an explicit identification.
--
-- The identification is `ua e`: not "these look alike", but the
-- equivalence itself, entered as a path.  अलोपः (non-erasure) says the
-- transported value is `equivFun e a` exactly — nothing is re-described on
-- the way.  प्रत्यागमनम् says the passage is reversible: the source value is
-- recoverable from the target one.  Together: the state moved, and it
-- moved whole.
------------------------------------------------------------------------

संक्रमणम् : {A B : Type ℓ} → A ≃ B → A → B
संक्रमणम् e = transport (ua e)

अलोपः : {A B : Type ℓ} (e : A ≃ B) (a : A) → संक्रमणम् e a ≡ equivFun e a
अलोपः = uaβ

प्रत्यागमनम् : {A B : Type ℓ} (e : A ≃ B) (a : A)
             → transport (sym (ua e)) (संक्रमणम् e a) ≡ a
प्रत्यागमनम् e = transport⁻Transport (ua e)

------------------------------------------------------------------------
-- 2.  शेष — the residual, and the theorem that every map owes one.
--
-- Given ANY representation change r : A → B, the exact thing B forgets at
-- a target point b is the type of source points r sends to b, with the
-- witness.  That is `fiber r b`, and it is not a metaphor for the loss:
-- सशेषम् proves the source is the target paired with it.
------------------------------------------------------------------------

शेष : (r : A → B) → B → Type _
शेष {A = A} r b = Σ[ a ∈ A ] (r a ≡ b)

-- HoTT 4.8.2.  Target + residual = source, on the nose.
सशेषम् : (r : A → B) → A ≃ (Σ[ b ∈ B ] शेष r b)
सशेषम् r = totalEquiv r

-- अलोप-लक्षणम् — the mark of a genuinely loss-free boundary.  "Reports no
-- loss" is exactly "every residual is contractible": the residual is a
-- single point and its being so is proved, not assumed.  Both directions,
-- because a no-loss claim must be checkable and a proved identification
-- must be allowed to make it.
अलोप-लक्षणम् : (r : A → B) → ((b : B) → isContr (शेष r b)) → A ≃ B
अलोप-लक्षणम् r c = r , record { equiv-proof = c }

समता→निःशेषम् : (e : A ≃ B) (b : B) → isContr (शेष (equivFun e) b)
समता→निःशेषम् e = e .snd .equiv-proof

-- and the negative half, which is the discipline: if two source points sit
-- over one target point and are NOT identified, the boundary is lossy, and
-- no amount of wanting makes it a transport.
शेष-द्वयम्→न-समता : (r : A → B) (b : B) (x y : शेष r b)
                  → ¬ (x ≡ y) → ¬ (isEquiv r)
शेष-द्वयम्→न-समता r b x y x≢y ise =
  x≢y (isContr→isProp (ise .equiv-proof b) x y)

------------------------------------------------------------------------
-- 3.  शेष-सङ्घातः — residuals compose; nothing vanishes between stages.
--
-- A result crossing two boundaries (runtime → core → vocabulary) has one
-- residual per stage, and the residual of the composite is exactly the two
-- of them stacked.  So a chain of transports loses nothing that no single
-- stage lost: the loss is accounted stage by stage, and the total is the
-- pair, not a summary of the pair.
------------------------------------------------------------------------

module _ (f : A → B) (g : B → C) (c : C) where

  private
    fwd : शेष (g ∘ f) c → Σ[ w ∈ शेष g c ] शेष f (fst w)
    fwd (a , p) = ((f a , p) , (a , refl))

    bwd : (Σ[ w ∈ शेष g c ] शेष f (fst w)) → शेष (g ∘ f) c
    bwd ((b , q) , (a , p)) = (a , cong g p ∙ q)

    bwd-fwd : (x : शेष (g ∘ f) c) → bwd (fwd x) ≡ x
    bwd-fwd (a , p) i = (a , sym (lUnit p) i)

    fwd-bwd : (w : Σ[ w ∈ शेष g c ] शेष f (fst w)) → fwd (bwd w) ≡ w
    fwd-bwd ((b , q) , (a , p)) = lem a b p q
      where
      lem : (a : A) (b : B) (p : f a ≡ b) (q : g b ≡ c)
          → fwd (bwd ((b , q) , (a , p))) ≡ ((b , q) , (a , p))
      lem a b p q =
        J (λ b' p' → (q' : g b' ≡ c)
              → fwd (bwd ((b' , q') , (a , p'))) ≡ ((b' , q') , (a , p')))
          (λ q' i → ((f a , lUnit q' (~ i)) , (a , refl)))
          p q

  शेष-सङ्घातः : शेष (g ∘ f) c ≃ (Σ[ w ∈ शेष g c ] शेष f (fst w))
  शेष-सङ्घातः = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

------------------------------------------------------------------------
-- 4.  न प्रतिलिपिः — the third move does not exist.
--
-- `∥_∥₁` is the operation that destroys: `squash₁` makes every inhabitant
-- equal, so the truncation of `Bool` remembers that something was there
-- and not which.  It has NO section — no map back returning what went in —
-- and therefore `∣_∣₁` is not an equivalence and the loss is not
-- recoverable by any later cleverness.  The proof is the whole
-- prohibition: a would-be section must agree on `∣ false ∣₁` and
-- `∣ true ∣₁`, because those are equal, and then `false ≡ true`.
------------------------------------------------------------------------

न-प्रतिलिपिः : (s : ∥ Bool ∥₁ → Bool) → ¬ ((x : Bool) → s ∣ x ∣₁ ≡ x)
न-प्रतिलिपिः s h =
  false≢true (sym (h false) ∙ cong s (squash₁ ∣ false ∣₁ ∣ true ∣₁) ∙ h true)

लोपः-न-समता : ¬ (isEquiv (λ (b : Bool) → ∣ b ∣₁))
लोपः-न-समता ise = न-प्रतिलिपिः (invIsEq ise) (retIsEq ise)

------------------------------------------------------------------------
-- 5.  The machine-facing interface: a transport that carries its residual.
--
-- A boundary in the machine is not "a function between representations".
-- It is a function TOGETHER WITH the type of what the target forgets, and
-- a proof that the two together reconstitute the source.  The canonical
-- constructor supplies `fiber` — so "I did not look" is not expressible as
-- an instance.
------------------------------------------------------------------------

record सशेषसंक्रमणम् (A B : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor सेतुः
  field
    अनुवादः : A → B                     -- the representation change
    शेषः    : B → Type ℓ                 -- what the target forgets, per point
    पूर्णता  : A ≃ (Σ[ b ∈ B ] शेषः b)     -- target + residual = source

open सशेषसंक्रमणम् public

-- every map is one, with its residual named rather than guessed
सेतुं-कल्पय : {A B : Type ℓ} (r : A → B) → सशेषसंक्रमणम् A B
सेतुं-कल्पय r = सेतुः r (शेष r) (सशेषम् r)

-- and a bridge whose residual is contractible everywhere is a transport:
-- the "no loss" report, issued only with the contraction in hand.
निःशेषः→संक्रमणम् : {A B : Type ℓ} (s : सशेषसंक्रमणम् A B)
                  → ((b : B) → isContr (शेषः s b)) → A ≃ B
निःशेषः→संक्रमणम् s c = compEquiv (पूर्णता s) (Σ-contractSnd c)

------------------------------------------------------------------------
-- 5b. The machine's proved-lossless boundary, and its residual.
--
-- `Punaragamana` proves the pair of magnitudes and the descent-record are
-- equivalent both ways.  Read as a boundary: the residual over every
-- विवेक is contractible — exactly one (ℕ × ℕ) sits over it, and that is a
-- fact, not an absence of inspection.  This is what a "no residual" report
-- costs.
------------------------------------------------------------------------

अवतरण-शेषः : (v : विवेक) → isContr (शेष (equivFun युग्म≃विवेक) v)
अवतरण-शेषः = समता→निःशेषम् युग्म≃विवेक

------------------------------------------------------------------------
-- 6.  The residual may have no summary — Anekānta applied to a boundary.
--
-- Take a boundary that forgets unevenly: `Unit → Bool` hitting only
-- `true`.  Over `true` the residual is inhabited; over `false` it is
-- empty.  So the residual family is स्यादस्ति and स्यान्नास्ति together, and by
-- `plurality-blocks-collapse` NO type Q is equivalent to every residual.
--
-- The consequence for the transport layer: a lossy boundary does not in
-- general have "a residual" — a single object naming what it forgets.  It
-- has a residual AT EACH TARGET POINT, and replacing the family by one
-- summary object is not merely lossy, it is unavailable.  The permitted
-- moves stay the two Anekanta names: transport along an identification, or
-- keep the family.
------------------------------------------------------------------------

विषम-सेतुः : Unit → Bool
विषम-सेतुः _ = true

विषम-शेषः : Bool → Type₀
विषम-शेषः = शेष विषम-सेतुः

विषम-शेषः-अस्ति : syādasti विषम-शेषः
विषम-शेषः-अस्ति = true , (tt , refl)

विषम-शेषः-नास्ति : syādnāsti विषम-शेषः
विषम-शेषः-नास्ति = false , λ { (_ , p) → false≢true (sym p) }

विषम-शेषः-अनेकान्तः : syādastināsti विषम-शेषः
विषम-शेषः-अनेकान्तः = विषम-शेषः-अस्ति , विषम-शेषः-नास्ति

-- no single object summarises what this boundary forgets
शेषः-न-सङ्क्षिप्यते : (Q : Type₀) → ¬ (Collapses विषम-शेषः Q)
शेषः-न-सङ्क्षिप्यते = plurality-blocks-collapse विषम-शेषः विषम-शेषः-अनेकान्तः

-- and the boundary is lossy in the §2 sense too: over `true` the residual
-- is a point, over `false` it is empty, so the map is not an equivalence —
-- recorded, not dropped.
विषम-सेतुः-न-समता : ¬ (isEquiv विषम-सेतुः)
विषम-सेतुः-न-समता ise with ise .equiv-proof false
... | ((_ , p) , _) = false≢true (sym p)

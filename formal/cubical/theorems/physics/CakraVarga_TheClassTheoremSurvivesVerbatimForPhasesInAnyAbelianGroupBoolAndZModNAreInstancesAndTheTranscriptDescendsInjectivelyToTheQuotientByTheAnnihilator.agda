{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- CakraVarga — the class theorem survives verbatim for phases in any
-- abelian group; Bool and ℤ/n are instances; the transcript descends
-- injectively to the quotient by the annihilator.
--
-- SOURCE.  `notes/CHARGE_EXTRACTION_SHOULD_BE_CYCLIC.md` (absent from this repository) (branch main),
-- §(b), verbatim:
--
--   - `GaugeOrbitClasses.agda` generalizes by replacing $\mathrm{Bool}$-valued
--     signs with $\mathbb Z/n$-valued phases; the class theorem (fibres = cosets of
--     the annihilator) is a general finite-abelian-group statement and should
--     survive verbatim. **This is a concrete, small, and checkable Agda `PROVE`
--     item**, and it would put the aliasing theorem in the `--safe` lane.
--
-- and its audit table, row 11, verbatim:
--
--   | 11 | `formal/cubical/NaturalMachine/GaugeOrbitClasses.agda` | `val-⋆`:
--   $n\mapsto(\tau\mapsto\mathrm{val}\,\tau\,n)$ is a **character** of $G$;
--   class theorem | **CYCLIC** | **already optimal**, and is the Agda-lane
--   aliasing theorem (§1.4.3). $G=(\mathbb N\to\mathrm{Bool})$ is an
--   elementary abelian $2$-group — a product of $n=2$ cyclic factors — so
--   "general $n$" here means going to $\mathbb Z/n$-valued signs, not merely
--   more $\mathbb Z/2$ places. |
--
-- (The note's path `NaturalMachine/GaugeOrbitClasses.agda` is the module
-- `GaugeOrbitClasses` of this library, at `theorems/physics/`.)
--
--
-- WHAT IS PROVED
--
-- The note's PROVE item, taken at its word "should survive verbatim".
-- `GaugeOrbitClasses` is re-run with the value group Bool = {±1} replaced
-- by an ARBITRARY abelian group A (Cubical.Algebra.AbGroup), written
-- multiplicatively below (⊗, 𝟙, inv).  Every proof of the original goes
-- through with the four Bool case-analyses (`shuffle`, `·-self`, `·-not`,
-- `·-unit-r`) replaced by the group axioms — that is the whole check.
-- The one place the Bool proof used exponent 2 (the group difference of
-- σ' and σ is σ' ⋆ σ, "no inversion appears") is the one place the
-- general proof genuinely differs: the difference is σ' ⋆ σ⁻¹, and the
-- annihilator's closure under INVERSE (`ann-inv`) replaces
-- `ann-self-inverse`.
--
--   §1  Phases = ℕ → ⟨A⟩ with the pointwise group; valᴬ; obsᴬ.
--       val-⋆ : valᴬ (τ ⋆ σ) n ≡ valᴬ τ n ⊗ valᴬ σ n         (T1)
--       val-⁻¹: valᴬ (σ ⁻¹) n ≡ inv (valᴬ σ n)
--   §2  AllNeutral τ qs  (qs^⊥), and it is a subgroup:
--       ann-unit, ann-mul, ann-inv.                            (T2)
--   §3  obs-agree⋆, no-decision⋆, charged-visible — blindness and
--       visibility for an arbitrary phase element.
--   §4  THE CLASS THEOREM, verbatim:                           (T3)
--       classes-⇐ : AllNeutral (σ' ⋆ σ ⁻¹) qs → obsᴬ σ qs ≡ obsᴬ σ' qs
--       classes-⇒ : obsᴬ σ qs ≡ obsᴬ σ' qs → AllNeutral (σ' ⋆ σ ⁻¹) qs
--   §5  THE QUOTIENT: Coset qs is a prop-valued equivalence relation,
--       Classes qs = Phases / Coset qs, and the transcript map factors
--       through it as obs/ with obs/ [σ] ≡ obsᴬ σ qs (refl) and
--       obs/ INJECTIVE — so the observable classes are indexed by
--       G/qs^⊥ exactly (`classes-as-quotient`).                (T5)
--   §6  A = Bool with `ParitySeparator._·_` (`BoolAb`): valᴬ, obsᴬ and
--       AllNeutral agree with the originals (`val-Bool`, `obs-Bool`,
--       `ann-Bool→/←`), the difference σ' ⋆ σ⁻¹ IS σ' ⋆ σ (refl), and
--       the general theorem, specialised, is the original theorem —
--       including that the two proofs are equal (`recover-⇒-is-original`,
--       via the propositionality of AllNeutral).                (T4)
--   §7  A = ℤ/3 (`ℤAbGroup/ 3`): the single-prime phase shift τω has
--       valᴬ τω [p₀] = ω ≠ 𝟙, τω ⋆ τω has ω² ≠ 𝟙, and τω³ ∈ [p₀]^⊥;
--       the transcripts of τ₊, τω, τω⋆τω on the single query [p₀] are
--       pairwise distinct — THREE observable classes on ONE query.
--       In the Bool theory: every τ ⋆ τ lies in every annihilator
--       (`bool-square-neutral`, from `GaugeOrbitClasses.ann-self-inverse`)
--       and any three sign assignments collide on any one query
--       (`bool-one-query-collide`).  The third phase is visible; the
--       Bool theory cannot express it.                          (T4)
--
--
-- WHAT IS NOT PROVED
--
-- * Nothing about Ramanujan sums, cyclotomic traces, or the DFT
--   projector Π_j = (1/n) Σ_ν ω^{-jν} V_ν of the note's §1; nothing
--   about its conditioning constants κ.  This module is only the
--   note's item (b): the class theorem over a general abelian group.
-- * The value group is an arbitrary AbGroup; finiteness is never used
--   and never assumed.  "Finite" in the note's sentence is a remark on
--   the intended instances, not a hypothesis of the theorem.
-- * `GaugeOrbitClasses` §4's constructed separator (`charge⇒separator⋆`)
--   is not generalised: it needs a decision procedure comparing group
--   elements, i.e. decidable equality on A, which an arbitrary AbGroup
--   does not carry.  `charged-visible` (the transcript entries DIFFER)
--   is proved; turning "differ" into a Bool-valued `decide` is the
--   instance's business.  For ℤ/3 the §7 disequalities are the witness.
-- * `GaugeOrbitClasses` §7 (squares are neutral) is specific to
--   exponent 2 and is not carried over; its general form would be
--   "n-th powers are neutral for ℤ/n", not stated here.
-- * No claim about `ChargeCriterion`, Goldbach, twin primes, W3/W4.
--
-- No holes, no postulates, --safe.
------------------------------------------------------------------------

module CakraVarga_TheClassTheoremSurvivesVerbatimForPhasesInAnyAbelianGroupBoolAndZModNAreInstancesAndTheTranscriptDescendsInjectivelyToTheQuotientByTheAnnihilator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp× ; isPropΠ)
open import Cubical.Foundations.Isomorphism using (Iso ; iso)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt* ; isPropUnit*)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; snotz ; injSuc)
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map ; isOfHLevelList)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Fin using (Fin ; fzero ; fone ; fsuc ; toℕ-injective)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/ ; squash/)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.AbGroup.Instances.IntMod using (ℤAbGroup/_)

open import ParitySeparator
  using (Number ; Signs ; val ; obs ; one-prime ; _·_ ; ·-assoc ; ·-comm)
import GaugeOrbitClasses as GOC

open BinaryRelation

------------------------------------------------------------------------
-- The theory, for an arbitrary abelian group of phases.
------------------------------------------------------------------------

module Phase {ℓ : Level} (A : AbGroup ℓ) where

  open AbGroupStr (snd A) public
    renaming ( _+_    to _⊗_
             ; 0g     to 𝟙
             ; -_     to inv
             ; +Assoc to ⊗-assoc
             ; +IdR   to ⊗-unit-r
             ; +IdL   to ⊗-unit-l
             ; +InvR  to ⊗-inv-r
             ; +InvL  to ⊗-inv-l
             ; +Comm  to ⊗-comm )
  open GroupTheory (AbGroup→Group A) using (inv1g ; ·CancelL ; ·CancelR)

  ----------------------------------------------------------------------
  -- §1  Phase assignments, the pointwise group, the value map, and the
  --     character law.  `GaugeOrbitClasses` §1–§2 with Bool → ⟨A⟩.
  ----------------------------------------------------------------------

  Phases : Type ℓ
  Phases = ℕ → ⟨ A ⟩

  infixr 5 _⋆_
  infix  8 _⁻¹

  _⋆_ : Phases → Phases → Phases
  (τ ⋆ σ) p = τ p ⊗ σ p

  _⁻¹ : Phases → Phases
  (σ ⁻¹) p = inv (σ p)

  τ₊ : Phases
  τ₊ _ = 𝟙

  -- `ParitySeparator.val` verbatim: the product of the phases at the
  -- prime indices, with multiplicity.
  valᴬ : Phases → Number → ⟨ A ⟩
  valᴬ σ []       = 𝟙
  valᴬ σ (p ∷ ns) = σ p ⊗ valᴬ σ ns

  -- `ParitySeparator.obs` verbatim.
  obsᴬ : Phases → List Number → List ⟨ A ⟩
  obsᴬ σ qs = map (valᴬ σ) qs

  -- The abelian shuffle — the original's sixteen `refl`s, now derived
  -- from associativity and commutativity, which is all they ever used.
  shuffle : (a b c d : ⟨ A ⟩) → (a ⊗ b) ⊗ (c ⊗ d) ≡ (a ⊗ c) ⊗ (b ⊗ d)
  shuffle a b c d =
      sym (⊗-assoc a b (c ⊗ d))
    ∙ cong (a ⊗_) ( ⊗-assoc b c d
                  ∙ cong (_⊗ d) (⊗-comm b c)
                  ∙ sym (⊗-assoc c b d) )
    ∙ ⊗-assoc a c (b ⊗ d)

  -- (T1) THE CHARACTER LAW.  n ↦ (τ ↦ valᴬ τ n) is a homomorphism
  -- (ℕ → A, ⋆) → A.  Proof text identical to `GaugeOrbitClasses.val-⋆`.
  val-⋆ : (τ σ : Phases) (n : Number)
        → valᴬ (τ ⋆ σ) n ≡ valᴬ τ n ⊗ valᴬ σ n
  val-⋆ τ σ []       = sym (⊗-unit-r 𝟙)
  val-⋆ τ σ (p ∷ ns) =
      cong ((τ p ⊗ σ p) ⊗_) (val-⋆ τ σ ns)
    ∙ shuffle (τ p) (σ p) (valᴬ τ ns) (valᴬ σ ns)

  -- Inversion distributes over ⊗ (abelian), hence commutes with valᴬ.
  -- This is the lemma that has no Bool ancestor: there, inv = id.
  inv-⊗ : (a b : ⟨ A ⟩) → inv (a ⊗ b) ≡ inv a ⊗ inv b
  inv-⊗ a b = ·CancelL (a ⊗ b)
    ( ⊗-inv-r (a ⊗ b)
    ∙ sym ( shuffle a b (inv a) (inv b)
          ∙ cong₂ _⊗_ (⊗-inv-r a) (⊗-inv-r b)
          ∙ ⊗-unit-r 𝟙 ) )

  val-⁻¹ : (σ : Phases) (n : Number) → valᴬ (σ ⁻¹) n ≡ inv (valᴬ σ n)
  val-⁻¹ σ []       = sym inv1g
  val-⁻¹ σ (p ∷ ns) =
      cong (inv (σ p) ⊗_) (val-⁻¹ σ ns)
    ∙ sym (inv-⊗ (σ p) (valᴬ σ ns))

  val-τ₊ : (n : Number) → valᴬ τ₊ n ≡ 𝟙
  val-τ₊ []       = refl
  val-τ₊ (p ∷ ns) = cong (𝟙 ⊗_) (val-τ₊ ns) ∙ ⊗-unit-r 𝟙

  ----------------------------------------------------------------------
  -- §2  The annihilator qs^⊥ and that it is a subgroup.
  --     `GaugeOrbitClasses` §3; `ann-self-inverse` becomes `ann-inv`.
  ----------------------------------------------------------------------

  AllNeutral : Phases → List Number → Type ℓ
  AllNeutral τ []       = Unit*
  AllNeutral τ (n ∷ qs) = (valᴬ τ n ≡ 𝟙) × AllNeutral τ qs

  -- Membership in qs^⊥ is a proposition (A is a set).
  isPropAllNeutral : (τ : Phases) (qs : List Number) → isProp (AllNeutral τ qs)
  isPropAllNeutral τ []       = isPropUnit*
  isPropAllNeutral τ (n ∷ qs) = isProp× (is-set _ _) (isPropAllNeutral τ qs)

  -- (T2) qs^⊥ is a subgroup.
  ann-unit : (qs : List Number) → AllNeutral τ₊ qs
  ann-unit []       = tt*
  ann-unit (n ∷ qs) = val-τ₊ n , ann-unit qs

  ann-mul : (τ ρ : Phases) (qs : List Number)
          → AllNeutral τ qs → AllNeutral ρ qs → AllNeutral (τ ⋆ ρ) qs
  ann-mul τ ρ []       _        _        = tt*
  ann-mul τ ρ (n ∷ qs) (e , es) (f , fs) =
      (val-⋆ τ ρ n ∙ cong₂ _⊗_ e f ∙ ⊗-unit-r 𝟙)
    , ann-mul τ ρ qs es fs

  ann-inv : (τ : Phases) (qs : List Number)
          → AllNeutral τ qs → AllNeutral (τ ⁻¹) qs
  ann-inv τ []       _        = tt*
  ann-inv τ (n ∷ qs) (e , es) =
      (val-⁻¹ τ n ∙ cong inv e ∙ inv1g)
    , ann-inv τ qs es

  ----------------------------------------------------------------------
  -- §3  Blindness and visibility for an arbitrary phase element.
  --     `GaugeOrbitClasses` §4, minus the constructed Bool decider.
  ----------------------------------------------------------------------

  neutral-invisible : (τ σ : Phases) (n : Number)
                    → valᴬ τ n ≡ 𝟙 → valᴬ (τ ⋆ σ) n ≡ valᴬ σ n
  neutral-invisible τ σ n e =
    val-⋆ τ σ n ∙ cong (_⊗ valᴬ σ n) e ∙ ⊗-unit-l (valᴬ σ n)

  -- A charged element CHANGES the entry: the general form of
  -- `charged-visible`, whose Bool conclusion `≡ not (val σ n)` is the
  -- only way two elements of {±1} can differ.
  charged-visible : (τ σ : Phases) (n : Number)
                  → ¬ (valᴬ τ n ≡ 𝟙) → ¬ (valᴬ (τ ⋆ σ) n ≡ valᴬ σ n)
  charged-visible τ σ n c e =
    c (·CancelR (valᴬ σ n) (sym (val-⋆ τ σ n) ∙ e ∙ sym (⊗-unit-l (valᴬ σ n))))

  obs-agree⋆ : (τ σ : Phases) (qs : List Number)
             → AllNeutral τ qs → obsᴬ σ qs ≡ obsᴬ (τ ⋆ σ) qs
  obs-agree⋆ τ σ []       _          = refl
  obs-agree⋆ τ σ (n ∷ qs) (e , rest) =
    cong₂ _∷_ (sym (neutral-invisible τ σ n e)) (obs-agree⋆ τ σ qs rest)

  no-decision⋆ : (τ σ : Phases) (qs : List Number) → AllNeutral τ qs
               → (decide : List ⟨ A ⟩ → Bool)
               → ¬ ((decide (obsᴬ σ qs) ≡ true) × (decide (obsᴬ (τ ⋆ σ) qs) ≡ false))
  no-decision⋆ τ σ qs all decide (yes , no) =
    true≢false (sym yes ∙ cong decide (obs-agree⋆ τ σ qs all) ∙ no)

  ----------------------------------------------------------------------
  -- §4  THE CLASS THEOREM — (T3).
  --
  -- Two phase assignments have the same transcript on qs exactly when
  -- they differ by an element of qs^⊥.  The group difference is now
  -- σ' ⋆ σ ⁻¹; at Bool, where inv = id, it is the original's σ' ⋆ σ.
  ----------------------------------------------------------------------

  -- Translating σ by the difference lands on σ'.
  cancel : (σ σ' : Phases) → ((σ' ⋆ σ ⁻¹) ⋆ σ) ≡ σ'
  cancel σ σ' = funExt (λ p →
      sym (⊗-assoc (σ' p) (inv (σ p)) (σ p))
    ∙ cong (σ' p ⊗_) (⊗-inv-l (σ p))
    ∙ ⊗-unit-r (σ' p))

  hd : List ⟨ A ⟩ → ⟨ A ⟩
  hd []      = 𝟙
  hd (a ∷ _) = a

  tl : List ⟨ A ⟩ → List ⟨ A ⟩
  tl []       = []
  tl (_ ∷ as) = as

  classes-⇐ : (qs : List Number) (σ σ' : Phases)
            → AllNeutral (σ' ⋆ σ ⁻¹) qs → obsᴬ σ qs ≡ obsᴬ σ' qs
  classes-⇐ qs σ σ' h =
      obs-agree⋆ (σ' ⋆ σ ⁻¹) σ qs h
    ∙ cong (λ ρ → obsᴬ ρ qs) (cancel σ σ')

  classes-⇒ : (qs : List Number) (σ σ' : Phases)
            → obsᴬ σ qs ≡ obsᴬ σ' qs → AllNeutral (σ' ⋆ σ ⁻¹) qs
  classes-⇒ []       σ σ' e = tt*
  classes-⇒ (n ∷ qs) σ σ' e =
      ( val-⋆ σ' (σ ⁻¹) n
      ∙ cong (valᴬ σ' n ⊗_) (val-⁻¹ σ n)
      ∙ cong (λ z → valᴬ σ' n ⊗ inv z) (cong hd e)
      ∙ ⊗-inv-r (valᴬ σ' n) )
    , classes-⇒ qs σ σ' (cong tl e)

  ----------------------------------------------------------------------
  -- §5  THE QUOTIENT — (T5).
  --
  -- The note's counting remark: the classes are indexed by G/qs^⊥.
  -- The coset relation is a prop-valued equivalence relation (all three
  -- laws are corollaries of §4, since "same transcript" trivially is
  -- one), the transcript map descends to the set quotient, and the
  -- descended map is injective.  So the fibres of obsᴬ (− , qs) are in
  -- bijection with Phases / Coset qs — no more, no less.
  ----------------------------------------------------------------------

  Coset : List Number → Phases → Phases → Type ℓ
  Coset qs σ σ' = AllNeutral (σ' ⋆ σ ⁻¹) qs

  Coset-isPropValued : (qs : List Number) → isPropValued (Coset qs)
  Coset-isPropValued qs σ σ' = isPropAllNeutral (σ' ⋆ σ ⁻¹) qs

  Coset-isEquivRel : (qs : List Number) → isEquivRel (Coset qs)
  Coset-isEquivRel qs = equivRel
    (λ σ → classes-⇒ qs σ σ refl)
    (λ σ σ' r → classes-⇒ qs σ' σ (sym (classes-⇐ qs σ σ' r)))
    (λ σ σ' σ'' r s →
       classes-⇒ qs σ σ'' (classes-⇐ qs σ σ' r ∙ classes-⇐ qs σ' σ'' s))

  Classes : List Number → Type ℓ
  Classes qs = Phases / Coset qs

  isSetTranscripts : isSet (List ⟨ A ⟩)
  isSetTranscripts = isOfHLevelList 0 is-set

  -- The transcript map factors through the quotient …
  obs/ : (qs : List Number) → Classes qs → List ⟨ A ⟩
  obs/ qs = SQ.rec isSetTranscripts (λ σ → obsᴬ σ qs) (classes-⇐ qs)

  obs/-factors : (qs : List Number) (σ : Phases) → obs/ qs [ σ ] ≡ obsᴬ σ qs
  obs/-factors qs σ = refl

  -- … injectively.
  obs/-injective : (qs : List Number) (x y : Classes qs)
                 → obs/ qs x ≡ obs/ qs y → x ≡ y
  obs/-injective qs =
    SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
                 (λ σ σ' e → eq/ σ σ' (classes-⇒ qs σ σ' e))

  -- Equivalently: equality of classes IS equality of transcripts.
  classes-as-quotient : (qs : List Number) (σ σ' : Phases)
                      → Iso ([ σ ] ≡ [ σ' ]) (obsᴬ σ qs ≡ obsᴬ σ' qs)
  classes-as-quotient qs σ σ' = iso
    (cong (obs/ qs))
    (λ e → eq/ σ σ' (classes-⇒ qs σ σ' e))
    (λ e → isSetTranscripts _ _ _ _)
    (λ p → squash/ _ _ _ _)

------------------------------------------------------------------------
-- §6  INSTANCE Bool — (T4).  `ParitySeparator._·_` on Bool is an abelian
--     group with unit true and inv = id; `GaugeOrbitClasses` is the
--     theory of §1–§5 at this instance, on the nose.
------------------------------------------------------------------------

BoolAb : AbGroup ℓ-zero
BoolAb = makeAbGroup true _·_ (λ b → b) isSetBool
  (λ a b c → sym (·-assoc a b c))
  GOC.·-unit-r
  GOC.·-self
  ·-comm

module 𝔹 = Phase BoolAb

-- The specialised value, transcript and annihilator are the originals.
val-Bool : (σ : Signs) (n : Number) → 𝔹.valᴬ σ n ≡ val σ n
val-Bool σ []       = refl
val-Bool σ (p ∷ ns) = cong (σ p ·_) (val-Bool σ ns)

obs-Bool : (σ : Signs) (qs : List Number) → 𝔹.obsᴬ σ qs ≡ obs σ qs
obs-Bool σ qs = cong (λ f → map f qs) (funExt (val-Bool σ))

ann-Bool→ : (τ : Signs) (qs : List Number)
          → 𝔹.AllNeutral τ qs → GOC.AllNeutral τ qs
ann-Bool→ τ []       _        = tt
ann-Bool→ τ (n ∷ qs) (e , es) = (sym (val-Bool τ n) ∙ e) , ann-Bool→ τ qs es

ann-Bool← : (τ : Signs) (qs : List Number)
          → GOC.AllNeutral τ qs → 𝔹.AllNeutral τ qs
ann-Bool← τ []       _        = tt*
ann-Bool← τ (n ∷ qs) (e , es) = (val-Bool τ n ∙ e) , ann-Bool← τ qs es

-- The general difference σ' ⋆ σ⁻¹ is, at Bool, the original's σ' ⋆ σ:
-- definitionally, because inv = id.
diff-Bool : (σ σ' : Signs) → (σ' 𝔹.⋆ σ 𝔹.⁻¹) ≡ (σ' GOC.⋆ σ)
diff-Bool σ σ' = refl

-- THE ORIGINAL CLASS THEOREM, recovered from the general one.  Same
-- types as `GaugeOrbitClasses.classes-⇒` / `classes-⇐`.
recover-⇒ : (qs : List Number) (σ σ' : Signs)
          → obs σ qs ≡ obs σ' qs → GOC.AllNeutral (σ' GOC.⋆ σ) qs
recover-⇒ qs σ σ' e =
  ann-Bool→ (σ' GOC.⋆ σ) qs
    (𝔹.classes-⇒ qs σ σ' (obs-Bool σ qs ∙ e ∙ sym (obs-Bool σ' qs)))

recover-⇐ : (qs : List Number) (σ σ' : Signs)
          → GOC.AllNeutral (σ' GOC.⋆ σ) qs → obs σ qs ≡ obs σ' qs
recover-⇐ qs σ σ' h =
    sym (obs-Bool σ qs)
  ∙ 𝔹.classes-⇐ qs σ σ' (ann-Bool← (σ' GOC.⋆ σ) qs h)
  ∙ obs-Bool σ' qs

-- …and the recovered proofs ARE the original proofs: both live in a
-- proposition (resp. in a set of transcripts).
isPropGOCAllNeutral : (τ : Signs) (qs : List Number) → isProp (GOC.AllNeutral τ qs)
isPropGOCAllNeutral τ []       = λ _ _ → refl
isPropGOCAllNeutral τ (n ∷ qs) = isProp× (isSetBool _ _) (isPropGOCAllNeutral τ qs)

recover-⇒-is-original : (qs : List Number) (σ σ' : Signs) (e : obs σ qs ≡ obs σ' qs)
                      → recover-⇒ qs σ σ' e ≡ GOC.classes-⇒ qs σ σ' e
recover-⇒-is-original qs σ σ' e = isPropGOCAllNeutral _ qs _ _

recover-⇐-is-original : (qs : List Number) (σ σ' : Signs)
                        (h : GOC.AllNeutral (σ' GOC.⋆ σ) qs)
                      → recover-⇐ qs σ σ' h ≡ GOC.classes-⇐ qs σ σ' h
recover-⇐-is-original qs σ σ' h = isOfHLevelList 0 isSetBool _ _ _ _

-- The character law at Bool is `GaugeOrbitClasses.val-⋆`, up to the
-- same bridge.
val-⋆-Bool : (τ σ : Signs) (n : Number) → val (τ GOC.⋆ σ) n ≡ val τ n · val σ n
val-⋆-Bool τ σ n =
    sym (val-Bool (τ GOC.⋆ σ) n)
  ∙ 𝔹.val-⋆ τ σ n
  ∙ cong₂ _·_ (val-Bool τ n) (val-Bool σ n)

------------------------------------------------------------------------
-- §7  INSTANCE ℤ/3 — the control (T4).  A third phase is visible.
--
-- ω = 1 ∈ ℤ/3 (written additively in the library: Fin 3 under +ₘ, unit
-- fzero).  τω puts ω at the prime p₀ and 𝟙 elsewhere.  On the single
-- query [p₀]:
--     valᴬ τω        [p₀] = ω     ≠ 𝟙
--     valᴬ (τω ⋆ τω) [p₀] = ω²    ≠ 𝟙
--     valᴬ (τω³)     [p₀] = ω³    = 𝟙
-- so τω has order 3 in G/[p₀]^⊥, and the three transcripts of
-- τ₊, τω, τω ⋆ τω are pairwise distinct: THREE classes on ONE query.
-- The Bool theory has exponent 2 (every τ ⋆ τ is in every annihilator)
-- and at most two transcripts on one query (pigeonhole, below).
------------------------------------------------------------------------

ℤ/3 : AbGroup ℓ-zero
ℤ/3 = ℤAbGroup/ 3

module ℤ₃ = Phase ℤ/3

ω : Fin 3
ω = fone

-- the phase shift by ω at the single prime p₀ = 0
τω : ℤ₃.Phases
τω zero    = ω
τω (suc _) = fzero

-- the single-query list [p₀]
qω : List Number
qω = one-prime ∷ []

-- The three values, by computation in Fin 3 (arithmetic is by refl).
τω-value : ℤ₃.valᴬ τω one-prime ≡ ω
τω-value = toℕ-injective refl

τω²-value : ℤ₃.valᴬ (τω ℤ₃.⋆ τω) one-prime ≡ fsuc fone
τω²-value = toℕ-injective refl

τω³-neutral : ℤ₃.AllNeutral (τω ℤ₃.⋆ τω ℤ₃.⋆ τω) qω
τω³-neutral = toℕ-injective refl , tt*

-- ω ≠ 𝟙 and ω² ≠ 𝟙: τω and τω ⋆ τω are charged for [p₀].
τω-charged : ¬ (ℤ₃.valᴬ τω one-prime ≡ ℤ₃.𝟙)
τω-charged e = snotz (cong fst e)

τω²-charged : ¬ (ℤ₃.valᴬ (τω ℤ₃.⋆ τω) one-prime ≡ ℤ₃.𝟙)
τω²-charged e = snotz (cong fst e)

-- An element whose square is NOT in the annihilator — impossible at Bool.
τω²-not-in-annihilator : ¬ (ℤ₃.AllNeutral (τω ℤ₃.⋆ τω) qω)
τω²-not-in-annihilator (e , _) = τω²-charged e

-- THREE pairwise distinct transcripts on the single query [p₀].
three-classes :
    (¬ (ℤ₃.obsᴬ ℤ₃.τ₊ qω ≡ ℤ₃.obsᴬ τω qω))
  × (¬ (ℤ₃.obsᴬ ℤ₃.τ₊ qω ≡ ℤ₃.obsᴬ (τω ℤ₃.⋆ τω) qω))
  × (¬ (ℤ₃.obsᴬ τω qω ≡ ℤ₃.obsᴬ (τω ℤ₃.⋆ τω) qω))
three-classes =
    (λ e → snotz (sym (cong (λ ℓ → fst (ℤ₃.hd ℓ)) e)))
  , (λ e → snotz (sym (cong (λ ℓ → fst (ℤ₃.hd ℓ)) e)))
  , (λ e → snotz (sym (injSuc (cong (λ ℓ → fst (ℤ₃.hd ℓ)) e))))

-- …and in the language of §5: the three classes are distinct.
three-classes/ :
    (¬ ([ ℤ₃.τ₊ ] ≡ [ τω ]))
  × (¬ ([ ℤ₃.τ₊ ] ≡ [ τω ℤ₃.⋆ τω ]))
  × (¬ ([ τω ] ≡ [ τω ℤ₃.⋆ τω ]))
three-classes/ =
    (λ p → fst three-classes (cong (ℤ₃.obs/ qω) p))
  , (λ p → fst (snd three-classes) (cong (ℤ₃.obs/ qω) p))
  , (λ p → snd (snd three-classes) (cong (ℤ₃.obs/ qω) p))

-- THE CONTRAST.  In the Bool theory:
-- (i) every square is in every annihilator (exponent 2), and
bool-square-neutral : (τ : Signs) (qs : List Number)
                    → GOC.AllNeutral (τ GOC.⋆ τ) qs
bool-square-neutral τ qs =
  subst (λ ρ → GOC.AllNeutral ρ qs) (sym (GOC.ann-self-inverse τ)) (GOC.ann-unit qs)

-- (ii) three sign assignments never have three distinct transcripts on
-- one query: {±1} has two elements.
pigeon : (a b c : Bool) → (a ≡ b) ⊎ ((a ≡ c) ⊎ (b ≡ c))
pigeon true  true  c     = inl refl
pigeon false false c     = inl refl
pigeon true  false true  = inr (inl refl)
pigeon false true  false = inr (inl refl)
pigeon true  false false = inr (inr refl)
pigeon false true  true  = inr (inr refl)

bool-one-query-collide : (σ₀ σ₁ σ₂ : Signs) (n : Number)
  →   (obs σ₀ (n ∷ []) ≡ obs σ₁ (n ∷ []))
    ⊎ ((obs σ₀ (n ∷ []) ≡ obs σ₂ (n ∷ [])) ⊎ (obs σ₁ (n ∷ []) ≡ obs σ₂ (n ∷ [])))
bool-one-query-collide σ₀ σ₁ σ₂ n with pigeon (val σ₀ n) (val σ₁ n) (val σ₂ n)
... | inl e       = inl (cong (_∷ []) e)
... | inr (inl e) = inr (inl (cong (_∷ []) e))
... | inr (inr e) = inr (inr (cong (_∷ []) e))

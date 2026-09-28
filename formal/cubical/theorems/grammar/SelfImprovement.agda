{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SelfImprovement
--
-- GENOTYPE / PHENOTYPE SEPARATION AS A CHECKED STATEMENT.
--
-- These are small statements.  Every proof below is a page of pattern
-- matching and none of them is deep.  Their value is not depth: it is that
-- contaminate identity", "fitness does not automatically transport",
-- "a gamed evaluator's observations are quarantinable without touching the
-- genotypes it scored" -- stops being prose that a reader must trust and
-- becomes a type the checker has accepted.  A slogan cannot be violated by
-- a definition; a theorem can, and then the file goes red.
--
-- Contents:
--
--   §1  Population    Genotype (identity a PARAMETER, no hashing faked),
--                     Environment, Evaluator, Evaluation, Store = List,
--                     and `Edit`: the grammar of store operations.
--   §2  identity-is-not-performance
--                     every evaluation surviving ANY sequence of store
--                     edits carries an identity that was already in the
--                     store or was written down in the edit.  No edit
--                     computes a genotype from scores.  Corollaries: the
--                     genotype index is fixed by re-scoring, and an edit
--                     that adds nothing invents no genotype.
--   §3  transport-needs-a-witness
--                     positive: a Bridge (Residual's sense) TOGETHER WITH
--                     an invariance hypothesis transports a faithful
--                     evaluation.  Sharp negative: the same rule with the
--                     Bridge and with observational agreement on a
--                     nonempty declared environment list, but WITHOUT the
--                     invariance hypothesis, is refuted -- a homometric
--                     pair with identical presentations, agreeing
--                     observations, and different scores.
--   §4  gamed-evaluator-is-quarantinable
--                     dropping one evaluator's evaluations keeps exactly
--                     the others, and invents no genotype.
--
-- WHICH ECOLOGY.md (absent from this repository) CLAIMS THIS COVERS
--
--   * "Genotype ≠ phenotype ... Performance must never contaminate
--     identity" (§ "The one early design decision")            -> §2.
--   * "an evaluation cites H_evaluator, so a gamed evaluator is
--     identifiable and its observations quarantinable WITHOUT touching the
--     genotypes it scored" (§ "Red Queen and Hyperagents")      -> §4.
--   * "fitness does not automatically transport ... requires a checked
--     equivalence ... plus a theorem or verified operator showing that the
--     evaluation is invariant" (§ "Trust correction")           -> §3, both
--     halves; the negative half is the checked form of "observation is not
--     isomorphism ... Homometric examples are the reason, not an edge
--     case".
--
-- Related checked work: `EvaluatorTransport` proves that
-- inverse precomposition is the UNIQUE evaluator transport conserving every
-- paired result along an equivalence.  That is the invariance law for a
-- moving evaluator; this module is about the store the results are kept in.
------------------------------------------------------------------------

module SelfImprovement where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots ; discreteℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; Discrete)

open import CostGeometry using (Presentation ; pres ; Edge ; edge)
open import Residual using (Bridge)
open import ChuAdvance using (Obs ; Agree)

------------------------------------------------------------------------
-- §0.  List membership, computed rather than indexed
------------------------------------------------------------------------

infix 4 _∈_

_∈_ : {A : Type₀} → A → List A → Type₀
x ∈ [] = ⊥
x ∈ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ ys)

∈-++-left : {A : Type₀} {x : A} (xs ys : List A) → x ∈ xs → x ∈ (xs ++ ys)
∈-++-left [] ys m = ⊥.rec m
∈-++-left (z ∷ zs) ys (inl p) = inl p
∈-++-left (z ∷ zs) ys (inr m) = inr (∈-++-left zs ys m)

∈-++-right : {A : Type₀} {x : A} (xs ys : List A) → x ∈ ys → x ∈ (xs ++ ys)
∈-++-right [] ys m = m
∈-++-right (z ∷ zs) ys m = inr (∈-++-right zs ys m)

∈-++-split : {A : Type₀} {x : A} (xs ys : List A)
           → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
∈-++-split [] ys m = inr m
∈-++-split (z ∷ zs) ys (inl p) = inl (inl p)
∈-++-split (z ∷ zs) ys (inr m) with ∈-++-split zs ys m
... | inl mL = inl (inr mL)
... | inr mR = inr mR

------------------------------------------------------------------------
-- §0'.  Reading a decision as a Bool, and back
------------------------------------------------------------------------

isYes : {A : Type₀} → Dec A → Bool
isYes (yes _) = true
isYes (no _) = false

isYes-refutes : {A : Type₀} (d : Dec A) → isYes d ≡ false → ¬ A
isYes-refutes (yes _) q = ⊥.rec (true≢false q)
isYes-refutes (no ¬p) _ = ¬p

isYes-refuted : {A : Type₀} (d : Dec A) → ¬ A → isYes d ≡ false
isYes-refuted (yes p) ¬p = ⊥.rec (¬p p)
isYes-refuted (no _) _ = refl

------------------------------------------------------------------------
-- §1.  A population
--
-- `Genotype` is abstract and its identity is a PARAMETER: a supplied
-- decision procedure, not a hash this module pretends to compute.
------------------------------------------------------------------------

module Population
  (Genotype    : Type₀) (_≟G_ : Discrete Genotype)
  (Environment : Type₀)
  (Evaluator   : Type₀) (_≟V_ : Discrete Evaluator)
  where

  -- An observation: who was measured, where, by whom, and what came out.
  -- ECOLOGY.md (absent from this repository)'s 6-tuple with the model/task coordinates elided; the three
  -- coordinates that carry the argument are subject, evaluator, score.
  record Evaluation : Type₀ where
    constructor evaluation
    field
      subject : Genotype
      under   : Environment
      by      : Evaluator
      score   : ℕ

  open Evaluation public

  Store : Type₀
  Store = List Evaluation

  -- The identity coordinates of an evaluation: everything except the
  -- score.  The genotype is the first of them.
  Identity : Type₀
  Identity = Genotype × Environment × Evaluator

  identityOf : Evaluation → Identity
  identityOf ev = subject ev , under ev , by ev

  genotypeOf : Evaluation → Genotype
  genotypeOf ev = fst (identityOf ev)

  -- The projection from a store to the genotypes it mentions.
  index : Store → List Genotype
  index s = map subject s

  ----------------------------------------------------------------------
  -- The grammar of store operations
  --
  -- Append an observation, discard the observations matching a test,
  -- re-score in place, or do one then another.  These are exactly the
  -- three verbs of the goal statement (adding, removing, re-scoring),
  -- closed under composition.
  ----------------------------------------------------------------------

  infixr 5 _⨟_

  data Edit : Type₀ where
    append  : Evaluation → Edit
    discard : (Evaluation → Bool) → Edit
    rescore : (Evaluation → ℕ) → Edit
    _⨟_     : Edit → Edit → Edit

  -- Re-scoring rewrites the score field and nothing else.  That is the
  -- only place a score may be written, and it is visibly not a place a
  -- genotype may be written.
  reset : (Evaluation → ℕ) → Evaluation → Evaluation
  reset f ev = evaluation (subject ev) (under ev) (by ev) (f ev)

  keep : Bool → Evaluation → Store → Store
  keep true  _  s = s
  keep false ev s = ev ∷ s

  sieve : (Evaluation → Bool) → Store → Store
  sieve p [] = []
  sieve p (ev ∷ s) = keep (p ev) ev (sieve p s)

  apply : Edit → Store → Store
  apply (append ev) s = ev ∷ s
  apply (discard p) s = sieve p s
  apply (rescore f) s = map (reset f) s
  apply (E ⨟ F)     s = apply F (apply E s)

  -- The evaluations an edit brings in from outside.  An edit can only
  -- introduce identities it literally carries.
  declared : Edit → List Evaluation
  declared (append ev) = ev ∷ []
  declared (discard _) = []
  declared (rescore _) = []
  declared (E ⨟ F)     = declared E ++ declared F

  NoAdds : Edit → Type₀
  NoAdds (append _)  = ⊥
  NoAdds (discard _) = Unit
  NoAdds (rescore _) = Unit
  NoAdds (E ⨟ F)     = NoAdds E × NoAdds F

  ----------------------------------------------------------------------
  -- Sieve and keep, in and out
  ----------------------------------------------------------------------

  keep-split : (b : Bool) (x ev : Evaluation) (t : Store)
             → ev ∈ keep b x t → ((ev ≡ x) × (b ≡ false)) ⊎ (ev ∈ t)
  keep-split true  x ev t m       = inr m
  keep-split false x ev t (inl p) = inl (p , refl)
  keep-split false x ev t (inr m) = inr m

  keep-cons : (b : Bool) (x ev : Evaluation) (t : Store)
            → ev ≡ x → b ≡ false → ev ∈ keep b x t
  keep-cons b x ev t q r = subst (λ c → ev ∈ keep c x t) (sym r) (inl q)

  keep-mono : (b : Bool) (x ev : Evaluation) (t : Store)
            → ev ∈ t → ev ∈ keep b x t
  keep-mono true  x ev t m = m
  keep-mono false x ev t m = inr m

  sieve-sound : (p : Evaluation → Bool) (s : Store) (ev : Evaluation)
              → ev ∈ sieve p s → (ev ∈ s) × (p ev ≡ false)
  sieve-sound p [] ev m = ⊥.rec m
  sieve-sound p (x ∷ s) ev m with keep-split (p x) x ev (sieve p s) m
  ... | inl (q , r) = inl q , cong p q ∙ r
  ... | inr m'      = inr (fst rest) , snd rest
        where rest = sieve-sound p s ev m'

  sieve-complete : (p : Evaluation → Bool) (s : Store) (ev : Evaluation)
                 → ev ∈ s → p ev ≡ false → ev ∈ sieve p s
  sieve-complete p [] ev m h = ⊥.rec m
  sieve-complete p (x ∷ s) ev (inl q) h =
    keep-cons (p x) x ev (sieve p s) q (cong p (sym q) ∙ h)
  sieve-complete p (x ∷ s) ev (inr m) h =
    keep-mono (p x) x ev (sieve p s) (sieve-complete p s ev m h)

  ----------------------------------------------------------------------
  -- The index, in and out
  ----------------------------------------------------------------------

  ∈-index : (s : Store) (ev : Evaluation) → ev ∈ s → subject ev ∈ index s
  ∈-index [] ev m = ⊥.rec m
  ∈-index (x ∷ s) ev (inl q) = inl (cong subject q)
  ∈-index (x ∷ s) ev (inr m) = inr (∈-index s ev m)

  index-∈ : (s : Store) (g : Genotype)
          → g ∈ index s
          → Σ[ ev ∈ Evaluation ] (ev ∈ s) × (subject ev ≡ g)
  index-∈ [] g m = ⊥.rec m
  index-∈ (x ∷ s) g (inl q) = x , inl refl , sym q
  index-∈ (x ∷ s) g (inr m) =
    fst rest , inr (fst (snd rest)) , snd (snd rest)
    where rest = index-∈ s g m

  ------------------------------------------------------------------------
  -- §2.  identity-is-not-performance
  --
  -- The statement: for EVERY edit E, every store s, and every evaluation
  -- surviving in `apply E s`, there is an evaluation ev₀ -- already in s,
  -- or written down in E itself -- with the SAME identity.  Adding,
  -- removing and re-scoring therefore cannot alter a genotype, and cannot
  -- produce one that no one supplied.  Scores are read (the `discard` and
  -- `rescore` predicates may read them freely); identities are only ever
  -- copied.
  ------------------------------------------------------------------------

  rescore-sound : (f : Evaluation → ℕ) (s : Store) (ev : Evaluation)
                → ev ∈ map (reset f) s
                → Σ[ ev₀ ∈ Evaluation ] (ev₀ ∈ s) × (identityOf ev ≡ identityOf ev₀)
  rescore-sound f [] ev m = ⊥.rec m
  rescore-sound f (x ∷ s) ev (inl q) = x , inl refl , cong identityOf q
  rescore-sound f (x ∷ s) ev (inr m) =
    fst rest , inr (fst (snd rest)) , snd (snd rest)
    where rest = rescore-sound f s ev m

  identity-is-not-performance :
      (E : Edit) (s : Store) (ev : Evaluation)
    → ev ∈ apply E s
    → Σ[ ev₀ ∈ Evaluation ]
        (((ev₀ ∈ s) ⊎ (ev₀ ∈ declared E)) × (identityOf ev ≡ identityOf ev₀))
  identity-is-not-performance (append e) s ev (inl q) =
    e , inr (inl refl) , cong identityOf q
  identity-is-not-performance (append e) s ev (inr m) =
    ev , inl m , refl
  identity-is-not-performance (discard p) s ev m =
    ev , inl (fst (sieve-sound p s ev m)) , refl
  identity-is-not-performance (rescore f) s ev m =
    fst rest , inl (fst (snd rest)) , snd (snd rest)
    where rest = rescore-sound f s ev m
  identity-is-not-performance (E ⨟ F) s ev m
    with identity-is-not-performance F (apply E s) ev m
  ... | ev₁ , inr dF , q = ev₁ , inr (∈-++-right (declared E) (declared F) dF) , q
  ... | ev₁ , inl mE , q with identity-is-not-performance E s ev₁ mE
  ...   | ev₀ , inl m₀ , q₀ = ev₀ , inl m₀ , q ∙ q₀
  ...   | ev₀ , inr d₀ , q₀ =
          ev₀ , inr (∈-++-left (declared E) (declared F) d₀) , q ∙ q₀

  -- The genotype coordinate on its own.
  genotype-is-not-performance :
      (E : Edit) (s : Store) (ev : Evaluation)
    → ev ∈ apply E s
    → Σ[ ev₀ ∈ Evaluation ]
        (((ev₀ ∈ s) ⊎ (ev₀ ∈ declared E)) × (genotypeOf ev ≡ genotypeOf ev₀))
  genotype-is-not-performance E s ev m =
    fst r , fst (snd r) , cong fst (snd (snd r))
    where r = identity-is-not-performance E s ev m

  -- An edit that declares no evaluation has nothing to introduce.
  nothing-declared : (E : Edit) → NoAdds E → (ev : Evaluation) → ¬ (ev ∈ declared E)
  nothing-declared (append _) ()
  nothing-declared (discard _) _ ev m = m
  nothing-declared (rescore _) _ ev m = m
  nothing-declared (E ⨟ F) (nE , nF) ev m with ∈-++-split (declared E) (declared F) m
  ... | inl mE = nothing-declared E nE ev mE
  ... | inr mF = nothing-declared F nF ev mF

  -- Removing and re-scoring, in any combination, invent no genotype.
  edits-without-additions-invent-no-genotype :
      (E : Edit) → NoAdds E → (s : Store) (g : Genotype)
    → g ∈ index (apply E s) → g ∈ index s
  edits-without-additions-invent-no-genotype E nE s g m
    with index-∈ (apply E s) g m
  ... | ev , mev , q with identity-is-not-performance E s ev mev
  ...   | ev₀ , inr d , _ = ⊥.rec (nothing-declared E nE ev₀ d)
  ...   | ev₀ , inl m₀ , qi =
          subst (_∈ index s) (sym (cong fst qi) ∙ q) (∈-index s ev₀ m₀)

  -- Re-scoring fixes the genotype index on the nose, not merely up to
  -- membership: the list of genotypes is literally unchanged.
  rescoring-fixes-the-index :
      (f : Evaluation → ℕ) (s : Store) → index (apply (rescore f) s) ≡ index s
  rescoring-fixes-the-index f [] = refl
  rescoring-fixes-the-index f (x ∷ s) =
    cong (subject x ∷_) (rescoring-fixes-the-index f s)

  -- The identity oracle takes no store.  This one is `refl`, and that is
  -- the point rather than an embarrassment: the discipline "performance
  -- must never contaminate identity" is enforced by the TYPE of the
  -- decision procedure, and the theorem records that the type was chosen
  -- that way and that nothing below secretly widens it.
  decideIdentity : Store → (g h : Genotype) → Dec (g ≡ h)
  decideIdentity _ g h = g ≟G h

  identity-does-not-read-the-store :
      (s t : Store) (g h : Genotype) → decideIdentity s g h ≡ decideIdentity t g h
  identity-does-not-read-the-store s t g h = refl

  ------------------------------------------------------------------------
  -- §3.  transport-needs-a-witness (positive half)
  --
  -- `σ : Scoring` is the ground truth an evaluator is trying to report; an
  -- evaluation is `Faithful` when its recorded score is that truth.
  -- Transport relabels an evaluation of g₀ as an evaluation of g₁.  The
  -- theorem says relabelling preserves faithfulness given (a) a Bridge
  -- between the two presentations and (b) an invariance hypothesis.
  --
  -- Note where the work is done: the Bridge `w` is an argument the proof
  -- NEVER USES.  That is the honest formalisation of the design rule.  The
  -- witness is what the protocol requires you to exhibit; the invariance
  -- theorem is what discharges the obligation; and the negative half below
  -- shows the first cannot be made to do the second's job.  (Compare
  -- Residual's `no-invariant-response-sees-ϱ`: the maps of a bridge do not
  -- determine the weights riding alongside them.)
  ------------------------------------------------------------------------

  Scoring : Type₀
  Scoring = Genotype → Environment → ℕ

  Faithful : Scoring → Evaluation → Type₀
  Faithful σ ev = score ev ≡ σ (subject ev) (under ev)

  relabel : Genotype → Evaluation → Evaluation
  relabel g ev = evaluation g (under ev) (by ev) (score ev)

  -- The theorem that must accompany a witness before a score may move.
  ScoreInvariant : Scoring → Genotype → Genotype → Type₀
  ScoreInvariant σ g₀ g₁ = (e : Environment) → σ g₀ e ≡ σ g₁ e

  transport-needs-a-witness :
      (σ : Scoring) (present : Genotype → Presentation) (g₀ g₁ : Genotype)
    → Bridge (present g₀) (present g₁)     -- the witness the protocol demands
    → ScoreInvariant σ g₀ g₁               -- and the invariance theorem
    → (ev : Evaluation) → subject ev ≡ g₀ → Faithful σ ev
    → Faithful σ (relabel g₁ ev)
  transport-needs-a-witness σ present g₀ g₁ w inv ev at faithful =
    faithful ∙ cong (λ g → σ g (under ev)) at ∙ inv (under ev)

  -- Transport writes a new observation; it never overwrites the old one.
  transport-is-append-only :
      (g : Genotype) (ev : Evaluation) (s : Store) (x : Evaluation)
    → x ∈ s → x ∈ apply (append (relabel g ev)) s
  transport-is-append-only g ev s x m = inr m

  ------------------------------------------------------------------------
  -- §4.  gamed-evaluator-is-quarantinable
  --
  -- Every evaluation records its evaluator, so "drop everything this
  -- evaluator said" is an expressible edit -- this is where the supplied
  -- decidable identity on `Evaluator` earns its place.  Quarantine keeps
  -- exactly the evaluations by other evaluators, and by §2 it invents no
  -- genotype and alters none.
  ------------------------------------------------------------------------

  producedBy : Evaluator → Evaluation → Bool
  producedBy v ev = isYes (by ev ≟V v)

  quarantine : Evaluator → Store → Store
  quarantine v s = apply (discard (producedBy v)) s

  quarantine-adds-nothing : (v : Evaluator) → NoAdds (discard (producedBy v))
  quarantine-adds-nothing v = tt

  -- Everything another evaluator said survives.
  quarantine-keeps-others :
      (v : Evaluator) (s : Store) (ev : Evaluation)
    → ev ∈ s → ¬ (by ev ≡ v) → ev ∈ quarantine v s
  quarantine-keeps-others v s ev m ¬p =
    sieve-complete (producedBy v) s ev m (isYes-refuted (by ev ≟V v) ¬p)

  -- Nothing else survives, and nothing new appears.
  quarantine-removes-the-evaluator :
      (v : Evaluator) (s : Store) (ev : Evaluation)
    → ev ∈ quarantine v s → (ev ∈ s) × (¬ (by ev ≡ v))
  quarantine-removes-the-evaluator v s ev m =
    fst r , isYes-refutes (by ev ≟V v) (snd r)
    where r = sieve-sound (producedBy v) s ev m

  -- Every genotype still witnessed by some other evaluator is still in the
  -- index afterwards ...
  quarantine-keeps-genotypes :
      (v : Evaluator) (s : Store) (ev : Evaluation)
    → ev ∈ s → ¬ (by ev ≡ v) → subject ev ∈ index (quarantine v s)
  quarantine-keeps-genotypes v s ev m ¬p =
    ∈-index (quarantine v s) ev (quarantine-keeps-others v s ev m ¬p)

  -- ... and quarantine never manufactures one.  Combined with §2: removing
  -- an evaluator's observations touches observations only.  A genotype
  -- scored ONLY by the gamed evaluator loses its record and keeps its
  -- identity -- `Genotype` is a different type, and `quarantine` has no
  -- way to produce or destroy an inhabitant of it.
  quarantine-invents-no-genotype :
      (v : Evaluator) (s : Store) (g : Genotype)
    → g ∈ index (quarantine v s) → g ∈ index s
  quarantine-invents-no-genotype v =
    edits-without-additions-invent-no-genotype
      (discard (producedBy v)) (quarantine-adds-nothing v)

------------------------------------------------------------------------
-- §3'.  transport-needs-a-witness, sharp negative half
--
-- A homometric pair, in ChuAdvance's `Agree` sense.  Genes are pairs: a
-- VISIBLE coordinate, which the declared tests fingerprint and which the
-- presentation exposes, and a HIDDEN coordinate, which the score reads.
-- The two genes below have
--
--   * the SAME presentation (definitionally: both are `pres ℕ (λ x y →
--     x + 0)`), hence a Bridge between them with identity maps;
--   * agreeing observations on a NONEMPTY declared environment list --
--     the empty-test escape of `ChuAdvance.no-tests-no-defect` is closed;
--   * different scores.
--
-- Therefore the transport rule with the Bridge and the agreement but
-- without the invariance hypothesis is refutable, and no rule converting
-- finite-environment agreement into score invariance can exist.  This is
-- ECOLOGY.md (absent from this repository)'s "observation is not isomorphism ... Homometric examples are
-- the reason, not an edge case", checked.
------------------------------------------------------------------------

Gene : Type₀
Gene = ℕ × ℕ

visible hidden : Gene → ℕ
visible = fst
hidden = snd

private
  eqNat : ℕ → ℕ → Bool
  eqNat zero zero = true
  eqNat zero (suc _) = false
  eqNat (suc _) zero = false
  eqNat (suc m) (suc n) = eqNat m n

  isCons : List ℕ → Type₀
  isCons [] = ⊥
  isCons (_ ∷ _) = Unit

discreteGene : Discrete Gene
discreteGene (a , b) (c , d) with discreteℕ a c | discreteℕ b d
... | yes p | yes q = yes (λ i → p i , q i)
... | yes p | no ¬q = no (λ r → ¬q (cong snd r))
... | no ¬p | _     = no (λ r → ¬p (cong fst r))

-- The declared test environment reads the visible coordinate only.
fingerprint : Obs Gene ℕ
fingerprint g n = eqNat (visible g) n

declaredTests : List ℕ
declaredTests = 0 ∷ 1 ∷ 2 ∷ []

tests-nonempty : ¬ (declaredTests ≡ [])
tests-nonempty p = subst isCons p tt

-- The score reads the hidden coordinate.
σ : Gene → ℕ → ℕ
σ g _ = hidden g

-- The presentation exposes the visible coordinate only.
present : Gene → Presentation
present g = pres ℕ (λ x y → x + visible g)

g₀ g₁ : Gene
g₀ = 0 , 0
g₁ = 0 , 1

-- Same presentation, so the identity maps are a Bridge in Residual's sense.
bridge₀₁ : Bridge (present g₀) (present g₁)
bridge₀₁ = edge (λ x → x) 0 , edge (λ x → x) 0

agree₀₁ : Agree fingerprint declaredTests g₀ g₁
agree₀₁ = refl , refl , refl , tt

genotypes-differ : ¬ (g₀ ≡ g₁)
genotypes-differ p = znots (cong snd p)

scores-differ : ¬ (σ g₀ 0 ≡ σ g₁ 0)
scores-differ = znots

-- The pair, packaged.
homometric-pair :
  Σ[ w ∈ Bridge (present g₀) (present g₁) ]
    ( Agree fingerprint declaredTests g₀ g₁
    × (¬ (declaredTests ≡ []))
    × (¬ (g₀ ≡ g₁))
    × (Σ[ e ∈ ℕ ] ¬ (σ g₀ e ≡ σ g₁ e)) )
homometric-pair =
  bridge₀₁ , agree₀₁ , tests-nonempty , genotypes-differ , (0 , scores-differ)

-- No rule turns agreement on a finite environment list into invariance.
agreement-is-not-invariance :
  ¬ ( (h₀ h₁ : Gene)
    → Agree fingerprint declaredTests h₀ h₁
    → (e : ℕ) → σ h₀ e ≡ σ h₁ e )
agreement-is-not-invariance rule = scores-differ (rule g₀ g₁ agree₀₁ 0)

-- The escape is real but environment-relative, exactly as ECOLOGY.md (absent from this repository) says.
-- A declared list that also fingerprints the hidden coordinate DOES tell
-- this pair apart.  The claim is not that observation is useless; it is
-- that which pairs a test list merges is a property of the list, never of
-- the objects -- so agreement can nominate an equivalence search and can
-- never discharge the invariance obligation.
deepFingerprint : Obs Gene ℕ
deepFingerprint g n = eqNat (hidden g) n

deeper-tests-separate : ¬ (Agree deepFingerprint (0 ∷ []) g₀ g₁)
deeper-tests-separate (p , _) = true≢false p

module Hidden = Population Gene discreteGene ℕ ℕ discreteℕ

-- One faithful evaluation of the visible-equal, hidden-different pair.
ev₀ : Hidden.Evaluation
ev₀ = Hidden.evaluation g₀ 0 0 0

ev₀-faithful : Hidden.Faithful σ ev₀
ev₀-faithful = refl

-- THE SHARP STATEMENT.  A transport rule that accepts a Bridge and
-- observational agreement, but not an invariance hypothesis, is false.
transport-without-invariance-is-unsound :
  ¬ ( (h₀ h₁ : Gene)
    → Bridge (present h₀) (present h₁)
    → Agree fingerprint declaredTests h₀ h₁
    → (ev : Hidden.Evaluation) → Hidden.subject ev ≡ h₀
    → Hidden.Faithful σ ev
    → Hidden.Faithful σ (Hidden.relabel h₁ ev) )
transport-without-invariance-is-unsound rule =
  znots (rule g₀ g₁ bridge₀₁ agree₀₁ ev₀ refl ev₀-faithful)

-- And the same rule WITH the invariance hypothesis is the theorem of §3;
-- instantiated here so the two statements can be read side by side.
transport-with-invariance-is-sound :
    (h₀ h₁ : Gene)
  → Bridge (present h₀) (present h₁)
  → Hidden.ScoreInvariant σ h₀ h₁
  → (ev : Hidden.Evaluation) → Hidden.subject ev ≡ h₀
  → Hidden.Faithful σ ev
  → Hidden.Faithful σ (Hidden.relabel h₁ ev)
transport-with-invariance-is-sound =
  λ h₀ h₁ w inv ev at f →
    Hidden.transport-needs-a-witness σ present h₀ h₁ w inv ev at f

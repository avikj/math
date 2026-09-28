{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- QuotientFiberLaw
--
-- THE ONE THEOREM, as a term.
--
-- The law:
--
--   A closed observation class sees exactly a quotient.  What it cannot
--   see is the fiber.  No post-processing of the quotient manufactures
--   the fiber.  Visibility returns only by a separating (charged) query.
--
-- The law appears as: Theorem F (operator algebra), the
-- PMTorus cokernel (finite cohomology), Cl_S closure (algebra), the
-- affine-g criterion (decision theory, upstream), Benzécri equivalence
-- (partitions), BAND's C<3 (analytic), collisionObstructsDecoder
-- (kernel pairs), ker B circulation (flow), three unmerged cubical
-- descent lemmas, the Lean strict-refinement iff, the reversibility
-- price, and the weighted-functional repair.  Twelve proofs, no shared
-- statement.  This module states the shared law, checked, over an
-- ARBITRARY state space and an ARBITRARY family of Boolean queries, and
-- derives ONE of the twelve (ParitySeparator's barrier) as an instance.
-- The other eleven are not re-derived here, so "these are one theorem"
-- is checked for that one instance only; for the rest it is still a
-- reading, not a term.
--
-- Contents (no holes, no postulates, --safe):
--
--   §1 general law, any X:
--     obs                      the transcript of a query list
--     AllBlind / HasCharged    the two sides: every query agrees on the
--                              pair / some query separates it
--     obs-agree                blind queries ⇒ EQUAL transcripts
--     no-decision              ⇒ no post-processing separates.  This is
--                              the fiber-invisibility half, proof: cong
--     charged⇒separator        one charged query ⇒ a CONSTRUCTED
--                              separator (drop k answers, look)
--     law                      the iff, packaged
--     not-both                 the sides are exclusive: no vacuity
--     collision-obstructs      Ishango's lemma in general form: a target
--                              that separates a blind pair factors
--                              through no post-processing of the
--                              transcript — the side record is NECESSARY
--
--   §2 the parity barrier as an instance:
--     queryOf                  a Number becomes a Query on Signs
--     evenBlind                even-Ω numbers are blind on (σ₊, flip σ₊)
--     parity-instance          ParitySeparator.no-decision, re-derived
--                              from §1's `no-decision` — the old theorem
--                              is literally `law` applied to one pair
--     parity-charged           …and one odd query flips it, via
--                              `charged⇒separator`
--
------------------------------------------------------------------------

module QuotientFiberLaw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false ; notnot)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Relation.Nullary using (¬_)

open import ParitySeparator using
  (Signs ; Number ; Ω ; val ; flip ; sgn ; neutral-blind ; charged-separates)
open import ChargeCriterion using (σ₊ ; val-σ₊ ; val-σ₋)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  The law, over any state space.
------------------------------------------------------------------------

module Law (X : Type ℓ) where

  Query : Type ℓ
  Query = X → Bool

  -- The transcript: everything a method ever learns from its reads.
  obs : List Query → X → List Bool
  obs []       x = []
  obs (o ∷ os) x = o x ∷ obs os x

  -- A query is blind on a pair when it cannot tell them apart; charged
  -- when it flips.  Over Bool these are the only possibilities, and
  -- stating charge as `≡ not` keeps everything computable.
  Blind Charged : Query → X → X → Type
  Blind   o x y = o x ≡ o y
  Charged o x y = o x ≡ not (o y)

  -- List versions, by recursion (never as indexed families — a
  -- criterion that does not compute under transport is not a test).
  AllBlind HasCharged : List Query → X → X → Type
  AllBlind   []       x y = Unit
  AllBlind   (o ∷ os) x y = Blind o x y × AllBlind os x y
  HasCharged []       x y = ⊥
  HasCharged (o ∷ os) x y = Charged o x y ⊎ HasCharged os x y

  -- A separator: some post-processing of the transcript that tells the
  -- pair apart.  `decide` is arbitrary — this quantifies over EVERY
  -- possible analysis, computable or not, of everything the method read.
  Separates : List Query → X → X → Type
  Separates os x y =
    Σ[ decide ∈ (List Bool → Bool) ]
      (decide (obs os x) ≡ not (decide (obs os y)))

  ----------------------------------------------------------------------
  -- Fiber invisibility.  Blind queries give EQUAL transcripts — not
  -- close, equal — so nothing downstream can differ.  The proof of the
  -- law's negative half is `cong`, because there is nothing to separate.
  ----------------------------------------------------------------------

  obs-agree : (os : List Query) (x y : X)
            → AllBlind os x y → obs os x ≡ obs os y
  obs-agree []       x y tt        = refl
  obs-agree (o ∷ os) x y (b , bs) = cong₂ _∷_ b (obs-agree os x y bs)

  no-decision : (os : List Query) (x y : X)
              → AllBlind os x y → ¬ Separates os x y
  no-decision os x y bs (decide , sep) =
    not-fix (decide (obs os y)) (sym (cong decide (obs-agree os x y bs)) ∙ sep)
    where
      not-fix : (b : Bool) → ¬ (b ≡ not b)
      not-fix true  e = true≢false e
      not-fix false e = true≢false (sym e)

  ----------------------------------------------------------------------
  -- Charge suffices, constructively: drop everything before the charged
  -- query and look.  Nothing clever is needed once a read carries
  -- charge — which is the whole point: power lives in WHAT IS READ.
  ----------------------------------------------------------------------

  hd : List Bool → Bool
  hd []      = false
  hd (b ∷ _) = b

  tl : List Bool → List Bool
  tl []       = []
  tl (_ ∷ bs) = bs

  charged⇒separator : (os : List Query) (x y : X)
                    → HasCharged os x y → Separates os x y
  charged⇒separator (o ∷ os) x y (inl c) = hd , c
  charged⇒separator (o ∷ os) x y (inr h) with charged⇒separator os x y h
  ... | (decide , sep) = (λ ℓs → decide (tl ℓs)) , sep

  ----------------------------------------------------------------------
  -- The law, packaged, with its non-vacuity.
  ----------------------------------------------------------------------

  law : (os : List Query) (x y : X)
      → (HasCharged os x y → Separates os x y)
      × (AllBlind   os x y → ¬ Separates os x y)
  law os x y = charged⇒separator os x y , no-decision os x y

  not-both : (os : List Query) (x y : X)
           → AllBlind os x y → ¬ HasCharged os x y
  not-both (o ∷ os) x y (b , _)  (inl c) = not-fix (o y) (sym b ∙ c)
    where
      not-fix : (v : Bool) → ¬ (v ≡ not v)
      not-fix true  e = true≢false e
      not-fix false e = true≢false (sym e)
  not-both (o ∷ os) x y (_ , bs) (inr h) = not-both os x y bs h

  ----------------------------------------------------------------------
  -- The side record is necessary (Ishango's lemma, general form): a
  -- target that separates a blind pair factors through NO analysis of
  -- the transcript.  Repair requires reading something new — a record —
  -- and by `law` the record works exactly when it is charged on the
  -- collision.  Absence type, per NEGATIVE_KNOWLEDGE_IS_TYPED: T2 — the
  -- certificate is this pair of halves, and either half alone misleads.
  ----------------------------------------------------------------------

  FactorsThrough : (os : List Query) → (X → Bool) → Type ℓ
  -- (lives in Type ℓ because the factoring condition quantifies over X)
  FactorsThrough os t =
    Σ[ g ∈ (List Bool → Bool) ] ((x : X) → g (obs os x) ≡ t x)

  collision-obstructs : (os : List Query) (t : X → Bool) (x y : X)
                      → AllBlind os x y → t x ≡ not (t y)
                      → ¬ FactorsThrough os t
  collision-obstructs os t x y bs c (g , comm) =
    no-decision os x y bs (g , (comm x ∙ c ∙ cong not (sym (comm y))))

------------------------------------------------------------------------
-- §2  The parity barrier is an instance.
--
-- The state space is the sign assignments; a Number is a query by
-- evaluation; even-Ω numbers are blind on the gauge pair and odd-Ω
-- numbers are charged on it.  ParitySeparator's theorems become two
-- applications of `law`.
------------------------------------------------------------------------

open Law Signs renaming (no-decision to gen-no-decision)

queryOf : Number → Query
queryOf n = λ σ → val σ n

queries : List Number → List Query
queries []       = []
queries (n ∷ ns) = queryOf n ∷ queries ns

-- Even-Ω query lists are blind on the gauge pair (σ₊ , flip σ₊)…
EvenΩ : List Number → Type
EvenΩ []       = Unit
EvenΩ (n ∷ ns) = (sgn (Ω n) ≡ true) × EvenΩ ns

evenBlind : (ns : List Number) → EvenΩ ns
          → AllBlind (queries ns) (flip σ₊) σ₊
evenBlind []       tt        = tt
evenBlind (n ∷ ns) (e , es) = neutral-blind σ₊ n e , evenBlind ns es

-- …so the barrier is one application of the general law:
parity-instance : (ns : List Number) → EvenΩ ns
                → ¬ Separates (queries ns) (flip σ₊) σ₊
parity-instance ns es = gen-no-decision (queries ns) (flip σ₊) σ₊ (evenBlind ns es)

-- And one odd-Ω read flips it — the repair, also one application:
oddCharged : (n : Number) → sgn (Ω n) ≡ false
           → Charged (queryOf n) (flip σ₊) σ₊
oddCharged n o = charged-separates σ₊ n o

parity-charged : (n : Number) (ns : List Number) → sgn (Ω n) ≡ false
               → Separates (queryOf n ∷ queries ns) (flip σ₊) σ₊
parity-charged n ns o =
  charged⇒separator (queryOf n ∷ queries ns) (flip σ₊) σ₊ (inl (oddCharged n o))

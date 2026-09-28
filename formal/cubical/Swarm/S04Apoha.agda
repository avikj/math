{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Swarm.S04Apoha
--
-- Two vocabularies for "these two states are not the same".
--
--   Serre form (positive, then negated):
--        Ind x y  =  every observation agrees on x and y
--        distinct =  ¬ Ind x y
--
--   Dignaga form (apoha: the term IS its exclusion):
--        Sep x y  =  SOME observation excludes the identification,
--                    and you hold the observation in your hand
--
-- Classically these are the same notion.  Constructively they are not,
-- and the whole content of this file is WHERE they part company:
--
--   * `Arbitrary.ind→¬sep` / `Arbitrary.¬sep→ind`
--       The two NEGATIVE forms always agree: `¬ Sep` and `Ind` are
--       interderivable for Bool-valued observables over ANY index type.
--       So the disagreement is not about negation.  It is about the
--       witness.
--
--   * `Finite.¬ind→sep`
--       For a FINITE observable family (a list), ¬ Ind yields an actual
--       separating observation, by bounded search.  Witnessed apoha and
--       negated indistinguishability coincide at every finite level.
--
--   * `MP→Witnessed` / `Witnessed→MP`
--       At the horizon (observables indexed by ℕ) the coincidence is
--       EXACTLY Markov's Principle -- an equivalence, both directions
--       proved.  Not "hard", not "open": a named principle, and the
--       reverse direction pins it from below with X := Bool.
--
-- Why this repository: upstream U0006 asks for the quotient X/~_O and
-- whether a datum descends to it; `collab/messages/shilpin/
-- persistent_workers_emergent_object.md` (absent from this repository) builds a certificate complex
-- whose stored proofs ARE shortest separating words.  The theorems below
-- say that such a complex is complete at every finite observation level
-- (`Finite.¬ind→sep`), that its stored witnesses survive refinement
-- (`Finite.sepMono`), that its state meanings coarsen under forgetting
-- (`Finite.indAnti`), and that the passage to the full family converts
-- witnessed exclusion into bare negation with deficit precisely MP.
-- The "locality failure" at the horizon has a name.
--
-- No postulates, no holes, no imports outside the cubical library.
------------------------------------------------------------------------

module Swarm.S04Apoha where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- 0.  Two Bool facts, spelled out so nothing is imported on faith.
------------------------------------------------------------------------

¬false≡true : ¬ (false ≡ true)
¬false≡true p = subst (λ b → if b then ⊥ else Bool) p true

eqB : Bool → Bool → Bool
eqB true  true  = true
eqB true  false = false
eqB false true  = false
eqB false false = true

eqBrefl : (a : Bool) → eqB a a ≡ true
eqBrefl true  = refl
eqBrefl false = refl

eqB→≡ : (a b : Bool) → eqB a b ≡ true → a ≡ b
eqB→≡ true  true  _ = refl
eqB→≡ true  false q = ⊥.rec (¬false≡true q)
eqB→≡ false true  q = ⊥.rec (¬false≡true q)
eqB→≡ false false _ = refl

≡→eqB : (a b : Bool) → a ≡ b → eqB a b ≡ true
≡→eqB a b p = subst (λ c → eqB a c ≡ true) p (eqBrefl a)

------------------------------------------------------------------------
-- 1.  An arbitrary observable family.  The negative forms agree.
------------------------------------------------------------------------

module Arbitrary {X : Type ℓ} {I : Type ℓ'} (O : I → X → Bool) where

  -- Serre: shortest positive statement of "indistinguishable".
  Ind : X → X → Type ℓ'
  Ind x y = (i : I) → O i x ≡ O i y

  -- Dignaga: the meaning of "distinct" is the exclusion, held in hand.
  Sep : X → X → Type ℓ'
  Sep x y = Σ[ i ∈ I ] (¬ (O i x ≡ O i y))

  sep→¬ind : {x y : X} → Sep x y → ¬ Ind x y
  sep→¬ind (i , d) ind = d (ind i)

  ind→¬sep : {x y : X} → Ind x y → ¬ Sep x y
  ind→¬sep ind (i , d) = d (ind i)

  -- The converse of `ind→¬sep`.  This is the one that does NOT need any
  -- finiteness or omniscience: Bool's decidable equality is enough,
  -- because ¬Sep hands us ¬¬(O i x ≡ O i y) at each single index and a
  -- Bool path is stable.
  ¬sep→ind : {x y : X} → ¬ Sep x y → Ind x y
  ¬sep→ind {x = x} {y = y} ns i with O i x ≟ O i y
  ... | yes p = p
  ... | no ¬p = ⊥.rec (ns (i , ¬p))

  -- Consequence: bare negation of distinctness is never the obstruction.
  -- Only the witness is.
  ¬ind→¬¬sep : {x y : X} → ¬ Ind x y → ¬ ¬ Sep x y
  ¬ind→¬¬sep ni ns = ni (¬sep→ind ns)

------------------------------------------------------------------------
-- 2.  Finite observation levels.  The witness is always recoverable.
--
--     A finite family is a list; this is not a coding trick, it is the
--     shape of the repository's own S₁ ⊆ S₂ ⊆ ⋯ chains (exp36's
--     {2} ⊆ {2,3} ⊆ ⋯ ⊆ {2,…,19}; U0006's "divisibility below √X").
------------------------------------------------------------------------

module Finite {X : Type ℓ} where

  Ind : List (X → Bool) → X → X → Type
  Ind []      x y = Unit
  Ind (O ∷ L) x y = (O x ≡ O y) × Ind L x y

  Sep : List (X → Bool) → X → X → Type
  Sep []      x y = ⊥
  Sep (O ∷ L) x y = (¬ (O x ≡ O y)) ⊎ Sep L x y

  -- Bounded search: the decision procedure IS the witness constructor,
  -- and it scans left to right, so the witness it returns is the
  -- leftmost separating observation.
  sepSearch : (L : List (X → Bool)) (x y : X) → Dec (Sep L x y)
  sepSearch []      x y = no (λ z → z)
  sepSearch (O ∷ L) x y with O x ≟ O y
  ... | no ¬p = yes (inl ¬p)
  ... | yes p with sepSearch L x y
  ...   | yes s = yes (inr s)
  ...   | no ¬s = no (λ { (inl ¬p) → ¬p p ; (inr s) → ¬s s })

  sep→¬ind : (L : List (X → Bool)) {x y : X} → Sep L x y → ¬ Ind L x y
  sep→¬ind (O ∷ L) (inl d) (e , _)   = d e
  sep→¬ind (O ∷ L) (inr s) (_ , ind) = sep→¬ind L s ind

  ¬sep→ind : (L : List (X → Bool)) {x y : X} → ¬ Sep L x y → Ind L x y
  ¬sep→ind []      ns = tt
  ¬sep→ind (O ∷ L) {x = x} {y = y} ns with O x ≟ O y
  ... | yes p = p , ¬sep→ind L (λ s → ns (inr s))
  ... | no ¬p = ⊥.rec (ns (inl ¬p))

  -- THE finite theorem.  At any finite observation level the Serre form
  -- and the Dignaga form of "distinct" are interderivable, effectively.
  ¬ind→sep : (L : List (X → Bool)) {x y : X} → ¬ Ind L x y → Sep L x y
  ¬ind→sep L {x = x} {y = y} ni with sepSearch L x y
  ... | yes s = s
  ... | no ns = ⊥.rec (ni (¬sep→ind L ns))

  ------------------------------------------------------------------
  -- The two monotonicity laws that the persistent-worker note states
  -- in prose (its bullets 1 and 4).  Adding observations refines
  -- meanings and never invalidates a stored witness.
  ------------------------------------------------------------------

  -- bullet 4: "Old inter-block witnesses remain valid."
  sepMono : (L M : List (X → Bool)) {x y : X} → Sep L x y → Sep (L ++ M) x y
  sepMono (O ∷ L) M (inl d) = inl d
  sepMono (O ∷ L) M (inr s) = inr (sepMono L M s)

  -- bullet 1: ~_{O∪N} = ~_O ∩ ~_N, both inclusions.
  indAnti : (L M : List (X → Bool)) {x y : X} → Ind (L ++ M) x y → Ind L x y
  indAnti []      M _       = tt
  indAnti (O ∷ L) M (e , r) = e , indAnti L M r

  indAntiR : (L M : List (X → Bool)) {x y : X} → Ind (L ++ M) x y → Ind M x y
  indAntiR []      M j       = j
  indAntiR (O ∷ L) M (_ , r) = indAntiR L M r

  indSplit : (L M : List (X → Bool)) {x y : X}
           → Ind L x y → Ind M x y → Ind (L ++ M) x y
  indSplit []      M _       jM = jM
  indSplit (O ∷ L) M (e , r) jM = e , indSplit L M r jM

------------------------------------------------------------------------
-- 3.  The horizon.  Exactly Markov's Principle.
--
--     `Witnessed` is the statement that the Dignaga form is recoverable
--     from the Serre form for an ℕ-indexed Bool observable family on a
--     small type.  It is stated at Type₀ deliberately: the reverse
--     direction only ever instantiates X := Bool, so the equivalence
--     below is tight from both sides.
------------------------------------------------------------------------

MP : Type
MP = (f : ℕ → Bool) → ¬ ((n : ℕ) → f n ≡ true) → Σ[ n ∈ ℕ ] (f n ≡ false)

Witnessed : Type₁
Witnessed = (X : Type) (O : ℕ → X → Bool) (x y : X)
          → ¬ ((n : ℕ) → O n x ≡ O n y)
          → Σ[ n ∈ ℕ ] (¬ (O n x ≡ O n y))

MP→Witnessed : MP → Witnessed
MP→Witnessed mp X O x y ni = n , d
  where
    f : ℕ → Bool
    f n = eqB (O n x) (O n y)

    hyp : ¬ ((n : ℕ) → f n ≡ true)
    hyp h = ni (λ n → eqB→≡ (O n x) (O n y) (h n))

    step : Σ[ n ∈ ℕ ] (f n ≡ false)
    step = mp f hyp

    n : ℕ
    n = fst step

    d : ¬ (O n x ≡ O n y)
    d p = ¬false≡true (sym (snd step) ∙ ≡→eqB (O n x) (O n y) p)

Witnessed→MP : Witnessed → MP
Witnessed→MP w f h = n , fn≡false
  where
    -- The probe family.  O n true ≡ f n and O n false ≡ true hold
    -- DEFINITIONALLY, so `h` is literally the hypothesis `w` wants.
    O : ℕ → Bool → Bool
    O n b = if b then f n else true

    step : Σ[ n ∈ ℕ ] (¬ (O n true ≡ O n false))
    step = w Bool O true false h

    n : ℕ
    n = fst step

    fn≡false : f n ≡ false
    fn≡false with dichotomyBool (f n)
    ... | inl q = ⊥.rec (snd step q)
    ... | inr q = q

------------------------------------------------------------------------
-- 4.  Reading of the pair.
--
-- `Arbitrary.¬sep→ind` + `Finite.¬ind→sep` + `MP→Witnessed` /
-- `Witnessed→MP` together say:
--
--   the Serre vocabulary (state the negation, delete the rest) and the
--   Dignaga vocabulary (a term is its exclusions, exhibited) are the
--   same theory over any FINITE observation set, and their difference
--   over an infinite one is not a matter of taste, style or length: it
--   is exactly one classical principle, MP, no more and no less.
--
-- Corollary for certificate complexes.  A proof store whose atoms are
-- separating observations is complete at every finite level and refines
-- monotonically (`sepMono`).  Its completion along S₁ ⊆ S₂ ⊆ ⋯ is
-- complete iff MP.  So an "incremental witness forest" can be exact
-- forever at finite stages and still fail to represent a distinction
-- that holds at the horizon -- and the failure is not a bug in the
-- forest.
------------------------------------------------------------------------

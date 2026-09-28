{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- वैधर्म्यम् · apartness is cotransitive, so it is an apartness relation;
-- and over a finite alphabet the shortest separating experiment exists.
--
-- notes/DISTINCTION_CARRIES_WITNESSES.md (absent from this repository) (main), §6 "Successor seeds":
--
--   "1. `PROVE`: `d_sep`, the shortest separating experiment, under
--    decidable `Obs`.  This is what `natural_crystal.py` (absent from this repository) actually
--    computes, and the Lean lane already has `BehavioralBFS.lean` doing
--    Hopcroft-style distinguishing-word search.  Porting that to the
--    apartness type would close the loop between the README's prose, the
--    executable, and the kernel."
--   "2. `PROVE`: cotransitivity (`x # z → (x # y) ⊎ (y # z)`) under
--    decidable `Obs` — the property that makes `#` an apartness relation
--    in the technical sense, and the one that would justify the name."
--
-- and its status line: "Not claimed: that Apart is decidable, or that
-- minimal separating depth (d_sep) exists constructively — it needs
-- decidable observation equality plus a search principle, and I did not
-- formalise it.  Delta 20's d_sep remains open here."
--
-- WHAT IS PROVED, on BehavioralApartness's own `System step obs`:
--
--   §1  Under `Discrete Obs`:
--         cotransitive : Apart x z → (Apart x y) ⊎ (Apart y z)
--       and unconditionally
--         irreflexive  : ¬ Apart x x
--         symmetric    : Apart x y → Apart y x
--       so Apart is an apartness relation in the technical sense
--       (irreflexive, symmetric, cotransitive).  The decision is on the
--       observation at the SAME word: given w separating x from z, either
--       w already separates x from y, or the observations of x and y at
--       w agree and then w separates y from z.  Cotransitivity costs
--       nothing beyond one decision; it does not need a search.
--
--   §2  The search principle, and d_sep.  With `Discrete Obs` and a
--       finite alphabet — a list `acts` with every action a member —
--       every word of length k is a member of `words k`, the Boolean
--       `sep? x y w` decides separation at w, and
--         shortest : Apart x y → Σ[ w ∈ List Act ] Apart-at x y w
--                    × ((v : List Act) → length v < length w → ¬ Apart-at x y v)
--       i.e. from ANY separating experiment a shortest one is computed,
--       with the proof that no shorter word separates.  `d-sep` is its
--       length.  The search is bounded by the length of the given
--       witness, so no unbounded principle is used.  This is the
--       apartness-type form of the Lean lane's BehavioralBFS: shortest
--       distinguishing word, by exhaustive layers.
--
-- WHAT IS NOT PROVED: that Apart is decidable (it is not, without a
-- bound); anything about natural_crystal.py (absent from this repository); Delta 21's evaluation
-- morphism.  --guardedness only because BehavioralApartness carries it.
-- The indexed membership type `_∈_` draws UnsupportedIndexedMatch
-- warnings (matches on `here`/`there` use injectivity of `_∷_`), as the
-- corpus's other indexed-membership modules do; nothing here is applied
-- to a transport.  Checked at the pin (Agda 2.8.0, agda/cubical v0.9,
-- --safe).
------------------------------------------------------------------------

module Vaidharmya_ApartnessIsCotransitiveUnderDecidableObservationSoItIsAnApartnessRelationAndTheShortestSeparatingExperimentExistsOverAFiniteAlphabet where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_ ; length ; _++_ ; map)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ≤-refl ; ≤-suc ; pred-≤-pred ; ¬-<-zero ; <-split ; suc-≤-suc ; zero-≤ ; ≤-trans ; <-weaken ; ¬m<m)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; Discrete)

open import BehavioralApartness

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- §1 · the three laws of an apartness relation
------------------------------------------------------------------------

module Laws {St : Type ℓ} {Act : Type ℓ'} {Obs : Type ℓ''}
            (step : St → Act → St) (obs : St → Obs) where

  open System step obs

  irreflexive : (x : St) → ¬ Apart x x
  irreflexive x (w , sep) = sep refl

  symmetric : {x y : St} → Apart x y → Apart y x
  symmetric (w , sep) = w , (λ e → sep (sym e))

  -- cotransitivity: decide the observations of x and y at the witness
  cotransitive : Discrete Obs → {x z : St} (y : St)
               → Apart x z → (Apart x y) ⊎ (Apart y z)
  cotransitive dec {x} {z} y (w , sep) with dec (behavior x w) (behavior y w)
  ... | yes xy = inr (w , (λ yz → sep (xy ∙ yz)))
  ... | no  nxy = inl (w , nxy)

------------------------------------------------------------------------
-- §2 · the shortest separating experiment over a finite alphabet
------------------------------------------------------------------------

-- membership in a list
data _∈_ {A : Type ℓ} (a : A) : List A → Type ℓ where
  here  : {xs : List A} → a ∈ (a ∷ xs)
  there : {b : A} {xs : List A} → a ∈ xs → a ∈ (b ∷ xs)

∈-++ˡ : {A : Type ℓ} {a : A} {xs ys : List A} → a ∈ xs → a ∈ (xs ++ ys)
∈-++ˡ here      = here
∈-++ˡ (there m) = there (∈-++ˡ m)

∈-++ʳ : {A : Type ℓ} {a : A} (xs : List A) {ys : List A} → a ∈ ys → a ∈ (xs ++ ys)
∈-++ʳ []       m = m
∈-++ʳ (x ∷ xs) m = there (∈-++ʳ xs m)

∈-map : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a : A} {xs : List A}
      → a ∈ xs → f a ∈ map f xs
∈-map f here      = here
∈-map f (there m) = there (∈-map f m)

-- all words of length k over an alphabet list
concatMap : {A : Type ℓ} {B : Type ℓ'} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (a ∷ as) = f a ++ concatMap f as

∈-concatMap : {A : Type ℓ} {B : Type ℓ'} (f : A → List B) {a : A} {b : B} {as : List A}
            → a ∈ as → b ∈ f a → b ∈ concatMap f as
∈-concatMap f here      mb = ∈-++ˡ mb
∈-concatMap f {as = a' ∷ as} (there ma) mb = ∈-++ʳ (f a') (∈-concatMap f ma mb)

-- membership in an append splits
∈-split : {A : Type ℓ} {a : A} (xs : List A) {ys : List A} → a ∈ (xs ++ ys) → (a ∈ xs) ⊎ (a ∈ ys)
∈-split []       m         = inr m
∈-split (x ∷ xs) here      = inl here
∈-split (x ∷ xs) (there m) with ∈-split xs m
... | inl l = inl (there l)
... | inr r = inr r

-- membership in a map comes from a member
∈-map⁻ : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {b : B} (xs : List A)
       → b ∈ map f xs → Σ[ a ∈ A ] (a ∈ xs) × (f a ≡ b)
∈-map⁻ f (x ∷ xs) here      = x , here , refl
∈-map⁻ f (x ∷ xs) (there m) with ∈-map⁻ f xs m
... | a , ma , e = a , there ma , e

-- membership in a concatMap comes from a member
∈-concatMap⁻ : {A : Type ℓ} {B : Type ℓ'} (f : A → List B) {b : B} (as : List A)
             → b ∈ concatMap f as → Σ[ a ∈ A ] (a ∈ as) × (b ∈ f a)
∈-concatMap⁻ f (a ∷ as) m with ∈-split (f a) m
... | inl l = a , here , l
... | inr r with ∈-concatMap⁻ f as r
...   | a' , ma , mb = a' , there ma , mb

words : {Act : Type ℓ} → List Act → ℕ → List (List Act)
words acts zero    = [] ∷ []
words acts (suc k) = concatMap (λ a → map (a ∷_) (words acts k)) acts

-- completeness: every word of length k is listed, when every action is
words-complete : {Act : Type ℓ} (acts : List Act) (all : (a : Act) → a ∈ acts)
               → (w : List Act) → w ∈ words acts (length w)
words-complete acts all []      = here
words-complete acts all (a ∷ w) =
  ∈-concatMap (λ a' → map (a' ∷_) (words acts (length w))) (all a)
              (∈-map (a ∷_) (words-complete acts all w))

-- soundness: every listed word has length k
words-length : {Act : Type ℓ} (acts : List Act) (k : ℕ) (w : List Act)
             → w ∈ words acts k → length w ≡ k
words-length acts zero    w here = refl
words-length acts (suc k) w m with ∈-concatMap⁻ (λ a → map (a ∷_) (words acts k)) acts m
... | a , _ , mw with ∈-map⁻ (a ∷_) (words acts k) mw
...   | u , mu , e = cong length (sym e) ∙ cong suc (words-length acts k u mu)

module Search {St : Type ℓ} {Act : Type ℓ'} {Obs : Type ℓ''}
              (step : St → Act → St) (obs : St → Obs)
              (dec : Discrete Obs)
              (acts : List Act) (all : (a : Act) → a ∈ acts) where

  open System step obs

  Apart-at : St → St → List Act → Type ℓ''
  Apart-at x y w = ¬ (behavior x w ≡ behavior y w)

  dec-at : (x y : St) (w : List Act) → Dec (Apart-at x y w)
  dec-at x y w with dec (behavior x w) (behavior y w)
  ... | yes e = no (λ n → n e)
  ... | no  n = yes n

  -- search a list of candidate words for a separating one
  findIn : (x y : St) (ws : List (List Act))
         → (Σ[ w ∈ List Act ] (w ∈ ws) × Apart-at x y w)
         ⊎ ((w : List Act) → w ∈ ws → ¬ Apart-at x y w)
  findIn x y []       = inr (λ w ())
  findIn x y (w ∷ ws) with dec-at x y w
  ... | yes s = inl (w , here , s)
  ... | no  n with findIn x y ws
  ...   | inl (v , m , s) = inl (v , there m , s)
  ...   | inr none = inr λ { v here → n ; v (there m) → none v m }

  -- no word shorter than n separates
  NoneBelow : St → St → ℕ → Type (ℓ-max ℓ' ℓ'')
  NoneBelow x y n = (v : List Act) → length v < n → ¬ Apart-at x y v

  -- one layer: nothing below n separates, and nothing of length n
  -- separates, so nothing below suc n separates
  extend : (x y : St) (n : ℕ) → NoneBelow x y n
         → ((w : List Act) → w ∈ words acts n → ¬ Apart-at x y w)
         → NoneBelow x y (suc n)
  extend x y n none atn v lt with <-split lt
  ... | inl lt' = none v lt'
  ... | inr e   = atn v (subst (λ k → v ∈ words acts k) e (words-complete acts all v))

  -- layered search up to a bound
  Shortest : St → St → Type (ℓ-max ℓ' ℓ'')
  Shortest x y = Σ[ w ∈ List Act ] Apart-at x y w × NoneBelow x y (length w)

  layers : (x y : St) (n : ℕ) → Shortest x y ⊎ NoneBelow x y (suc n)
  layers x y zero with findIn x y (words acts 0)
  ... | inl (w , m , s) = inl (w , s , λ v lt _ → ¬-<-zero (subst (λ t → length v < t) (words-length acts 0 w m) lt))
  ... | inr none = inr (extend x y 0 (λ v lt → ⊥rec (¬-<-zero lt)) none)
  layers x y (suc n) with layers x y n
  ... | inl found = inl found
  ... | inr none with findIn x y (words acts (suc n))
  ...   | inl (w , m , s) = inl (w , s , λ v lt → none v (subst (λ t → length v < t) (words-length acts (suc n) w m) lt))
  ...   | inr atn = inr (extend x y (suc n) none atn)

  -- THE THEOREM: from any separating experiment, a shortest one
  shortest : (x y : St) → Apart x y → Shortest x y
  shortest x y (w , sep) with layers x y (length w)
  ... | inl found = found
  ... | inr none  = ⊥rec (none w ≤-refl sep)

  d-sep : (x y : St) → Apart x y → ℕ
  d-sep x y ap = length (fst (shortest x y ap))

  -- the depth is a lower bound for every witness
  d-sep-least : (x y : St) (ap : Apart x y) (v : List Act) → Apart-at x y v → ¬ (length v < d-sep x y ap)
  d-sep-least x y ap v s lt = snd (snd (shortest x y ap)) v lt s

------------------------------------------------------------------------
-- §3 · the minimal system of BehavioralApartness §5, run through the search
------------------------------------------------------------------------

module Laghutama where
  open import Cubical.Data.Unit using (Unit ; tt)
  open import Cubical.Data.Bool using (isSetBool ; _≟_)

  step : Bool → Unit → Bool
  step b _ = b

  obs : Bool → Bool
  obs b = b

  allUnit : (u : Unit) → u ∈ (tt ∷ [])
  allUnit tt = here

  discreteBool : Discrete Bool
  discreteBool = _≟_

  open Search step obs discreteBool (tt ∷ []) allUnit
  open System step obs

  false#true : Apart false true
  false#true = (tt ∷ []) , λ e → Cubical.Data.Bool.false≢true e

  -- the empty word is a shortest separator, and the search finds depth 0
  depth-0 : d-sep false true false#true ≡ 0
  depth-0 = refl

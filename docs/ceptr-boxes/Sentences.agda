{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Sentences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; isEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ ; zero)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Foundations.Equiv using (fiber ; equivFun)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

-- the development above, as its twelve modules.
import Carrier             as C
import Install             as I
import SemanticAlternation as S
import Protocol            as P
import Integrity           as G
import Provenance          as V
import Receptor            as R
import Listening           as L
import Instances           as N
import Scape               as K
import SemanticWeb         as W
import MutualCredit        as M

sentences :
    ((s : C.Point ℓ-zero) → C.Receptor s)                         -- 10.3  the general carrier
  × ({l r : I.Tm} (d : I.Derivation l r)
       → isContr (I.Locus (I.install d)))                         -- 10.5  install's locus is a point
  × (¬ isProp (ℕ ≃ ℕ)) × isContr (Σ[ T ∈ Type ] (T ≃ ℕ))        -- 10.8  semantic alternation
  × ({l r : I.Tm} (R : Type) (d : I.Derivation l r) {s t : I.Tm}
       → I.NativeOperation.Control (I.demand R d) s
       → I.NativeOperation.Control (I.demand R d) t → s ≡ t)    -- 11.2  the slot is safe
  × ((S : P.Session) (ρ : ℕ)
       → P.eval (P.NativeOperation.source (P.retire S)) ρ
       ≡ P.eval (P.NativeOperation.target (P.retire S)) ρ)       -- 11.5  the session retires soundly
  × ((op : G.NativeOperation) (ρ : ℕ)
       → G.eval (G.NativeOperation.source op) ρ
       ≡ G.eval (G.NativeOperation.target op) ρ)                 -- 12.2  validity travels with the operation
  × (({A B X : Type} (pA : A → X) (pB : B → X) (e : V.Identified A B)
        → V.Sourced pA pB e) → ⊥)                                    -- 12.4  provenance is not carried
  × ({a b : G.Tm} (d e : G.Derivation a b) (ρ : ℕ)
       → G.derivation-sound d ρ ≡ G.derivation-sound e ρ)        -- 12.6  two nodes cannot disagree
  × (¬ G.direct ≡ G.detour)                                       -- 12.8  a fork is two carriers of one fact
  × (¬ G.Derivation G.zero (G.suc G.zero))                        -- 12.10 the warrant
  × ((n : ℕ) → isContr (R.DetISC n)) × (¬ isContr (R.FreeISC zero)) -- 13.2 receipts collapse, receptivity opens
  × ({X : Type} (J : L.Interaction X) (x : X) → L.Run J x ≃ L.Signals J x) -- 13.4 the run is its signals
  × ({A : Type} {x y : N.Instance A} → (x ≡ y) ≡ (x N.≈ y))      -- 13.6  synchrony is identity
  × ({A B : Type} (f : A → B) → A ≃ (Σ[ b ∈ B ] K.Scape f b))    -- 14.2  a scape is the partition
  × ({A B X : Type} (f : A → B) (g : B → X) (c : X)
       → K.Scape (g ∘ f) c ≃ (Σ[ w ∈ K.Scape g c ] K.Scape f (fst w))) -- 14.4 the scape algebra
  × ({A X : Type} (c : A → X)
       → ((x : X) → K.Scape c x) ≃ (Σ[ s ∈ (X → A) ] ((x : X) → c (s x) ≡ x))) -- 14.6 uncombining is a section
  × ({A : Type} → K.Scape (K.drop {A = A}) tt ≃ A)               -- 14.6  dropping forgets everything
  × ({A B : Type} (f : A → B)
       → (Σ[ a ∈ A ] Σ[ a' ∈ A ] (f a ≡ f a')) ≃ (Σ[ b ∈ B ] fiber f b × fiber f b))
  × (¬ (Σ[ B ∈ Type ] Σ[ f ∈ (W.Profile → B) ]
       ((a a' : W.Profile) → (W.Friend a a' → f a ≡ f a') × (f a ≡ f a' → W.Friend a a'))))
                                                                  -- 15.2  scapes and assertions
  × ({A B Q : Type} (R : A → B → Type) (q : A → Q)
       → W.Sufficient R q ≃ W.RespondsFrom R q)
  × ({A B Q : Type} (f : A → B) (q : A → Q) → W.Sufficient (W.Graph f) q
       → {a a' : A} → ¬ f a ≡ f a' → ¬ q a ≡ q a')
  × W.Sufficient W.R3 W.π × W.Sufficient W.R3 W.σ
  × (¬ W.Sufficient W.R3 (λ (_ : W.Pt) → tt))                      -- 15.5  what matters is fixed by R
  × (W.Sufficient (W._then_ W.Rm W.Sm) (λ (_ : W.Two) → tt)
       × (¬ W.Sufficient W.Rm (λ (_ : W.Two) → tt)))               -- 15.7  each layer has its own scape
  × (¬ (Σ[ g ∈ (∥ Bool ≃ Bool ∥₁ → Bool → Bool) ]
          ((e : Bool ≃ Bool) → g ∣ e ∣₁ ≡ equivFun e)))           -- 15.8  sameAs transports nothing
  × ((t : ℤ) (x : M.Accounts) → M.supply (M.transfer t x) ≡ M.supply x)
  × ((t : ℤ) → isEquiv (M.transfer t))                           -- 16.2  zero sum, and a transport
  × ((t : ℤ) (x : M.Accounts) → fst (M.transfer t x) ≡ fst x → t ≡ pos 0) -- 16.4  both chains move
sentences =
    C.receive
  , I.installLocusIsAPoint
  , S.structureFixesNoSymbol , S.oneSymbolOverTheStructure
  , I.anyDemandIsSafe
  , P.retireIsSound
  , G.everyOperationIsSound
  , V.provenanceIsNotCarried
  , G.twoNodesCannotDisagree
  , G.routesGenuinelyDiffer
  , G.warrant
  , R.deterministicCollapse , R.receptivityIsStrictlyWider
  , L.runIsItsSignals
  , N.path≡bisim
  , K.scapeOf
  , K.compose
  , K.uncombine
  , K.dropForgetsEverything
  , W.sameCellPairs , W.friendshipIsNoScape
  , W.sufficientIsRespondingFromTheScape
  , (λ f q → W.relevantDifferencesAreKept f q)
  , W.πSufficient , W.σSufficient , W.joinFails
  , W.materializationGap
  , W.sameAsTransportsNothing
  , M.zeroSum , (λ t → snd (M.transferEquiv t))
  , M.bothMove

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module CorpusLosslessPresentation where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber ; _≃_ ; equivFun)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
import Fibre.CorpusInteraction as C
import CompressionIsTransportSoTheOnlyCostIsTheNonContractibleFibre as Compression
import FiniteInformation as FI
private variable ℓ ℓt : Level
Source : C.Point ℓ → Type ℓ
Source = fst
source : (s : C.Point ℓ) → Source s
source = snd
Codomain : (s : C.Point ℓ) → C.Question s → Type ℓ
Codomain _ = fst
query : (s : C.Point ℓ) (q : C.Question s) → Source s → Codomain s q
query _ = snd
Residual : (s : C.Point ℓ) (q : C.Question s) → Type ℓ
Residual s q = fiber (query s q) (query s q (source s))
Presentation : (s : C.Point ℓ) (q : C.Question s) → Type ℓ
Presentation s q = Σ[ b ∈ Codomain s q ] fiber (query s q) b
lossless : (s : C.Point ℓ) (q : C.Question s) → Source s ≃ Presentation s q
lossless s q = Compression.lossless (query s q)
encode : (s : C.Point ℓ) (q : C.Question s) → Source s → Presentation s q
encode s q = equivFun (lossless s q)
current-residual : (s : C.Point ℓ) (q : C.Question s) → Residual s q
current-residual s q = source s , refl
Descends : (s : C.Point ℓ) (q : C.Question s) {T : Type ℓt} → (Source s → T) → Type _
Descends s q t = FI.FactorsThrough (query s q) t
ConstantOnResidual : (s : C.Point ℓ) (q : C.Question s) {T : Type ℓt} → (Source s → T) → Type _
ConstantOnResidual s q t = FI.FiberConstant (query s q) t
descends-iff-constant-on-residual : (s : C.Point ℓ) (q : C.Question s) {T : Type ℓt} (isSetT : isSet T) (t : Source s → T) → Iso (Descends s q t) (ConstantOnResidual s q t)
descends-iff-constant-on-residual s q isSetT t = FI.factorsThroughIsoFiberConstant isSetT (query s q) t

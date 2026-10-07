{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module CorpusSelfPresentation where
open import Cubical.Foundations.Prelude
import Fibre.CorpusInteraction as C
import Fibre.TheOrbitIsTheOneQueryCaseOfTheInteractiveCoalgebraAndTheDemandIsWhatDiffers as S
import CorpusLosslessPresentation as LP
private variable ℓ : Level
Event : (s : C.Point ℓ) (q : C.Question s) (s' : C.Point ℓ) → C.Receipt s q s' → Type (ℓ-suc ℓ)
Event {ℓ} s q s' receipt = Lift {j = ℓ-suc ℓ} (LP.Residual s q)
SelfPresentation : C.Point ℓ → Type (ℓ-suc ℓ)
SelfPresentation = S.ISC C.Question C.Receipt Event
present : (s : C.Point ℓ) → SelfPresentation s
S.react (present s) q = C.target s q , refl , lift (LP.current-residual s q) , present (C.target s q)

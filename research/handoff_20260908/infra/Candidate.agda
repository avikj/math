{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Candidate where
open import Cubical.Foundations.Prelude
open import Kernel.RewriteCertificate
import TheGenerativeLoopOnTheKernelsOwnTermsACertifiedNormalizerEmitsDerivationsSoLearnCallsInstall as N
demo : Tm
demo = add var (suc zero)
answer : Tm
answer = N.normalForm demo
checked : answer ≡ suc var
checked = refl

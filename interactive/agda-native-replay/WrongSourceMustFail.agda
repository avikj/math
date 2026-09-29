{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- NEGATIVE CONTROL: this file must NOT typecheck.
module WrongSourceMustFail where

open import Cubical.Foundations.Prelude
open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar

wrong-source : EnabledFuture zero
EnabledFuture.operation wrong-source = install accepted
-- accepted starts at add var (suc zero), NOT zero.
EnabledFuture.control wrong-source = refl

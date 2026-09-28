{-# OPTIONS --cubical --safe --guardedness #-}

-- Definitional-equality observation for the corpus: each declaration's
-- checked type, normalised.  Normalisation is an observation (never a
-- destructive ingestion); by ConservativeSemanticCompression the
-- observer quotient it induces IS conservative semantic compression,
-- and by NerodeYantra (absent from this repository) its kernel — group by stored normal form — is
-- the greatest congruence for that observation.  No pairwise work:
-- one normalise per declaration, then pure grouping.

module Fibre.CorpusNorm where

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Fibre.CorpusReflection using (expandAll)

NormEntry : Set
NormEntry = Σ Name (λ _ → Term)   -- declaration, normal form of its type

NormCorpus : Set
NormCorpus = List NormEntry

normOne : Name → TC NormEntry
normOne n =
  bindTC (getType n) λ ty →
  bindTC (normalise ty) λ nty →
  returnTC (n , nty)

normAll : List Name → TC NormCorpus
normAll [] = returnTC []
normAll (n ∷ ns) =
  bindTC (catchTC (bindTC (normOne n) λ e → returnTC (e ∷ [])) (returnTC [])) λ here →
  bindTC (normAll ns) λ rest →
  returnTC (append here rest)
  where
  append : NormCorpus → NormCorpus → NormCorpus
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

materializeNormTerm : List Name → TC Term
materializeNormTerm ns = bindTC (normAll ns) quoteTC

macro
  materializeNorm : List Name → Term → TC ⊤
  materializeNorm ns hole = bindTC (materializeNormTerm ns) (unify hole)

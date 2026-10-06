{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module ColorFrame where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_)
import photon as P

data Color : Type where c0 c1 c2 : Color
data Frame : Type where p012 p021 p102 p120 p201 p210 : Frame

apply : Frame → Color → Color
apply p012 c0 = c0
apply p012 c1 = c1
apply p012 c2 = c2
apply p021 c0 = c0
apply p021 c1 = c2
apply p021 c2 = c1
apply p102 c0 = c1
apply p102 c1 = c0
apply p102 c2 = c2
apply p120 c0 = c1
apply p120 c1 = c2
apply p120 c2 = c0
apply p201 c0 = c2
apply p201 c1 = c0
apply p201 c2 = c1
apply p210 c0 = c2
apply p210 c1 = c1
apply p210 c2 = c0

inverse : Frame → Frame
inverse p012 = p012
inverse p021 = p021
inverse p102 = p102
inverse p120 = p201
inverse p201 = p120
inverse p210 = p210

undo : (p : Frame) (c : Color) → apply (inverse p) (apply p c) ≡ c
undo p012 c0 = refl
undo p012 c1 = refl
undo p012 c2 = refl
undo p021 c0 = refl
undo p021 c1 = refl
undo p021 c2 = refl
undo p102 c0 = refl
undo p102 c1 = refl
undo p102 c2 = refl
undo p120 c0 = refl
undo p120 c1 = refl
undo p120 c2 = refl
undo p201 c0 = refl
undo p201 c1 = refl
undo p201 c2 = refl
undo p210 c0 = refl
undo p210 c1 = refl
undo p210 c2 = refl

redo : (p : Frame) (c : Color) → apply p (apply (inverse p) c) ≡ c
redo p012 c0 = refl
redo p012 c1 = refl
redo p012 c2 = refl
redo p021 c0 = refl
redo p021 c1 = refl
redo p021 c2 = refl
redo p102 c0 = refl
redo p102 c1 = refl
redo p102 c2 = refl
redo p120 c0 = refl
redo p120 c1 = refl
redo p120 c2 = refl
redo p201 c0 = refl
redo p201 c1 = refl
redo p201 c2 = refl
redo p210 c0 = refl
redo p210 c1 = refl
redo p210 c2 = refl

different : Color → Color → Bool
different c0 c0 = false
different c0 c1 = true
different c0 c2 = true
different c1 c0 = true
different c1 c1 = false
different c1 c2 = true
different c2 c0 = true
different c2 c1 = true
different c2 c2 = false

permutation-invariant : (p : Frame) (a b : Color) → different (apply p a) (apply p b) ≡ different a b
permutation-invariant p012 c0 c0 = refl
permutation-invariant p012 c0 c1 = refl
permutation-invariant p012 c0 c2 = refl
permutation-invariant p012 c1 c0 = refl
permutation-invariant p012 c1 c1 = refl
permutation-invariant p012 c1 c2 = refl
permutation-invariant p012 c2 c0 = refl
permutation-invariant p012 c2 c1 = refl
permutation-invariant p012 c2 c2 = refl
permutation-invariant p021 c0 c0 = refl
permutation-invariant p021 c0 c1 = refl
permutation-invariant p021 c0 c2 = refl
permutation-invariant p021 c1 c0 = refl
permutation-invariant p021 c1 c1 = refl
permutation-invariant p021 c1 c2 = refl
permutation-invariant p021 c2 c0 = refl
permutation-invariant p021 c2 c1 = refl
permutation-invariant p021 c2 c2 = refl
permutation-invariant p102 c0 c0 = refl
permutation-invariant p102 c0 c1 = refl
permutation-invariant p102 c0 c2 = refl
permutation-invariant p102 c1 c0 = refl
permutation-invariant p102 c1 c1 = refl
permutation-invariant p102 c1 c2 = refl
permutation-invariant p102 c2 c0 = refl
permutation-invariant p102 c2 c1 = refl
permutation-invariant p102 c2 c2 = refl
permutation-invariant p120 c0 c0 = refl
permutation-invariant p120 c0 c1 = refl
permutation-invariant p120 c0 c2 = refl
permutation-invariant p120 c1 c0 = refl
permutation-invariant p120 c1 c1 = refl
permutation-invariant p120 c1 c2 = refl
permutation-invariant p120 c2 c0 = refl
permutation-invariant p120 c2 c1 = refl
permutation-invariant p120 c2 c2 = refl
permutation-invariant p201 c0 c0 = refl
permutation-invariant p201 c0 c1 = refl
permutation-invariant p201 c0 c2 = refl
permutation-invariant p201 c1 c0 = refl
permutation-invariant p201 c1 c1 = refl
permutation-invariant p201 c1 c2 = refl
permutation-invariant p201 c2 c0 = refl
permutation-invariant p201 c2 c1 = refl
permutation-invariant p201 c2 c2 = refl
permutation-invariant p210 c0 c0 = refl
permutation-invariant p210 c0 c1 = refl
permutation-invariant p210 c0 c2 = refl
permutation-invariant p210 c1 c0 = refl
permutation-invariant p210 c1 c1 = refl
permutation-invariant p210 c1 c2 = refl
permutation-invariant p210 c2 c0 = refl
permutation-invariant p210 c2 c1 = refl
permutation-invariant p210 c2 c2 = refl

-- X indexes all vertices other than the distinguished adjacent pair.
module Coloring (X : Type) where
  data Vertex : Type where
    left right : Vertex
    other : X → Vertex

  -- The first two distinct colours are encoded by the unique frame taking
  -- c0,c1 to that ordered pair. The remaining colours are arbitrary.
  Raw CanonicalWithFibre : Type
  Raw = Frame × (X → Color)
  CanonicalWithFibre = Frame × (X → Color)

  canonicalize : Raw → CanonicalWithFibre
  canonicalize (p , rest) = p , λ x → apply (inverse p) (rest x)

  restore : CanonicalWithFibre → Raw
  restore (p , rest) = p , λ x → apply p (rest x)

  restore-canonicalize : (r : Raw) → restore (canonicalize r) ≡ r
  restore-canonicalize (p , rest) = cong (p ,_) (funExt (λ x → redo p (rest x)))

  canonicalize-restore : (c : CanonicalWithFibre) → canonicalize (restore c) ≡ c
  canonicalize-restore (p , rest) = cong (p ,_) (funExt (λ x → undo p (rest x)))

  frame-presentation : Raw ≃ CanonicalWithFibre
  frame-presentation = isoToEquiv (iso canonicalize restore canonicalize-restore restore-canonicalize)

  rawRead : Raw → Vertex → Color
  rawRead (p , rest) left = apply p c0
  rawRead (p , rest) right = apply p c1
  rawRead (p , rest) (other x) = rest x

  canonicalRead : (X → Color) → Vertex → Color
  canonicalRead rest left = c0
  canonicalRead rest right = c1
  canonicalRead rest (other x) = rest x

  Edge : Type
  Edge = Vertex × Vertex

  valid : List Edge → (Vertex → Color) → Bool
  valid [] color = true
  valid ((u , v) ∷ edges) color = different (color u) (color v) and valid edges color

  valid-invariant : (edges : List Edge) (p : Frame) (color : Vertex → Color)
    → valid edges (λ v → apply p (color v)) ≡ valid edges color
  valid-invariant [] p color = refl
  valid-invariant ((u , v) ∷ edges) p color =
    cong₂ _and_ (permutation-invariant p (color u) (color v)) (valid-invariant edges p color)

  restored-reading : (c : CanonicalWithFibre) (v : Vertex)
    → rawRead (restore c) v ≡ apply (fst c) (canonicalRead (snd c) v)
  restored-reading (p , rest) left = refl
  restored-reading (p , rest) right = refl
  restored-reading (p , rest) (other x) = refl

  -- Evaluate only the canonical colouring; the entire frame fibre remains
  -- available for reconstruction. This proves the runtime factoring equation.
  factored-verdict : (edges : List Edge) (c : CanonicalWithFibre)
    → valid edges (rawRead (restore c)) ≡ valid edges (canonicalRead (snd c))
  factored-verdict edges (p , rest) =
    cong (valid edges) (funExt (restored-reading (p , rest)))
    ∙ valid-invariant edges p (canonicalRead rest)

  -- Continuing dynamics may be transported with the whole retained state.
  module Continuing (edges : List Edge) (step : Raw → Raw) where
    observation : Raw → Bool
    observation r = valid edges (rawRead r)
    retained-future : (r : Raw)
      → P.Orbit.mapO (P.Carrier.carry-transport observation) (P.Orbit.unfold step r)
        ≡ P.Orbit.unfold (P.Carrier.Φ-carrier observation step) (P.Carrier.descend observation r)
    retained-future = P.Nucleus.transport-orbit observation step

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

module SexticParityEliminant where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

module Sextic {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  A : Type ℓ
  A = fst R

  E : A → A → A → A
  E b d y = y · y · y + b · (y · y) + d · y + 1r

  O : A → A → A → A → A
  O a c e y = a · (y · y) + c · y + e

  sextic : A → A → A → A → A → A → A
  sextic a b c d e x =
      x · x · x · x · x · x
    + a · (x · x · x · x · x)
    + b · (x · x · x · x)
    + c · (x · x · x)
    + d · (x · x)
    + e · x
    + 1r

  sextic-shape : (a b c d e x : A)
    → E b d (x · x) + x · O a c e (x · x)
    ≡ sextic a b c d e x
  sextic-shape _ _ _ _ _ _ = solve! R

  sextic-reflect : (a b c d e x : A)
    → E b d (x · x) - x · O a c e (x · x)
    ≡ sextic a b c d e (- x)
  sextic-reflect _ _ _ _ _ _ = solve! R

  H : A → A → A → A → A → A → A
  H a b c d e y = E b d y · E b d y - y · (O a c e y · O a c e y)

  reflect-sextic : (a b c d e x : A)
    → sextic a b c d e x · sextic a b c d e (- x)
    ≡ H a b c d e (x · x)
  reflect-sextic _ _ _ _ _ _ = solve! R

  private
    det2 : A → A → A → A → A
    det2 m11 m12 m21 m22 = m11 · m22 - m12 · m21

    det3 : A → A → A → A → A → A → A → A → A → A
    det3 m11 m12 m13 m21 m22 m23 m31 m32 m33 =
        m11 · det2 m22 m23 m32 m33
      - m12 · det2 m21 m23 m31 m33
      + m13 · det2 m21 m22 m31 m32

    det4 : A → A → A → A
         → A → A → A → A
         → A → A → A → A
         → A → A → A → A → A
    det4 m11 m12 m13 m14
         m21 m22 m23 m24
         m31 m32 m33 m34
         m41 m42 m43 m44 =
        m11 · det3 m22 m23 m24 m32 m33 m34 m42 m43 m44
      - m12 · det3 m21 m23 m24 m31 m33 m34 m41 m43 m44
      + m13 · det3 m21 m22 m24 m31 m32 m34 m41 m42 m44
      - m14 · det3 m21 m22 m23 m31 m32 m33 m41 m42 m43

    det5 : A → A → A → A → A
         → A → A → A → A → A
         → A → A → A → A → A
         → A → A → A → A → A
         → A → A → A → A → A → A
    det5 m11 m12 m13 m14 m15
         m21 m22 m23 m24 m25
         m31 m32 m33 m34 m35
         m41 m42 m43 m44 m45
         m51 m52 m53 m54 m55 =
        m11 · det4 m22 m23 m24 m25
                   m32 m33 m34 m35
                   m42 m43 m44 m45
                   m52 m53 m54 m55
      - m12 · det4 m21 m23 m24 m25
                   m31 m33 m34 m35
                   m41 m43 m44 m45
                   m51 m53 m54 m55
      + m13 · det4 m21 m22 m24 m25
                   m31 m32 m34 m35
                   m41 m42 m44 m45
                   m51 m52 m54 m55
      - m14 · det4 m21 m22 m23 m25
                   m31 m32 m33 m35
                   m41 m42 m43 m45
                   m51 m52 m53 m55
      + m15 · det4 m21 m22 m23 m24
                   m31 m32 m33 m34
                   m41 m42 m43 m44
                   m51 m52 m53 m54

  -- The coefficient-order convention is explicit: two shifted rows of
  -- E = y^3 + b y^2 + d y + 1, followed by three shifted rows of
  -- O = a y^2 + c y + e.
  sylSextic : A → A → A → A → A → A
  sylSextic a b c d e =
    det5 1r b  d  1r 0r
         0r 1r b  d  1r
         a  c  e  0r 0r
         0r a  c  e  0r
         0r 0r a  c  e

  twice : A → A
  twice x = x + x

  thrice : A → A
  thrice x = x + x + x

  -- The displayed thirteen-term polynomial in SEXTIC_OBSTRUCTION.md (absent from this repository).
  D : A → A → A → A → A → A
  D a b c d e =
      a · a · a
    - twice (a · a · b · e)
    - a · a · c · d
    + a · a · d · d · e
    + a · b · b · e · e
    + a · b · c · c
    - a · b · c · d · e
    + thrice (a · c · e)
    - twice (a · d · e · e)
    - b · c · e · e
    - c · c · c
    + c · c · d · e
    + e · e · e

  syl-sextic-closed : (a b c d e : A)
    → sylSextic a b c d e ≡ D a b c d e
  syl-sextic-closed _ _ _ _ _ = solve! R

  -- Supplying the factorized quadratic is the honest root-presentation
  -- hypothesis; no roots are extracted and no division by a is used.
  O-factorized : (a y₁ y₂ y : A)
    → O a (- (a · (y₁ + y₂))) (a · (y₁ · y₂)) y
    ≡ a · (y - y₁) · (y - y₂)
  O-factorized _ _ _ _ = solve! R

  res-sextic-roots : (a b d y₁ y₂ : A)
    → a · a · a · (E b d y₁ · E b d y₂)
    ≡ D a b (- (a · (y₁ + y₂))) d (a · (y₁ · y₂))
  res-sextic-roots _ _ _ _ _ = solve! R

  -- A degenerate leading-coefficient control catches a coefficient/sign
  -- transcription error in the explicit Sylvester convention.
  degenerate-D-sign : D 0r 0r 1r 0r 0r ≡ - 1r
  degenerate-D-sign = solve! R

  degenerate-sylvester-sign : sylSextic 0r 0r 1r 0r 0r ≡ - 1r
  degenerate-sylvester-sign =
    syl-sextic-closed 0r 0r 1r 0r 0r ∙ degenerate-D-sign

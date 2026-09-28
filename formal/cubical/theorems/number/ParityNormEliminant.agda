{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ParityNormEliminant
--
-- The exact algebra underneath the parity/resultant lane of this corpus:
--
-- Those notes compute, by hand, one degree-10 reflection product, a 3x3
-- and a 4x4 Sylvester determinant, and a norm-multiplicativity step; and
-- every later stage (the coefficient boxes, the 1591-solution
-- enumeration, the 18 surviving quintic candidates, the 62/46/26/24
-- quartic filtration) rests on those four being right.  Each is a finite
-- exact identity over an arbitrary commutative ring, so under CLAUDE.md (absent from this repository)
-- it is provable rather than measurable, and it is proved here.
--
-- Everything is stated over an arbitrary CommRing, not over Z.  That is
-- not decoration: the identities are formal, and proving them formally
-- is what lets them be reused modulo any prime and over any coefficient
-- domain.  (It is also what the pinned solver can actually do -- the
-- v0.5 CommRingSolver does not reduce `1r` at the concrete `ZCommRing`
-- instance, but handles it fine at a variable ring.)
------------------------------------------------------------------------

module ParityNormEliminant where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

module Parity {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  A : Type ℓ
  A = fst R

  ----------------------------------------------------------------------
  -- 1.  The parity decomposition and its norm
  --
  -- Every p in A[x] splits as p(x) = e(x^2) + x o(x^2).  Write the pair
  -- (e , o) for the split.  Two operations act on such pairs:
  --
  --   reflection   x |-> -x        (e , o) |-> (e , -o)
  --   the norm     N(e,o) = e^2 - y o^2   at  y = x^2 .
  --
  -- The norm is the eliminant: it turns a divisibility question in x
  -- into one in y = x^2, of half the degree.
  ----------------------------------------------------------------------

  -- p(x) q(x) where p = e + x o and q = u + x v: the parity split of a
  -- product.  This is PARITY_RESULTANT (5.1)'s source identity -- the
  -- even part of the product is  e u + y o v,  the odd part  e v + o u.
  parity-mult : (e o u v x : A)
    → (e + x · o) · (u + x · v)
    ≡ (e · u + (x · x) · (o · v)) + x · (e · v + o · u)
  parity-mult _ _ _ _ _ = solve! R

  -- p(x) p(-x) = N(y) at y = x^2.  Not special to any degree: it is the
  -- difference of squares in the parity split.  QUINTIC_OBSTRUCTION
  -- (1.3) and PARITY_RESULTANT's H are instances.
  reflect-norm : (e o x : A)
    → (e + x · o) · (e - x · o) ≡ e · e - (x · x) · (o · o)
  reflect-norm _ _ _ = solve! R

  -- THE NORM IS MULTIPLICATIVE.  With composition
  --     (e , o) * (u , v) = (e u + y o v ,  e v + o u)
  -- reading off `parity-mult`, one has
  --     N((e,o)*(u,v)) = N(e,o) N(u,v).
  -- This is Brahmagupta's composition law for the form X^2 - y Y^2, and
  -- it is exactly why p |-> N_p carries the factorisation of a
  -- prime-prefix polynomial to a factorisation of one fixed polynomial
  norm-mult : (e o u v y : A)
    →   ((e · u + y · (o · v)) · (e · u + y · (o · v)))
      - y · ((e · v + o · u) · (e · v + o · u))
    ≡ (e · e - y · (o · o)) · (u · u - y · (v · v))
  norm-mult _ _ _ _ _ = solve! R

  -- The parity identity of the prime-prefix family: with P = 1 + x A(x^2)
  -- (the shape forced by "every prime above 2 is odd"), P(x) + P(-x) = 2
  -- and the reflection norm of P is 1 - y A(y)^2, a polynomial in y that
  -- involves no candidate factor at all.  (Here `a` stands for the value
  -- A(x^2); substituting that value is what makes the right-hand side
  -- N_X evaluated at y = x^2.)
  parity-identity : (a x : A) → (1r + x · a) + (1r - x · a) ≡ 1r + 1r
  parity-identity _ _ = solve! R

  norm-of-prefix : (a x : A)
    → (1r + x · a) · (1r - x · a) ≡ 1r - (x · x) · (a · a)
  norm-of-prefix _ _ = solve! R

  ----------------------------------------------------------------------
  -- 2.  The two shapes the corpus needs
  --
  --   quartic  g = x^4 + a x^3 + b x^2 + c x + 1 ,  E = y^2+by+1, O = ay+c
  --   quintic  g = x^5 + a x^4 + b x^3 + c x^2 + d x + 1 ,
  --                                        E = ay^2+cy+1, O = y^2+by+d
  --
  -- The `-shape` lemmas certify that these E and O really are the even
  -- and odd parts of the advertised monic polynomial.  They are stated
  -- with y free and then specialised at y = x·x by the monomial lemmas,
  -- which is exactly the substitution the notes perform silently.
  ----------------------------------------------------------------------

  Eq : A → A → A → A                   -- quintic even part
  Eq a c y = a · (y · y) + c · y + 1r

  Oq : A → A → A → A                   -- quintic odd part
  Oq b d y = y · y + b · y + d

  Ec : A → A → A                       -- quartic even part
  Ec b y = y · y + b · y + 1r

  Oc : A → A → A → A                   -- quartic odd part
  Oc a c y = a · y + c

  -- the advertised monic polynomials
  quintic : A → A → A → A → A → A
  quintic a b c d x =
    x · x · x · x · x + a · (x · x · x · x) + b · (x · x · x) + c · (x · x) + d · x + 1r

  quartic : A → A → A → A → A
  quartic a b c x = x · x · x · x + a · (x · x · x) + b · (x · x) + c · x + 1r

  -- E and O really are its even and odd parts, at y = x^2
  quintic-shape : (a b c d x : A)
    → Eq a c (x · x) + x · Oq b d (x · x) ≡ quintic a b c d x
  quintic-shape _ _ _ _ _ = solve! R

  quartic-shape : (a b c x : A)
    → Ec b (x · x) + x · Oc a c (x · x) ≡ quartic a b c x
  quartic-shape _ _ _ _ = solve! R

  -- and negating x negates exactly the odd part, i.e. the second factor of
  -- the reflection product is literally g(-x)
  quintic-reflect : (a b c d x : A)
    → Eq a c (x · x) - x · Oq b d (x · x) ≡ quintic a b c d (- x)
  quintic-reflect _ _ _ _ _ = solve! R

  quartic-reflect : (a b c x : A)
    → Ec b (x · x) - x · Oc a c (x · x) ≡ quartic a b c (- x)
  quartic-reflect _ _ _ _ = solve! R

  -- the two reflection norms, as the notes write them
  Hq : A → A → A → A → A → A
  Hq a b c d y = Eq a c y · Eq a c y - y · (Oq b d y · Oq b d y)

  Hc : A → A → A → A → A
  Hc a b c y = Ec b y · Ec b y - y · (Oc a c y · Oc a c y)

  -- The reflection identity in fully explicit coefficient form: for the
  -- general monic quintic (resp. quartic) with constant term 1,
  --
  --     g(x) * g(-x) = H(x^2),
  --
  -- with no substitution left to the reader.  This is QUINTIC_OBSTRUCTION
  -- (1.3) and the H of PARITY_RESULTANT (5.2), verbatim.  It is a degree-10
  -- (resp. degree-8) identity in five (resp. four) indeterminates.
  reflect-quintic : (a b c d x : A)
    → quintic a b c d x · quintic a b c d (- x) ≡ Hq a b c d (x · x)
  reflect-quintic _ _ _ _ _ = solve! R

  reflect-quartic : (a b c x : A)
    → quartic a b c x · quartic a b c (- x) ≡ Hc a b c (x · x)
  reflect-quartic _ _ _ _ = solve! R

  ----------------------------------------------------------------------
  -- 3.  The two resultants, each computed twice
  --
  -- QUINTIC_OBSTRUCTION (1.5):  Res_y(O,E) = (1-ad)^2 - (c-ab)(b-cd)
  --                             for O = y^2+by+d, E = ay^2+cy+1
  -- PARITY_RESULTANT   (2.3):   Res_y(O,E) = a^2 - abc + c^2
  --                             for O = ay+c,     E = y^2+by+1
  --
  -- Both are certified in the two independent presentations a resultant
  -- has: the Sylvester determinant (no roots extracted) and the product
  -- of E over the roots of O (the form the notes actually argue with).
  -- Their agreement is a theorem, not a definition, so proving each side
  -- separately pins the closed form and would catch a sign slip or a
  -- transposed Sylvester matrix in either note.
  ----------------------------------------------------------------------

  Dq : A → A → A → A → A
  Dq a b c d = (1r - a · d) · (1r - a · d) - (c - a · b) · (b - c · d)

  Dc : A → A → A → A
  Dc a b c = a · a - a · (b · c) + c · c

  private
    det3 : A → A → A → A → A → A → A → A → A → A
    det3 m₁₁ m₁₂ m₁₃ m₂₁ m₂₂ m₂₃ m₃₁ m₃₂ m₃₃ =
        m₁₁ · (m₂₂ · m₃₃ - m₂₃ · m₃₂)
      - m₁₂ · (m₂₁ · m₃₃ - m₂₃ · m₃₁)
      + m₁₃ · (m₂₁ · m₃₂ - m₂₂ · m₃₁)

  -- Syl(O,E) for two quadratics, O = y^2+by+d and E = ay^2+cy+1:
  --
  --     [ 1 b d 0 ]
  --     [ 0 1 b d ]
  --     [ a c 1 0 ]
  --     [ 0 a c 1 ]
  --
  -- Laplace expansion down column 1 (nonzero in rows 1 and 3, cofactor
  -- signs + and +).
  sylQuintic : A → A → A → A → A
  sylQuintic a b c d =
      det3 1r b  d    c  1r 0r   a  c  1r
    + a · det3 b  d  0r   1r b  d    a  c  1r

  syl-quintic-closed : (a b c d : A) → sylQuintic a b c d ≡ Dq a b c d
  syl-quintic-closed _ _ _ _ = solve! R

  -- Syl(O,E) for O = ay+c (degree 1) and E = y^2+by+1 (degree 2):
  --
  --     [ a c 0 ]
  --     [ 0 a c ]
  --     [ 1 b 1 ]
  sylQuartic : A → A → A → A
  sylQuartic a b c = det3 a c 0r   0r a c   1r b 1r

  syl-quartic-closed : (a b c : A) → sylQuartic a b c ≡ Dc a b c
  syl-quartic-closed _ _ _ = solve! R

  -- The same two quantities as products of E over the roots of O.  No
  -- roots are postulated: the roots are presented as indeterminates
  -- y1, y2 and the coefficients of O are their elementary symmetric
  -- functions, b = -(y1+y2), d = y1 y2.
  res-quintic-roots : (a c y₁ y₂ : A)
    → Eq a c y₁ · Eq a c y₂ ≡ Dq a (- (y₁ + y₂)) c (y₁ · y₂)
  res-quintic-roots _ _ _ _ = solve! R

  -- For the quartic, O = a y + c has the single root y0 with a y0 = -c,
  -- and Res(O,E) = a^2 E(y0).  Presenting the root as y0 and c as -(a y0):
  res-quartic-root : (a b y₀ : A)
    → a · a · Ec b y₀ ≡ Dc a b (- (a · y₀))
  res-quartic-root _ _ _ = solve! R

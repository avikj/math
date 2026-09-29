{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- भावना — क्षेपो मूलाभ्यां निर्धार्यते, समासे च गुण्यते ।
-- (composition: the interpolator is determined by the two roots, and
--  composing multiplies it.)
--
-- SOURCES.
--
--   Brahmagupta, *Brāhmasphuṭasiddhānta*, chapter 18 (कुट्टकाध्याय), 628
--   CE — the भावना, the composition law for वर्गप्रकृति, the "square-
--   nature" equation.  The vocabulary used below is his: प्रकृति for the
--   multiplier D, ज्येष्ठ for the greater root a, कनिष्ठ for the lesser
--   root b, क्षेप for the interpolator k in
--
--       ज्येष्ठ² − प्रकृति · कनिष्ठ² = क्षेप          (a² − D b² = k)
--
--   and समास-भावना for the composition of two such rows.
--
--   Jayadeva (c. 950, surviving only inside Udayadivkara's *Sundar*
--   commentary) and Bhāskara II, *Bījagaṇita*, 1150 — the चक्रवाल, the
--   cyclic method, which is the algorithm that repeatedly applies this
--   composition against a chosen multiplier and divides through by the
--   current क्षेप.
--
-- CLAIMED OF THE SOURCES: that a² − D b²
-- is the quantity their algorithms carry alongside the pair of roots, and
-- that it is a FUNCTION of that pair, which is why it belongs in the
-- carried slot and not in the base.
--
------------------------------------------------------------------------
-- WHICH SLOTS ARE BASE AND WHICH ARE CARRIED.
--
-- Exact, with no residue.  The base is the pair of roots
-- (ज्येष्ठ , कनिष्ठ) : ℤ × ℤ, genuinely two independent integers.  The
-- क्षेप is carried:
--
--     क्षेपः D (a , b)  =  a · a − D · (b · b)
--     वर्गप्रकृति D      =  Carrier (क्षेपः D)
--
-- with base = (a , b), carried = k, and witness : क्षेपः D (a , b) ≡ k.
-- The fibre is Σ[ k ∈ ℤ ] (क्षेपः D (a , b) ≡ k) = singl (क्षेपः D (a , b)),
-- contractible, so (ℤ × ℤ) ≃ वर्गप्रकृति D and, by univalence,
-- (ℤ × ℤ) ≡ वर्गप्रकृति D.
--
-- This is the clean case, and the contrast with the kuaka module in
-- this same library is the point: there, none of the three slots was a
-- function of the other two and all three had to stay in the base.  Here
-- the third slot is exactly a function of the first two, so it may be
-- carried — present as a real projectable term, contributing no degree of
-- freedom.
--
-- THE STEP.  समास-भावना against a fixed row (p , q) is an endomorphism of
-- the base:
--
--     भावना (p , q) (a , b)  =  (a·p + D·(b·q) , a·q + b·p)
--
-- It lifts by `Φ-carrier`, and `Φ-square` closes DEFINITIONALLY — it is
-- `refl` for an opaque variable, since Σ has eta and `descend` does not
-- pattern match.  That is the law being instantiated, not re-proved.
--
-- THE ARITHMETIC CONTENT, which the law does not give and which is proved
-- here by hand: `भावना-क्षेपः`, Brahmagupta's identity
--
--     क्षेपः D (भावना (p,q) (a,b))  ≡  क्षेपः D (a,b) · क्षेपः D (p,q)
--
-- so the carried datum of the lifted step is the PRODUCT of the two
-- क्षेप.  That is what makes the method work: composing a row of क्षेप k
-- with itself gives k², and dividing through by it is what the चक्रवाल is
-- driving at.
--
-- Brahmagupta's identity is proved by hand, from
-- +Assoc / +Comm / ·Assoc / ·Comm / ·DistL+ / ·DistR+ / -Dist+ /
-- -DistL· / -DistR· / -DistLR· / -Cancel / pos0+ only.  A commutative
-- ring solver would do it in one line, but the solver's module path
-- differs between agda/cubical v0.5 (`Cubical.Algebra.CommRingSolver.*`)
-- and later releases (`Cubical.Tactics.CommRingSolver`), so using it
-- would pin this file to one of them.  Every lemma named above is present
-- and identically typed in both.
------------------------------------------------------------------------

module Fibre.Composition_TheKsepaIsDeterminedByTheRootsAndCompositionMultipliesIt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Int
  using ( ℤ; pos; negsuc; _+_; _-_; -_; _·_
        ; +Assoc; +Comm; ·Assoc; ·Comm; ·DistL+; ·DistR+
        ; -Dist+; -DistL·; -DistR·; -DistLR·; -Cancel; pos0+ )
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)

open import Fibre.Carrier
open import Fibre.Orbit
open import Fibre.Nucleus

------------------------------------------------------------------------
-- A commutative-ring toolkit, small and reused.  Nothing here is about
-- वर्गप्रकृति; it is the rearrangement the identity needs.
------------------------------------------------------------------------

private
  -- pull the head of a product past the head of its tail
  बहिः : (x y z : ℤ) → x · (y · z) ≡ y · (x · z)
  बहिः x y z = ·Assoc x y z ∙ cong (_· z) (·Comm x y) ∙ sym (·Assoc y x z)

  -- मध्यविनिमय, the middle exchange: (w·x)·(y·z) ≡ (w·y)·(x·z)
  मध्यविनिमय : (w x y z : ℤ) → (w · x) · (y · z) ≡ (w · y) · (x · z)
  मध्यविनिमय w x y z =
      sym (·Assoc w x (y · z))
    ∙ cong (w ·_) (बहिः x y z)
    ∙ ·Assoc w y (x · z)

  -- the same two moves for +
  +बहिः : (x y z : ℤ) → x + (y + z) ≡ y + (x + z)
  +बहिः x y z = +Assoc x y z ∙ cong (_+ z) (+Comm x y) ∙ sym (+Assoc y x z)

  विनिमय : (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  विनिमय a b c d =
      sym (+Assoc a b (c + d))
    ∙ cong (a +_) (+बहिः b c d)
    ∙ +Assoc a c (b + d)

  विनिमय' : (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + d) + (b + c)
  विनिमय' a b c d = cong ((a + b) +_) (+Comm c d) ∙ विनिमय a b d c

  शून्यम् : (x : ℤ) → x + pos 0 ≡ x
  शून्यम् x = +Comm x (pos 0) ∙ sym (pos0+ x)

  -- कर्तन: a term and its negative delete each other out of a sum.
  कर्तन : (g h k : ℤ) → (g + h) + (k + (- h)) ≡ g + k
  कर्तन g h k =
      विनिमय g h k (- h)
    ∙ cong ((g + k) +_) (-Cancel h)
    ∙ शून्यम् (g + k)

  -- the square of a sum, already sorted into diagonal and cross terms
  वर्गयोगः : (u v : ℤ) → (u + v) · (u + v) ≡ (u · u + v · v) + (u · v + v · u)
  वर्गयोगः u v =
      ·DistL+ u v (u + v)
    ∙ cong₂ _+_ (·DistR+ u u v) (·DistR+ v u v)
    ∙ विनिमय' (u · u) (u · v) (v · u) (v · v)

------------------------------------------------------------------------
-- क्षेपः — the interpolator, as a function of the two roots.  THIS is the
-- f of the law.  The pair is the base; k is what the pair determines.
------------------------------------------------------------------------

क्षेपः : ℤ → ℤ × ℤ → ℤ
क्षेपः D x = fst x · fst x - D · (snd x · snd x)

module _ (D : ℤ) where

  वर्गप्रकृति : Type
  वर्गप्रकृति = Carrier (क्षेपः D)

  -- the three coordinates: two base, one carried
  ज्येष्ठ : वर्गप्रकृति → ℤ
  ज्येष्ठ c = fst (base c)

  कनिष्ठ : वर्गप्रकृति → ℤ
  कनिष्ठ c = snd (base c)

  क्षेप : वर्गप्रकृति → ℤ
  क्षेप c = carried c

  प्रमाण : (c : वर्गप्रकृति)
         → ज्येष्ठ c · ज्येष्ठ c - D · (कनिष्ठ c · कनिष्ठ c) ≡ क्षेप c
  प्रमाण c = witness c

  -- the fibre is singl, hence contractible: k adds no degree of freedom
  क्षेप-क्षेत्र-सम्पूर्ण : (x : ℤ × ℤ) → isContr (fibre (क्षेपः D) x)
  क्षेप-क्षेत्र-सम्पूर्ण = fibre-isContr (क्षेपः D)

  युग्म-Iso-वर्गप्रकृति : Iso (ℤ × ℤ) वर्गप्रकृति
  युग्म-Iso-वर्गप्रकृति = Carrier-Iso (क्षेपः D)

  युग्म≃वर्गप्रकृति : (ℤ × ℤ) ≃ वर्गप्रकृति
  युग्म≃वर्गप्रकृति = Carrier≃ (क्षेपः D)

  युग्म≡वर्गप्रकृति : (ℤ × ℤ) ≡ वर्गप्रकृति
  युग्म≡वर्गप्रकृति = Carrier≡ (क्षेपः D)

  अवतरण : ℤ × ℤ → वर्गप्रकृति
  अवतरण = descend (क्षेपः D)

  आरोहः : वर्गप्रकृति → ℤ × ℤ
  आरोहः = ascend (क्षेपः D)

  परिवहन : ℤ × ℤ → वर्गप्रकृति
  परिवहन = carry-transport (क्षेपः D)

  परिवहन-अवतरण : (x : ℤ × ℤ) → परिवहन x ≡ अवतरण x
  परिवहन-अवतरण = carry-transport-descend (क्षेपः D)

  ----------------------------------------------------------------------
  -- समास-भावना — composition against a fixed row, as a Φ on the base.
  ----------------------------------------------------------------------

  module _ (p q : ℤ) where

    भावना : ℤ × ℤ → ℤ × ℤ
    भावना x = (fst x · p + D · (snd x · q)) , (fst x · q + snd x · p)

    --------------------------------------------------------------------
    -- Brahmagupta's identity.  Proved by hand; see the header.
    --
    --   (a² − D b²)(p² − D q²) = (ap + D bq)² − D (aq + bp)²
    --
    -- The two cross monomials a·p · D·(b·q) and D · (a·q · b·p) are the
    -- SAME monomial, and `कर्तन` is where they delete each other.
    --------------------------------------------------------------------

    भावना-क्षेपः : (a b : ℤ)
                → क्षेपः D (भावना (a , b)) ≡ क्षेपः D (a , b) · क्षेपः D (p , q)
    भावना-क्षेपः a b = वाम ∙ sym दक्षिण
      where
        A B C E X Y Z W : ℤ
        A = a · p
        B = D · (b · q)
        C = a · q
        E = b · p
        X = a · a
        Y = D · (b · b)
        Z = p · p
        W = D · (q · q)

        -- the four surviving monomials
        AA : A · A ≡ X · Z
        AA = मध्यविनिमय a p a p

        BB : B · B ≡ Y · W
        BB = मध्यविनिमय D (b · q) D (b · q)
           ∙ cong ((D · D) ·_) (मध्यविनिमय b q b q)
           ∙ मध्यविनिमय D D (b · b) (q · q)

        DCC : D · (C · C) ≡ X · W
        DCC = cong (D ·_) (मध्यविनिमय a q a q) ∙ बहिः D (a · a) (q · q)

        DEE : D · (E · E) ≡ Y · Z
        DEE = cong (D ·_) (मध्यविनिमय b p b p) ∙ ·Assoc D (b · b) (p · p)

        -- the two cross monomials, both normalised to (a·b) · (D · (p·q))
        AB : A · B ≡ (a · b) · (D · (p · q))
        AB = मध्यविनिमय a p D (b · q)
           ∙ cong ((a · D) ·_) (बहिः p b q)
           ∙ मध्यविनिमय a D b (p · q)

        DCE : D · (C · E) ≡ (a · b) · (D · (p · q))
        DCE = cong (D ·_) (मध्यविनिमय a q b p)
            ∙ बहिः D (a · b) (q · p)
            ∙ cong ((a · b) ·_) (cong (D ·_) (·Comm q p))

        -- the cross terms of the two sides agree exactly
        तिर्यक् : (A · B + B · A) ≡ (D · (C · E) + D · (E · C))
        तिर्यक् = cong₂ _+_
                   (AB ∙ sym DCE)
                   (·Comm B A ∙ AB ∙ sym DCE ∙ cong (D ·_) (·Comm C E))

        -- expand D · (aq + bp)² into diagonal + cross
        ऋण : D · ((C + E) · (C + E))
           ≡ (D · (C · C) + D · (E · E)) + (D · (C · E) + D · (E · C))
        ऋण = cong (D ·_) (वर्गयोगः C E)
           ∙ ·DistR+ D (C · C + E · E) (C · E + E · C)
           ∙ cong₂ _+_ (·DistR+ D (C · C) (E · E)) (·DistR+ D (C · E) (E · C))

        सामान्यम् : ℤ
        सामान्यम् = (X · Z + - (X · W)) + (- (Y · Z) + Y · W)

        वाम : क्षेपः D (भावना (a , b)) ≡ सामान्यम्
        वाम =
            cong₂ _+_ (वर्गयोगः A B) (cong -_ (ऋण ∙ sym (cong ((D · (C · C) + D · (E · E)) +_) तिर्यक्)))
          ∙ cong ((A · A + B · B) + (A · B + B · A) +_)
                 (-Dist+ (D · (C · C) + D · (E · E)) (A · B + B · A))
          ∙ कर्तन (A · A + B · B) (A · B + B · A) (- (D · (C · C) + D · (E · E)))
          ∙ cong₂ _+_ (cong₂ _+_ AA BB) (cong -_ (cong₂ _+_ DCC DEE))
          ∙ cong ((X · Z + Y · W) +_) (-Dist+ (X · W) (Y · Z))
          ∙ विनिमय (X · Z) (Y · W) (- (X · W)) (- (Y · Z))
          ∙ cong ((X · Z + - (X · W)) +_) (+Comm (Y · W) (- (Y · Z)))

        दक्षिण : क्षेपः D (a , b) · क्षेपः D (p , q) ≡ सामान्यम्
        दक्षिण =
            ·DistL+ X (- Y) (Z + (- W))
          ∙ cong₂ _+_ (·DistR+ X Z (- W)) (·DistR+ (- Y) Z (- W))
          ∙ cong₂ _+_ (cong ((X · Z) +_) (sym (-DistR· X W)))
                      (cong₂ _+_ (sym (-DistL· Y Z)) (sym (-DistLR· Y W)))

    --------------------------------------------------------------------
    -- THE LIFT, AND THE SQUARE.  Both are instances of the law; neither
    -- is proved in this file.  Φ-square is refl, definitionally, opaque
    -- argument.
    --------------------------------------------------------------------

    भावना-वर्गप्रकृति : वर्गप्रकृति → वर्गप्रकृति
    भावना-वर्गप्रकृति = Φ-carrier (क्षेपः D) भावना

    भावना-वर्गः : (x : ℤ × ℤ) → भावना-वर्गप्रकृति (अवतरण x) ≡ अवतरण (भावना x)
    भावना-वर्गः = Φ-square (क्षेपः D) भावना

    भावना-आरोहः : (c : वर्गप्रकृति) → आरोहः (भावना-वर्गप्रकृति c) ≡ भावना (आरोहः c)
    भावना-आरोहः = Φ-ascend (क्षेपः D) भावना

    भावना-परिवहन : (x : ℤ × ℤ) → परिवहन (भावना x) ≡ अवतरण (भावना x)
    भावना-परिवहन = Φ-transport (क्षेपः D) भावना

    -- the two halves joined: the carried datum of the LIFTED step is the
    -- product of the two क्षेप.  The law supplies that the datum is
    -- recomputed; Brahmagupta supplies what it recomputes to.
    भावना-क्षेप-लब्धः : (x : ℤ × ℤ)
                     → क्षेप (भावना-वर्गप्रकृति (अवतरण x))
                     ≡ क्षेपः D x · क्षेपः D (p , q)
    भावना-क्षेप-लब्धः x = भावना-क्षेपः (fst x) (snd x)

    -- the whole cascade of compositions, as one object
    भावना-जाल : Type
    भावना-जाल = Orbit वर्गप्रकृति

    बुन : ℤ × ℤ → भावना-जाल
    बुन x = unfold भावना-वर्गप्रकृति (अवतरण x)

    -- the n-th row is the n-th composition, descended
    भावना-निरीक्षण : (x : ℤ × ℤ) (n : ℕ)
                  → lookup (बुन x) n ≡ अवतरण (iterate भावना n x)
    भावना-निरीक्षण = orbit-lookup (क्षेपः D) भावना

------------------------------------------------------------------------
-- IT RUNS.  D = 2, the row (3 , 2): 3² − 2·2² = 9 − 8 = 1.
-- Composing it with itself gives (3·3 + 2·(2·2) , 3·2 + 2·3) = (17 , 12),
-- and 17² − 2·12² = 289 − 288 = 1 = 1 · 1.
--
-- Each holds by refl, so Agda must execute the arithmetic in ℤ.
------------------------------------------------------------------------

गणना-मूलम् : क्षेपः (pos 2) (pos 3 , pos 2) ≡ pos 1
गणना-मूलम् = refl

गणना-भावना : भावना (pos 2) (pos 3) (pos 2) (pos 3 , pos 2) ≡ (pos 17 , pos 12)
गणना-भावना = refl

गणना-क्षेपः : क्षेपः (pos 2) (भावना (pos 2) (pos 3) (pos 2) (pos 3 , pos 2)) ≡ pos 1
गणना-क्षेपः = refl

-- the same number, but obtained from the identity rather than from
-- normalisation: this one is NOT refl, it is Brahmagupta's theorem
गणना-गुणनम् : क्षेपः (pos 2) (भावना (pos 2) (pos 3) (pos 2) (pos 3 , pos 2))
            ≡ क्षेपः (pos 2) (pos 3 , pos 2) · क्षेपः (pos 2) (pos 3 , pos 2)
गणना-गुणनम् = भावना-क्षेपः (pos 2) (pos 3) (pos 2) (pos 3) (pos 2)

-- a row whose क्षेप is not ±1: D = 7, (3 , 1) has 9 − 7 = 2, and
-- composing it with itself gives क्षेप 4.
गणना-सप्त : क्षेपः (pos 7) (pos 3 , pos 1) ≡ pos 2
गणना-सप्त = refl

गणना-सप्त-भावना : क्षेपः (pos 7) (भावना (pos 7) (pos 3) (pos 1) (pos 3 , pos 1)) ≡ pos 4
गणना-सप्त-भावना = refl

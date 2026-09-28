{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- - — the bridge into the forest.  The Liouville/parity program's
-- The Liouville/parity program's exact arithmetic
-- interface as a checked cubical term, orthogonal to the fibre/transport
-- spine.  Two facts, both exact, no numerics:
--
--   §1  THE SHIFT–DILATION INTERFACE.  On sequences X = ℕ → A with the
--       shift (σ x)(n) = x(n+1) and the dilations (D_m x)(n) = x(m·n),
--       FOREST.md (absent from this repository) §1 states the exact commutation that governs the whole
--       program — the multiplicative dilations do NOT preserve the
--       additive shift, and the exact defect is:
--
--           σ ∘ D_m  ≡  D_m ∘ σ^m                    (checked here)
--
--       i.e. shifting a dilated sequence by one is dilating a sequence
--       shifted by m.  This is the σ D_m = D_m σ^m of FOREST.md (absent from this repository)/DIRECT.md (absent from this repository),
--       and it is the reason M (the multiplicative eigenvectors) is not
--       shift-invariant — the interface the whole Liouville question
--       turns on.
--
--   §2  THE LIOUVILLE POINT IS AN EIGENVECTOR OF EVERY DILATION.  For a
--       completely multiplicative sign sequence (x(m·n) = x(m)·x(n),
--       here over the sign group (Bool, xor) with -1 = true), FOREST.md (absent from this repository)'s
--       characterisation D_p λ = -λ becomes, exactly: if x(m) = -1 then
--       D_m x = -x pointwise.  The Liouville function is the point with
--       x(p) = -1 at every prime; §2 proves the eigen-relation from
--       complete multiplicativity alone, at ANY m with x(m) = -1, no
--       primality needed for the algebra.
--
-- TERM.  The forest and its objects are the corpus's (FOREST.md (absent from this repository)).
-- Signs live in
-- (Bool, _xor_): false = +1, true = -1, so multiplication of signs is
-- xor and "negate" is `not`.  Exact, finite, --safe.
------------------------------------------------------------------------

module VanaSetu_TheShiftDilationInterfaceAndTheLiouvillePointIsTheAllMinusOneEigenvector where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; ·-suc; +-suc)
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; not; ⊕-comm)

private
  variable
    ℓ : Level

-- sequences over a value type A, indexed by ℕ.
Seq : Type ℓ → Type ℓ
Seq A = ℕ → A

module _ {A : Type ℓ} where

  -- the additive shift σ.
  σ : Seq A → Seq A
  σ x n = x (suc n)

  -- its iterate σ^m.
  σ^ : ℕ → Seq A → Seq A
  σ^ zero    x = x
  σ^ (suc m) x = σ (σ^ m x)

  -- σ^m reads m steps ahead: (σ^ m x) k = x (m + k).
  σ^-index : (m : ℕ) (x : Seq A) (k : ℕ) → σ^ m x k ≡ x (m + k)
  σ^-index zero    x k = refl
  σ^-index (suc m) x k = σ^-index m x (suc k) ∙ cong x (+-suc m k)

  -- the multiplicative dilation D_m.
  D : ℕ → Seq A → Seq A
  D m x n = x (m · n)

------------------------------------------------------------------------
-- §1 · THE INTERFACE:  σ ∘ D_m ≡ D_m ∘ σ^m.

  interface : (m : ℕ) (x : Seq A) → σ (D m x) ≡ D m (σ^ m x)
  interface m x i n = pf n i
    where
    pf : (n : ℕ) → σ (D m x) n ≡ D m (σ^ m x) n
    pf n =
      -- σ (D m x) n = x (m · suc n)
      cong x (·-suc m n)                       -- x (m · suc n) ≡ x (m + m · n)
      ∙ sym (σ^-index m x (m · n))             -- ≡ σ^ m x (m · n) = D m (σ^ m x) n

------------------------------------------------------------------------
-- §2 · THE LIOUVILLE EIGEN-RELATION, over the sign group (Bool, ⊕).
-- false = +1, true = −1; sign multiplication is ⊕; negation is `not`.

Sign : Type
Sign = Bool

-- a sequence is completely multiplicative if x(m·n) = x(m) ⊕ x(n).
CompletelyMult : Seq Sign → Type
CompletelyMult x = (m n : ℕ) → x (m · n) ≡ (x m) ⊕ (x n)

-- negating a sign: multiply by −1.  Over ⊕, −1 = true, and true ⊕ b = not b.
neg : Sign → Sign
neg = not

-- THE THEOREM.  If x is completely multiplicative and x(m) = −1 (true),
-- then D_m x = −x pointwise: dilating by an index of sign −1 flips every
-- sign.  The Liouville function (x p = −1 at every prime) is the special
-- point; the algebra needs only x(m) = −1.
liouville-eigen : (x : Seq Sign) → CompletelyMult x
  → (m : ℕ) → x m ≡ true
  → (n : ℕ) → D m x n ≡ neg (x n)
liouville-eigen x mult m em n =
  mult m n              -- x (m · n) ≡ x m ⊕ x n
  ∙ cong (_⊕ x n) em    -- ≡ true ⊕ x n
                        -- true ⊕ x n ≡ not (x n) definitionally

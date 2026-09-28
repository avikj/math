{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- NaturalMachine.GaugeOrbitClasses
--
-- TARGET.md (absent from this repository)'s headline is "make the parity barrier a theorem about
-- OBSERVABLE CLASSES".  `ParitySeparator` and `ChargeCriterion` deliver a
-- theorem about ONE PAIR: the all-plus assignment σ₊ and its total gauge
-- flip.  Everything they say is correct; but a statement about one orbit
-- of order two is not yet a statement about the shape of the space, and
-- the difference turns out to be visible, checkable, and worth having.
--
-- This module replaces the pair by the whole group.
--
--
-- THE GLOBAL PICTURE (why the generalisation is the natural object)
--
-- Sign assignments σ : ℕ → Bool are not just a set with a distinguished
-- involution on it.  They are a TORSOR over the gauge group
-- G = (ℕ → Bool, pointwise ·) — the full torus of `GAUGE.md` (absent from this repository) §F.1, of
-- which `ParitySeparator.flip` is the single element (−1,−1,−1,…).  Once
-- that is said, the right lemma is not `flip-law` but the bilinearity of
-- `val` in its sign argument:
--
--     val (τ ⋆ σ) n  ≡  val τ n · val σ n                    (`val-⋆`)
--
-- i.e. n ↦ (τ ↦ val τ n) is a CHARACTER of G, and `flip-law` is its
-- evaluation at the one element τ₋ = (false,false,…) — re-derived below
-- as `flip-law-again` from `val-⋆` alone, which is the check that the
-- generalisation really contains the special case rather than merely
-- resembling it.
--
-- With that, the observable classes fall out exactly.  For a query list
-- qs put
--
--     qs^⊥  =  { τ ∈ G : val τ n = +1 for every n in qs }   (`AllNeutral`)
--
-- a subgroup of G (`ann-unit`, `ann-mul`, `ann-self-inverse`).  Then:
--
--     **THE FIBRES OF THE TRANSCRIPT MAP ARE EXACTLY THE COSETS OF qs^⊥.**
--
--         obs σ qs ≡ obs σ' qs   ⟺   σ' ⋆ σ  ∈  qs^⊥
--
-- (`classes-⇐`, `classes-⇒`; note σ' ⋆ σ is the group difference, since
-- every element of G is its own inverse).  That is the theorem about
-- observable classes: the class of σ is the coset σ · qs^⊥, and what an
-- observer restricted to qs can ever learn is exactly which coset it is
-- in — no more, and, by the constructed separator, no less.
--
--
-- `ChargeCriterion` reads, as a test on a method: *all even Ω ⇒ provably
-- parity-blind.*  Sound, and sound for the intended adversary.  But the
-- criterion `HasOdd` is the evaluation of the character at ONE group
-- element, so the blindness it certifies is blindness to ONE element.
-- §6 below exhibits the witness, checked:
--
--     the query set {p₀p₁} has even Ω — `ChargeCriterion.probe-6-cannot`
--     proves it cannot separate σ₊ from its total flip — and yet it
--     SEPARATES σ from τ₀ ⋆ σ, for every σ, where τ₀ flips the sign at
--     the single prime p₀.
--
-- So `AllEven` is not "sees no gauge structure"; it is "annihilated by
-- the total flip".  The annihilator of {p₀p₁} contains τ₋ and does not
-- contain τ₀, and both facts are `refl`.  A method passing the even-Ω
-- test is blind to the parity grading — which is what the barrier is
-- about, so the test is not wrong — but it is not blind to the gauge
-- group, and the two readings of the word "charge" are separated here.
--
--
-- AND THE STATEMENT THAT THERE IS NO GRADIENT (§7)
--
-- The reason this matters for the programme rather than the bookkeeping:
-- because charge is a CHARACTER, valued in a 2-element group, separating
-- power is not a quantity that can be increased by degrees.  §7 makes
-- the sharp form checkable: for every k, the query at k² is neutral for
-- EVERY gauge element (`square-neutral`), so appending it changes no
-- annihilator (`square-free-of-charge`) and splits no observable class
-- (`square-adds-no-class`) — while naming an arbitrarily large number.
-- An unbounded family of queries with exactly zero separating power.
-- Size is not partial charge; there is no partial charge.
--
--
-- * No new arithmetic.  The content is that a completely multiplicative
--   ±1 function reads exactly the SQUARE CLASS of its argument, which is
--   classical (the square-class group ℚ^×_{>0}/(ℚ^×_{>0})², whose F₂-dual
--   is the space of such functions).  Only the checked statement, and the
--   scope correction of §6, are contributed.
-- * §7 proves the concatenated form `val σ (m ++ (k ++ k)) ≡ val σ m`,
--   which is the core and avoids permutation machinery.
--
-- Contents (no holes, no postulates, --safe):
--
--   §1  _⋆_, ·-self, ·-not, ·-unit-r   the gauge group acting on signs
--   §2  val-⋆                          the character law (bilinearity)
--       flip-law-again                 `flip-law` re-derived from it
--   §3  AllNeutral, HasCharge          the annihilator and its complement
--       ann-unit/mul/self-inverse      qs^⊥ is a subgroup
--   §4  obs-agree⋆, no-decision⋆       blindness, for an arbitrary τ
--       charge⇒separator⋆              the converse, separator CONSTRUCTED,
--                                      and for an arbitrary base point σ
--   §5  classes-⇐, classes-⇒           THE CLASS THEOREM: transcript
--                                      fibres = cosets of qs^⊥
--   §6  even-but-not-blind             the scope-correction witness
--   §7  square-neutral, …              no gradient: unboundedly large
--                                      queries of exactly zero power
------------------------------------------------------------------------

module NaturalMachine.GaugeOrbitClasses where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map ; _++_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import NaturalMachine.ParitySeparator
open import NaturalMachine.ChargeCriterion
  using (σ₊ ; probe-6 ; probe-6-cannot ; hd ; tl)

------------------------------------------------------------------------
-- §1  The gauge group and its action.
--
-- G is `Signs` again — the group of sign patterns under pointwise
-- multiplication — acting on `Signs` regarded as a torsor.  Writing the
-- two roles with two names would suggest they are different objects; the
-- fact that they are the same object, one of them with a base point
-- forgotten, is the reason the class theorem is so short.
------------------------------------------------------------------------

Gauge : Type
Gauge = Signs

infixr 5 _⋆_

_⋆_ : Gauge → Signs → Signs
(τ ⋆ σ) p = τ p · σ p

-- The three Bool facts the module runs on.  {±1} has exponent 2, and
-- that single fact is what makes every quantitative question below
-- collapse to a yes/no one; see §7.
·-self : (b : Bool) → b · b ≡ true
·-self true  = refl
·-self false = refl

·-not : (b : Bool) → b · not b ≡ false
·-not true  = refl
·-not false = refl

·-unit-r : (b : Bool) → b · true ≡ b
·-unit-r true  = refl
·-unit-r false = refl

-- The identity and the parity element of G.
τ₊ : Gauge
τ₊ _ = true

τ₋ : Gauge
τ₋ _ = false

------------------------------------------------------------------------
-- §2  The character law.
--
-- `val` is bilinear: a homomorphism in the sign argument for fixed n.
-- This is the whole content of the module — every later statement is a
-- corollary of it plus the exponent-2 facts of §1.
------------------------------------------------------------------------

-- The abelian shuffle, exhaustively.  All sixteen cases are `refl`
-- because `_·_` is XOR on Bool; written out because it is the only
-- computation in §2.
shuffle : (a b c d : Bool) → (a · b) · (c · d) ≡ (a · c) · (b · d)
shuffle true  true  true  true  = refl
shuffle true  true  true  false = refl
shuffle true  true  false true  = refl
shuffle true  true  false false = refl
shuffle true  false true  true  = refl
shuffle true  false true  false = refl
shuffle true  false false true  = refl
shuffle true  false false false = refl
shuffle false true  true  true  = refl
shuffle false true  true  false = refl
shuffle false true  false true  = refl
shuffle false true  false false = refl
shuffle false false true  true  = refl
shuffle false false true  false = refl
shuffle false false false true  = refl
shuffle false false false false = refl

val-⋆ : (τ σ : Signs) (n : Number) → val (τ ⋆ σ) n ≡ val τ n · val σ n
val-⋆ τ σ []       = refl
val-⋆ τ σ (p ∷ ns) =
    cong (λ z → (τ p · σ p) · z) (val-⋆ τ σ ns)
  ∙ shuffle (τ p) (σ p) (val τ ns) (val σ ns)

-- The parity element's own character is the parity grading itself.
val-τ₋ : (n : Number) → val τ₋ n ≡ sgn (Ω n)
val-τ₋ []       = refl
val-τ₋ (p ∷ ns) = cong (λ z → false · z) (val-τ₋ ns)

-- …and `flip` is translation by it, definitionally.
flip-is-τ₋ : (σ : Signs) → flip σ ≡ (τ₋ ⋆ σ)
flip-is-τ₋ σ = funExt (λ p → refl)

-- Hence `ParitySeparator.flip-law` is the character law evaluated at one
-- group element.  Re-derived rather than re-imported, as the check that
-- the general statement contains the special one.
flip-law-again : (σ : Signs) (n : Number)
               → val (flip σ) n ≡ sgn (Ω n) · val σ n
flip-law-again σ n =
    cong (λ ρ → val ρ n) (flip-is-τ₋ σ)
  ∙ val-⋆ τ₋ σ n
  ∙ cong (λ z → z · val σ n) (val-τ₋ n)

------------------------------------------------------------------------
-- §3  The annihilator of a query set, and that it is a subgroup.
--
-- "Coset" in §5 is only meaningful because of this section: qs^⊥ is
-- closed under the group operations, so the fibres really are translates
-- of one subgroup and not merely fibres of some map.
------------------------------------------------------------------------

AllNeutral : Gauge → List Number → Type
AllNeutral τ []       = Unit
AllNeutral τ (n ∷ qs) = (val τ n ≡ true) × AllNeutral τ qs

HasCharge : Gauge → List Number → Type
HasCharge τ []       = ⊥
HasCharge τ (n ∷ qs) = (val τ n ≡ false) ⊎ HasCharge τ qs

-- No query set is both, so the criterion of §4 is not vacuously
-- satisfiable — the analogue of `ChargeCriterion.not-both`.
neutral-not-charged : (τ : Gauge) (qs : List Number)
                    → AllNeutral τ qs → ¬ (HasCharge τ qs)
neutral-not-charged τ (n ∷ qs) (e , _)    (inl c) = true≢false (sym e ∙ c)
neutral-not-charged τ (n ∷ qs) (_ , rest) (inr h) =
  neutral-not-charged τ qs rest h

val-τ₊ : (n : Number) → val τ₊ n ≡ true
val-τ₊ []       = refl
val-τ₊ (p ∷ ns) = val-τ₊ ns

ann-unit : (qs : List Number) → AllNeutral τ₊ qs
ann-unit []       = tt
ann-unit (n ∷ qs) = val-τ₊ n , ann-unit qs

ann-mul : (τ ρ : Gauge) (qs : List Number)
        → AllNeutral τ qs → AllNeutral ρ qs → AllNeutral (τ ⋆ ρ) qs
ann-mul τ ρ []       _        _        = tt
ann-mul τ ρ (n ∷ qs) (e , es) (f , fs) =
    (val-⋆ τ ρ n ∙ cong (λ z → z · val ρ n) e ∙ f)
  , ann-mul τ ρ qs es fs

-- Inverses are free: G has exponent 2.
ann-self-inverse : (τ : Gauge) → (τ ⋆ τ) ≡ τ₊
ann-self-inverse τ = funExt (λ p → ·-self (τ p))

------------------------------------------------------------------------
-- §4  Blindness and its converse, for an ARBITRARY gauge element and an
--     ARBITRARY base point.
--
-- `ParitySeparator` fixes τ = τ₋; `ChargeCriterion` fixes additionally
-- σ = σ₊.  Both restrictions are dropped here, and the separator is
-- still constructed rather than asserted — which costs one extra idea,
-- namely that the separator must compare the answer against `val σ n`
-- rather than just read it, because for a general base point the
-- accepted transcript is not all-true.
------------------------------------------------------------------------

neutral-invisible : (τ σ : Signs) (n : Number)
                  → val τ n ≡ true → val (τ ⋆ σ) n ≡ val σ n
neutral-invisible τ σ n e = val-⋆ τ σ n ∙ cong (λ z → z · val σ n) e

charged-visible : (τ σ : Signs) (n : Number)
                → val τ n ≡ false → val (τ ⋆ σ) n ≡ not (val σ n)
charged-visible τ σ n c = val-⋆ τ σ n ∙ cong (λ z → z · val σ n) c

obs-agree⋆ : (τ σ : Signs) (qs : List Number)
           → AllNeutral τ qs → obs σ qs ≡ obs (τ ⋆ σ) qs
obs-agree⋆ τ σ []       tt         = refl
obs-agree⋆ τ σ (n ∷ qs) (e , rest) =
  cong₂ _∷_ (sym (neutral-invisible τ σ n e)) (obs-agree⋆ τ σ qs rest)

no-decision⋆ : (τ σ : Signs) (qs : List Number) → AllNeutral τ qs
             → (decide : List Bool → Bool)
             → ¬ ((decide (obs σ qs) ≡ true) × (decide (obs (τ ⋆ σ) qs) ≡ false))
no-decision⋆ τ σ qs all decide (yes , no) =
  true≢false (sym yes ∙ cong decide (obs-agree⋆ τ σ qs all) ∙ no)

Separates⋆ : Gauge → Signs → List Number → Type
Separates⋆ τ σ qs =
  Σ[ decide ∈ (List Bool → Bool) ]
    ((decide (obs σ qs) ≡ true) × (decide (obs (τ ⋆ σ) qs) ≡ false))

neutral⇒no-separator⋆ : (τ σ : Signs) (qs : List Number)
                      → AllNeutral τ qs → ¬ (Separates⋆ τ σ qs)
neutral⇒no-separator⋆ τ σ qs all (decide , yes , no) =
  no-decision⋆ τ σ qs all decide (yes , no)

charge⇒separator⋆ : (τ σ : Signs) (qs : List Number)
                  → HasCharge τ qs → Separates⋆ τ σ qs
charge⇒separator⋆ τ σ (n ∷ qs) (inl c) =
    (λ ℓ → val σ n · hd ℓ)
  , ·-self (val σ n)
  , cong (λ z → val σ n · z) (charged-visible τ σ n c) ∙ ·-not (val σ n)
charge⇒separator⋆ τ σ (n ∷ qs) (inr h) with charge⇒separator⋆ τ σ qs h
... | (decide , yes , no) = (λ ℓ → decide (tl ℓ)) , yes , no

-- The criterion, now relative to the adversary it is a criterion for.
gauge-criterion : (τ : Gauge) (σ : Signs) (qs : List Number)
                → (HasCharge τ qs → Separates⋆ τ σ qs)
                × (AllNeutral τ qs → ¬ (Separates⋆ τ σ qs))
gauge-criterion τ σ qs = charge⇒separator⋆ τ σ qs , neutral⇒no-separator⋆ τ σ qs

------------------------------------------------------------------------
-- §5  THE CLASS THEOREM.
--
-- Two sign assignments have the same transcript on qs exactly when they
-- differ by an element of qs^⊥.  Both directions; the fibres of the
-- transcript map are therefore precisely the cosets of the subgroup of
-- §3, and "observable class" acquires a definition rather than a
-- gesture.
--
-- Note the group difference of σ' and σ is σ' ⋆ σ itself — no inversion
-- appears, because §1's `·-self` says every element is its own inverse.
------------------------------------------------------------------------

-- (σ' ⋆ σ) ⋆ σ ≡ σ' : translating by the difference lands on σ'.
cancel : (σ σ' : Signs) → ((σ' ⋆ σ) ⋆ σ) ≡ σ'
cancel σ σ' = funExt (λ p →
    ·-assoc (σ' p) (σ p) (σ p)
  ∙ cong (λ z → σ' p · z) (·-self (σ p))
  ∙ ·-unit-r (σ' p))

classes-⇐ : (qs : List Number) (σ σ' : Signs)
          → AllNeutral (σ' ⋆ σ) qs → obs σ qs ≡ obs σ' qs
classes-⇐ qs σ σ' h =
    obs-agree⋆ (σ' ⋆ σ) σ qs h
  ∙ cong (λ ρ → obs ρ qs) (cancel σ σ')

classes-⇒ : (qs : List Number) (σ σ' : Signs)
          → obs σ qs ≡ obs σ' qs → AllNeutral (σ' ⋆ σ) qs
classes-⇒ []       σ σ' e = tt
classes-⇒ (n ∷ qs) σ σ' e =
    ( val-⋆ σ' σ n
    ∙ cong (λ z → z · val σ n) (sym (cong hd e))
    ∙ ·-self (val σ n) )
  , classes-⇒ qs σ σ' (cong tl e)

------------------------------------------------------------------------
-- §6  THE SCOPE CORRECTION, with its witness.
--
-- `ChargeCriterion.probe-6` is the query set {p₀p₁}.  Its Ω is 2, so it
-- is `AllEven`, and `probe-6-cannot` proves — correctly — that it admits
-- no procedure separating σ₊ from its total flip.
--
-- Nevertheless it separates, at every base point, the pair (σ, τ₀ ⋆ σ)
-- where τ₀ flips exactly one prime.  The single-prime flip is a perfectly
-- ordinary element of `GAUGE.md` (absent from this repository)'s torus; it was simply never the
-- adversary, because the word "parity" fixes attention on the diagonal
-- element.
--
-- Both facts about probe-6's annihilator are `refl`:
--   τ₋ ∈ probe-6^⊥   (false · (false · true) = true)
--   τ₀ ∉ probe-6^⊥   (false · (true  · true) = false)
------------------------------------------------------------------------

-- the flip at the single prime p₀
τ₀ : Gauge
τ₀ zero    = false
τ₀ (suc _) = true

τ₀-is-charged-for-probe-6 : HasCharge τ₀ probe-6
τ₀-is-charged-for-probe-6 = inl refl

τ₋-is-neutral-for-probe-6 : AllNeutral τ₋ probe-6
τ₋-is-neutral-for-probe-6 = refl , tt

-- τ₀ is a genuine third element: neither the identity nor the total flip.
-- (Both are decided at the prime p₁, where τ₀ agrees with τ₊.)
τ₀≢τ₋ : ¬ (τ₀ 1 ≡ τ₋ 1)
τ₀≢τ₋ e = true≢false e

τ₀≢τ₊ : ¬ (τ₀ 0 ≡ τ₊ 0)
τ₀≢τ₊ e = true≢false (sym e)

-- THE WITNESS.  An even-Ω query set that is provably blind to the total
-- flip and provably NOT blind to the gauge group — at every base point,
-- with the separating procedure constructed.
even-but-not-blind :
    (¬ (NaturalMachine.ChargeCriterion.Separates probe-6))
  × ((σ : Signs) → Separates⋆ τ₀ σ probe-6)
even-but-not-blind =
    probe-6-cannot
  , (λ σ → charge⇒separator⋆ τ₀ σ probe-6 τ₀-is-charged-for-probe-6)

-- and, in the vocabulary of §5: probe-6 does not separate the classes of
-- σ and τ₋ ⋆ σ, but it does separate those of σ and τ₀ ⋆ σ.
probe-6-class-collapse : (σ : Signs) → obs σ probe-6 ≡ obs (τ₋ ⋆ σ) probe-6
probe-6-class-collapse σ = obs-agree⋆ τ₋ σ probe-6 τ₋-is-neutral-for-probe-6

------------------------------------------------------------------------
-- §7  NO GRADIENT.
--
-- `val` is a monoid homomorphism from the factorisation monoid
-- (Number, ++) to ({±1}, ·).  Since {±1} has exponent 2, every square is
-- sent to +1 by EVERY sign assignment — so a query at a square is
-- invisible to the entire gauge group at once.
--
-- The consequence is the one that bears on TARGET.md (absent from this repository) §2's W4.  W4 asks
-- "how much archimedean input, at what depth, buys how much parity
-- information".  At the exact algebraic layer that quantity does not
-- exist: separating power is not increased by making a query bigger, by
-- adding more queries, or by any amount of computation on the answers.
-- Below is an unbounded family of arbitrarily large queries whose
-- separating power is exactly zero, forever — not small, zero.  A
-- quantitative coupling theorem, if there is one, must therefore be a
-- theorem about a NORM on approximations, not about query sets; those
-- are two different theorems and only the second is what this barrier
-- is made of.
------------------------------------------------------------------------

val-++ : (σ : Signs) (m n : Number) → val σ (m ++ n) ≡ val σ m · val σ n
val-++ σ []       n = refl
val-++ σ (p ∷ m) n =
    cong (λ z → σ p · z) (val-++ σ m n)
  ∙ sym (·-assoc (σ p) (val σ m) (val σ n))

-- A square is neutral for every sign assignment, hence for every gauge
-- element: the observable content of a query is its square class.
square-neutral : (σ : Signs) (k : Number) → val σ (k ++ k) ≡ true
square-neutral σ k = val-++ σ k k ∙ ·-self (val σ k)

-- …and more generally an argument is read only modulo squares.
square-invisible : (σ : Signs) (m k : Number)
                 → val σ (m ++ (k ++ k)) ≡ val σ m
square-invisible σ m k =
    val-++ σ m (k ++ k)
  ∙ cong (λ z → val σ m · z) (square-neutral σ k)
  ∙ ·-unit-r (val σ m)

-- Appending a square query changes no annihilator …
square-free-of-charge : (qs : List Number) (k : Number) (τ : Gauge)
                      → AllNeutral τ qs → AllNeutral τ ((k ++ k) ∷ qs)
square-free-of-charge qs k τ h = square-neutral τ k , h

-- … and splits no observable class.  Both directions of §5 are therefore
-- untouched by it, at every size of k.
square-adds-no-class : (qs : List Number) (k : Number) (σ σ' : Signs)
                     → obs σ qs ≡ obs σ' qs
                     → obs σ ((k ++ k) ∷ qs) ≡ obs σ' ((k ++ k) ∷ qs)
square-adds-no-class qs k σ σ' e =
  cong₂ _∷_ (square-neutral σ k ∙ sym (square-neutral σ' k)) e

-- The extreme instance, spelled out because it is the sentence that
-- answers W4 at the exact layer: the ENTIRE gauge group annihilates a
-- query set built only of squares, whatever the squares are.
all-squares-blind : (ks : List Number) (τ : Gauge)
                  → AllNeutral τ (map (λ k → k ++ k) ks)
all-squares-blind []       τ = tt
all-squares-blind (k ∷ ks) τ = square-neutral τ k , all-squares-blind ks τ

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- OuteMeizonOuteElasson_TheParallelInterfacePriceMultipliesExactlyWhereTheRegulatorHasNoChoice
--
-- cf-tessera-m-0, 2026-08-20.  Agda 2.6.3 + cubical v0.5 (NOT the repo pin).
--
------------------------------------------------------------------------
-- ON THE NAME.  **No  term is claimed and none is invented**, per
-- CLAUDE.md (absent from this repository)'s file-naming rule, note 2.  The method this module formalises
-- is Greek and the file leads with the source's own words for it.
--
-- Archimedes' quadratures close by eliminating both inequalities: the
-- magnitude sought is shown to be neither GREATER (μεῖζον, *meizon*) nor
-- LESS (ἔλασσον, *elasson*) than the asserted value, therefore equal.  That
-- two-sided elimination is the whole of the demonstration, and its shape is
-- what §5 below checks.
--
-- WHAT IS CLAIMED OF THE GREEK SOURCES.  Only this: the double elimination
-- is their argument form, and it consumes a hypothesis that the bracket can
-- be driven below any assigned magnitude — Eudoxus' admission condition
-- (Euclid, *Elements* V, def. 4) acting through the bisection lemma
-- (*Elements* X.1).
-- §§1–4 is NOT Greek; its statement of record here is the owner
-- transmission quoted below, and the lower bound cited in §5 is linear
-- programming duality.
--
-- "Method of exhaustion" is not a Greek phrase either.  It is Grégoire de
-- Saint-Vincent's coinage, *Opus geometricum*, 1647 — a 17th-century Latin
-- name for a 4th-century-BCE Greek argument.  Repo-wide, the later name has
-- displaced the sources.  Grep over `notes/` before writing this file, for
-- the TEXT's name and not the author's:
--
--     exhaustion                      42     Elements                   14
--     Archimedes                       6     Eudoxus                     1
--     Method of Mechanical Theorems    0     Quadrature of the Parabola  0
--     Measurement of a Circle          0     On the Sphere and Cylinder  0
--     Palimpsest                       0     Heiberg                     0
--
-- (Indian comparison, same grep, same hour: Adhyy 20, Chandastra
-- 13, Brhmasphuasiddhnta 12, Anuyogadvra 7, Sthnga 5.)  An author's
-- name propagates through citation; a work's name appears only where
-- someone attended to the work.  For the Greek lane nobody had.
--
-- TRANSMISSION, named because the sibling module carrying it in full landed
-- the same hour and this one must not re-land it:
-- `LogonEchein_TheArchimedeanConditionIsIndependentOfOrderAdditionAndALeastPositive.agda`
-- records the chain — 10th-c. Byzantine copy, scraped and overwritten as a
-- euchologion signed 14 April 1229, undertext identified by Johan Ludvig
-- Heiberg at the Metochion of the Holy Sepulchre, Constantinople, 1906,
-- published 1906–1913, sold at Christie's New York 29 October 1998,
-- multispectral and synchrotron imaging at the Walters Art Museum
-- 1999–2008.  Read it there.  What is used here is the *Method*'s own
-- preface: the mechanical procedure supplies the result and does NOT
-- demonstrate it (οὐκ ἀποδεδειγμένον).  Two stages, and §5 is the second.
--
-- THE OTHER-DIRECTION SEARCH, REPORTED PLAINLY AS A NEGATIVE.  Established
-- today by cf-tessera-i-0 and not re-derived: the ulba-stras, the Jaina
-- *Anuyogadvra* / *Sthnga*, and Pigala/Halyudha carry no signed
-- incidence structure and no difference-of-endpoints operator, and "the
-- meru-prastra's rule is a summation along a graded DAG, not a signed
-- difference across an undirected edge."  I ran the adjacent question for
-- THIS module's object — a MINIMUM transversal of a family of witness sets,
-- and its behaviour under parallel composition — and it comes back empty
-- too.  *Anuyogadvra* and *Sthnga* enumerate *bhaga* combinations and
-- Pigala's *prastra* generates an array by rule; neither poses a
-- minimisation over subsets subject to a covering constraint, which is what
-- κ₀ is.  A reported negative is a result and I do not manufacture a use
-- for one.
--
------------------------------------------------------------------------
-- THE OWNER TRANSMISSION THIS MODULE CHECKS.
--
-- `collab/upstream/library/raw/SUFFICIENT_INTERFACES_DELTA_02_2026-08-13.md` (absent from this repository),
-- quoted, not paraphrased:
--
--   §0  "Strict submultiplicativity already occurs in the smallest
--        interesting symmetric example. This means jointly solving two
--        independent relational tasks can require fewer interface states
--        than separately minimizing and multiplying their interfaces."
--
--   §3  "The interface is not required to factor as q1×q2. This
--        correlation produces compression."
--
--   §7  "This distinguishes: exact state reconstruction; exact
--        deterministic target reconstruction; relational witness
--        realization.  Only the third has selector freedom large enough for
--        the triangle compression above."
--
--   §8  "The invariant κ0 is submultiplicative under tensor:
--        κ0(R⊗S)≤κ0(R)κ0(S), but not multiplicative."
--
--   §10 "LIVE FRONTIER: Prove or disprove G∞=0 for finite witness
--        hypergraphs under unrestricted block selectors."
--
-- Delta 02's Theorem 1 (κ₀ = 2) and Theorem 2 (κ₀ of the square = 3 < 4)
-- are the owner's.  §2 below re-derives them as checked terms so §§3–6 can
-- stand on them; the credit is his.
--
------------------------------------------------------------------------
-- THE TWO LENSES, AND WHERE THEY SPLIT.
--
-- ASHBY: a regulator must have at least as much variety as what it
-- regulates.  The NUMBER a designer takes from that law: to regulate two
-- tasks in parallel you need the product of the two varieties,
-- κ₀(R⊗S) = κ₀(R)·κ₀(S).
--
-- DIRAC: follow the formal beauty of the equation past what is currently
-- justified.  The beautiful invariant here is the fractional cover value
-- τ*, which Delta 02's Theorem 4 proves EXACTLY multiplicative; the
-- integral κ₀ is a discretisation artefact; hence K∞ = log τ*, G∞ = 0, and
-- Delta 02's own §10 frontier resolves by beauty.
--
-- They disagree about one finite number: κ₀ of the triangle squared.
-- Ashby's number says 4.  Dirac's says track τ*² = 9/4, hence 3.
--
-- VERDICT, in three parts because the material splits it in three:
--
--   §2  DIRAC WINS ON THE FINITE FACT.  Ashby's number is refuted by a
--       checked term — three interface states suffice for the squared task,
--       so the price is not 4.  `ashby-number-refuted`.
--
--   §3–§4  DIRAC LOSES ON THE EXTRAPOLATION HE WINS BY.  "Selector freedom,
--       hence compression" is false as stated.  §3 proves generically that
--       where the witness is FORCED the price multiplies exactly; §4 states
--       MY OWN strengthening of that — freedom anywhere gives compression —
--       and kills it with a checked counterexample.
--
--   §5  ARCHIMEDES REFUSES G∞ = 0.  At n = 4 the transmission's own bracket
--       is [6, 9] and does not shrink.  A double elimination yields equality
--       only from a bracket drivable below any assigned magnitude.
--       `G∞-is-not-decided-by-this-bracket` is that refusal, checked.
--
-- ASHBY'S LAW SURVIVES, HIS NUMBER DOES NOT — the correction already landed
-- as `NaturalMachine/Prastara_TheGaugeStreamCostsZeroCarriedBitsAndInvisibilityIsWeakerThanGauge.agda`
-- (cf-tessera-j-1, 2026-08-20): the correct price is the image of the
-- disturbance set under the evaluation, not its cardinality.  Not re-landed
-- here.  §3 adds where the cardinality answer IS right: a relation whose
-- witness is forced offers the selector nothing to correlate, and there the
-- two prices coincide.  The law prices choice.
--
-- §6's negative is written in the positive-data idiom of the drawn module
-- `NaturalMachine/FormationDirectionIncidence.agda`, whose §4 says of its
-- own `ExposureBound`: "It is positive data, not the negation of a missed
-- search."  `FactorBound` here has that shape and is refuted the same way.
------------------------------------------------------------------------

module OuteMeizonOuteElasson_TheParallelInterfacePriceMultipliesExactlyWhereTheRegulatorHasNoChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
  using (Bool ; true ; false ; _and_ ; _or_ ; true≢false ; false≢true)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.List
  using (List ; [] ; _∷_ ; _++_ ; map ; foldr ; length)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; ·-comm ; snotz ; znots ; injSuc)
open import Cubical.Data.Nat.Order
  using ( _≤_ ; _<_ ; ≤-refl ; ≤-trans ; ≤-·k ; <-weaken ; <→≢ ; ¬m<m
        ; ¬-<-zero ; pred-≤-pred ; Trichotomy ; lt ; eq ; gt ; _≟_ )
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' : Level

------------------------------------------------------------------------
-- 1.  The object: a relational task, its interfaces, and parallel
--     composition.
--
-- `Rel A B` is Delta 02's R: `R a b ≡ true` says b is a valid witness at
-- input a.  An interface is a subset S of B; it SUFFICES when every input
-- still has a valid witness inside S.  κ₀ is the least size of a sufficient
-- S — the least transversal of the family {R a}, i.e. the least hyperedge
-- cover of the witness hypergraph H_R.
------------------------------------------------------------------------

Rel : Type ℓA → Type ℓB → Type _
Rel A B = A → B → Bool

Iface : Type ℓB → Type _
Iface B = B → Bool

-- Sufficiency as positive data: for each input, an exhibited witness.
Hits : {A : Type ℓA} {B : Type ℓB} → Rel A B → Iface B → Type _
Hits {A = A} {B = B} R S =
  (a : A) → Σ[ b ∈ B ] ((R a b ≡ true) × (S b ≡ true))

-- Parallel composition: Delta 02's ⊗, the Cartesian product of tasks.
_⊗ᴿ_ : {A : Type ℓA} {B : Type ℓB} {A' : Type ℓA'} {B' : Type ℓB'}
     → Rel A B → Rel A' B' → Rel (A × A') (B × B')
(R ⊗ᴿ R') (a , a') (b , b') = R a b and R' a' b'

_⊗ˢ_ : {B : Type ℓB} {B' : Type ℓB'} → Iface B → Iface B' → Iface (B × B')
(S ⊗ˢ S') (b , b') = S b and S' b'

and-both : {x y : Bool} → x ≡ true → y ≡ true → (x and y) ≡ true
and-both p q = cong₂ _and_ p q

and-split : (x y : Bool) → (x and y) ≡ true → (x ≡ true) × (y ≡ true)
and-split true  true  _ = refl , refl
and-split true  false p = Empty.rec (false≢true p)
and-split false _     p = Empty.rec (false≢true p)

-- LAX MONOIDALITY.  A pair of interfaces gives an interface for the pair of
-- tasks.  This is the ≤ half of Delta 02 §8, and it holds for all
-- relations, over any types, with no finiteness anywhere.
hits-⊗ : {A : Type ℓA} {B : Type ℓB} {A' : Type ℓA'} {B' : Type ℓB'}
       → {R : Rel A B} {R' : Rel A' B'} {S : Iface B} {S' : Iface B'}
       → Hits R S → Hits R' S' → Hits (R ⊗ᴿ R') (S ⊗ˢ S')
hits-⊗ h h' (a , a') =
  (fst (h a) , fst (h' a'))
  , ( and-both (fst (snd (h a))) (fst (snd (h' a')))
    , and-both (snd (snd (h a))) (snd (snd (h' a'))) )

------------------------------------------------------------------------
-- 2.  Finite machinery, and Delta 02's Theorems 1 and 2 as checked terms.
--
-- Exhaustive Boolean verification decided by `refl`.  Under CLAUDE.md (absent from this repository)'s
-- rule this is certified symbolic computation, i.e. proof, not measurement.
------------------------------------------------------------------------

all? : {X : Type ℓ} → (X → Bool) → List X → Bool
all? p [] = true
all? p (x ∷ xs) = p x and all? p xs

any? : {X : Type ℓ} → (X → Bool) → List X → Bool
any? p [] = false
any? p (x ∷ xs) = p x or any? p xs

or-true : (b : Bool) → (b or true) ≡ true
or-true false = refl
or-true true  = refl

concatMap : {X : Type ℓ} {Y : Type ℓ'} → (X → List Y) → List X → List Y
concatMap f xs = foldr (λ x ys → f x ++ ys) [] xs

pairsOf : {X : Type ℓ} {Y : Type ℓ'} → List X → List Y → List (X × Y)
pairsOf xs ys = concatMap (λ x → map (λ y → (x , y)) ys) xs

-- All lists of length n over a carrier list, with repetition.
tuples : {X : Type ℓ} → ℕ → List X → List (List X)
tuples zero    xs = [] ∷ []
tuples (suc n) xs = concatMap (λ x → map (x ∷_) (tuples n xs)) xs

-- Boolean sufficiency of a listed interface.
suffices : {A : Type ℓA} {B : Type ℓB} → Rel A B → List A → List B → Bool
suffices R as S = all? (λ a → any? (λ b → R a b) S) as

-- Membership, and enough of its theory to turn an exhaustive `false` into
-- a genuine universal negative rather than a claim about one enumeration.

data _∈_ {X : Type ℓ} (x : X) : List X → Type ℓ where
  here  : {xs : List X} → x ∈ (x ∷ xs)
  there : {y : X} {xs : List X} → x ∈ xs → x ∈ (y ∷ xs)

∈-map : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {x : X} {xs : List X}
      → x ∈ xs → f x ∈ map f xs
∈-map f here      = here
∈-map f (there m) = there (∈-map f m)

∈-++ˡ : {Y : Type ℓ} {y : Y} {ys zs : List Y} → y ∈ ys → y ∈ (ys ++ zs)
∈-++ˡ here      = here
∈-++ˡ (there m) = there (∈-++ˡ m)

∈-++ʳ : {Y : Type ℓ} {y : Y} (ys : List Y) {zs : List Y}
      → y ∈ zs → y ∈ (ys ++ zs)
∈-++ʳ []       m = m
∈-++ʳ (_ ∷ ys) m = there (∈-++ʳ ys m)

∈-concatMap : {X : Type ℓ} {Y : Type ℓ'} (f : X → List Y)
            → {x : X} {xs : List X} {y : Y}
            → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
∈-concatMap f here        n = ∈-++ˡ n
∈-concatMap f (there {y = w} m) n = ∈-++ʳ (f w) (∈-concatMap f m n)

∈-pairsOf : {X : Type ℓ} {Y : Type ℓ'} {x : X} {y : Y}
          → {xs : List X} {ys : List Y}
          → x ∈ xs → y ∈ ys → (x , y) ∈ pairsOf xs ys
∈-pairsOf {x = x} px py = ∈-concatMap _ px (∈-map (λ y → (x , y)) py)

tuples-complete : {X : Type ℓ} {carrier : List X}
                → ((x : X) → x ∈ carrier)
                → (n : ℕ) (S : List X) → length S ≡ n → S ∈ tuples n carrier
tuples-complete c zero    []       p = here
tuples-complete c zero    (_ ∷ _)  p = Empty.rec (snotz p)
tuples-complete c (suc n) []       p = Empty.rec (znots p)
tuples-complete c (suc n) (x ∷ xs) p =
  ∈-concatMap _ (c x) (∈-map (x ∷_) (tuples-complete c n xs (injSuc p)))

any?-of-member : {X : Type ℓ} (p : X → Bool) {x : X} {xs : List X}
               → x ∈ xs → p x ≡ true → any? p xs ≡ true
any?-of-member p (here {xs = ys})   h = cong (_or any? p ys) h
any?-of-member p (there {y = y} m)  h =
  cong (p y or_) (any?-of-member p m h) ∙ or-true (p y)

-- Every list of length n over a complete carrier is searched, so a `false`
-- from the search is a statement about every interface of that size.
exhaustive : {X : Type ℓ} {carrier : List X}
           → ((x : X) → x ∈ carrier)
           → {A : Type ℓA} (R : Rel A X) (as : List A) (n : ℕ)
           → any? (suffices R as) (tuples n carrier) ≡ false
           → (S : List X) → length S ≡ n → ¬ (suffices R as S ≡ true)
exhaustive c R as n none S len h =
  false≢true
    (sym none ∙ any?-of-member (suffices R as) (tuples-complete c n S len) h)

-- --- The triangle relation, Delta 02 §1. ------------------------------
--   R(1) = {12,13},  R(2) = {12,23},  R(3) = {13,23}.

data A₃ : Type₀ where α₁ α₂ α₃ : A₃
data W₃ : Type₀ where e₁₂ e₁₃ e₂₃ : W₃

allA₃ : List A₃
allA₃ = α₁ ∷ α₂ ∷ α₃ ∷ []

allW₃ : List W₃
allW₃ = e₁₂ ∷ e₁₃ ∷ e₂₃ ∷ []

allW₃-complete : (w : W₃) → w ∈ allW₃
allW₃-complete e₁₂ = here
allW₃-complete e₁₃ = there here
allW₃-complete e₂₃ = there (there here)

tri : Rel A₃ W₃
tri α₁ e₁₂ = true
tri α₁ e₁₃ = true
tri α₁ e₂₃ = false
tri α₂ e₁₂ = true
tri α₂ e₁₃ = false
tri α₂ e₂₃ = true
tri α₃ e₁₂ = false
tri α₃ e₁₃ = true
tri α₃ e₂₃ = true

-- THEOREM 1 (owner, Delta 02 §1): κ₀ = 2.
tri-no-interface-of-size-1 : any? (suffices tri allA₃) (tuples 1 allW₃) ≡ false
tri-no-interface-of-size-1 = refl

tri-interface-2 : suffices tri allA₃ (e₁₂ ∷ e₁₃ ∷ []) ≡ true
tri-interface-2 = refl

-- --- The square task R × R. -------------------------------------------

A₉ : Type₀
A₉ = A₃ × A₃

W₉ : Type₀
W₉ = W₃ × W₃

allA₉ : List A₉
allA₉ = pairsOf allA₃ allA₃

allW₉ : List W₉
allW₉ = pairsOf allW₃ allW₃

allW₉-complete : (w : W₉) → w ∈ allW₉
allW₉-complete (a , b) = ∈-pairsOf (allW₃-complete a) (allW₃-complete b)

triSq : Rel A₉ W₉
triSq = tri ⊗ᴿ tri

-- The owner's explicit three-state interface, Delta 02 §2:
--   E_12×E_12,  E_13×E_23,  E_23×E_13.
ownerInterface : List W₉
ownerInterface = (e₁₂ , e₁₂) ∷ (e₁₃ , e₂₃) ∷ (e₂₃ , e₁₃) ∷ []

-- THEOREM 2 (owner, Delta 02 §2): κ₀(R×R) = 3 < 4 = κ₀(R)².
triSq-interface-3 : suffices triSq allA₉ ownerInterface ≡ true
triSq-interface-3 = refl

triSq-no-interface-of-size-2 :
  any? (suffices triSq allA₉) (tuples 2 allW₉) ≡ false
triSq-no-interface-of-size-2 = refl

triSq-two-states-never-suffice :
  (S : List W₉) → length S ≡ 2 → ¬ (suffices triSq allA₉ S ≡ true)
triSq-two-states-never-suffice =
  exhaustive allW₉-complete triSq allA₉ 2 triSq-no-interface-of-size-2

-- ASHBY'S NUMBER, stated by what it forbids, and refuted.
--
-- If the parallel price were the product of the prices, 2·2 = 4, then no
-- three-state interface could suffice for the squared task.  One does.
AshbyProductPrice : Type₀
AshbyProductPrice =
  ¬ (Σ[ S ∈ List W₉ ] ((length S ≡ 3) × (suffices triSq allA₉ S ≡ true)))

ashby-number-refuted : ¬ AshbyProductPrice
ashby-number-refuted p = p (ownerInterface , refl , triSq-interface-3)

-- NON-VACUITY CONTROL.  An exhaustive `false` is worth nothing if the
-- enumeration is empty or short, and nothing detects that: `any? p [] ≡
-- false` typechecks for every p.  So the sizes are checked too, and
-- `suffices` is checked to return `true` somewhere (it does, three lines
-- up) so that the searches below are not reporting a broken predicate.
enumeration-sizes :
  (length allA₃ ≡ 3) × (length allW₃ ≡ 3)
  × (length allA₉ ≡ 9) × (length allW₉ ≡ 9)
  × (length (tuples 1 allW₃) ≡ 3)
  × (length (tuples 2 allW₉) ≡ 81)
enumeration-sizes = refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- 3.  Where the cardinality answer is EXACTLY right: no choice.
--
-- A relation is FUNCTION-LIKE when each input has exactly one valid
-- witness.  Then sufficiency is not a covering problem at all: the
-- interface is FORCED, pointwise, with nothing to minimise.  This is
-- Delta 02 §7's second category — "exact deterministic target
-- reconstruction" — against its third.
--
-- Proved generically, arbitrary types, no finiteness.
------------------------------------------------------------------------

FunctionLike : {A : Type ℓA} {B : Type ℓB} → Rel A B → (A → B) → Type _
FunctionLike {A = A} {B = B} R f =
  ((a : A) → R a (f a) ≡ true)
  × ((a : A) (b : B) → R a b ≡ true → b ≡ f a)

-- The regulator has no choice: every sufficient interface contains f a.
functionLike-forces :
  {A : Type ℓA} {B : Type ℓB} {R : Rel A B} {f : A → B} {S : Iface B}
  → FunctionLike R f → Hits R S → (a : A) → S (f a) ≡ true
functionLike-forces {S = S} (_ , uniq) h a =
  subst (λ w → S w ≡ true) (uniq a (fst (h a)) (fst (snd (h a))))
        (snd (snd (h a)))

-- …and the image is already sufficient, so it is the least interface.
functionLike-image-suffices :
  {A : Type ℓA} {B : Type ℓB} {R : Rel A B} {f : A → B} {S : Iface B}
  → FunctionLike R f → ((a : A) → S (f a) ≡ true) → Hits R S
functionLike-image-suffices {f = f} (tot , _) p a = f a , (tot a , p a)

-- STRONG MONOIDALITY ON THE DETERMINISTIC PART.  A tensor of function-like
-- relations is function-like with witness map f × f'; so the forced
-- interface of the tensor is exactly the product of the two forced
-- interfaces.  No correlation is available to exploit and Ashby's product
-- NUMBER is the correct price.
functionLike-⊗ :
  {A : Type ℓA} {B : Type ℓB} {A' : Type ℓA'} {B' : Type ℓB'}
  {R : Rel A B} {R' : Rel A' B'} {f : A → B} {f' : A' → B'}
  → FunctionLike R f → FunctionLike R' f'
  → FunctionLike (R ⊗ᴿ R') (λ p → (f (fst p) , f' (snd p)))
functionLike-⊗ {R = R} {R' = R'} (tot , uniq) (tot' , uniq') =
  (λ p → and-both (tot (fst p)) (tot' (snd p)))
  , λ p q h →
      let sp = and-split (R (fst p) (fst q)) (R' (snd p) (snd q)) h
      in λ i → ( uniq  (fst p) (fst q) (fst sp) i
               , uniq' (snd p) (snd q) (snd sp) i )

functionLike-⊗-forces :
  {A : Type ℓA} {B : Type ℓB} {A' : Type ℓA'} {B' : Type ℓB'}
  {R : Rel A B} {R' : Rel A' B'} {f : A → B} {f' : A' → B'}
  {T : Iface (B × B')}
  → FunctionLike R f → FunctionLike R' f'
  → Hits (R ⊗ᴿ R') T
  → (a : A) (a' : A') → T (f a , f' a') ≡ true
functionLike-⊗-forces F F' h a a' =
  functionLike-forces (functionLike-⊗ F F') h (a , a')

-- A finite witness that the forced price really is the product.
-- A = {1,2}, B = {x,y}, R(1) = {x}, R(2) = {y}: κ₀ = 2, squared task 4.

data A₂ : Type₀ where β₁ β₂ : A₂
data W₂ : Type₀ where x₁ x₂ : W₂

allA₂ : List A₂
allA₂ = β₁ ∷ β₂ ∷ []

allW₂ : List W₂
allW₂ = x₁ ∷ x₂ ∷ []

allW₂-complete : (w : W₂) → w ∈ allW₂
allW₂-complete x₁ = here
allW₂-complete x₂ = there here

det : Rel A₂ W₂
det β₁ x₁ = true
det β₁ x₂ = false
det β₂ x₁ = false
det β₂ x₂ = true

detWitness : A₂ → W₂
detWitness β₁ = x₁
detWitness β₂ = x₂

det-is-function-like : FunctionLike det detWitness
det-is-function-like =
  (λ { β₁ → refl ; β₂ → refl })
  , λ { β₁ x₁ _ → refl
      ; β₁ x₂ p → Empty.rec (false≢true p)
      ; β₂ x₁ p → Empty.rec (false≢true p)
      ; β₂ x₂ _ → refl }

det-no-interface-of-size-1 : any? (suffices det allA₂) (tuples 1 allW₂) ≡ false
det-no-interface-of-size-1 = refl

det-interface-2 : suffices det allA₂ (x₁ ∷ x₂ ∷ []) ≡ true
det-interface-2 = refl

detSq : Rel (A₂ × A₂) (W₂ × W₂)
detSq = det ⊗ᴿ det

allA₄ : List (A₂ × A₂)
allA₄ = pairsOf allA₂ allA₂

allW₄ : List (W₂ × W₂)
allW₄ = pairsOf allW₂ allW₂

allW₄-complete : (w : W₂ × W₂) → w ∈ allW₄
allW₄-complete (a , b) = ∈-pairsOf (allW₂-complete a) (allW₂-complete b)

detSq-no-interface-of-size-3 :
  any? (suffices detSq allA₄) (tuples 3 allW₄) ≡ false
detSq-no-interface-of-size-3 = refl

detSq-three-states-never-suffice :
  (S : List (W₂ × W₂)) → length S ≡ 3 → ¬ (suffices detSq allA₄ S ≡ true)
detSq-three-states-never-suffice =
  exhaustive allW₄-complete detSq allA₄ 3 detSq-no-interface-of-size-3

detSq-interface-4 :
  suffices detSq allA₄
    ((x₁ , x₁) ∷ (x₁ , x₂) ∷ (x₂ , x₁) ∷ (x₂ , x₂) ∷ []) ≡ true
detSq-interface-4 = refl

------------------------------------------------------------------------
-- 4.  REFUTATION OF MY OWN CLAIM.
--
-- CLAIM M, which I held after §§2–3 and which is the Dirac reading pushed
-- one step past the transmission:
--
--   "Compression is exactly the presence of choice.  §3 shows the price
--    multiplies when the witness is forced; §2 shows it drops when it is
--    not; therefore κ₀(R ⊗ R) < κ₀(R)² whenever some input has two or more
--    valid witnesses."
--
-- It is false, and the counterexample is small.  Take
--
--   A = {γ₁, γ₂},  B = {u, v, z},  R(γ₁) = {u, v},  R(γ₂) = {z}.
--
-- γ₁ has genuine choice, so Claim M predicts strict compression.  But the
-- four required witness sets of the squared task,
--
--   {u,v}×{u,v},   {u,v}×{z},   {z}×{u,v},   {z}×{z},
--
-- are PAIRWISE DISJOINT, so four states are forced and κ₀ = 4 = 2·2
-- exactly.  Ashby's number is right here in spite of the choice.
--
-- WHAT KILLED IT.  Choice AT an input is not choice ACROSS inputs.  The
-- triangle's compression in §2 needs two different inputs whose witness
-- sets OVERLAP, so one product state can serve different coordinate-pairs
-- under a correlated selector.  Here the two witness sets are disjoint, the
-- selector has nothing to correlate, and the local freedom at γ₁ is
-- invisible to the product.  Local non-determinism is necessary for
-- compression and is not sufficient.
--
-- Delta 02 §7 already says "selector freedom LARGE ENOUGH"; Claim M dropped
-- the qualifier, and the qualifier was carrying the theorem.
------------------------------------------------------------------------

data A₂′ : Type₀ where γ₁ γ₂ : A₂′
data W₃′ : Type₀ where u v z : W₃′

allA₂′ : List A₂′
allA₂′ = γ₁ ∷ γ₂ ∷ []

allW₃′ : List W₃′
allW₃′ = u ∷ v ∷ z ∷ []

allW₃′-complete : (w : W₃′) → w ∈ allW₃′
allW₃′-complete u = here
allW₃′-complete v = there here
allW₃′-complete z = there (there here)

spl : Rel A₂′ W₃′
spl γ₁ u = true
spl γ₁ v = true
spl γ₁ z = false
spl γ₂ u = false
spl γ₂ v = false
spl γ₂ z = true

-- Claim M's hypothesis genuinely holds: γ₁ has two distinct witnesses.
isU : W₃′ → Bool
isU u = true
isU v = false
isU z = false

u≢v : ¬ (u ≡ v)
u≢v p = true≢false (cong isU p)

spl-γ₁-has-two-witnesses : (spl γ₁ u ≡ true) × (spl γ₁ v ≡ true)
spl-γ₁-has-two-witnesses = refl , refl

-- κ₀(spl) = 2.
spl-no-interface-of-size-1 :
  any? (suffices spl allA₂′) (tuples 1 allW₃′) ≡ false
spl-no-interface-of-size-1 = refl

spl-interface-2 : suffices spl allA₂′ (u ∷ z ∷ []) ≡ true
spl-interface-2 = refl

splSq : Rel (A₂′ × A₂′) (W₃′ × W₃′)
splSq = spl ⊗ᴿ spl

allA₄′ : List (A₂′ × A₂′)
allA₄′ = pairsOf allA₂′ allA₂′

allW₉′ : List (W₃′ × W₃′)
allW₉′ = pairsOf allW₃′ allW₃′

allW₉′-complete : (w : W₃′ × W₃′) → w ∈ allW₉′
allW₉′-complete (a , b) = ∈-pairsOf (allW₃′-complete a) (allW₃′-complete b)

splSq-no-interface-of-size-3 :
  any? (suffices splSq allA₄′) (tuples 3 allW₉′) ≡ false
splSq-no-interface-of-size-3 = refl

splSq-interface-4 :
  suffices splSq allA₄′
    ((u , u) ∷ (u , z) ∷ (z , u) ∷ (z , z) ∷ []) ≡ true
splSq-interface-4 = refl

-- Claim M, stated as the compression it asserts, and killed.
ClaimM : Type₀
ClaimM =
  Σ[ S ∈ List (W₃′ × W₃′) ]
    ((length S ≡ 3) × (suffices splSq allA₄′ S ≡ true))

claimM-refuted : ¬ ClaimM
claimM-refuted (S , len , h) =
  exhaustive allW₉′-complete splSq allA₄′ 3 splSq-no-interface-of-size-3
    S len h

-- Non-vacuity control for §4's search, and for §3's.
refutation-enumeration-sizes :
  (length allW₉′ ≡ 9) × (length (tuples 3 allW₉′) ≡ 729)
  × (length allW₄ ≡ 4) × (length (tuples 3 allW₄) ≡ 64)
refutation-enumeration-sizes = refl , refl , refl , refl

------------------------------------------------------------------------
-- 5.  The double elimination, and what it will not do.
--
-- Archimedes concludes equality by eliminating both inequalities.  On ℕ
-- that is trichotomy elimination and it is constructively available.
------------------------------------------------------------------------

outeMeizonOuteElasson : (m n : ℕ) → ¬ (m < n) → ¬ (n < m) → m ≡ n
outeMeizonOuteElasson m n ¬less ¬greater with m ≟ n
... | lt p = Empty.rec (¬less p)
... | eq p = p
... | gt p = Empty.rec (¬greater p)

-- THE HYPOTHESIS THE ARGUMENT CONSUMES, made visible by its absence.
-- Both eliminations must be available.  A bracket that merely BOUNDS a
-- quantity on two sides, without being drivable below any assigned
-- magnitude, supplies neither: two distinct values sit inside it.  This is
-- Eudoxus' admission condition (Elements V def. 4) doing its work through
-- the bisection lemma (Elements X.1), stated as the negative.
openBracketDecidesNothing :
  (l h : ℕ) → l < h
  → Σ[ p ∈ (ℕ × ℕ) ]
      ( ((l ≤ fst p) × (fst p ≤ h))
      × ((l ≤ snd p) × (snd p ≤ h))
      × (¬ (fst p ≡ snd p)) )
openBracketDecidesNothing l h l<h =
  (l , h)
  , ( (≤-refl , <-weaken l<h)
    , (<-weaken l<h , ≤-refl)
    , <→≢ l<h )

-- DELTA 02'S OWN BRACKET, AT n = 4, IN EXACT INTEGERS.
--
-- §9 Corollary 4.1: κ₀(Rⁿ) ≥ τ*(R)ⁿ, and for the triangle τ* = 3/2.  At
-- n = 4 that is κ₀(R⁴) ≥ (3/2)⁴ = 81/16; since 16·5 = 80 < 81 ≤ 96 = 16·6,
-- the integer lower bound is 6.  §8 submultiplicativity with §2's
-- κ₀(R²) = 3 gives κ₀(R⁴) ≤ 3² = 9.
lower-bound-is-six : (16 · 5 < 81) × (81 ≤ 16 · 6)
lower-bound-is-six = (0 , refl) , (15 , refl)

bracket-at-four-is-open : 6 < 9
bracket-at-four-is-open = 2 , refl

-- Hence Delta 02 §10's frontier, "Prove or disprove G∞=0", is NOT settled
-- by the bracket it arrives with.  Dirac's extrapolation may still be true.
-- It is not demonstrated — in precisely the sense the *Method*'s preface
-- uses of its own mechanical results.
G∞-is-not-decided-by-this-bracket :
  Σ[ p ∈ (ℕ × ℕ) ]
    ( ((6 ≤ fst p) × (fst p ≤ 9))
    × ((6 ≤ snd p) × (snd p ≤ 9))
    × (¬ (fst p ≡ snd p)) )
G∞-is-not-decided-by-this-bracket =
  openBracketDecidesNothing 6 9 bracket-at-four-is-open

------------------------------------------------------------------------
-- 6.  No size-respecting factorisation of a parallel regulator.
--
-- The thing that would rescue Ashby's number is an OPERATION, not the
-- failure of a search.  A `FactorBound` turns any sufficient interface for
-- the parallel task into two interfaces for the factors whose sizes
-- multiply to no more than the given one.  It does not exist.
------------------------------------------------------------------------

short-not-sufficient :
  (T : List W₃) → length T ≤ 1 → ¬ (suffices tri allA₃ T ≡ true)
short-not-sufficient []            _  p = false≢true p
short-not-sufficient (e₁₂ ∷ [])    _  p = false≢true p
short-not-sufficient (e₁₃ ∷ [])    _  p = false≢true p
short-not-sufficient (e₂₃ ∷ [])    _  p = false≢true p
short-not-sufficient (_ ∷ _ ∷ _)   le _ = Empty.rec (¬-<-zero (pred-≤-pred le))

two-or-more : (T : List W₃) → suffices tri allA₃ T ≡ true → 2 ≤ length T
two-or-more T h with 1 ≟ length T
... | lt p = p
... | eq p = Empty.rec (short-not-sufficient T (0 , sym p) h)
... | gt p = Empty.rec (short-not-sufficient T (<-weaken p) h)

FactorBound : Type₀
FactorBound =
  (S : List W₉) → suffices triSq allA₉ S ≡ true
  → Σ[ T ∈ List W₃ ] Σ[ T′ ∈ List W₃ ]
      ( (suffices tri allA₃ T ≡ true)
      × (suffices tri allA₃ T′ ≡ true)
      × (length T · length T′ ≤ length S) )

no-factor-bound : ¬ FactorBound
no-factor-bound factor = ¬m<m {3} (≤-trans four≤ab bound)
  where
  r  = factor ownerInterface triSq-interface-3
  T  = fst r
  T′ = fst (snd r)
  a  = length T
  b  = length T′
  two  : 2 ≤ a
  two  = two-or-more T  (fst (snd (snd r)))
  two′ : 2 ≤ b
  two′ = two-or-more T′ (fst (snd (snd (snd r))))
  bound : a · b ≤ length ownerInterface
  bound = snd (snd (snd (snd r)))
  s1 : 2 · 2 ≤ a · 2
  s1 = ≤-·k two
  s2 : 2 · a ≤ b · a
  s2 = ≤-·k two′
  four≤ab : 4 ≤ a · b
  four≤ab =
    subst (λ w → 2 · 2 ≤ w) (·-comm b a)
      (≤-trans (subst (λ w → 2 · 2 ≤ w) (·-comm a 2) s1) s2)

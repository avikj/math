{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ElsewhereCondition
--
-- utsarga / apavda -- the narrower rule blocks the wider -- as an exact
-- predicate over a guarded rule system, with the theorem
-- form the priority order reaches*, and not a measured contest.
--
-- The Elsewhere Condition (Kiparsky 1973, who coined the term reading
-- Pini; Sanders' Proper Inclusion Precedence) selects, among the rules
-- applicable at a point, the one whose domain is contained in all the
-- others.  What is proved about that selector:
--
--   leastUnique     when it decides, it decides uniquely -- two least
--                   applicable guards have the same domain.  This is the
--                   determinism half.
--
--   chainRooted     if the guard domains form an ascending chain, a least
--                   applicable guard exists at every point where anything
--                   applies.  (utsarga/apavda alone suffices.)
--
--   directedRooted  the general sufficient condition: it is enough that
--                   any two applicable guards have a common applicable
--                   lower bound *in the family*.  This is the repair --
--                   the grammar must state the narrower rule for the
--                   overlap; then the Elsewhere Condition is complete.
--
--   repairedRooted  directedness is strictly weaker than laminarity
--                   ("every two domains disjoint or nested").  A three-rule
--                   system that is Elsewhere-complete everywhere while
--                   still containing a properly crossing pair
--                   (`gAgB-cross`) is exhibited.  So the taxonomy under
--                   which rule-conflict analysers flag an *intersecting*
--                   pair as an anomaly over-flags: a crossing is harmless
--                   whenever the overlap is separately covered.
--
--   noLeastCrossing / noEquivariantTiebreak
--                   the existence half fails, and fails irreparably from
--                   inside.  Two guards that properly cross admit no least
--                   element at the crossing point (`noLeastCrossing`), and
--                   -- the sharper statement -- NO relabelling-invariant
--                   tiebreak can choose between them (`noEquivariantTiebreak`),
--                   because the carrier has an involution that fixes the
--                   disputed point and exchanges the two guards.
--
--                   Hence A 1.4.2 (vipratiedhe para kryam) is logically
--                   INDEPENDENT of the apavda principle, on either reading
--                   of it: whether "the later rule wins" (traditional) or
--                   "the rule applying to the right-hand operand wins"
--                   (Rajpopat 2022), the tiebreak must import data --
--                   textual position, or operand position -- that the guard
--                   family does not carry.  The formal content of "must
--                   import data" is failure of equivariance, and that is
--                   what `noEquivariantTiebreak` proves.  This module takes
--                   no side in the Rajpopat dispute; it shows both sides are
--                   answering a question apavda provably cannot.
--
-- The instance is the ancient one: Ethiopian / Egyptian doubling
-- multiplication.  Its three rules (`stop at zero`, `halve-and-double`,
-- `peel one`) have domains {0} ⊆ evens ⊆ ℕ -- a chain -- so `chainRooted`
-- applies and the dispatch is total and deterministic with no tiebreak
-- whatever (`dispatchZero`, `dispatchEven`, `dispatchOdd`).  The normal
-- form it reaches is the product: `egyCorrect`.
--
-- Note what the chain condition costs.  A rule list sorted narrowest-first
-- needs no metarule at all: first-match-wins already IS the Elsewhere
-- Condition.  Pini's text is not so sorted -- the utsarga is routinely
-- stated before its own apavda -- which is precisely why the Adhyy
-- needs 1.4.1/1.4.2 as metarules rather than as an editorial convention.
------------------------------------------------------------------------

module ElsewhereCondition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty as ⊥ using (⊥ ; ⊥*)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; +-suc
                                   ; ·-distribʳ ; ·-distribˡ)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §0  Guarded rule systems
--
-- A rule is identified with its guard: the decidable predicate cutting out
-- the inputs it applies to.  (`runtime/panini/conflict.py` (absent from this repository) reaches the same
-- predicate syntactically, through pattern subsumption; the extensional
-- version is what the principle is about, and is what is proved here.)
------------------------------------------------------------------------

Guard : Type ℓ → Type ℓ
Guard A = A → Bool

-- "rule g fires at x"
Holds : {A : Type ℓ} → Guard A → A → Type
Holds g x = g x ≡ true

-- domain containment: g is at least as narrow as h.
-- `g ⋐ h` is exactly "h is the utsarga, g a candidate apavda to it".
_⋐_ : {A : Type ℓ} → Guard A → Guard A → Type ℓ
_⋐_ {A = A} g h = (x : A) → Holds g x → Holds h x

⋐-refl : {A : Type ℓ} (g : Guard A) → g ⋐ g
⋐-refl g x p = p

⋐-trans : {A : Type ℓ} {g h k : Guard A} → g ⋐ h → h ⋐ k → g ⋐ k
⋐-trans p q x r = q x (p x r)

-- Membership in the rule book, as a recursive family rather than an
-- inductive one: pattern matching on an inductive `_∈_` whose index is
-- `h ∷ gs` would rest on injectivity of `_∷_`, which Cubical Agda does not
-- support.  Recursion on the list avoids the issue entirely.
_∈_ : {A : Type ℓ} → Guard A → List (Guard A) → Type ℓ
_∈_ {ℓ} g [] = ⊥* {ℓ}
g ∈ (h ∷ gs) = (g ≡ h) ⊎ (g ∈ gs)

pattern here p = inl p
pattern there m = inr m

-- `g ∈ []` reduces to `⊥*`, so this eliminates any empty-book membership
-- without needing to recover the carrier from the (carrier-free) type.
∉[] : {ℓ' : Level} {B : Type ℓ'} → ⊥* {ℓ} → B
∉[] m = ⊥.rec* m

------------------------------------------------------------------------
-- §1  What the Elsewhere Condition selects
------------------------------------------------------------------------

-- g is THE apavda at x: it is in the book, it fires at x, and its domain
-- is contained in the domain of every other rule of the book that fires
-- at x.
record IsLeast {A : Type ℓ} (gs : List (Guard A)) (x : A) (g : Guard A)
       : Type ℓ where
  constructor least
  field
    mem  : g ∈ gs
    fire : Holds g x
    narr : (h : Guard A) → h ∈ gs → Holds h x → g ⋐ h

open IsLeast public

-- The system is Elsewhere-complete ("rooted") when the selection succeeds
-- wherever any rule at all applies.
Rooted : {A : Type ℓ} → List (Guard A) → Type ℓ
Rooted {ℓ} {A} gs =
  (x : A) → Σ[ g ∈ Guard A ] ((g ∈ gs) × Holds g x)
          → Σ[ g ∈ Guard A ] IsLeast gs x g

------------------------------------------------------------------------
-- §2  Determinism: when the Elsewhere Condition decides, it decides once
--
-- Two least applicable guards have the same domain.  (Not the same *term*
-- -- a grammar may state the same domain twice -- but the selector is a
-- function of the domain, so this is the strongest uniqueness available
-- and the only one the principle claims.)
------------------------------------------------------------------------

⋐-antisym : {A : Type ℓ} {g h : Guard A}
          → g ⋐ h → h ⋐ g → (x : A) → g x ≡ h x
⋐-antisym {g = g} {h = h} p q x with dichotomyBool (g x)
... | inl gt = gt ∙ sym (p x gt)
... | inr gf with dichotomyBool (h x)
...   | inl ht = ⊥.rec (false≢true (sym gf ∙ q x ht))
...   | inr hf = gf ∙ sym hf

leastUnique : {A : Type ℓ} {gs : List (Guard A)} {x : A} {g g' : Guard A}
            → IsLeast gs x g → IsLeast gs x g' → (y : A) → g y ≡ g' y
leastUnique {g = g} {g' = g'} l l' =
  ⋐-antisym (narr l g' (mem l') (fire l')) (narr l' g (mem l) (fire l))

------------------------------------------------------------------------
-- §3  Sufficient condition I: a chain of domains
--
-- `Chain gs` says each rule's domain is contained in the domain of every
-- rule stated after it -- the book is sorted narrowest-first.
------------------------------------------------------------------------

Chain : {A : Type ℓ} → List (Guard A) → Type ℓ
Chain {ℓ} [] = Unit* {ℓ}
Chain {A = A} (g ∷ gs) = ((h : Guard A) → h ∈ gs → g ⋐ h) × Chain gs

chainRooted : {A : Type ℓ} (gs : List (Guard A)) → Chain gs → Rooted gs
chainRooted [] _ x (g , m , _) = ∉[] m
chainRooted (k ∷ ks) (kmin , ch) x (g , m , hg)
  with dichotomyBool (k x)
... | inl kt = k , least (here refl) kt nrr
  where
    nrr : (h : Guard _) → h ∈ (k ∷ ks) → Holds h x → k ⋐ h
    nrr h (here p)  _ = subst (k ⋐_) (sym p) (⋐-refl k)
    nrr h (there mh) _ = kmin h mh
... | inr kf = rec' m
  where
    step : Σ[ g' ∈ Guard _ ] IsLeast ks x g'
         → Σ[ g' ∈ Guard _ ] IsLeast (k ∷ ks) x g'
    step (g' , l) = g' , least (there (mem l)) (fire l) nrr
      where
        nrr : (h : Guard _) → h ∈ (k ∷ ks) → Holds h x → g' ⋐ h
        nrr h (here p) hh = ⊥.rec (false≢true (sym kf ∙ sym (cong (λ u → u x) p) ∙ hh))
        nrr h (there mh) hh = narr l h mh hh
    rec' : g ∈ (k ∷ ks) → Σ[ g' ∈ Guard _ ] IsLeast (k ∷ ks) x g'
    rec' (here p)  = ⊥.rec (false≢true (sym kf ∙ sym (cong (λ u → u x) p) ∙ hg))
    rec' (there mg) = step (chainRooted ks ch x (g , mg , hg))

------------------------------------------------------------------------
-- §4  Sufficient condition II: downward directedness -- the repair
--
-- The chain condition is far stronger than necessary.  All that is needed
-- is that whenever two rules of the book compete at x, the book ALSO
-- contains a rule that fires at x and is narrower than both.  This is the
-- grammarian's actual move: when two rules cross, state a third, narrower
-- rule for the overlap.  Adding the pairwise meets of the guard family
-- (its intersection-closure) is exactly the canonical way to achieve it.
--
-- The theorem is the finite-directedness argument: a finite downward
-- directed nonempty family has a least element.  The induction carries a
-- running candidate and is the mechanised form of "keep composing
-- exceptions".
------------------------------------------------------------------------

Directed : {A : Type ℓ} → List (Guard A) → A → Type ℓ
Directed {ℓ} {A} gs x =
  (g h : Guard A) → g ∈ gs → h ∈ gs → Holds g x → Holds h x
  → Σ[ k ∈ Guard A ] ((k ∈ gs) × Holds k x × (k ⋐ g) × (k ⋐ h))

module _ {A : Type ℓ} (gs : List (Guard A)) (x : A) (dir : Directed gs x) where

  private
    Below : List (Guard A) → Guard A → Type ℓ
    Below rest k = (h : Guard A) → h ∈ rest → Holds h x → k ⋐ h

    Cand : List (Guard A) → Guard A → Type ℓ
    Cand rest c =
      Σ[ k ∈ Guard A ] ((k ∈ gs) × Holds k x × (k ⋐ c) × Below rest k)

    -- sweep `rest` (a sublist of the book) refining the candidate `c`
    sweep : (rest : List (Guard A))
          → ((h : Guard A) → h ∈ rest → h ∈ gs)
          → (c : Guard A) → c ∈ gs → Holds c x
          → Cand rest c
    sweep [] _ c mc hc = c , mc , hc , ⋐-refl c , λ h m _ → ∉[] m
    sweep (r ∷ rs) sub c mc hc with dichotomyBool (r x)
    ... | inr rf =
      let (k , mk , hk , kc , bel) = sweep rs (λ h m → sub h (there m)) c mc hc
      in k , mk , hk , kc , nrr k bel
      where
        nrr : (k : Guard A) → Below rs k → Below (r ∷ rs) k
        nrr k bel h (here p) hh =
          ⊥.rec (false≢true (sym rf ∙ sym (cong (λ u → u x) p) ∙ hh))
        nrr k bel h (there m) hh = bel h m hh
    ... | inl rt =
      let (k₀ , mk₀ , hk₀ , k₀c , k₀r) = dir c r mc (sub r (here refl)) hc rt
          (k , mk , hk , kk₀ , bel)    = sweep rs (λ h m → sub h (there m)) k₀ mk₀ hk₀
      in k , mk , hk , ⋐-trans kk₀ k₀c , nrr k kk₀ bel
      where
        nrr : (k : Guard A) → k ⋐ _ → Below rs k → Below (r ∷ rs) k
        nrr k kk₀ bel h (here p) hh =
          subst (k ⋐_) (sym p) (⋐-trans kk₀ (dir c r mc (sub r (here refl)) hc rt .snd .snd .snd .snd))
        nrr k kk₀ bel h (there m) hh = bel h m hh

  directedRooted : Σ[ g ∈ Guard A ] ((g ∈ gs) × Holds g x)
                 → Σ[ g ∈ Guard A ] IsLeast gs x g
  directedRooted (g , mg , hg) =
    let (k , mk , hk , _ , bel) = sweep gs (λ _ m → m) g mg hg
    in k , least mk hk bel

------------------------------------------------------------------------
-- §5  The no-go: apavda alone is incomplete, and the gap is not
--     closable from inside the guard family
--
-- Three points, two rules whose domains properly cross:
--
--       gA = {t0, t1}        gB = {t1, t2}
--
-- At t1 both fire and neither is narrower.  Worse: the involution
-- swapping t0 and t2 fixes t1 and exchanges gA with gB, so the two rules
-- are indistinguishable by anything the family itself provides.
------------------------------------------------------------------------

data Three : Type₀ where
  t0 t1 t2 : Three

gA gB : Guard Three
gA t0 = true
gA t1 = true
gA t2 = false
gB t0 = false
gB t1 = true
gB t2 = true

crossing : List (Guard Three)
crossing = gA ∷ gB ∷ []

crossingFires : Σ[ g ∈ Guard Three ] ((g ∈ crossing) × Holds g t1)
crossingFires = gA , here refl , refl

-- (a) the Elsewhere Condition returns nothing at the crossing point.
noLeastCrossing : ¬ (Σ[ g ∈ Guard Three ] IsLeast crossing t1 g)
noLeastCrossing (g , l) = split (mem l)
  where
    gA⋐ : g ⋐ gA
    gA⋐ = narr l gA (here refl) refl
    gB⋐ : g ⋐ gB
    gB⋐ = narr l gB (there (here refl)) refl
    split : g ∈ crossing → ⊥
    split (here p) =
      -- g ≡ gA, so gA ⋐ gB; but gA fires at t0 and gB does not
      false≢true (gB⋐ t0 (cong (λ u → u t0) p))
    split (there (here p)) =
      -- g ≡ gB, so gB ⋐ gA; but gB fires at t2 and gA does not
      false≢true (gA⋐ t2 (cong (λ u → u t2) p))
    split (there (there m)) = ∉[] m

-- (b) the carrier symmetry that makes the two rules interchangeable
swap3 : Three → Three
swap3 t0 = t2
swap3 t1 = t1
swap3 t2 = t0

swap3-invol : (y : Three) → swap3 (swap3 y) ≡ y
swap3-invol t0 = refl
swap3-invol t1 = refl
swap3-invol t2 = refl

swap3-fixes : swap3 t1 ≡ t1
swap3-fixes = refl

gA∘swap≡gB : (y : Three) → gA (swap3 y) ≡ gB y
gA∘swap≡gB t0 = refl
gA∘swap≡gB t1 = refl
gA∘swap≡gB t2 = refl

gB∘swap≡gA : (y : Three) → gB (swap3 y) ≡ gA y
gB∘swap≡gA t0 = refl
gB∘swap≡gA t1 = refl
gB∘swap≡gA t2 = refl

-- (c) THE no-go.  A tiebreak is a function `sel` that, given two competing
-- guards and the point, returns one of them.  Ask of it only three things:
--
--   pick : it returns one of the two guards it was handed;
--   symm : it depends on the *pair* of rules, not on which argument slot
--          each was passed in;
--   equi : relabelling the carrier by an involution, and the point with
--          it, relabels the answer -- the tiebreak reads the guards as
--          subsets and the point, and nothing else.
--
-- No such `sel` exists.  All three hypotheses are needed, and each is
-- separately satisfiable, so the statement is not vacuous:
--   * drop `equi`: the textual-order tiebreak -- "return whichever of the
--     two is stated earlier in a fixed enumeration of the book" -- has
--     `pick` and `symm`.  This is exactly *para* (A 1.4.2, traditional
--     reading), and the theorem says its content is precisely the
--     arbitrary enumeration, not anything the rules themselves carry.
--   * drop `symm`: `sel g h y = g` has `pick` and `equi`.
--   * drop `pick`: any constant `sel` has `symm` and `equi`.
-- Restricting `equi` to involutions only weakens that hypothesis, so this
-- is stronger than the version quantified over all carrier automorphisms.
noEquivariantTiebreak :
    (sel : Guard Three → Guard Three → Three → Guard Three)
  → ((g h : Guard Three) (y : Three) → (sel g h y ≡ g) ⊎ (sel g h y ≡ h))
  → ((g h : Guard Three) (y : Three) → sel g h y ≡ sel h g y)
  → ((g h : Guard Three) (y : Three) (π : Three → Three)
       → ((z : Three) → π (π z) ≡ z)
       → sel (λ z → g (π z)) (λ z → h (π z)) (π y)
         ≡ (λ z → sel g h y (π z)))
  → ⊥
noEquivariantTiebreak sel pick symm equi = branch (pick gA gB t1)
  where
    s : Guard Three
    s = sel gA gB t1
    -- relabelling by swap3 turns (gA , gB , t1) into (gB , gA , t1)
    pA : (λ z → gA (swap3 z)) ≡ gB
    pA = funExt gA∘swap≡gB
    pB : (λ z → gB (swap3 z)) ≡ gA
    pB = funExt gB∘swap≡gA
    relabel : sel gB gA t1 ≡ (λ z → s (swap3 z))
    relabel =
      cong₂ (λ u v → sel u v t1) (sym pA) (sym pB)
      ∙ equi gA gB t1 swap3 swap3-invol
    -- the selected guard is therefore swap3-invariant ...
    fix : s t0 ≡ s t2
    fix = funExt⁻ (symm gA gB t1 ∙ relabel) t0
    -- ... but neither gA nor gB is.
    branch : (s ≡ gA) ⊎ (s ≡ gB) → ⊥
    branch (inl q) =
      true≢false (sym (funExt⁻ q t0) ∙ fix ∙ funExt⁻ q t2)
    branch (inr q) =
      false≢true (sym (funExt⁻ q t0) ∙ fix ∙ funExt⁻ q t2)

-- Non-vacuity, mechanised for two of the three hypotheses: dropping `symm`,
-- or dropping `pick`, leaves the remaining hypotheses satisfiable.
selFirst : Guard Three → Guard Three → Three → Guard Three
selFirst g _ _ = g

selFirst-pick : (g h : Guard Three) (y : Three)
              → (selFirst g h y ≡ g) ⊎ (selFirst g h y ≡ h)
selFirst-pick g h y = inl refl

selFirst-equi : (g h : Guard Three) (y : Three) (π : Three → Three)
              → ((z : Three) → π (π z) ≡ z)
              → selFirst (λ z → g (π z)) (λ z → h (π z)) (π y)
                ≡ (λ z → selFirst g h y (π z))
selFirst-equi g h y π inv = refl

selConst : Guard Three → Guard Three → Three → Guard Three
selConst _ _ _ = λ _ → true

selConst-symm : (g h : Guard Three) (y : Three)
              → selConst g h y ≡ selConst h g y
selConst-symm g h y = refl

selConst-equi : (g h : Guard Three) (y : Three) (π : Three → Three)
              → ((z : Three) → π (π z) ≡ z)
              → selConst (λ z → g (π z)) (λ z → h (π z)) (π y)
                ≡ (λ z → selConst g h y (π z))
selConst-equi g h y π inv = refl

-- (d) the repair, on the very system that fails: state the apavda for the
-- overlap.  `gM` cuts out {t1} = gA ∩ gB, and the Elsewhere Condition is
-- restored -- with no tiebreak, and no appeal to rule order.
gM : Guard Three
gM t0 = false
gM t1 = true
gM t2 = false

repaired : List (Guard Three)
repaired = gM ∷ gA ∷ gB ∷ []

gM⋐gA : gM ⋐ gA
gM⋐gA t0 p = ⊥.rec (false≢true p)
gM⋐gA t1 _ = refl
gM⋐gA t2 p = ⊥.rec (false≢true p)

gM⋐gB : gM ⋐ gB
gM⋐gB t0 p = ⊥.rec (false≢true p)
gM⋐gB t1 _ = refl
gM⋐gB t2 p = ⊥.rec (false≢true p)

repairedLeast : IsLeast repaired t1 gM
repairedLeast = least (here refl) refl nrr
  where
    nrr : (h : Guard Three) → h ∈ repaired → Holds h t1 → gM ⋐ h
    nrr h (here p) _               = subst (gM ⋐_) (sym p) (⋐-refl gM)
    nrr h (there (here p)) _       = subst (gM ⋐_) (sym p) gM⋐gA
    nrr h (there (there (here p))) _ = subst (gM ⋐_) (sym p) gM⋐gB
    nrr h (there (there (there m))) _ = ∉[] m

-- `repaired` is Elsewhere-complete at EVERY point, and it is still not
-- laminar: gA and gB cross exactly as before.  So the folk condition
-- "disjoint or nested" (the taxonomy under which rule-conflict analysers
-- flag an `intersecting` pair as an anomaly) is SUFFICIENT BUT NOT
-- NECESSARY.  The correct condition is pointwise directedness -- an
-- intersecting pair is harmless whenever the overlap is separately
-- covered.
repairedRooted : Rooted repaired
repairedRooted t0 _ = gA , least (there (here refl)) refl nrr
  where
    nrr : (h : Guard Three) → h ∈ repaired → Holds h t0 → gA ⋐ h
    nrr h (here p) hh = ⊥.rec (false≢true (sym (funExt⁻ p t0) ∙ hh))
    nrr h (there (here p)) _ = subst (gA ⋐_) (sym p) (⋐-refl gA)
    nrr h (there (there (here p))) hh =
      ⊥.rec (false≢true (sym (funExt⁻ p t0) ∙ hh))
    nrr h (there (there (there m))) _ = ∉[] m
repairedRooted t1 _ = gM , repairedLeast
repairedRooted t2 _ = gB , least (there (there (here refl))) refl nrr
  where
    nrr : (h : Guard Three) → h ∈ repaired → Holds h t2 → gB ⋐ h
    nrr h (here p) hh = ⊥.rec (false≢true (sym (funExt⁻ p t2) ∙ hh))
    nrr h (there (here p)) hh = ⊥.rec (false≢true (sym (funExt⁻ p t2) ∙ hh))
    nrr h (there (there (here p))) _ = subst (gB ⋐_) (sym p) (⋐-refl gB)
    nrr h (there (there (there m))) _ = ∉[] m

-- ... and the crossing pair genuinely still crosses inside `repaired`:
gAgB-cross : (¬ (gA ⋐ gB)) × (¬ (gB ⋐ gA))
gAgB-cross = (λ c → false≢true (c t0 refl)) , (λ c → false≢true (c t2 refl))

------------------------------------------------------------------------
-- §6  The instance: Ethiopian / Egyptian doubling multiplication
--
-- Three rules on the multiplier:
--
--   Z  a = 0        -- stop
--   D  a even       -- halve a, double b
--   S  otherwise    -- peel one b off and continue
--
-- Their domains are {0} ⊆ evens ⊆ ℕ: a chain.  So `chainRooted` gives a
-- total, deterministic dispatch at every ℕ, with NO tiebreak -- neither
-- para nor position.  The doubling algorithm is thus the (rare) case where
-- utsarga/apavda is by itself a complete strategy.
------------------------------------------------------------------------

even? : ℕ → Bool
even? zero = true
even? (suc zero) = false
even? (suc (suc n)) = even? n

isZero? : ℕ → Bool
isZero? zero = true
isZero? (suc _) = false

gZero gEven gAny : Guard ℕ
gZero = isZero?
gEven = even?
gAny _ = true

gZero⋐gEven : gZero ⋐ gEven
gZero⋐gEven zero _ = refl
gZero⋐gEven (suc n) p = ⊥.rec (false≢true p)

⋐gAny : (g : Guard ℕ) → g ⋐ gAny
⋐gAny g _ _ = refl

doubling : List (Guard ℕ)
doubling = gZero ∷ gEven ∷ gAny ∷ []

doublingChain : Chain doubling
doublingChain = z , e , a , tt*
  where
    z : (h : Guard ℕ) → h ∈ (gEven ∷ gAny ∷ []) → gZero ⋐ h
    z h (here p) = subst (gZero ⋐_) (sym p) gZero⋐gEven
    z h (there (here p)) = subst (gZero ⋐_) (sym p) (⋐gAny gZero)
    z h (there (there m)) = ∉[] m
    e : (h : Guard ℕ) → h ∈ (gAny ∷ []) → gEven ⋐ h
    e h (here p) = subst (gEven ⋐_) (sym p) (⋐gAny gEven)
    e h (there m) = ∉[] m
    a : (h : Guard ℕ) → h ∈ [] → gAny ⋐ h
    a h m = ∉[] m

-- every ℕ has an applicable rule (gAny), so the dispatch is total
doublingRooted : (n : ℕ) → Σ[ g ∈ Guard ℕ ] IsLeast doubling n g
doublingRooted n =
  chainRooted doubling doublingChain n (gAny , there (there (here refl)) , refl)

-- ... and here is exactly which rule it reaches, in each of the three cases.
dispatchZero : IsLeast doubling zero gZero
dispatchZero = least (here refl) refl nrr
  where
    nrr : (h : Guard ℕ) → h ∈ doubling → Holds h zero → gZero ⋐ h
    nrr h (here p) _ = subst (gZero ⋐_) (sym p) (⋐-refl gZero)
    nrr h (there (here p)) _ = subst (gZero ⋐_) (sym p) gZero⋐gEven
    nrr h (there (there (here p))) _ = subst (gZero ⋐_) (sym p) (⋐gAny gZero)
    nrr h (there (there (there m))) _ = ∉[] m

dispatchEven : (m : ℕ) → even? (suc m) ≡ true → IsLeast doubling (suc m) gEven
dispatchEven m ev = least (there (here refl)) ev nrr
  where
    nrr : (h : Guard ℕ) → h ∈ doubling → Holds h (suc m) → gEven ⋐ h
    nrr h (here p) hh = ⊥.rec (false≢true (sym (cong (λ u → u (suc m)) p) ∙ hh))
    nrr h (there (here p)) _ = subst (gEven ⋐_) (sym p) (⋐-refl gEven)
    nrr h (there (there (here p))) _ = subst (gEven ⋐_) (sym p) (⋐gAny gEven)
    nrr h (there (there (there m'))) _ = ∉[] m'

dispatchOdd : (n : ℕ) → even? n ≡ false → IsLeast doubling n gAny
dispatchOdd n od = least (there (there (here refl))) refl nrr
  where
    notZero : isZero? n ≡ true → ⊥
    notZero = zc n od
      where
        zc : (k : ℕ) → even? k ≡ false → isZero? k ≡ true → ⊥
        zc zero e _ = true≢false e
        zc (suc _) _ r = false≢true r
    nrr : (h : Guard ℕ) → h ∈ doubling → Holds h n → gAny ⋐ h
    nrr h (here p) hh = ⊥.rec (notZero (sym (cong (λ u → u n) p) ∙ hh))
    nrr h (there (here p)) hh =
      ⊥.rec (true≢false (sym (sym (cong (λ u → u n) p) ∙ hh) ∙ od))
    nrr h (there (there (here p))) _ = subst (gAny ⋐_) (sym p) (⋐-refl gAny)
    nrr h (there (there (there m))) _ = ∉[] m

------------------------------------------------------------------------
-- §7  The normal form the priority order reaches
--
-- The halving column of the Egyptian/Ethiopian table IS the binary
-- expansion of the multiplier, least significant digit first; the rows
-- kept are the odd ones.  Taking that trace column as the argument makes
-- the recursion structural -- no fuel, no well-founded order -- which is
-- ryabhaa's move applied to Ames' algorithm: keep the trace column and
-- the equation stops resisting.
------------------------------------------------------------------------

-- value of a trace column (LSB first)
val : List Bool → ℕ
val [] = zero
val (false ∷ bs) = val bs + val bs
val (true  ∷ bs) = suc (val bs + val bs)

-- the doubling algorithm, driven by its own trace column
egy : List Bool → ℕ → ℕ
egy [] b = zero
egy (false ∷ bs) b = egy bs (b + b)
egy (true  ∷ bs) b = b + egy bs (b + b)

-- the halve-and-double rule, as the arithmetic identity it is
ruleDouble : (k b : ℕ) → (k + k) · b ≡ k · (b + b)
ruleDouble k b = sym (·-distribʳ k k b) ∙ ·-distribˡ k b b

egyCorrect : (bs : List Bool) (b : ℕ) → egy bs b ≡ val bs · b
egyCorrect [] b = refl
egyCorrect (false ∷ bs) b =
  egyCorrect bs (b + b) ∙ sym (ruleDouble (val bs) b)
egyCorrect (true ∷ bs) b =
  cong (b +_) (egyCorrect bs (b + b) ∙ sym (ruleDouble (val bs) b))

-- The trace column and the dispatch agree: the guard `even?` reads off
-- exactly the bit the column records, so §6's dispatch is not a separate
-- decision procedure bolted onto §7 -- it is the column.
evenDouble : (n : ℕ) → even? (n + n) ≡ true
evenDouble zero = refl
evenDouble (suc n) = cong even? (cong suc (+-suc n n)) ∙ evenDouble n

oddDouble : (n : ℕ) → even? (suc (n + n)) ≡ false
oddDouble zero = refl
oddDouble (suc n) = cong even? (cong suc (cong suc (+-suc n n))) ∙ oddDouble n

traceEven : (bs : List Bool) → even? (val (false ∷ bs)) ≡ true
traceEven bs = evenDouble (val bs)

traceOdd : (bs : List Bool) → even? (val (true ∷ bs)) ≡ false
traceOdd bs = oddDouble (val bs)

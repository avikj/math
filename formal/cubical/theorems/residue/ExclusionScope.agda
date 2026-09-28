{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- ExclusionScope
--
-- WHAT IS AN EXCLUSION OPERATOR, AND ON WHICH LATTICE DOES IT EXIST?
--
-- The conjecture: that the shape
-- nearest to Dignga's `anypoha` is "a relative pseudo-complement in a
-- lattice" rather than `¬` in a Boolean algebra.  This module settles
-- that conjecture on the repository's OWN meaning-carriers, and the
-- answer is negative.
--
-- The repository's semantics for "what a term/probe/channel means" is
-- fixed by `runtime/render/channel.py` (absent from this repository): a channel is a function on a
-- declared language, and its content is the PARTITION it induces
-- ("the partition of L induced by encode is a coarsening of equality").
-- Probes in `machinery/active_observer_design.py` (absent from this repository) are likewise partitions of a
-- finite set, i.e. equivalence relations.  So the ambient lattice here
-- is Eq(X), not the powerset P(X).
--
-- Contents:
--
--   Theorem 1 (`Imp-is-exclusion`).  On UNRESTRICTED relations the
--     exclusion operator exists, for every X, and is pointwise
--     implication.  So the failure below is not a failure of relations.
--
--   Theorem 2 (`no-exclusion`).  A general obstruction: if two
--     admissible exclusions T₁, T₂ connect u and v through a common
--     third point w, then {τ : τ ⊓ P ⊑ S} has no greatest element.
--     The single mechanism is TRANSITIVITY.
--
--   Theorem 3 (`three-coordinates`).  Instance on three points: with
--     P the term "a,b" and S equality, no exclusion exists.  Three
--     pairwise-incompatible coordinate terms are already enough.
--
--   Theorem 4 (`declared-vocabulary`).  Instance on X = Bool × Bool
--     with two declared coordinates: RELATIVE TO the declared
--     four-element vocabulary {Δ, kfst, ksnd, ⊤} the exclusion of
--     `kfst` relative to Δ exists and IS `ksnd` — literally set
--     difference on the vocabulary index.  `no-vocabulary-extension`
--     then shows this operator does NOT survive admitting one further
--     equivalence (parity) that the vocabulary did not list.
--
-- Theorem 4 is the formal content of `INDIC_FORMAL_TRADITIONS_MAP.md` (absent from this repository)
-- §2.3's warning about `Obstruction.agda`: a residual drawn from a
-- fixed finite vocabulary IS an exclusion operator, but only on the
-- Boolean algebra of that vocabulary's index set — the pre-given
-- universe.  §2.3 said "do not call it apoha"; Theorem 3 + Theorem 4
-- say why, exactly: the operator does not extend past the list.
------------------------------------------------------------------------

module ExclusionScope where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 0. Relations, equivalence, refinement order, meet
------------------------------------------------------------------------

Rel : Type₀ → Type₁
Rel X = X → X → Type₀

record IsEq {X : Type₀} (R : Rel X) : Type₀ where
  constructor iseq
  field
    rfl : (x : X) → R x x
    sm  : {x y : X} → R x y → R y x
    tr  : {x y z : X} → R x y → R y z → R x z

open IsEq public

-- Refinement: R ⊑ S says R separates at least as much as S, i.e. R is
-- the finer partition.  This is the ONLY comparison used below.
_⊑_ : {X : Type₀} → Rel X → Rel X → Type₀
_⊑_ {X} R S = (x y : X) → R x y → S x y

_⊓_ : {X : Type₀} → Rel X → Rel X → Rel X
(R ⊓ S) x y = R x y × S x y

⊓-left : {X : Type₀} (R S : Rel X) → (R ⊓ S) ⊑ R
⊓-left R S x y h = fst h

⊓-right : {X : Type₀} (R S : Rel X) → (R ⊓ S) ⊑ S
⊓-right R S x y h = snd h

⊓-greatest : {X : Type₀} (T R S : Rel X) → T ⊑ R → T ⊑ S → T ⊑ (R ⊓ S)
⊓-greatest T R S h k x y t = h x y t , k x y t

⊓-IsEq : {X : Type₀} (R S : Rel X) → IsEq R → IsEq S → IsEq (R ⊓ S)
⊓-IsEq R S e f =
  iseq (λ x → rfl e x , rfl f x)
       (λ h → sm e (fst h) , sm f (snd h))
       (λ h k → tr e (fst h) (fst k) , tr f (snd h) (snd k))

-- Kernels are the canonical equivalence relations: `ker c` is exactly
-- what `runtime/render/channel.py` (absent from this repository) calls the fibre partition of a
-- channel `c`.  Being an equivalence is path algebra, nothing more.
ker : {X Y : Type₀} → (X → Y) → Rel X
ker f x y = f x ≡ f y

ker-IsEq : {X Y : Type₀} (f : X → Y) → IsEq (ker f)
ker-IsEq f = iseq (λ _ → refl) sym _∙_

------------------------------------------------------------------------
-- 1. Exclusion, defined as the universal property and nothing else
--
-- `Excludes P S E` says: E is the greatest equivalence whose overlap
-- with P is confined to S.  Read: "E is what P excludes, relative to
-- the scope S".  Setting S = Δ gives the absolute reading that the
-- popular gloss "cow = not-(non-cow)" presupposes.
------------------------------------------------------------------------

Excludes : {X : Type₀} (P S E : Rel X) → Type₁
Excludes {X} P S E =
    IsEq E
  × ((E ⊓ P) ⊑ S)
  × ((T : Rel X) → IsEq T → (T ⊓ P) ⊑ S → T ⊑ E)

HasExclusion : {X : Type₀} (P S : Rel X) → Type₁
HasExclusion {X} P S = Σ[ E ∈ Rel X ] Excludes P S E

-- The operator, when it exists, is determined: nonexistence below is
-- therefore a statement about the scope, not about a bad choice.
excludes-unique : {X : Type₀} (P S E E' : Rel X)
                → Excludes P S E → Excludes P S E'
                → (E ⊑ E') × (E' ⊑ E)
excludes-unique P S E E' (eE , mE , gE) (eE' , mE' , gE') =
  gE' E eE mE , gE E' eE' mE'

-- CONTROL (non-vacuity).  `Excludes` is satisfiable inside Eq(X): the
-- universal term excludes exactly equality, for every X.  So the two
-- nonexistence theorems below are not artefacts of an unsatisfiable
-- definition.
topRel : {X : Type₀} → Rel X
topRel _ _ = Unit

idKer : {X : Type₀} → Rel X
idKer {X} = ker (λ (x : X) → x)

top-excludes-id : {X : Type₀} → Excludes (topRel {X}) (idKer {X}) (idKer {X})
top-excludes-id =
    ker-IsEq (λ x → x)
  , (λ x y h → fst h)
  , (λ T _ m x y t → m x y (t , tt))

------------------------------------------------------------------------
-- 2. Theorem 1 — on unrestricted relations, exclusion always exists
--
-- Pointwise implication is the exclusion operator on Rel X, for EVERY
-- X.  This is the control: whatever goes wrong in §4 is not caused by
-- relations, by constructivity, or by the definition of `Excludes`.
------------------------------------------------------------------------

Imp : {X : Type₀} → Rel X → Rel X → Rel X
Imp P S x y = P x y → S x y

Imp-meet : {X : Type₀} (P S : Rel X) → ((Imp P S) ⊓ P) ⊑ S
Imp-meet P S x y h = fst h (snd h)

Imp-greatest : {X : Type₀} (P S T : Rel X) → (T ⊓ P) ⊑ S → T ⊑ Imp P S
Imp-greatest P S T h x y t p = h x y (t , p)

------------------------------------------------------------------------
-- 3. Theorem 2 — the general obstruction, in positive form
--
-- The load-bearing lemma is `joins-through`, and it contains no
-- negation at all: any equivalence lying above two admissible
-- exclusions ALREADY RELATES the two points they were meant to keep
-- apart, because both reach a common third point w.  Transitivity is
-- the entire mechanism.  The nonexistence statement is its corollary,
-- and is the only place falsity is used.
------------------------------------------------------------------------

joins-through : {X : Type₀} (E T₁ T₂ : Rel X) (u v w : X)
              → IsEq E → T₁ ⊑ E → T₂ ⊑ E
              → T₁ u w → T₂ v w
              → E u v
joins-through E T₁ T₂ u v w eE h₁ h₂ t₁ t₂ =
  tr eE (h₁ u w t₁) (sm eE (h₂ v w t₂))

no-exclusion : {X : Type₀} (P S T₁ T₂ : Rel X) (u v w : X)
             → IsEq T₁ → IsEq T₂
             → (T₁ ⊓ P) ⊑ S → (T₂ ⊓ P) ⊑ S
             → T₁ u w → T₂ v w → P u v → ¬ (S u v)
             → ¬ (HasExclusion P S)
no-exclusion P S T₁ T₂ u v w e₁ e₂ m₁ m₂ t₁ t₂ p ns (E , eE , mE , gE) =
  ns (mE u v
       ( joins-through E T₁ T₂ u v w eE (gE T₁ e₁ m₁) (gE T₂ e₂ m₂) t₁ t₂
       , p ))

------------------------------------------------------------------------
-- 4. Theorem 3 — three coordinate terms already destroy the operator
------------------------------------------------------------------------

data Three : Type₀ where
  pa pb pc : Three

isPa : Three → Type₀
isPa pa = Unit
isPa pb = ⊥
isPa pc = ⊥

isPb : Three → Type₀
isPb pa = ⊥
isPb pb = Unit
isPb pc = ⊥

a≢b : ¬ (pa ≡ pb)
a≢b p = subst isPa p tt

a≢c : ¬ (pa ≡ pc)
a≢c p = subst isPa p tt

b≢a : ¬ (pb ≡ pa)
b≢a p = subst isPb p tt

c≢a : ¬ (pc ≡ pa)
c≢a p = a≢c (sym p)

-- Three terms.  `fab` merges a with b; `fac` merges a with c; `fbc`
-- merges b with c.  Their kernels are the three atoms of Eq(Three).
fab : Three → Three
fab pa = pa
fab pb = pa
fab pc = pc

fac : Three → Three
fac pa = pa
fac pb = pb
fac pc = pa

fbc : Three → Three
fbc pa = pa
fbc pb = pb
fbc pc = pb

Δ₃ : Rel Three
Δ₃ = ker (λ x → x)

P₃ : Rel Three
P₃ = ker fab

Tac : Rel Three
Tac = ker fac

Tbc : Rel Three
Tbc = ker fbc

-- Both rival exclusions are admissible: each meets P₃ only in equality.
Tac-adm : (Tac ⊓ P₃) ⊑ Δ₃
Tac-adm pa pa h = refl
Tac-adm pa pb h = Empty.rec (a≢b (fst h))
Tac-adm pa pc h = Empty.rec (a≢c (snd h))
Tac-adm pb pa h = Empty.rec (b≢a (fst h))
Tac-adm pb pb h = refl
Tac-adm pb pc h = Empty.rec (b≢a (fst h))
Tac-adm pc pa h = Empty.rec (c≢a (snd h))
Tac-adm pc pb h = Empty.rec (a≢b (fst h))
Tac-adm pc pc h = refl

Tbc-adm : (Tbc ⊓ P₃) ⊑ Δ₃
Tbc-adm pa pa h = refl
Tbc-adm pa pb h = Empty.rec (a≢b (fst h))
Tbc-adm pa pc h = Empty.rec (a≢b (fst h))
Tbc-adm pb pa h = Empty.rec (b≢a (fst h))
Tbc-adm pb pb h = refl
Tbc-adm pb pc h = Empty.rec (a≢c (snd h))
Tbc-adm pc pa h = Empty.rec (b≢a (fst h))
Tbc-adm pc pb h = Empty.rec (c≢a (snd h))
Tbc-adm pc pc h = refl

-- The positive core: anything above both rivals already relates a to b.
three-coordinates-collapse :
    (E : Rel Three) → IsEq E → Tac ⊑ E → Tbc ⊑ E → E pa pb
three-coordinates-collapse E eE h₁ h₂ =
  joins-through E Tac Tbc pa pb pc eE h₁ h₂ refl refl

-- Corollary: the exclusion of P₃ relative to equality does not exist.
three-coordinates : ¬ (HasExclusion P₃ Δ₃)
three-coordinates =
  no-exclusion P₃ Δ₃ Tac Tbc pa pb pc
    (ker-IsEq fac) (ker-IsEq fbc) Tac-adm Tbc-adm refl refl refl a≢b

------------------------------------------------------------------------
-- 5. Theorem 4 — exclusion IS definable, relative to a declared
--    vocabulary, and does not survive leaving it
------------------------------------------------------------------------

isTrue : Bool → Type₀
isTrue false = ⊥
isTrue true = Unit

f≢t : ¬ (false ≡ true)
f≢t p = subst isTrue (sym p) tt

t≢f : ¬ (true ≡ false)
t≢f p = f≢t (sym p)

Pt : Type₀
Pt = Bool × Bool

Δ₄ : Rel Pt
Δ₄ = ker (λ p → p)

kfst : Rel Pt
kfst = ker fst

ksnd : Rel Pt
ksnd = ker snd

top₄ : Rel Pt
top₄ _ _ = Unit

top₄-IsEq : IsEq top₄
top₄-IsEq = iseq (λ _ → tt) (λ _ → tt) (λ _ _ → tt)

-- The two declared coordinates jointly separate: this is the whole
-- content of "the vocabulary is a coordinate system".
ksnd-adm : (ksnd ⊓ kfst) ⊑ Δ₄
ksnd-adm x y h = ΣPathP (snd h , fst h)

Δ₄-adm : (Δ₄ ⊓ kfst) ⊑ Δ₄
Δ₄-adm x y h = fst h

-- ksnd is above every admissible member of the declared vocabulary …
Δ₄⊑ksnd : Δ₄ ⊑ ksnd
Δ₄⊑ksnd x y h = cong snd h

ksnd⊑ksnd : ksnd ⊑ ksnd
ksnd⊑ksnd x y h = h

-- … and the other two members of the vocabulary are NOT admissible.
u₀ v₀ w₀ : Pt
u₀ = (false , false)
v₀ = (false , true)
w₀ = (true , false)

u₀≢v₀ : ¬ (Δ₄ u₀ v₀)
u₀≢v₀ p = f≢t (cong snd p)

kfst-inadm : ¬ ((kfst ⊓ kfst) ⊑ Δ₄)
kfst-inadm h = u₀≢v₀ (h u₀ v₀ (refl , refl))

top₄-inadm : ¬ ((top₄ ⊓ kfst) ⊑ Δ₄)
top₄-inadm h = u₀≢v₀ (h u₀ v₀ (tt , refl))

-- THEOREM 4a.  Relative to the declared vocabulary {Δ₄, kfst, ksnd,
-- top₄}, the exclusion of kfst relative to Δ₄ exists and is ksnd: the
-- admissible members are exactly Δ₄ and ksnd, and ksnd dominates both.
-- On the index side this is the set difference {1,2} ∖ {1} = {2}.
declared-vocabulary :
    ((Δ₄ ⊓ kfst) ⊑ Δ₄)
  × ((ksnd ⊓ kfst) ⊑ Δ₄)
  × (¬ ((kfst ⊓ kfst) ⊑ Δ₄))
  × (¬ ((top₄ ⊓ kfst) ⊑ Δ₄))
  × (Δ₄ ⊑ ksnd)
  × (ksnd ⊑ ksnd)
declared-vocabulary =
  Δ₄-adm , ksnd-adm , kfst-inadm , top₄-inadm , Δ₄⊑ksnd , ksnd⊑ksnd

-- One relation the vocabulary did not list: parity of the two
-- coordinates.  It is a kernel, hence an equivalence, for free.
par : Bool × Bool → Bool
par (false , false) = false
par (false , true)  = true
par (true  , false) = true
par (true  , true)  = false

kpar : Rel Pt
kpar = ker par

par-inj-snd : (x y w : Bool) → par (x , y) ≡ par (x , w) → y ≡ w
par-inj-snd false false false _ = refl
par-inj-snd false false true  h = Empty.rec (f≢t h)
par-inj-snd false true  false h = Empty.rec (t≢f h)
par-inj-snd false true  true  _ = refl
par-inj-snd true  false false _ = refl
par-inj-snd true  false true  h = Empty.rec (t≢f h)
par-inj-snd true  true  false h = Empty.rec (f≢t h)
par-inj-snd true  true  true  _ = refl

-- Parity is admissible too: it meets kfst only in equality.
kpar-adm : (kpar ⊓ kfst) ⊑ Δ₄
kpar-adm x y h =
  ΣPathP ( snd h
         , par-inj-snd (fst x) (snd x) (snd y)
             (fst h ∙ cong (λ t → par (t , snd y)) (sym (snd h))) )

-- THEOREM 4b.  Admitting parity destroys the operator: `ksnd` and
-- `kpar` are both admissible and reach the common third point w₀, so
-- nothing above both is admissible.  The exclusion of kfst relative to
-- Δ₄ does not exist in Eq(Bool × Bool).
no-vocabulary-extension : ¬ (HasExclusion kfst Δ₄)
no-vocabulary-extension =
  no-exclusion kfst Δ₄ ksnd kpar u₀ v₀ w₀
    (ker-IsEq snd) (ker-IsEq par) ksnd-adm kpar-adm refl refl refl u₀≢v₀

------------------------------------------------------------------------
-- 6. What the two theorems jointly say
--
-- `declared-vocabulary` and `no-vocabulary-extension` are about the
-- SAME pair (kfst , Δ₄).  The exclusion exists relative to the declared
-- list and fails absolutely.  So "the other" is not a function of the
-- term; it is a function of the term AND the declared scope, and the
-- absolute scope has no answer at all.  That is the exact sense in
-- which the operator reading of `anypoha` fails here, and it is not
-- the sense the Boolean gloss anticipates: `Imp-is-exclusion`-style
-- pointwise negation is available on Rel X (Theorem 1) and simply is
-- not an equivalence relation, hence not a meaning-carrier for this
-- repository's channels.
------------------------------------------------------------------------

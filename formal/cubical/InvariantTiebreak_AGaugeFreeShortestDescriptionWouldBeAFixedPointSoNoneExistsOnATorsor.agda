{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- InvariantTiebreak_AGaugeFreeShortestDescriptionWouldBeAFixedPoint
--                   SoNoneExistsOnATorsor
--
-- ON THE NAME.  The mathematics here is group actions, torsors, and
-- invariant orders — Galois/Jordan/Baer/Grothendieck-era European
-- algebra.  There is no Indian source term for this object and none is
-- invented, per CLAUDE.md (absent from this repository)'s file-naming note 2.  The interpretive frame
-- that prompted it is Latin scholastic (Burley, *De obligationibus*,
-- c. 1302; Ockham, *Summa Logicae* I.63–77, c. 1323) and that frame
-- yielded a NAMING and not a theorem.
-- Nothing below depends on it.
--
-- ────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED, AND WHAT IS ALREADY IN THE TREE
--
-- ALREADY IN THE TREE, NOT RE-LANDED.
-- `NaturalMachine.StabilizerTorsor`
-- proves, for the transporter `T x y = Σ[ g ] (g ▸ x ≡ y)`:
-- `invariantPoint→contrStab`, `uniqueCertificate→contrStab`,
-- `contrStab→uniqueCertificate`.  That is the whole TORSOR case: a
-- stabilizer-invariant certificate exists iff the stabilizer is trivial.
-- §2 below restates one direction of it for a BARE action, because the
-- bare form is what §4 needs.
--
-- NEW HERE.
--
--  §3  `leastIsFixed`.  Let a group act on C and let `_≼_` be ANY
--      relation on C that is (i) antisymmetric, (ii) has a least
--      element `m`, and (iii) is preserved by the action.  Then `m` is
--      a FIXED POINT of the action.
--
--      No transitivity of `_≼_`, no totality, no finiteness, no
--      decidability is used.  The proof is four lines: `m ≼ (g⁻¹ ▸ m)`
--      by leastness, push it forward by `g` to get `(g ▸ m) ≼ m`, meet
--      it with `m ≼ (g ▸ m)`, apply antisymmetry.
--
--      Contrapositive (`noFixed→noInvariantTiebreak`): on an action
--      WITHOUT a fixed point there is NO action-invariant antisymmetric
--      relation with a least element.
--
--      WHY THIS IS THE POINT.  "Take the shortest description" does not
--      name a point until ties are broken, and a tiebreak is exactly an
--      antisymmetric relation with a least element.  So on a
--      fixed-point-free action the tiebreak cannot be invariant: the
--      enumeration of programs IS the gauge, in the sense of
--      `smith_certificate_canonicality_correction.md` (absent from this repository) §3 ("a
--      deterministic chosen section is not forbidden … canonical only
--      relative to that extra structure").  This turns that sentence
--      from a caveat into a theorem.
--
--  §5  Two pairs of actions, each pair sharing the SAME group and the
--      SAME carrier type, with OPPOSITE canonicality verdicts:
--
--        (Bool, Bool)  `xorAct`  transitive, no fixed point
--                      `trivAct` not transitive, every point fixed
--        (Bool, Four)  `allAct`  faithful, no fixed point
--                      `oneAct`  faithful, `c` and `d` fixed
--
--      Because each pair shares its carrier TYPE, every invariant that
--      is a function of the group and the carrier alone takes the same
--      value on both members — no cardinality argument is needed and
--      none is made.  In particular the uniform measure on the carrier
--      is literally the same measure, so every Rényi entropy H_α,
--      α ∈ [0,∞], agrees across the pair while the verdicts differ.
--
--      The size of a certificate ensemble does not decide whether a
--      symmetry-natural point exists: it does so on a torsor
--      (§2 + StabilizerTorsor) and only
--      there.  `oneAct` is the counterexample: faithful, four-element
--      carrier, and two fixed points.
--
--  §6  `hasPoint`.  A point exists in all four actions.  So the
--      predicate "a shortest description exists" is inhabited in all
--      four while "a symmetry-natural point exists" is inhabited in
--      exactly two: the description-length functional separates
--      nothing here.
------------------------------------------------------------------------

module InvariantTiebreak_AGaugeFreeShortestDescriptionWouldBeAFixedPointSoNoneExistsOnATorsor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; injSuc ; znots ; snotz)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ ℓ' ℓ'' : Level

------------------------------------------------------------------------
-- 1.  A minimal action structure
--
-- cubical v0.5 ships no group-action record and
-- `NaturalMachine.StabilizerTorsor` defines its own over the library's
-- `Group`.  Only two consequences of the group laws are used below, so
-- only those are fields; `fromGroupLaws` derives the second one from
-- the ordinary laws, so nothing stronger than "an action of a group"
-- is being assumed.
------------------------------------------------------------------------

record Act (G : Type ℓ) (C : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    e     : G
    inv   : G → G
    _▸_   : G → C → C
    ▸-e   : (c : C) → e ▸ c ≡ c
    ▸-inv : (g : G) (c : C) → g ▸ (inv g ▸ c) ≡ c

  infixl 20 _▸_

-- `▸-inv` is not an extra assumption: it is `▸-·` + right inverses.

fromGroupLaws :
  {G : Type ℓ} {C : Type ℓ'}
  (e : G) (_·_ : G → G → G) (inv : G → G) (_▸_ : G → C → C)
  (▸-e : (c : C) → e ▸ c ≡ c)
  (▸-· : (g h : G) (c : C) → (g · h) ▸ c ≡ g ▸ (h ▸ c))
  (invʳ : (g : G) → (g · inv g) ≡ e)
  → Act G C
fromGroupLaws e _·_ inv _▸_ ▸-e ▸-· invʳ = record
  { e = e ; inv = inv ; _▸_ = _▸_ ; ▸-e = ▸-e
  ; ▸-inv = λ g c → sym (▸-· g (inv g) c) ∙ cong (_▸ c) (invʳ g) ∙ ▸-e c
  }

-- A point moved by nothing: the symmetry-natural point.

Fixed : {G : Type ℓ} {C : Type ℓ'} (A : Act G C) → C → Type (ℓ-max ℓ ℓ')
Fixed {G = G} A c = (g : G) → Act._▸_ A g c ≡ c

Canonical : {G : Type ℓ} {C : Type ℓ'} (A : Act G C) → Type (ℓ-max ℓ ℓ')
Canonical {C = C} A = Σ[ c ∈ C ] Fixed A c

Transitive : {G : Type ℓ} {C : Type ℓ'} (A : Act G C) → Type (ℓ-max ℓ ℓ')
Transitive {G = G} {C = C} A = (x y : C) → Σ[ g ∈ G ] (Act._▸_ A g x ≡ y)

------------------------------------------------------------------------
-- 2.  The torsor case, credited
--
-- `NaturalMachine.StabilizerTorsor.Torsor.invariantPoint→contrStab`
-- already has this for transporters.  The bare-action form is here only
-- because §5 needs something to be the restriction that survives.
------------------------------------------------------------------------

transitiveFixed→allEqual :
  {G : Type ℓ} {C : Type ℓ'} (A : Act G C)
  → Transitive A → (c : C) → Fixed A c → (c' : C) → c' ≡ c
transitiveFixed→allEqual A t c fix c' =
  sym (snd (t c c')) ∙ fix (fst (t c c'))

------------------------------------------------------------------------
-- 3.  THE THEOREM.  An invariant tiebreak is a fixed point.
------------------------------------------------------------------------

record InvariantTiebreak
         {G : Type ℓ} {C : Type ℓ'} (A : Act G C) (ℓ'' : Level)
       : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) where
  open Act A
  field
    _≼_     : C → C → Type ℓ''
    antisym : (x y : C) → x ≼ y → y ≼ x → x ≡ y
    least   : C
    isLeast : (c : C) → least ≼ c
    mono    : (g : G) (x y : C) → x ≼ y → (g ▸ x) ≼ (g ▸ y)

leastIsFixed :
  {G : Type ℓ} {C : Type ℓ'} {A : Act G C}
  (t : InvariantTiebreak A ℓ'') → Fixed A (InvariantTiebreak.least t)
leastIsFixed {A = A} t g =
  antisym (g ▸ m) m
    (subst (λ z → (g ▸ m) ≼ z) (▸-inv g m)
           (mono g m (inv g ▸ m) (isLeast (inv g ▸ m))))
    (isLeast (g ▸ m))
  where
    open Act A
    open InvariantTiebreak t
    m : _
    m = least

tiebreak→canonical :
  {G : Type ℓ} {C : Type ℓ'} {A : Act G C}
  → InvariantTiebreak A ℓ'' → Canonical A
tiebreak→canonical t = InvariantTiebreak.least t , leastIsFixed t

-- The contrapositive is the statement about description length: with no
-- symmetry-natural point there is no action-invariant way to say which
-- description is shortest.

noFixed→noInvariantTiebreak :
  {G : Type ℓ} {C : Type ℓ'} {A : Act G C}
  → ¬ (Canonical A) → ¬ (InvariantTiebreak A ℓ'')
noFixed→noInvariantTiebreak nc t = nc (tiebreak→canonical t)

------------------------------------------------------------------------
-- 4.  Actions of the two-element group, built from an involution
------------------------------------------------------------------------

xorB : Bool → Bool → Bool
xorB false b = b
xorB true  false = true
xorB true  true  = false

xorB-assoc : (g h b : Bool) → xorB (xorB g h) b ≡ xorB g (xorB h b)
xorB-assoc false h     b     = refl
xorB-assoc true  false b     = refl
xorB-assoc true  true  false = refl
xorB-assoc true  true  true  = refl

xorB-invʳ : (g : Bool) → xorB g g ≡ false
xorB-invʳ false = refl
xorB-invʳ true  = refl

module Invol {ℓx : Level} (X : Type ℓx) (f : X → X)
             (finv : (x : X) → f (f x) ≡ x) where

  ap : Bool → X → X
  ap false x = x
  ap true  x = f x

  ap-e : (x : X) → ap false x ≡ x
  ap-e x = refl

  ap-· : (g h : Bool) (x : X) → ap (xorB g h) x ≡ ap g (ap h x)
  ap-· false h     x = refl
  ap-· true  false x = refl
  ap-· true  true  x = sym (finv x)

  A : Act Bool X
  A = fromGroupLaws false xorB (λ g → g) ap ap-e ap-· xorB-invʳ

  -- For a two-element group, being fixed is exactly being fixed by the
  -- generator.  This is the α → −∞ end of the Rényi family made
  -- concrete: the orbit of `x` is a singleton exactly here.

  fixed-from-f : (x : X) → f x ≡ x → Fixed A x
  fixed-from-f x p false = refl
  fixed-from-f x p true  = p

  f-from-fixed : (x : X) → Fixed A x → f x ≡ x
  f-from-fixed x h = h true

------------------------------------------------------------------------
-- 5.  Two pairs, same group and same carrier, opposite verdicts
------------------------------------------------------------------------

-- 5a.  Carrier `Bool`.

notB : Bool → Bool
notB false = true
notB true  = false

notB-invol : (b : Bool) → notB (notB b) ≡ b
notB-invol false = refl
notB-invol true  = refl

bcode : Bool → ℕ
bcode false = 0
bcode true  = 1

f≢t : ¬ (false ≡ true)
f≢t p = znots (cong bcode p)

module Xor  = Invol Bool notB notB-invol
module Triv = Invol Bool (λ b → b) (λ b → refl)

xorAct : Act Bool Bool
xorAct = Xor.A

trivAct : Act Bool Bool
trivAct = Triv.A

-- xorAct is transitive and has no fixed point: a torsor.

xorTransitive : Transitive xorAct
xorTransitive false false = false , refl
xorTransitive false true  = true  , refl
xorTransitive true  false = true  , refl
xorTransitive true  true  = false , refl

xorNoFixed : ¬ (Canonical xorAct)
xorNoFixed (false , h) = f≢t (sym (Xor.f-from-fixed false h))
xorNoFixed (true  , h) = f≢t (Xor.f-from-fixed true h)

-- trivAct is not transitive and every point is fixed.

trivNotTransitive : ¬ (Transitive trivAct)
trivNotTransitive t = f≢t (help (t false true))
  where
    help : Σ[ g ∈ Bool ] (Act._▸_ trivAct g false ≡ true) → false ≡ true
    help (false , p) = p
    help (true  , p) = p

trivCanonical : Canonical trivAct
trivCanonical = false , Triv.fixed-from-f false refl

-- 5b.  Carrier `Four`, and BOTH actions faithful, so nobody can say the
--      pair works only because one action is trivial.

data Four : Type where
  a b c d : Four

code : Four → ℕ
code a = 0
code b = 1
code c = 2
code d = 3

swapAll : Four → Four
swapAll a = b
swapAll b = a
swapAll c = d
swapAll d = c

swapAll-invol : (x : Four) → swapAll (swapAll x) ≡ x
swapAll-invol a = refl
swapAll-invol b = refl
swapAll-invol c = refl
swapAll-invol d = refl

swapOne : Four → Four
swapOne a = b
swapOne b = a
swapOne c = c
swapOne d = d

swapOne-invol : (x : Four) → swapOne (swapOne x) ≡ x
swapOne-invol a = refl
swapOne-invol b = refl
swapOne-invol c = refl
swapOne-invol d = refl

module All = Invol Four swapAll swapAll-invol
module One = Invol Four swapOne swapOne-invol

allAct : Act Bool Four
allAct = All.A

oneAct : Act Bool Four
oneAct = One.A

b≢a : ¬ (b ≡ a)
b≢a p = snotz (cong code p)

a≢b : ¬ (a ≡ b)
a≢b p = znots (cong code p)

d≢c : ¬ (d ≡ c)
d≢c p = snotz (injSuc (injSuc (cong code p)))

c≢d : ¬ (c ≡ d)
c≢d p = znots (injSuc (injSuc (cong code p)))

a≢c : ¬ (a ≡ c)
a≢c p = znots (cong code p)

b≢c : ¬ (b ≡ c)
b≢c p = znots (injSuc (cong code p))

-- allAct: no fixed point.

allNoFixed : ¬ (Canonical allAct)
allNoFixed (a , h) = b≢a (All.f-from-fixed a h)
allNoFixed (b , h) = a≢b (All.f-from-fixed b h)
allNoFixed (c , h) = d≢c (All.f-from-fixed c h)
allNoFixed (d , h) = c≢d (All.f-from-fixed d h)

-- oneAct: two fixed points, on the SAME carrier, under the SAME group.

oneCanonicalC : Fixed oneAct c
oneCanonicalC = One.fixed-from-f c refl

oneCanonicalD : Fixed oneAct d
oneCanonicalD = One.fixed-from-f d refl

oneCanonical : Canonical oneAct
oneCanonical = c , oneCanonicalC

-- Both are faithful — the generator moves a point in each.

allFaithful : ¬ (swapAll a ≡ a)
allFaithful = b≢a

oneFaithful : ¬ (swapOne a ≡ a)
oneFaithful = b≢a

-- Neither is transitive, so the surviving restriction in §2 excludes
-- both.

allNotTransitive : ¬ (Transitive allAct)
allNotTransitive t = help (t a c)
  where
    help : Σ[ g ∈ Bool ] (Act._▸_ allAct g a ≡ c) → ⊥
    help (false , p) = a≢c p
    help (true  , p) = b≢c p

oneNotTransitive : ¬ (Transitive oneAct)
oneNotTransitive t = help (t a c)
  where
    help : Σ[ g ∈ Bool ] (Act._▸_ oneAct g a ≡ c) → ⊥
    help (false , p) = a≢c p
    help (true  , p) = b≢c p

------------------------------------------------------------------------
-- 6.  The description-length functional separates nothing
--
-- A section of a one-object indexing is just a point of the carrier.
-- All four actions have one; exactly two have a symmetry-natural one.
------------------------------------------------------------------------

pointXor : Bool
pointXor = false

pointTriv : Bool
pointTriv = false

pointAll : Four
pointAll = a

pointOne : Four
pointOne = a

-- and by §3 no invariant tiebreak can produce `pointXor` or `pointAll`:

xorNoInvariantTiebreak : ¬ (InvariantTiebreak xorAct ℓ-zero)
xorNoInvariantTiebreak = noFixed→noInvariantTiebreak xorNoFixed

allNoInvariantTiebreak : ¬ (InvariantTiebreak allAct ℓ-zero)
allNoInvariantTiebreak = noFixed→noInvariantTiebreak allNoFixed

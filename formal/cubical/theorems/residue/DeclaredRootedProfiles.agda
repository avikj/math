{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- DeclaredRootedProfiles
--
-- A bounded exact refinement of Delta 25 T25.F
-- (`collab/upstream/raw/D0025-eternal-golden-braid-indras-net.txt` (absent from this repository)).  A rooted
-- profile is a declared
-- family of state observations, with a possibly different observation type
-- at each root.  Local state maps act contravariantly on the whole family.
-- Identity, composition, and higher cells are preserved pointwise.
--
-- A separator is root-indexed.  Equivalence transports it at that same root,
-- and an explicit declared family of separators transports root by root.
-- Nothing promotes one local separator to an arbitrary all-roots fact.  The
-- Bool control at the end makes that boundary executable.
------------------------------------------------------------------------

module DeclaredRootedProfiles where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Data.Bool using (Bool ; false ; true ; false≢true)
open import Cubical.Data.Sigma using (_×_ ; Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓR ℓX ℓO ℓC ℓD : Level

------------------------------------------------------------------------
-- Rooted profiles and functorial reindexing
------------------------------------------------------------------------

RootedProfile : (Root : Type ℓR) (State : Type ℓX)
              → (Root → Type ℓO)
              → Type (ℓ-max ℓR (ℓ-max ℓX ℓO))
RootedProfile Root State Observation =
  (root : Root) → State → Observation root

reindexProfile : {Root : Type ℓR} {X Y : Type ℓX}
               {Observation : Root → Type ℓO}
               → (X → Y)
               → RootedProfile Root Y Observation
               → RootedProfile Root X Observation
reindexProfile f profile root x = profile root (f x)

reindex-id : {Root : Type ℓR} {X : Type ℓX}
           {Observation : Root → Type ℓO}
           → (profile : RootedProfile Root X Observation)
           → reindexProfile (λ x → x) profile ≡ profile
reindex-id profile = refl

reindex-comp : {Root : Type ℓR} {X Y Z : Type ℓX}
             {Observation : Root → Type ℓO}
             → (f : X → Y) (g : Y → Z)
             → (profile : RootedProfile Root Z Observation)
             → reindexProfile f (reindexProfile g profile)
              ≡ reindexProfile (λ x → g (f x)) profile
reindex-comp f g profile = refl

-- A local state equivalence induces an equivalence of the entire dependent
-- rooted-profile type.  Both inverse laws are pointwise triangle laws; no
-- root is enumerated or overwritten.
profileReindexEquiv : {Root : Type ℓR} {X Y : Type ℓX}
                    {Observation : Root → Type ℓO}
                    → (e : X ≃ Y)
                    → RootedProfile Root Y Observation
                     ≃ RootedProfile Root X Observation
profileReindexEquiv e = isoToEquiv (iso
  (reindexProfile (equivFun e))
  (reindexProfile (invEq e))
  (λ profile → funExt λ root → funExt λ x →
    cong (profile root) (retEq e x))
  (λ profile → funExt λ root → funExt λ y →
    cong (profile root) (secEq e y)))

-- A higher cell between local maps changes every rooted profile by the
-- induced pointwise path.  The root is quantified, not rewritten.
stateCell→profilePath :
    {Root : Type ℓR} {X Y : Type ℓX}
    {Observation : Root → Type ℓO} {f g : X → Y}
  → ((x : X) → f x ≡ g x)
  → (profile : RootedProfile Root Y Observation)
  → reindexProfile f profile ≡ reindexProfile g profile
stateCell→profilePath cell profile = funExt λ root → funExt λ x →
  cong (profile root) (cell x)

------------------------------------------------------------------------
-- Adjoining a new root-dependent coordinate
------------------------------------------------------------------------

adjoinProfile : {Root : Type ℓR} {X : Type ℓX}
               {Observation : Root → Type ℓO}
               {Added : Root → Type ℓC}
               → RootedProfile Root X Observation
               → RootedProfile Root X Added
               → RootedProfile Root X (λ root → Observation root × Added root)
adjoinProfile profile added root x = profile root x , added root x

-- Propagation conserves the old root-specific coordinate exactly.  Only the
-- warranted added coordinate is new.
adjoin-retains-profile :
    {Root : Type ℓR} {X : Type ℓX}
    {Observation : Root → Type ℓO} {Added : Root → Type ℓC}
    (profile : RootedProfile Root X Observation)
    (added : RootedProfile Root X Added) (root : Root) (x : X)
  → fst (adjoinProfile profile added root x) ≡ profile root x
adjoin-retains-profile profile added root x = refl

adjoin-reindex : {Root : Type ℓR} {X Y : Type ℓX}
                {Observation : Root → Type ℓO}
                {Added : Root → Type ℓC}
                → (f : X → Y)
                → (profile : RootedProfile Root Y Observation)
                → (added : RootedProfile Root Y Added)
                → reindexProfile f (adjoinProfile profile added)
                 ≡ adjoinProfile (reindexProfile f profile)
                                   (reindexProfile f added)
adjoin-reindex f profile added = refl

ProfileCell : {Root : Type ℓR} {X : Type ℓX}
            {Observation : Root → Type ℓO}
            → RootedProfile Root X Observation
            → RootedProfile Root X Observation
            → Type (ℓ-max ℓR (ℓ-max ℓX ℓO))
ProfileCell left right =
  (root : _) → (x : _) → left root x ≡ right root x

-- Adjoining a higher cell changes only the adjoined coordinate and retains
-- each root's old reading.  This is pointwise naturality, not state copying.
adjoinProfileCell :
    {Root : Type ℓR} {X : Type ℓX}
    {Observation : Root → Type ℓO} {Added : Root → Type ℓC}
    (profile : RootedProfile Root X Observation)
    {left right : RootedProfile Root X Added}
  → ProfileCell left right
  → ProfileCell (adjoinProfile profile left) (adjoinProfile profile right)
adjoinProfileCell profile cell root x i = profile root x , cell root x i

profileCell→path :
    {Root : Type ℓR} {X : Type ℓX}
    {Observation : Root → Type ℓO}
    {left right : RootedProfile Root X Observation}
  → ProfileCell left right → left ≡ right
profileCell→path cell = funExt λ root → funExt λ x → cell root x

------------------------------------------------------------------------
-- Root-indexed separators and declared propagation
------------------------------------------------------------------------

SeparatorAt : {Root : Type ℓR} {X : Type ℓX}
            {Observation : Root → Type ℓO}
            → RootedProfile Root X Observation → Root
            → Type (ℓ-max ℓX ℓO)
SeparatorAt {X = X} profile root =
  Σ[ x ∈ X ] Σ[ y ∈ X ] ¬ (profile root x ≡ profile root y)

-- A separator carried by the adjoined coordinate invalidates the proposed
-- identification in the joint rooted view.
addedSeparator→jointSeparator :
    {Root : Type ℓR} {X : Type ℓX}
    {Observation : Root → Type ℓO} {Added : Root → Type ℓC}
    (profile : RootedProfile Root X Observation)
    (added : RootedProfile Root X Added) (root : Root)
  → SeparatorAt added root
  → SeparatorAt (adjoinProfile profile added) root
addedSeparator→jointSeparator profile added root (x , y , separated) =
  x , y , λ jointPath → separated (cong snd jointPath)

-- Pull a separator through an equivalence.  The selected root is retained.
pullSeparator :
    {Root : Type ℓR} {X Y : Type ℓX}
    {Observation : Root → Type ℓO}
    → (e : X ≃ Y) (profile : RootedProfile Root Y Observation) (root : Root)
    → SeparatorAt profile root
    → SeparatorAt (reindexProfile (equivFun e) profile) root
pullSeparator e profile root (x , y , separated) =
  invEq e x , invEq e y , λ pulledPath →
    separated
      (sym (cong (profile root) (secEq e x))
       ∙ pulledPath
       ∙ cong (profile root) (secEq e y))

-- Push a separator back to the original presentation.  Definitional
-- reduction keeps the root and the two transported states visible.
pushSeparator :
    {Root : Type ℓR} {X Y : Type ℓX}
    {Observation : Root → Type ℓO}
    → (e : X ≃ Y) (profile : RootedProfile Root Y Observation) (root : Root)
    → SeparatorAt (reindexProfile (equivFun e) profile) root
    → SeparatorAt profile root
pushSeparator e profile root (x , y , separated) =
  equivFun e x , equivFun e y , separated

SeparatorFamily : {Root : Type ℓR} {X : Type ℓX}
                {Observation : Root → Type ℓO}
                → (Declared : Root → Type ℓD)
                → RootedProfile Root X Observation
                → Type (ℓ-max ℓR (ℓ-max ℓD (ℓ-max ℓX ℓO)))
SeparatorFamily Declared profile =
  (root : _) → Declared root → SeparatorAt profile root

-- Propagation across the whole declared family is pointwise transport of the
-- same law.  It requires a separator at each declared root as input.
pullSeparatorFamily :
    {Root : Type ℓR} {X Y : Type ℓX}
    {Observation : Root → Type ℓO} {Declared : Root → Type ℓD}
    → (e : X ≃ Y) (profile : RootedProfile Root Y Observation)
    → SeparatorFamily Declared profile
    → SeparatorFamily Declared (reindexProfile (equivFun e) profile)
pullSeparatorFamily e profile family root declared =
  pullSeparator e profile root (family root declared)

pushSeparatorFamily :
    {Root : Type ℓR} {X Y : Type ℓX}
    {Observation : Root → Type ℓO} {Declared : Root → Type ℓD}
    → (e : X ≃ Y) (profile : RootedProfile Root Y Observation)
    → SeparatorFamily Declared (reindexProfile (equivFun e) profile)
    → SeparatorFamily Declared profile
pushSeparatorFamily e profile family root declared =
  pushSeparator e profile root (family root declared)

------------------------------------------------------------------------
-- Killer: local change does not manufacture arbitrary global state
------------------------------------------------------------------------

BoolObservation : Bool → Type₀
BoolObservation root = Bool

baseProfile : RootedProfile Bool Bool BoolObservation
baseProfile root x = false

-- The added coordinate distinguishes the two states only at the north root
-- `false`; at the south root `true` it remains constant.
localAdded : RootedProfile Bool Bool BoolObservation
localAdded false x = x
localAdded true  x = false

jointProfile : RootedProfile Bool Bool
  (λ root → BoolObservation root × BoolObservation root)
jointProfile = adjoinProfile baseProfile localAdded

north-added-separator : SeparatorAt localAdded false
north-added-separator = false , true , false≢true

north-joint-separator : SeparatorAt jointProfile false
north-joint-separator =
  addedSeparator→jointSeparator baseProfile localAdded false
    north-added-separator

-- The positive declared family contains precisely roots identified with
-- north.  Its witness is transported along that declaration path; nothing is
-- required or inferred at an unrelated root.
northDeclared : Bool → Type₀
northDeclared root = root ≡ false

northDeclaredSeparators : SeparatorFamily northDeclared jointProfile
northDeclaredSeparators root declared =
  subst (SeparatorAt jointProfile) (sym declared) north-joint-separator

south-joint-equal : (x y : Bool) → jointProfile true x ≡ jointProfile true y
south-joint-equal x y = refl

-- A separator at one root is not an all-roots separator family.  The south
-- component would contradict its definitional constancy.
local-separator-not-global :
  ¬ ((root : Bool) → SeparatorAt jointProfile root)
local-separator-not-global everyRoot with everyRoot true
... | x , y , separated = separated (south-joint-equal x y)

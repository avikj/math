{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

-- StabilizerTorsor: the checked core of R0027
-- (collab/discovery/claims/R0027-invariant-schema-envelope.md (absent from this repository), eq (3) of
-- thread in collab/messages/0342 and corrected in
-- collab/messages/shilpin/smith_certificate_canonicality_correction.md (absent from this repository)).
--
-- For a group G acting on a set X and points x y : X, the transporter
--
--     T x y = Σ[ g ∈ G ] (g ▸ x ≡ y)
--
-- carries a free and transitive action of Stab x (by precomposition) and,
-- equivalently, of Stab y (by postcomposition): any two transporters
-- differ by a unique stabilizer element (`isTorsorT`, `isTorsorTL`).
-- Consequently a transporter fixed by every stabilizer element forces the
-- stabilizer to be trivial (`invariantPoint→contrStab`) — R0027's no-go:
-- endpoint-invariant data cannot select a certificate equivariantly unless
-- the stabilizer is already trivial.  Shilpin's sharp statement 1 is the
-- bridge `uniqueCertificate→contrStab` / `contrStab→uniqueCertificate`.
--
-- cubical v0.5 has no group-action record, so a minimal one is defined
-- here (`Action`).  The stabilizer is packaged both as a Group in its own
-- right (`StabGroup`, any universe levels) and, at matching levels, as a
-- library `Subgroup` (`StabIsSubgroup.StabSubgroup`) whose underlying
-- carrier agrees definitionally with the torsor-side stabilizer.
-- The Smith-thread shape — two commuting one-sided actions (L , R) on a
-- set of matrices, certificates as transporters to a normal form D, and
-- the two-sided target stabilizer Γ_D — is the instance `TwoSided`.

module StabilizerTorsor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Powerset using (ℙ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.DirProd

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ---------------------------------------------------------------------
-- A minimal group-action record (cubical v0.5 ships no GroupAction).
-- Composition convention: (g · h) ▸ x ≡ g ▸ (h ▸ x).
-- ---------------------------------------------------------------------

record Action (G : Group ℓ) (X : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isSetX : isSet X
    _▸_    : ⟨ G ⟩ → X → X
    ▸-1g   : (x : X) → (GroupStr.1g (snd G)) ▸ x ≡ x
    ▸-·    : (g h : ⟨ G ⟩) (x : X)
           → (GroupStr._·_ (snd G) g h) ▸ x ≡ g ▸ (h ▸ x)

-- ---------------------------------------------------------------------
-- The transporter groupoid of an action, its stabilizer groups, and the
-- torsor theorem.
-- ---------------------------------------------------------------------

module Torsor (G : Group ℓ) {X : Type ℓ'} (A : Action G X) where

  open GroupStr (snd G)
  open Action A

  -- The transporter from x to y: a group element together with a checked
  -- carry certificate.  Stab x = T x x is the stabilizer.
  T : X → X → Type (ℓ-max ℓ ℓ')
  T x y = Σ[ g ∈ ⟨ G ⟩ ] ((g ▸ x) ≡ y)

  Stab : X → Type (ℓ-max ℓ ℓ')
  Stab x = T x x

  isSetT : (x y : X) → isSet (T x y)
  isSetT x y = isSetΣ is-set (λ g → isProp→isSet (isSetX (g ▸ x) y))

  -- Carry certificates are paths in a set, hence proofs are irrelevant:
  -- transporters are compared on their group component alone.
  transporterPath : {x y : X} {t₁ t₂ : T x y} → fst t₁ ≡ fst t₂ → t₁ ≡ t₂
  transporterPath {x} {y} = Σ≡Prop (λ g → isSetX (g ▸ x) y)

  -- Groupoid structure on transporters.
  idT : (x : X) → T x x
  idT x = 1g , ▸-1g x

  _∙T_ : {x y z : X} → T y z → T x y → T x z
  _∙T_ {x} (g , p) (h , q) = (g · h) , (▸-· g h x ∙ cong (g ▸_) q ∙ p)

  invT : {x y : X} → T x y → T y x
  invT {x} {y} (g , p) = inv g ,
    ( cong (inv g ▸_) (sym p)
    ∙ sym (▸-· (inv g) g x)
    ∙ cong (_▸ x) (·InvL g)
    ∙ ▸-1g x )

  ∙T-IdR : {x y : X} (t : T x y) → (t ∙T idT x) ≡ t
  ∙T-IdR (g , _) = transporterPath (·IdR g)

  ∙T-IdL : {x y : X} (t : T x y) → (idT y ∙T t) ≡ t
  ∙T-IdL (g , _) = transporterPath (·IdL g)

  ∙T-Assoc : {w x y z : X} (u : T y z) (v : T x y) (t : T w x)
           → (u ∙T (v ∙T t)) ≡ ((u ∙T v) ∙T t)
  ∙T-Assoc (g , _) (h , _) (k , _) = transporterPath (·Assoc g h k)

  ∙T-InvR : {x y : X} (t : T x y) → (t ∙T invT t) ≡ idT y
  ∙T-InvR (g , _) = transporterPath (·InvR g)

  ∙T-InvL : {x y : X} (t : T x y) → (invT t ∙T t) ≡ idT x
  ∙T-InvL (g , _) = transporterPath (·InvL g)

  -- (1) The stabilizer is a group under transporter composition.  (Its
  -- presentation as a subgroup of G via the library record is
  -- `StabIsSubgroup` below; here no level restriction is needed.)
  StabGroup : X → Group (ℓ-max ℓ ℓ')
  StabGroup x = makeGroup (idT x) _∙T_ invT (isSetT x x)
                          ∙T-Assoc ∙T-IdR ∙T-IdL ∙T-InvR ∙T-InvL

  -- Stab x acts on T x y on the right by precomposition (t , s) ↦ t ∙T s;
  -- the action laws are the instances ∙T-IdR and ∙T-Assoc.  Stab y acts
  -- on the left by postcomposition (s , t) ↦ s ∙T t, with laws ∙T-IdL and
  -- ∙T-Assoc.  Both actions are free and transitive:

  -- The difference of two transporters, as a source-stabilizer element...
  diff : {x y : X} (t₁ t₂ : T x y) → Stab x
  diff t₁ t₂ = invT t₁ ∙T t₂

  -- ...which carries t₁ to t₂ (transitivity of the right action)...
  diff-carries : {x y : X} (t₁ t₂ : T x y) → (t₁ ∙T diff t₁ t₂) ≡ t₂
  diff-carries (g₁ , _) (g₂ , _) = transporterPath
    (·Assoc g₁ (inv g₁) g₂ ∙ cong (_· g₂) (·InvR g₁) ∙ ·IdL g₂)

  -- ...and is the only stabilizer element that does (freeness).
  diff-unique : {x y : X} (t₁ t₂ : T x y) (s : Stab x)
              → (t₁ ∙T s) ≡ t₂ → diff t₁ t₂ ≡ s
  diff-unique (g₁ , _) (g₂ , _) (h , _) e = transporterPath
    ( cong (inv g₁ ·_) (sym (cong fst e))
    ∙ ·Assoc (inv g₁) g₁ h
    ∙ cong (_· h) (·InvL g₁)
    ∙ ·IdL h )

  -- (2)+(3)+(4) packaged: any two transporters differ by a UNIQUE
  -- source-stabilizer element.  This is the torsor theorem for the right
  -- Stab x action; freeness and transitivity below are its corollaries.
  isTorsorT : {x y : X} (t₁ t₂ : T x y)
            → isContr (Σ[ s ∈ Stab x ] ((t₁ ∙T s) ≡ t₂))
  isTorsorT {x} {y} t₁ t₂ =
    (diff t₁ t₂ , diff-carries t₁ t₂) ,
    λ se → Σ≡Prop (λ s → isSetT x y (t₁ ∙T s) t₂)
                  (diff-unique t₁ t₂ (fst se) (snd se))

  -- (3) transitivity, separately named.
  transitive : {x y : X} (t₁ t₂ : T x y) → Σ[ s ∈ Stab x ] ((t₁ ∙T s) ≡ t₂)
  transitive t₁ t₂ = diff t₁ t₂ , diff-carries t₁ t₂

  -- (2) freeness, separately named: only the identity fixes a transporter.
  free : {x y : X} (t : T x y) (s : Stab x) → (t ∙T s) ≡ t → s ≡ idT x
  free {x} t s e = sym (diff-unique t t s e) ∙ diff-unique t t (idT x) (∙T-IdR t)

  -- The same three statements for the target stabilizer Stab y acting on
  -- the left ("equivalently Stab(y)"; this is R0027's `Stab(target)` and
  -- shilpin's Γ_D).
  diffL : {x y : X} (t₁ t₂ : T x y) → Stab y
  diffL t₁ t₂ = t₂ ∙T invT t₁

  diffL-carries : {x y : X} (t₁ t₂ : T x y) → (diffL t₁ t₂ ∙T t₁) ≡ t₂
  diffL-carries (g₁ , _) (g₂ , _) = transporterPath
    (sym (·Assoc g₂ (inv g₁) g₁) ∙ cong (g₂ ·_) (·InvL g₁) ∙ ·IdR g₂)

  diffL-unique : {x y : X} (t₁ t₂ : T x y) (s : Stab y)
               → (s ∙T t₁) ≡ t₂ → diffL t₁ t₂ ≡ s
  diffL-unique (g₁ , _) (g₂ , _) (h , _) e = transporterPath
    ( cong (_· inv g₁) (sym (cong fst e))
    ∙ sym (·Assoc h g₁ (inv g₁))
    ∙ cong (h ·_) (·InvR g₁)
    ∙ ·IdR h )

  isTorsorTL : {x y : X} (t₁ t₂ : T x y)
             → isContr (Σ[ s ∈ Stab y ] ((s ∙T t₁) ≡ t₂))
  isTorsorTL {x} {y} t₁ t₂ =
    (diffL t₁ t₂ , diffL-carries t₁ t₂) ,
    λ se → Σ≡Prop (λ s → isSetT x y (s ∙T t₁) t₂)
                  (diffL-unique t₁ t₂ (fst se) (snd se))

  freeL : {x y : X} (t : T x y) (s : Stab y) → (s ∙T t) ≡ t → s ≡ idT y
  freeL {x} {y} t s e =
    sym (diffL-unique t t s e) ∙ diffL-unique t t (idT y) (∙T-IdL t)

  -- The torsor statement in its inhabitation-guarded form: a merely
  -- inhabited transporter type is a Stab x torsor.
  isTorsor : (x y : X) → Type (ℓ-max ℓ ℓ')
  isTorsor x y =
    ∥ T x y ∥₁
    × ((t₁ t₂ : T x y) → isContr (Σ[ s ∈ Stab x ] ((t₁ ∙T s) ≡ t₂)))

  inhabited→isTorsor : {x y : X} → ∥ T x y ∥₁ → isTorsor x y
  inhabited→isTorsor h = h , isTorsorT

  -- ------------------------------------------------------------------
  -- R0027's no-go, pinned: a transporter invariant under the whole
  -- stabilizer action exists only over a trivial stabilizer.  So no
  -- selector built from endpoint-invariant data (which is exactly the
  -- data fixed by the stabilizer) can pick a transporter equivariantly
  -- unless Stab is trivial.
  -- ------------------------------------------------------------------
  invariantPoint→trivialStab : {x y : X} (t : T x y)
    → ((s : Stab x) → (t ∙T s) ≡ t)
    → (s : Stab x) → s ≡ idT x
  invariantPoint→trivialStab t fix s = free t s (fix s)

  invariantPoint→contrStab : {x y : X} (t : T x y)
    → ((s : Stab x) → (t ∙T s) ≡ t)
    → isContr (Stab x)
  invariantPoint→contrStab {x} t fix =
    idT x , λ s → sym (invariantPoint→trivialStab t fix s)

  -- Target-stabilizer form (the R0027 / Smith-certificate phrasing).
  invariantPointL→trivialStab : {x y : X} (t : T x y)
    → ((s : Stab y) → (s ∙T t) ≡ t)
    → (s : Stab y) → s ≡ idT y
  invariantPointL→trivialStab t fix s = freeL t s (fix s)

  invariantPointL→contrStab : {x y : X} (t : T x y)
    → ((s : Stab y) → (s ∙T t) ≡ t)
    → isContr (Stab y)
  invariantPointL→contrStab {x} {y} t fix =
    idT y , λ s → sym (invariantPointL→trivialStab t fix s)

  -- Shilpin's sharp statement 1 (the "ordinary torsor theorem"): the
  -- transporter/certificate is unique iff the stabilizer is trivial.
  uniqueCertificate→contrStab : {x y : X} (t : T x y)
    → isProp (T x y) → isContr (Stab x)
  uniqueCertificate→contrStab t prop =
    invariantPoint→contrStab t (λ s → prop (t ∙T s) t)

  contrStab→uniqueCertificate : {x y : X} → isContr (Stab x) → isProp (T x y)
  contrStab→uniqueCertificate {x} {y} c t₁ t₂ =
    sym (∙T-IdR t₁)
    ∙ cong (t₁ ∙T_) (isContr→isProp c (idT x) (diff t₁ t₂))
    ∙ diff-carries t₁ t₂

-- ---------------------------------------------------------------------
-- (1) with the library record: at matching universe levels the stabilizer
-- is a Subgroup of G in the sense of Cubical.Algebra.Group.Subgroup, and
-- the group it presents has definitionally the same carrier as Torsor.Stab.
-- ---------------------------------------------------------------------

module StabIsSubgroup (G : Group ℓ) {X : Type ℓ} (A : Action G X) where

  open GroupStr (snd G)
  open Action A
  open isSubgroup

  stabSubset : X → ℙ ⟨ G ⟩
  stabSubset x g = ((g ▸ x) ≡ x) , isSetX (g ▸ x) x

  isSubgroupStab : (x : X) → isSubgroup G (stabSubset x)
  id-closed (isSubgroupStab x) = ▸-1g x
  op-closed (isSubgroupStab x) {g} {h} pg ph =
    ▸-· g h x ∙ cong (g ▸_) ph ∙ pg
  inv-closed (isSubgroupStab x) {g} pg =
      cong (inv g ▸_) (sym pg)
    ∙ sym (▸-· (inv g) g x)
    ∙ cong (_▸ x) (·InvL g)
    ∙ ▸-1g x

  StabSubgroup : X → Subgroup G
  StabSubgroup x = stabSubset x , isSubgroupStab x

  -- The library-side subgroup and the torsor-side stabilizer coincide on
  -- the nose (both are Σ[ g ∈ ⟨ G ⟩ ] ((g ▸ x) ≡ x)).
  stabCarrier≡ : (x : X)
    → ⟨ Subgroup→Group G (StabSubgroup x) ⟩ ≡ Torsor.Stab G A x
  stabCarrier≡ x = refl

-- ---------------------------------------------------------------------
-- The Smith-thread specialization: two commuting one-sided actions
-- (row operations L and column operations R) assemble into an action of
-- the product group, and the general theorem applies verbatim.  For
-- matrices, Cert A D is the set of two-sided certificates carrying A to
-- the normal form D, and Γ D is shilpin's two-sided target stabilizer
-- Γ_D = {(H , K) : H D K ≡ D}; `certificateTorsor` is the statement that
-- the certificate set is a Γ_D-torsor, and `gaugeFreeSelector→trivialΓ`
-- is the no-go that closes msg 0342's producer problem.
-- ---------------------------------------------------------------------

module TwoSided
  (H : Group ℓ) (K : Group ℓ') {M : Type ℓ''}
  (AL : Action H M) (AR : Action K M)
  (comm : (h : ⟨ H ⟩) (k : ⟨ K ⟩) (m : M)
        → Action._▸_ AL h (Action._▸_ AR k m)
        ≡ Action._▸_ AR k (Action._▸_ AL h m))
  where

  private
    module L = Action AL
    module R = Action AR

  pairAction : Action (DirProd H K) M
  Action.isSetX pairAction = L.isSetX
  Action._▸_ pairAction (h , k) m = L._▸_ h (R._▸_ k m)
  Action.▸-1g pairAction m =
    cong (L._▸_ (GroupStr.1g (snd H))) (R.▸-1g m) ∙ L.▸-1g m
  Action.▸-· pairAction (h₁ , k₁) (h₂ , k₂) m =
      cong (L._▸_ (GroupStr._·_ (snd H) h₁ h₂)) (R.▸-· k₁ k₂ m)
    ∙ L.▸-· h₁ h₂ (R._▸_ k₁ (R._▸_ k₂ m))
    ∙ cong (L._▸_ h₁) (comm h₂ k₁ (R._▸_ k₂ m))

  module Certificates = Torsor (DirProd H K) pairAction

  Cert : M → M → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Cert = Certificates.T

  Γ : M → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Γ D = Certificates.Stab D

  -- Any two certificates from A to D differ by a unique element of the
  -- two-sided target stabilizer Γ_D (acting by postcomposition).
  certificateTorsor : (A D : M) (c₁ c₂ : Cert A D)
    → isContr (Σ[ γ ∈ Γ D ] (Certificates._∙T_ γ c₁ ≡ c₂))
  certificateTorsor A D = Certificates.isTorsorTL

  -- A certificate fixed by every Γ_D symmetry — i.e. selected by
  -- endpoint-invariant data alone, with no gauge — forces Γ_D trivial.
  gaugeFreeSelector→trivialΓ : (A D : M) (c : Cert A D)
    → ((γ : Γ D) → Certificates._∙T_ γ c ≡ c)
    → isContr (Γ D)
  gaugeFreeSelector→trivialΓ A D = Certificates.invariantPointL→contrStab

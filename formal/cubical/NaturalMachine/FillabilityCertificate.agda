{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- FillabilityCertificate
--
-- The checkable core of notes/FILLABILITY_AS_SUCCESS.md (absent from this repository) (seed 177):
-- the CERTIFICATE STRUCTURE of the two fillability predicates of that
-- note's Def 2.2.2, formalised as datatypes and decision procedures.
--
-- HEADLINE STATEMENTS (all checked, no postulates, no holes, --safe):
--
--  1. Cert / FillTerm      The finite certificate of the note's
--                          Fill_term (Def 2.2.2, §3.4(i)): an inductive
--                          list of chosen fillers ending in a
--                          distinguished obstruction.  `FillTerm` is
--                          "there exists a certificate".  Being
--                          inductive, it is finite by construction —
--                          this is the honest content of "Σ⁰₁ with a
--                          finite certificate": positive instances are
--                          exhibited and checked, in finite time, by
--                          the kernel.
--
--  2. Branch / FillInf     The note's Fill_∞: a coinductive total
--                          choice function filling every level.
--     cert→branch          Prop 2.2.3 (⇒), which needs — and here
--                          explicitly takes — the hypothesis that a
--                          distinguished obstruction has an identity
--                          filler whose boundary is again distinguished.
--
--  3. A∞ / noCert / branchA∞
--                          Prop 2.2.3 STRICTNESS, as the note's own A_∞
--                          witness: a system in which every level is
--                          filled (a branch exists) and no level is ever
--                          distinguished (no certificate exists).
--                          FillInf ∧ ¬ FillTerm, both proved.
--                          This system is FINITELY (indeed uniquely)
--                          branching, so it is simultaneously the
--                          formal shadow of §4.2's refutation of
--                          nilpotence: the hypothesis that bounds the
--                          BRANCHING does not bound the LENGTH.  See 6.
--
--  4. decBCert             The decision procedure, as a term: for each
--                          fuel k, `Dec` of "there is a certificate of
--                          depth ≤ k".  It takes decidability of the
--                          distinguished-element check and a FINITE
--                          BRANCHING structure (`FinBranch`: a finite
--                          enumeration of the fillers at each node, with
--                          a covering proof) as explicit arguments.
--                          Delete either argument and the term does not
--                          typecheck — the consumption is the point.
--
--  5. truncCert            Theorem 4.1: an N-truncated system (every
--     truncated-FillTerm   obstruction at level ≥ N is distinguished)
--                          admits a certificate of depth ≤ N, hence
--                          Fill_term holds and is DECIDABLE — trivially,
--                          by `yes`.  This is also the note's COST
--                          bound: the tower is bounded exactly by the
--                          truncation of the ambient, and the depth
--                          index of the constructed BCert IS that bound.
--
--  6. infBranch-decides-∃  The asymmetry, in the only form that is a
--                          theorem rather than an observation about
--                          which arguments a term mentions: for a system
--                          with INFINITE branching at level 0, a
--                          decision procedure for `Cert` would decide
--                          `Σ[ k ∈ ℕ ] P k ≡ true` for an arbitrary
--                          P : ℕ → Bool.  So certificate-existence is
--                          not decidable without finite branching, on
--                          pain of deciding an arbitrary unbounded
--                          existential; positive instances stay
--                          exhibitable (`∃→Cert`), negative ones do not.
--                          That is the checkable shadow of §3.4's
--                          "failure cannot be reported".
--
--  * The note's §5 (Theorem 5.3: the dividing line for quantitative
--    defects is ARITY, not an attainable zero) is formalised in
--    `NaturalMachine.ArityOfRepair`, which imports
--    this module's A∞ for the "escapes Theorem A" half.
--  * §4.2's refutation of nilpotence is formalised in its ABSTRACT
--    form (3 above: finite branching does not bound length).
------------------------------------------------------------------------

module NaturalMachine.FillabilityCertificate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc; +-zero)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl)
open import Cubical.Data.Bool using (Bool; true)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §0.  Any, over a finite enumeration.  (Local, to keep the module
--      self-contained; `Any P xs` is the finite disjunction over xs.)
------------------------------------------------------------------------

data Any {A : Type ℓ} (P : A → Type ℓ) : List A → Type ℓ where
  here  : ∀ {x xs} → P x       → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs  → Any P (x ∷ xs)

mapAny : {A : Type ℓ} {P Q : A → Type ℓ} {xs : List A}
       → (∀ x → P x → Q x) → Any P xs → Any Q xs
mapAny f (here p)  = here (f _ p)
mapAny f (there a) = there (mapAny f a)

anyΣ : {A : Type ℓ} {P : A → Type ℓ} {xs : List A} → Any P xs → Σ[ x ∈ A ] P x
anyΣ (here {x = x} p) = x , p
anyΣ (there a)        = anyΣ a

decAny : {A : Type ℓ} {P : A → Type ℓ}
       → (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
decAny d [] = no λ ()
decAny d (x ∷ xs) with d x
... | yes p = yes (here p)
... | no ¬p with decAny d xs
...   | yes a  = yes (there a)
...   | no ¬a  = no λ { (here p) → ¬p p ; (there a) → ¬a a }

------------------------------------------------------------------------
-- §1.  A filling system: the note's §2.2 tower, ℕ-indexed.
--
--      Obs n      : the level-n obstruction set        (δ^(n) lives here)
--      IsZero n d : d is the distinguished element     (reading (R3))
--      Filler n d : the fillers of d                   (χ^(n+1); (R1))
--      ∂ n d χ    : the residual obligation of χ       (δ^(n+1); (R2))
--
--      `∂` is a function of the CHOSEN filler, which is exactly the
--      note's (R2) reading of D0016 §C's equation as a definition of
--      δ^(n+1) rather than a constraint on it (§2.4).
------------------------------------------------------------------------

record FillSys (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Obs    : ℕ → Type ℓ
    IsZero : (n : ℕ) → Obs n → Type ℓ
    Filler : (n : ℕ) → Obs n → Type ℓ
    ∂      : (n : ℕ) (d : Obs n) → Filler n d → Obs (suc n)

open FillSys public

module _ {ℓ} (S : FillSys ℓ) where

  ----------------------------------------------------------------------
  -- §2.  The finite certificate, and Fill_term.
  --
  --      A certificate at (n , d) is a finite filling sequence
  --      χ^(n+1), …, χ^(β) together with the equality δ^(β) = 0.  It is
  --      inductive: every inhabitant is a finite object, checked in
  --      finite time.  That is the note's §3.4(i) "finite certificate"
  --      as a type, and it is the honest Agda content of "Σ⁰₁".
  ----------------------------------------------------------------------

  data Cert : (n : ℕ) → Obs S n → Type ℓ where
    done : ∀ {n d} → IsZero S n d → Cert n d
    step : ∀ {n d} (χ : Filler S n d) → Cert (suc n) (∂ S n d χ) → Cert n d

  FillTerm : (n : ℕ) → Obs S n → Type ℓ
  FillTerm = Cert

  -- Depth-bounded certificates: `BCert k n d` is a certificate using at
  -- most k filling steps.  The fuel is what makes search terminate; the
  -- note's §4.1 supplies the fuel as a theorem (see §6 below).
  data BCert : ℕ → (n : ℕ) → Obs S n → Type ℓ where
    bdone : ∀ {k n d} → IsZero S n d → BCert k n d
    bstep : ∀ {k n d} (χ : Filler S n d)
          → BCert k (suc n) (∂ S n d χ) → BCert (suc k) n d

  bcert→cert : ∀ {k n d} → BCert k n d → Cert n d
  bcert→cert (bdone z)   = done z
  bcert→cert (bstep χ b) = step χ (bcert→cert b)

  ----------------------------------------------------------------------
  -- §3.  Fill_∞: the coinductive total branch (Def 2.2.2, second box).
  ----------------------------------------------------------------------

  record Branch (n : ℕ) (d : Obs S n) : Type ℓ where
    coinductive
    field
      chosen : Filler S n d
      onward : Branch (suc n) (∂ S n d chosen)

  open Branch public

  FillInf : (n : ℕ) → Obs S n → Type ℓ
  FillInf = Branch

------------------------------------------------------------------------
-- §4.  Prop 2.2.3 (⇒): Fill_term ⇒ Fill_∞.
--
--      The note's proof is "extend by identities, since ∂(id) is again
--      distinguished".  That is a hypothesis on the system and it is
--      taken here as one, explicitly, rather than smuggled in.
------------------------------------------------------------------------

HasIdFillers : {ℓ : Level} → FillSys ℓ → Type ℓ
HasIdFillers S =
  (n : ℕ) (d : Obs S n) → IsZero S n d
  → Σ[ χ ∈ Filler S n d ] IsZero S (suc n) (∂ S n d χ)

module _ {ℓ} {S : FillSys ℓ} (idf : HasIdFillers S) where

  branchFromZero : ∀ n d → IsZero S n d → Branch S n d
  chosen (branchFromZero n d z) = fst (idf n d z)
  onward (branchFromZero n d z) =
    branchFromZero (suc n) (∂ S n d (fst (idf n d z))) (snd (idf n d z))

  -- Prop 2.2.3 (⇒).
  cert→branch : ∀ {n d} → Cert S n d → Branch S n d
  cert→branch (done {n} {d} z) = branchFromZero n d z
  chosen (cert→branch (step χ c)) = χ
  onward (cert→branch (step χ c)) = cert→branch c

------------------------------------------------------------------------
-- §5.  Prop 2.2.3, STRICTNESS — and §4.2's refutation of nilpotence.
--
--      A∞ is the note's A_∞ witness in its barest form: one obstruction
--      per level, never distinguished, always fillable, with exactly
--      ONE filler at each node.  So it is uniquely (hence finitely)
--      branching, and it has a total branch and no certificate.
--
--      Read as strictness (Prop 2.2.3): Fill_∞ does not imply Fill_term.
--      Read as §4.2: a hypothesis that bounds the branching — which is
--      all the note's Corollary 4.2 says nilpotence buys — cannot bound
--      the LENGTH of the tower, since branching here is 1 and the tower
--      is infinite.  Only truncation bounds the length (§6).
------------------------------------------------------------------------

A∞ : FillSys ℓ-zero
Obs    A∞ _     = Unit
IsZero A∞ _ _   = ⊥
Filler A∞ _ _   = Unit
∂      A∞ _ _ _ = tt

noCert : ∀ n d → ¬ Cert A∞ n d
noCert n d (done z)   = ⊥-rec z
noCert n d (step χ c) = noCert (suc n) tt c

branchA∞ : ∀ n d → Branch A∞ n d
chosen (branchA∞ n d) = tt
onward (branchA∞ n d) = branchA∞ (suc n) tt

-- Fill_∞ holds, Fill_term fails.  A∞ is uniquely branching: see
-- `A∞-FinBranch` in §6, which exhibits the one-element enumeration.
A∞-strict : Branch A∞ 0 tt × (¬ Cert A∞ 0 tt)
A∞-strict = branchA∞ 0 tt , noCert 0 tt

------------------------------------------------------------------------
-- §6.  The decision procedure, and what it consumes.
------------------------------------------------------------------------

-- Decidability of the distinguished-element check: hypothesis (E)'s
-- "the predicate δ^(γ) = 0 is decidable".
DecZero : {ℓ : Level} → FillSys ℓ → Type ℓ
DecZero S = (n : ℕ) (d : Obs S n) → Dec (IsZero S n d)

-- FINITE BRANCHING (Thm 3.2(b)'s hypothesis): the fillers at each node
-- are covered by a finite list.  `cover` is what makes a failed search
-- conclusive; without it `enum` would only ever produce witnesses.
record FinBranch {ℓ : Level} (S : FillSys ℓ) : Type ℓ where
  field
    enum  : (n : ℕ) (d : Obs S n) → List (Filler S n d)
    cover : (n : ℕ) (d : Obs S n) (χ : Filler S n d)
          → Any (λ χ' → χ' ≡ χ) (enum n d)

open FinBranch public

A∞-FinBranch : FinBranch A∞
enum  A∞-FinBranch _ _   = tt ∷ []
cover A∞-FinBranch _ _ _ = here refl

module _ {ℓ} {S : FillSys ℓ} (dz : DecZero S) (fb : FinBranch S) where

  -- The decision procedure, as a term.  Both `dz` and `fb` are consumed:
  -- `dz` in the `bdone` case, `enum fb` to generate candidates and
  -- `cover fb` to refute `bstep` when the search fails.
  decBCert : (k n : ℕ) (d : Obs S n) → Dec (BCert S k n d)
  decBCert k n d with dz n d
  ... | yes z = yes (bdone z)
  decBCert zero n d | no ¬z = no λ { (bdone z) → ¬z z }
  decBCert (suc k) n d | no ¬z
    with decAny (λ χ → decBCert k (suc n) (∂ S n d χ)) (enum fb n d)
  ... | yes a = let (χ , b) = anyΣ a in yes (bstep χ b)
  ... | no ¬a = no λ
        { (bdone z)   → ¬z z
        ; (bstep χ b) →
            ¬a (mapAny (λ χ' p → subst (λ y → BCert S k (suc n) (∂ S n d y))
                                       (sym p) b)
                       (cover fb n d χ)) }

------------------------------------------------------------------------
-- §7.  Theorem 4.1: truncation bounds the tower, and the bound IS the
--      depth index.  Under it Fill_term holds and is decidable.
------------------------------------------------------------------------

-- N-truncated: every obstruction at level ≥ N is the distinguished one.
Truncated : {ℓ : Level} → FillSys ℓ → ℕ → Type ℓ
Truncated S N = (n : ℕ) → N ≤ n → (d : Obs S n) → IsZero S n d

-- The tower must be fillable at all to be filled: one filler per node.
HasFillers : {ℓ : Level} → FillSys ℓ → Type ℓ
HasFillers S = (n : ℕ) (d : Obs S n) → Filler S n d

module _ {ℓ} {S : FillSys ℓ} {N : ℕ}
         (tr : Truncated S N) (hf : HasFillers S) where

  private
    ≤-step : {j n : ℕ} → N ≤ suc j + n → N ≤ j + suc n
    ≤-step {j} {n} p = subst (N ≤_) (sym (+-suc j n)) p

  -- j steps of fuel suffice as soon as the level reached, j + n, is at
  -- or above the truncation level.
  build : (j n : ℕ) (d : Obs S n) → N ≤ j + n → BCert S j n d
  build zero n d p = bdone (tr n p d)
  build (suc j) n d p =
    bstep (hf n d) (build j (suc n) (∂ S n d (hf n d)) (≤-step {j} {n} p))

  -- Theorem 4.1: a certificate of depth ≤ N, from any level-0 defect.
  truncCert : (d : Obs S 0) → BCert S N 0 d
  truncCert d = build N 0 d (subst (N ≤_) (sym (+-zero N)) ≤-refl)

  truncated-FillTerm : (d : Obs S 0) → FillTerm S 0 d
  truncated-FillTerm d = bcert→cert S (truncCert d)

  -- …hence decidable, trivially and honestly: the answer is always yes.
  truncated-FillTerm-dec : (d : Obs S 0) → Dec (FillTerm S 0 d)
  truncated-FillTerm-dec d = yes (truncated-FillTerm d)

------------------------------------------------------------------------
-- §8.  The asymmetry: without finite branching, deciding certificate
--      existence decides an arbitrary unbounded existential over ℕ.
--
--      InfB P has ONE level-0 defect with ℕ-many fillers, the k-th
--      producing the Boolean P k as the level-1 obstruction; above
--      level 0 the obstruction never changes.  A certificate is
--      therefore exactly a k with P k ≡ true.
--
--      Positive instances remain exhibitable (`∃→Cert`), which is the
--      point: Fill_term's successes are certifiable, its failures are
--      not — "neither success nor failure of coherence is reportable"
--      loses its first half and keeps its second.
------------------------------------------------------------------------

module _ (P : ℕ → Bool) where

  ObsP : ℕ → Type ℓ-zero
  ObsP zero    = Unit
  ObsP (suc _) = Bool

  InfB : FillSys ℓ-zero
  Obs    InfB              = ObsP
  IsZero InfB zero    _    = ⊥
  IsZero InfB (suc _) b    = b ≡ true
  Filler InfB zero    _    = ℕ
  Filler InfB (suc _) _    = Unit
  ∂      InfB zero    _  k = P k
  ∂      InfB (suc _) b  _ = b

  -- Above level 0 the obstruction is invariant, so a certificate there
  -- can only end by being already distinguished.
  certAbove : ∀ n (b : Bool) → Cert InfB (suc n) b → b ≡ true
  certAbove n b (done z)   = z
  certAbove n b (step χ c) = certAbove (suc n) b c

  Cert→∃ : Cert InfB 0 tt → Σ[ k ∈ ℕ ] P k ≡ true
  Cert→∃ (done z)   = ⊥-rec z
  Cert→∃ (step k c) = k , certAbove 0 (P k) c

  ∃→Cert : Σ[ k ∈ ℕ ] P k ≡ true → Cert InfB 0 tt
  ∃→Cert (k , q) = step k (done q)

-- The reduction.  A uniform decision procedure for certificate
-- existence on infinitely-branching systems would decide, for every
-- P : ℕ → Bool, whether some k has P k ≡ true.  Such a decision is not
-- available, so neither is the decision procedure, and the finite
-- branching consumed by `decBCert` in §6 is load-bearing rather than
-- convenient.
infBranch-decides-∃ :
    ((P : ℕ → Bool) → Dec (Cert (InfB P) 0 tt))
  → ((P : ℕ → Bool) → Dec (Σ[ k ∈ ℕ ] P k ≡ true))
infBranch-decides-∃ d P with d P
... | yes c  = yes (Cert→∃ P c)
... | no ¬c  = no λ w → ¬c (∃→Cert P w)

-- Conversely the systems of §8 ARE covered by the rest of the module
-- when the search is bounded: `∃→Cert` exhibits positive instances and
-- the kernel checks them in finite time.  That is the whole asymmetry.
witness-is-checkable : (P : ℕ → Bool) (k : ℕ) → P k ≡ true → Cert (InfB P) 0 tt
witness-is-checkable P k q = ∃→Cert P (k , q)

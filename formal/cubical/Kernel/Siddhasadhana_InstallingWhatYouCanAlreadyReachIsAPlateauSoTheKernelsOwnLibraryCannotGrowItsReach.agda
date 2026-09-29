{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateau
--                      SoTheKernelsOwnLibraryCannotGrowItsReach
--
-- TERM.  सिद्धसाधन · siddhasādhana -- establishing what is already
-- established; in the Nyya debate literature a defect of a would-be proof,
-- because the sdhya is already siddha for the opponent, so the inference
-- accomplishes nothing.  Discussed under the निग्रहस्थान / जाति apparatus
-- descending from Gautama's *Nyyastra* (~2nd c. CE) book 5 and developed
-- in the later Naiyyika manuals.
--
------------------------------------------------------------------------
-- `NaturalMachine.Obstruction` proves a separation on ITS substrate (unary
-- terms, a vocabulary of head shapes):
--
--   plateau : FreqChain V W → Matches W ≡ Matches V
--
-- A proposer that installs what it can already match leaves the matcher
-- EQUAL AS A FUNCTION, after any number of steps; and `obs-step-strict`
-- says one obstruction-indexed step cannot.
--
-- THIS FILE ANSWERS THE FIRST HALF: the plateau transfers, and it is not a
-- port.  Obstruction's proof runs through `extend-absorbed` on a Bool
-- membership test.  The kernel's runs through `control-sound`, which is a
-- different fact about a different object: the control of `install d` at t′
-- IS an identification t′ ≡ t, so a library extended by a theorem it could
-- already reach enables nothing it could not already enable.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--
--   §1  InstallChain -- the kernel's analogue of FreqChain: extend the
--       library with a derivation from a context already enabled.
--   §2  install-chain-plateau -- reach is invariant along any such chain.
--   §3  kernel-install-chains-cannot-reach-a-tower -- the concrete
--       corollary, on the kernel's OWN library.  Exact analogue of
--       Obstruction.frequency-cannot-reach.
--
-- SCOPE.  The plateau is a fact about `NativeOperation` (ground installs).
-- It does NOT hold for the pervading operations of
-- kernel-flat/TheControlCarriesItsInstanceAndLocusSoOneTheoremFiresAtAClass:
-- installing `pervading d` for a derivation from an enabled context enables
-- every instance and locus of that context, which can include terms not
-- enabled before (e.g. `accepted` at `add var (suc zero)` pervades to
-- `add zero (suc zero)`).  Generalisation is exactly what breaks the plateau.
--
-- `SomeEnabled` is restated here from Vyapti_ rather than imported, so
-- that this module depends on the kernel and not on that module's
-- other machinery; the definition is identical.
------------------------------------------------------------------------

module Kernel.Siddhasadhana_InstallingWhatYouCanAlreadyReachIsAPlateauSoTheKernelsOwnLibraryCannotGrowItsReach where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar
open import Kernel.GenerativeKernel using (direct-operation ; detour-operation)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)

------------------------------------------------------------------------
-- §1.  The reach predicate, and the kernel's analogue of a FreqChain.
------------------------------------------------------------------------

-- Identical to Vyapti_'s definition; restated so this module's dependency
-- is the kernel itself.
SomeEnabled : List NativeOperation → Tm → Type₀
SomeEnabled []       t = ⊥
SomeEnabled (op ∷ L) t = NativeOperation.Control op t ⊎ SomeEnabled L t

-- Obstruction.FreqChain installs `headShape W t m` -- a head read off a term
-- the vocabulary ALREADY matches.  The kernel's counterpart: install a
-- derivation starting at a context the library ALREADY enables.
data InstallChain (L : List NativeOperation) : List NativeOperation → Type₁ where
  done : InstallChain L L
  step : {M : List NativeOperation} → InstallChain L M
       → (t : Tm) → SomeEnabled M t
       → {b : Tm} (d : Derivation t b)
       → InstallChain L (install d ∷ M)

------------------------------------------------------------------------
-- §2.  THE PLATEAU.  One step first: the control of `install d` at t′ is an
--      identification t′ ≡ t, and t was already enabled, so transporting
--      the old evidence backwards along it discharges the new branch.
------------------------------------------------------------------------

install-step-absorbed :
  (M : List NativeOperation) (t : Tm) (e : SomeEnabled M t)
  {b : Tm} (d : Derivation t b) (t' : Tm)
  → SomeEnabled (install d ∷ M) t' → SomeEnabled M t'
install-step-absorbed M t e d t' (inl c) = subst (SomeEnabled M) (sym c) e
install-step-absorbed M t e d t' (inr s) = s

-- Hence along a whole chain.  Compare Obstruction.plateau: there the
-- conclusion is an equality of matchers; here it is that the reach of the
-- grown library is contained in the reach of the seed, which with
-- monotonicity is the same statement and is the half the corollary needs.
install-chain-plateau :
  {L M : List NativeOperation} → InstallChain L M
  → (t' : Tm) → SomeEnabled M t' → SomeEnabled L t'
install-chain-plateau done            t' s = s
install-chain-plateau (step ch t e d) t' s =
  install-chain-plateau ch t' (install-step-absorbed _ t e d t' s)

------------------------------------------------------------------------
-- §3.  THE COROLLARY, on the kernel's own two operations.  Both have source
--      `add var (suc zero)`; a tower has an outermost `suc`.  A head
--      discriminator kills the control, and §2 extends it to anything the
--      library builds from itself.
------------------------------------------------------------------------

isAdd : Tm → Bool
isAdd (add _ _) = true
isAdd _         = false

tower : ℕ → Tm
tower ℕ.zero    = zero
tower (ℕ.suc n) = suc (tower n)

kernel-library : List NativeOperation
kernel-library = direct-operation ∷ detour-operation ∷ []

-- The seed case: neither of the kernel's two operations fires on a tower.
kernel-cannot-reach-a-tower :
  SomeEnabled kernel-library (tower (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))) → ⊥
kernel-cannot-reach-a-tower (inl p)       = true≢false (sym (cong isAdd p))
kernel-cannot-reach-a-tower (inr (inl p)) = true≢false (sym (cong isAdd p))

-- And by §2, nothing the library builds out of itself does either.
kernel-install-chains-cannot-reach-a-tower :
  {M : List NativeOperation} → InstallChain kernel-library M
  → SomeEnabled M (tower (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))) → ⊥
kernel-install-chains-cannot-reach-a-tower ch s =
  kernel-cannot-reach-a-tower (install-chain-plateau ch _ s)

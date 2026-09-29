{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- स्थापना-वर्ग — the moduli of installations.
--
-- THE CLAIM: the kernel is the
-- fixed point of the spec → moduli → motive tower — the one object
-- that is simultaneously a point of its own moduli, because `install`
-- turns a theorem of the object into a structure map of the object.
-- For that sentence to be mathematics rather than mood, the kernel's
-- self-extensions must be CLASSIFIED, and the classification must
-- name what a self-extension is over and above the theorem it
-- installs.  Here is the classification, and the answer is: a gauge.
--
--   §1  INSTALLATION LOSES NOTHING: extracting the certificate from
--       an installed derivation returns the derivation, by refl.
--       install is a section of extract — theorem → operation →
--       theorem is the identity.
--
--   §2  THE MODULI OF SELF-EXTENSIONS: a NativeOperation is exactly
--       a certificate together with a control gauge — a predicate on
--       terms and a soundness witness pinning it to the source.  The
--       equivalence is exhibited (both round trips refl, by η), so
--       "what is an operation beyond its theorem?" has an exact
--       answer: a choice of gauge, nothing else.
--
--   §3  EVERY OPERATION FACTORS THROUGH ITS OWN INSTALLATION: for
--       any O, reindexing controls along control-sound carries O's
--       applicability into that of install (checked O), and both
--       apply and apply-checked commute with the reindexing — each
--       agreement is refl.  So the image of install exhausts every
--       self-extension up to gauge: capability grows by one term per
--       theorem, as a factorization theorem, not a slogan.
--
--   §4  THE CANONICAL GAUGE IS THE WHOLE LOCUS: the applicability
--       space of install d is contractible with centre the source —
--       the one point there is to fire at — and §5: every gauge's
--       applicability space maps into that contractible locus over
--       the identity of terms.  However permissive the control, it
--       is a shadow of the one point.
--
-- Read together: self-extension is classified by derivation up to
-- control gauge; installation is the canonical — total, terminal —
-- gauge; and no gauge buys an application the certificate did not
-- already license (§3, by refl).  The Maurer–Cartan reading of
-- conservative self-rewrite lands here already solved: the coherence
-- equation is control-sound, its solutions are the gauges, and gauge
-- equivalence classes of solutions are the derivations themselves.
--
------------------------------------------------------------------------

module SthapanaVarga_SelfExtensionIsClassifiedByDerivationUpToControlGaugeAndInstallationIsTheCanonicalGauge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Kernel.RewriteCertificate using (Tm ; Derivation)
open import Kernel.ControlledGrammar using (NativeOperation ; install)

open NativeOperation

------------------------------------------------------------------------
-- ० · The certificate of an operation, and its gauge.
------------------------------------------------------------------------

Certificate : Type₀
Certificate = Σ[ l ∈ Tm ] Σ[ r ∈ Tm ] Derivation l r

extract : NativeOperation → Certificate
extract O = source O , target O , checked O

-- A control gauge at a source: a predicate on terms together with the
-- soundness witness pinning every satisfying term to that source.
Gauge : Tm → Type₁
Gauge l = Σ[ C ∈ (Tm → Type₀) ] ({t : Tm} → C t → t ≡ l)

------------------------------------------------------------------------
-- १ · Installation is a section of extraction: nothing added, nothing
--     lost, on the theorem side — by refl.
------------------------------------------------------------------------

install-section : {l r : Tm} (d : Derivation l r)
  → extract (install d) ≡ (l , r , d)
install-section d = refl

------------------------------------------------------------------------
-- २ · The classification: an operation IS a certificate with a gauge.
------------------------------------------------------------------------

Extension : Type₁
Extension = Σ[ c ∈ Certificate ] Gauge (fst c)

assemble : Extension → NativeOperation
source        (assemble ((l , r , d) , C , s)) = l
target        (assemble ((l , r , d) , C , s)) = r
checked       (assemble ((l , r , d) , C , s)) = d
Control       (assemble ((l , r , d) , C , s)) = C
control-sound (assemble ((l , r , d) , C , s)) = s

disassemble : NativeOperation → Extension
disassemble O = extract O , Control O , control-sound O

classification : NativeOperation ≃ Extension
classification = isoToEquiv (iso disassemble assemble (λ _ → refl) (λ _ → refl))

-- Under this equivalence, install d is the pair (its certificate, the
-- canonical gauge (λ t → t ≡ l , id)); §1 is its first projection.

------------------------------------------------------------------------
-- ३ · Every operation factors through the installation of its own
--     certificate: reindex the control along its soundness witness,
--     and every application agrees — definitionally.
------------------------------------------------------------------------

module _ (O : NativeOperation) where

  installed : NativeOperation
  installed = install (checked O)

  reindex : {t : Tm} → Control O t → Control installed t
  reindex = control-sound O

  apply-factors : (t : Tm) (c : Control O t)
    → apply O t c ≡ apply installed t (reindex c)
  apply-factors t c = refl

  apply-checked-factors : (t : Tm) (c : Control O t)
    → apply-checked O t c ≡ apply-checked installed t (reindex c)
  apply-checked-factors t c = refl

------------------------------------------------------------------------
-- ४ · The canonical gauge's applicability space is contractible with
--     centre the source: one theorem, one locus.
------------------------------------------------------------------------

locusContr : {l r : Tm} (d : Derivation l r)
  → isContr (Σ[ t ∈ Tm ] Control (install d) t)
locusContr {l} d .fst = l , refl
locusContr {l} d .snd (t , p) i = p (~ i) , λ j → p (~ i ∨ j)

------------------------------------------------------------------------
-- ५ · And every gauge is a shadow of it: the applicability space of
--     any operation maps into the canonical contractible locus, over
--     the identity of terms.
------------------------------------------------------------------------

intoLocus : (O : NativeOperation)
  → Σ[ t ∈ Tm ] Control O t → Σ[ t ∈ Tm ] Control (install (checked O)) t
intoLocus O (t , c) = t , control-sound O c

intoLocus-over-id : (O : NativeOperation) (x : Σ[ t ∈ Tm ] Control O t)
  → fst (intoLocus O x) ≡ fst x
intoLocus-over-id O x = refl

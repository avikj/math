{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Adesa_SubstitutionIsAdmissibleOnDerivationsSoASchemaCan
--               CarryACertificateAndNotOnlyAMeaning
--
-- TERM.  आदेश · ādeśa -- in Pāṇini, *Aṣṭādhyāyī* (~500 BCE), the SUBSTITUTE
-- that takes the place of a स्थानिन् (sthānin, the substituend); the
-- machinery around it includes स्थानेऽन्तरतमः (1.1.50, the nearest
-- substitute) and the sthānivadbhāva rule स्थानिवदादेशोऽनल्विधौ (1.1.56),
-- which says an dea behaves LIKE its sthnin for the purposes of further
-- rules, with a stated exception.
--
------------------------------------------------------------------------
-- MOTIVATION.
--
-- Vyapti_.SchematicOperation carries `apply-sound`, an EVAL EQUALITY:
--
--     apply-sound : (t : Tm) (c : Control t) (ρ : Env)
--                 → eval t ρ ≡ eval (apply t c) ρ
--
-- Kernel.ControlledGrammar.NativeOperation carries `apply-checked`, a DERIVATION:
--
--     apply-checked : (t : Tm) (c : Control t) → Derivation t (apply t c)
--
-- So a schema has the semantics of its instances and not their
-- certificates.
------------------------------------------------------------------------
-- WHAT IS PROVED.  §1 substitution is admissible on one rewrite; §2 hence
-- on a whole walk; §3 the consequence for schemas; §4 exhibited at the two
-- contexts Vyapti_ proves no single NativeOperation can both fire at.
------------------------------------------------------------------------

module Kernel.Adesa_SubstitutionIsAdmissibleOnDerivationsSoASchemaCanCarryACertificateAndNotOnlyAMeaning where

open import Cubical.Foundations.Prelude
open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  One rewrite survives substitution, structurally, all six
--      constructors.  `reverse` included, so the groupoid structure of the
--      derivation space is carried across unchanged.
------------------------------------------------------------------------

subStep : (u : Tm) {a b : Tm} → Step a b → Step (subVar u a) (subVar u b)
subStep u (add-zero x)    = add-zero (subVar u x)
subStep u (add-suc x y)   = add-suc (subVar u x) (subVar u y)
subStep u (suc-step p)    = suc-step (subStep u p)
subStep u (add-left p z)  = add-left (subStep u p) (subVar u z)
subStep u (add-right z p) = add-right (subVar u z) (subStep u p)
subStep u (reverse p)     = reverse (subStep u p)

------------------------------------------------------------------------
-- §2.  Hence a whole walk survives it.  No relation is imposed and none is
--      quotiented: `then-step` goes to `then-step`, so the image of a
--      derivation has exactly the length of its preimage.
------------------------------------------------------------------------

subDeriv : (u : Tm) {a b : Tm} → Derivation a b
         → Derivation (subVar u a) (subVar u b)
subDeriv u (done x)        = done (subVar u x)
subDeriv u (then-step p d) = then-step (subStep u p) (subDeriv u d)

------------------------------------------------------------------------
-- §3.  THE CONSEQUENCE.  A checked derivation instantiates to a checked
--      derivation at every substitution instance, with no new proof
--      obligation and no appeal to `eval`.  This is the certificate a
--      schematic operation lacks.
------------------------------------------------------------------------

schema-instance-is-certified :
  {lhs rhs : Tm} → Derivation lhs rhs
  → (u : Tm) → Derivation (subVar u lhs) (subVar u rhs)
schema-instance-is-certified d u = subDeriv u d

------------------------------------------------------------------------
-- §4.  Exhibited on the kernel's own accepted theorem
--      `accepted : Derivation (add var (suc zero)) (suc var)`
--      at the two contexts of Vyapti_.ctx₀ and Vyapti_.ctx₁, which
--      `no-native-operation-does-this` proves no single NativeOperation can
--      both fire at.  One derivation, two certified instances.
------------------------------------------------------------------------

inst₀ : Derivation (add zero (suc zero)) (suc zero)
inst₀ = schema-instance-is-certified accepted zero

inst₁ : Derivation (add (suc zero) (suc zero)) (suc (suc zero))
inst₁ = schema-instance-is-certified accepted (suc zero)

-- And each still means what it says, at every environment, through the
-- kernel's own `derivation-sound` and not through a new soundness argument.

inst₀-sound : (ρ : Env) → eval (add zero (suc zero)) ρ ≡ eval (suc zero) ρ
inst₀-sound = derivation-sound inst₀

inst₁-sound : (ρ : Env) → eval (add (suc zero) (suc zero)) ρ ≡ eval (suc (suc zero)) ρ
inst₁-sound = derivation-sound inst₁

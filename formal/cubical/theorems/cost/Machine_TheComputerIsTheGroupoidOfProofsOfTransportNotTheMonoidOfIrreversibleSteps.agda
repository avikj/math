{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- यन्त्र — what the computer is: the groupoid of proofs-of-transport, not
-- the monoid of irreversible steps.
--
-- WHAT IS THE COMPUTER?  Not a metaphor — the
-- machine.  This file answers it as a checked term, and the answer is one
-- word with a proof: a GROUPOID.
--
-- A CLASSICAL COMPUTER's operations form a MONOID.  You can sequence
-- steps (∘) and there is a no-op (id), but you cannot in general UNDO a
-- step: erasing a bit is irreversible, and by Landauer it costs kT ln 2
-- of heat each time (Bennett: reversible computation has no such floor,
-- but pays per EXECUTION).  A monoid has composition and identity and NO
-- inverse.  That missing inverse is the heat.
--
-- THIS COMPUTER's operations are PROOFS OF TRANSPORT — equivalences
-- e : A ≃ B, equivalently paths ua e : A ≡ B (`PramanaSankramana`).  And
-- those form a GROUPOID: composition, identity, AND a two-sided inverse,
-- with the laws holding definitionally (the library proves each by
-- `equivEq refl`).  Every program is invertible; every run can be run
-- backwards to exactly where it began; nothing is erased.
--
-- "Nothing is erased" is checked below (§2's inverse laws) and is a
-- statement about types;
-- "nothing dissipates" is a statement about a physical implementation,
-- of which there is none here — no energy, no temperature, no entropy,
-- no measure appears in this file.  Landauer's principle is the MOTIVE
-- for asking which step is non-injective, and the precise typal content
-- of "erases nothing" is `Vyapti_TheLossOrderIsCoarsening…agda` §६: the
-- collision type `विस्मृतिः Φ` is empty when `Φ` is an equivalence.
-- That is the whole of it.  No heat is derived and no physical constant
-- is on this page.
--
-- The groupoid IS the computer, and the presence of the
-- inverse — the one thing the monoid lacks — is the whole difference.
--
-- यन्त्र (yantra) is the corpus's word for the machine (`Yantra_The-
-- OrgansAreOneMachineOnOneWire`).
--
-- WHAT IS PROVED (all reusing the library's checked equivalence laws, so
-- these are the machine's instruction-set laws, not new mathematics):
--
--   §2  the five groupoid laws on Receipt = _≃_:
--       एकाग्रता-वाम / -दक्षिण   identity is a two-sided no-op
--       प्रतिलोमः-दक्षिण / -वाम   inverse is two-sided (the run undoes)
--       साहचर्यम्                composition is associative (sequencing)
--   §3  चालनम् : running a program IS transport along its path.
--       चालनं-प्रतिलोम्यम् : every run has an inverse run — reversible.
--       चालन-सन्धिः : composing programs, then running, = running each in
--       turn (the machine is a functor from the groupoid to functions).
--   §4  the contrast, as types: a MONOID interface has ∘ and id and no
--       inverse field; the groupoid adds प्रतिलोमः.  The added field is
--       the reversibility.  (NOT the heat — see above.)
--
-- WHY THIS IS THE RIGHT COMPUTER FOR COMPUTATIONAL SPACETIME.  Physics is
-- reversible (unitary evolution, time-symmetric microdynamics); its state
-- moves by PARALLEL TRANSPORT along paths, and indistinguishable
-- configurations are genuinely identified (gauge / general covariance).
-- A groupoid of transports is exactly that structure: paths compose and
-- invert, and univalence (`ua`) makes equivalent types EQUAL — so the
-- machine cannot even express a difference between physically
-- indistinguishable states.  General covariance is not imposed on this
-- computer; it is what its equality IS.
------------------------------------------------------------------------

module Machine_TheComputerIsTheGroupoidOfProofsOfTransportNotTheMonoidOfIrreversibleSteps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using ( _≃_ ; idEquiv ; compEquiv ; invEquiv ; equivFun
        ; compEquivIdEquiv ; compEquivEquivId
        ; invEquiv-is-rinv ; invEquiv-is-linv ; compEquiv-assoc )
open import Cubical.Foundations.Univalence using (ua)

private
  variable
    ℓ : Level
    A B C D : Type ℓ

------------------------------------------------------------------------
-- §1  A program is a proof of transport: a receipt/equivalence.
------------------------------------------------------------------------

Program : Type ℓ → Type ℓ → Type ℓ
Program A B = A ≃ B

_∥_ : Program A B → Program B C → Program A C     -- sequencing
_∥_ = compEquiv

नो-कर्म : Program A A                               -- the no-op
नो-कर्म = idEquiv _

प्रतिलोमः : Program A B → Program B A               -- the undo
प्रतिलोमः = invEquiv

------------------------------------------------------------------------
-- §2  The five groupoid laws — the machine's instruction-set identities.
--     Each is a library term; that they hold is what makes this a
--     groupoid and not merely a monoid-with-a-partial-undo.
------------------------------------------------------------------------

एकाग्रता-वाम : (p : Program A B) → (नो-कर्म ∥ p) ≡ p
एकाग्रता-वाम = compEquivIdEquiv

एकाग्रता-दक्षिण : (p : Program A B) → (p ∥ नो-कर्म) ≡ p
एकाग्रता-दक्षिण = compEquivEquivId

-- the run undoes: forward then back is the no-op, and back then forward too
प्रतिलोमः-दक्षिण : (p : Program A B) → (p ∥ प्रतिलोमः p) ≡ नो-कर्म
प्रतिलोमः-दक्षिण = invEquiv-is-rinv

प्रतिलोमः-वाम : (p : Program A B) → (प्रतिलोमः p ∥ p) ≡ नो-कर्म
प्रतिलोमः-वाम = invEquiv-is-linv

साहचर्यम् : (p : Program A B) (q : Program B C) (r : Program C D)
          → ((p ∥ q) ∥ r) ≡ (p ∥ (q ∥ r))
साहचर्यम् p q r = sym (compEquiv-assoc p q r)

------------------------------------------------------------------------
-- §3  Running a program IS transport, and it is a functor: composition
--     of programs runs as composition of functions, and every run is
--     reversible.
------------------------------------------------------------------------

-- to run p on a datum is to transport along its path (or apply the equiv)
चालनम् : Program A B → A → B
चालनम् p = equivFun p

-- every run has an inverse run — this is the field a monoid lacks
चालनं-प्रतिलोम्यम् : Program A B → B → A
चालनं-प्रतिलोम्यम् p = equivFun (प्रतिलोमः p)

-- the machine is a functor: run (p then q) = run q ∘ run p
चालन-सन्धिः : (p : Program A B) (q : Program B C) (a : A)
            → चालनम् (p ∥ q) a ≡ चालनम् q (चालनम् p a)
चालन-सन्धिः p q a = refl        -- compEquiv composes the functions; definitional

-- the no-op runs as the identity
चालनं-नो-कर्म : (a : A) → चालनम् (नो-कर्म {A = A}) a ≡ a
चालनं-नो-कर्म a = refl

------------------------------------------------------------------------
-- §4  The contrast made into types: a monoid interface has sequencing and
--     a no-op and no inverse; the groupoid adds प्रतिलोमः with its two
--     laws.  The added field is the reversibility.  (NOT the heat: see the
--     correction inset at the top.  Records, so the difference is structural.)
------------------------------------------------------------------------

-- what a classical machine offers on its operations (one object, for
-- brevity): compose and a no-op.  No inverse.
record MonoidMachine (Op : Type ℓ) : Type ℓ where
  field
    seq  : Op → Op → Op
    noop : Op
    unitL : (x : Op) → seq noop x ≡ x
    unitR : (x : Op) → seq x noop ≡ x
    assoc : (x y z : Op) → seq (seq x y) z ≡ seq x (seq y z)

-- what THIS machine offers: everything above, PLUS a two-sided inverse.
record GroupoidMachine (Op : Type ℓ) : Type ℓ where
  field
    mon : MonoidMachine Op
    inv : Op → Op
  open MonoidMachine mon public
  field
    invR : (x : Op) → seq x (inv x) ≡ noop
    invL : (x : Op) → seq (inv x) x ≡ noop

-- the endo-programs A ≃ A ARE a groupoid-machine: the added `inv` field
-- is populated by प्रतिलोमः, the field a MonoidMachine cannot fill.
यन्त्रम् : (A : Type ℓ) → GroupoidMachine (Program A A)
यन्त्रम् A = record
  { mon = record
      { seq = _∥_ ; noop = नो-कर्म
      ; unitL = एकाग्रता-वाम ; unitR = एकाग्रता-दक्षिण ; assoc = साहचर्यम् }
  ; inv = प्रतिलोमः
  ; invR = प्रतिलोमः-दक्षिण ; invL = प्रतिलोमः-वाम }

{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- TheControlCarriesItsInstanceAndLocusSoOneTheoremFiresAtAClass
--
-- TERM.  व्याप्ति · vyāpti — pervasion, the invariable concomitance that
-- makes an inference carry from the case at hand to every case of the same
-- mark.  Root notion in Gautama, *Nyāyasūtra* (~2nd c. CE) under अनुमान;
-- the vyāptivāda and the उपाधि that defeats a proposed pervasion are
-- Navya-Nyya, Gagea, *Tattvacintmai* (~1325).
--
------------------------------------------------------------------------
-- WHAT THIS FILE DOES, in one sentence.
--
-- It gives the kernel's unit of learned behaviour a control that carries
-- its own INSTANCE and its own LOCUS, so one installed theorem fires at a
-- `Tm × Locus`-indexed family of contexts instead of at one term — and it
-- does so with NO new soundness obligation, because the two lemmas that
-- discharge it are structural recursions the calculus already admitted.
--
-- THE SITUATION IT ANSWERS.  Two records stood side by side and only one
-- of them was wired to anything:
--
--   `Kernel.ControlledGrammar.NativeOperation` — what `install` produces, what
--     `EnabledFuture` / `advance` / `Branch` / `merge` / `retire` are all
--     typed against.  `TheInstalledTheoremHasExactlyOneLocus…` proves it
--     can never pervade: `control-sound : Control t → t ≡ source` forces
--     `eka-adhikarana` for EVERY control a caller can supply, so capability
--     grows by one TERM per theorem and never by a class.
--
--   `TheInstalledOperationHasNoPervasion….SchematicOperation` — control
--     carrying a substitution witness, proved STRICTLY more expressive
--     (`no-native-operation-does-this`).  It produces no NativeOperation,
--     so it cannot enter `EnabledFuture`, cannot be stepped by `advance`,
--     cannot be merged, cannot be retired.  A proof of expressiveness
--     standing BESIDE the executable kernel rather than inside it.
--
-- So `learn = install ∘ CheckedFuture.derivation` — the metacircular step,
-- "the transcript of a session is the machine's stock of moves" — closed
-- only over GROUND facts.  Every session taught the machine exactly one
-- key/value pair, and `kernel-cannot-reach-a-tower` exhibits that on the
-- kernel's own library.
--
------------------------------------------------------------------------
-- THE TWO LEMMAS, and why neither is a new axiom.
--
-- §1  SUBSTITUTION ACTS ON THE REWRITE CALCULUS.  `subStep` and `subDer`:
--     every `Step` constructor commutes with `subVar` on the nose, by
--     structural recursion, six clauses.  This is the DERIVATION-level
--     companion of `eval-subVar`, which was already in RewriteCertificate
--     and which `TheInstalledOperationHasNoPervasion…` used to make
--     SchematicOperation sound at the level of MEANING.  Doing it at the
--     level of the CERTIFICATE is what lets the schema keep the kernel's
--     defining property — that `apply-checked` transports a proof to the
--     site, so every firing arrives carrying a proof about that firing —
--     instead of degrading to a meaning-only operation.
--
-- §2  CONTEXT ACTS ON THE REWRITE CALCULUS.  `weaveDer`, lifting
--     `IntrinsicRewrite.weave-step` from `Step` (and `Run`) to
--     `Derivation`.  `IntrinsicRewrite` proved one local motion reweaves
--     through any one-hole `Locus`; `Derivation` is what a
--     `NativeOperation` actually carries.
--
-- Substitution and locus are orthogonal and pervasion needs both: a rule
-- should fire at `subVar u lhs` PLUGGED ANYWHERE.  §4's control is exactly
-- that pair, and §3's `apply-checked` is `subst` of `weaveDer l (subDer u
-- checked)` — the certificate travelling through both.
--
------------------------------------------------------------------------
-- WHAT IS PROVED
--   §1  sub-step / sub-derivation      substitution acts, structurally
--   §2  weave-derivation               context acts, structurally
--   §3  Operation, apply-checked,      the unified record; soundness by
--       operation-is-sound             the transported certificate alone
--   §4  ground / schematic / pervading three instances of ONE record;
--       native→operation               and every NativeOperation is one
--   §5  fires-at-two-contexts,         a pervading operation fires at two
--       no-native-operation-does-this  contexts differing in BOTH the
--                                      instance and the locus, which §1 of
--                                      TheInstalledTheoremHasExactlyOne…
--                                      forbids to every NativeOperation
--   §6  Future, advance, advance-      the wiring: the same no-premature-
--       preserves-branch-count         collapse law, over Operation
------------------------------------------------------------------------

module TheControlCarriesItsInstanceAndLocusSoOneTheoremFiresAtAClass where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; _×_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map ; length ; _++_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (rec to ⊎rec)
open import Cubical.Relation.Nullary using (¬_)

open import Kernel.RewriteCertificate
open import Kernel.ControlledGrammar using (NativeOperation ; install)
open import TheInstalledTheoremHasExactlyOneLocusSoCapabilityGrowsByOneNotByAClass
  using (eka-adhikarana)
open import Kernel.Interaction_TheKernelIsAnInteractiveSystemAndTheSessionRetiresIntoOneOperation
  using (Session)
open import TheCountingSemanticsIsADecategorificationAndTheBitItDropsIsASymmetry
  using (TEnv ; ⟦_⟧ ; derivation-equiv)
open import IntrinsicRewrite using (Locus ; root ; under-suc ; under-left
                                   ; under-right ; plug ; weave-step)

------------------------------------------------------------------------
-- §0.  `var` is the identity substitution.
--
-- Needed so that the GROUND case is genuinely an instance of the general
-- record rather than a parallel definition: an operation installed at a
-- fixed source is the one whose instance is `var` and whose locus is
-- `root`.
------------------------------------------------------------------------

subVar-var : (t : Tm) → subVar var t ≡ t
subVar-var var       = refl
subVar-var yvar      = refl
subVar-var zvar      = refl
subVar-var uvar      = refl
subVar-var vvar      = refl
subVar-var wvar      = refl
subVar-var zero      = refl
subVar-var (suc t)   = cong suc (subVar-var t)
subVar-var (add l r) = cong₂ add (subVar-var l) (subVar-var r)

------------------------------------------------------------------------
-- §1.  SUBSTITUTION ACTS ON THE REWRITE CALCULUS.
--
-- Every constructor of `Step` commutes with `subVar` definitionally —
-- `subVar u zero` is `zero`, `subVar u (add x (suc y))` is
-- `add (subVar u x) (suc (subVar u y))` — so each clause is the same
-- constructor at substituted arguments and nothing is proved by hand.
-- `reverse` comes along, so the substituted calculus is still reversible.
------------------------------------------------------------------------

sub-step : (u : Tm) {x y : Tm} → Step x y → Step (subVar u x) (subVar u y)
sub-step u (add-zero t)     = add-zero (subVar u t)
sub-step u (add-suc l r)    = add-suc (subVar u l) (subVar u r)
sub-step u (suc-step p)     = suc-step (sub-step u p)
sub-step u (add-left p t)   = add-left (sub-step u p) (subVar u t)
sub-step u (add-right t p)  = add-right (subVar u t) (sub-step u p)
sub-step u (reverse p)      = reverse (sub-step u p)

sub-derivation : (u : Tm) {a b : Tm}
               → Derivation a b → Derivation (subVar u a) (subVar u b)
sub-derivation u (done t)        = done (subVar u t)
sub-derivation u (then-step p d) = then-step (sub-step u p) (sub-derivation u d)

------------------------------------------------------------------------
-- §2.  CONTEXT ACTS ON THE REWRITE CALCULUS.
--
-- `IntrinsicRewrite.weave-step` already transports one motion through a
-- one-hole context.  A `Derivation` is a list of motions, so it transports
-- clause by clause.  This is the lift
-- the kernel needs, because `NativeOperation.checked` is a
-- `Derivation` and not a `Run`.
------------------------------------------------------------------------

weave-derivation : (l : Locus) {a b : Tm}
                 → Derivation a b → Derivation (plug l a) (plug l b)
weave-derivation l (done t)        = done (plug l t)
weave-derivation l (then-step p d) =
  then-step (weave-step l p) (weave-derivation l d)

------------------------------------------------------------------------
-- §3.  THE UNIFIED RECORD.
--
-- The single change from `NativeOperation` is the type of `control-sound`.
-- There, the enabling evidence at `t` is an identification of `t` with ONE
-- term, which is what `eka-adhikarana` reads off in a line.  Here it is an
-- identification of `t` with the operation's left-hand side AT AN INSTANCE
-- AND IN A LOCUS, both of which the control itself supplies.  `Control`
-- stays an open field: the caller may still hand over any type family, and
-- the soundness surface is still exactly one equation.
--
-- `apply` now CONSUMES the control, where `NativeOperation.apply` was
-- constant.  That is forced — the output depends on the instance — and it
-- is the change §4 of `TheInstalledOperationHasNoPervasion…` priced in
-- advance: the enabled set maps many-to-one onto emissions, so the witness
-- must be kept.  `advance` already keeps whole futures and is forbidden to
-- dedupe, so the kernel was built for this.
------------------------------------------------------------------------

record Operation : Type₁ where
  field
    lhs rhs : Tm
    checked : Derivation lhs rhs
    Control : Tm → Type₀
    instance-of : {t : Tm} → Control t → Tm
    locus-of    : {t : Tm} → Control t → Locus
    control-sound : {t : Tm} (c : Control t)
                  → t ≡ plug (locus-of c) (subVar (instance-of c) lhs)

  apply : (t : Tm) → Control t → Tm
  apply _ c = plug (locus-of c) (subVar (instance-of c) rhs)

  -- THE CERTIFICATE TRANSPORTED TO THE SITE, through both actions.  No new
  -- proof obligation: §1 and §2 are structural, and `subst` moves the
  -- result along the caller's own identification.
  apply-checked : (t : Tm) (c : Control t) → Derivation t (apply t c)
  apply-checked t c =
    subst (λ q → Derivation q (apply t c))
          (sym (control-sound c))
          (weave-derivation (locus-of c) (sub-derivation (instance-of c) checked))

open Operation using (lhs ; rhs ; Control ; apply ; apply-checked)

-- Soundness is not a field and is not re-proved: it is `derivation-sound`
-- of the transported certificate.  Nothing can be installed that is false,
-- for the same reason as before — an `Operation` cannot be constructed
-- without a `Derivation` between its declared endpoints.
operation-is-sound : (op : Operation) (t : Tm) (c : Control op t) (ρ : Env)
                   → eval t ρ ≡ eval (apply op t c) ρ
operation-is-sound op t c ρ = derivation-sound (apply-checked op t c) ρ

------------------------------------------------------------------------
-- §4.  THREE INSTANCES OF ONE RECORD — and the embedding.
------------------------------------------------------------------------

-- GROUND.  Instance `var`, locus `root`: exactly `Kernel.ControlledGrammar.install`.
ground : {a b : Tm} → Derivation a b → Operation
Operation.lhs           (ground {a} d) = a
Operation.rhs           (ground {b = b} d) = b
Operation.checked       (ground d) = d
Operation.Control       (ground {a} d) t = t ≡ a
Operation.instance-of   (ground d) _ = var
Operation.locus-of      (ground d) _ = root
Operation.control-sound (ground {a} d) c = c ∙ sym (subVar-var a)

-- SCHEMATIC.  The instance is carried; the locus is still the root.
schematic : {a b : Tm} → Derivation a b → Operation
Operation.lhs           (schematic {a} d) = a
Operation.rhs           (schematic {b = b} d) = b
Operation.checked       (schematic d) = d
Operation.Control       (schematic {a} d) t = Σ[ u ∈ Tm ] (t ≡ subVar u a)
Operation.instance-of   (schematic d) c = fst c
Operation.locus-of      (schematic d) _ = root
Operation.control-sound (schematic d) c = snd c

-- PERVADING.  Both are carried.  One theorem, a `Tm × Locus`-indexed
-- family of contexts.
pervading : {a b : Tm} → Derivation a b → Operation
Operation.lhs           (pervading {a} d) = a
Operation.rhs           (pervading {b = b} d) = b
Operation.checked       (pervading d) = d
Operation.Control       (pervading {a} d) t =
  Σ[ u ∈ Tm ] Σ[ l ∈ Locus ] (t ≡ plug l (subVar u a))
Operation.instance-of   (pervading d) c = fst c
Operation.locus-of      (pervading d) c = fst (snd c)
Operation.control-sound (pervading d) c = snd (snd c)

-- It fires at every instance in every locus, and the evidence is `refl`.
pervades : {a b : Tm} (d : Derivation a b) (u : Tm) (l : Locus)
         → Control (pervading d) (plug l (subVar u a))
pervades d u l = u , l , refl

-- EVERY NativeOperation IS AN Operation.  The embedding is why nothing
-- downstream is invalidated: `install` and its whole library remain
-- expressible, as the ground case.
native→operation : NativeOperation → Operation
native→operation op =
  ground (NativeOperation.checked op)

------------------------------------------------------------------------
-- §5.  THE SEPARATION, at two contexts differing in BOTH coordinates.
--
-- `accepted : Derivation (add var (suc zero)) (suc var)` is
-- RewriteCertificate's own theorem, unchanged.  As a pervading operation
-- it fires at
--
--     ctx₀ = add zero (suc zero)                    u = zero,     l = root
--     ctx₂ = add var (add (suc zero) (suc zero))    u = suc zero, l = under-right
--
-- and no `NativeOperation` whatsoever fires at both, for any control its
-- caller can invent.
------------------------------------------------------------------------

plus-one : Operation
plus-one = pervading accepted

ctx₀ ctx₂ : Tm
ctx₀ = add zero (suc zero)
ctx₂ = add var (add (suc zero) (suc zero))

ctx₀-enabled : Control plus-one ctx₀
ctx₀-enabled = pervades accepted zero root

ctx₂-enabled : Control plus-one ctx₂
ctx₂-enabled = pervades accepted (suc zero) (under-right var root)

-- and the outputs are the instantiated right-hand side, in place.
ctx₀-emits : apply plus-one ctx₀ ctx₀-enabled ≡ suc zero
ctx₀-emits = refl

ctx₂-emits : apply plus-one ctx₂ ctx₂-enabled ≡ add var (suc (suc zero))
ctx₂-emits = refl

leftIsVar : Tm → Bool
leftIsVar (add var _) = true
leftIsVar _           = false

ctx₀≢ctx₂ : ¬ (ctx₀ ≡ ctx₂)
ctx₀≢ctx₂ p = true≢false (sym (cong leftIsVar p))

-- THE POINT.  One theorem, two contexts that differ in instance and in
-- locus at once — and `eka-adhikarana` converts any NativeOperation that
-- managed the same into a path between the two contexts, which is empty.
no-native-operation-does-this :
  (op : NativeOperation)
  → NativeOperation.Control op ctx₀
  → NativeOperation.Control op ctx₂
  → ⊥
no-native-operation-does-this op c₀ c₂ =
  ctx₀≢ctx₂ (eka-adhikarana op ctx₀ ctx₂ c₀ c₂)

------------------------------------------------------------------------
-- §6.  THE WIRING.  `advance`, over `Operation`, with the same law.
--
-- This is the half that `SchematicOperation` never had, and the reason
-- this module is not a fourth unwired record: a pervading operation can be
-- offered as a future, executed, and carried in a branch list whose
-- multiplicity is exactly conserved.
------------------------------------------------------------------------

record Future (seed : Tm) : Type₁ where
  field
    operation : Operation
    control : Control operation seed

  target : Tm
  target = apply operation seed control

  derivation : Derivation seed target
  derivation = apply-checked operation seed control

record Checked (seed : Tm) : Type₀ where
  field
    target : Tm
    derivation : Derivation seed target

execute : {seed : Tm} → Future seed → Checked seed
Checked.target     (execute f) = Future.target f
Checked.derivation (execute f) = Future.derivation f

advance : {seed : Tm} → List (Future seed) → List (Checked seed)
advance = map execute

advance-preserves-branch-count : {seed : Tm} (fs : List (Future seed))
  → length (advance fs) ≡ length fs
advance-preserves-branch-count []       = refl
advance-preserves-branch-count (f ∷ fs) =
  cong ℕ.suc (advance-preserves-branch-count fs)

------------------------------------------------------------------------
-- §7.  THE LOOP CLOSES OVER A CLASS.
--
-- `learn` installs what a session did.  Over `NativeOperation` that was a
-- ground fact — one key, one value — which is `TheInstalledOperationHas
-- NoPervasion…`'s whole diagnosis.  Here it is `pervading`, and the point
-- is that this costs NOTHING: `pervading` places no condition whatever on
-- the derivation it is given, because §1 and §2 act on every derivation.
--
-- So the generalisation of a transcript is FREE, and it is free exactly
-- when the transcript mentions `var` — a derivation over a term containing
-- `var` already IS a schema, and `sub-derivation` hands you its instance
-- at any `u` without a search and without a new proof.  That is the
-- sentence `Vyapti`'s header wrote at the level of MEANING
-- ("generalisation is free in this calculus; memorisation is what costs"),
-- now at the level of the CERTIFICATE, and wired to the loop.
------------------------------------------------------------------------

learn : {s : Tm} → Checked s → Operation
learn f = pervading (Checked.derivation f)

learn-remembers-where-it-was :
  {s : Tm} (f : Checked s) → Operation.lhs (learn f) ≡ s
learn-remembers-where-it-was f = refl

learn-remembers-where-it-went :
  {s : Tm} (f : Checked s) → Operation.rhs (learn f) ≡ Checked.target f
learn-remembers-where-it-went f = refl

-- and what it learned fires at every instance in every locus.
learn-generalises : {s : Tm} (f : Checked s) (u : Tm) (l : Locus)
                  → Control (learn f) (plug l (subVar u s))
learn-generalises f u l = pervades (Checked.derivation f) u l

------------------------------------------------------------------------
-- §8.  A SESSION RETIRES INTO ONE OPERATION — a pervading one.
--
-- `Session` is imported, not re-declared: it is the same object
-- `TheKernelIsAnInteractiveSystem…` built, and `session-sound` is
-- unchanged.  Only the retirement differs, and it differs in exactly one
-- word.  A whole dialogue is one `Derivation`, hence one theorem, hence
-- one installable operation — and now that operation covers a class.
------------------------------------------------------------------------

retire : Session → Operation
retire S = pervading (Session.trace S)

retire-spans-the-whole-session :
  (S : Session)
  → (Operation.lhs (retire S) ≡ Session.origin S)
  × (Operation.rhs (retire S) ≡ Session.here S)
retire-spans-the-whole-session S = refl , refl

-- the retired move means what the conversation meant, at every site it
-- now fires at — soundness is the transported certificate, not a new proof
retire-is-sound :
  (S : Session) (t : Tm) (c : Control (retire S) t) (ρ : Env)
  → eval t ρ ≡ eval (apply (retire S) t c) ρ
retire-is-sound S = operation-is-sound (retire S)

-- and the whole dialogue is now available at every instance and locus,
-- which is the difference this module makes to the metacircular step.
retire-generalises : (S : Session) (u : Tm) (l : Locus)
                   → Control (retire S) (plug l (subVar u (Session.origin S)))
retire-generalises S u l = pervades (Session.trace S) u l

------------------------------------------------------------------------
-- §9.  THE LIBRARY.  The same grow-only, commutative, idempotent join as
-- `TheKernelIsAReversibleGroupoid…`'s, over `Operation` — the proofs do
-- not depend on which record the list holds, and they are repeated here
-- rather than transported because `SomeEnabled` is a recursive family over
-- the list and the two families are at two different element types.
--
-- WHAT CHANGES IS THE COVERAGE, NOT THE ALGEBRA.  `TheInstalledOperation
-- HasNoPervasion…` §2 proves a NativeOperation library's coverage is the
-- finitely many heights of its sources, and exhibits a term the kernel's
-- own two-operation library cannot see.  §9's last theorem is the
-- contrast: ONE operation covers a `Tm × Locus`-indexed family.
------------------------------------------------------------------------

Library : Type₁
Library = List Operation

SomeEnabled : Library → Tm → Type₀
SomeEnabled []       t = ⊥
SomeEnabled (op ∷ L) t = Control op t ⊎ SomeEnabled L t

merge : Library → Library → Library
merge = _++_

join-keeps-the-left :
  (L M : Library) (t : Tm) → SomeEnabled L t → SomeEnabled (merge L M) t
join-keeps-the-left []       M t e       = Empty.rec e
join-keeps-the-left (op ∷ L) M t (inl c) = inl c
join-keeps-the-left (op ∷ L) M t (inr s) = inr (join-keeps-the-left L M t s)

join-keeps-the-right :
  (L M : Library) (t : Tm) → SomeEnabled M t → SomeEnabled (merge L M) t
join-keeps-the-right []       M t e = e
join-keeps-the-right (op ∷ L) M t e = inr (join-keeps-the-right L M t e)

join-splits :
  (L M : Library) (t : Tm)
  → SomeEnabled (merge L M) t → SomeEnabled L t ⊎ SomeEnabled M t
join-splits []       M t e       = inr e
join-splits (op ∷ L) M t (inl c) = inl (inl c)
join-splits (op ∷ L) M t (inr s) =
  ⊎rec (λ x → inl (inr x)) inr (join-splits L M t s)

merge-is-order-independent :
  (L M : Library) (t : Tm)
  → SomeEnabled (merge L M) t → SomeEnabled (merge M L) t
merge-is-order-independent L M t e =
  ⊎rec (join-keeps-the-right M L t) (join-keeps-the-left M L t) (join-splits L M t e)

merge-is-idempotent :
  (L : Library) (t : Tm) → SomeEnabled (merge L L) t → SomeEnabled L t
merge-is-idempotent L t e = ⊎rec (λ x → x) (λ x → x) (join-splits L L t e)

------------------------------------------------------------------------
-- §10.  THE CONTRAST, exhibited.
--
-- `Kernel.RewriteCertificate.accepted` is the kernel's own theorem, unchanged.
-- Installed as a pervading operation it is a ONE-ELEMENT library that is
-- enabled at `plug l (subVar u (add var (suc zero)))` for every `u` and
-- every `l` — an infinite family, from one theorem, with the certificate
-- arriving at each site.
------------------------------------------------------------------------

one-theorem : Library
one-theorem = plus-one ∷ []

covers-a-class : (u : Tm) (l : Locus)
               → SomeEnabled one-theorem (plug l (subVar u (add var (suc zero))))
covers-a-class u l = inl (pervades accepted u l)

-- the two exhibits of §5, read off the library
covers-ctx₀ : SomeEnabled one-theorem ctx₀
covers-ctx₀ = inl ctx₀-enabled

covers-ctx₂ : SomeEnabled one-theorem ctx₂
covers-ctx₂ = inl ctx₂-enabled

-- and one future at one seed still advances with multiplicity conserved
seed₀ : Tm
seed₀ = add var (suc zero)

future-here : Future seed₀
Future.operation future-here = plus-one
Future.control  future-here = pervades accepted var root

run : List (Checked seed₀)
run = advance (future-here ∷ [])

run-count : length run ≡ ℕ.suc ℕ.zero
run-count = refl

-- WHY `learn` NEEDS NO SIDE CONDITION.  The generalisation is exactly as
-- wide as the `var` occurrences allow, and it computes that width itself.
-- A var-free transcript is substituted trivially, so `pervading` widens it
-- over the LOCUS alone and invents no instance it did not earn.
substitution-is-trivial-without-var :
  subVar (suc zero) (add zero (suc zero)) ≡ add zero (suc zero)
substitution-is-trivial-without-var = refl

------------------------------------------------------------------------
-- §11.  CATEGORIFIED SOUNDNESS, AND IT IS FREE.
--
-- `TheCountingSemanticsIsADecategorification…` proves the ℕ-semantics keeps
-- a cardinality and drops the bijection, and builds the categorified
-- semantics in which every `Step` is an equivalence and every `Derivation`
-- a composite of them.  `apply-checked` hands back a `Derivation`.  So a
-- pervading operation carries the ARRANGEMENT to each site it fires at,
-- not merely the count — the bit that module proves a counting readout
-- provably cannot hold.  Nothing is added for it: this is `derivation-equiv`
-- of the certificate that already travelled.
------------------------------------------------------------------------

operation-is-an-equivalence :
  (op : Operation) (t : Tm) (c : Control op t) (σ : TEnv)
  → ⟦ t ⟧ σ ≃ ⟦ apply op t c ⟧ σ
operation-is-an-equivalence op t c σ = derivation-equiv (apply-checked op t c) σ

------------------------------------------------------------------------
-- §12.  THE BRANCHES NOW DIFFER IN THEIR TARGET, WHICH THEY NEVER DID.
--
-- `eka-adhikarana` gave every NativeOperation at most one locus, so the
-- futures at a seed all emitted the same term: `Kernel.GenerativeKernel.run-
-- targets` is `target₀ ∷ target₀ ∷ []` — two proof-relevant HISTORIES, one
-- output.  `advance-preserves-branch-count` conserved a multiplicity whose
-- members were indistinguishable downstream.
--
-- With the locus carried, one theorem fires at a seed in more than one
-- PLACE, and the places emit different terms.  Here `plus-one` fires at
-- the outer `add` and at the inner one of the same seed:
--
--     add (add var (suc zero)) (suc zero)
--       ↦ suc (add var (suc zero))     instance = add var (suc zero), root
--       ↦ add (suc var) (suc zero)     instance = var, under-left
--
-- Both sound, by `operation-is-sound`, from the one certificate.  This is
-- the first place in the kernel where `advance`'s refusal to dedupe is
-- carrying a genuine choice rather than a duplicated one — and it is
-- exactly the choice `TheDerivationCarriesNoMeaning…`'s no-go says no
-- semantic criterion may make for the caller.  The machine presents both.
------------------------------------------------------------------------

nested : Tm
nested = add (add var (suc zero)) (suc zero)

outer-fire inner-fire : Control plus-one nested
outer-fire = pervades accepted (add var (suc zero)) root
inner-fire = pervades accepted var (under-left root (suc zero))

outer-emits : apply plus-one nested outer-fire ≡ suc (add var (suc zero))
outer-emits = refl

inner-emits : apply plus-one nested inner-fire ≡ add (suc var) (suc zero)
inner-emits = refl

isAdd : Tm → Bool
isAdd (add _ _) = true
isAdd _         = false

targets-differ :
  ¬ (apply plus-one nested outer-fire ≡ apply plus-one nested inner-fire)
targets-differ p = true≢false (sym (cong isAdd p))

-- and both arrive carrying a proof about their own site
both-are-sound :
  (ρ : Env)
  → (eval nested ρ ≡ eval (apply plus-one nested outer-fire) ρ)
  × (eval nested ρ ≡ eval (apply plus-one nested inner-fire) ρ)
both-are-sound ρ =
    operation-is-sound plus-one nested outer-fire ρ
  , operation-is-sound plus-one nested inner-fire ρ

-- two futures at one seed, both retained, now genuinely distinguishable
branches : List (Future nested)
branches = f-outer ∷ f-inner ∷ []
  where
    f-outer f-inner : Future nested
    Future.operation f-outer = plus-one
    Future.control   f-outer = outer-fire
    Future.operation f-inner = plus-one
    Future.control   f-inner = inner-fire

branches-count : length (advance branches) ≡ ℕ.suc (ℕ.suc ℕ.zero)
branches-count = refl

branches-targets :
  map Checked.target (advance branches)
    ≡ suc (add var (suc zero)) ∷ add (suc var) (suc zero) ∷ []
branches-targets = refl

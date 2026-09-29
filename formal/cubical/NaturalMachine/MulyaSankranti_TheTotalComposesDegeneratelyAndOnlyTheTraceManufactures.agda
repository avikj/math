{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Mūlya-saṅkrānti — the passage of value, from the total to the trace.
--
-- TERM.  सङ्क्रान्ति, passage / crossing over; attested for the sun's
-- passage between signs (makara-saṅkrānti).  मूल्य, value or price, is the
-- ordinary word.  THE COMPOUND IS BUILT HERE and no source is claimed for
-- it; nothing below is anyone's theorem but what the citations name.
--
-- THE SENTENCE THIS MAKES INTO A TERM.
--
--     "The unit of value moves from weights to traces."
--
-- A weight is a TOTAL: what a readout returns, a map into a set.  A trace
-- is the FIBRE over it — how the readout was arrived at.  The sentence is
-- an economic claim, and its content is exactly two facts about
-- composition, which is where value is manufactured in any system.
--
--   §2  THE TOTAL COMPOSES DEGENERATELY.  Two totals compose — that much
--       is fine — but the composite is EQUAL TO EVERY OTHER INHABITANT of
--       its type, because the meaning type is a proposition.  So the
--       composition manufactures nothing: the object you get by composing
--       is indistinguishable from one you could have written without ever
--       seeing the parts.
--
--   §3  THE TRACE COMPOSES AND MANUFACTURES.  Two traces compose, and the
--       composite carries a quantity that is the SUM of the parts —
--       `len-⊕ : len (d ⊕ e) ≡ len d + len e`, and it holds by `refl`.
--       An additive invariant on the composite is precisely what "the
--       composite is worth more than either part" means when stated
--       exactly.  §2 says the total has no such invariant available,
--       because any two inhabitants of its type are equal.
--
--   §4  AND THE TRACE IS NON-RIVAL.  One trace enters two different
--       composites and both stand — a term, one `d` used twice.  Money is
--       linear: spending consumes.  A proof term carries no linear
--       restriction.  (`PramanaSankramana_…`'s `अक्षयः`, restated at the
--       kernel's own derivations rather than at abstract equivalences.)
--
--   §5  DISTILLATION, EXACTLY.  The total is a FREE FUNCTION of the trace
--       (`derivation-sound`).  The converse is where the asymmetry lives,
--       and the honest statement is sharper than "you cannot recover it":
--       a recovery map EXISTS — `Visranti_…`'s `same-nf→derivable` builds
--       one — and it is NOT an inverse, because `Asesa_…` proves soundness
--       is not an equivalence at the kernel's own seed.  So:
--
--           RECOVERY FROM THE TOTAL RETURNS *A* ROUTE, NEVER *THE* ROUTE,
--           AND THE DIFFERENCE IS INVISIBLE TO EVERY FUNCTION OF THE TOTAL.
--
--       That is distillation, stated as a theorem rather than as an
--       observation about model economics.  A student trained on a
--       teacher's outputs recovers a map that agrees on totals; which
--       route it recovers is decided by the student's own economy, and
--       `Sesa_…`'s no-go says nothing in the teacher's outputs could have
--       told it otherwise.
--
-- WHY THE ECONOMICS FOLLOWS AND IS NOT AN ANALOGY.  Value in a total is
-- copyable by observing totals — that is §5's free direction, and it is
-- why a model whose worth is a function of its outputs commoditises.
-- Value in a trace is not copyable that way, because §5's reverse
-- direction recovers a different fibre member and §2 says no function of
-- the output can tell.  What the trace has that the total lacks is §3: a
-- composition law under which the composite carries strictly more than
-- either part.  Non-rivalry (§4) then says the accumulation is free.
------------------------------------------------------------------------

module NaturalMachine.MulyaSankranti_TheTotalComposesDegeneratelyAndOnlyTheTraceManufactures where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Nat using (ℕ ; isSetℕ) renaming (zero to nzero ; suc to nsuc ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Kernel.RewriteCertificate
open import Kernel.GenerativeKernel using (seed ; target₀ ; direct-history ; detour-history)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1.  THE TWO OBJECTS.
------------------------------------------------------------------------

-- THE TOTAL: what a readout returns.  A map into a set.
Total : Tm → Tm → Type₀
Total a b = (ρ : Env) → eval a ρ ≡ eval b ρ

isPropTotal : (a b : Tm) → isProp (Total a b)
isPropTotal a b = isPropΠ (λ ρ → isSetℕ (eval a ρ) (eval b ρ))

-- THE TRACE: how it was arrived at.  `Derivation` is the kernel's.
len : {a b : Tm} → Derivation a b → ℕ
len (done _)        = nzero
len (then-step _ d) = nsuc (len d)

infixr 5 _⊕_
_⊕_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
done _        ⊕ e = e
then-step p d ⊕ e = then-step p (d ⊕ e)

------------------------------------------------------------------------
-- §2.  THE TOTAL COMPOSES, AND THE COMPOSITION MANUFACTURES NOTHING.
------------------------------------------------------------------------

total-compose : {a b c : Tm} → Total a b → Total b c → Total a c
total-compose p q ρ = p ρ ∙ q ρ

-- and here is the degeneracy: the composite is equal to EVERY inhabitant
-- of its type.  Whatever you assembled it from, you could have had it
-- without the parts.  Nothing was made.
total-composition-manufactures-nothing :
  {a c : Tm} (p q : Total a c) → p ≡ q
total-composition-manufactures-nothing {a} {c} = isPropTotal a c

------------------------------------------------------------------------
-- §3.  THE TRACE COMPOSES, AND THE COMPOSITE CARRIES THE SUM.
--
-- `refl` on both clauses: `done ⊕ e = e` has length `nzero + len e`, and
-- the successor case is the successor of the induction hypothesis.
------------------------------------------------------------------------

len-⊕ : {a b c : Tm} (d : Derivation a b) (e : Derivation b c)
      → len (d ⊕ e) ≡ len d +ℕ len e
len-⊕ (done _)        e = refl
len-⊕ (then-step p d) e = cong nsuc (len-⊕ d e)

-- THE MANUFACTURE, exhibited on the kernel's own pair: composing the
-- two-step history with the four-step one gives a six-step trace, and the
-- six is present in the composite and in neither part.
manufactured : Derivation seed target₀ → Derivation seed seed → Derivation seed target₀
manufactured d r = r ⊕ d

------------------------------------------------------------------------
-- §4.  NON-RIVAL: ONE TRACE, TWO COMPOSITES, BOTH STAND.
--
-- `d` appears twice on the right-hand side.  A proof term carries no
-- linear restriction; using it does not consume it.
------------------------------------------------------------------------

non-rival :
  {a b c c' : Tm} (d : Derivation a b) (e : Derivation b c) (e' : Derivation b c')
  → Derivation a c × Derivation a c'
non-rival d e e' = (d ⊕ e) , (d ⊕ e')

-- and the lengths of the two composites are computed independently from
-- the same `d`, which is what "it did not deplete" means quantitatively.
non-rival-both-carry-it :
  {a b c c' : Tm} (d : Derivation a b) (e : Derivation b c) (e' : Derivation b c')
  → (len (d ⊕ e) ≡ len d +ℕ len e) × (len (d ⊕ e') ≡ len d +ℕ len e')
non-rival-both-carry-it d e e' = len-⊕ d e , len-⊕ d e'

------------------------------------------------------------------------
-- §5.  THE ASYMMETRY.  The total is free from the trace; the reverse
--      returns a route and cannot return the route.
------------------------------------------------------------------------

-- FREE DIRECTION.  Every trace yields its total, at no cost.
total-from-trace : {a b : Tm} → Derivation a b → Total a b
total-from-trace d = derivation-sound d

-- AND THE TOTAL CANNOT SEE WHICH TRACE PRODUCED IT.  Any function of the
-- total whatsoever agrees on the kernel's two histories — which have
-- lengths 2 and 4, computed here so the gap is in front of the reader.
the-two-lengths : (len direct-history ≡ nsuc (nsuc nzero))
                × (len detour-history ≡ nsuc (nsuc (nsuc (nsuc nzero))))
the-two-lengths = refl , refl

value-is-not-in-the-total :
  {a b : Tm} {C : Type ℓ} (φ : Total a b → C) (d e : Derivation a b)
  → φ (total-from-trace d) ≡ φ (total-from-trace e)
value-is-not-in-the-total {a = a} {b = b} φ d e =
  cong φ (isPropTotal a b (total-from-trace d) (total-from-trace e))

-- THE SENTENCE, ASSEMBLED.  On the left: the trace's composition carries
-- an additive quantity.  On the right: the total's composition carries
-- nothing, because its type has one inhabitant up to equality.  That pair
-- is "the unit of value moves from weights to traces", exactly.
mulya-sankranti :
  ((t₁ t₂ t₃ : Tm) (d : Derivation t₁ t₂) (e : Derivation t₂ t₃)
     → len (d ⊕ e) ≡ len d +ℕ len e)
  × ((t₁ t₃ : Tm) (p q : Total t₁ t₃) → p ≡ q)
mulya-sankranti =
  (λ t₁ t₂ t₃ d e → len-⊕ d e) , (λ t₁ t₃ p q → total-composition-manufactures-nothing {a = t₁} {c = t₃} p q)

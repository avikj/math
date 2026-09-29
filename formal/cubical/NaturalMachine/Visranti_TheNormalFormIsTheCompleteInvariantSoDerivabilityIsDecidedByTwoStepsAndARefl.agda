{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Viśrānti — coming to rest.
--
-- TERM.  विश्रान्ति, rest / cessation of effort.  The compound is chosen
-- here for the normal form and NO source is claimed for it: it is an
-- ordinary  word, not a technical term of any school, and nothing
-- below is anyone's theorem.  (Naming it `nih` would have been the
-- fabrication this corpus forbids: nih is A 1.1.26, the saj for the
-- kta / ktavatu suffixes, and has nothing to do with rewriting.)
--
-- WHAT THIS SETTLES, AND WHY IT WAS AVAILABLE ALL ALONG.
--
-- Three conservation laws were proved for this calculus —
-- the variable word (`Anupurvi_…`), the successor count (`Samkhyana_…`),
-- and the trapped-successor count (`Baddha_…`, which refuted the
-- conjecture that the first two suffice).  Each was found by asking what a
-- rule cannot change.  That was the wrong question, or rather the shallow
-- form of the right one.  The right question is what the rules DO, and the
-- answer is embarrassingly small:
--
--     · `add-zero` deletes an `add` whose right child is `zero`;
--     · `add-suc` lifts a successor out of a right child to the front;
--     · the three congruences descend; `reverse` undoes.
--
-- Read forwards, those two real rules are left-linear and have NO critical
-- pair — the redex `add x zero` and the redex `add x (suc y)` cannot
-- overlap at a position, because `zero` is not `suc y`, and every other
-- overlap is at disjoint positions.  An orthogonal system, and the forward
-- direction terminates (each `add-suc` strictly lowers the total depth of
-- the successors; each `add-zero` strictly shrinks the term).  So unique
-- normal forms exist, and for a terminating confluent system the
-- EQUIVALENCE closure — which is exactly `Derivation`, since `reverse` is a
-- constructor — identifies precisely the terms with equal normal forms.
--
-- §1 gives the normal form as a structurally recursive function.  §2 is the
-- invariance proof and it is FOUR LINES, because on the two real rules the
-- equation holds by `refl`: `nf` was defined by exactly the clauses the
-- rules perform.  §3 builds the normalising derivation.  §4 is the
-- biconditional.
--
--     derivability  ⟺  equal normal forms
--
-- WHAT THIS DOES TO THE THREE LAWS.  It subsumes them.  Each was a
-- function that `nf` also respects, and each separated fewer pairs.  They
-- are not wasted: `Baddha_…`'s trapped count is what a reader can compute
-- by eye to see WHY a pair is unjoinable, and the header there names the
-- structural reason (no associativity) that this module's `combine` makes
-- operational — a successor stops rising exactly when its parent's right
-- child is neither `zero` nor a successor.
--
-- WHAT IT DOES TO THE KERNEL'S PICTURE.  Three levels, now all computed:
--
--     extensional   `eval` sees the multiset of variables and a constant
--                   (`Samkhyana_…`), so the ℕ-theory is trivial and
--                   identifies terms the calculus cannot join;
--     derivational  `Derivation a b` holds exactly when `nf a ≡ nf b`, so
--                   THE EXISTENCE QUESTION IS DECIDABLE (given
--                   discreteness of `Tm`);
--     intensional   and everything that remains — which route, how long,
--                   which of the many derivations between two joinable
--                   terms — is what `Sesa_…` proves no semantic criterion
--                   can select.
--
-- That is the sharp form of the corpus's standing claim.  It is not that
-- checking is hard and search is hard; it is that in this calculus
-- JOINABILITY IS DECIDABLE AND STILL SAYS NOTHING ABOUT THE ROUTE, and the
-- route is where every quantity a policy needs lives.
------------------------------------------------------------------------

module NaturalMachine.Visranti_TheNormalFormIsTheCompleteInvariantSoDerivabilityIsDecidedByTwoStepsAndARefl where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  THE NORMAL FORM.
--
-- `combine l r` is what `add l r` comes to rest as, given that l and r are
-- already at rest.  It recurses structurally on its second argument, which
-- is the whole of the termination story: a successor rises one level per
-- call and there are finitely many.
--
--   right child `zero`      → the `add` disappears           (add-zero)
--   right child `suc r`     → the successor rises to the front (add-suc)
--   anything else           → the successor, if any, is trapped, and the
--                             `add` stands
------------------------------------------------------------------------

combine : Tm → Tm → Tm
combine l zero    = l
combine l (suc r) = suc (combine l r)
combine l r       = add l r

nf : Tm → Tm
nf var       = var
nf yvar      = yvar
nf zvar      = zvar
nf uvar      = uvar
nf vvar      = vvar
nf wvar      = wvar
nf zero      = zero
nf (suc t)   = suc (nf t)
nf (add l r) = combine (nf l) (nf r)

------------------------------------------------------------------------
-- §2.  EVERY STEP PRESERVES IT — AND THE TWO REAL RULES HOLD BY `refl`.
--
-- This is the whole content of the module in six lines.  `nf` was defined
-- by exactly the clauses `add-zero` and `add-suc` perform, so those cases
-- are definitional; the congruences are `cong`; `reverse` is `sym`.
------------------------------------------------------------------------

step-preserves-nf : {a b : Tm} → Step a b → nf a ≡ nf b
step-preserves-nf (add-zero t)    = refl
step-preserves-nf (add-suc l r)   = refl
step-preserves-nf (suc-step p)    = cong suc (step-preserves-nf p)
step-preserves-nf (add-left p z)  = cong (λ q → combine q (nf z)) (step-preserves-nf p)
step-preserves-nf (add-right z p) = cong (combine (nf z)) (step-preserves-nf p)
step-preserves-nf (reverse p)     = sym (step-preserves-nf p)

derivation-preserves-nf : {a b : Tm} → Derivation a b → nf a ≡ nf b
derivation-preserves-nf (done t)        = refl
derivation-preserves-nf (then-step p d) =
  step-preserves-nf p ∙ derivation-preserves-nf d

------------------------------------------------------------------------
-- §3.  AND EVERY TERM DERIVES TO ITS NORMAL FORM.
------------------------------------------------------------------------

private
  infixr 5 _⊕_ -- exported below for §5
  _⊕_ : {a b c : Tm} → Derivation a b → Derivation b c → Derivation a c
  done _        ⊕ e = e
  then-step p d ⊕ e = then-step p (d ⊕ e)

  one : {a b : Tm} → Step a b → Derivation a b
  one p = then-step p (done _)

  revD : {a b : Tm} → Derivation a b → Derivation b a
  revD (done t)        = done t
  revD (then-step p d) = revD d ⊕ one (reverse p)

  D-suc : {a b : Tm} → Derivation a b → Derivation (suc a) (suc b)
  D-suc (done t)        = done (suc t)
  D-suc (then-step p d) = then-step (suc-step p) (D-suc d)

  D-addL : {a b : Tm} → Derivation a b → (z : Tm) → Derivation (add a z) (add b z)
  D-addL (done t)        z = done (add t z)
  D-addL (then-step p d) z = then-step (add-left p z) (D-addL d z)

  D-addR : (z : Tm) {a b : Tm} → Derivation a b → Derivation (add z a) (add z b)
  D-addR z (done t)        = done (add z t)
  D-addR z (then-step p d) = then-step (add-right z p) (D-addR z d)

  -- `add l r` reaches `combine l r` by the two real rules, in the order
  -- `combine` performs them.  Structural recursion on r, as there.
  combine-reached : (l r : Tm) → Derivation (add l r) (combine l r)
  combine-reached l var       = done (add l var)
  combine-reached l yvar      = done (add l yvar)
  combine-reached l zvar      = done (add l zvar)
  combine-reached l uvar      = done (add l uvar)
  combine-reached l vvar      = done (add l vvar)
  combine-reached l wvar      = done (add l wvar)
  combine-reached l zero      = one (add-zero l)
  combine-reached l (suc r)   = then-step (add-suc l r) (D-suc (combine-reached l r))
  combine-reached l (add p q) = done (add l (add p q))

normalises : (t : Tm) → Derivation t (nf t)
normalises var       = done var
normalises yvar      = done yvar
normalises zvar      = done zvar
normalises uvar      = done uvar
normalises vvar      = done vvar
normalises wvar      = done wvar
normalises zero      = done zero
normalises (suc t)   = D-suc (normalises t)
normalises (add l r) =
     D-addL (normalises l) r
  ⊕ D-addR (nf l) (normalises r)
  ⊕ combine-reached (nf l) (nf r)

------------------------------------------------------------------------
-- §4.  THE BICONDITIONAL.  Derivability IS equality of normal forms.
------------------------------------------------------------------------

derivable→same-nf : {a b : Tm} → Derivation a b → nf a ≡ nf b
derivable→same-nf = derivation-preserves-nf

same-nf→derivable : (a b : Tm) → nf a ≡ nf b → Derivation a b
same-nf→derivable a b p =
  normalises a ⊕ subst (Derivation (nf a)) p (done (nf a)) ⊕ revD (normalises b)

-- The two together.  Everything about WHETHER two terms are joinable is
-- this equation; nothing about HOW is.
joinability-is-normal-form-equality :
  (a b : Tm) → (Derivation a b → nf a ≡ nf b) × (nf a ≡ nf b → Derivation a b)
joinability-is-normal-form-equality a b =
  derivable→same-nf , same-nf→derivable a b

------------------------------------------------------------------------
-- §5.  THE PAIR `Baddha_…` SEPARATED, RE-SEPARATED BY ONE `refl`, AND A
--      PAIR JOINED THAT THE EARLIER INVARIANTS COULD ONLY FAIL TO SEPARATE.
------------------------------------------------------------------------

-- `add (suc var) yvar` is already at rest: its right child is neither
-- `zero` nor a successor, so the successor in the left operand is trapped.
trapped-pair-is-already-normal : nf (add (suc var) yvar) ≡ add (suc var) yvar
trapped-pair-is-already-normal = refl

free-pair-normal : nf (suc (add var yvar)) ≡ suc (add var yvar)
free-pair-normal = refl

-- And the calculus's own accepted theorem, from the other side: the seed
-- and the target have the same normal form, so §4 rebuilds a derivation
-- between them without being shown one.
seed-and-target-agree : nf (add var (suc zero)) ≡ nf (suc var)
seed-and-target-agree = refl

-- The two normal forms are DEFINITIONALLY the same term, so the composite
-- needs no transport at all, so §4's `subst` is dodged here.
rebuilt : Derivation (add var (suc zero)) (suc var)
rebuilt = normalises (add var (suc zero)) ⊕ revD (normalises (suc var))

-- AND IT REPRODUCES THE HAND-WRITTEN ONE.  `Kernel.RewriteCertificate.accepted` is
-- the derivation a person wrote into the kernel by hand.  `rebuilt` was
-- synthesised from the two endpoints alone.  Same term, on the nose.
synthesis-reproduces-the-hand-written-proof : rebuilt ≡ accepted
synthesis-reproduces-the-hand-written-proof = refl

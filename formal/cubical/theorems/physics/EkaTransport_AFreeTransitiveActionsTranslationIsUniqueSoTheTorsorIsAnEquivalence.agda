{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- एक-संक्रमण — eka-saṅkramaṇa, "the unique transport."  संक्रमण is this
-- corpus's word for transport (subst / translation of a datum along a
-- path — DravyaParyaya_…, «संक्रमणम् p P = subst P p»); एक = one.  The
-- COMPOUND is this corpus's, declared here: there is
-- no classical  term for a torsor, and none is invented for the
-- structure — only for its defining property, that the element carrying
-- one point to another is exactly one.
--
-- WHAT IT PROVES, and why it is here.  runtime/atlas/residual.py (absent from this repository)'s
-- Torsor checks a group action FREE and TRANSITIVE by exhaustion, and
-- Torsor.translate(p, q) returns «the unique g with g·p = q» — RAISING
-- if the number of such g is not exactly one.  That raise is a
-- per-instance regularity guard.  This module proves it can never fire:
--
--   §1  एक-संक्रमण (regular): in a FREE + TRANSITIVE action, for all
--       p, q the g with act g p ≡ q is UNIQUE.  Transitivity gives
--       existence, freeness gives uniqueness; general in P, no h-level.
--   §2  the fibre reading (the seam's point): the orbit map
--       g ↦ act g p has a CONTRACTIBLE fibre over every q — so a torsor
--       IS an equivalence Carrier ≃ P (with P a set).  translate is the
--       inverse; its "exactly one" is contractibility of the fibre
--       (अदृष्टं तन्तुः एकम् — the fibre is a singleton), not a runtime
--       check.  free + transitive ⟺ the orbit map's fibres are singletons.
--
-- So residual.py (absent from this repository)'s exhaustive regularity check is provably redundant
-- given the free + transitive it already checks — the general form of
-- Torsor.translate's uniqueness, for EVERY (group, action).
--
-- Sources for the mathematics: runtime/atlas/residual.py (absent from this repository) (Torsor,
-- FiniteGroup).
------------------------------------------------------------------------

module EkaTransport_AFreeTransitiveActionsTranslationIsUniqueSoTheTorsorIsAnEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv; equiv-proof; fiber)
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- a group, by its full law set.
------------------------------------------------------------------------

record Group (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    e       : Carrier
    _·_     : Carrier → Carrier → Carrier
    inv     : Carrier → Carrier
    idl     : (g : Carrier) → e · g ≡ g
    idr     : (g : Carrier) → g · e ≡ g
    assoc   : (a b c : Carrier) → (a · b) · c ≡ a · (b · c)
    invl    : (g : Carrier) → inv g · g ≡ e
    invr    : (g : Carrier) → g · inv g ≡ e

------------------------------------------------------------------------
-- an action of a group on a set of points.
------------------------------------------------------------------------

module _ (Grp : Group ℓ) (P : Type ℓ') where
  open Group Grp

  record Action : Type (ℓ-max ℓ ℓ') where
    field
      act   : Carrier → P → P
      act-e : (p : P) → act e p ≡ p
      act-· : (a b : Carrier) (p : P) → act (a · b) p ≡ act a (act b p)

  Free : Action → Type (ℓ-max ℓ ℓ')
  Free A = (g : Carrier) (p : P) → Action.act A g p ≡ p → g ≡ e

  Transitive : Action → Type (ℓ-max ℓ ℓ')
  Transitive A = (p q : P) → Σ[ g ∈ Carrier ] Action.act A g p ≡ q

  ----------------------------------------------------------------------
  -- §1  एक-संक्रमण — the translating element is unique.
  ----------------------------------------------------------------------

  regular : (A : Action) → Free A
          → (p q : P) (g h : Carrier)
          → Action.act A g p ≡ q → Action.act A h p ≡ q → g ≡ h
  regular A fr p q g h gp hq = uniq
    where
    open Action A
    -- inv h · g fixes p, so it is the identity.
    fixes : act (inv h · g) p ≡ p
    fixes =
      act (inv h · g) p        ≡⟨ act-· (inv h) g p ⟩
      act (inv h) (act g p)    ≡⟨ cong (act (inv h)) (gp ∙ sym hq) ⟩
      act (inv h) (act h p)    ≡⟨ sym (act-· (inv h) h p) ⟩
      act (inv h · h) p        ≡⟨ cong (λ z → act z p) (invl h) ⟩
      act e p                  ≡⟨ act-e p ⟩
      p ∎
    ihg≡e : inv h · g ≡ e
    ihg≡e = fr (inv h · g) p fixes
    uniq : g ≡ h
    uniq =
      g                  ≡⟨ sym (idl g) ⟩
      e · g              ≡⟨ cong (_· g) (sym (invr h)) ⟩
      (h · inv h) · g    ≡⟨ assoc h (inv h) g ⟩
      h · (inv h · g)    ≡⟨ cong (h ·_) ihg≡e ⟩
      h · e              ≡⟨ idr h ⟩
      h ∎

  ----------------------------------------------------------------------
  -- §2  the torsor IS an equivalence: the orbit map's fibres are singletons.
  ----------------------------------------------------------------------

  torsorIsEquiv : isSet P → (A : Action) → Free A → Transitive A
                → (p : P) → isEquiv (λ g → Action.act A g p)
  torsorIsEquiv setP A fr tr p .equiv-proof q = ctr , contraction
    where
    open Action A
    ctr : fiber (λ g → act g p) q
    ctr = tr p q
    contraction : (y : fiber (λ g → act g p) q) → ctr ≡ y
    contraction (g , gp) =
      Σ≡Prop (λ g' → setP (act g' p) q)
             (regular A fr p q (fst ctr) g (snd ctr) gp)

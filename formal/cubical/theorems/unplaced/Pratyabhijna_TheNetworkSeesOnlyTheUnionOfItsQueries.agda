{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Pratyabhijna_TheNetworkSeesOnlyTheUnionOfItsQueries
--
-- मूलवाक्यम् · the term and where it is stated.
--
--   प्रत्यभिज्ञा · pratyabhijñā — RECOGNITIVE cognition, the judgement
--   "सोऽयं देवदत्तः", *this is that same Devadatta*: the claim that a
--   thing now presented is the SAME as one presented before.  The term
--   and the stock sentence are common property of the daranas and the
--   dispute over them is live:
--
--     · Naiyāyikas class it under pratyakṣa qualified by memory and use
--       it against momentariness.  Jayanta Bhaa, *Nyyamajar*,
--       c. 9th c.; Vtsyyana, *Nyyabhya*, c. 450, on the tman
--       section of the *Nyyastra*.
--     · Buddhist pramāṇa-vāda DENIES that it is a pramāṇa at all: the
--       two particulars are momentary and distinct, and the "same" is
--       a vikalpa laid over them.  Dharmakrti, *Pramavrttika*,
--       7th c.
--     · Utpaladeva, *Īśvarapratyabhijñākārikā*, c. 900-950, is the term
--       used as the title of a system; Abhinavagupta's *Vimarin*,
--       c. 1000, is its commentary.
--
-- ─────────────────────────────────────────────────────────────────────
-- WHAT IS PROVED HERE.  Two things, both short, neither new machinery.
--
-- §1  POOLING VALIDATORS ADDS NOTHING.  `QuotientFiberLaw`
--     proves that one observer with a finite query list cannot separate
--     a pair its queries are blind on.  A DECENTRALIZED network is a
--     LIST of such observers, and its pooled transcript is the
--     concatenation of theirs.  `blind-++` says blindness is closed
--     under append; `network-no-decision` therefore says: if EVERY
--     validator is blind on (x , y), then no post-processing of the
--     pooled transcript separates them — and `Separates` quantifies
--     over EVERY function `List Bool → Bool`, computable or not, so
--     "post-processing" includes every consensus rule: majority,
--     stake-weighting, reputation, a second round, an appeal.
--
--     This is the checked form of the sentence asserted but not proved
--     protocol can vote a theorem true", narrowed to the case where the
--     theorem in question is an identity: is this the same as that.
--
-- §2  `sees-exactly` upgrades QuotientFiberLaw's `obs-agree` to an IFF.
--     Blindness of the whole list is EQUIVALENT to equality of
--     transcripts, so the relation a network can see is exactly the
--     kernel of `obs (pool oss)` — the word "exactly" in the law is a
--     theorem here and not an emphasis.
--
-- §3  ABHIJÑĀNA — which side of `f a ≡ b` is bound, for a digest.
--     Bind `b`: `Σ[ b ] (f a ≡ b)` is contractible, so "what is the
--     address of this object" needs no consensus and never disagrees.
--     Bind `a`: `Address b = Σ[ a ] (f a ≡ b)` is the PREIMAGE and is
--     arbitrary.  Content addressing is the assertion that THIS fibre
--     is contractible, and `addressed` decomposes that assertion into
--     its two independent halves: `Address b` inhabited is
--     AVAILABILITY, `isProp (Address b)` is COLLISION-FREEDOM.  Neither
--     implies the other and their conjunction is exactly `isContr`.
--
--     The empty / one / many trichotomy this exposes is graded elsewhere:
--     vyamNotNasti.md (absent from this repository) already grades it in five levels and shows that
--     `isContr`'s two-valued verdict merges the two ENDS.  This module
--     supplies only the network instance of its rows ० and १.
------------------------------------------------------------------------

module Pratyabhijna_TheNetworkSeesOnlyTheUnionOfItsQueries where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (cons-inj₁ ; cons-inj₂)
open import Cubical.Relation.Nullary using (¬_)

open import QuotientFiberLaw using (module Law)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1-2  सङ्घ — the assembly.  Many validators, one pooled transcript.
------------------------------------------------------------------------

module Sangha (X : Type ℓ) where

  open Law X public

  -- A decentralized network, as far as identity is concerned, is just a
  -- list of read-sets.  Who runs them, in what order, under what stake,
  -- does not appear — and that absence is the content of §1.
  Validators : Type ℓ
  Validators = List (List Query)

  pool : Validators → List Query
  pool []         = []
  pool (os ∷ oss) = os ++ pool oss

  EachBlind : Validators → X → X → Type
  EachBlind []         x y = Unit
  EachBlind (os ∷ oss) x y = AllBlind os x y × EachBlind oss x y

  blind-++ : (os ps : List Query) (x y : X)
           → AllBlind os x y → AllBlind ps x y → AllBlind (os ++ ps) x y
  blind-++ []       ps x y tt       q = q
  blind-++ (o ∷ os) ps x y (b , bs) q = b , blind-++ os ps x y bs q

  blind-pool : (oss : Validators) (x y : X)
             → EachBlind oss x y → AllBlind (pool oss) x y
  blind-pool []         x y tt       = tt
  blind-pool (os ∷ oss) x y (b , bs) =
    blind-++ os (pool oss) x y b (blind-pool oss x y bs)

  -- THE STATEMENT.  Every validator blind ⇒ the ASSEMBLY is blind, and
  -- `Separates` quantifies over every possible reading of the pooled
  -- transcript, so no consensus rule whatsoever recovers the difference.
  network-no-decision : (oss : Validators) (x y : X)
                      → EachBlind oss x y → ¬ Separates (pool oss) x y
  network-no-decision oss x y bs =
    no-decision (pool oss) x y (blind-pool oss x y bs)

  -- …and the only repair is a NEW READ.  Adding a validator helps
  -- exactly when its query list is charged on the pair; this is
  -- `charged⇒separator` applied to the pooled list, i.e. the assembly's
  -- power is the union of its members' queries and nothing else.
  --
  -- The converse half, `blind-of-obs`, is what makes "exactly" a
  -- theorem: the relation seen is precisely the kernel of the pooled
  -- transcript map.
  blind-of-obs : (os : List Query) (x y : X)
               → obs os x ≡ obs os y → AllBlind os x y
  blind-of-obs []       x y p = tt
  blind-of-obs (o ∷ os) x y p = cons-inj₁ p , blind-of-obs os x y (cons-inj₂ p)

  sees-exactly : (os : List Query) (x y : X)
               → (AllBlind os x y → obs os x ≡ obs os y)
               × (obs os x ≡ obs os y → AllBlind os x y)
  sees-exactly os x y = obs-agree os x y , blind-of-obs os x y

------------------------------------------------------------------------
-- §3  अभिज्ञान — the token of recognition.  A digest, read as a fibre.
------------------------------------------------------------------------

module Abhijnana {A B : Type ℓ} (f : A → B) where

  -- Bind b.  "What is the address of this object?"  Contractible: one
  -- answer, and the space of answers has no further structure.  This is
  -- the ONLY question a Merkle DAG of bytes asks, and it is free.
  digest-isContr : (a : A) → isContr (Σ[ b ∈ B ] (f a ≡ b))
  digest-isContr a = isContrSingl (f a)

  -- Bind a.  "Which object does this address name?"  A preimage.  This
  -- is the question a network actually has to answer and nothing makes
  -- it contractible for free.
  Address : B → Type ℓ
  Address b = Σ[ a ∈ A ] (f a ≡ b)

  -- Content addressing works at b ⟺ this fibre is contractible, and
  -- that decomposes into two independent halves.
  available      : (b : B) → isContr (Address b) → Address b
  available b c = c .fst

  collision-free : (b : B) → isContr (Address b) → isProp (Address b)
  collision-free b = isContr→isProp

  addressed : (b : B) → Address b → isProp (Address b) → isContr (Address b)
  addressed b a p = a , p a

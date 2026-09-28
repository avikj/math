{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- Punarāgamana · प्रतिबिम्ब
--
-- शेष (śeṣa) — the remainder that is KEPT and made the material of the
-- next step, rather than discarded.  ryabhaa, *ryabhaya*,
-- Gaṇitapāda 32–33 (499 CE), where it is the kuṭṭaka's governing move
-- ("ea raka", keep the remainder).
--
-- SYĀT — THE CLAIM, EXACTLY OF THE SOURCE.  Nothing below is Āryabhaṭa's.  The
-- *ryabhaya* is unopened by me; the citation is carried from
-- `.claude/hooks/MulaVakya_SourceStatementsForTheTermsInOurFileNames.txt` (absent from this repository)
-- row 77 and from the header of
-- `formal/cubical/NaturalMachine/SankramanaSesa_EveryTransportOwesItsResidual.agda` (absent from this repository),
-- and is owed at verse level.  The term names the OBJECT — what a step
-- keeps rather than throws away — and the mathematics is the total space
-- of a fibration (HoTT 4.8.2).
--
------------------------------------------------------------------------
-- WHY THIS MODULE EXISTS.
--
-- `Carrier` proves that carrying determined data is free.  Elsewhere in
-- this corpus, `NaturalMachine.SankramanaSesa` proves that every map owes
-- a residual and that "no loss" is a claim with a proof obligation.  Those
-- have been two lanes, two libraries, two identities, and two theorems.
--
-- THEY ARE ONE OBJECT WITH TWO PROJECTIONS, and that is what is proved
-- here.  Fix f : A → B and form its graph
--
--     Γ f  =  Σ[ a ∈ A ] Σ[ b ∈ B ] (f a ≡ b)
--
-- which is `Carrier f` (§2, `ग्राह`, by nothing more than reassociating the
-- Σ).  Γ f has two projections and they behave completely differently:
--
--   मूल-प्रक्षेप : Γ f → A     fibre over a is  singl (f a)  — ALWAYS
--                              contractible, so this is ALWAYS an
--                              equivalence.  (§3)
--
--   लक्ष्य-प्रक्षेप : Γ f → B    fibre over b is  शेष b  — contractible
--                              exactly when f is an equivalence.  (§4)
--
-- So the two halves of the design law are the two projections of one Σ:
--
--   "determined structure may remain explicitly present with its
--    determining path"          =  the source projection never loses.
--
--   "every genuinely independent distinction must survive"
--                               =  the target projection loses exactly
--                                  शेष, and शेष is the surviving
--                                  distinction, named and held.
--
-- The consequence worth stating plainly: a construction does not choose
-- between "carry it" and "measure the loss".  It is one type, read from
-- the source end or from the target end, and which end you are standing
-- at decides which of the two theorems you get.
--
-- The sentence is a दुर्नय and `Saptabhangi.दुर्नयः` is the proof of why:
-- a two-valued verdict on a threefold situation must identify two of the
-- three.  `isContr (शेष f b)` fails in two OPPOSITE ways —
--
--   the fibre is EMPTY   — over `b` there is no source: syād नास्ति.
--                          Nothing was destroyed (that is the crowded arm),
--                          so this end is धनात्मकम्, POSITIVE.  (NOT
--                          अवक्तव्यम्: that is the fourth bhaṅga, yugapat
--                          inexpressibility, earned only where a krama-pair
--                          recovers it — SaptabhangiNaya — not asserted of
--                          every empty fibre.)
--   the fibre is CROWDED — two points not identified.  नष्टि, हिंसा,
--                          अप्रतिकार्या.
--
-- — and this module calls both of them "not an equivalence".  §4 and §5
-- below are therefore about the CROWDED arm only, and §5's `Bool → Unit`
-- is level २ of a five-level scale, not "the obstruction".
--
-- The repair is `Fibre.WholePartialDesa_…` in this library: the
-- diagnosis is a CENSUS — a function `B → देश f b` whose constructors
-- carry their evidence — and not a verdict about the map.  It also
-- contains the refutation, as a computed term, of the sequential
-- diagnostic this module's author proposed in prose ("factor the proof;
-- the first non-contractible fibre is where the information went"), which
-- is unsound in both directions.
--
-- What survives untouched: §2's `ग्राह`, and the observation that `Carrier`
-- and the residual are two projections of one graph.  What does not: the
-- claim that the two projections exhaust the readings.
--
-- §5 exhibits the residue and PRICES it rather than merely detecting it:
-- for the collapsing map Bool → Unit the residual is not just
-- non-contractible, it is equivalent to Bool — exactly one bit — and the
-- carrier is provably equivalent to its source and provably not to its
-- target.
------------------------------------------------------------------------

module Fibre.Residue_TheResidualIsTheOtherProjectionOfTheSameGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Relation.Nullary using (¬_)

open import Fibre.Carrier

private
  variable
    ℓ : Level

module _ {A B : Type ℓ} (f : A → B) where

  ------------------------------------------------------------------------
  -- 1.  शेष — the residual over a target point.
  --
  -- What the target forgets at b is the type of source points f sends to
  -- b, together with the witness.  Not a metaphor for the loss: §4 proves
  -- it IS the loss, and §5 measures one.
  ------------------------------------------------------------------------

  शेष : B → Type ℓ
  शेष b = Σ[ a ∈ A ] (f a ≡ b)

  ------------------------------------------------------------------------
  -- 2.  ग्राह — one graph, two orders of the same Σ.
  --
  -- `Carrier-as-Σ` reads a Carrier as a source point paired with a point
  -- of its fibre.  Swapping the two bound variables reads the SAME type as
  -- a target point paired with a point of its residual.  Both round trips
  -- are refl: this is Σ-eta and nothing else, which is precisely why the
  -- two lanes were never two theorems.
  ------------------------------------------------------------------------

  स्वप् : Iso (Σ[ a ∈ A ] fibre f a) (Σ[ b ∈ B ] शेष b)
  Iso.fun      स्वप् (a , (b , p)) = (b , (a , p))
  Iso.inv      स्वप् (b , (a , p)) = (a , (b , p))
  Iso.rightInv स्वप् _ = refl
  Iso.leftInv  स्वप् _ = refl

  ग्राह : Carrier f ≃ (Σ[ b ∈ B ] शेष b)
  ग्राह = compEquiv (isoToEquiv (Carrier-as-Σ f)) (isoToEquiv स्वप्)

  ------------------------------------------------------------------------
  -- 3.  मूल-प्रक्षेप — the source projection.  ALWAYS an equivalence.
  --
  -- No hypothesis on f.  This is `Carrier≃-via-law` renamed to say what it
  -- is: reading the graph from the source end loses nothing, ever, for any
  -- map whatsoever.  That is the whole content of "carrying determined
  -- data is free" — and the freeness is unconditional.
  ------------------------------------------------------------------------

  मूल-प्रक्षेप : Carrier f → A
  मूल-प्रक्षेप = ascend f

  मूल-प्रक्षेप-समता : Carrier f ≃ A
  मूल-प्रक्षेप-समता = Carrier≃-via-law f

  -- and the equivalence's forward map IS that projection, definitionally
  मूल-प्रक्षेप-अभेदः : (c : Carrier f) → equivFun मूल-प्रक्षेप-समता c ≡ मूल-प्रक्षेप c
  मूल-प्रक्षेप-अभेदः _ = refl

  ------------------------------------------------------------------------
  -- 4.  लक्ष्य-प्रक्षेप — the target projection.  An equivalence exactly when
  --     every residual is contractible.
  --
  -- This is the half that can fail, and the hypothesis that rescues it is
  -- not a formality: `isEquiv` in this substrate is DEFINED as "every
  -- fibre is contractible", so "f loses nothing" and "f is an
  -- identification" are the same statement, and both directions below are
  -- one line because there is nothing between them.
  ------------------------------------------------------------------------

  लक्ष्य-प्रक्षेप : Carrier f → B
  लक्ष्य-प्रक्षेप c = carried c

  निःशेषः→समता : ((b : B) → isContr (शेष b)) → Carrier f ≃ B
  निःशेषः→समता c = compEquiv ग्राह (Σ-contractSnd c)

  निःशेषः→मूल-समता : ((b : B) → isContr (शेष b)) → A ≃ B
  निःशेषः→मूल-समता c = f , record { equiv-proof = c }

  समता→निःशेषः : isEquiv f → (b : B) → isContr (शेष b)
  समता→निःशेषः e b = e .equiv-proof b

  -- the discipline, stated negatively: two source points over one target
  -- point that are not identified are a proof that f is not a transport.
  -- No amount of later cleverness recovers what is not there.
  शेष-द्वयम्→न-समता : (b : B) (x y : शेष b) → ¬ (x ≡ y) → ¬ (isEquiv f)
  शेष-द्वयम्→न-समता b x y x≢y e = x≢y (isContr→isProp (e .equiv-proof b) x y)

------------------------------------------------------------------------
-- 5.  The residue, priced.
--
-- Bool → Unit is the smallest genuine collapse.  Over its single target
-- point the residual is not merely non-contractible — it is EQUIVALENT TO
-- Bool.  The loss is one bit, and "one bit" is a theorem here rather than
-- a description.
--
-- Then both halves of §3/§4 at that instance: the carrier is equivalent
-- to its source (हस्ते) and provably not to its target (न-लक्ष्ये).  The
-- graph did not lose the distinction; the target projection did.
------------------------------------------------------------------------

सर्वैकम् : Bool → Unit
सर्वैकम् _ = tt

-- the residual over tt is exactly one bit
शेष-सर्वैकम्≃Bool : शेष सर्वैकम् tt ≃ Bool
शेष-सर्वैकम्≃Bool = isoToEquiv (iso fst (λ b → (b , refl)) (λ _ → refl) lem)
  where
    lem : (x : शेष सर्वैकम् tt) → (fst x , refl) ≡ x
    lem (b , p) i = (b , isSetUnit tt tt refl p i)

-- so it is not contractible, and the map is not an identification
शेष-सर्वैकम्-न-सम्पूर्णम् : ¬ (isContr (शेष सर्वैकम् tt))
शेष-सर्वैकम्-न-सम्पूर्णम् c =
  false≢true (cong fst (isContr→isProp c (false , refl) (true , refl)))

सर्वैकम्-न-समता : ¬ (isEquiv सर्वैकम्)
सर्वैकम्-न-समता e = शेष-सर्वैकम्-न-सम्पूर्णम् (समता→निःशेषः सर्वैकम् e tt)

-- §3 at this instance: the carrier still knows its source, unconditionally
हस्ते : Carrier सर्वैकम् ≃ Bool
हस्ते = मूल-प्रक्षेप-समता सर्वैकम्

-- §4 at this instance: and it is provably not its target
न-Bool≃Unit : ¬ (Bool ≃ Unit)
न-Bool≃Unit e = false≢true (sym (retEq e false) ∙ retEq e true)

न-लक्ष्ये : ¬ (Carrier सर्वैकम् ≃ Unit)
न-लक्ष्ये e = न-Bool≃Unit (compEquiv (invEquiv हस्ते) e)

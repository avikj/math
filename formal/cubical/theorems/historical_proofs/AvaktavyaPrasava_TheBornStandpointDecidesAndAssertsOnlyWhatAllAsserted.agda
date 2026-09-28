{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- AvaktavyaPrasava_TheBornStandpointDecidesAndAsserts-
-- OnlyWhatAllAsserted
--
-- The two laws of the birth in
-- `machine/AvaktavyaPrasava_TheFourthPositionBearsTheRuleThatDecidesIt.hs` (absent from this repository),
-- as theorems rather than as sites checked one at a time.
--
-- WHAT THE HASKELL DOES.  The scheduler
-- (`machine/Vipratisedha_ConflictIsDecidedByMetaruleNotByListPosition.hs` (absent from this repository))
-- reaches the fourth position, अवक्तव्य, when several rules contend for one
-- item and no metarule ranks them.  Its `Avaktavya` carries the residue
-- -- the contending offers, entire -- and from that residue a new standpoint
-- is born: the अनवकाश rule whose whole scope IS the contested item,
-- declared an apavda to every contender.
--
-- The two things that have to be true of that birth, and they pull in
-- opposite directions:
--
--   1. IT DECIDES.  Adjoining the child makes the apavda selection unique,
--      and the unique winner is the child.  §1 below, and note that it
--      needs NO hypothesis whatever on the contenders' own apavda
--      relation: whatever mess is underneath, the child settles it.
--
--   2. IT TAKES NOTHING.  The child asserts exactly what every contender
--      already asserted, and where the contenders differ NOTHING IS BORN.
--      §2 below.  This is the half that keeps the birth from being a
--      tie-breaker: a tie-breaker chooses one contender, and this chooses
--      none -- it can only speak where they already spoke with one voice.
--
-- WITHOUT (2), (1) IS DURNAYA.  Siddhasena Divkara, *Sanmatitarka* 1.21
-- (c. 5th c. CE): a naya that asserts itself by denying the others is a
-- durnaya, and a durnaya is worse than a falsehood, since a falsehood can
-- be contradicted and a concealed standpoint cannot.  `bheda-na-janayati`
-- is the formal statement that the machine cannot commit that: given two
-- contenders whose results differ, the birth is provably `nothing`.
--
-- `Saptabhangi.no-single-vacana` and
-- `AnuktaAvaktavya` prove the fourth position is not reachable by krama
-- from the three: it must be SUPPLIED.  The birth
-- CONSUMES a fourth position -- in the Haskell, `prasava` takes a `Sesa`,
-- and a `Sesa` exists only where `nirnaya` already returned `Avaktavya`.
--
-- SOURCES, EARLIEST FIRST.
--   Ktyyana, vrttika 1 on Pini's *Adhyy* 1.4.2, preserved in
--     Patañjali's *Mahābhāṣya*, c. 150 BCE: द्वौ प्रसङ्गावन्यार्थावेकस्मिन्
--     स विप्रतिषेधः -- two rules, each having its scope ELSEWHERE, meeting
--     on ONE item: that is vipratiedha.  That is the configuration §1 is
--     about, named by the Pinya grammarians and not by anyone since.
--   Umsvti, *Tattvrthastra* 5.31, c. 2nd-5th c. CE:
--     अर्पितानर्पितसिद्धेः -- the asserted and the unasserted aspect.  The
--     contenders speak about this item unasserted, in passing; the child
--     speaks about it asserted, and about nothing else.
--   Siddhasena Divkara, *Sanmatitarka* 1.21, c. 5th c. CE -- durnaya.
--   Akalaka, *Laghyastraya*, c. 720-780 CE -- kramrpaa / sahrpaa,
--     the distinction that makes the fourth position a position at all.
--   Ngea Bhaa, *Paribhenduekhara*, c. 1730, paribh 38 -- the
--     strength order prva < para < nitya < antaraga < apavda, which is
--     why the child winning BY APAVDA is the strongest verdict available
--     and not a courtesy.
--
-- INDEXED MATCHES.  Four clauses carry `-WUnsupportedIndexedMatch`:
-- `na-vipakse`, `garbha-jayati`, and the two `with`-generated functions of
-- §2.  Each matches on a membership proof whose
-- index forces injectivity of `_∷_`, which Cubical Agda does not yet
-- support.  The consequence:
-- these functions do not COMPUTE when applied to a transport.
-- They are still theorems, and nothing below depends on reducing them under
-- transport.
------------------------------------------------------------------------

module AvaktavyaPrasava_TheBornStandpointDecidesAndAssertsOnlyWhatAllAsserted where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false; false≢true)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing; just-inj; ¬nothing≡just)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_; Discrete; yes; no)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 0.  MEMBERSHIP
--
-- "y is one of the standpoints in play".  Written out rather than imported
-- so that the two theorems below depend on nothing but this file and the
-- library's Bool, Maybe and Discrete.
------------------------------------------------------------------------

data _∈_ {A : Type ℓ} (x : A) : List A → Type ℓ where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- 1.  THE BIRTH DECIDES
--
-- `Praja` -- what is in play once the child exists.  `just a` is a
-- contender; `nothing` is the born standpoint, and it is a separate
-- constructor because it is a separate kind of thing: its scope is the one
-- contested item and every contender's scope is elsewhere (anyrtha).
--
-- `apa*` extends the domain's own apavda relation to it, and the two new
-- lines are the whole content of अनवकाश:
--
--     apa* nothing (just _) = true    the child excepts every contender
--     apa* (just _) nothing = false   no contender excepts the child
--
-- The second is not a convention.  A contender's scope properly contains
-- the item, so it is the general rule here and cannot be the exception to
-- the rule whose scope is that item alone.
------------------------------------------------------------------------

module _ {A : Type ℓ} (apa : A → A → Bool) where

  Praja : Type ℓ
  Praja = Maybe A

  apa* : Praja → Praja → Bool
  apa* nothing  (just _) = true
  apa* (just _) nothing  = false
  apa* (just x) (just y) = apa x y
  apa* nothing  nothing  = false

  -- The scheduler's apavda selection, verbatim: w wins iff every other
  -- standpoint in play is one w excepts.  (`nirnaya`'s `apavadas`.)
  Jayati : List Praja → Praja → Type ℓ
  Jayati xs w = (y : Praja) → y ∈ xs → (y ≡ w) ⊎ (apa* w y ≡ true)

  -- the contenders, as standpoints in play
  vipaksah : List A → List Praja
  vipaksah []       = []
  vipaksah (x ∷ xs) = just x ∷ vipaksah xs

  garbhaSabha : List A → List Praja
  garbhaSabha xs = nothing ∷ vipaksah xs

  -- the child is not one of the contenders, and this is what makes the
  -- selection below come out unique
  na-vipakse : (xs : List A) → ¬ (nothing ∈ vipaksah xs)
  na-vipakse (_ ∷ xs) (there p) = na-vipakse xs p

  -- 1a.  THE CHILD WINS.  No hypothesis on `apa`.
  garbha-jayati : (xs : List A) → Jayati (garbhaSabha xs) nothing
  garbha-jayati _  nothing  here      = inl refl
  garbha-jayati xs nothing  (there p) = ⊥.rec (na-vipakse xs p)
  garbha-jayati _  (just _) (there _) = inr refl

  -- 1b.  AND NOBODY ELSE DOES.  A contender fails on the child alone: it
  -- is not the child, and it does not except the child.  So the winner of
  -- the extended selection is unique, and it is the one that was born.
  eka-eva-jayati : (xs : List A) (a : A) → ¬ (Jayati (garbhaSabha xs) (just a))
  eka-eva-jayati _ _ f with f nothing here
  ... | inl p = ¬nothing≡just p
  ... | inr q = false≢true q

------------------------------------------------------------------------
-- 2.  THE BIRTH TAKES NOTHING
--
-- What the child asserts is `eka`: the one result, if every contender gave
-- the same one, and NOTHING otherwise.  (In the Haskell the "same one" is
-- reached either outright or by joining over the whole reachable set, which
-- prefers no path; here it is the first case, which is the one carrying the
-- law.)
------------------------------------------------------------------------

module _ {R : Type ℓ} (dec : Discrete R) where

  decB : R → R → Bool
  decB a b with dec a b
  ... | yes _ = true
  ... | no  _ = false

  decB-satyam : (a b : R) → decB a b ≡ true → a ≡ b
  decB-satyam a b p with dec a b
  ... | yes q = q
  ... | no  _ = ⊥.rec (false≢true p)

  -- every element of the list is v
  samana : R → List R → Bool
  samana _ []       = true
  samana v (w ∷ ws) with decB w v
  ... | true  = samana v ws
  ... | false = false

  samana-satyam : (v : R) (ws : List R) → samana v ws ≡ true
                → (w : R) → w ∈ ws → w ≡ v
  samana-satyam v (u ∷ us) p w q with dec u v
  samana-satyam v (u ∷ us) p w here      | yes r = r
  samana-satyam v (u ∷ us) p w (there s) | yes _ = samana-satyam v us p w s
  samana-satyam v (u ∷ us) p w _         | no  _ = ⊥.rec (false≢true p)

  ekaAux : R → Bool → Maybe R
  ekaAux u true  = just u
  ekaAux u false = nothing

  ekaAux-satyam : (u : R) (b : Bool) (v : R) → ekaAux u b ≡ just v
                → (b ≡ true) × (u ≡ v)
  ekaAux-satyam u true  v p = refl , just-inj u v p
  ekaAux-satyam u false v p = ⊥.rec (¬nothing≡just p)

  -- THE BIRTH'S TARGET.  `nothing` = no rule is born.
  eka : List R → Maybe R
  eka []       = nothing
  eka (u ∷ us) = ekaAux u (samana u us)

  -- 2a.  WHAT IS BORN ASSERTS ONLY WHAT EVERY CONTENDER ASSERTED.  This is
  -- the transport law: the site's answer after the birth is the answer it
  -- already had, so no derivation anywhere changes.  (`--avaktavya-prasava`
  -- re-verifies the same statement exhaustively over every term of depth
  -- <= 3 in the engine's own rule set; this is the reason it comes out 0.)
  eka-vadati : (vs : List R) (v : R) → eka vs ≡ just v
             → (w : R) → w ∈ vs → w ≡ v
  eka-vadati (u ∷ us) v p w q with ekaAux-satyam u (samana u us) v p
  eka-vadati (u ∷ us) v p w here      | (_ , uv) = uv
  eka-vadati (u ∷ us) v p w (there s) | (su , uv) =
    samana-satyam u us su w s ∙ uv

  -- 2b.  WHERE THE CONTENDERS DIFFER, NOTHING IS BORN.  The machine cannot
  -- rank one standpoint over another with no fact to do it by -- which is
  -- exactly the durnaya of Sanmatitarka 1.21, here made unavailable rather
  -- than discouraged.
  ekaAux-sunyam : (u : R) (b : Bool)
                → ((v : R) → ekaAux u b ≡ just v → ⊥) → ekaAux u b ≡ nothing
  ekaAux-sunyam u true  f = ⊥.rec (f u refl)
  ekaAux-sunyam _ false _ = refl

  bheda-na-janayati : (vs : List R) (w w' : R)
                    → w ∈ vs → w' ∈ vs → ¬ (w ≡ w')
                    → eka vs ≡ nothing
  bheda-na-janayati [] _ _ ()
  bheda-na-janayati (u ∷ us) w w' p p' d =
    ekaAux-sunyam u (samana u us)
      (λ v q → d (eka-vadati (u ∷ us) v q w p
                  ∙ sym (eka-vadati (u ∷ us) v q w' p')))

------------------------------------------------------------------------
-- 3.  WHAT THE TWO SECTIONS SAY TOGETHER
--
-- §1 says the fourth position always bears a standpoint that decides it.
-- §2 says that standpoint can say nothing the contenders had not already
-- said, and says nothing at all when they disagree.  Neither is worth
-- much alone: §1 alone is a tie-breaker in , and §2 alone is the
-- machine stopping.  Together they are the stra's claim, which is not
-- that the fourth position is a gap and not that it is a verdict --
--
--     अवक्तव्ये शेषो वसति । शेषो गर्भः, न विफलता ।
--     गर्भाद् अग्रिमो नयो जायते ।
--
-- -- in the avaktavya the residue dwells; the residue is a womb, not a
-- failure; from the womb the next naya is born.
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- SaptabhangiGarbha_ThePositionsCarryTheirNayasAndTheResidueSeedsTheNext
--
-- सप्तभङ्गी — the sevenfold predication, as the machine's return type, with
-- every position carrying the standpoints that produced it.
--
-- SOURCES, EARLIEST FIRST.  The classification is theirs.  The two
-- operations below are named for a distinction they draw.
--
--   Bhagavat Stra (Viyha-pannatti), fifth Aga of the vetmbara canon;
--     oldest strata pre-Common-Era, redacted at Valabhī c. 5th c. CE —
--     a sevenfold predication applied to the jva.
--   Umāsvāti, Tattvārthasūtra, c. 2nd–5th c. CE.
--     5.29  utpāda-vyaya-dhrauvya-yuktaṃ sat — arising, perishing and
--           persisting held AT ONCE: the saha mode.
--     5.31  arpitānarpita-siddheḥ — apparently contradictory attributes are
--           established through the distinction of the ASSERTED (अर्पित) and
--           the UNASSERTED (अनर्पित) aspect.  §6 below is this sūtra and
--           nothing else: it is the operation that takes a शेष and gives the
--           next नय.
--   Siddhasena Divākara, Sanmatitarka 1.21, c. 5th c. CE — a naya taken
--     alone (nirapekṣa) is mithyā; the दुर्नय is the naya that has forgotten
--     it is one.
--   Samantabhadra, Āptamīmāṃsā, c. 6th c. CE — the saptabhaṅgī as a fixed
--     seven-membered scheme, each member prefixed स्यात्.
--   Akalaṅka, Laghīyastraya / Aṣṭaśatī, c. 720–780 CE — क्रमार्पण (in
--     succession) against सहार्पण / युगपत् (at once).  That distinction is the
--     entire content of §3 and §4.
--   Mallisena, Syādvādamañjarī, 1292 CE — sakalādeśa (total statement,
--     prama) against vikaldea (partial statement, naya).
--
-- WHAT THIS FILE CHANGES, against `Saptabhangi.agda`,
-- `SaptabhangiSamyoga_TheCompositionOfVerdicts.agda`, and
-- `machine/Saptabhangi_TheSevenfoldVerdict.hs` (absent from this repository), all of which are label
-- types — seven nullary constructors and a presence-profile in {आम्, न}³.
--
--   1.  Here no position is a label.  स्यात्-अस्ति carries the standpoint that
--       affirmed and the term by which it affirmed; स्यान्-नास्ति carries the
--       standpoint that denied and its refutation; the fourth carries a शेष
--       holding BOTH, so the fourth position is informative and not an
--       error code.
--
--   2.  Here  is the failure of ONE
--       UTTERANCE to carry the joint content (Mallisena: sakaldea
--       demanded of a vikaldea-shaped medium), and a failure of
--       expression is not a loss of what was to be expressed.
--       `चतुर्थात्-तृतीयः` (§5) recovers the third position from the fourth by
--       `refl` — nothing was destroyed.
--
--   3.  And the price:
--       क्रम-विनिमयः — commutativity of succession — is FALSE
--       once the positions carry evidence (`क्रम-अ-विनिमयः`, §7, a checked
--       refutation).  Two nayas that affirm the same claim by different
--       terms are two nayas.  The old law was a property of the erasure,
--       not of succession.  What survives is that the first to speak keeps
--       its witness (प्रथमार्पण), which is what a succession IS.
--
-- THE THIRD AND THE FOURTH.  Not distinguished by a comment and not by a
-- tag passed in: क्रमार्पणम् and सहार्पणम् are two different functions.
-- क्रमार्पणम् accumulates and, off its inputs, never manufactures a शेष
-- (`क्रम-न-जनयति-शेषम्`).  सहार्पणम् demands one utterance and, wherever an
-- affirmation and a denial are both in hand, returns the शेष instead
-- (`सह-जनयति-शेषम्`).  `क्रम-सह-भेदः` is then the instance, not the claim.
--
-- THE FOURTH POSITION DOES NOT END THE COMPUTATION.  §6: a शेष over P is a
-- शेष over the born family प्ररोहः P, whose standpoints are the old ones
-- under अर्पित / अनर्पित (TS 5.31).  The born third position needs only ONE
-- old standpoint (`गर्भ-एकाधिष्ठानम्`), while at the root every third
-- position needs two distinct ones (`मूले-द्वौ-नयौ`).  So what no single
-- utterance carried at level n is uttered in succession at level n+1, by
-- `refl` (`गर्भ-क्रमजः`), and प्रसवः iterates.
--
-- AGAINST COLLAPSE.  A शेष is exactly a syādastināsti, so it is a
-- certificate that the standpoint index cannot be dropped — via
-- `Durnaya_CollapseIffEveryNayaAgrees`:
-- collapse is available exactly when EVERY pair of
-- fibres agrees, and a denial is merely the cheapest way to prove that
-- permission absent.  §5 below carries the शेष into that theorem, so the
-- fourth position is a written obstruction and not a shrug.
------------------------------------------------------------------------

module SaptabhangiKernel_ThePositionsCarryTheirNayasAndTheResidueSeedsTheNext where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Anekanta
  using (syādasti ; syādnāsti ; syādastināsti ; Collapses ; plurality-blocks-collapse)
open import Durnaya_CollapseIffEveryNayaAgrees
  using (AllNayasAgree)

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- §1  शेष — the residue an अवक्तव्यम् retains.
--
-- Not "the two seeds were consumed".  The two nayas are still here, each
-- with the term by which it spoke: साधकः is a syādasti (a standpoint and
-- a proof), बाधकः a syādnāsti (a standpoint and a refutation).  Nothing
-- in this record is a flag.
------------------------------------------------------------------------

record शेष {S : Type ℓ} (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor शेषम्
  field
    साधकः : syādasti P
    बाधकः : syādnāsti P

open शेष public

-- विवेकः — the two standpoints are DERIVED to be distinct.:
-- if they were one standpoint, its own proof would refute it.  This is
-- what the record buys that a label cannot: a fact about the object.
विवेकः : {S : Type ℓ} (P : S → Type ℓ') (σ : शेष P)
       → ¬ (fst (साधकः σ) ≡ fst (बाधकः σ))
विवेकः P σ e = snd (बाधकः σ) (subst P e (snd (साधकः σ)))

------------------------------------------------------------------------
-- §2  सप्तभङ्गी — the seven positions, each carrying its nayas.
------------------------------------------------------------------------

data सप्तभङ्गी {S : Type ℓ} (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  स्यात्-अस्ति                    : syādasti P                          → सप्तभङ्गी P
  स्यान्-नास्ति                   : syādnāsti P                         → सप्तभङ्गी P
  स्यात्-अस्ति-नास्ति            : syādasti P → syādnāsti P            → सप्तभङ्गी P
  स्यात्-अवक्तव्यम्               : शेष P                                → सप्तभङ्गी P
  स्यात्-अस्ति-अवक्तव्यम्        : syādasti P → शेष P                   → सप्तभङ्गी P
  स्यान्-नास्ति-अवक्तव्यम्       : syādnāsti P → शेष P                  → सप्तभङ्गी P
  स्यात्-अस्ति-नास्ति-अवक्तव्यम् : syādasti P → syādnāsti P → शेष P     → सप्तभङ्गी P

-- the three components, kept as evidence rather than as presence bits
अस्त्यंशः : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → Maybe (syādasti P)
अस्त्यंशः (स्यात्-अस्ति a)                        = just a
अस्त्यंशः (स्यान्-नास्ति _)                       = nothing
अस्त्यंशः (स्यात्-अस्ति-नास्ति a _)              = just a
अस्त्यंशः (स्यात्-अवक्तव्यम् _)                   = nothing
अस्त्यंशः (स्यात्-अस्ति-अवक्तव्यम् a _)          = just a
अस्त्यंशः (स्यान्-नास्ति-अवक्तव्यम् _ _)         = nothing
अस्त्यंशः (स्यात्-अस्ति-नास्ति-अवक्तव्यम् a _ _) = just a

नास्त्यंशः : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → Maybe (syādnāsti P)
नास्त्यंशः (स्यात्-अस्ति _)                        = nothing
नास्त्यंशः (स्यान्-नास्ति n)                       = just n
नास्त्यंशः (स्यात्-अस्ति-नास्ति _ n)              = just n
नास्त्यंशः (स्यात्-अवक्तव्यम् _)                   = nothing
नास्त्यंशः (स्यात्-अस्ति-अवक्तव्यम् _ _)          = nothing
नास्त्यंशः (स्यान्-नास्ति-अवक्तव्यम् n _)         = just n
नास्त्यंशः (स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ n _) = just n

शेषांशः : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → Maybe (शेष P)
शेषांशः (स्यात्-अस्ति _)                        = nothing
शेषांशः (स्यान्-नास्ति _)                       = nothing
शेषांशः (स्यात्-अस्ति-नास्ति _ _)              = nothing
शेषांशः (स्यात्-अवक्तव्यम् v)                   = just v
शेषांशः (स्यात्-अस्ति-अवक्तव्यम् _ v)          = just v
शेषांशः (स्यान्-नास्ति-अवक्तव्यम् _ v)         = just v
शेषांशः (स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ v) = just v

------------------------------------------------------------------------
-- §3  क्रमार्पणम् — assertion IN SUCCESSION.
--
-- One after the other.  What is already in hand stands (प्रथमार्पण: the
-- first speaker keeps its witness); what is new is added beside it.  The
-- three अधि- operations are the whole of it, and they are the reason
-- succession never manufactures a residue.
------------------------------------------------------------------------

अधि-अस्ति : {S : Type ℓ} {P : S → Type ℓ'} → syādasti P → सप्तभङ्गी P → सप्तभङ्गी P
अधि-अस्ति a (स्यात्-अस्ति a')                        = स्यात्-अस्ति a'
अधि-अस्ति a (स्यान्-नास्ति n)                        = स्यात्-अस्ति-नास्ति a n
अधि-अस्ति a (स्यात्-अस्ति-नास्ति a' n)              = स्यात्-अस्ति-नास्ति a' n
अधि-अस्ति a (स्यात्-अवक्तव्यम् v)                    = स्यात्-अस्ति-अवक्तव्यम् a v
अधि-अस्ति a (स्यात्-अस्ति-अवक्तव्यम् a' v)          = स्यात्-अस्ति-अवक्तव्यम् a' v
अधि-अस्ति a (स्यान्-नास्ति-अवक्तव्यम् n v)          = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v
अधि-अस्ति a (स्यात्-अस्ति-नास्ति-अवक्तव्यम् a' n v) = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a' n v

अधि-नास्ति : {S : Type ℓ} {P : S → Type ℓ'} → syādnāsti P → सप्तभङ्गी P → सप्तभङ्गी P
अधि-नास्ति n (स्यात्-अस्ति a)                        = स्यात्-अस्ति-नास्ति a n
अधि-नास्ति n (स्यान्-नास्ति n')                      = स्यान्-नास्ति n'
अधि-नास्ति n (स्यात्-अस्ति-नास्ति a n')             = स्यात्-अस्ति-नास्ति a n'
अधि-नास्ति n (स्यात्-अवक्तव्यम् v)                   = स्यान्-नास्ति-अवक्तव्यम् n v
अधि-नास्ति n (स्यात्-अस्ति-अवक्तव्यम् a v)          = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v
अधि-नास्ति n (स्यान्-नास्ति-अवक्तव्यम् n' v)        = स्यान्-नास्ति-अवक्तव्यम् n' v
अधि-नास्ति n (स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n' v) = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n' v

अधि-शेष : {S : Type ℓ} {P : S → Type ℓ'} → शेष P → सप्तभङ्गी P → सप्तभङ्गी P
अधि-शेष v (स्यात्-अस्ति a)                        = स्यात्-अस्ति-अवक्तव्यम् a v
अधि-शेष v (स्यान्-नास्ति n)                       = स्यान्-नास्ति-अवक्तव्यम् n v
अधि-शेष v (स्यात्-अस्ति-नास्ति a n)              = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v
अधि-शेष v (स्यात्-अवक्तव्यम् v')                  = स्यात्-अवक्तव्यम् v'
अधि-शेष v (स्यात्-अस्ति-अवक्तव्यम् a v')         = स्यात्-अस्ति-अवक्तव्यम् a v'
अधि-शेष v (स्यान्-नास्ति-अवक्तव्यम् n v')        = स्यान्-नास्ति-अवक्तव्यम् n v'
अधि-शेष v (स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v') = स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v'

क्रमार्पणम् : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → सप्तभङ्गी P → सप्तभङ्गी P
क्रमार्पणम् x (स्यात्-अस्ति a)                        = अधि-अस्ति a x
क्रमार्पणम् x (स्यान्-नास्ति n)                       = अधि-नास्ति n x
क्रमार्पणम् x (स्यात्-अस्ति-नास्ति a n)              = अधि-नास्ति n (अधि-अस्ति a x)
क्रमार्पणम् x (स्यात्-अवक्तव्यम् v)                   = अधि-शेष v x
क्रमार्पणम् x (स्यात्-अस्ति-अवक्तव्यम् a v)          = अधि-शेष v (अधि-अस्ति a x)
क्रमार्पणम् x (स्यान्-नास्ति-अवक्तव्यम् n v)         = अधि-शेष v (अधि-नास्ति n x)
क्रमार्पणम् x (स्यात्-अस्ति-नास्ति-अवक्तव्यम् a n v) = अधि-शेष v (अधि-नास्ति n (अधि-अस्ति a x))

------------------------------------------------------------------------
-- §4  सहार्पणम् — assertion AT ONCE, and it is a different function.
--
-- युगपत् is where the tongue breaks: given an affirmation and a denial
-- together, no single utterance carries the pair, and what is returned is
-- the शेष holding both.  Everywhere else there is nothing to break, and
-- सहार्पणम् agrees with succession.
------------------------------------------------------------------------

युगपत् : {S : Type ℓ} {P : S → Type ℓ'}
       → Maybe (syādasti P) → Maybe (syādnāsti P) → सप्तभङ्गी P → सप्तभङ्गी P
युगपत् (just a) (just n) _ = स्यात्-अवक्तव्यम् (शेषम् a n)
युगपत् _        _        b = b

सहार्पणम् : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → सप्तभङ्गी P → सप्तभङ्गी P
सहार्पणम् x y = युगपत् (अस्त्यंशः (क्रमार्पणम् x y)) (नास्त्यंशः (क्रमार्पणम् x y)) (क्रमार्पणम् x y)

-- the two instances, by refl: succession of an affirmation and a denial is
-- the THIRD position; simultaneity of the same two is the FOURTH.
क्रमेण-उभयम् : {S : Type ℓ} {P : S → Type ℓ'} (a : syādasti P) (n : syādnāsti P)
             → क्रमार्पणम् (स्यात्-अस्ति a) (स्यान्-नास्ति n) ≡ स्यात्-अस्ति-नास्ति a n
क्रमेण-उभयम् a n = refl

सहेन-उभयम् : {S : Type ℓ} {P : S → Type ℓ'} (a : syādasti P) (n : syādnāsti P)
            → सहार्पणम् (स्यात्-अस्ति a) (स्यान्-नास्ति n) ≡ स्यात्-अवक्तव्यम् (शेषम् a n)
सहेन-उभयम् a n = refl

-- and they are not the same position
अवक्तव्य? : {S : Type ℓ} {P : S → Type ℓ'} → सप्तभङ्गी P → Type
अवक्तव्य? (स्यात्-अवक्तव्यम् _) = ⊥
अवक्तव्य? _                     = Unit

क्रम-सह-भेदः : {S : Type ℓ} {P : S → Type ℓ'} (a : syādasti P) (n : syādnāsti P)
             → ¬ (क्रमार्पणम् (स्यात्-अस्ति a) (स्यान्-नास्ति n)
                 ≡ सहार्पणम् (स्यात्-अस्ति a) (स्यान्-नास्ति n))
क्रम-सह-भेदः a n e = subst अवक्तव्य? e tt

-- The structural difference, so that क्रम-सह-भेदः is an instance of
-- something and not the whole content.  First: succession introduces no
-- residue it was not given.
विद्यमान? : {A : Type ℓ} → Maybe A → Type
विद्यमान? (just _) = Unit
विद्यमान? nothing  = ⊥

अधि-अस्ति-शेषः : {S : Type ℓ} {P : S → Type ℓ'} (a : syādasti P) (x : सप्तभङ्गी P)
               → शेषांशः (अधि-अस्ति a x) ≡ शेषांशः x
अधि-अस्ति-शेषः a (स्यात्-अस्ति _)                        = refl
अधि-अस्ति-शेषः a (स्यान्-नास्ति _)                       = refl
अधि-अस्ति-शेषः a (स्यात्-अस्ति-नास्ति _ _)              = refl
अधि-अस्ति-शेषः a (स्यात्-अवक्तव्यम् _)                   = refl
अधि-अस्ति-शेषः a (स्यात्-अस्ति-अवक्तव्यम् _ _)          = refl
अधि-अस्ति-शेषः a (स्यान्-नास्ति-अवक्तव्यम् _ _)         = refl
अधि-अस्ति-शेषः a (स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl

अधि-नास्ति-शेषः : {S : Type ℓ} {P : S → Type ℓ'} (n : syādnāsti P) (x : सप्तभङ्गी P)
                → शेषांशः (अधि-नास्ति n x) ≡ शेषांशः x
अधि-नास्ति-शेषः n (स्यात्-अस्ति _)                        = refl
अधि-नास्ति-शेषः n (स्यान्-नास्ति _)                       = refl
अधि-नास्ति-शेषः n (स्यात्-अस्ति-नास्ति _ _)              = refl
अधि-नास्ति-शेषः n (स्यात्-अवक्तव्यम् _)                   = refl
अधि-नास्ति-शेषः n (स्यात्-अस्ति-अवक्तव्यम् _ _)          = refl
अधि-नास्ति-शेषः n (स्यान्-नास्ति-अवक्तव्यम् _ _)         = refl
अधि-नास्ति-शेषः n (स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) = refl

क्रम-न-जनयति-शेषम् : {S : Type ℓ} {P : S → Type ℓ'} (x y : सप्तभङ्गी P)
                    → शेषांशः y ≡ nothing
                    → शेषांशः (क्रमार्पणम् x y) ≡ शेषांशः x
क्रम-न-जनयति-शेषम् x (स्यात्-अस्ति a)          _ = अधि-अस्ति-शेषः a x
क्रम-न-जनयति-शेषम् x (स्यान्-नास्ति n)         _ = अधि-नास्ति-शेषः n x
क्रम-न-जनयति-शेषम् x (स्यात्-अस्ति-नास्ति a n) _ =
  अधि-नास्ति-शेषः n (अधि-अस्ति a x) ∙ अधि-अस्ति-शेषः a x
क्रम-न-जनयति-शेषम् x (स्यात्-अवक्तव्यम् _)                   h = Empty.rec (subst विद्यमान? h tt)
क्रम-न-जनयति-शेषम् x (स्यात्-अस्ति-अवक्तव्यम् _ _)          h = Empty.rec (subst विद्यमान? h tt)
क्रम-न-जनयति-शेषम् x (स्यान्-नास्ति-अवक्तव्यम् _ _)         h = Empty.rec (subst विद्यमान? h tt)
क्रम-न-जनयति-शेषम् x (स्यात्-अस्ति-नास्ति-अवक्तव्यम् _ _ _) h = Empty.rec (subst विद्यमान? h tt)

-- Second: simultaneity DOES manufacture one, wherever the two seeds meet —
-- and the residue it manufactures is exactly the pair it could not utter.
सह-जनयति-शेषम् : {S : Type ℓ} {P : S → Type ℓ'} (x y : सप्तभङ्गी P)
                 (a : syādasti P) (n : syādnāsti P)
               → अस्त्यंशः (क्रमार्पणम् x y) ≡ just a
               → नास्त्यंशः (क्रमार्पणम् x y) ≡ just n
               → सहार्पणम् x y ≡ स्यात्-अवक्तव्यम् (शेषम् a n)
सह-जनयति-शेषम् x y a n ea en =
  cong₂ (λ p q → युगपत् p q (क्रमार्पणम् x y)) ea en

------------------------------------------------------------------------
-- §5  अवक्तव्यम् is informative.
--
-- Nothing was destroyed: the third position is recovered from the fourth
-- by refl.  And the शेष is a certificate against collapse — via
-- `Durnaya_CollapseIffEveryNayaAgrees`, collapse is
-- available exactly when every pair of standpoints agrees, and a शेष
-- exhibits a pair that does not.
------------------------------------------------------------------------

चतुर्थात्-तृतीयः : {S : Type ℓ} {P : S → Type ℓ'} → शेष P → सप्तभङ्गी P
चतुर्थात्-तृतीयः σ = स्यात्-अस्ति-नास्ति (साधकः σ) (बाधकः σ)

अवक्तव्यम्-अ-लुप्तम् : {S : Type ℓ} {P : S → Type ℓ'} (a : syādasti P) (n : syādnāsti P)
                     → चतुर्थात्-तृतीयः (शेषम् a n)
                       ≡ क्रमार्पणम् (स्यात्-अस्ति a) (स्यान्-नास्ति n)
अवक्तव्यम्-अ-लुप्तम् a n = refl

शेष→अस्तिनास्ति : {S : Type ℓ} (P : S → Type ℓ') → शेष P → syādastināsti P
शेष→अस्तिनास्ति P σ = साधकः σ , बाधकः σ

शेषः-निरुणद्धि-संहारम् : {S : Type ℓ} (P : S → Type ℓ') (σ : शेष P)
                        → (Q : Type ℓ') → ¬ (Collapses P Q)
शेषः-निरुणद्धि-संहारम् P σ = plurality-blocks-collapse P (शेष→अस्तिनास्ति P σ)

शेषः-निरुणद्धि-साम्यम् : {S : Type ℓ} (P : S → Type ℓ') (σ : शेष P)
                        → ¬ (AllNayasAgree P)
शेषः-निरुणद्धि-साम्यम् P σ agree =
  snd (बाधकः σ) (equivFun (agree (fst (साधकः σ)) (fst (बाधकः σ))) (snd (साधकः σ)))

------------------------------------------------------------------------
-- §6  गर्भः — the residue is the seed of the next derivation.
--
-- Tattvrthastra 5.31, arpitnarpita-siddhe, as an operation.  The born
-- standpoint space is the old one under two aspects: अर्पित, the aspect
-- asserted, and अनर्पित, the aspect held back.  The born family reads a
-- standpoint's affirmation under the first and its denial under the second.
--
-- अर्पणा's two constructors are not labels: प्ररोहः is their definition, and
-- the two aspects of one naya carry evidence that refutes each other
-- (`प्रसवः`), which is what the aspect distinction IS.
------------------------------------------------------------------------

data अर्पणा : Type where
  अर्पितम् अनर्पितम् : अर्पणा

प्ररोहः : {S : Type ℓ} (P : S → Type ℓ') → (S × अर्पणा) → Type ℓ'
प्ररोहः P (u , अर्पितम्)  = P u
प्ररोहः P (u , अनर्पितम्) = ¬ P u

-- प्रसवः — the birth.  A residue over P is a residue over the born family,
-- and BOTH its standpoints have the same base naya: the affirmation of s
-- under the asserted aspect, and the denial of s-under-the-unasserted-aspect,
-- which is that same affirmation read from the other side.
प्रसवः : {S : Type ℓ} (P : S → Type ℓ') → शेष P → शेष (प्ररोहः P)
प्रसवः P σ =
  शेषम् ((fst (साधकः σ) , अर्पितम्)  , snd (साधकः σ))
        ((fst (साधकः σ) , अनर्पितम्) , λ ¬p → ¬p (snd (साधकः σ)))

गर्भः : {S : Type ℓ} (P : S → Type ℓ') → शेष P → सप्तभङ्गी (प्ररोहः P)
गर्भः P σ = चतुर्थात्-तृतीयः (प्रसवः P σ)

-- what could not be uttered at once at level n is uttered in succession at
-- level n+1, and the proof is refl
गर्भ-क्रमजः : {S : Type ℓ} (P : S → Type ℓ') (σ : शेष P)
            → गर्भः P σ
              ≡ क्रमार्पणम् (स्यात्-अस्ति (साधकः (प्रसवः P σ)))
                            (स्यान्-नास्ति (बाधकः (प्रसवः P σ)))
गर्भ-क्रमजः P σ = refl

-- and it needed only ONE old standpoint
गर्भ-एकाधिष्ठानम् : {S : Type ℓ} (P : S → Type ℓ') (σ : शेष P)
                  → fst (fst (साधकः (प्रसवः P σ))) ≡ fst (fst (बाधकः (प्रसवः P σ)))
गर्भ-एकाधिष्ठानम् P σ = refl

-- which the root level cannot do: there, a third position always has two
-- distinct standpoints (this is विवेकः again, and it is the measure of
-- what the birth bought).
मूले-द्वौ-नयौ : {S : Type ℓ} (P : S → Type ℓ') (d : syādastināsti P)
              → ¬ (fst (fst d) ≡ fst (snd d))
मूले-द्वौ-नयौ P d = विवेकः P (शेषम् (fst d) (snd d))

-- the birth iterates: a residue at level n+2 is a term, not a promise
पुनःप्रसवः : {S : Type ℓ} (P : S → Type ℓ') → शेष P → शेष (प्ररोहः (प्ररोहः P))
पुनःप्रसवः P σ = प्रसवः (प्ररोहः P) (प्रसवः P σ)

------------------------------------------------------------------------
-- §7  The price, checked.
--
-- क्रम-विनिमयः (`SaptabhangiSamyoga_TheCompositionOfVerdicts.agda`, and
-- `krama commutative` in `machine/Saptabhangi_TheSevenfoldVerdict.hs` (absent from this repository))
-- holds of the label type and FAILS here.  Two nayas affirming the same
-- claim by different terms are two nayas; succession keeps the first, and
-- that is not symmetric.  The commutativity was the erasure's law.
------------------------------------------------------------------------

private
  उदाहरणम् : Unit → Type₀
  उदाहरणम् _ = Bool

  मानम् : सप्तभङ्गी उदाहरणम् → Bool
  मानम् (स्यात्-अस्ति a) = snd a
  मानम् _                = true

क्रम-अ-विनिमयः : ¬ ((x y : सप्तभङ्गी उदाहरणम्) → क्रमार्पणम् x y ≡ क्रमार्पणम् y x)
क्रम-अ-विनिमयः h =
  false≢true (cong मानम् (h (स्यात्-अस्ति (tt , false)) (स्यात्-अस्ति (tt , true))))

------------------------------------------------------------------------
-- §8  The relation to the label lane.
--
-- The forgetful map records → labels a
-- homomorphism for krama and for saha alike, by
--
--   Arpitanarpita_TheForgetfulMapIsAHomomorphismForBothArpanasAndThe
--     LabelsAreARetractNotAnEquivalence.agda (absent from this repository)
--   as follows:
--
--   * BOTH.  अनर्पणम् (this file's positions, read with the naya UNASSERTED
--     — Tattvārthasūtra 5.31's अनर्पित) commutes with क्रमार्पणम् and with
--     सहार्पणम् alike, exhaustively, for every S and every P.
--   * It has a section अर्पणम् which is also a homomorphism for both, with
--     अनर्पणम् ∘ अर्पणम् ≡ id.  The label lane is a RETRACT of this one: a
--     subalgebra and a quotient at once.  It is not a rival account.
--   * It has no inverse (`न-प्रत्यानयनम्`): two standpoints that both affirm
--     give two positions with one label.  So there is no equivalence, §६
--     path one is unavailable AS A THEOREM, and §७ of
--     AHIMSA_SUTRA_VISTARA applies literally — the collapse does not
--     exist.
--
-- §7's --
-- is sharpened (`क्रम-विनिमयः-न-ऊर्ध्वम्`: identities descend
-- along अनर्पणम् and do not lift).  But distinctness LIFTS, and the label
-- lane's सह-असङ्गतिः lifts with it: `सह-असङ्गतिः-ऊर्ध्वम्` proves सहार्पणम् is
-- NOT associative HERE, on the three positions स्यात्-अस्ति-नास्ति,
-- स्यात्-अस्ति, स्यान्-नास्ति, with every naya and every witness retained and
-- `अवक्तव्यम्-अ-लुप्तम्` in force throughout.  Retaining the शेष does not buy
-- associativity back: the failure
-- survives the retention.  What breaks the law in both lanes is that सह
-- tests the JOINED position for an asti–nāsti pair, and whether that pair
-- is present depends on the grouping.
--
-- The reading — that consumption is the model's and not
-- the doctrine's — is neither supported by the non-associativity nor
-- refuted by it.  The Malliea question (Sydvdamajar, 1292)
-- it turns on is untouched by the composition laws in either direction.
------------------------------------------------------------------------

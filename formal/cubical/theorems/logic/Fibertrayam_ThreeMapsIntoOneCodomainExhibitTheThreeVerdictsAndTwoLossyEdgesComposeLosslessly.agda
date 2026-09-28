{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- - —    
--
-- (three fibres over one codomain.)
--
-- §१ · THE THREE VERDICTS, EXHIBITED AT THE SMALLEST SCALE.  Three maps
-- into ONE codomain, `Unit`, with fibres रिक्तम् / एकम् / बहु.  A boolean
-- verdict -- "is this an equivalence?" -- answers NO to the first and the
-- third alike, and §१.४ proves those two are not the same situation.
-- That is `Saptabhangi.दुर्नयः`'s pigeonhole at the minimum instance, and
-- it is what `interactive/Lopa_…hs` withholds a verdict for rather than guess.
--
-- §२ · TWO LOSSY EDGES COMPOSING LOSSLESSLY.  `Unit → Bool → Unit`: the
-- second factor loses a bit (§१.३), and the composite loses nothing.  So
-- loss does not accumulate along composition -- the alignment term
-- `rank(AB) = rank(B) − dim(im B ∩ ker A)` at its smallest, and the
-- Knill–Laflamme condition `im B ∩ ker A = 0` exhibited: the first edge's
-- image dodges the second edge's collapse.  README movement 2 names
-- `Unit→Bool→Unit` as the checked cancellation; this is that term.
--
-- RELATION TO `Parampara_...agda` (absent from this repository).
-- That module also finds that losses do not add along a
-- chain, by a DIFFERENT mechanism -- an ABSENCE sitting in the middle fibre
-- -- over three maps rather than two.  Section 2 here is the other mechanism
-- at minimum scale: the first edge's image DODGES the second edge's collapse,
-- with nothing empty anywhere.  Two distinct ways for the alignment term to
-- vanish, and the corpus now carries both.
------------------------------------------------------------------------

module Fibertrayam_ThreeMapsIntoOneCodomainExhibitTheThreeVerdictsAndTwoLossyEdgesComposeLosslessly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; fiber ; idIsEquiv)
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; _×_)
open import Cubical.Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- १ · त्रयो निर्णयाः — three maps into Unit, three fibres.
------------------------------------------------------------------------

-- १.१ रिक्तम् — the empty fibre.  No answer exists.
रिक्त-मार्गः : ⊥ → Unit
रिक्त-मार्गः ()

रिक्तम् : ¬ (fiber रिक्त-मार्गः tt)
रिक्तम् (x , _) = Empty.rec x

-- १.२ एकम् — the singleton fibre.  Free: the identity loses nothing.
एक-मार्गः : Unit → Unit
एक-मार्गः u = u

एकम् : isEquiv एक-मार्गः
एकम् = idIsEquiv Unit

-- १.३ बहु — the many fibre.  One bit destroyed, and the two witnesses
--      of that destruction are distinct.
बहु-मार्गः : Bool → Unit
बहु-मार्गः _ = tt

सत् असत् : fiber बहु-मार्गः tt
सत्  = true  , refl
असत् = false , refl

बहु : ¬ (isContr (fiber बहु-मार्गः tt))
बहु c = false≢true (cong fst (sym (c .snd असत्) ∙ c .snd सत्))

-- १.४ दुर्नयः — AND THE BOOLEAN MERGES THE FIRST AND THE THIRD.
--
-- Both रिक्त-मार्गः and बहु-मार्गः fail to be equivalences, so a two-valued
-- verdict returns the same answer for both.  They are not the same
-- situation: one fibre is uninhabited and the other is inhabited, and
-- that difference is exactly what the boolean destroys.
भेदः : (¬ (fiber रिक्त-मार्गः tt)) × (fiber बहु-मार्गः tt)
भेदः = रिक्तम् , सत्

------------------------------------------------------------------------
-- २ · संयोगे शेषः क्षीयते — loss does not accumulate.
--
-- `बहु-मार्गः` destroys a bit.  Precompose it with a map whose image
-- dodges the collapse and the composite destroys nothing.
------------------------------------------------------------------------

उत्थानम् : Unit → Bool
उत्थानम् _ = true

संयोगः : Unit → Unit
संयोगः u = बहु-मार्गः (उत्थानम् u)

-- the composite is an equivalence, though its second factor is not
संयोगः-अक्षयः : isEquiv संयोगः
संयोगः-अक्षयः = idIsEquiv Unit

-- and the second factor still is not, so the cancellation is real
मध्यमः-क्षयी : ¬ (isContr (fiber बहु-मार्गः tt))
मध्यमः-क्षयी = बहु

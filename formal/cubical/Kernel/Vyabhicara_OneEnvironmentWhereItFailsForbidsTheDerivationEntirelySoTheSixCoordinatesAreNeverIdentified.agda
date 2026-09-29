{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- Kernel.Vyabhicara_OneEnvironmentWhereItFailsForbidsTheDerivation
--                   EntirelySoTheSixCoordinatesAreNeverIdentified
--
-- TERM, AND THE SCHOOL IS NYYA, NAMED BEFORE THE TERM IS USED.
--
-- व्यभिचार · vyabhicāra -- straying, deviation.  A hetu that is found where
-- the sādhya is absent is सव्यभिचार, and Gautama's *Nyāyasūtra* (~2nd c. CE)
-- lists it first among the hetvbhsas and defines it in three words:
--
--     अनैकान्तिकः सव्यभिचारः     anaikāntikaḥ savyabhicāraḥ
--
-- GRETIL's `sa_gautama-nyAyasUtra.txt` (absent from this repository) line 204 reads `1.2.5:
-- anaikntika savyabhicra`, and line 200 is 1.2.4, the hetvbhsa
-- list.
--
-- The received placement is in the hetvbhsa passage of adhyya 1, pda 2.  The
-- definitional apparatus for vypti and its defeat is much later --
-- Gagea, *Tattvacintmai*, vyptivda (~1325).
-- `Vyapti_…` in this directory is the
-- sibling module and uses the same school's vocabulary.
--
-- AND THE DISPUTE, WHICH IS THE POINT AND MUST NOT BE FLATTENED.
--
-- Gautama's name for the fault is अनैकान्तिक · anaikāntika -- literally
-- not-one-endedness.  The Jainas' name for their central doctrine is
-- अनेकान्त · anekānta, the same root, and they mean it as the structure of
-- the real.  So the SAME CONFIGURATION -- a claim that holds under one
-- updhi and fails under another -- is for the Naiyyika a defect that
-- destroys the inference, and for the Jaina the first two bhagas of the
-- saptabhag, both determinate, both retained.  The Jaina logicians were
-- answering the charge that aneknta is merely anaikntika, at length, for
-- centuries; Akalaka and Vidynanda are where that argument lives.
--
-- §2 BELOW IS THE NAIYYIKA READING AND IT IS A THEOREM.  §3 exhibits the
-- same pair under both updhis, which is what the Jaina reading keeps.
-- NOTHING HERE ADJUDICATES BETWEEN THEM.  The two schools reject each
-- other's categories and this file does not blend them into one toolkit;
-- it states which reading each section is, and stops.
--
------------------------------------------------------------------------
-- THE COMMENT IN `RewriteCertificate`.
--
-- `RewriteCertificate` states a design rationale in a comment:
--
--     "Keeping all six coordinates distinct matters: identifying them
--      would prove only equality on the diagonal."
--
-- That is a claim about what this calculus CANNOT derive, and prose is not
-- a source for an absence.
-- §1 gives the general instrument in one line and §2 uses
-- it, so the comment becomes a checked non-existence.
--
------------------------------------------------------------------------
-- WHAT IS PROVED.
--
--   §1  vyabhicara -- ONE environment at which the meanings differ forbids
--       a derivation entirely.  It is `derivation-sound` read backwards,
--       and it is one line, which is the whole reason the kernel's
--       soundness quantifies over every ρ instead of holding at one.
--   §2  var is derivably identified with none of the other five
--       coordinates; and yvar with zvar, so the fact is not about `var`.
--   §3  the same pair, asti at one updhi and nsti at another, both
--       checked -- the configuration §2 reads as a fault.
------------------------------------------------------------------------

module Kernel.Vyabhicara_OneEnvironmentWhereItFailsForbidsTheDerivationEntirelySoTheSixCoordinatesAreNeverIdentified where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
import Cubical.Data.Empty as E

open import Kernel.RewriteCertificate

------------------------------------------------------------------------
-- §1.  THE INSTRUMENT.  `derivation-sound` says a derivation holds at
--      EVERY environment.  Contrapose it: deviation at ONE forbids the
--      derivation at all.  This is why the quantifier in the kernel's
--      soundness is where it is -- move it inside and `install` would
--      accept operations that are false off one point.
------------------------------------------------------------------------

vyabhicara : {a b : Tm} (ρ : Env)
           → (eval a ρ ≡ eval b ρ → E.⊥)
           → Derivation a b → E.⊥
vyabhicara ρ ne d = ne (derivation-sound d ρ)

------------------------------------------------------------------------
-- §2.  THE COMMENT IN `RewriteCertificate`, PROVED.  One environment
--      separates each pair: set the first coordinate to 0 and the second
--      to 1 and leave the rest anywhere.
------------------------------------------------------------------------

var≢yvar : Derivation var yvar → E.⊥
var≢yvar = vyabhicara (env 0 1 0 0 0 0) znots

var≢zvar : Derivation var zvar → E.⊥
var≢zvar = vyabhicara (env 0 0 1 0 0 0) znots

var≢uvar : Derivation var uvar → E.⊥
var≢uvar = vyabhicara (env 0 0 0 1 0 0) znots

var≢vvar : Derivation var vvar → E.⊥
var≢vvar = vyabhicara (env 0 0 0 0 1 0) znots

var≢wvar : Derivation var wvar → E.⊥
var≢wvar = vyabhicara (env 0 0 0 0 0 1) znots

-- and it is not a fact about `var`.
yvar≢zvar : Derivation yvar zvar → E.⊥
yvar≢zvar = vyabhicara (env 0 0 1 0 0 0) znots

------------------------------------------------------------------------
-- §3.  THE SAME PAIR UNDER BOTH UPDHIS.  §2 is the Naiyyika reading --
--      deviation, therefore no inference.  What the configuration itself
--      contains is this: a determinate holding, and a determinate failing,
--      of one claim about one pair, at two conditions.  Both are checked.
------------------------------------------------------------------------

asti : eval var (env 0 0 0 0 0 0) ≡ eval yvar (env 0 0 0 0 0 0)
asti = refl

nasti : eval var (env 0 1 0 0 0 0) ≡ eval yvar (env 0 1 0 0 0 0) → E.⊥
nasti = znots

-- Taken in succession those two are expressible by construction; taken
-- jointly they would be a square over a pair of environments, and this
-- calculus has no constructor for that.  Which of those two readings the
-- configuration deserves is the dispute named in the header, and is not
-- settled here.

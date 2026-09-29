{-# OPTIONS --cubical --guardedness --safe #-}

------------------------------------------------------------------------
-- परीक्षा — the examination of यन्त्र (944676e4), as terms rather than as
-- a review.  Four objections, each turned into something the kernel can
-- reject.
--
--   Chaya       944676e4's message says the collapse from the witnessed
--               Goldbach statement to the truncated one "exists while the
--               reverse provably does not."  The reverse map exists; the
--               SECTION does not.  Both are proved.
--
--   Pramanya    `Ganana`/`Ekam` decide primality with an unbacked `Bool`
--               and `Purna`/`Sakshi` decide it with a `Dec`, and nothing
--               joins them.  The bridge is supplied, and the Goldbach
--               sweep is rebuilt so its output is 49 certified
--               decompositions instead of the word `true`.
--
--   Kuttaka-    `Kuttaka` runs the descent law on a fuel constant
--   samapti     and proves nothing.  The fuel is removed by well-founded
--               recursion on the remainder, and the divisor comes back
--               carrying proofs that it divides both inputs.
--
--   Upadhi      `Shodhita`/`Ekam` call `|M(k)|² ≤ k` a fragment of the
--               Riemann Hypothesis.  It is the Mertens conjecture, which
--               was disproved in 1985.  The universal statement and the
--               finite check are separated into two types with a map in
--               one direction only.
------------------------------------------------------------------------

module PrimesCheck where

import Chaya_TheShadowHasNoSectionThoughItHasAMap
import Pramanya_TheBooleanCarriesNoWarrantSoTheSweepCarriesTheProof
import KuttakaSamapti_TheValliTerminatesWithoutFuel
import Qualifier_TheMertensGateIsTheDisprovedConjectureNotTheHypothesis

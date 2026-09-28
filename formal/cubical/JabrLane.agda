{-# OPTIONS --cubical --safe --no-import-sorts #-}

------------------------------------------------------------------------
-- JabrLane — a gate for modules whose named source tradition is the
-- Arabic algebraic one (al-Khwrizm, al-Karaj, al-Samawʾal).
--
-- ON THE NAME.  *al-jabr* is al-Khwrizm's own word, from the title of
-- *al-Kitb al-mukhtaar f isb al-jabr wa'l-muqbala* (c. 820 CE).
-- Like `ArchivistLane`, this file is a BUILD AGGREGATE: it states no
-- theorem and proves nothing.  The name says which tradition the modules
-- under it cite, not that al-Khwrizm proved them.
------------------------------------------------------------------------

module JabrLane where

------------------------------------------------------------------------
-- The antidiagonal sector pairing of an odd-character family: which
-- (ℤ/2)^k-isotypic sectors can pair at all.  Isolates the algebra of
-- collab/messages/goldbach-machine/direct-minor-shadow.md (absent from this repository) Thm 4.1 /
-- Prop 4.2 and mixed-sector-prescribed-center.md (absent from this repository) Thm 5.1 at k characters.
------------------------------------------------------------------------

import Muqabala_TheAntidiagonalSectorPairingIsSupportedOnConjugates

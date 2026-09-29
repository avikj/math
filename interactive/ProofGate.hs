-- ProofGate.hs — the Agda emitter for the kernel gate.
--
-- LEGACY POINTER (2026-08-23).  MathMachine.hs — "the CLOSE-lane
-- ℕ-equation spinner", 239 rounds / ZERO theorems installed — was RETIRED
-- at commit 832a549 as a toy that "looks alive but isn't".  ProofGate.hs
-- is one of the four organs the commit records as SURVIVING it (with
-- Certify.hs, ArithVocab.hs, library.terms); the live substrate is the
-- cubical corpus + the crystal runtime, and candidate generation is now
-- the endogenous frontier (Sanghatta critical pairs, Obstruction's kernel
-- obligation stream). The MathMachine references below are the historical
-- record of what this emitter was built against; read them past tense.
--
-- WHAT THIS REPLACES, AND WHY (retained as the emitter's design record)
--
-- MathMachine.hs [RETIRED, 832a549] proved equations with its own
-- rewriting + structural induction, then submitted each one to
-- `kernelAccept`, which emits a candidate Agda module and typechecks it.
-- The emitter it used (`agdaCertificate`, MathMachine.hs ~1193) was
--
--     candidate : (x y z u v w : ℕ) → LHS ≡ RHS
--     candidate x y z u v w = refl
--
-- Three separate faults make that gate reject everything.  All three were
-- reproduced directly (see the notes on each below); this module fixes all
-- three.
--
--   (1) LIBRARY RESOLUTION.  The engine runs
--
--           agda -i formal/cubical -i <tmpdir> <tmpdir>/Candidate.agda
--
--       from the repository root.  `formal/cubical` is NOT the cubical
--       library — it is the NaturalMachine lane, and it carries
--       `natural-machine.agda-lib` (`depend: cubical`).  The cubical
--       library itself lives at /tmp/cubical and is reachable only through
--       ~/.agda/libraries.  Agda finds a library only by walking up from
--       the *checked file* to an .agda-lib; a module in a temp directory
--       has none, so `Cubical.Foundations.Prelude` is unresolvable and the
--       candidate dies at scope-checking, before any proof term is looked
--       at.  Reproduced with the engine's own positive control:
--
--           $ LC_ALL=C.UTF-8 ./math-machine --kernel-self-test
--             KERNEL-REJECT round=0 (0+x) = x  ... Failed to find source
--             of module Cubical.Fou...
--
--       i.e. the gate rejects `0 + x ≡ x`.  Zero KERNEL-ACCEPTs was never
--       a statement about the emitter's expressiveness; nothing could pass.
--       Fixed here by `kAgdaLibrary` / `agdaArgs`, which add
--       `--library=cubical` to the otherwise identical invocation.
--
--   (2) FILE ENCODING.  `kernelAccept` writes the candidate with plain
--       `writeFile`, which uses the locale encoding.  Without a UTF-8
--       locale in the machine's own environment this throws before agda is
--       ever spawned:
--
--           mm: /tmp/math-machine-agda.pXe4qi/Candidate.agda: withFile:
--               invalid argument (cannot encode character '\8469')
--
--       Fixed here by `writeUtf8`, which sets the handle encoding
--       explicitly rather than trusting the ambient locale, and by
--       forcing LC_ALL in the agda child's environment.
--
--   (3) EXPRESSIVENESS, the fault the seam was actually designed around.
--       `agdaTerm` knew only 0, s, + and · — four of the eight symbols in
--       `vocabulary` — and the only proof shape was `refl`, so nothing
--       needing induction could be certified.  Both are addressed below.
--
-- FAITHFULNESS (the load-bearing point)
--
-- A certificate about a different function is worse than no certificate.
-- Each symbol below is either an Agda function that is clause-for-clause
-- the same recursion as the corresponding `symDefs` in MathMachine's
-- `vocabulary`, or a local definition transcribed from those `symDefs`:
--
--   0, s     zero, suc                                     (identical)
--   +        Agda.Builtin.Nat._+_  via Cubical.Data.Nat     (see note A)
--   *        Agda.Builtin.Nat._*_  via Cubical.Data.Nat     (see note A)
--   -        Agda.Builtin.Nat._-_ = _∸_ via Cubical.Data.Nat
--            machine: -x0=x, -0x=0, -(sx)(sy)=-xy
--            builtin:  n-zero=n, zero-suc m=zero, suc n-suc m=n-m
--            — same clauses, same order.  Exact match.
--   max      LOCAL.  Cubical's `max` (Cubical.Data.Nat.Properties) is the
--            same function but splits on the FIRST argument, whereas
--            MathMachine's symDefs are (max x 0 = x), (max 0 x = x),
--            (max (s x) (s y) = s (max x y)) — first clause on the second
--            argument.  Emitted locally in the machine's clause order so
--            the machine's own reductions are available (see note B).
--   le       LOCAL.  Cubical has no ℕ-valued ≤ test.  Transcribed from
--            symDefs: le 0 x = s 0, le (s x) 0 = 0, le (s x) (s y) = le x y.
--            Agrees with `symSem` (\vs -> if a <= b then 1 else 0).
--   gcd      Cubical.Data.Nat.GCD.gcd.  Same function as Haskell `gcd` on
--            ℕ (both are the ≡-unique greatest common divisor, gcd 0 0 = 0),
--            but it is defined through `euclid` and reduces on no open
--            term, so gcd equations will essentially never certify.  It is
--            translated anyway: a KERNEL-REJECT carrying agda's message is
--            more informative than a KERNEL-SKIP.
--
-- Note A.  Agda's `+` and `·` recurse on the FIRST argument; MathMachine's
-- symDefs recurse on the second (x+0=x, x+s y = s(x+y)).  These are the
-- same function on ℕ — the machine's `symSem` is Haskell's (+) and (*),
-- and the cubical/builtin operations are ordinary ℕ addition and
-- multiplication — so the certificate is about the right object.  The
-- clause order differs only in which equations hold *definitionally*, and
-- the first-argument order was measured to certify strictly more of the
-- machine's library than a transcription of the symDefs would (it makes
-- (s x + y) = s (x + y) and (s x · y) = y + x · y refl, which the
-- second-argument order does not).
--
-- Note B.  No Agda case tree reproduces MathMachine's `max` reductions
-- exactly: the machine uses (max x 0 = x) and (max 0 x = x) as
-- unconditional rewrite rules in BOTH argument positions, while a case
-- tree must commit to splitting one column first.  The local definition
-- here matches the symDefs clause list literally; what it cannot match is
-- the machine's rewriting being stronger than pattern matching.  This is a
-- real residual gap and it is why `(x max s 0) = (s 0 max x)` does not
-- certify (see `main`'s report).
--
-- INVOCATION BUDGET
--
-- Trying several proof shapes means calling agda more than once per
-- candidate.  That is bounded and explicit: `kMaxAgdaCalls`.  The order is
-- always cheapest-first — a plain `refl` module (one call), then the
-- induction skeleton with step shapes from `stepShapes`.  If the *base*
-- clause is what agda rejects, the remaining step shapes cannot help, so
-- the search stops there (`baseClauseFailed`); a false equation therefore
-- costs 2 calls, not `kMaxAgdaCalls`.
--
-- A candidate whose proof note names NO induction variable used to cost 1
-- call and be rejected, always — the emitter emitted no induction module for
-- it at all.  That is the traffic the engine's residual seam carries, since a
-- subgoal harvested from the kernel's own stall arrives unannotated.  Such a
-- candidate now gets the same shape menu once per variable, bounded by
-- `kMaxAgdaCallsUnannotated`, and the annotated case is unchanged in reach,
-- in shape and in budget.  Measured on `interactive/library.snapshot.txt` with
-- every note stripped — which is exactly the shape a residual arrives in —
-- by `interactive/SesaPariksa_WhichOfTheSixOutstandingDemandsInductionReaches.hs`
-- on 2026-08-20:
--
--     note-less, before:  5/28 certified, 28 agda calls   (derived, exactly:
--                         only the `refl` lines could close)
--     note-less, after : 15/28 certified, 144 agda calls  (measured)
--     annotated, after : 15/28 certified, 123 agda calls  (measured,
--                        byte-identical to the run before the change)
--
-- So the annotation is no longer load-bearing for REACH; it is worth 21 agda
-- calls over the snapshot, and the whole of the difference is search the note
-- would have skipped.
--
-- THE CERTIFICATE CACHE (added 2026-08-16)
--
-- The gate's wall clock is one agda process per emitted module, ~1-3 s
-- each, almost all of it re-loading library interfaces.  The engine
-- re-derives and re-submits the same equations across rounds and across
-- runs, so it re-pays that cost for modules it has already checked.  The
-- cache below removes exactly that repetition and nothing else.
--
-- WHAT IS KEYED.  The unit is ONE EMITTED MODULE, not one conclusion.  The
-- module source is the complete input to agda — it already encodes the
-- conclusion, the concept definitions, the vocabulary transcriptions
-- (`localMax`, `localLe`), the imports, and the proof skeleton — so hashing
-- it is hashing everything the verdict depends on inside this process.
-- Keying per module rather than per conclusion also means the search in
-- `certifyWith` reuses its own intermediate failures: a rejected shape that
-- cost a call last time costs none this time.
--
-- The key is a 128-bit FNV-1a hash of the UTF-8 bytes of
-- `toolchain ++ "\0" ++ source`, where `toolchain` is the output of
-- `agda --version` together with `kAgdaLibrary` and `kIncludeRoot`.  The
-- toolchain is in the key because a verdict is a fact about a source AND a
-- checker: upgrading agda must miss, not falsely hit.  What is still NOT in
-- the key is the content of the cubical library itself and of
-- `formal/cubical/`; editing those can in principle change a verdict
-- without changing the key.  That is a real residual and it is why
-- `MATH_CERTCACHE=0` exists (it bypasses the cache entirely, for a clean
-- re-measurement or after a library edit).
--
-- THE HASH IS ONLY AN INDEX.  Every entry stores the full source it was
-- built from, and `lookupCache` compares that stored source to the
-- requested source byte for byte before returning a verdict.  A hash
-- collision therefore produces a MISS, never a wrong answer; the hash's job
-- is to name a file, not to stand in for the content.
--
-- WHAT IS STORED.  `interactive/.certcache/<key>`, one small UTF-8 file:
-- the verdict word, agda's exit code, the toolchain string, agda's output
-- verbatim, and the module source.  A reader can copy the SOURCE block into
-- a file and re-run agda on it; that is the point of storing it.
--
-- WHAT IS NOT STORED.
--
--   * `Untranslatable` is never cached.  It is a property of the emitter --
--     `agdaTermWith` returned Nothing -- and no agda process is involved,
--     so there is nothing to memoise and caching it would freeze an
--     emitter limitation into a file that outlives the emitter.
--
--   * A REJECTION IS CACHED ONLY WHEN IT IS A GENUINE TYPE ERROR
--     (`cacheableFailure`).  This is the decision requirement (e) asks for,
--     and the reasoning is: exit 0 can only mean "agda typechecked this
--     module", so success is always cacheable; a non-zero exit means
--     nothing on its own, because a missing library, a locale fault, an
--     absent `formal/cubical`, or a killed process all produce one.
--     Caching those would turn a transient environment fault into a
--     permanent verdict — the failure mode this whole file was written to
--     fix (see fault (1) above: a path error was recorded as a
--     KERNEL-REJECT indistinguishable from a false statement).  So a
--     failure is cached only if agda located the error inside
--     Candidate.agda AND the message carries a type-error signature AND no
--     environment-failure marker appears.  Everything else is re-run.
--
-- HOW A HIT IS REPORTED.  A cached run spends 0 agda calls, and that 0 is
-- what the `Verdict` carries; the shape string is prefixed `cached, ` (and
-- a cached rejection's message `cached: `) so no log line and no
-- measurement can read a cache hit as fresh kernel work.  If a search mixes
-- hits and fresh calls the count is the number of FRESH calls, and the
-- label is not marked cached — the run did do kernel work.
--
-- IDENTIFIER VALIDATION (added 2026-08-16)
--
-- `defName` was the one candidate-supplied string that reached the emitted
-- module verbatim, in three positions.  It is now checked against
-- [A-Za-z_][A-Za-z0-9_]* at each of them, and a candidate carrying an
-- ill-formed name produces NO MODULE (`Untranslatable`, 0 agda calls) rather
-- than an emitted module that agda then declines.  See `validAgdaIdent` for
-- what was reproducible before the check, including the case that made three
-- different right-hand sides certify against one left-hand side.
--
-- This module deliberately has no dependency on MathMachine: it carries
-- its own copy of the Term type so it can be compiled, run and tested on
-- its own.  `main` is that test.  From the repository root:
--
--     ghc -O0 -Wall -main-is ProofGate.main \
--         -outputdir /tmp/cert-build -o /tmp/cert interactive/ProofGate.hs
--     /tmp/cert            # or: /tmp/cert <repository-root>
--
-- It takes about 100 seconds and prints one line per equation.  Result at
-- the time of writing: 15 of the 28 lines of interactive/library.snapshot.txt
-- certify, 13 are rejected with agda's reason, none are untranslatable,
-- and four deliberate falsehoods are all rejected.  Every one of the 13
-- rejections is a commutativity- or associativity-shaped statement whose
-- BASE case is itself a lemma (y ≢ y + zero definitionally); closing them
-- needs a lemma environment — certificates emitted in dependency order,
-- with earlier theorems in scope for later ones — not more step shapes.

module ProofGate
  ( -- * terms
    Term(..)
  , Equation
  , varsOf
  , symbolsOf
    -- * translation
  , Definition(..)
  , agdaTerm
  , agdaTermWith
  , agdaVar
  , validAgdaIdent
  , agdaReserved
  , definitionsSafe
  , preamble
  , preambleWith
    -- * certificates
  , agdaCertificate
  , agdaCertificateWith
  , agdaInductionCertificate
  , agdaSolverCertificate
  , agdaSolverPeelCertificate
  , peelSuc
  , inductionVariable
  , stepShapes
  , citingStepShapes
  , solverShapes
    -- * policy
  , kMaxAgdaCalls
  , kMaxAgdaCallsUnannotated
  , kMaxCongArguments
  , kMaxInductionVariables
  , kAgdaLibrary
  , kIncludeRoot
  , agdaArgs
  , agdaArgsWith
  , corpusIncludeRoots
    -- * running
  , Verdict(..)
  , certify
  , certifyWith
  , runAgda
  , runAgdaUnwatched
  , runAgdaModule
  , Analysis(..)
  , runAgdaAnalyze
  , vetSuccess
  , vetForeignRun
  , main
    -- * the two controls (a kernel that accepts a falsehood is not a kernel)
  , kernelIsChecking
  , KernelStatus(..)
  , kernelStatus
  , kOptionsPragma
  , canaryTrue
  , canaryFalse
  , successHidesAnError
  , kEnvironmentFault
  , kAgdaTimeoutMicros
  , agdaTimeoutMicros
    -- * the certificate cache (content-addressed, one file per module)
  , kCertCacheDir
  , cacheEnabled
  , cacheKey
  , toolchainIdentity
  , cacheableFailure
  , runAgdaCached
    -- * serialisable certificates + replay (the re-checkable ledger)
  , ProofWitness(..)
  , SerialCert(..)
  , mkSerialCert
  , serTerm
  , parseSerTerm
  , serializeCert
  , parseSerialCert
  , reconstructModule
  , certifyCert
  , replayCert
    -- * reading interactive/library.txt
  , parseShowTerm
  , parseLibraryLine
  ) where

import Control.Exception (SomeException, finally, try)
import Data.Bits (shiftR, xor, (.&.), (.|.))
import Data.Char (isAlphaNum, isDigit, isSpace, ord, toLower)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (foldl', intercalate, isInfixOf, isPrefixOf, nub, sort)
import Data.Maybe (isJust, mapMaybe)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Word (Word64)
import GHC.IO.Encoding (setLocaleEncoding)
import System.Environment (getArgs, getEnvironment, lookupEnv)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.FilePath ((</>))
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import System.Directory
  ( createDirectoryIfMissing, doesFileExist, getTemporaryDirectory
  , removePathForcibly, renameFile, makeAbsolute )
import System.Timeout (timeout)
import System.Process
  (CreateProcess(..), proc, readProcess, readCreateProcessWithExitCode)
import Text.Printf (printf)

-- ------------------------------------------------------------------ terms
--
-- Mirrors MathMachine's `data Term = V !Int | F !String [Term]`.  Kept
-- separate on purpose: this module must be compilable and testable without
-- the engine.  The seam adapts one to the other.

data Term = V !Int | F !String [Term] deriving (Eq, Ord, Show)

type Equation = (Term, Term)

varsOf :: Term -> [Int]
varsOf (V i) = [i]
varsOf (F _ ts) = concatMap varsOf ts

symbolsOf :: Term -> [String]
symbolsOf (V _) = []
symbolsOf (F f ts) = f : concatMap symbolsOf ts

equationVars :: Equation -> [Int]
equationVars (l, r) = sort (nub (varsOf l ++ varsOf r))

equationSymbols :: Equation -> [String]
equationSymbols (l, r) = nub (symbolsOf l ++ symbolsOf r)

-- ------------------------------------------------------------ translation

-- The six universe names, matching MathMachine's Show instance for terms
-- so that log lines and certificates talk about the same variables.
agdaVar :: Int -> Maybe String
agdaVar i
  | i >= 0 && i < 6 = Just ["xyzuvw" !! i]
  | otherwise = Nothing

-- A concept the machine named for itself.  `inventConcept`
-- (MathMachine.hs ~1478) builds `Sym nm ar (\args -> eval sem args p)`
-- with the single defining equation (p, cN x0 … x_{ar-1}); so the Agda
-- transcription is `cN a0 … a_{ar-1} = p[V i := a_i]`, which is what
-- `preambleWith` emits.  Without this an invented symbol is a
-- KERNEL-SKIP, and concept invention is the machine's main growth axis.
data Definition = Definition
  { defName :: String   -- ^ the machine's name for it, e.g. "c0"
  , defArity :: Int
  , defBody :: Term     -- ^ body, over variables V 0 .. V (defArity - 1)
  } deriving (Eq, Show)

-- ------------------------------------------------- identifier validation
--
-- §(1), both 2026-08-16).
--
-- `defName` is the ONLY candidate-supplied string that reaches the emitted
-- module, and until this predicate existed it reached it VERBATIM in three
-- positions: the definition's signature line and its clause line (`emit` in
-- `preambleWith`), and every occurrence of the concept inside the equation's
-- own type (`prefixAgda`, via the `lookupDef` fallback in `render`).  A name
-- is not a token to the emitter, it is a string, so a name may contain
-- anything — including newlines.  Two consequences were reproduced against
-- this very file:
--
--   * a name containing "\n{-# OPTIONS --no-safe #-}\npostulate evil : …"
--     put that pragma and that postulate into `Candidate.agda` verbatim
--     (harmless in the end: the injection lands after the module header, so
--     the pragma is ignored, `--safe` stays locked at line 1, and the
--     postulate is refused — verdict `Rejected`); and
--
--   * `injName = "suc x) ≡ (suc x) -- "` is worse and is NOT harmless: it
--     closes the emitter's own parenthesis and comments out the rest of the
--     line, so the module agda checks is `candidate : (x : ℕ) → (suc x) ≡
--     (suc x)`, whatever right-hand side was submitted.  GateAudit obtained
--     `Certified "refl" 1` for three DIFFERENT right-hand sides over one
--     left-hand side (GateAudit.hs:100–109).  That is a soundness break, not
--     a defense-in-depth gap.
--
-- Neither was reachable from the engine, because `inventConcept`
-- (MathMachine.hs:1547) names concepts `"c" ++ show n`.  That is safety by
-- CALLER CONVENTION: the gate did no validation and the convention is not
-- stated in any type.  It is now enforced here, at the emission site, and
-- the enforcement FAILS CLOSED — an offending name yields no module at all
-- (`Nothing` → `Untranslatable`), never an emitted module that agda is asked
-- to have an opinion about.  A candidate the emitter cannot render honestly
-- is a rejected candidate.
--
-- The grammar is the audit's: [A-Za-z_][A-Za-z0-9_]*, ASCII by construction
-- and not via `isAlpha`/`isAlphaNum`, whose Unicode generality would readmit
-- characters Agda's lexer treats specially.  Every character of a legal name
-- is one Agda lexes as part of a single identifier token, so a legal name
-- cannot close a parenthesis, open a comment, start a pragma, or reach the
-- next line — the three positions become splice-proof rather than
-- splice-audited.
validAgdaIdent :: String -> Bool
validAgdaIdent s = case s of
  [] -> False
  (c : cs) -> identStart c && all identRest cs && notElem s agdaReserved
  where
    identStart c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
    identRest c = identStart c || (c >= '0' && c <= '9')

-- Strengthening beyond the audit's regex, at no cost to any real name: the
-- regex alone admits `where`, `module`, `postulate`, `data` …, which lex as
-- KEYWORDS rather than identifiers and so would still restructure the module
-- (they cannot make a false equation check — `--safe` is untouched at line 1
-- and postulates are refused — but a name that changes the module's grammar
-- has no business reaching agda).  `candidate` is in the list because it is
-- the name the emitter gives the theorem itself.
agdaReserved :: [String]
agdaReserved =
  [ "abstract", "candidate", "codata", "coinductive", "constructor", "data"
  , "do", "eta_equality", "field", "forall", "hiding", "import", "in"
  , "inductive", "infix", "infixl", "infixr", "instance", "interleaved"
  , "let", "macro", "module", "mutual", "no_eta_equality", "open", "opaque"
  , "overlap", "pattern", "postulate", "primitive", "private", "public"
  , "quote", "quoteTerm", "record", "renaming", "rewrite", "syntax", "tactic"
  , "unquote", "unquoteDecl", "using", "variable", "where", "with"
  , "Set", "Prop", "Setω"
  ]

-- The gate's precondition on a definition list, checked once per candidate
-- before anything is rendered.  ALL supplied names, not merely the ones the
-- equation happens to mention: a caller that can name one concept
-- adversarially can name the one the equation uses, and there is no reason
-- to make the verdict depend on which of its concepts a candidate chose to
-- exercise.
definitionsSafe :: [Definition] -> Bool
definitionsSafe = all (validAgdaIdent . defName)

-- Every symbol of MathMachine's `vocabulary` (0 s + * max - gcd le), plus
-- whatever invented concepts the caller supplies.  Anything else — the
-- eigenconstant #, an unsupplied concept — returns Nothing, which the
-- caller reports as untranslatable.
agdaTerm :: Term -> Maybe String
agdaTerm = agdaTermWith []

agdaTermWith :: [Definition] -> Term -> Maybe String
agdaTermWith defs = render defs agdaVar

-- `nameOf` is how variables are spelled: the candidate's own variables are
-- x y z u v w, a local definition's parameters are a0 a1 ….
render :: [Definition] -> (Int -> Maybe String) -> Term -> Maybe String
render defs nameOf = go
  where
    go (V i) = nameOf i
    go (F "0" []) = Just "zero"
    go (F "s" [t]) = (\u -> "(suc " ++ u ++ ")") <$> go t
    go (F "+" [a, b]) = infixAgda go "+" a b
    go (F "*" [a, b]) = infixAgda go "·" a b
    go (F "-" [a, b]) = infixAgda go "∸" a b
    go (F "max" [a, b]) = prefixAgda go "max" [a, b]
    go (F "le" [a, b]) = prefixAgda go "le" [a, b]
    go (F "gcd" [a, b]) = prefixAgda go "gcd" [a, b]
    go (F f as)
      | Just d <- lookupDef defs f, defArity d == length as =
          prefixAgda go f as
    go _ = Nothing

-- EMISSION SITE 1 (terms).  Every path by which a concept name reaches the
-- rendered module goes through here — `render`'s fallback clause, which then
-- calls `prefixAgda` and splices the name into the candidate's type; and
-- `preambleWith`'s `closure`, which decides which definitions get emitted at
-- all.  Refusing to resolve an ill-formed name therefore removes it from
-- both, and `render` falls through to `Nothing`: untranslatable, no module.
lookupDef :: [Definition] -> String -> Maybe Definition
lookupDef defs f
  | not (validAgdaIdent f) = Nothing
  | otherwise = case [ d | d <- defs, defName d == f ] of
      (d : _) -> Just d
      [] -> Nothing

infixAgda :: (Term -> Maybe String) -> String -> Term -> Term -> Maybe String
infixAgda go op a b = do
  x <- go a
  y <- go b
  pure ("(" ++ x ++ " " ++ op ++ " " ++ y ++ ")")

prefixAgda :: (Term -> Maybe String) -> String -> [Term] -> Maybe String
prefixAgda go f as = do
  xs <- mapM go as
  pure ("(" ++ unwords (f : xs) ++ ")")

-- Parameter names for a local definition's own clause.  Deliberately not
-- x y z u v w: those name the candidate's universally quantified
-- variables and a local definition must not appear to capture them.
defVar :: Int -> Maybe String
defVar i | i >= 0 = Just ("a" ++ show i)
         | otherwise = Nothing

-- Imports and local definitions are demand-driven: a candidate that never
-- mentions gcd must not pay for typechecking Cubical.Data.Nat.GCD (which
-- roughly triples the cost of a call).
preamble :: [String] -> [String]
preamble = preambleWith []

preambleWith :: [Definition] -> [String] -> [String]
preambleWith defs syms =
  preambleCore (syms ++ concatMap (symbolsOf . defBody) used)
    ++ concatMap emit used
  where
    -- transitive: c1's body may mention c0, and Agda needs c0 first.
    used = [ d | d <- defs, defName d `elem` closure ]
    closure = grow (filter (isJust . lookupDef defs) syms)
    grow seen =
      let more = nub (seen ++ [ f | s <- seen
                                  , Just d <- [lookupDef defs s]
                                  , f <- symbolsOf (defBody d)
                                  , isJust (lookupDef defs f) ])
      in if length more == length seen then seen else grow more
    -- EMISSION SITE 2 (the preamble): the signature line and the clause
    -- line, the two places a name is written as Agda source rather than
    -- used as a term.  The `validAgdaIdent` guard is redundant given
    -- `lookupDef` above — an ill-formed name cannot enter `closure`, hence
    -- cannot enter `used` — and it is kept anyway, because this is where the
    -- string actually becomes source and a future refactor of `closure`
    -- must not be able to reopen the channel silently.
    emit d
      | not (validAgdaIdent (defName d)) = []
    emit d =
      case render defs defVar (defBody d) of
        Nothing -> []   -- an untranslatable body drops the definition, so
                        -- the candidate fails to scope-check rather than
                        -- silently meaning something else
        Just body ->
          [ defName d ++ " : " ++ concat (replicate (defArity d) "ℕ → ") ++ "ℕ"
          , unwords (defName d : params) ++ " = " ++ body
          ]
      where
        params = mapMaybe defVar [0 .. defArity d - 1]

-- THE OPTIONS LINE, WRITTEN ONCE.
--
-- It was written twice — here and in `canaryModule` — and the two copies
-- drifted: the candidate modules carried `--guardedness`, the controls did
-- not.  That is not a cosmetic difference.  Agda's `[InfectiveImport]` rule
-- makes `--guardedness` propagate through imports, so under a cubical library
-- compiled with it (Agda 2.8.0 + the Homebrew cubical build, measured
-- 2026-08-20) a module that opens `Cubical.Foundations.Prelude` WITHOUT
-- `--guardedness` fails at scope-checking, before any proof term is looked at:
--
--     error: [InfectiveImport]
--     Importing module Cubical.Foundations.Prelude using the
--     --guardedness flag from a module which does not.
--
-- `canaryTrue` therefore failed for a reason that has nothing to do with the
-- kernel's ability to check proofs, `kernelIsChecking` returned False, and
-- `vetSuccess` downgraded EVERY acceptance to an environment fault.  Measured
-- reach on that container: 0/28, where the same binary with the pragmas
-- agreeing gets 15/28.  The negative verdict was correct and the reason given
-- for it was invented, which is not.
--
-- Sharing the string is the mechanism.  A control module that is not compiled
-- the way the candidate modules are compiled is not a control for them, and
-- the only way to keep that true under future edits is for there to be one
-- string.
kOptionsPragma :: String
kOptionsPragma = "{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}"

preambleCore :: [String] -> [String]
preambleCore syms =
  [ kOptionsPragma
  , "module Candidate where"
  , "open import Cubical.Foundations.Prelude"
  -- _+_, _·_ and _∸_ come in unconditionally even when the equation does
  -- not mention them: the step shapes in `stepShapes` build sections like
  -- (y +_) and (_· k), and an operator that is not in scope makes the
  -- module fail to PARSE rather than to typecheck — which burns an
  -- invocation and reports a syntax error where the real answer is "that
  -- shape does not apply".  They all live in the module being opened
  -- anyway, so naming them costs nothing.
  , "open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; _∸_)"
  ]
  ++ [ "open import Cubical.Data.Nat.GCD using (gcd)" | need "gcd" ]
  ++ localMax
  ++ localLe
  ++ localMaxZeroL
  ++ localMinusZeroL
  where
    need s = s `elem` syms
    -- transcribed from vocabulary's symDefs for "max", in that order
    localMax
      | need "max" =
          [ "max : ℕ → ℕ → ℕ"
          , "max a zero = a"
          , "max zero b = b"
          , "max (suc a) (suc b) = suc (max a b)"
          ]
      | otherwise = []
    -- transcribed from vocabulary's symDefs for "le", in that order
    localLe
      | need "le" =
          [ "le : ℕ → ℕ → ℕ"
          , "le zero b = suc zero"
          , "le (suc a) zero = zero"
          , "le (suc a) (suc b) = le a b"
          ]
      | otherwise = []
    -- CLAUSE-COMPLETION LEMMAS (anuvtti, Adhyy 4.45): a theorem proved
    -- once, carried into scope for the candidate that needs it.  `max zero n`
    -- and `zero ∸ n` are STUCK terms — the first clause of `max` (max a zero)
    -- and of `_∸_` (n ∸ zero) blocks on a variable in the second argument, so
    -- neither reduces and no step shape over `refl`/`cong`/`ih` can close a
    -- goal that mentions them.  These two lemmas ARE those clauses completed,
    -- each proved by induction with both cases `refl`; the citing step shapes
    -- in `citingStepShapes` discharge the goal with `sym (…)`.  This is the
    -- lemma environment ProofGate.hs:238-240 named, realised as a fixed,
    -- bounded, in-scope set rather than an unbounded dependency-ordered search.
    localMaxZeroL
      | need "max" =
          [ "maxZeroL : (n : ℕ) → max zero n ≡ n"
          , "maxZeroL zero = refl"
          , "maxZeroL (suc n) = refl"
          ]
      | otherwise = []
    localMinusZeroL
      | need "-" =
          [ "minusZeroL : (n : ℕ) → zero ∸ n ≡ zero"
          , "minusZeroL zero = refl"
          , "minusZeroL (suc n) = refl"
          ]
      | otherwise = []

-- ----------------------------------------------------------- certificates

-- The fast case, and the only case the old emitter had: an equation true
-- by definitional unfolding.
agdaCertificate :: Equation -> Maybe String
agdaCertificate = agdaCertificateWith []

-- EMISSION SITE 3 (the module as a whole), and the fail-closed one.  Sites 1
-- and 2 already make an ill-formed name unrenderable; this guard makes the
-- candidate carrying it unemittable, so the failure is a REJECTED CANDIDATE
-- and not a module that agda is asked to have an opinion about.  The
-- distinction is the whole point of the fix: `Rejected` after 8 agda calls
-- means agda examined an injected module and disliked it, which is a fact
-- about agda; `Untranslatable` with 0 calls means the gate never emitted
-- one, which is a fact about the gate.  Only the second is a property this
-- file can guarantee.
agdaCertificateWith :: [Definition] -> Equation -> Maybe String
agdaCertificateWith defs _ | not (definitionsSafe defs) = Nothing
agdaCertificateWith defs eq@(l, r) = do
  lhs <- agdaTermWith defs l
  rhs <- agdaTermWith defs r
  names <- mapM agdaVar (equationVars eq)
  pure $ unlines $
    preambleWith defs (equationSymbols eq)
    ++ [ "candidate : " ++ telescope names ++ lhs ++ " ≡ " ++ rhs
       , "candidate " ++ unwords names ++ " = refl"
       ]

telescope :: [String] -> String
telescope [] = ""
telescope ns = "(" ++ unwords ns ++ " : ℕ) → "

-- The induction skeleton.  Returns the module source and the 1-based line
-- number of the base clause, so a base-clause failure can be told apart
-- from a step-clause failure without rerunning anything.
agdaInductionCertificate :: [Definition] -> Equation -> Int -> String
                         -> Maybe (String, Int)
-- Same fail-closed guard as `agdaCertificateWith`; see EMISSION SITE 3.  It
-- is repeated rather than factored because these are the two functions that
-- turn a candidate into a file, and each must be safe when read alone.
agdaInductionCertificate defs _ _ _ | not (definitionsSafe defs) = Nothing
agdaInductionCertificate defs eq@(l, r) v step = do
  lhs <- agdaTermWith defs l
  rhs <- agdaTermWith defs r
  let vs = equationVars eq
  nv <- agdaVar v
  if v `notElem` vs then Nothing else do
    names <- mapM agdaVar vs
    let pre = preambleWith defs (equationSymbols eq)
        sig = "candidate : " ++ telescope names ++ lhs ++ " ≡ " ++ rhs
        pat u = unwords [ if i == v then u else n | (i, n) <- zip vs names ]
        baseC = "candidate " ++ pat "zero" ++ " = refl"
        stepC = "candidate " ++ pat ("(suc " ++ nv ++ ")") ++ " = " ++ step
        baseLine = length pre + 2
    pure (unlines (pre ++ [sig, baseC, stepC]), baseLine)

-- A NON-INDUCTIVE certificate: hand the whole telescoped equation to a
-- reflection semiring solver (Cubical.Tactics.NatSolver), used point-free
-- as `candidate = <macro>`.  This closes the commutativity/associativity/
-- distributivity class that ProofGate.hs:238-240 named as needing "a lemma
-- environment ... not more step shapes": those thirteen rejections are all
-- ℕ-semiring identities whose base case is itself a lemma (y ≢ y + zero
-- definitionally), and a semiring solver is the decision procedure for
-- exactly that class.  It is SOUND because the macro emits a proof term the
-- kernel checks under the candidate's own pragmas — probed 2026-08-24: it
-- discharges (x + y) ≡ (y + x) (rc 0) and DENIES (x + y) ≡ (x · y) (rc 1) —
-- so it is not a trusted oracle, and the two watched controls in the caller
-- are unaffected.  `imp` and `body` are supplied by `solverShapes` because
-- the macro's import path and name differ by cubical version.
agdaSolverCertificate :: [Definition] -> Equation -> String -> String
                      -> Maybe String
agdaSolverCertificate defs _ _ _ | not (definitionsSafe defs) = Nothing
agdaSolverCertificate defs eq@(l, r) imp body = do
  lhs <- agdaTermWith defs l
  rhs <- agdaTermWith defs r
  names <- mapM agdaVar (equationVars eq)
  -- The v0.9 macro parses only a BARE equation goal: a telescoped type is
  -- "failed to parse the goal" (probed 2026-08-29).  The library's own
  -- Examples.agda binds the variables with a module telescope and leaves
  -- the goal bare; emitted here the same way, `candidate` still has the
  -- telescoped type from outside the anonymous module, so nothing
  -- downstream changes.
  pure $ unlines $
    preambleWith defs (equationSymbols eq)
    ++ [ imp ]
    ++ (if null names
          then [ "candidate : " ++ lhs ++ " ≡ " ++ rhs
               , "candidate = " ++ body ]
          else [ "module _ " ++ concatMap (\v -> "(" ++ v ++ " : ℕ) ") names ++ "where"
               , "  candidate : " ++ lhs ++ " ≡ " ++ rhs
               , "  candidate = " ++ body ])

-- The solver shapes, in order, each an (label, import line, macro name).
-- Both cubical versions the corpus meets are covered so the shape survives
-- the toolchain skew that fibered VargaPrakrtiWitness109: v0.5 exposes the
-- hole macro as `Cubical.Tactics.NatSolver.Reflection.solve`; v0.9 renamed
-- it `solveℕ!` and re-exported it from the aggregator `Cubical.Tactics
-- .NatSolver`.  Only one import resolves per toolchain; the other fails with
-- "Failed to find source of module" — an ordinary rejection, not an
-- environment fault — so the search simply moves to the next shape.
solverShapes :: [(String, String, String)]
solverShapes =
  [ ( "solve"
    , "open import Cubical.Tactics.NatSolver.Reflection using (solve)"
    , "solve" )
  , ( "solveℕ!"
    , "open import Cubical.Tactics.NatSolver using (solveℕ!)"
    , "solveℕ!" )
  ]

-- Peel matching leading `suc` constructors off both sides.  `suc E` is
-- `F "s" [E]`; the count returned is how many peeled, and the equation is the
-- common core.  A goal `sucᵏ E₁ ≡ sucᵏ E₂` is closed by `(cong suc)ᵏ` applied
-- to a proof of `E₁ ≡ E₂`, so peeling lets the semiring solver reach a core
-- it could not see under the constructors.
peelSuc :: Equation -> (Int, Equation)
peelSuc (F "s" [a], F "s" [b]) = let (k, e) = peelSuc (a, b) in (k + 1, e)
peelSuc eq = (0, eq)

-- A solver certificate for a `suc`-wrapped semiring identity: peel k leading
-- `suc`s, prove the core with the solver in a telescoped `where` helper (the
-- macro needs a concrete goal type, so the helper quantifies the variables and
-- is applied, exactly as the solver's own Examples.agda does), and rewrap with
-- k `cong suc`.  Nothing when there is nothing to peel.
agdaSolverPeelCertificate :: [Definition] -> Equation -> String -> String
                          -> Maybe String
agdaSolverPeelCertificate defs _ _ _ | not (definitionsSafe defs) = Nothing
agdaSolverPeelCertificate defs eq@(l, r) imp body =
  case peelSuc eq of
    (0, _) -> Nothing
    (k, (il, ir)) -> do
      lhs  <- agdaTermWith defs l
      rhs  <- agdaTermWith defs r
      ilhs <- agdaTermWith defs il
      irhs <- agdaTermWith defs ir
      names <- mapM agdaVar (equationVars eq)
      let wrap s = foldr (\_ acc -> "cong suc (" ++ acc ++ ")") s [1 .. k]
      -- Same bare-goal requirement as the direct certificate: the clause
      -- already binds the variables, so `inner` in its where-block states
      -- the core equation bare and the macro can parse it.
      pure $ unlines $
        preambleWith defs (equationSymbols eq)
        ++ [ imp
           , "candidate : " ++ telescope names ++ lhs ++ " ≡ " ++ rhs
           , "candidate " ++ unwords names ++ " = " ++ wrap "inner"
           , "  where inner : " ++ ilhs ++ " ≡ " ++ irhs
           , "        inner = " ++ body
           ]

-- The lemma-citing step shapes: only emitted for the operations whose
-- clause-completion lemma `preambleCore` puts in scope, and only for the
-- induction variable `nv` (the position the stuck term appears in after one
-- step).  Kept out of `stepShapes` proper so the other callers of that
-- function — ClauseOrder, certifyCert — are untouched.
citingStepShapes :: [String] -> String -> [(String, String)]
citingStepShapes syms nv =
  [ s | "max" `elem` syms
      , s <- [ ("sym (maxZeroL " ++ nv ++ ")", "sym (maxZeroL " ++ nv ++ ")")
             , ( "cong suc (sym (maxZeroL " ++ nv ++ "))"
               , "cong suc (sym (maxZeroL " ++ nv ++ "))" ) ] ]
  ++
  [ s | "-" `elem` syms
      , s <- [ ("sym (minusZeroL " ++ nv ++ ")", "sym (minusZeroL " ++ nv ++ ")")
             , ( "cong suc (sym (minusZeroL " ++ nv ++ "))"
               , "cong suc (sym (minusZeroL " ++ nv ++ "))" ) ] ]

-- The induction hypothesis, as a term: `candidate` applied to the same
-- variables, with the induction variable at its (now smaller) name.
inductionHypothesis :: Equation -> Int -> Maybe String
inductionHypothesis eq _ = do
  names <- mapM agdaVar (equationVars eq)
  pure ("candidate " ++ unwords names)

-- The ordered shape list for the step case.  Cheapest and most likely
-- first.  `ih` alone is not decoration: it is what closes every monus and
-- le theorem in the library (suc x ∸ suc x reduces to x ∸ x, so the goal
-- IS the hypothesis).
stepShapes :: String -> [String] -> [(String, String)]
stepShapes ih ks =
  [ ("refl", "refl")
  , ("ih", ih)
  , ("cong suc", "cong suc (" ++ ih ++ ")")
  ]
  ++ concat
     [ [ ("cong (_+ " ++ k ++ ")", "cong (_+ " ++ k ++ ") (" ++ ih ++ ")")
       , ("cong (" ++ k ++ " +_)", "cong (" ++ k ++ " +_) (" ++ ih ++ ")")
       , ("cong (_· " ++ k ++ ")", "cong (_· " ++ k ++ ") (" ++ ih ++ ")")
       , ("cong (" ++ k ++ " ·_)", "cong (" ++ k ++ " ·_) (" ++ ih ++ ")")
       ]
     | k <- ks ]

-- Read the machine's proof annotation.  MathMachine writes
-- "induction on " ++ show (V v); library.snapshot.txt writes it in
-- brackets.  Both are accepted, as is a bare variable name.
inductionVariable :: String -> Maybe Int
inductionVariable s = go (dropWhile isSpace s)
  where
    marker = "induction on "
    go [] = Nothing
    go t@(_:rest)
      | marker `isPrefixOf` t = nameToIndex (drop (length marker) t)
      | otherwise = go rest
    nameToIndex t = case dropWhile isSpace t of
      (c:_) | Just i <- lookup c (zip "xyzuvw" [0 ..]) -> Just i
      ('n':ds) | (d@(_:_), _) <- span isDigit ds -> Just (read d)
      _ -> Nothing

-- ---------------------------------------------------------------- policy

-- How many cong-shapes get an argument, and which arguments.  Every
-- variable of the equation is a candidate `k`; the cap keeps the budget a
-- constant rather than a function of the equation.
kMaxCongArguments :: Int
kMaxCongArguments = 2

-- The invocation budget per candidate, stated once and derived, not
-- guessed: one refl module plus one module per step shape.  This is the
-- budget for an ANNOTATED candidate — one whose proof note names the
-- induction variable — and it is unchanged by the fallback below.
kMaxAgdaCalls :: Int
kMaxAgdaCalls = 1
             + 2 * length solverShapes  -- direct + peel module per macro
             + length (stepShapes "ih" (replicate kMaxCongArguments "k"))
             + length (citingStepShapes ["max", "-"] "n")

-- How many variables get tried when the caller's proof note names none.
-- `equationVars` returns at most the six universe variables, so this is a
-- cap and not a formality; three covers every equation MathMachine has ever
-- written, and the demands in interactive/SesaPariksa_...hs certify on the
-- FIRST variable in all three cases that certify.
kMaxInductionVariables :: Int
kMaxInductionVariables = 3

-- The budget for a candidate whose note names no variable, derived rather
-- than guessed: the shared refl module, then the step menu once per
-- variable tried.  A false equation costs far less than this in practice —
-- the base clause fails and `blamedLine` stops each variable's search at 2
-- calls — but the bound is what is guaranteed and it is what is stated.
kMaxAgdaCallsUnannotated :: Int
kMaxAgdaCallsUnannotated = 1 + 2 * length solverShapes
  + kMaxInductionVariables * (kMaxAgdaCalls - 1 - 2 * length solverShapes)

-- The cubical library, by name as registered in ~/.agda/libraries.
-- Without this the engine's invocation cannot resolve Cubical.* at all;
-- see fault (1) in the header.
kAgdaLibrary :: String
kAgdaLibrary = "cubical"

-- The engine's include root, kept so NaturalMachine.* stays reachable.
kIncludeRoot :: FilePath
kIncludeRoot = "formal/cubical"

agdaArgs :: FilePath -> FilePath -> [String]
agdaArgs dir file = agdaArgsWith [] dir file

-- The same invocation with extra include roots spliced in.  The candidate
-- modules the emitter writes import only Cubical.* and NaturalMachine.*, so
-- the base args never needed more than the one root; a WHOLE module handed
-- over the wire (sadhana.patra) may import any module of the corpus, whose
-- own .agda-lib names further roots (kernel, theorems/…).  Those roots are
-- read from that file at the moment of the run — see `corpusIncludeRoots` —
-- never restated here, so the two cannot drift.
agdaArgsWith :: [FilePath] -> FilePath -> FilePath -> [String]
agdaArgsWith extra dir file =
  concat [ ["-i", r] | r <- kIncludeRoot : extra ]
  ++ ["-i", dir, "--library=" ++ kAgdaLibrary, file]

-- The corpus's own include roots, read from its .agda-lib and made relative
-- to the repository root the agda child runs in.  `.` is kIncludeRoot itself
-- and is dropped rather than doubled.  An unreadable or absent file yields
-- [], which is exactly today's behaviour — the base root alone — so nothing
-- new can break the emitter's gate or the two controls.
corpusIncludeRoots :: FilePath -> IO [FilePath]
corpusIncludeRoots root = do
  r <- try (readFile (root </> kIncludeRoot </> "natural-machine.agda-lib"))
         :: IO (Either SomeException String)
  pure $ case r of
    Left _ -> []
    Right s ->
      [ kIncludeRoot </> p
      | l <- lines s
      , ("include:" : ps) <- [words l]
      , p <- ps, p /= "." ]

-- --------------------------------------------------------------- running

data Verdict
  = Certified String Int     -- ^ shape that worked, agda calls spent
  | Rejected String Int      -- ^ agda's first error line, agda calls spent
  | Untranslatable String    -- ^ symbol or variable outside the fragment
  deriving (Eq, Show)

-- Write UTF-8 regardless of the ambient locale.  `writeFile` does not; see
-- fault (2) in the header.
writeUtf8 :: FilePath -> String -> IO ()
writeUtf8 path s = withFile path WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s

-- One agda invocation.  `root` is the working directory (the repository
-- root, as the engine uses).  LC_ALL is forced because agda prints λ and
-- dies under the C locale.
--
-- The reader's own locale is forced too.  Agda's diagnostics contain ℕ and
-- ≡, and `readCreateProcessWithExitCode` decodes the child's pipes with
-- the process locale encoding; under LANG=C that throws
--   hGetContents: invalid argument (cannot decode byte sequence ...)
-- which is fault (2) again, on the way back.  This is idempotent global
-- state and is set on every call so the seam cannot forget it.
--
-- THE SEAM, CLOSED 2026-08-20.  Until today this function returned the
-- child's exit status untouched, and `vetSuccess` — the falsifier watch of
-- 2026-08-16 — was reached from exactly ONE caller, `runAgdaCached`.  So the
-- repair lived in a wrapper and the seam itself was open: `ClauseOrder`
-- calls `runAgda` directly, and under `agda "$@" 2>&1 | cat`
-- `ClauseOrder.certifyUnder` returned `Accepted "refl"` for `s(x) ≡ x`, in
-- ONE call, from a real agda that had just printed `1 != 0` (measured, this
-- container, Agda 2.8.0, `MATH_CERTCACHE=0`).
--
-- A repair that has to be remembered at each call site is not a repair; it
-- is a note.  So the WATCH IS NOW THE DEFAULT and the unwatched launch has
-- to be asked for by name (`runAgdaUnwatched`), which is the only ordering
-- under which forgetting is safe.  The two callers that must stay unwatched
-- are the controls themselves — `kernelStatus`, which would otherwise
-- recurse — and `GateAudit`'s PROBE-RAW, whose whole purpose is to print
-- what the child returned before anyone judged it.
--
-- The cost is one memoised `kernelStatus` per process (two agda runs), paid
-- on the first SUCCESS only; a run in which nothing checks pays nothing,
-- because a non-zero exit is passed straight through.
runAgda :: FilePath -> String -> IO (ExitCode, String)
runAgda root source = do
  (code, out) <- runAgdaUnwatched root source
  case code of
    ExitSuccess -> vetSuccess root out
    _ -> pure (code, out)

-- The raw launch: the child's own exit status, unexamined.  Everything the
-- old `runAgda` was, under the name that says so.  A zero from here is a
-- number a process returned and is not evidence about mathematics — see
runAgdaUnwatched :: FilePath -> String -> IO (ExitCode, String)
runAgdaUnwatched root source = do
  micros <- agdaTimeoutMicros
  r <- try (timeout micros (runAgdaRaw root source))
         :: IO (Either SomeException (Maybe (ExitCode, String)))
  pure $ case r of
    Right (Just ok) -> ok
    -- BOTH OF THESE USED TO ESCAPE.  A missing agda, a `root` that does not
    -- exist, a mktemp failure: `runAgda` let the IO exception out, past
    -- `certifyWith`, past `kernelAcceptWith`, and the engine ABORTED where
    -- the honest answer is "this candidate was not certified".  An agda
    -- that never returns blocked the gate forever, and `kMaxAgdaCalls`
    -- bounds processes, not wall clock.  A gate must fail closed on both.
    Right Nothing ->
      ( ExitFailure 124
      , kEnvironmentFault ++ ": agda did not return within "
          ++ show (micros `div` 1000000) ++ "s\n" )
    Left e ->
      ( ExitFailure 127
      , kEnvironmentFault ++ ": agda invocation raised: " ++ show e ++ "\n" )

-- The wall-clock bound on one agda process.  Generous: the slowest module
-- the gate emits (a gcd candidate, which pulls in Cubical.Data.Nat.GCD)
-- checks in single-digit seconds, so a candidate that reaches this bound is
-- not slow, it is stuck.
kAgdaTimeoutMicros :: Int
kAgdaTimeoutMicros = 120 * 1000000

-- `MATH_AGDA_TIMEOUT` overrides it, in whole seconds.  Not a tuning knob:
-- a bound that cannot be moved cannot be TESTED, and the probe that proves
-- the gate survives a hung agda has to be able to hang it for less time
-- than the audit itself is willing to wait.  Anything unparseable, zero or
-- negative falls back to the default rather than disabling the bound.
agdaTimeoutMicros :: IO Int
agdaTimeoutMicros = do
  mv <- lookupEnv "MATH_AGDA_TIMEOUT"
  pure $ case mv >>= readSeconds of
    Just s | s > 0 -> s * 1000000
    _ -> kAgdaTimeoutMicros
  where
    readSeconds v = case span isDigit (dropWhile isSpace v) of
      (ds@(_ : _), rest) | all isSpace rest -> Just (read ds)
      _ -> Nothing

-- The marker that says "this non-zero exit is about the environment, not
-- about the mathematics".  `cacheableFailure` refuses to freeze anything
-- carrying it, so a broken toolchain cannot leave rejections behind that
-- outlive the breakage -- the 2026-08-15 fault, kept shut.
kEnvironmentFault :: String
kEnvironmentFault = "kernel gate environment fault"

runAgdaRaw :: FilePath -> String -> IO (ExitCode, String)
runAgdaRaw = runAgdaRawWith []

runAgdaRawWith :: [FilePath] -> FilePath -> String -> IO (ExitCode, String)
runAgdaRawWith extra root source = do
  setLocaleEncoding utf8
  tmp <- getTemporaryDirectory
  dirLine <- readProcess "mktemp" ["-d", tmp </> "math-machine-agda.XXXXXX"] ""
  let dir = reverse (dropWhile isSpace (reverse dirLine))
      file = dir </> "Candidate.agda"
  (do writeUtf8 file source
      base <- getEnvironment
      let env' = ("LC_ALL", "C.UTF-8")
                 : ("LANG", "C.UTF-8")
                 : [ kv | kv@(k, _) <- base, k /= "LC_ALL", k /= "LANG" ]
          cp = (proc "agda" (agdaArgsWith extra dir file))
                 { cwd = Just root, env = Just env' }
      (code, out, err) <- readCreateProcessWithExitCode cp ""
      pure (code, out ++ err))
    `finally` removePathForcibly dir

-- A WHOLE module, watched, with the corpus's own include roots on the path.
-- The controls and the emitter's candidates keep the narrow invocation they
-- always had; this is the wire's door (sadhana.patra) and nothing else calls
-- it.  Watched exactly as `runAgda` is: a success is vetted, and the vet's
-- own kernelStatus runs on the NARROW args, so the controls stay the
-- controls of the gate, not of this widened path.
runAgdaModule :: FilePath -> String -> IO (ExitCode, String)
runAgdaModule root source = do
  extra <- corpusIncludeRoots root
  micros <- agdaTimeoutMicros
  r <- try (timeout micros (runAgdaRawWith extra root source))
         :: IO (Either SomeException (Maybe (ExitCode, String)))
  let raw = case r of
        Right (Just ok) -> ok
        Right Nothing ->
          ( ExitFailure 124
          , kEnvironmentFault ++ ": agda did not return within "
              ++ show (micros `div` 1000000) ++ "s\n" )
        Left e ->
          ( ExitFailure 127
          , kEnvironmentFault ++ ": agda invocation raised: " ++ show e ++ "\n" )
  case raw of
    (ExitSuccess, out) -> vetSuccess root out
    other -> pure other

-- ---------------------------------------------- the analyzer readout
--
-- WHAT THE KERNEL SAYS BEYOND YES.  `runAgdaModule` returns a verdict; this
-- returns the ANALYSIS.  agda's --interaction mode answers two questions
-- about any expression in a loaded module: `Cmd_compute_toplevel` gives its
-- NORMAL FORM, `Cmd_infer_toplevel` gives its TYPE.  So for a submitted
-- module and a list of expressions, the kernel hands back, per expression,
-- what it computes it to and what it is — every bit it derives, not a green.
--
-- Include roots are made ABSOLUTE here: in --interaction mode agda resolves
-- `-i` relative to the loaded file, not the working directory (measured), so
-- the relative roots that runAgdaModule uses would miss the corpus.  Same
-- corpus, same library, same locale; a different question asked of them.
--
-- Returns, per requested expression, (expr, normal-form-or-error,
-- type-or-error).  A load failure surfaces as agda's report in the first
-- entry's fields; nothing is paraphrased.
data Analysis = Analysis
  { anExpr   :: String
  , anNormal :: String   -- Cmd_compute_toplevel DefaultCompute
  , anType   :: String   -- Cmd_infer_toplevel Simplified
  } deriving (Eq, Show)

runAgdaAnalyze :: FilePath -> String -> [String] -> IO (ExitCode, [Analysis])
runAgdaAnalyze root0 modSource exprs = do
  setLocaleEncoding utf8
  -- agda --interaction resolves relative `-i` roots against the loaded
  -- file's directory (the temp dir below), not against cwd, so the corpus
  -- would be invisible unless the roots are absolute.  Canonicalise first.
  root <- makeAbsolute root0
  extra <- corpusIncludeRoots root
  micros <- agdaTimeoutMicros
  tmp <- getTemporaryDirectory
  dirLine <- readProcess "mktemp" ["-d", tmp </> "math-machine-anal.XXXXXX"] ""
  let dir  = reverse (dropWhile isSpace (reverse dirLine))
      file = dir </> "Candidate.agda"
      absRoots = [ root </> r | r <- kIncludeRoot : extra ]
      incArgs  = concat [ ["-i", r] | r <- absRoots ]
                 ++ ["-i", dir, "--library=" ++ kAgdaLibrary]
      iotcm payload = "IOTCM " ++ show file ++ " NonInteractive Direct (" ++ payload ++ ")"
      compute e = iotcm ("Cmd_compute_toplevel DefaultCompute " ++ show e)
      inferT  e = iotcm ("Cmd_infer_toplevel Simplified " ++ show e)
      stdinText = unlines (concat [ [compute e, inferT e] | e <- exprs ])
  (do writeUtf8 file modSource
      base <- getEnvironment
      let env' = ("LC_ALL", "C.UTF-8") : ("LANG", "C.UTF-8")
                 : [ kv | kv@(k, _) <- base, k /= "LC_ALL", k /= "LANG" ]
          cp = (proc "agda" ("--interaction" : incArgs))
                 { cwd = Just root, env = Just env' }
      r <- try (timeout micros (readCreateProcessWithExitCode cp stdinText))
             :: IO (Either SomeException (Maybe (ExitCode, String, String)))
      pure $ case r of
        Right (Just (code, out, err)) ->
          (code, pairUp exprs (infoResults (out ++ err)))
        Right Nothing ->
          ( ExitFailure 124
          , [ Analysis e (kEnvironmentFault ++ ": agda did not return") "" | e <- exprs ] )
        Left ex ->
          ( ExitFailure 127
          , [ Analysis e (kEnvironmentFault ++ ": " ++ show ex) "" | e <- exprs ] ))
    `finally` removePathForcibly dir
  where
    -- Pair the ordered info-action results back to the expressions: compute
    -- then infer, one result each, in the order the commands were sent.
    pairUp [] _ = []
    pairUp (e : es) (nf : ty : rest) = Analysis e nf ty : pairUp es rest
    pairUp (e : es) [nf]             = [Analysis e nf "(no type returned)"]
    pairUp (e : es) []               = [ Analysis e' "(no answer returned)" "" | e' <- e : es ]

-- Scan agda2 s-expression output for `agda2-info-action "TITLE" "BODY"`,
-- returning each BODY (unescaped) whose TITLE is a real answer — dropping the
-- "*Type-checking*" progress lines and empty bodies.  An "*Error*" body is
-- kept: an expression that failed to elaborate is a real, reported answer.
infoResults :: String -> [String]
infoResults = go
  where
    marker = "agda2-info-action "
    go s = case breakOn marker s of
      Nothing -> []
      Just after -> case readSExpString after of
        Just (title, r1) -> case readSExpString (dropWhile isSpace r1) of
          Just (body, r2)
            | title == "*Type-checking*" || all isSpace body -> go r2
            | otherwise -> body : go r2
          Nothing -> go r1
        Nothing -> go after
    breakOn m t = fmap (drop (length m)) (findPrefix m t)
    findPrefix m t@(_ : cs)
      | m `isPrefixOf` t = Just t
      | otherwise = findPrefix m cs
    findPrefix _ [] = Nothing

-- Read one double-quoted, backslash-escaped string; return it (decoded) and
-- the remainder after the closing quote.
readSExpString :: String -> Maybe (String, String)
readSExpString ('"' : cs) = decode cs
  where
    decode ('\\' : x : r) = fmap (first (unesc x :)) (decode r)
    decode ('"' : r)      = Just ([], r)
    decode (c : r)        = fmap (first (c :)) (decode r)
    decode []             = Nothing
    unesc 'n' = '\n'; unesc 't' = '\t'; unesc c = c
    first f (a, b) = (f a, b)
readSExpString _ = Nothing

-- ------------------------------------------------------- the two controls
--
-- WHAT AN EXIT STATUS IS WORTH.  Until 2026-08-16 the gate's entire evidence
-- that a candidate had been PROVED was `code == ExitSuccess`.  That is not
-- evidence about mathematics, it is evidence about a number a process
-- returned, and `interactive/GateAudit.hs` section C exhibited three ways to
-- separate the two.  The cheapest is not exotic: a wrapper of the shape
--
--     agda "$@" 2>&1 | cat
--
-- has the exit status of `cat`.  Real agda runs, really reports `suc x != x`,
-- really exits 1 -- and the gate read 0 and returned `Certified "refl" 1`
-- for `s(x) = x`.  Anyone who has ever piped a compiler through `tee` to
-- keep its output has built this shim by accident.
--
-- The repair is the discipline this repository already applies to its
-- finite verifications: a positive control is not evidence without a
-- FALSIFIER.  `ArithVocab`'s lifting-the-exponent law is trusted because
-- the same harness that accepts 53,760 true triples is watched rejecting a
-- false one at (p=2,a=3,n=2).  The kernel gets the same treatment.  Two
-- modules, run once per process, uncached, through the same `runAgda` the
-- candidates use:
--
--   * `canaryTrue` MUST check.  It fails when agda is missing, the library
--     is unregistered, the include root has moved -- the 2026-08-15 fault,
--     where every candidate became a KERNEL-REJECT.
--   * `canaryFalse` MUST NOT.  It is `suc x ≡ x` closed by `refl`.  A
--     checker that accepts it is not checking, and NOTHING it says can be
--     read as a proof.
--
-- One of the two catches every attack in section C, because each of them
-- has to make a false module pass in order to make a false candidate pass.
-- The cost is two agda processes per engine run, paid on the first success
-- and never again; a run that certifies nothing never pays it at all.
--
-- The controls are run UNCACHED on purpose.  A canary served from an
-- unauthenticated on-disk store would be a canary an attacker can answer.

canaryModule :: String -> String
canaryModule claim = unlines
  [ kOptionsPragma
  , "module Candidate where"
  , "open import Cubical.Foundations.Prelude"
  , "open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)"
  , "canary : (x : ℕ) → " ++ claim
  , "canary x = refl"
  ]

-- True definitionally: `_+_` recurses on its FIRST argument in cubical, so
-- `zero + x` reduces to `x` and `refl` closes it with no lemma.
canaryTrue :: String
canaryTrue = canaryModule "(zero + x) ≡ x"

-- False for every x, and false in the cheapest possible way -- a
-- constructor clash, which agda reports without unfolding anything.
canaryFalse :: String
canaryFalse = canaryModule "(suc x) ≡ x"

-- WHY THIS IS FOUR VALUES AND NOT A BOOLEAN.
--
-- The two controls fail for opposite reasons and the old code folded them
-- into one `Bool`, so `vetSuccess` printed ONE sentence for BOTH:
--
--     the kernel accepted `suc x ≡ x` by refl.  It is not checking proofs
--
-- On 2026-08-20 that sentence was printed 33 times by a container in which
-- the kernel had rejected `suc x ≡ x` exactly as it should, and in which the
-- POSITIVE control was the thing that failed — for an `[InfectiveImport]`
-- scope error (see `kOptionsPragma`).  The verdict was right and the reason
-- was invented, and a reader who believed the reason would have gone looking
-- for a broken agda instead of a drifted pragma.  Two distinct observations
-- reported under one name is the collapse this repository's own contract
-- forbids: a written defect must state WHICH.
--
-- Fail-closed is unchanged.  Only `KernelChecking` licenses an acceptance;
-- the other three are negative verdicts.  What changes is that the verdict now names
-- the control that actually failed and carries agda's own words for it.
--
-- The fourth constructor exists for the same reason as the split: a negative
-- control that merely EXITED NONZERO has not been watched rejecting anything,
-- and reporting that as "accepted a falsehood" would repeat the invented
-- reason one level down.  Not-observed and observed-false stay apart.
data KernelStatus
  = KernelChecking
    -- ^ positive control checked; negative control produced a located type
    --   error.  The falsifier was watched firing.
  | KernelPositiveControlFailed String
    -- ^ `(zero + x) ≡ x` did NOT check.  agda's output.  Says nothing about
    --   whether the kernel is honest — it says this container cannot compile
    --   the modules this emitter produces, so no verdict from it means anything.
  | KernelAcceptedAFalsehood
    -- ^ `(suc x) ≡ x` checked.  The kernel is not checking proofs, and
    --   nothing it accepts is one.
  | KernelNegativeControlInconclusive String
    -- ^ the negative control failed, but not with a type error located in the
    --   module — a missing include root, a timeout, a killed process.  The
    --   kernel was not observed rejecting a falsehood, and it was not observed
    --   accepting one either.  Both are asserted at once and the pair has no
    --   single verdict: *avaktavyam*, the fourth position of the saptabhag
    --   and not an absence.  No acceptance is licensed, as with the others.
  deriving (Eq, Show)

{-# NOINLINE kernelChecksRef #-}
kernelChecksRef :: IORef (Maybe KernelStatus)
kernelChecksRef = unsafePerformIO (newIORef Nothing)

-- Does the thing on the far side of this seam actually check proofs, and if
-- not, which of the two controls said so?  Memoised per process: the answer is
-- a property of the toolchain, and a toolchain that changes under a running
-- engine is not a threat this can address (nor one the cache key can, which is
-- the same admission).
--
-- Order matters.  The positive control is examined FIRST, because a container
-- that cannot compile this emitter's own preamble cannot be asked anything about
-- the negative one either: under `[InfectiveImport]` both canaries fail to
-- scope-check, `negCode /= ExitSuccess` holds vacuously, and reading that as
-- "the kernel rejected a falsehood" credits the kernel with a rejection it
-- never performed.
kernelStatus :: FilePath -> IO KernelStatus
kernelStatus root = do
  cached <- readIORef kernelChecksRef
  case cached of
    Just s -> pure s
    Nothing -> do
      (posCode, posOut) <- runAgdaUnwatched root canaryTrue
      let positiveHolds =
            posCode == ExitSuccess && not (successHidesAnError posOut)
      status <-
        if not positiveHolds
          then pure (KernelPositiveControlFailed posOut)
          else do
            (negCode, negOut) <- runAgdaUnwatched root canaryFalse
            -- A nonzero exit is not by itself a rejection: a vanished include
            -- root produces one too.  `cacheableFailure` is exactly the
            -- predicate "agda located a genuine TYPE error inside the module
            -- we emitted, with no environment marker", and the canary module
            -- is named `Candidate` for the same reason the candidates are, so
            -- it applies verbatim.  Demanding it means `KernelChecking` is
            -- only ever returned by a process that WATCHED the kernel produce
            -- `1 != 0` — the falsifier, not merely the absence of a success.
            pure $ case negCode of
              ExitSuccess -> KernelAcceptedAFalsehood
              ExitFailure _
                | cacheableFailure negOut -> KernelChecking
                | otherwise -> KernelNegativeControlInconclusive negOut
      writeIORef kernelChecksRef (Just status)
      pure status

-- The boolean face, kept because `KernelContext` and `ClauseOrder` ask the
-- question in that form and only need the true fibre.  `KernelStatus` is where
-- the two false fibres are kept apart; collapsing them HERE is safe precisely
-- because a caller of this function consumes only `True`.
kernelIsChecking :: FilePath -> IO Bool
kernelIsChecking root = (== KernelChecking) <$> kernelStatus root

-- The per-call form of the same suspicion, and the one that catches the
-- `| cat` shim on the very first candidate rather than on the first
-- success: agda's output is CAPTURED, so under that wrapper the type error
-- is sitting in the text next to the zero exit status.  A successful agda
-- run says "Checking Candidate (…)" and nothing else.
successHidesAnError :: String -> Bool
successHidesAnError out = any (`isInfixOf` out) markers
  where
    markers =
      [ " != "
      , "when checking"
      , "Not in scope"
      , "Multiple definitions"
      , "Unsolved"
      , "Termination checking failed"
      , "Failed to find source"
      , "error:"
      , "Parse error"
      ]

-- ---------------------------------------------- the certificate cache
--
-- See "THE CERTIFICATE CACHE" in the header for the design and for the two
-- honesty decisions (never cache Untranslatable; cache a rejection only
-- when agda's message is a genuine type error).  This section is the
-- mechanism.

-- Where entries live, relative to the same `root` the agda child runs in.
kCertCacheDir :: FilePath
kCertCacheDir = "interactive" </> ".certcache"

-- The one escape hatch.  `MATH_CERTCACHE=0|off|no|false` bypasses the cache
-- completely: every module is sent to agda and nothing is read or written.
-- It exists so a measurement can be taken against a cold kernel, and so a
-- change to the cubical library (which is NOT in the key) can be recovered
-- from without deleting files by hand.
cacheEnabled :: IO Bool
cacheEnabled = do
  mv <- lookupEnv "MATH_CERTCACHE"
  pure $ case fmap (map toLower) mv of
    Just v | v `elem` ["0", "off", "no", "false"] -> False
    _ -> True

-- The checker's identity, folded into every key.  Queried once per process
-- and memoised: `agda --version` is itself a process launch and the whole
-- point here is not to launch processes.  If the query fails the identity
-- is a fixed unknown string, which is still consistent within and across
-- runs, so the cache stays correct-by-comparison (the stored source is
-- always re-checked) but stops distinguishing toolchains.
{-# NOINLINE toolchainRef #-}
toolchainRef :: IORef (Maybe String)
toolchainRef = unsafePerformIO (newIORef Nothing)

toolchainIdentity :: IO String
toolchainIdentity = do
  cached <- readIORef toolchainRef
  case cached of
    Just s -> pure s
    Nothing -> do
      r <- try (readProcess "agda" ["--version"] "")
             :: IO (Either SomeException String)
      let ver = either (const "agda:version-unknown") id r
          s = unwords (words ver)
                ++ " | library=" ++ kAgdaLibrary
                ++ " | include=" ++ kIncludeRoot
      writeIORef toolchainRef (Just s)
      pure s

-- UTF-8 encoding of one character, so the key really is a hash of the bytes
-- that would be written to disk and handed to agda.
utf8Bytes :: Char -> [Int]
utf8Bytes ch
  | n < 0x80 = [n]
  | n < 0x800 =
      [ 0xC0 .|. (shiftR n 6 .&. 0x1F), 0x80 .|. (n .&. 0x3F) ]
  | n < 0x10000 =
      [ 0xE0 .|. (shiftR n 12 .&. 0x0F)
      , 0x80 .|. (shiftR n 6 .&. 0x3F)
      , 0x80 .|. (n .&. 0x3F) ]
  | otherwise =
      [ 0xF0 .|. (shiftR n 18 .&. 0x07)
      , 0x80 .|. (shiftR n 12 .&. 0x3F)
      , 0x80 .|. (shiftR n 6 .&. 0x3F)
      , 0x80 .|. (n .&. 0x3F) ]
  where n = ord ch

-- FNV-1a, two independent lanes (different basis and prime, second lane run
-- over the reversed byte string) concatenated to 128 bits.  A cryptographic
-- hash is not needed and would be a dependency: the stored source is
-- compared byte for byte on every hit, so the hash cannot cause a wrong
-- answer, only a wasted lookup.
fnv1a :: Word64 -> Word64 -> [Int] -> Word64
fnv1a basis prime = foldl' step basis
  where step h b = (h `xor` fromIntegral b) * prime

hex64 :: Word64 -> String
hex64 w = [ hexDigit (fromIntegral (shiftR w k .&. 0xF)) | k <- [60, 56 .. 0] ]
  where hexDigit i = "0123456789abcdef" !! i

cacheKey :: String -> String -> String
cacheKey toolchain source = hex64 h1 ++ hex64 h2
  where
    bs = concatMap utf8Bytes (toolchain ++ "\NUL" ++ source)
    h1 = fnv1a 14695981039346656037 1099511628211 bs
    h2 = fnv1a 0xcbf29ce484222325 0x100000001b3f (reverse bs)

-- One stored verdict.  `ceSource` is the whole point of the format: it is
-- what makes the entry re-runnable by a reader and what makes a hash
-- collision harmless.
data CacheEntry = CacheEntry
  { ceExit :: Int
  , ceToolchain :: String
  , ceOutput :: String
  , ceSource :: String
  } deriving (Eq, Show)

encodeEntry :: CacheEntry -> String
encodeEntry e = unlines $
  [ "CERTCACHE 1"
  , "VERDICT " ++ (if ceExit e == 0 then "accepted" else "rejected")
  , "EXIT " ++ show (ceExit e)
  , "TOOLCHAIN " ++ ceToolchain e
  ]
  ++ block "AGDA-OUTPUT" (ceOutput e)
  ++ block "SOURCE" (ceSource e)

-- A length-and-trailing-newline delimited block, so encode/decode is an
-- exact inverse on arbitrary text (agda's output ends without a newline
-- often enough to matter, and an inexact round trip would make every
-- lookup miss).
block :: String -> String -> [String]
block tag s = (tag ++ " " ++ show (length ls) ++ " " ++ flag) : ls
  where
    ls = lines s
    flag = if not (null s) && last s == '\n' then "nl" else "nonl"

decodeEntry :: String -> Maybe CacheEntry
decodeEntry txt = case lines txt of
  (hdr : rest0) | hdr == "CERTCACHE 1" -> do
    (_verd, rest1) <- takeP "VERDICT " rest0
    (exitS, rest2) <- takeP "EXIT " rest1
    ec <- readMaybeInt exitS
    (tc, rest3) <- takeP "TOOLCHAIN " rest2
    (out, rest4) <- readBlock "AGDA-OUTPUT" rest3
    (src, _) <- readBlock "SOURCE" rest4
    pure (CacheEntry ec tc out src)
  _ -> Nothing
  where
    takeP pfx (l : more) | pfx `isPrefixOf` l = Just (drop (length pfx) l, more)
    takeP _ _ = Nothing

readBlock :: String -> [String] -> Maybe (String, [String])
readBlock tag ls = case ls of
  (l : more) | (tag ++ " ") `isPrefixOf` l ->
    case words (drop (length tag + 1) l) of
      [nS, flag] -> do
        n <- readMaybeInt nS
        let (body, rest) = splitAt n more
        if length body /= n then Nothing else Just (rebuild body flag, rest)
      _ -> Nothing
  _ -> Nothing
  where
    rebuild body "nl" = unlines body
    rebuild body _ = intercalate "\n" body

readUtf8 :: FilePath -> IO String
readUtf8 path = withFile path ReadMode $ \h -> do
  hSetEncoding h utf8
  s <- hGetContents h
  length s `seq` pure s

-- A hit requires the stored source and the stored toolchain to match
-- EXACTLY.  Any change to the emitter, to a concept definition, to the
-- vocabulary transcriptions, or to agda itself changes one of them and
-- therefore misses.
lookupCache :: FilePath -> String -> String -> String
            -> IO (Maybe (ExitCode, String))
lookupCache root tc key source = do
  r <- try (do
         present <- doesFileExist path
         if not present then pure Nothing else decodeEntry <$> readUtf8 path)
         :: IO (Either SomeException (Maybe CacheEntry))
  pure $ case r of
    Right (Just e) | ceSource e == source, ceToolchain e == tc ->
      Just (toExit (ceExit e), ceOutput e)
    _ -> Nothing
  where
    path = root </> kCertCacheDir </> key
    toExit 0 = ExitSuccess
    toExit n = ExitFailure n

-- Written to a unique temporary name in the same directory and renamed, so
-- a concurrent reader never sees a half-written entry and two engines
-- racing on the same key both end up with a complete file.  Any IO failure
-- here is swallowed: an unwritable cache must slow the gate down, never
-- break it.
storeCache :: FilePath -> String -> String -> CacheEntry -> IO ()
storeCache root tc key entry = do
  r <- try (do
         createDirectoryIfMissing True dir
         (tmpPath, h) <- openTempFile dir (key ++ ".tmp")
         hSetEncoding h utf8
         hPutStr h (encodeEntry entry { ceToolchain = tc })
         hClose h
         renameFile tmpPath (dir </> key))
         :: IO (Either SomeException ())
  either (const (pure ())) pure r
  where dir = root </> kCertCacheDir

-- Requirement (e), decided: cache a failure only when agda plainly reports a
-- TYPE error located in the module we emitted.  A non-zero exit otherwise
-- carries no mathematical content — a missing library, a locale fault, a
-- vanished include root or a killed process all produce one, and freezing
-- any of those into a persistent "rejected" would recreate exactly the bug
-- described as fault (1) in the header, where a path error was recorded as a
-- rejection indistinguishable from a false statement.
cacheableFailure :: String -> Bool
cacheableFailure out =
  not (null (dropWhile isSpace out))
    && "Candidate.agda:" `isInfixOf` out
    && isJust (blamedLine out)
    && not (any (`isInfixOf` out) environmentMarkers)
    && any (`isInfixOf` out) typeErrorMarkers
  where
    environmentMarkers =
      [ "Failed to find source of module"
      , "No such file or directory"
      , "does not exist"
      , "cannot be found"
      , "not found"
      , "Cannot find"
      , "internal error"
      , "Interrupted"
      , "cannot encode character"
      , "invalid argument"
      , kEnvironmentFault      -- timeout, or an exception out of `runAgda`
      ]
    typeErrorMarkers =
      [ " != "
      , "when checking"
      ]

-- ASYMMETRIC TRUST, which is the only kind an unauthenticated store can
-- carry.  `interactive/.certcache` is a directory of files.  Anything that can
-- write there can write "VERDICT accepted" beside any module it likes, and
-- `GateAudit --probe poison` does exactly that: one hand-written file turns
-- `s(x) = x` into a `Certified` for zero agda invocations.  Signing is not
-- available (there is no secret here, and an adversary with the filesystem
-- has `ProofGate.hs` too), so the answer is not to authenticate the store
-- but to stop asking it the question that matters.
--
-- The two directions are not symmetric:
--
--   a WRONG REJECTION costs a theorem.  The engine misses something true,
--   the loop continues, the corpus stays sound.
--
--   a WRONG ACCEPTANCE installs a false rewrite rule, and every later round
--   reasons with it.
--
-- So rejections are served from disk, and an ACCEPTANCE ON DISK IS A HINT:
-- the first time this process is asked to honour one it re-runs agda and
-- believes agda.  Confirmed keys go in an in-memory set, so a candidate
-- resubmitted a hundred times in one run still costs one call, not a
-- hundred -- which is where nearly all of the cache's measured win came
-- from (the same module is re-emitted every round it survives, not once).
-- An entry agda then contradicts is DELETED, because it is either poisoned
-- or was written by a toolchain that lied.
--
-- Stated as one line: on-disk acceptances are hints, in-memory acceptances
-- are verdicts, and no acceptance of either kind is honoured by a process
-- whose kernel has not been watched rejecting a false module.

{-# NOINLINE confirmedRef #-}
confirmedRef :: IORef [String]
confirmedRef = unsafePerformIO (newIORef [])

confirmedHere :: String -> IO Bool
confirmedHere key = elem key <$> readIORef confirmedRef

confirmHere :: String -> IO ()
confirmHere key = modifyIORef' confirmedRef (key :)

-- Every route by which a success leaves this module passes through here.
-- A zero exit is upgraded to an acceptance only if agda's own output is
-- free of complaints AND this process has seen the kernel reject a false
-- module.  Otherwise the zero exit is reported as what it is: a fault in
-- the environment, uncacheable, and a negative verdict.
--
-- THE ACCOUNTABILITY OF A NEGATIVE VERDICT.  This function's negative verdicts
-- now carry the observation that produced them, which is the whole of the repair
-- of 2026-08-20.  A negative verdict that does not say what was looked at, and found
-- unfit, is a verdict asserting itself while concealing its standpoint —
-- दुर्नयो भवति").  The older Mīmāṃsā name for the requirement is
-- *yogynupalabdhi*: a non-apprehension is evidence only when the looking was
-- FIT to have apprehended (Kumrila, *lokavrttika*, Abhvapariccheda,
-- c. 7th c.; sūtra §19, "यत्र दृश्येत तत्र न दृष्टम् इति प्रमाणम्").  A
-- container that cannot compile the emitter's own preamble is not fit
-- looking, and reporting its silence as "the kernel accepted a falsehood" is
-- the precise failure that doctrine names.
vetSuccess :: FilePath -> String -> IO (ExitCode, String)
vetSuccess root out
  | successHidesAnError out =
      pure ( ExitFailure 125
           , kEnvironmentFault
               ++ ": agda exited 0 while reporting an error; the exit status\n"
               ++ "of this invocation is not agda's.  Original output:\n" ++ out )
  | otherwise = do
      status <- kernelStatus root
      pure $ case status of
        KernelChecking -> (ExitSuccess, out)
        KernelPositiveControlFailed posOut ->
          ( ExitFailure 126
          , kEnvironmentFault
              ++ ": the POSITIVE control did not check.  `(zero + x) ≡ x` by\n"
              ++ "refl did not check in this container, so it cannot compile the\n"
              ++ "modules this emitter produces and no verdict of its is about\n"
              ++ "mathematics.  This is NOT a claim that the kernel is\n"
              ++ "dishonest -- the negative control was never reached.\n"
              ++ "agda's words:\n" ++ posOut )
        KernelAcceptedAFalsehood ->
          ( ExitFailure 126
          , kEnvironmentFault
              ++ ": the NEGATIVE control checked.  The kernel accepted\n"
              ++ "`suc x ≡ x` by refl, so it is not checking proofs and\n"
              ++ "nothing it accepts is one.\n" )
        KernelNegativeControlInconclusive negOut ->
          ( ExitFailure 126
          , kEnvironmentFault
              ++ ": the NEGATIVE control neither checked nor produced a type\n"
              ++ "error.  This container was not watched rejecting a falsehood,\n"
              ++ "and was not watched accepting one; no acceptance is honoured\n"
              ++ "on that evidence.  agda's words:\n" ++ negOut )

-- The same watch, for a caller that launched agda ITSELF.
--
-- Eight modules under `interactive/` do not call `runAgda` at all: they build
-- their own `CreateProcess` and read the exit status, having copied the
-- LOCALE discipline out of `runAgdaRaw` and left the fitness behind.  Closing
-- the seam at `runAgda` does nothing for them, because they never cross it.
-- This is the one line each of them needs, and it takes what they already
-- have in hand — the code and the captured output — rather than asking them
-- to re-plumb their invocation through this module's temp-directory and
-- argument conventions, which are not theirs.
--
-- A non-zero exit is returned untouched: a negative verdict needs no watch, because
-- the failure mode being guarded against is a FALSE ACCEPTANCE.  Only a zero
-- is asked to earn itself.
vetForeignRun :: FilePath -> ExitCode -> String -> IO (ExitCode, String)
vetForeignRun root code out = case code of
  ExitSuccess -> vetSuccess root out
  _ -> pure (code, out)

-- The cached invocation.  The third component is the number of agda
-- PROCESSES actually launched: 0 on a hit, 1 on a miss.  Everything that
-- reports an invocation count counts this, so a cache hit can never be
-- mistaken for kernel work.  (The two control modules are not counted:
-- they are paid once per process and belong to no candidate.)
runAgdaCached :: FilePath -> String -> IO (ExitCode, String, Int)
runAgdaCached root source = do
  on <- cacheEnabled
  if not on
    then do
      (code, out) <- runAgdaUnwatched root source
      case code of
        ExitSuccess -> do
          (code', out') <- vetSuccess root out
          pure (code', out', 1)
        _ -> pure (code, out, 1)
    else do
      tc <- toolchainIdentity
      let key = cacheKey tc source
      hit <- lookupCache root tc key source
      case hit of
        -- a cached REJECTION: served, as before.  It can only lose a
        -- theorem, and the stored source is byte-compared, so the worst
        -- case is a candidate re-derived later at full price.
        Just (ExitFailure n, out) -> pure (ExitFailure n, out, 0)
        -- a cached ACCEPTANCE: free only after this process has confirmed
        -- it against the kernel itself.
        Just (ExitSuccess, out) -> do
          seen <- confirmedHere key
          if seen
            then pure (ExitSuccess, out, 0)
            else do
              (code, out') <- runAgdaUnwatched root source
              case code of
                ExitSuccess -> do
                  (code', out'') <- vetSuccess root out'
                  case code' of
                    ExitSuccess -> confirmHere key >> pure (ExitSuccess, out, 1)
                    _ -> dropEntry root key >> pure (code', out'', 1)
                _ -> do
                  dropEntry root key
                  pure (code, out', 1)
        Nothing -> do
          (code, out) <- runAgdaUnwatched root source
          case code of
            ExitSuccess -> do
              (code', out') <- vetSuccess root out
              case code' of
                ExitSuccess -> do
                  confirmHere key
                  storeCache root tc key (CacheEntry 0 tc out source)
                  pure (ExitSuccess, out, 1)
                ExitFailure n -> pure (ExitFailure n, out', 1)
            ExitFailure n -> do
              when (cacheableFailure out) $
                storeCache root tc key (CacheEntry n tc out source)
              pure (ExitFailure n, out, 1)

-- An entry the kernel contradicts is removed rather than left to be
-- re-tested by every future process.  Failure to remove it is not fatal:
-- the next process re-tests it and reaches the same answer.
dropEntry :: FilePath -> String -> IO ()
dropEntry root key = do
  r <- try (removePathForcibly (root </> kCertCacheDir </> key))
         :: IO (Either SomeException ())
  either (const (pure ())) pure r

-- How a verdict announces provenance.  0 fresh agda calls => the whole
-- result came out of the cache and says so; any fresh call at all and the
-- label is left alone, because the run really did use the kernel.
cachedShape :: Int -> String -> String
cachedShape 0 s = "cached, " ++ s
cachedShape _ s = s

cachedError :: Int -> String -> String
cachedError 0 s = "cached: " ++ s
cachedError _ s = s

-- Agda's first complaint, as one line, for the log.  The location line
-- ("<tmpdir>/Candidate.agda:12,25-31") is dropped: the path is a temp
-- directory that no longer exists by the time anyone reads the log, and it
-- would otherwise crowd out the message.
firstErrorLine :: String -> String
firstErrorLine out =
  case dropWhile uninformative (lines out) of
    [] -> "(agda said nothing)"
    ls -> unwords (words (unwords (take 2 ls)))
  where
    uninformative ln =
      null (dropWhile isSpace ln)
        || "Checking " `isPrefixOf` dropWhile isSpace ln
        || ".agda:" `isInfixOf` ln

-- The line agda blamed, if it named one.
--
-- TWO SPELLINGS, AND WHY BOTH ARE HERE (2026-08-20).  Agda 2.6.3 prints a
-- range as `<path>:LINE,COL-COL`; Agda 2.8.0 prints `<path>:LINE.COL-COL`.
-- This function accepted only the comma, so under 2.8 it returned `Nothing`
-- on every diagnostic agda has ever produced, and three separate things
-- downstream quietly stopped working:
--
--   1. `certifyWith`'s base-clause early exit (`blamedLine out == Just
--      baseLine`) never fired, so every candidate whose BASE clause was the
--      problem still paid all eleven remaining step shapes.  That is the
--      whole of the observed "worst-case 12 (bound 12)": not a hard search,
--      a dead comparison.
--   2. `cacheableFailure` requires `isJust (blamedLine out)`, so NO rejection
--      was cacheable and every run re-paid for every rejection.
--   3. `kernelStatus`'s negative control, which reuses `cacheableFailure`,
--      could not recognise `suc x != x` as a located type error — so the
--      falsifier fired, correctly, and was not credited with firing.
--
-- The separator is required to be one of `,.` AND to be followed by a digit,
-- so `Prelude.agda:` (no line) and prose containing a colon still yield
-- `Nothing` rather than a fabricated line number.  Fabricating one is worse
-- than declining: it would make the base-clause exit fire on the wrong
-- clause.
blamedLine :: String -> Maybe Int
blamedLine out = case mapMaybe grab (lines out) of
  (n : _) -> Just n
  [] -> Nothing
  where
    grab ln = case break (== ':') (dropWhile isSpace ln) of
      (_, ':' : rest)
        | (ds@(_ : _), sep : more) <- span isDigit rest
        , sep `elem` (",." :: String)
        , (_ : _) <- takeWhile isDigit more
        -> Just (read ds)
      _ -> Nothing

-- The gate.  Fast path first, then the induction skeleton if the machine's
-- proof used induction.  Never exceeds kMaxAgdaCalls.
certify :: FilePath -> (Equation, String) -> IO Verdict
certify = certifyWith []

certifyWith :: [Definition] -> FilePath -> (Equation, String) -> IO Verdict
-- The `Int` in the Verdict is the number of agda processes this call
-- actually launched — 0 when every module in the search came from the
-- cache, in which case the shape/error string is marked `cached`.  It is
-- deliberately not the number of modules examined: that number would make
-- a cache hit look like kernel work in every log and every measurement.
certifyWith defs root (eq, proofNote) =
  case agdaCertificateWith defs eq of
    Nothing -> pure (Untranslatable (untranslatableReason defs eq))
    Just reflSource -> do
      (code, out, n0) <- runAgdaCached root reflSource
      case code of
        ExitSuccess -> pure (Certified (cachedShape n0 "refl") n0)
        -- FAIL CLOSED AND FAIL FAST.  An environment fault says nothing
        -- about this equation, so the eleven remaining step shapes have
        -- nothing to add: they will each hang for the same timeout, or
        -- raise the same exception, and the candidate will be rejected
        -- anyway twelve invocations later.  Under a hung agda that is the
        -- difference between one timeout and the whole budget's worth.
        ExitFailure _ | environmentFault out ->
          pure (Rejected (firstErrorLine out) n0)
        ExitFailure _ ->
          trySolvers solverModules n0 (firstErrorLine out)
  where
    -- The reflection-solver modules are tried after the definitional `refl`
    -- module and before the induction search: one call closes the whole
    -- ℕ-semiring class (directly, or under k leading `suc`s via the peel
    -- certificate), and for an equation the solver does not handle (monus, le,
    -- gcd) it fails fast and the induction search runs exactly as before.
    -- Exhausting the solver modules falls through to `tryVariables`, so no
    -- candidate the old emitter certified can be lost.  Each solver macro
    -- contributes a direct module and, when the equation has matching leading
    -- `suc`s, a peel module.
    solverModules :: [(String, String)]
    solverModules = concat
      [    [ ("solver: " ++ label, s)
           | Just s <- [agdaSolverCertificate defs eq imp body] ]
        ++ [ ("solver-peel: " ++ label, s)
           | Just s <- [agdaSolverPeelCertificate defs eq imp body] ]
      | (label, imp, body) <- solverShapes ]

    trySolvers [] used lastErr =
      tryVariables (inductionCandidates proofNote eq) used lastErr
    trySolvers ((label, source) : more) used _lastErr = do
      (code, out, n) <- runAgdaCached root source
      let used' = used + n
      case code of
        ExitSuccess -> pure (Certified (cachedShape used' label) used')
        ExitFailure _
          | environmentFault out -> pure (Rejected (firstErrorLine out) used')
          | otherwise -> trySolvers more used' (firstErrorLine out)
    -- WHEN THE CALLER NAMES NO VARIABLE, CHOOSE ONE (2026-08-20).
    --
    -- `inductionVariable` reads the induction variable off the caller's proof
    -- note.  The engine annotates its OWN proofs, so a theorem it derived
    -- arrives with "[induction on x]" and gets the eleven step shapes.  A
    -- RESIDUAL — a subgoal harvested from the kernel's own stall and asked
    -- back — has no such note, and the `Nothing` branch that used to stand
    -- here turned it back after ONE agda call, having emitted no induction module
    -- at all.  `MathMachine.koNaya` already records the consequence: the naya
    -- attempted is `NRefl` exactly when the note named no variable, and over
    -- the committed log 541 of 1457 obligations attach to claims the same
    -- log accepts elsewhere.
    --
    -- Measured on the six lemmas the kernel demanded and no composition law
    -- reaches (interactive/SesaPariksa_...hs, and §9 of
    -- variable in turn moves THREE of the six from open to certified with the
    -- shape menu completely unchanged —
    --
    --     x = x + (0 * x)                  induction on x, step = cong suc
    --     max(0,x) + 0 = max(0 + 0, x + 0) induction on x, step = refl
    --     0 = le(s(s(s(x))), x)            induction on x, step = ih
    --
    -- the first of which is the flagship residual this engine circled for 239
    -- rounds.  None of the three needed a new shape; they needed to be asked.
    --
    -- THIS IS NOT THE PROOF SEARCH §3a OF CERTIFICATE_REACH.md RULES OUT.  That
    -- prohibition is about searching over COMPOSITIONS of proof shapes, where the
    -- space is unbounded and the search is a prover in another process.  This
    -- searches over the ≤ 6 VARIABLES OF THE EQUATION with the shape menu
    -- fixed, and the bound is stated below and derived rather than guessed.
    --
    -- An ANNOTATED candidate is unaffected in every respect, including its
    -- budget: the note names one variable and one variable is tried, exactly
    -- as before.  Only the note-less case changes, and it changes from
    -- "1 call, always rejected" to "at most kMaxAgdaCallsUnannotated calls,
    -- sometimes certified".
    inductionCandidates :: String -> Equation -> [Int]
    inductionCandidates note e = case inductionVariable note of
      Just v  -> [v]
      Nothing -> take kMaxInductionVariables (equationVars e)

    tryVariables [] used lastErr = pure (Rejected (cachedError used lastErr) used)
    tryVariables (v : vs) used lastErr =
      let ks = take kMaxCongArguments (mapMaybe agdaVar (equationVars eq))
          nv = maybe (show v) id (agdaVar v)
      in case inductionHypothesis eq v of
           Nothing -> pure (Rejected (cachedError used lastErr) used)
           Just ih -> do
             res <- tryShapes v
                      (stepShapes ih ks
                       ++ citingStepShapes (equationSymbols eq) nv)
                      used lastErr
             case res of
               Certified{} -> pure res
               Untranslatable{} -> pure res
               -- An environment fault says nothing about this equation, and
               -- the next variable would hit the same fault; fail closed
               -- rather than spend the rest of the budget on it.
               Rejected err n
                 | null vs || kEnvironmentFault `isInfixOf` err -> pure res
                 | otherwise -> tryVariables vs n err

    tryShapes _ [] used lastErr = pure (Rejected (cachedError used lastErr) used)
    tryShapes v ((label, step) : more) used _lastErr =
      case agdaInductionCertificate defs eq v step of
        Nothing ->
          pure (Rejected
                  (cachedError used "induction variable outside the equation")
                  used)
        Just (source, baseLine) -> do
          (code, out, n) <- runAgdaCached root source
          let used' = used + n
          case code of
            ExitSuccess ->
              let nv = maybe (show v) id (agdaVar v)
              in pure (Certified
                         (cachedShape used'
                            ("induction on " ++ nv ++ ", step = " ++ label))
                         used')
            ExitFailure _
              | environmentFault out ->
                  pure (Rejected (firstErrorLine out) used')
              -- Agda blamed the base clause: no step shape can rescue it.
              | blamedLine out == Just baseLine ->
                  pure (Rejected
                          (cachedError used'
                             ("base clause: " ++ firstErrorLine out))
                          used')
              | otherwise -> tryShapes v more used' (firstErrorLine out)

-- Did this non-zero exit come from the environment rather than from the
-- mathematics?  Only the faults this module synthesises itself count: a
-- timeout, an exception out of `runAgda`, a zero exit contradicted by its
-- own output, a kernel that failed its controls.  Agda's own diagnostics
-- are not searched, because a candidate that merely MENTIONS the phrase
-- must not be able to shorten its own examination.
environmentFault :: String -> Bool
environmentFault out = kEnvironmentFault `isPrefixOf` dropWhile isSpace out

untranslatableReason :: [Definition] -> Equation -> String
untranslatableReason defs eq@(l, r) =
  -- The identifier check reports first and by name.  A rejected injection
  -- must be legible as an injection in the log, not disguised as the
  -- emitter running out of vocabulary.
  case [ defName d | d <- defs, not (validAgdaIdent (defName d)) ] of
    (n : _) -> "illegal concept name (not [A-Za-z_][A-Za-z0-9_]*): " ++ show n
    [] -> case [ s | s <- equationSymbols eq, not (known s) ] of
      (s : _) -> "unknown symbol " ++ show s
      [] -> case [ i | i <- equationVars eq, not (isJust (agdaVar i)) ] of
        (i : _) -> "variable index out of range: " ++ show i
        [] -> "untranslatable: " ++ show l ++ " = " ++ show r
  where
    known s = s `elem` ["0", "s", "+", "*", "-", "max", "le", "gcd"]
                || isJust (lookupDef defs s)

-- --------------------------------------------- serialisable certificates
--
-- The corpus wants interactive/library.txt to be a re-checkable LEDGER, not a
-- trust-me list.  `certify` above proves a library equation once, inside
-- this process, and then the proof term is gone: the file records only the
-- equation and a prose note ("[induction on x]").  Re-reading the file
-- therefore re-runs the *search* (agdaCertificate + stepShapes), which is
-- not the same as re-checking a fixed proof — a change to `stepShapes` could
-- silently change which library entries are provable.
--
-- A `SerialCert` closes that gap.  It records the exact proof WITNESS that
-- agda accepted (refl, or induction on a named variable with the exact step
-- term), so:
--
--   (a) it RECONSTRUCTS THE PROOF TERM deterministically — `reconstructModule`
--       emits the one Agda module that carries the accepted proof, with no
--       search; and
--   (b) it ROUND-TRIPS — `serializeCert` / `parseSerialCert` are inverses on
--       the fragment, so a serialised ledger entry parses back to the same
--       witness, whose reconstructed module agda re-checks to the same
--       theorem (`replayCert`).
--
-- The Agda side these land in is Kernel.RewriteCertificate: a checked
-- `candidate : lhs ≡ rhs` is exactly the hypothesis of `derivation-sound` /
-- `induction-sound` there, i.e. the semantic warrant that the endpoints
-- denote pointwise-equal functions ℕ → ℕ.

-- The proof that a `SerialCert` carries, in a form that reconstructs a
-- specific Agda module rather than a search.
data ProofWitness
  = WRefl                    -- ^ true by definitional unfolding: `refl`
  | WInduction Int String    -- ^ induction on variable i, with this exact
                             --   step term (an Agda expression, e.g. the
                             --   induction hypothesis under `cong suc`)
  deriving (Eq, Show)

-- A ledger entry: the theorem endpoints, the concept definitions its terms
-- need in scope, and the witness that discharges it.  Everything needed to
-- rebuild and re-check the proof, with nothing left to a search.
data SerialCert = SerialCert
  { scLhs :: Term
  , scRhs :: Term
  , scDefs :: [Definition]
  , scWitness :: ProofWitness
  } deriving (Eq, Show)

mkSerialCert :: [Definition] -> Equation -> ProofWitness -> SerialCert
mkSerialCert defs (l, r) w = SerialCert l r defs w

-- Canonical prefix serialisation of a Term.  Deliberately NOT the machine's
-- infix `show` (which is ambiguous for word operators like `max`: `(xmaxx)`);
-- this form is an exact inverse of `parseSerTerm` on the whole Term type.
serTerm :: Term -> String
serTerm (V i)    = "v" ++ show i
serTerm (F f ts) = "(" ++ unwords (f : map serTerm ts) ++ ")"

serTokenize :: String -> [String]
serTokenize [] = []
serTokenize (c : cs)
  | c == '('  = "(" : serTokenize cs
  | c == ')'  = ")" : serTokenize cs
  | isSpace c = serTokenize cs
  | otherwise =
      let (a, rest) = span (\x -> x /= '(' && x /= ')' && not (isSpace x)) (c : cs)
      in a : serTokenize rest

parseSerTerm :: String -> Maybe Term
parseSerTerm s = case pSer (serTokenize s) of
  Just (t, []) -> Just t
  _            -> Nothing

pSer :: [String] -> Maybe (Term, [String])
pSer ("(" : name : rest)
  | name /= "(" && name /= ")" = do
      (args, rest') <- pSerArgs rest
      pure (F name args, rest')
pSer (tok : rest)
  | ('v' : ds) <- tok, not (null ds), all isDigit ds = Just (V (read ds), rest)
pSer _ = Nothing

pSerArgs :: [String] -> Maybe ([Term], [String])
pSerArgs (")" : rest) = Just ([], rest)
pSerArgs toks = do
  (a, r1)  <- pSer toks
  (as, r2) <- pSerArgs r1
  pure (a : as, r2)

-- A ledger block.  Line-oriented and self-delimiting so many entries can
-- share one file.
serializeCert :: SerialCert -> String
serializeCert sc = unlines $
  [ "BEGIN-CERT 1"
  , "LHS " ++ serTerm (scLhs sc)
  , "RHS " ++ serTerm (scRhs sc)
  , "DEFS " ++ show (length (scDefs sc))
  ]
  ++ [ "DEF " ++ defName d ++ " " ++ show (defArity d) ++ " " ++ serTerm (defBody d)
     | d <- scDefs sc ]
  ++ [ case scWitness sc of
         WRefl            -> "WITNESS refl"
         WInduction v stp -> "WITNESS induction " ++ show v ++ " " ++ stp
     , "END-CERT"
     ]

parseSerialCert :: String -> Maybe SerialCert
parseSerialCert = parseSerialFrom . lines

-- Parses the first BEGIN-CERT..END-CERT block in a line list.
parseSerialFrom :: [String] -> Maybe SerialCert
parseSerialFrom ls0 = do
  rest0            <- dropTo "BEGIN-CERT" ls0
  (lhsL, rest1)    <- takePrefixed "LHS " rest0
  lhs              <- parseSerTerm lhsL
  (rhsL, rest2)    <- takePrefixed "RHS " rest1
  rhs              <- parseSerTerm rhsL
  (defsN, rest3)   <- takePrefixed "DEFS " rest2
  n                <- readMaybeInt defsN
  (defs, rest4)    <- readDefs n rest3
  (witL, _)        <- takePrefixed "WITNESS " rest4
  w                <- parseWitness witL
  pure (SerialCert lhs rhs defs w)
  where
    dropTo pfx ls = case dropWhile (not . isPrefixOf pfx) ls of
      (_ : more) -> Just more
      []         -> Nothing
    takePrefixed pfx (l : more)
      | pfx `isPrefixOf` l = Just (drop (length pfx) l, more)
    takePrefixed _ _ = Nothing
    readDefs 0 ls = Just ([], ls)
    readDefs k ls = do
      (dl, more) <- takePrefixed "DEF " ls
      d          <- parseDefLine dl
      (ds, r)    <- readDefs (k - 1) more
      pure (d : ds, r)
    parseDefLine dl = case words dl of
      (nm : arS : bodyToks) -> do
        ar   <- readMaybeInt arS
        body <- parseSerTerm (unwords bodyToks)
        pure (Definition nm ar body)
      _ -> Nothing
    parseWitness w = case words w of
      ["refl"]                -> Just WRefl
      ("induction" : v : stp) -> do
        vi <- readMaybeInt v
        pure (WInduction vi (unwords stp))
      _ -> Nothing

readMaybeInt :: String -> Maybe Int
readMaybeInt s = case reads s of { [(n, "")] -> Just n ; _ -> Nothing }

-- Rebuild the exact Agda module the witness names.  No search: a witness is
-- reconstructed to one module, and that module is what agda re-checks.
reconstructModule :: SerialCert -> Maybe String
reconstructModule sc = case scWitness sc of
  WRefl            -> agdaCertificateWith (scDefs sc) eq
  WInduction v stp -> fst <$> agdaInductionCertificate (scDefs sc) eq v stp
  where eq = (scLhs sc, scRhs sc)

-- Discover the certificate: prove the equation once and RECORD which witness
-- agda accepted, so it never has to be searched for again.  Same search order
-- and same budget as `certify`; the only difference is the return value.
certifyCert :: [Definition] -> FilePath -> (Equation, String)
            -> IO (Either String SerialCert)
certifyCert defs root (eq, proofNote) =
  case agdaCertificateWith defs eq of
    Nothing -> pure (Left (untranslatableReason defs eq))
    Just reflSource -> do
      (code, out, _) <- runAgdaCached root reflSource
      case code of
        ExitSuccess -> pure (Right (mkSerialCert defs eq WRefl))
        ExitFailure _ ->
          case inductionVariable proofNote of
            Nothing -> pure (Left (firstErrorLine out))
            Just v -> case inductionHypothesis eq v of
              Nothing -> pure (Left (firstErrorLine out))
              Just ih ->
                let ks = take kMaxCongArguments (mapMaybe agdaVar (equationVars eq))
                in tryShapes v (stepShapes ih ks) (firstErrorLine out)
  where
    tryShapes _ [] lastErr = pure (Left lastErr)
    tryShapes v ((_label, stp) : more) _ =
      case agdaInductionCertificate defs eq v stp of
        Nothing -> pure (Left "induction variable outside the equation")
        Just (source, baseLine) -> do
          (code, out, _) <- runAgdaCached root source
          case code of
            ExitSuccess -> pure (Right (mkSerialCert defs eq (WInduction v stp)))
            ExitFailure _
              | blamedLine out == Just baseLine ->
                  pure (Left ("base clause: " ++ firstErrorLine out))
              | otherwise -> tryShapes v more (firstErrorLine out)

-- Replay a serialised certificate: reconstruct the module named by the
-- witness and re-check it with agda.  This is the operation that makes the
-- ledger re-checkable — it trusts the witness, never re-searches.
replayCert :: FilePath -> SerialCert -> IO (Either String ())
replayCert root sc = case reconstructModule sc of
  Nothing     -> pure (Left "witness does not reconstruct to a module")
  Just source -> do
    (code, out, _) <- runAgdaCached root source
    case code of
      ExitSuccess   -> pure (Right ())
      ExitFailure _ -> pure (Left (firstErrorLine out))

-- ------------------------------------------------ reading library.txt
--
-- library.txt is written with the machine's infix `show`
-- (MathMachine.hs ~465): variables are x y z u v w / nⁱ, `0` and other
-- nullary symbols are bare, `+ * ^ gcd max` are infix `(a op b)`, and every
-- other symbol (`s`, `-`, `le`, invented concepts `c0`…) is prefix
-- `f(a,b,…)`.  This parser is the exact inverse of that `show`, so a line the
-- machine wrote parses back to the term it denotes.

-- Operators the machine renders infix (Show instance's list).  Order does
-- not matter here: their first characters are disjoint.
showInfixOps :: [String]
showInfixOps = ["gcd", "max", "+", "*", "^"]

parseShowTerm :: String -> Maybe Term
parseShowTerm s = case pShow (dropWhile isSpace s) of
  Just (t, rest) | all isSpace rest -> Just t
  _                                 -> Nothing

pShow :: String -> Maybe (Term, String)
pShow ('(' : rest0) = do            -- infix: ( term OP term )
  (a, r1)   <- pShow rest0
  (op, r2)  <- pShowOp (dropWhile isSpace r1)
  (b, r3)   <- pShow r2
  case dropWhile isSpace r3 of
    ')' : r4 -> Just (F op [a, b], r4)
    _        -> Nothing
pShow s = do                        -- atom, possibly prefix-applied
  (name, r1) <- pShowName (dropWhile isSpace s)
  case dropWhile isSpace r1 of
    '(' : r2 -> do
      (args, r3) <- pShowArgs r2
      pure (F name args, r3)
    r1' -> pure (atom name, r1')

pShowOp :: String -> Maybe (String, String)
pShowOp s = case [ (op, drop (length op) s) | op <- showInfixOps, op `isPrefixOf` s ] of
  (r : _) -> Just r
  []      -> Nothing

-- A prefix head / atom name: alphanumerics plus `_ #`, or a bare `-` (monus).
--
-- THE WORD-OPERATOR AMBIGUITY, AND WHY THE GREEDY SCAN WAS WRONG (2026-08-20).
--
-- MathMachine's `Show` renders `max` and `gcd` INFIX AND WITHOUT SPACES, so
-- `x max x` is written `(xmaxx)` and `s(0) max x` is written `(s(0)maxx)`.
-- A scan that takes the longest run of identifier characters swallows the
-- operator: it read `xmaxx` as one nullary symbol, then looked for an infix
-- operator, found `)`, and returned `Nothing`.  `parseLibraryLine` therefore
-- failed on EVERY `max` line the machine has ever written — four of the 28
-- lines of `interactive/library.snapshot.txt` — and failed by returning "this
-- line did not parse", which reads as a malformed file rather than as a
-- defect in the reader.  `ProofGate.main` never saw it because its
-- `snapshot` is transcribed by hand in Haskell; anything that reads the FILE
-- (`CertReplay`, and the combined-reach harness) lost those lines silently.
--
-- The repair is to stop the run at any position after the first where one of
-- the word operators begins.  `showInfixOps` is the same list `pShowOp`
-- consults, so the scanner and the operator reader cannot disagree about what
-- an operator is.  Position 0 is exempt, so the PREFIX spellings `gcd(x,0)`
-- and the nullary `max` still read as names; and the guard `not (null taken)`
-- means the stop can never produce an empty name.
--
-- This is a parser repair only.  It changes no verdict about any equation: a
-- line that did not parse produced no candidate at all.
pShowName :: String -> Maybe (String, String)
pShowName ('-' : rest) = Just ("-", rest)
pShowName s = case scan 0 s of
  ("", _)     -> Nothing
  (nm, rest)  -> Just (nm, rest)
  where
    identChar c = isAlphaNum c || c == '_' || c == '#'
    scan :: Int -> String -> (String, String)
    scan _ [] = ("", [])
    scan i t@(c : cs)
      | not (identChar c) = ("", t)
      | i > 0, any (`isPrefixOf` t) showInfixOps = ("", t)
      | otherwise = let (nm, rest) = scan (i + 1) cs in (c : nm, rest)

pShowArgs :: String -> Maybe ([Term], String)
pShowArgs s = case dropWhile isSpace s of
  ')' : rest -> Just ([], rest)
  s'         -> do
    (a, r1) <- pShow s'
    case dropWhile isSpace r1 of
      ',' : r2 -> do (as, r3) <- pShowArgs r2; pure (a : as, r3)
      ')' : r2 -> Just ([a], r2)
      _        -> Nothing

-- A bare name is a variable if it is one of the six universe letters or the
-- machine's out-of-range spelling nⁱ; otherwise a nullary symbol like `0`.
atom :: String -> Term
atom nm
  | [c] <- nm, Just i <- lookup c (zip "xyzuvw" [0 ..]) = V i
  | ('n' : ds) <- nm, not (null ds), all isDigit ds     = V (read ds)
  | otherwise                                           = F nm []

-- One line of library.txt / library.snapshot.txt: "LHS = RHS [note]".  The
-- note is returned verbatim (including its brackets) for `inductionVariable`.
parseLibraryLine :: String -> Maybe (Equation, String)
parseLibraryLine line0
  | all isSpace line0 = Nothing
  | otherwise = do
      let (lhsS, afterEq) = breakOn '=' line0
      rhsAndNote <- afterEq
      let (rhsS, note) = splitNote rhsAndNote
      l <- parseShowTerm lhsS
      r <- parseShowTerm rhsS
      pure ((l, r), note)
  where
    breakOn c s = case break (== c) s of
      (a, _ : b) -> (a, Just b)
      (a, [])    -> (a, Nothing)
    -- Split trailing "[...]" note off the RHS.
    splitNote s = case break (== '[') s of
      (r, note@('[' : _)) -> (r, note)
      (r, note)           -> (r, note)

-- ------------------------------------------------------------- self-test
--
-- Runs the gate against the repository root, on MathMachine's own library
-- snapshot plus deliberate falsehoods.  This is not a measurement standing
-- in for a theorem: each line either produces a machine-checked Agda term
-- or it does not, and the run reports which.

zero_ :: Term
zero_ = F "0" []

su :: Term -> Term
su t = F "s" [t]

bin :: String -> Term -> Term -> Term
bin f a b = F f [a, b]

x_, y_, z_ :: Term
x_ = V 0
y_ = V 1
z_ = V 2

c0 :: Term -> Term
c0 t = F "c0" [t]

-- The concept MathMachine actually invents first, verbatim from its own
-- self-test: "collision-pattern=x+x primitive=c0/1" (MathMachine.hs ~2174).
selfTestDefs :: [Definition]
selfTestDefs = [ Definition "c0" 1 (bin "+" (V 0) (V 0)) ]

-- interactive/library.snapshot.txt, transcribed exactly, in order.
snapshot :: [(String, Equation, String)]
snapshot =
  [ ("x = (0+x)", (x_, bin "+" zero_ x_), "[induction on x]")
  , ("s(x) = (s(0)+x)", (su x_, bin "+" (su zero_) x_), "[induction on x]")
  , ("(s(x)+y) = s((x+y))", (bin "+" (su x_) y_, su (bin "+" x_ y_)), "[induction on y]")
  , ("(x+y) = (y+x)", (bin "+" x_ y_, bin "+" y_ x_), "[induction on x]")
  , ("(x+(x+y)) = (y+(x+x))", (bin "+" x_ (bin "+" x_ y_), bin "+" y_ (bin "+" x_ x_)), "[induction on y]")
  , ("(x+(y+y)) = (y+(x+y))", (bin "+" x_ (bin "+" y_ y_), bin "+" y_ (bin "+" x_ y_)), "[induction on x]")
  , ("(x+(y+z)) = (y+(x+z))", (bin "+" x_ (bin "+" y_ z_), bin "+" y_ (bin "+" x_ z_)), "[induction on x]")
  , ("0 = (0*x)", (zero_, bin "*" zero_ x_), "[induction on x]")
  , ("x = (s(0)*x)", (x_, bin "*" (su zero_) x_), "[induction on x]")
  , ("(s(x)*y) = (y+(x*y))", (bin "*" (su x_) y_, bin "+" y_ (bin "*" x_ y_)), "[induction on y]")
  , ("(s(x)*y) = (y+(y*x))", (bin "*" (su x_) y_, bin "+" y_ (bin "*" y_ x_)), "[induction on x]")
  , ("(x*(x*y)) = (x*(y*x))", (bin "*" x_ (bin "*" x_ y_), bin "*" x_ (bin "*" y_ x_)), "[induction on x]")
  , ("(x*(y*z)) = (x*(z*y))", (bin "*" x_ (bin "*" y_ z_), bin "*" x_ (bin "*" z_ y_)), "[induction on y]")
  , ("s((x*c0(x))) = s((c0(x)*x))", (su (bin "*" x_ (c0 x_)), su (bin "*" (c0 x_) x_)), "[induction on x]")
  , ("s((x*c0(y))) = s((c0(y)*x))", (su (bin "*" x_ (c0 y_)), su (bin "*" (c0 y_) x_)), "[induction on x]")
  , ("s(s((x*y))) = s(s((y*x)))", (su (su (bin "*" x_ y_)), su (su (bin "*" y_ x_))), "[induction on x]")
  , ("(x*y) = (y*x)", (bin "*" x_ y_, bin "*" y_ x_), "[induction on x]")
  , ("x = (xmaxx)", (x_, bin "max" x_ x_), "[induction on x]")
  , ("s(x) = (xmaxs(x))", (su x_, bin "max" x_ (su x_)), "[induction on x]")
  , ("s(x) = (s(x)maxx)", (su x_, bin "max" (su x_) x_), "[induction on x]")
  , ("(xmaxs(0)) = (s(0)maxx)", (bin "max" x_ (su zero_), bin "max" (su zero_) x_), "[induction on x]")
  , ("0 = -(x,x)", (zero_, bin "-" x_ x_), "[induction on x]")
  , ("0 = -(x,s(x))", (zero_, bin "-" x_ (su x_)), "[induction on x]")
  , ("s(0) = -(s(x),x)", (su zero_, bin "-" (su x_) x_), "[induction on x]")
  , ("0 = le(s(x),x)", (zero_, bin "le" (su x_) x_), "[induction on x]")
  , ("s(0) = le(x,x)", (su zero_, bin "le" x_ x_), "[induction on x]")
  , ("s(0) = le(x,s(x))", (su zero_, bin "le" x_ (su x_)), "[induction on x]")
  , ("le(x,0) = -(s(0),x)", (bin "le" x_ zero_, bin "-" (su zero_) x_), "[induction on x]")
  ]

-- Equations that are FALSE.  A gate that admits any of these is worthless,
-- so they are checked with the same code path and the same budget.
falsehoods :: [(String, Equation, String)]
falsehoods =
  [ ("s(x) = x  [FALSE]", (su x_, x_), "[induction on x]")
  , ("(x+y) = (x*y)  [FALSE]", (bin "+" x_ y_, bin "*" x_ y_), "[induction on x]")
  , ("x = le(x,x)  [FALSE]", (x_, bin "le" x_ x_), "[induction on x]")
  , ("(xmaxy) = (x+y)  [FALSE]", (bin "max" x_ y_, bin "+" x_ y_), "[induction on x]")
  ]

-- Not in the snapshot: exercises the gcd import path, which no snapshot
-- line reaches and which is the one symbol translated to a cubical
-- definition that does not reduce structurally.
extras :: [(String, Equation, String)]
extras =
  [ ("gcd(x,0) = x", (bin "gcd" x_ zero_, x_), "[induction on x]")
  ]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  let root = case argv of { (p : _) -> p ; [] -> "." }
  printf "Certificate self-test (repository root %s).\n" (show root)
  printf "budget = %d agda calls per candidate.\n" kMaxAgdaCalls
  on <- cacheEnabled
  printf "certificate cache: %s at %s\n\n"
    (if on then "ON" else "OFF (MATH_CERTCACHE)" :: String)
    (show (root </> kCertCacheDir))
  t0 <- getCurrentTime
  putStrLn "== interactive/library.snapshot.txt =="
  trues <- mapM (report root) snapshot
  putStrLn ""
  putStrLn "== beyond the snapshot =="
  extraVs <- mapM (report root) extras
  putStrLn ""
  putStrLn "== deliberate falsehoods (must all be rejected) =="
  falses <- mapM (report root) falsehoods
  t1 <- getCurrentTime
  putStrLn ""
  let ok = length [ () | Certified _ _ <- trues ]
      skipped = length [ () | Untranslatable _ <- trues ]
      everything = trues ++ extraVs ++ falses
      worst = maximum (0 : map spent (trues ++ falses))
      admitted = [ () | Certified _ _ <- falses ]
      totalCalls = sum (map spent everything)
      hits = length [ () | v <- everything, spent v == 0, not (isSkip v) ]
      isSkip (Untranslatable _) = True
      isSkip _ = False
  printf "snapshot: %d/%d certified, %d rejected, %d untranslatable\n"
    ok (length snapshot) (length snapshot - ok - skipped) skipped
  printf "worst-case agda invocations observed: %d (bound %d)\n" worst kMaxAgdaCalls
  printf "total agda invocations this run: %d over %d candidates (%d fully cached)\n"
    totalCalls (length everything) hits
  printf "wall clock for the gated section: %.2f s\n"
    (realToFrac (diffUTCTime t1 t0) :: Double)
  if null admitted
    then do
      printf "falsehoods: %d/%d rejected\n" (length falses) (length falses)
      putStrLn "CERTIFICATE GATE CHECKED"
      exitSuccess
    else do
      putStrLn "UNSOUND: a false equation was certified"
      exitFailure
  where
    spent (Certified _ n) = n
    spent (Rejected _ n) = n
    spent (Untranslatable _) = 0
    report root (label, eq, note) = do
      v <- certifyWith selfTestDefs root (eq, note)
      case v of
        Certified how n ->
          printf "  OK    %-26s %-52s (%d call%s)\n" label how n (plural n)
        Rejected err n ->
          printf "  NO    %-26s %-52s (%d call%s)\n" label (clip err) n (plural n)
        Untranslatable why ->
          printf "  SKIP  %-24s %s\n" label why
      pure v
    plural (1 :: Int) = ""
    plural _ = "s"
    clip s = let t = intercalate " " (words s)
             in if length t > 52 then take 49 t ++ "..." else t

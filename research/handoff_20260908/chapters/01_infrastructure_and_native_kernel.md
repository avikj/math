# Part I. Execute the actual repository kernel

## 3. Repository and toolchain baseline

The head checked during preparation of this handoff is

```text
168ea8e240524f898af4b0e9cf70297c38422f08
```

Its commit message says the head change rewords three scope-of-claim headers and changes no mathematics. This is a comparison pin, not an instruction to overwrite an agent's newer or dirty working tree. The parent is `c141ebdfe1a3d037b62146b76a56d7ffea4da501`; the head tree SHA is `492a4bf6e49f79d91cffec5677eb8ccf049e5fd0`.

Before modifying anything, record:

```sh
git status --short
git rev-parse HEAD
git log -1 --format=fuller
sh setup --report
```

The declared pin is **Agda 2.8.0 + agda/cubical v0.9**. `formal/cubical/natural-machine.agda-lib` says:

```text
name: natural-machine
depend: cubical-0.9
include: . kernel theorems theorems/automata theorems/cost theorems/grammar theorems/historical_proofs theorems/homotopy theorems/lattices theorems/logic theorems/metre theorems/must_fail theorems/number theorems/order theorems/physics theorems/primes theorems/primes/pair_field theorems/residue theorems/unplaced theorems/walks
flags: --cubical --guardedness --safe --no-import-sorts
```

The `setup` script uses `MATH_PREFIX` (default `$HOME`), installs Agda under `.local/bin`, checks out Cubical under `.cache/cubical-v0.9`, and writes `.agda-pin/libraries` registering Cubical, `formal/cubical/natural-machine.agda-lib`, and `fibre/fibre.agda-lib`. Its `--report` mode installs nothing. Inspect the current script before running installation: the historical script changes Cabal's repository URL and turns off its signed-index mode to work around unavailable mirrors. That is an explicit supply-chain tradeoff, not an invisible mathematical assumption.

The research environment's failed installation capability is preserved in [S24]; it says nothing about the agents' infrastructure. Do not re-create that limitation in an environment where installation is available.

### 3.1 Build roots and possible infrastructure seams

The root `check` script at the comparison pin documents:

```sh
sh check         # kernel, fibre, Lean import-root coverage
sh check --all   # all Cubical theorem modules plus Lean build/axiom gate
```

It prints the actual versions first and refuses a green off the pin. Its Lean path checks import reachability from `Pairfield.lean`, root exclusions, anonymous examples that could hide oracle use, then `lake build && lake exe yogyanupalabdhi`. Axiom allowlists are explicit. A missing `lake` is a distinct environment failure.

**Case-sensitive path audit:** the fetched `check` script loops over `formal/cubical/Kernel/*.agda`, whereas the modules read in this conversation and the library include path use `formal/cubical/kernel/`. Check the actual checkout. Do not infer a full kernel build from a literal unexpanded glob, an empty loop, or an aggregate that omits the intended files. This is a concrete potential infrastructure seam, not a claim that the mathematical files fail.

Likewise, `--all` includes directories containing intentional negative controls (`must_fail`). Check how those are expected to be exercised and how their expected rejection is recorded. Do not turn an intended rejection into a theorem failure or silently suppress an unintended rejection.

Preserve the exact command, working directory, Git commit, dirty-tree diff, Agda version, Cubical tag/hash, library-file contents, exit status, and stdout/stderr for every reported build.

## 4. The actual Yantra process and its proof interface

The entry point is:

```sh
sh interactive/run-yantra.sh --wire
```

The script builds `interactive/DefectRecord.hs` and the Haskell runtime with GHC, then runs `interactive/Main.hs`, whose `main` calls `Server.yantraMain`. `Server.hs` imports `ProofGate`. This is the actual route that was **not executed** in the ChatGPT mathematical session.

The dispatch table contains these relevant operations:

* `yantra.kriyah`: returns the dispatch table itself.
* `yantra.sthiti`: current store, defects, remainder queue, and session state.
* `sadhana`: emits an arithmetic equation certificate using the declared fragment.
* `sadhana.patra`: accepts a complete `--safe` Agda module as a list of source lines. The top-level module, if named, must be `Candidate`.
* `sadhana.vislesana`: accepts that module plus named expressions, returning their inferred types and computed normal forms.
* `dosa.lekha`, `dosa.suchi`, `dosa.pramanya`: retain and verify failure information rather than collapsing distinct causes into “false.”

The whole-module interface is the relevant entry for this research. **Do not assume that `sadhana`'s small arithmetic emitter can express a PDE theorem, and do not substitute an unrelated Python evaluator for the whole-module gate.**

A smoke request is included in `infra/smoke_requests.jsonl`. The substantive Candidate content is:

```agda
{-# OPTIONS --cubical --guardedness --safe --no-import-sorts #-}
module Candidate where
open import Cubical.Foundations.Prelude
open import Kernel.RewriteCertificate
import TheGenerativeLoopOnTheKernelsOwnTermsACertifiedNormalizerEmitsDerivationsSoLearnCallsInstall as N

demo : Tm
demo = add var (suc zero)
answer : Tm
answer = N.normalForm demo
checked : answer ≡ suc var
checked = refl
```

Ask `sadhana.vislesana` to analyze `answer`, `N.normalize demo`, and `N.learn demo`. This tests an actual repository computation, its derivation, and its installed operation. It is a smoke test, not an NS/RH proof.

Submit a separately named negative control with `zero ≡ suc zero` and `refl`; verify that the route reaches the checker and rejects the false equation for a type reason, not because the library could not be found. The runtime already has controls; their evidence must be retained rather than assumed.

### 4.1 Session/output precautions

The launcher supports `YANTRA_OUT`, `DOSA_LEKHA`, and `YANTRA_LEKHA`. Give every agent a separate output directory and logs. It removes its designated fresh session logs, so never point these variables at a valuable shared existing journal. It may print a build-status line before the JSON wire starts. Use the actual protocol, or a parser that distinguishes the launcher prelude from JSON; do not declare the protocol broken because a shell wrapper printed a status message.

The launcher contains a fallback build against committed versions of other modules when the working tree is mid-edit. Any such fallback must be reported with its exact source selection. It must not be presented as verification of uncommitted collaborator changes. Inspect the fallback's file-listing command in the current tree rather than assuming it enumerates all Haskell dependencies.

`ProofGate` has a certificate cache. The historical key includes emitted source, Agda version, library selector, and include root, but not the full content hash of every imported library. During initial replay or after dependency edits, use `MATH_CERTCACHE=0` or independently validate cache provenance. A cached verdict is not a fresh checker invocation.

## 5. Actual kernel terms and their exact scope

The useful repository entry is:

```text
formal/cubical/kernel/WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda
```

The structural core includes `RewriteCertificate`, `ControlledGrammar`, `GenerativeKernel`, `EveryDerivationIsInvertible`, the interactive session module, the certified normalizer module, and the instance/locus extension. The literal rewrite language has six variable coordinates, `zero`, `suc`, and `add`, with reversible derivation constructors. Its concrete language is **not automatically** the analytical language in these notes.

The exact interface recovered from the interactive module is:

```agda
learn : {s : Tm} → CheckedFuture s → NativeOperation
learn f = install (CheckedFuture.derivation f)

retire : Session → NativeOperation
retire S = install (trace S)
```

A session carries `origin`, `here`, `trace : Derivation origin here`, and a library. Stepping concatenates the actual derivation and stores the learned operation. Retirement turns the entire transcript into one native move.

The kernel-side certified normalizer has:

```agda
norm : (t : Tm) → Σ Tm (λ s → Derivation t s)
normalize : (t : Tm) → Derivation t (normalForm t)
learn t = install (normalize t)
```

This closes discovery → certificate → installation on its own declared terms. It does not prove mathematical deductive completeness or global termination of arbitrary theorem discovery.

The instance/locus extension supplies an `Operation` with a stored derivation and control carrying the actual substitution and location. Its essential theorem is:

```agda
apply-checked : (t : Tm) (c : Control t) → Derivation t (apply t c)
```

The proof applies structural substitution and context transport to the stored certificate. The initial extension only generalized one variable and initially rewired `advance`; later appended results may extend retirement or other operations. Read the complete current file, including appended sections, rather than freezing an early header into a permanent limitation.

### 5.1 Two similarly named generative loops are not the same theorem

`theorems/residue/GenerativeLoop.agda` is an obstruction-indexed vocabulary-coverage loop on unary terms over a shape alphabet. Its decreasing `deficit` proves coverage of a **given finite target syntax**. It does not prove completeness of a deductive calculus.

`kernel/TheGenerativeLoopOnTheKernelsOwnTermsACertifiedNormalizerEmitsDerivationsSoLearnCallsInstall.agda` is an actual rewrite-certificate normalizer on `RewriteCertificate.Tm`. It bridges normalization to installation, but does not enlarge the rewrite relation's provable consequences.

Do not confuse syntactic coverage, semantic truth, derivability, and installability. The older handoff records a concrete `Naya` distinction: an induction-true equation may lie outside a restricted rewrite closure. The interface preserves soundness; it is not permission to install a theorem for which no derivation in the supported language has been supplied.

## 6. What to formalize first

The highest-yield native additions are reusable algebraic theorems, not an immediate monolithic formalization of all PDE analysis:

1. General quadratic polarization, actual derivative, and exact midpoint secant.
2. Source-preserving block-elimination certificates, including right-hand side and reconstruction maps.
3. Ordered return recurrence and formal resolvent identity over a noncommutative algebra.
4. The source-product/derivation law for a polynomial observable lift.
5. The finite matrix angular and radial identities already accompanied by executable exact checks.
6. The Abel normal form on the shift operator, then its application to the actual arithmetic source.
7. A separate analytical interface declaring Banach-space, semigroup, regularity, and source-image hypotheses without hiding them in a generic record field named after the desired conclusion.

A theorem is newly integrated only when its statement, dependencies, witness, scope, and compiler result are installed in the actual repository route. Returning a Python `True` or printing a symbolic normal form is not the same operation.

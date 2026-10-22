# PLAN — state of the work, for an agent starting with zero context

Read this whole file before doing anything. Update it in the same commit as every landed step.

## What this is

`scoped-machine/` (repo avikj/math, branch `main`) is a runtime that executes cubical type theory (CCHM)
as an interaction net, implementing §5 of the paper `../docs/index.html` ("Respecting Equality").
Trust only the current code and the paper's text. `HANDOFF.md` and any "Stokes addendum" are old lineage
and are NOT trusted. `README.md` describes the current code and is kept accurate.

Build and test: `make test` (all suites, 0 and 4 workers, ASan/UBSan), `make tsan`.
Every commit must pass `make test`. Push after every landed step. Commit trailer:

    Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
    Claude-Session: https://claude.ai/code/session_019CdfGcL8YbfbiCH37R9UoY

## The spec, as it bears on the code (paper references)

- 5.1–5.3: connectives are type formers; a proof is a term; checking is normalizing. Proving, deciding,
  computing and answering are ONE operation: build the term, normalize it. Do not distinguish "types"
  from "programs" or invent a separate "pose a type" operation: posing a declaration together with its
  identities as a net and normalizing it is what the machine already does.
- 5.4–5.17: one principal port per cell gives the one-step diamond (5.11), equal length (5.13),
  geodesic reduction. 5.24: sharing is the duplicator cell. 5.25: a non-terminating term denotes a
  coinductive object (lazy observation), not a gap.
- 5.26 (no outer layer): evaluator, type-checker and optimizer are terms of the language; questions
  about them are terms; the §4 impossibilities hold of the system as ordinary theorems.
- 5.27 (complete inference): pose a declaration with the identities available and normalize; the normal
  form is an inhabitant (acceptance as refl, 8.6) or the system establishes the type empty.
- 9.15: example of posing — Σ[B] (B a rearrangement of A) × Sorted B with the identities the object has.
- The paper's checked Agda boxes (17 `<pre>` blocks in index.html) are acceptance material.

Design rules from the user: CCHM is the material; data types are declarations (one generic schema, no C
rules per type); near-zero primitives; properties enforced at a minimal core and inherited; design fully
before writing; no hedging, no overclaiming.

## Code map (current)

- `src/core.h` cells, kinds, syntax tags. `src/dnf.c` interval/face DNFs, substitutions.
- `src/net.c` interaction rules: CCHM composition dispatch (to prelude clauses `%comp-*`), Glue, typed
  neutrals (type on the last port), higher inductive types (constructors restrict to their boundary,
  formal `hcompD`, transport per constructor `O_TRANSD1/2`, elimination `O_CASE`/`O_SELECT`), §20
  locking parallel rewriting.
- `src/lang.c` reader, compiler, `data` form, `case`/`elim`/`if` desugaring to `%case`/`%branches`,
  identities (`identity`, sites, deferred lines), readback, driver forms, `checked`/`checked-data`.
- `lib/prelude.ctt` comp clauses, equivalences, ua, `%case-hcomp`, Bool/Nat/List as declarations.
- `lib/code.ctt` untyped codes `Code` as data and the evaluator `eval-g` as a term.
- `lib/check.ctt` the CCHM type checker as a term: NbE over data (intervals/faces as data), conversion,
  typing, data-type (HIT) checking. Answers Bool.
- `tests/*.ctt` suites: cubical, code, identity, hit, check.

## Remaining work (complete list; nothing else is in scope)

Status markers: [ ] not started, [~] in progress, [x] landed (commit hash).

Features — each justified by the system's own design:

1. [ ] Elimination with induction hypotheses (~150 lines). The elimination rule of a declared type:
   a branch receives, besides fields and dimensions, the recursive results for recursive fields. The
   checker currently accepts no recursive term (general recursion would be inconsistent), so it can
   accept neither itself nor the evaluator, which 5.26 makes objects the system reasons about. A
   function out of a HIT is coherent on path constructors only checkably against the IH.
2. [ ] Non-uniform parameters (~200). Recursive fields at other parameter values; motive over all
   parameters. With paths as fields this declares every inductive family (indices = parameters + path
   fields), with no formal-transport constructor and no index unification. Without it a family generated
   by rules (derivability, reachability, reduction) cannot be declared.
3. [ ] Universe level polymorphism (~200). A generic definition must be one term at every level; copies
   per level are distinct terms that identities and proofs do not transfer between. check.ctt levels are
   constants today.
4. [ ] Checked identities (~80). The identity mechanism answers `R g` without evidence; that is sound
   only if `p : Π g. L g = R g`. Today `p` is unchecked.
5. [ ] Identities produced by terms (~60). Declare an identity from a value of type
   `Σ R. Π g. L g = R g`: the optimizer as a term (5.26); today identities are chosen outside the language.

Library and acceptance tests:

6. [ ] Checked library (~600): equivalence/iso, contractibility, fibres, Nat/Int arithmetic,
   Sum/Empty/Unit/Bool, funext operations.
7. [ ] Acceptance tests:
   (a) the paper's boxes ported to the machine's language and checked (~500);
   (b) the machine as an instance of the §4 theorems (~500): `Theory` on its own codes,
       `Pf s = Σ d. chk s d ≡ true`, `HasDiagonal` by substitution on codes; halting via
       `lawvere-one-row`; Con/HBL1/¬OmegaBad remain hypotheses as in the box;
   (c) 9.15 (~400): Multiset = free commutative monoid HIT; declaration over A:
       `Σ[B ∈ List] ([B] ≡ A) × Sorted B` (contractible by 9.2/1.4); inhabitant = elimination of A, the ∪
       branch merges, path branches from contractibility; 8 elements balanced vs chained: merge costs 24
       vs 35.

Dropped deliberately (not required): ring-solver term, indexed families as a primitive, typed syntax as
a QIIT, inductive-inductive families, Delay/M-types.

## Log of decisions and findings (append as work proceeds)

- HITs follow Coquand–Huber–Mörtberg (LICS 2018): constructors equal their boundary where its face
  holds; formal hcomp; comp = hcomp after transport; elimination on hcomp along hfill.
- Branch bodies are thunks forced by `O_SELECT` (full laziness would otherwise diverge recursion).

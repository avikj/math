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

## CURRENT DIRECTION (2026-10-22, supersedes the item list below)

Findings, established by reading the code and the history (git log 10-14..10-22):

1. There is one operation: normalizing (5.1–5.3). Checking, evaluating, judging are names for it.
   "t : A" internally is a type over codes, HasType ⌜t⌝ ⌜A⌝; its normal form is a derivation or
   it is established empty. A Bool-valued checker is the lossy decide-projection of that (8.4–8.6).
   The theory expresses its own normalization as an internal object (5.26), like a C++ compiler
   written in C++; that internal object must run on the same reduction, at zero added cost.
2. What went wrong: the net normalizes CCHM natively (cells for λ, Π, Σ, PathP, Glue, comp, systems,
   data/con/hcomp/case, typed neutrals). `lib/code.ctt` has `eval-g`: Code → the net's own value. The
   RETURN (net normal value → Code) was never written. So `lib/check.ctt` carries a second, complete
   CCHM normalizer over data (lines ~48–610: intervals, faces, Val/Neu, act, comp-*, data transport,
   veval), and every "ok: checks" is that copy's verdict at interpretive cost (lemIso 276M steps).
   History: 10-20 on the C machine a code WAS the machine's own term record (`c82a17e` quote), so
   the return was the identity; the 10-21 from-scratch net (`77f566e`) made Code separate data with
   only the one-way eval-g; `8b27dfd` then wrote the duplicate normalizer. All later checker perf work
   (masks, interning, defunctionalized branches, on-demand neutral types) and proof reshaping
   (η-expanded transportIsEquiv, hp/pp arguments in equivEq/msort-at) existed only because of it.
3. Rule: nothing may take more interactions than hand reduction. `case` costs 22 interactions per
   level of a two-way case (hand: ~3: select, substitute, call) because `ds()` compiles it to closed
   branch λs + an environment λg. g shared..., thunks, %branches records, O_CASE→O_SELECT→apps→force.
   Measured: (lebc 1 2) − (lebc 0 2) = 11 O_APP, 2 O_FORCE, 2 O_CASE, 2 O_SELECT, 2 O_DUP, 3 O_ERA.

Work, in order:

A. [x] `case` = one interaction (landed; one level of lebc: 22 → 5 interactions = hand count;
   8-element merges 3492 → 1346; tests/check.ctt 6.6M → 3.5M). Also: closed-λ/constant definitions unfold in
   one interaction (built from syntax), saturated constructor applications compile to the constructor,
   a case without a motive has no motive port. The case cell carries a static table of branch records (one
   multi-parameter Record per constructor: parameters = fields, hypotheses, dimensions; environment =
   the shared variables), and the shared variables once as ports. CASE meets CON: build the selected
   branch's record with the constructor's fields and the case's environment ports (unused ones erased).
   Hypotheses: V_SUSP holding the table, motive, field, environment copies; forcing it is a CASE.
   hcomp: %case-hcomp takes the case as a function value. Neutral case reads back with its branches
   built on fresh variables.
B. [x] The return path (landed). Not a deep QUOTE but %view: one
   interaction turning a value's head into a View constructor whose fields are the value's own parts
   (lib/code.ctt `View`; neutrals carry their type). The checker's values ARE the net's values:
   eval-g builds them (lists for environments), application/projection/comp/Glue/endpoints are the
   net's own steps; conversion walks views, typed at Π/Σ/path/Glue/data so variables carry types.
   Primitives (src/net.c, one interaction each, numerals counted one per interaction): %view,
   %var k T / %dim k (variables and dimensions at de Bruijn levels: LVL_TAG, DIM_LVL), %abs k v (the
   line binding level-dim k), %ieq/%feq (canonical DNF equality → Bool), %clauses φ, %restrict c v,
   %branch f c params (branch c of an elimination at given fields/hypotheses/dimensions: eliminations
   compare by branches with hypotheses as variables), %gval/%gty/%dtab/%dent n (the checker's tables
   in lang.c: references to globals; %gval gives the definition's own value, not following its
   identities). U carries its level (prelude Level gains lomega = the level of types over levels).
   No signature value is threaded anywhere. check.ctt: 1066 → ~550 lines; the duplicate normalizer is
   gone. tests/check.ctt: 3.5M → 1.53M interactions (9.2M this morning).

C. [x] Neutral types in the NET computed from the spine (O_NTYPE), only a variable stores one; the
   endpoint rule p@0 copies the spine, computes the type, answers the endpoint (O_PEND). Same
   exponential as 2026-10-22 morning's check.ctt fix, now at the machine (diagonalGivesGoedelFix
   stalled > 10 min; now 3.2M). %clos: two λs of one record compare by (copies of) their environments,
   falling back to applying both (pathToEquiv-ua: 741M → 0.7M).
   Results (`make library`): std+boxes 154/154, 62M interactions, 37 s (morning: 605M, 468 s);
   std+sort 106/106, 77M, 41 s (400M, 307 s); lemIso 20.7M (276M); tests/check.ctt 1.12M (9.2M).
   msort readings: balanced 20985 interactions (6556 erasures), chained 26429 (9622).

D. [x] Copies a hand reduction does not make, removed by principle (located with CUBICAL_PROFILE's
   dup/era origins): a case branch mentioning its scrutinee rebuilds it from its fields; V_REF holds
   a value once (a variable's type, the checker's context types via %box); closed constant
   definitions (λ, constructor, data type) unfold in one interaction.
   State: tests/check.ctt 0.53M; boxes 154/154 17.3M interactions 10 s; sort 106/106 44.7M 23 s
   (lemIso 5.7M, msort-at 30M).
E. [x] (user approved) Stored values are read one level at a time: V_REF holds a value once
   (refcounted Box); an operation meeting a reference copies its top cell, parts become references
   (lazy_copy). A duplicator meeting a value with parts boxes it and gives each side a reference.
   Words: V_WORD holds a machine word (`#n`), %wsucc %weq %wlt %wadd %wmax %wsub, %welim w z s (the
   dependent eliminator; the hypothesis is a V_WSUSP forced on use). Saturated calls of λ-chain
   definitions (S_CALL/O_CALL) are one interaction building the n-ary record.
   State: boxes 154/154 6.2M interactions; sort 106/106 18.7M; tests/check.ctt 0.26M.
F. [x] Codes carry their compiled terms (landed). lang.c `ann` emits, for `checked` forms, data
   declarations and identity evidence, a `Tm` (lib/check.ctt): every node carries its value, the
   machine's value of that subterm (let-bound, so each value is computed once from its parts'
   values; a binder's value is the compiled binder; checked definitions are (%gval #n)). A binder
   node holds a function: λ x xT. code-of-body for a term binder (a variable's node is (tv x xT)),
   λ i. code-of-body for a dimension. A system's branches are thunks, restricted then forced, so a
   branch is computed under its face. A data declaration is a `Tel` (parameters, then each
   constructor's fields, dimensions, boundary). check.ctt has no context, no eval-g, no counter:
   (%var T) and (%dim) make fresh names (never lifted out of their level, lang.c maxlev).
   Indices, levels' constants, constructor and data indices are words; `Num` is gone (code.ctt's
   plain Code for tests/code.ctt also uses words). `(%raw t)` passes an already desugared term.
   Also: the lifting test walks only until it meets a variable of the current level (was
   quadratic in let chains: 29 s → 2.3 s for boxes).
   State: tests/check.ctt 0.16M; boxes 154/154 2.85M, 2.3 s; sort 106/106 9.1M, 5.9 s
   (msort-at 7.1M, lemIso 0.31M).
G. [ ] Word typed in the checker (a type Word, #n : Word, %wsucc, %welim's dependent rule);
   Word ≃ Nat proved in the language (toNat/fromNat, round trips by induction, ua), and %weq %wlt
   %wadd %wmax declared as identities with inductive evidence, so the machine's operations stay
   representable inside the theory (5.26).
H. [ ] msort-at: 7.1M interactions — find what it does that hand checking does not.

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

1. [x] Elimination with induction hypotheses (~150 lines). The elimination rule of a declared type:
   a branch receives, besides fields and dimensions, the recursive results for recursive fields. The
   checker currently accepts no recursive term (general recursion would be inconsistent), so it can
   accept neither itself nor the evaluator, which 5.26 makes objects the system reasons about. A
   function out of a HIT is coherent on path constructors only checkably against the IH.
2. [x] Inductive families generated by rules (~100, a test, no schema change). Re-derived while doing
   item 1: such a family is Σ (t : T) (valid t indices), T a uniform data type of derivation trees and
   `valid` by recursion on t into U. Needs item 1 and large elimination only. Deliver: Trace (the equal-length
   box's family) declared this way, eliminated, and checked, in tests/check.ctt.
3. [x] Universe level polymorphism (~200). A generic definition must be one term at every level; copies
   per level are distinct terms that identities and proofs do not transfer between. check.ctt levels are
   constants today.
4. [x] Checked identities (~80). The identity mechanism answers `R g` without evidence; that is sound
   only if `p : Π g. L g = R g`. Today `p` is unchecked.
5. [x] Identities produced by terms (~60). Declare an identity from a value of type
   `Σ R. Π g. L g = R g`: the optimizer as a term (5.26); today identities are chosen outside the language.

Library and acceptance tests:

6. [x] Checked library (~600): equivalence/iso, contractibility, fibres, Nat/Int arithmetic,
   Sum/Empty/Unit/Bool, funext operations.
7. Acceptance tests:
   (a) [x] the paper's boxes ported to the machine's language and checked (~500);
   (b) [ ] the machine as an instance of the §4 theorems (~500): `Theory` on its own codes,
       `Pf s = Σ d. chk s d ≡ true`, `HasDiagonal` by substitution on codes; halting via
       `lawvere-one-row`; Con/HBL1/¬OmegaBad remain hypotheses as in the box;
   (c) [x] 9.15 (~400): Multiset = free commutative monoid HIT; declaration over A:
       `Σ[B ∈ List] ([B] ≡ A) × Sorted B` (contractible by 9.2/1.4); inhabitant = elimination of A, the ∪
       branch merges, path branches from contractibility; 8 elements balanced vs chained: merge costs 24
       vs 35.

Dropped deliberately (not required): ring-solver term, indexed families as a primitive, typed syntax as
a QIIT, inductive-inductive families, Delay/M-types.

## Log of decisions and findings (append as work proceeds)

- HITs follow Coquand–Huber–Mörtberg (LICS 2018): constructors equal their boundary where its face
  holds; formal hcomp; comp = hcomp after transport; elimination on hcomp along hfill.
- Branch bodies are thunks forced by `O_SELECT` (full laziness would otherwise diverge recursion).
- Item 1 (landed): `(rec x)` in a branch = induction hypothesis of recursive field x (field whose declared
  type is D itself). Machine: `%branches D mask b...` (mask = branches taking hypotheses); O_SELECT with
  mask bit builds one V_SUSP (branches, motive, field) per recursive field; O_FORCE on V_SUSP = O_CASE.
  Branch binder order everywhere: fields, hypotheses (one per recursive field), dimensions. Codes: a branch
  not using hypotheses still binds them in its code; `(cforce t)` is the code of `force` (identity in the
  checker). Checker: velim passes hypotheses = velim of recursive fields; branch typing binds them as
  those eliminations (type P f); conversion of eliminations uses fresh hypotheses.
- Found and fixed while doing item 1 (all pre-existing): `ff`, `tt`, `0`, `1`, `U` are constants even when
  bound, so check.ctt's `(let ff ...)` in conv-branches-at and comp-glue and `(some U)` in let-checking
  silently used the constants; the compiler now rejects binding a constant. Eliminations without a motive
  were compared at an unknown type (always false); now `uconv` compares them without a type.
- Item 2 re-derived: NOT a schema change. An inductive family generated by rules is
  Σ (t : T) (valid t indices) with T a uniform data type of derivation trees and `valid` defined by
  recursion on t into U (item 1 + large elimination). No non-uniform parameters needed. Item 2 is done by
  a test showing such a family (Trace) declared, eliminated and checked.
- Item 3 (landed): codes clevel/clzero/clsuc/clmax, cuniv takes a level code; checker values vlevel,
  vlvl c ts (max over neutral atoms, compared as joins), vuw (sort of level-quantifying types, no type);
  infer-sort for Π/Σ/annotations/definitions/parameters, infer-level (a U_l) where a universe at a level
  is needed (paths, Glue, data fields). Data levels must be closed. Machine: `(data Level ...)` in the
  prelude; U ignores its level. Paths in Level are not formed (Level : Uω); level equality shows as
  conversion of universes.
- Item 4 (landed): `(checked-identity L R p [n])`, `checked-identity-fail`, `supply-fail`; checker
  functions id-tele, id-type, chk-identity-def, chk-identity at the end of check.ctt. Plain `identity`
  stays the unchecked machine form, parallel to `def` vs `checked`.
- Item 5 (landed): `(identity-from L e [n])`, `checked-identity-from[-fail]`; checker opt-type,
  chk-optimizer. Test: map fusion `fuse` proved by induction, applied to `twomaps`.
  Found and fixed: eliminations of an elimination without a motive could not be compared (the inner
  neutral had no type); branches now carry (brs d sg bs) and fields of untyped scrutinees are fresh
  untyped variables. Codes of a constructor short of fields are eta-expanded.
- Items 6/7a (in progress, uncommitted work in lib/std.ctt and tests/boxes.ctt): the checked library
  (data via check-data of the prelude's Bool/Nat/List, Empty/Unit/Sum/Int; paths; contractibility,
  fibres, equivalences, lemIso/isoToEquiv, ua, uaβ, pathToEquiv, isPropIsContr, isPropIsEquiv, toPathP,
  isProp→PathP, equivEq (Σ≡Prop at isEquiv, propositionality as an argument), pathToEquiv-ua; Nat
  arithmetic and semiring laws; le; not, true≢false; negZ). Boxes 0,2,3,4,6,7,9,11,12,15 ported.
  Box 9's Trace is defined by recursion on its length index (Trace 0 s t = s ≡ t; Trace (n+1) s t =
  Σ u. Step s u × Trace n u t); box 15's solveℕ! steps are explicit chains (generated by a script; the
  generator's output is what is in boxes.ctt).
- Language additions made for the library: telescopes (Pi ((x A) (y B)) C); PathP over a line given
  as a term; infer of plam (a line's type from its body), so lets can bind squares; a motive may be any
  term of type Π x:D. U; (check-data D) checks a data type already declared; (case e D)/(elim P e D)
  for a type with no constructors; codes of unsaturated constructors are eta-expanded; binding a
  keyword or a constant is an error.
- Performance of the checker (all landed or in the working tree, every change semantics-preserving):
  environment trimming (closures keep only the entries their body uses, by a Bool mask cfv); variables'
  types are not re-substituted by substitutions of later dimensions; branches are code + environment
  (Brs d sg cs env), only the selected branch is evaluated; two eliminations with the same codes over
  convertible environments convert without evaluating branches; codes are interned as shared global
  definitions (%cN) so copying a code is copying a reference; global lookup by hash. lemIso: 1.1G → 161M
  interactions; equivEq: failed after 2.2G → 9.6M (with the propositionality abstracted).
- 7b (corrected; the earlier entry claiming it impossible was wrong): Pf is Gödel's provability
  predicate, Pf s = Σ t. Σ n. checkN n t s ≡ true: a term t and a step bound n with which the checker
  accepts t at s. checkN is check.ctt's checker with a fuel argument, structural on the fuel, so it is
  a checked total function; no normalization or consistency of the system is needed, the witness
  carries the bound (Proof(d, s) is decidable, Prov(s) = ∃d. Proof(d, s)). The work: check.ctt as a
  typed fuelled function over Code; quote : Code → Code; Theory with Sent = Code, neg s = code of
  s → Empty, prov s = code of Pf ⌜s⌝; HasDiagonal with imp = Π-code, Form = codes with a free
  variable, apF = substitution, negProv by computation on codes, and two lemmas about the checker:
  mp (application rule plus fuel monotonicity) and fix (G = D ⌜D⌝ converts to f ⌜G⌝ because the
  diagonal computes in the checker's conversion, so λx.x is accepted at G → f G and back). Halting:
  lawvere-one-row with A = Code, B = Bool, phi a b = h (app a ⌜b⌝) for a decider h given with its
  code; the row is the program λb. not (h (b ⌜b⌝)), its equation a lemma relating the fuelled
  evaluator on that program to h.
- 7c re-derived: needs merge correctness on sorted lists (commutativity, associativity, units, up to the
  free commutative monoid's paths) to give the path branches; feasible, larger than first estimated.
- Correction to item 1's stated driver: elimination with hypotheses lets the checker accept recursive
  definitions in general (the whole library); it does not make check.ctt itself checkable. check.ctt is
  untyped and uses general recursion, and a total checker typed inside the system would prove the
  system's consistency.
- pathToEquiv-ua: checked in 12M interactions once transportIsEquiv is η-expanded (its value becomes a
  closure over its code, which conversion compares unapplied). Before, comparing the two identical
  transported isEquiv proofs computed CCHM Glue composition on both sides and ran for hours.
- Neutral types computed on demand (`ntype` in check.ctt). Before, every neutral stored its type, so
  the type of `snd^k D` held `fst (snd^j D)` for j<k each with its own stored type; values are copied
  whole by the net, so a telescope of depth k cost ~8^k (measured, a Σ chain each component a path
  between the previous one and itself: p2..p6 = 54K, 366K, 2.6M, 19.6M, 159M steps; after: 36K, 122K,
  335K, 784K, 1.6M). Box 7's `diagonalGivesGoedelFix` ran for over an hour; its core `snd (dfix ..)`
  now checks in 4M. Only a variable stores its type; papp at an endpoint, unglue, argument comparison
  and elimination fields ask `ntype`. tests/check.ctt: 9.2M → 6.6M steps.
- `make library` = std + boxes, std + sort; both pass. std + boxes: 154 checks, 605M interactions,
  468 s (lemIso alone 276M). std + sort: 106 checks, 400M interactions, 307 s. Selected costs: uaβ 6.5M,
  isPropIsEquiv 2.5M, equivEq 3.7M, pathToEquiv-ua 7.8M, diagonalGivesGoedelFix 9.8M, sorted-unique 28M,
  msort-at 18.6M. Readings: msort of the balanced 8-element sum 43449 interactions (11573 erasures),
  of the chained one 47433 (14466 erasures), same sorted list.
- msort-at takes isProp→PathP as an argument (pp) like the propositionality (hp); msort = msort-at
  Fs-prop (isProp→PathP lzero). As a definition, isProp→PathP at a boundary is a transport in Fs
  computed back to the point; that check did not finish in over an hour. As an argument, its type
  gives the endpoints.
- State: every item is landed except 7b, designed above, not started. Nothing
  else is in scope. A fresh agent: run `make test` (fast) and `make library` (~13 min) to confirm.

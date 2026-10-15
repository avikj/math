# Reviewer guide

This is a from-scratch C11 implementation of §§1–38 of `HANDOFF.md` (*Scoped cubical
interaction machine and identity compiler*, 14 October 2026; §§39–48 are the next
increment). The guide
says how to check it without trusting the implementer's summary.

## 1. Run

    make test     # ASan/UBSan/LSan: checking (74), comparison (12), templates and admission (52),
                  # the review's regression cases (4 modes), acceptance/law (124 + 23 net),
                  # 24-schedule comparison, concurrent clients (storms, pools); then the acceptance,
                  # schedule, checking and template suites again with 4-thread pools
    make tsan     # every suite under ThreadSanitizer, including the review's concurrent case
                  # with halt_on_error (several minutes)

Expected: `74 passed, 0 failed`, `12 passed, 0 failed`, `52 passed, 0 failed`, every
`(expected …)` line of `review-regressions` matching its expectation, `124 passed, 0 failed`,
`schedule check passed`, `concurrent check passed`, and `make tsan` ending with the same lines
and no `WARNING`. Where LeakSanitizer cannot run (restricted `/proc`), `ASAN_OPTIONS=detect_leaks=0`
keeps ASan/UBSan; leak checking was run here.

## 2. Where each spec section lives

See the table in `README.md`. Entry points worth reading first:

| Spec | Function | File:line (approx.) |
| --- | --- | --- |
| §3 interval substitution, negation | `iv_substitute`, `iv_negate` | `src/interval.c` |
| §4 endpoints, substitution, entailment | `fc_endpoint`, `fc_substitute`, `fc_entails` | `src/face.c` |
| §5 ∀ vs π | `fc_forall`, `fc_project` | `src/face.c` |
| §6 make_view, reindex, compose | `make_view`, `reindex`, `compose` | `src/term.c` |
| §7 support | side data set in `make_view` / `ref_var` | `src/term.c` |
| §8 binder identity, lifting | `binder_term_var`, `lifted_map`, `resolve_*_binder` | `src/term.c` |
| §9 open, unfold | `open_ref`, `unfold_global` | `src/term.c` |
| §10 cache protocol | `eval_request`, `publish`, `evaluate` | `src/eval.c` |
| §12 dispatch | `evaluate`, `resume`, `eval_system_head`, `publish_branchwise`, `resume_branch` | `src/eval.c` |
| §13 comp with retained components | `evaluate` (T_COMP), `resume_comp_family` | `src/eval.c` |
| §14–17 clauses | `mk_fill`, `comp_clause_*`, `mk_line_equiv`, `mk_ua`, `mk_id_equiv` | `src/lib.c` |
| §19 rule table, materialization, duplication | `rule_op`, `materialize`, `rule_dup_*`, `net_eval_deliver` | `src/net.c` |
| §20 replacement discipline | `rep_commit`, `step` | `src/net.c` |
| §26 events | counters in `eval_request`, `deliver`, `publish`, `execute` | `src/eval.c` |
| §2 contexts | `context_make`, `occurrence_validate`, `whnf_in` | `src/term.c`, `src/eval.c` |
| §33 checking | `check_context`, `check_map`, `check_origin`, `infer_head`, `check_clause`, `validate_symbol` | `src/check.c` |
| §34 conversion | `conv_type_clause`, `conv_term_clause`, `spine`, `conv_memo_get` | `src/check.c` |
| §35 quiescence | `reserve_job`, `enqueue_reserved`, `finish_job`, `eval_run`, `whnf`; `push_active`, `net_finish_job`, `net_run_with_eval` | `src/eval.c`, `src/net.c` |
| §36 ownership | `cont_release`, `gather_free`, `rootbox_release`, `eval_free` | `src/eval.c` |
| §37 comparison | `canon_export`, `graph_match` (`unify`, `solve`) | `src/canon.c`, `src/match.c` |

## 3. What the tests establish, and what they do not

- `tests/test_main.c`: every row of the §23 table; the projection/quantifier laws checked
  exhaustively over all 48 canonical faces on two dimensions; β, projections, path
  endpoints before path demand, Glue on/off its face, systems (selection, retention,
  branchwise action, invalid occurrence), composition precedences, neutral composition,
  type-family systems with ∀ guards, Π/Σ/PathP/Glue/U clauses firing with the expected
  heads, transport along `ua`, contexts. These are acceptance checks of the transcription;
  they are not proofs of the cubical clauses, which the spec also does not claim.
- `tests/test_schedule.c`: one initial configuration, 24 schedules (FIFO/LIFO/random job
  selection × LIFO/FIFO/random active-pair selection, several seeds), fresh machine each
  time. Required equal: W = (REQUEST, EVAL_STEP, PUB, DELIVER), net rule counts, and the
  exact canonical dump of all root observations and all cache keys with per-key counts.
  Ready-hit/running-hit diagnostics vary across schedules (so request/publication order is
  actually exercised) while W does not.
- `tests/test_concurrent.c`: barrier-released client storms on one fresh key (no spurious
  `W_STUCK`, one task, one result pointer), storms on a cyclic key (all stuck, nothing
  published, clean teardown), and multi-client runs whose W and canonical graph equal the
  sequential run of the same client program.
- `src/canon.c` is exact: no hash participates in the comparison (partition refinement
  with exact signatures, DFS numbering, aliasing preserved). Input names are anchored by
  declaration index, generated names by provenance, globals by name.

- `tests/test_check.c`: the §38 checking list (β/η acceptance, rejections, dependent maps,
  comp agreement, path endpoints, Glue map agreement, system coverage/overlaps, UNRESOLVED
  for cycles and budget), that every composition clause's output checks at its type, opaque
  constants, symbol validation on first use, scope under the false face.
- `tests/test_match.c`: §37/§38 comparison list, including graphs refinement cannot separate.

## 4. Independent audits already performed

Two audits by an agent that had not seen the code being written, against the spec text:
the first (§3–§17 algorithms, §19–§20 wiring) found no correctness bugs and three
letter-of-the-spec deviations, all fixed (branchwise action under `χ ∧ φ_k`, guard
substitution in `APPLY_PARTIAL_DIM_BINDER`, required-face propagation). The second
(concurrency, counting, canonical comparison, contexts, reclamation) found one real
concurrency bug — the EVALUATE job was enqueued after the entry lock was released, so a
concurrent client could observe a running key with no runnable evaluator and report a
spurious `W_STUCK`, after which a late delivery wrote into a destroyed root box — and a
broken `make tsan` chain that had hidden it. Both are fixed: the launch is enqueued inside
the entry's critical section, root boxes are reference-counted between client and
continuation, and `make tsan` runs all three suites. The auditor's storm scenario is now a
permanent test.

A third audit, of the §32–§38 work, found no deviation in the scheduler protocol, the
required-face annotation, or the typing rules' acceptance, and four real bugs, all fixed
and now covered by tests: the matcher's backtracking did not revisit inner choices
(incomplete, never unsound); observing an opaque constant aborted instead of yielding a
neutral; a Π-conversion fresh variable was keyed without its expected type head; a stuck
branchwise join leaked at teardown. Its deviations are also closed: symbols are validated
on first use, λ-domain annotations are checked as types in check mode, scope is checked
under the false face, the conversion cache key is the projected face over the
declarations, and the required-face annotation is part of the exported graph.

## 5. The review of 8bfd227: corrections made

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| R1 provisional recursive validation | Claims with provisional premises; commit only when the symbol's body is accepted; rejected premises withdraw dependents; mutual recursion commits as a component; top-level requests settle before returning | `check.c` `claim_*`, `resolve_locked`, `top_settled` | `review-regressions recursive`; `test_templates.c` (mutual recursion valid / invalid, 8-client storms from both ends) |
| R2 memo key visible before value storage | `wordmap_get` reads the value chunk with an acquire load and reports a miss when it does not exist yet (`chunked_peek`) | `intern.c` | `review-regressions wordmap-window` |
| R3 timing-dependent UNRESOLVED | One producer per request, all other clients wait and receive its outcome; wait cycles detected on the wait-for graph; a symbol on the cycle yields by assumption; only a cycle without a symbol is a cyclic request | `check.c` `claim_acquire`, `may_block_locked` | `review-regressions concurrent` (8 identical conversions: all EQUAL), also under TSan |
| R4 per-invocation construction | Fixed templates: one origin per definition and shape, formals for term/interval arguments, invocation = `reindex(body, σ)`; pairs annotated with their Σ type | `lib.c`, `term.c` `mk_pair_at`, `check.c` PAIR synthesis | `test_templates.c`: specialize/instantiate commute and share one producer for refl, Path, papp (term and interval formals), reversal, concatenation, fib, ua, extend_contr (partial formal), fill (cap and interval formals), the Π/Σ/Path/U/Glue clauses (cap; tube where in place; renamed face); clause outputs still check |
| R5 false-face map scope | Term images are scope-checked independently of the clause loop; only typing is vacuous on false | `check.c` `check_map` | `review-regressions` default mode |
| R6 pointer-equality context compatibility | Declared type compatible with the recorded declaration by conversion under each clause; UNRESOLVED propagated | `check.c` `check_context` | `review-regressions` default mode |

Two further corrections that the fix pass required: `check_map` checks a target
declaration's image under `ψ ∧ φ_x[σ]` (a declaration partial on φ_x is only used under
φ_x) instead of demanding `ψ ⊢ φ_x[σ]`, and `make_view` lets an image that is available on
all of a partial formal's guard add no requirement to the view; both are what templates
with partial tube formals need and both are the §33 reading of "the target's required face
obligations".

Q1 and Q2 are answered as the author stated: control outcomes stay in DELIVER
(`NO_OBSERVATION` for a false face, `INVALID` for a failed occurrence guard; neither adds
REQUEST or PUB), and recursive occurrences use their declared signatures while provisional
successes stay uncommitted until the dependency checks succeed.

### Open item: type parameters of templates

The review prescribed `refl` as `PLAM(j, VAR(value))` over `type : U_ℓ`, `value : type`.
Term formals are implemented exactly so; a *type* formal needs the universe level ℓ of the
argument at invocation, because levels are exact (no cumulativity) and the instantiated view
is checked by `check_map` against `U_ℓ`. The evaluator invokes the composition clauses with
the exposed family head and has no ℓ: `COMP` carries no level annotation, and the level of a
Π/Σ/Path/Glue head is not syntactic. So type and family arguments are the template's shape
(one fixed origin per type instance, canonicalized over dimension formals), and the law
`reindex(T(a), τ) = T(a[τ])` holds for τ on term and interval formals and for
order-preserving renamings of the shape's dimensions, not for τ that changes a type
argument. Full parametricity in types needs one of: (a) a universe-level annotation on
`COMP` (and on the derived definitions' API), (b) the checker recording the inferred family
level per `COMP` origin for the evaluator to read, which makes the clause output depend on
whether admission ran, or (c) accepting the per-type-instance templates. The author should
choose; (c) is implemented.

### Open item: §39–48

The identity compiler (§39–48) is the next, additive increment; it is not in this commit.

## 6. Representation choices a reviewer should know

Listed in `README.md` under "Representation decisions". The two most likely to raise an
eyebrow: a neutral result retains the original eliminator reference (as §12 says) rather
than a rebuilt head around the evaluated scrutinee (the review accepted this); and the
composition clauses are fixed templates whose type/family/face arguments are shape data
rather than formals, for the reason in §5 above.

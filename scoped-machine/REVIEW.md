# Reviewer guide

This is a from-scratch C11 implementation of `HANDOFF.md` (*Scoped cubical interaction
machine and identity compiler*, §§1–59, 14 October 2026). The guide
says how to check it without trusting the implementer's summary.

## 1. Run

    make test     # ASan/UBSan/LSan: checking (76), comparison (12), templates and admission (61),
                  # identity compiler (85), the review's regression cases (4 modes), acceptance/law
                  # (124 + 35 net), 24-schedule comparison, concurrent clients (storms, pools); then
                  # the acceptance, schedule, checking, template and compiler suites with 4-thread
                  # pools; then the reviews' reproductions (review-followup in 4 modes,
                  # review-claim-wait, review-checker-lifecycle, review-ae756a1 in 11 modes,
                  # review-0f787a3 in 6 modes, review-9eadaf2 in 6 modes, review-end-to-end
                  # in 10 modes plus the four-worker pipeline, review-nested-scope),
                  # each exiting nonzero on a miss
    make tsan     # every suite under ThreadSanitizer, including the review's concurrent case and
                  # the three reproductions with halt_on_error (several minutes)

Expected: `85 passed, 0 failed`, `12 passed, 0 failed`, `80 passed, 0 failed`, `85 passed, 0 failed`, every
`(expected …)` line of `review-regressions` matching its expectation, `124 passed, 0 failed`,
`35 net checks passed`, `schedule check passed`, `concurrent check passed`, the reproductions
printing their observations without a `FAIL:` line (`<mode>: 0 expectation failures` for each
review_ae756a1, review_0f787a3 and review_9eadaf2 mode), and `make tsan` ending with the same lines and no `WARNING`. Where LeakSanitizer cannot run (restricted `/proc`), `ASAN_OPTIONS=detect_leaks=0`
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
| §14–17, §52–54 clauses | `mk_fill`, `comp_clause`, `mk_line_equiv`, `mk_ua`, `mk_id_equiv`, `mk_down` (thin wrappers over `template_call`) | `src/lib.c` |
| §19 rule table, materialization, duplication | `rule_op`, `materialize`, `rule_dup_*`, `net_eval_deliver` | `src/net.c` |
| §20 replacement discipline | `rep_commit`, `step` | `src/net.c` |
| §26 events | counters in `eval_request`, `deliver`, `publish`, `execute` | `src/eval.c` |
| §2 contexts | `context_make`, `occurrence_validate`, `whnf_in` | `src/term.c`, `src/eval.c` |
| §33 checking | `check_context`, `check_map`, `check_origin`, `infer_head`, `check_clause`, `validate_symbol` | `src/check.c` |
| §34 conversion | `conv_type_clause`, `conv_term_clause`, `spine`, `conv_claim` | `src/check.c` |
| §34–35 claims / admission transaction | `claim_acquire`, `claim_release`, `resolve_locked`, `may_block_locked`, `top_settled` | `src/check.c` |
| §49–51 scopes, templates, TVIEW | `capture_scope`, `apply_scope`, `reindex_scope`, `forall_scope`, `trav_*` (`src/scope.c`); `register_library` (the DSL), `interp`, `make_view_env`, `tview_open`, `tview_reindex`, `tnode_signature` (`src/template.c`); `ref_intern_tview`, `open_ref`/`reindex` dispatch (`src/term.c`) | — |
| §55 scope/template agents | `rule_op` OP_CAPTURE_* … OP_TYPED_PARTIAL_GUARD; `test_net` | `src/net.c` |
| §57, §59.4 admission gate, sessions | `check_admission`, `observe_checked`, `tid_locked`, `check_new_attempt` | `src/check.c` |
| §59.1 levels | `origin_levels`, `mk_*_lv`, `term_levels_push` (`src/term.c`); `level_ok1/2`, `check_is_type`, `infer_tview` (`src/check.c`) | — |
| §59.3 fixed call origin | `build_generic_call`, `transform_publish`, `mk_transform_call` | `src/compiler.c` |
| §39 diagrams, realization, canonical substitution | `diagram_declare`, `diagram_validate`, `diagram_build` | `src/compiler.c` |
| §41 singleton maps | `down`, `emit_collapse`, `emit_expand`, `diagram_collapse`, `diagram_expand` | `src/compiler.c` |
| §42 identity compilation | `graph_pair`, `derive_identity`, `compile_identity`, `certificate_verify` | `src/compiler.c` |
| §43 invocation | `mk_tcall` (`src/term.c`), `mk_transform_call`, `compiler_decode_call`; `evaluate` T_TCALL and `pop_locked` (`src/eval.c`); `rule_op` OP_APPLY_TRANSFORM and `apply_rule` A_CONTINUE_REFERENCE (`src/net.c`); `infer_head` T_TCALL (`src/check.c`) | — |
| §44 equivalence, residual, cut, contractible fibre | `derive_equivalence`, `derive_residual`, `derive_cut`, `derive_contractible` | `src/compiler.c` |
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

### Type parameters of templates: resolved by §59.1

The author chose explicit universe annotations. Type and family arguments are now ordinary
template parameters (`src/template.c`, §51), every type position carries its level, and the
sharing law `reindex(T(a), τ) = T(a[τ])` is an identity of references for every parameter;
the per-type-instance templates are gone. `review-followup` (default mode) is the author's
reproduction: `reindex(refl(A, x), [A ↦ B, x ↦ y]) == refl(B, y)` and one producer.

### §39–48

Implemented in `src/compiler.c` (README, "Identity compiler"); the eleven §47 cases are in
`tests/test_compiler.c` and case 10 in `tests/test_schedule.c`. The two readings offered with
8329456 were confirmed by §59.2/§59.3 (map-as-fields and the common `y`), with the
correction that invocations are views of one fixed call origin per orientation.

## 5b. The review of 8329456: corrections made (§59)

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| §59.1 explicit levels | Levels word on every origin; annotated constructors; level-bearing library API; templates always annotate; checker validates every annotation and every template parameter image against its instantiated declared type | `term.*`, `lib.*`, `template.*`, `check.c` | `test_templates.c` (type-changing specialization is one reference; distinct levels are distinct references); `test_compiler.c` (wrong annotation rejected; stored record levels) |
| §59.2 guarded substitution, annotated pairs | `check_map` checks an image under `ψ ∧ φ_x[σ]`; pairs carry and validate their Σ annotation (now with its level) | `check.c`, `term.c` | existing R4/R5 cases |
| §59.3 one fixed call origin | `generic_call[id,dir]` built at publication over the parameters and the argument slot; `mk_transform_call = reindex(generic, σ|Γ + slot ↦ a)`; visibility only after both orientations exist | `compiler.c` | `review-followup call` (identical reference, one application pair); `test_compiler.c` 8b |
| Checker wait through a freed claim pointer | Every wait re-reads `&K.recs.data[idx]` after resuming; the dependency vector may grow during a wait | `check.c` `claim_acquire` | `review-claim-wait` (200 claims interned while a reader waits), ASan and TSan |
| Thread identities reused across checker restart | Session generation: `tl_gen != session_gen` re-registers the thread; attempts number UNRESOLVED outcomes so a later attempt retries them | `check.c` `tid_locked`, `check_new_attempt` | `review-checker-lifecycle` (8/8 EQUAL after `check_free(); check_init()`) |
| Residual validation accepted a term for a type | `check_is_type`: the inferred type is observed and must be a universe; used for every type position of diagrams, declarations and the λ domain | `check.c`, `compiler.c` | `review-followup formation`; `test_compiler.c` bad node type |
| Admission gate not connected | `check_admission` keyed by the global environment version; entered by `observe_checked` and by every compiler publication | `check.c`, `compiler.c` | `review-followup admission`; `test_check.c` (a well-typed term is refused once a rejected body is registered) |

§§49–56 are implemented alongside (README, "Contextual templates and explicit levels"):
scopes with bound atoms, template programs and TVIEW references, the library and all five
composition clauses as fixed programs, `Down` over a captured scope, the §55 descriptors and
operations (`test_net`: each rule agrees with the host operation and allocates no origin),
and the exported graph labels for TVIEWs, scopes and bound atoms (`canon.c`).

## 5c. The review of ae756a1: corrections made

Both implementation notes of ae756a1 were deviations, as the review said, and are withdrawn:
declared parameter types are never skipped (R2) and no untyped scope or unknown level reaches
the fixed library (R4). The reviewer's `tests/review_ae756a1.c` is in `make test` and
`make tsan` with all nine modes, the `environment` mode adapted as the review directed once
registration fails closed, plus two concurrent modes the review asked for.

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| R1 environment freeze, attempt caching | `check_admission` freezes the environment first; `define_global` returns 0 and `set_global_body` false while frozen; `check_open_environment` opens a candidate environment with a fresh checker session (claims, admission state, diagnostics) and a reset evaluator (every observation retired, workers and policies kept); the admission verdict is keyed by environment version and reused only when settled or within the attempt that produced it; the budget is fixed per top-level request on entry | `term.c` (`env_freeze/unfreeze`), `check.c` (`check_admission`, `check_open_environment`, `top_enter`), `eval.c` (`eval_reset`) | `review-ae756a1 environment`, `retry`; `test_check.c` (fail-closed registration, open environment) |
| R2 template typed closure | A node's environment is closed under the declared types / levels / signatures of its retained parameters (`decl_closure`), the root node also under the declared result type (`rtype`); every reference parameter of the library has a declared type (`EquivMap`/`EquivContr` now take their levels and types; the clause caps, `ExtendContr`'s `k` and `Down`'s parameters are declared); `tnode_signature` never substitutes a missing type; the instance's inferred type must convert to the declared result type | `template.c`, `check.c` `tview_boundary`, `infer_tview` | `review-ae756a1 signature` (`Refl(0,A,x) ≠ Refl(0,B,x) ≠ Refl(1,A,x)`, both rejected); `test_templates.c` sharing laws still hold |
| R3 scope signatures | Every scope parameter has a contextual signature (`psig`: expected telescope, result type, level, guard, κ-relative); `check_scope_arg` opens signature and argument at one common fresh telescope, compares local declarations by conversion, requires expected guard ⊢ supplied guard under the source clause, forms the supplied result type at its stated level, converts it to the expected one, and checks the body under the supplied guard; face/interval scopes are compared as total syntax | `template.c` (`SIG_*`), `check.c` `check_scope_arg` | `review-ae756a1 scope` (false result annotation; false-only family at a total formal) |
| R4 checking forms, missing levels | `check_clause` validates a λ's stored domain level and an annotated pair's stored Σ (forms at its level, converts to the expected type, governs the components); a TVIEW in a checking form enters the template boundary first; `LEVEL_NONE` at a required type position is INVALID in both modes; `comp_clause` instantiates no clause for an unannotated family (the demand is reported invalid); internal constructions carry levels (`mk_pi_lv`/`mk_sigma_lv` for synthesized types, `mk_papp_lv`/`mk_unglue_lv` in η-conversion and in the evaluator's eliminator rebuild) | `check.c`, `lib.c`, `eval.c` | `review-ae756a1 annotations`, `missing-level` |
| R5 partial declarations | Declaration formation and compatibility run under the projected prefix assumption conjoined with the declaration's guard | `check.c` `check_context` | `review-ae756a1 partial-context` |
| R6 duplicate publication | Compiled records are interned by the structural key (environment version, schema, every certificate input, the derived record data; no registry numbers); the key is claimed under the registry lock, both call origins are built privately, one record is published and waiting clients receive it; diagrams are interned by their declaration likewise | `compiler.c` `record_key`, `transform_publish`, `diagram_new` | `review-ae756a1 publication`, `publication-concurrent` (eight clients, one record) |
| R7 raw-origin levels in comparison | The exported raw-origin label carries the packed level annotation | `canon.c` | `review-ae756a1 canon` |
| diagnostics buffer | Runtime diagnostics are immutable strings owned by the checker session | `check.c` `diag_intern` | `review-ae756a1 diagnostics-concurrent` |

One further defect surfaced by the concurrent publication case and fixed: without a worker
pool, a client thread whose demand was being executed by another client thread drained an
empty queue and reported `W_STUCK`; `whnf` now waits for its root or for quiescence in that
configuration too (`eval.c`).

## 5d. The review of 0f787a3: corrections made

Reading 1 (observation retirement) is implemented at a closed session boundary as the review
directs: `check_open_environment` requires no top-level checker client in progress and no
running admission attempt, `eval_reset` requires no outstanding evaluator work, and the API
comment states that previously returned `EvalResult` and diagnostic pointers are dead. Reading
2 (binder locals) is withdrawn: descendants retain and check the declarations of the locals
they use freely (F3).

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| F1 scope validity vs. compatibility | `check_scope_own` validates the supplied scope in its own context: each term local's declaration forms in the supplied prefix under the projected clause ∧ its own required face, at a required (non-`LEVEL_NONE`) stated level; under C ∧ supplied guard the result type forms at its required stated level and the body has that type. `check_scope_arg` then compares against the signature on the common telescope (declarations by conversion, expected guard ⊢ supplied guard, result types under the expected guard) without substituting expected declarations for supplied ones | `check.c` | `review-0f787a3 scope-level`, `scope-locals`; existing partial-tube and Glue positives unchanged |
| F2 call-root programs | `finish` integrates a call root into caller-owned nodes once at registration (`inline_root`: callee parameters ↦ argument recipes, κ stays the caller's, callee locals ↦ fresh caller locals with their declarations, callee nodes ↦ caller nodes with substituted field/payload/level/required recipes); the caller's parameter signatures and result type are the retained boundary; partial parameters keep their guard (`ptype_on`: ExtendContr's `v` on κ∧θ) and are checked on it | `template.c`, `check.c` `tview_boundary` | `review-0f787a3 call-boundary`; `test_templates.c` (ExtendContr/Down roots are their own nodes, partial `v` valid, `v : B` rejected, Down's scope annotation/guard rejected and distinct) |
| F3 escaped constructor locals | Term-local declarations (type, level, required face) are recorded for constructor binders and scope locals; free sets are recomputed at `finish` over the complete table to a fixpoint, closing each node under the declarations of the parameters and locals it retains; a local is removed only at its binder; `tnode_signature` reports retained locals with their instantiated declarations and the boundary checks their images on the declared guard | `template.c` (`NODE_req`, `decl_closure`, `finish`), `check.c` | `review-0f787a3 binder-boundary`; `test_templates.c` (valid substitute checks; two-step reindexing of the child's boundary composes) |
| F4 fresh machine frozen | `machine_init` opens the environment (`env_control_init`); the version counter is not reused | `term.c`, `machine.c` | `review-0f787a3 machine-restart` |
| regressions / docs | `review_ae756a1 missing-level` keeps the original unannotated negative case and the annotated positive case; README's composition paragraph and the `level_ok1` comment corrected | — | — |

## 5e. The review of 9eadaf2: corrections made

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| R1 finite scope before opening | `scope_validate` runs before any opening, independent of faces: through the traversal engine with scope enter/leave hooks it checks that every bound occurrence (in the records and in scopes nested anywhere inside them, through views and template environments) names an existing enclosing telescope, an in-range slot of the right sort; each local's declaration is traversed over its prefix telescope; required metadata is present; the scope's free identities must be declared in the occurrence context. `check_scope_own` then performs the guarded formation and body checks | `scope.c`, `check.c` | `review-9eadaf2 scope-depth`, `scope-sort`, `nested-control`; `test_templates.c` (depth, sort, slot range, prefix, nested outer use, captured library scopes) |
| R2 κ across machine lifetimes | The thread's κ is qualified by the machine generation (`machine_generation`, incremented by `machine_init`, never reused); a thread entering a later machine observes the default true face; overrides and `comp_clause`'s save/restore stay within their machine | `machine.c`, `template.c` | `review-9eadaf2 kappa-restart`, `kappa-alias`, `kappa-thread` (a retained client thread) |

The session boundary (`check_open_environment`) is a host precondition: the caller stops
admitting new clients and waits for whole public calls (checker, compiler, observation) to
return and for evaluator work to drain. The in-progress counter, the admission-attempt flag
and `eval_reset`'s outstanding-work check are partial assertions of that precondition, not
its enforcement: `top_leave` releases the counter before `top_settled`, and compound compiler
and observation calls have intervals outside individual checker entries. No concurrent reset
is supported.

## 5f. The end-to-end review of e9c7dcb: corrections made

The reviewer's `tests/review_end_to_end.c` (nine negative modes, the checked associativity
pipeline in both orientations with repeated-demand sharing, the four-worker adjacent-redex
stress) is in `make test` and `make tsan` unchanged (`universe`/`packed-level` under
ASan, `diagram-race` under TSan, as the runner distributes them).

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| R1 old claims survive a candidate mutation | Every claim key and every evaluator memo key carries the environment version, so a successful registration makes all earlier environment-dependent verdicts, conversions and observations unreachable; a previously checked opaque declaration is re-validated with its body at admission | `check.c` `claim_index_locked`, `eval.c` `entry_intern`/`eval_entry_lookup` | `review-end-to-end candidate`; `test_check.c` positive companion (opaque → body `a`: conversion recomputed to EQUAL, observation recomputed, admission valid) |
| R2 checking forms bypass the required face | `check_clause` and `infer_clause` require the clause to entail every non-variable occurrence's required face before any form-specific path (vacuous under false, which has no clauses) | `check.c` | `review-end-to-end guard` (total check and total admission INVALID; under `i=0` VALID) |
| R3 structural validation before every use | `ref_validate` (the structural traversal at the top level, through template environments and nested scopes with their actual stack) runs in `scope_ok` and on every map image; `tview_boundary` validates every retained scope and reference image before any signature recipe can apply a scope; positive outcomes memoized per record | `scope.c`, `check.c` | `review-end-to-end false-scope`, `coe-scope` |
| R4 partial dimension binder on a TVIEW | The guard is read through the opened head; `LIFT_*` and `UNFOLD_GLOBAL` return a status for a template view instead of a raw-origin access | `net.c` | `review-end-to-end net-tview` |
| R5 diagram verdict after a session reset | A diagram's cached verdict is qualified by checker session and environment version; a later call revalidates and returns currently owned text | `compiler.c` | `review-end-to-end diagram-session` (ASan clean) |
| R6 registry lookup race | `DG` takes the registry lock for the id check and the stable pointer; no caller holds the lock across it | `compiler.c` | `review-end-to-end diagram-race` (TSan clean) |
| R7 universe wrap | `levels_pack` and `mk_universe` require the representable range (host failure); the universe rule uses the checked successor | `term.c`, `check.c` | `review-end-to-end universe`, `packed-level` (child aborts) |

## 5g. The review of fec0f69: the remaining R3 correction

| Finding | Correction | Where | Regression |
| --- | --- | --- | --- |
| R3 raw-origin children escaped structural validation | The validator is a separate finite walk, distinct from the substitution traversal (which, by the representation contract, visits only a raw view's boundary images): it visits boundary images, the stored fields of raw origins (binders are ordinary identities, so the depth is unchanged — inactive branches and metadata included), the environments of template views, and every scope reachable from them with the actual enclosing telescope stack; memoized per (record, telescope stack), so validity inside a telescope is never reused at the top level; GLOBAL bodies are not unfolded | `scope.c` `val_ref`, `val_scope` | `review-nested-scope` (fst-wrapped malformed tube under false, system with the malformed tube in its false branch at true, zero-arity scope holding the wrapper; positive: a valid tube below a raw annotated pair and fst) |

## 5h. The §73 increment: identity-execution accounting and cost refinement

Baseline `24b2bfb`. New: `src/work.{h,c}`, `tests/test_work.c` (198 checks, run
sequentially and with `CUBICAL_WORKERS=4` under ASan/UBSan/LSan and under TSan),
trace fields in the evaluator and net, HANDOFF v8 (`HANDOFF.md`) and the §73
direction (`DIRECTION-73.md`). All previous gates unchanged and passing.

Section → function → acceptance case (§73.5):

| Spec | Functions | Cases |
| --- | --- | --- |
| §60.1 identities | `atom_producer/request/deliver/pub/eval/apply`, evaluator `deps/steps/env`, net trace | 1, 10 |
| §60.2 closure, cuts, laws | `demand_closure`, `work_ready_snapshot` | 1, 2, 10 |
| §60.3 extraction | `work_extract`, `workset_counts` (= coarse events) | 1, 10 |
| §61.1–61.3 algebra, dominance | `family_make/plus/times`, `formula_antichain`, `family_dominates`, `family_residual` | 4, 7 |
| §62.1–62.3 specialization | `set_specialize`, `formula_specialize`, `plan_specialize` (reindex → validate → intern → dedupe → then cuts/costs) | 3, 7 |
| §63 differences | `costdiff_make/epsilon/masked/current` | 3, 10 |
| §64.3 geodesic certificates | `geo_new/edge/value/policy/rank/check` | 6 |
| §65.1, §71 frames and ledger | `op_*`, `work_ledger`, `work_record_execution` | 8, 9 |
| §66–67 records, compatibility | `boundary_make`, `plan_make`, `connector_make`, `expr_*`, `problem_prepare` | 4, 5, 6 |
| §68.1 formulas | `formula_and/or/atom/restrict/subst/support/must` | 4, 6, 8 |
| §68.3 reconstruction | `realize`, `realization_reference` | 3, 4, 5, 10 |
| §68.4 invalidation | `problem_current`, certificate problem identity | 3, 6 |
| §69.1/69.4 verification | `proof_*`, `certificate_make/check` | 6, 7 |
| §70.1–70.3 direct fragment | `formula_reduce`, `problem_reduce`, EQUAL/shared-or | 4, 7 |
| §70.4 schemas | `schema_make`, `atom_map_make`, `schema_instantiate` | 7 |
| §73.3 integration | `dgraph_from_trace_since`, case 10 (associativity, both orientations, overlapping demands, APPLY atoms, commit through `observe_checked`) | 10 |

Boundaries a reviewer should know: (i) the atom order anchored in a problem is the
first-occurrence order over the plans' and connectors' *ordered* work lists
(`plan_make` takes a list, keeps a set beside it); (ii) kernel helpers reached from
the accounting layer (`reindex`, `fc_reindex`, `ref_validate`, `check`,
`check_map`) are charged as `kernel_calls`, not refined into frames — the fine
ledger covers the retained §71 operations; (iii) `OP_RESOURCE_LIMIT` is reserved
for checked-arithmetic overflow and is not resumable; budget exhaustion is
`OP_RUNNING`; (iv) hash-consed proof records cannot form a cycle, so the
back-reference rejection in `step_proof` guards the in-progress mark rather than
a constructible input; (v) the EQUAL constructor exists only for the §70.3
displayed equality and the checker re-derives the image structurally.

## 5i. The §§74–82 increment: uniform reuse

Baseline `3a0d7c4`. Handoff v9 is `HANDOFF.md` (§§74–82 normative), the
amendment alone is `AMENDMENT-74-82.md`, the worker brief `WORKER-v9.txt`; the
assessment's diagnostics and captured results are in `tests/baseline-3a0d7c4/`
and its three target acceptance sources are `tests/accept_*.c` (gated,
sequential and under `CUBICAL_WORKERS=4`, ASan/UBSan/LSan and TSan).
`tests/run_reuse_acceptance.py` is the supplied runner (run it with
`tests/` on the include path, as the Makefile does).

Section → function → test:

| Spec | Functions | Tests |
| --- | --- | --- |
| §74.2 counters | `reuse_bump/reuse_count` (`src/reuse.*`), bump sites in `eval.c`, `net.c`, `check.c`, `work.c`, `shape.c` | every A-case; `accept_*` |
| §75.1–75.3 persistent jobs, keys, handles | `Op` (job), `job_key`, `job_for`, `push` (join/create/deliver), `service`, `op_step`, `op_release`, `reduction_record`, proof-check job | `work` case 8 (A14 handles), `accept_shared_work_handle`, `accept … work`, A12, A13, A21 |
| §76 shape | `shape_under/shape_of`, `entry_intern`, `chain_pick_locked`, `ShapeSide` | A1, A2, A3, `origin`, `alpha` |
| §77.1 action identity, provenance | `record_key`, `transform_publish`, `transform_sources` | A10, A11, `identity-name` |
| §77.2 projected judgments | `project_context`, `conv_claim` | A15, `checker`, e2e |
| §78.1–78.2 receipts/residuals | `publish_with`, `rc_*`, `forward_rc`, `rebuild_elim`, `resume`, `resume_comp_family`, `eval_system_head`, `eval_forward_result` | A4, A5, A7, A16, A18 |
| §78.3–78.5 adapters, edges | `record_edge`/`instantiation_edges` (term.c), `find_adapter`, `adapter_candidate`, `evaluate` (adapter branch), alias publication | A4–A7, A16, A17, A18, A20, `face`, `specialize` |
| §79 revisions, validity, session | `global_revision`, `gdeps_*`, `eval_entry_deps_valid`, claim `gdeps`, `check_open_environment` | A8, A9, `environment` |
| §80 runtime action | `identity_pair`, `identity_action` | A19, e2e |
| §81 accounting, bounded helpers | `FR_PRODUCER_LOOKUP/ALIAS_DELIVERY/SHAPE_NODE/DEPENDENCY_CHECK/RECEIPT`, `atom_producer_at` (shape, face, snapshot), `dgraph_mark_alias`, SORT frames, framed relocation, indices | A20, A21, `work` cases 1, 9, 10 |

Semantic producer counts before/after for A1–A20 are read in `tests/test_reuse.c`
through the counters: A1–A3 second demands 0 bodies/0 betas (before: 1 body + 1
beta each, 2 bodies for A2); A4 0 betas and 1 receipt instance (before: 1 beta);
A5 exactly 1 new beta (the exposed redex) and no stale neutral; A6 0 betas
(before 1); A7 1 endpoint rule / 1 glue rule, no leak; A8 0 bodies after an
unrelated declaration (before 3 producers); A9 1 unfold on the new revision, the
old answer invalid; A10 0 APPLY and 0 bodies (before 1 + 1); A11 two actions;
A12 0 reduce bodies / 0 proof bodies on repeat (before a full rerun); A13 one
new reduction under the changed model; A14 six concurrent alpha-variant demands:
1 run, 6 requests, 6 deliveries, 1 publication; A15 0 conversion bodies under
weakening (before 2 claims); A16 0 betas, 1 projection on the substituted
instance; A17 0 betas on either adaptation, 1 path beta; A18 no self-wait, the
genuine cycle stuck; A19 0 transforms published, 0 APPLY; A20 one shared
producer counted once with two consumer occurrences and the record equal to
the run's events.

Fine-cost obligation (§81.2, §82.3): **not complete**. The bounded-helper audit
in README lists two unrefined classes — kernel calls reached from
specialization and preparation frames, and the constructor-level synchronous
APIs — so the §65 constant-factor refinement is claimed only for the formula /
set / cost / certificate / realization / demand / family operations. The old
work suite's 217 checks are regression evidence, not that proof.

Adapted assertions (each names its clause and keeps the mathematical
assertion): `tests/test_work.c` case 8 (§75.2: an already completed key
completes at once, so each suspension test uses a fresh instance and a third
handle checks persistence); `demo_speculation` is unchanged — the restricted
decision is still the same result object because the branch's residual key is
alias-published (§76.3/§78).

## 5j. The b612a07 review (R1, R2) and the §§83–84/88–89 increment

Baseline `b612a07`. Masters: `HANDOFF.md` is the v13 master (§§92–96
inserted before the appendices); the amendments alone are `AMENDMENT-83-87.md`,
`AMENDMENT-88-91.md`, `AMENDMENT-92-95.md`, `AMENDMENT-96.md`; the briefs
`WORKER-v10.txt` … `WORKER-v13.txt`; the author's §96 evidence is in
`tests/review-v13/`. The author's probes and runners are
gated unchanged: `tests/review_alias_scope.c`, `review_alias_faces.c`,
`review_work_budget.c` (white-box over `work.c`), `review_workers.c` +
`run_review.py` (17 runs, ASan+LSan and TSan), `run_boundaries.py` (6 runs),
`run_core_witnesses.py` (3 witnesses), `test_proof_boundary.c` (11 cases),
`review_certificate_boundary.c`, `review_frame_cost.c`, the three §83
witnesses, and the v9 `run_reuse_acceptance.py` (9 jobs).

Correction → function → test:

| Correction | Functions | Tests |
| --- | --- | --- |
| R1 §93 alias publication | `publish_with` (eval.c): `result_new(cls, residual)` / `result_system(residual, …)` for the alias descriptor; the alias is published before the source's READY store | `review_alias_scope` 0/4, `review_alias_faces` 0/4, `test_reuse` (101), `test_check` (85), `demo_speculation` |
| R2 §94.2(1) NORMALIZE / payload copies | `step_normalize` ph 0 (chunked flags) ph 3 (chunked compaction), `words_take`, `fr_intern_own`, `fr_sort_own`, `push_intern_own` and their callers (support/Must merge, set ops, SORT dedupe, LIST, workset, atom-set specialization, MAPSET) | `review_work_budget` normalize 64/4096: 32 flags per unit; `test_work` (217) |
| R2 §94.2(2) delivery | `deliver_to`, `service` (pop-and-deliver), `waiters` registration in `step_join` | `review_work_budget` fanout 256: ≤ 1 delivery per unit; `accept_shared_work_handle`; `test_work` case 8 |
| R2 §94.2(3) scheduling, cycle checks | `Op.path`, `tip_of`, `service`, `step_join` ph 2 (`CYCLE_CHECK` one hop per unit), `FR_SCHEDULE_STEP` | `test_work` cases 1, 8, 9; `accept_*`; A12–A14, A18 |
| R2 §94.2(4) table operations | `OF_JOIN` (`push` → framed key `INTERN`), `KTab.moving/probe`, `ktab_grow_chunk` (probe-bounded units), `step_intern` ph 1/4 and `step_lookup` ph 1/3 (no synchronous `ktab_settle`) | `test_work` case 9 (ledger), `review_work_budget` |
| R2 §94.2(5) allocation/release | `fail` retains the stack; `service` releases one frame per unit; ownership transfer removes the copies; buffer growth remains amortized (disclosed) | `test_work`; LSan clean |
| R2 §94.2(6) kernel administration | `kernel_mark/kernel_charge` charging `FR_SHAPE_NODE/DEPENDENCY_CHECK/RECEIPT` from `reuse_count` around kernel calls in `ATOMSPEC` and `atom_producer_ref`; `FC_AUDIT_STEPS` | `test_runtime` case 7, `test_proof_use` ledger check |

Section → function → test for the increment:

| Spec | Functions | Tests |
| --- | --- | --- |
| §83.1 Maps, presentations | `rt_maps_type/id/compose/inverse`, `rt_pres_type/const`, projections | `test_runtime` block 1; `review_runtime_presentations` |
| §83.2 singleton with h,k | `rt_singleton_type/maps/singleton` (levels `(a,r)`, `D` formal, scope `capture_term2`) | `test_runtime` block 2; `review_singleton_witnesses` |
| §83.3 Diagram, zero, extend | `rt_diagram_type/zero/extend`, `rt_diagram_value/family/maps` | `test_runtime` block 3, case 2 |
| §83.4 action, middle maps, groupoid laws | `rt_action`, `rt_action_fun`, `rt_action_middle`, `rt_action_maps`, `rt_J`, `rt_lunit/rinv/linv/assoc`, `rt_ap`, `K_of`/`k_base`/`words_equal` | `test_runtime` groupoid block, `runtime full`; `review_generic_identity_action` |
| §96.2–96.4 closed node function | `rt_node_fun` (runtime.c) over `rt_diagram_extend`'s template | `test_runtime` §96 block (four level tuples, computed tail, β-equality with `extend`); `review_runtime_nodes` 0/4 + levels (ASan+LSan), generic+levels (TSan); `run_runtime_nodes.py` |
| §84.1 export, comparison with the compiler | `rt_diagram_export`, `diagram_nodes/output/params` (compiler.c) | `test_runtime` case 3 (empty, two-node, shared predecessor, loop residual) |
| §84.2 reuse along an identity | `rt_reuse` | `test_runtime` case 2 |
| §87 cases 1–7 | as listed in README | `test_runtime`, witnesses |
| §88.1–88.3 audit | `proof_use`, `symbols_of` (explicit stack, memo per ref/scope), `global_edges` (memo per `(symbol, revision)`), `audit_graph` (iterative Tarjan), verdict cache with `deps_current` | `test_proof_boundary` (11 via the `proof_boundary.h` shim), `test_proof_use`, `test_runtime` case 6 |
| §88.2 original evidence and expected type | `transform_evidence` (compiler.c), `transform_proof_use` | `test_proof_use` (recursive equivalence: `check` VALID, `certificate_verify` VALID, audit PENDING), `review_certificate_boundary` |
| §88.4 mathematical use | `audit_use`, `audit_reference_use`, `step_prepare` ph 1, `problem_assumptions`, `problem_core`, `FR_PROOF_USE_AUDIT` | `test_proof_use` (plan evidence, connector reference, connector transform; CORE / ASSUMED / PENDING outcomes) |
| §89 fine accounting | `src/fine.*`, instrumentation in `term.c`, `intern.c`, `dnf.c`, `face.c`, `eval.c`, `net.c`, `check.c`, `proof.c` | `test_fine_cost` (coarse constant, fine growing), `review_frame_cost` |

Measured before/after of the two R2 counterexamples: NORMALIZE 64 / 4,096
candidates at budget 1 — 64 / 4,096 flags written per unit before, 32 after;
fan-out of 256 waiting parents — 256 deliveries in the completing unit
before, at most 1 per unit after. Alias regressions: `escaped_z` 1 → 0,
`returned_term_check` INVALID → VALID; conversion of `f a` and `g a` after
opposite-face warm-ups EQUAL → UNEQUAL (unchanged from before the warm-ups).

Fine-cost obligation (§81.2, §89, §94): the bounded-helper table in README
is the exact contract; three classes remain outside the unit bound and are
named there (kernel calls, fixed-key index probes, amortized buffer growth).
The constant-factor simulation theorem is not claimed.

Two further corrections found while gating the increment (both in v9 code):
`shape.c::shape_under` — memo keyed by the whole ρ made shape computation
exponential on shared subterms under distinct binders; ρ is restricted to the
subterm's free boundary (`rho_restrict`) before the lookup, shapes unchanged
(`test_reuse` 101 and the eight boundaries pass; `test_main`'s map table
16,636 → 991). `net.c` — the `CONTINUE_REFERENCE` event counter was
incremented after `eval_forward_result`, a diagnostic ordering race visible as
`test_compiler` (67) failing with workers on a 2-core host, at b612a07 too; the
count now precedes the publication. `eval.c::eval_reset` — drains work a
client left outstanding under a worker pool before enforcing quiescence
(`review_alias_faces 4` aborted under load).

The ba09e33 review's six findings (R1 interning transaction, R2 singleton
level, R3 residual export, R4 ap/J/reuse templates, R5 lifecycle init, R6
framed reduction records) are corrected as tabulated in README ("The ba09e33
review — six corrections"); its nine regressions (`review_work_edges`,
`review_runtime_edges`) and the unchanged §96 witness are gated, and
`run_ba09e33_review.py` (12 jobs) passes under both sanitizers
(`tests/acceptance-results/v14/`). The b8ba937 review retains `rt_node_fun`
and adds `review_node_level` (`node_(2,0,0)` VALID at level 3) as R2 coverage;
it is gated, and `run_b8ba937_review.py` (14 jobs) passes under both
sanitizers (`tests/acceptance-results/v15/`). The v14 review accepts R1–R5 and
the R6 drain case; its `reservation.patch` (no payload zero-fill in the
reservation unit) is applied and its probe gated, and the §94 lowering is
continued — chunked record-store relocation with a non-moving offset table,
framed lookups for the fixed-key indices consulted from units, ownership
transfer for `PREPARE`'s list/hypotheses and `FAMOP` plus; `run_v14_review.py`
(15 jobs) passes under both sanitizers (`tests/acceptance-results/v16/`). The
remaining unrefined bodies are listed in README ("The v14 review"). The v16
review accepts that increment, supplies `prepare-boundary.patch` (the cold
`expr_boundary` recursion in `PREPARE` becomes the shared `BOUNDARY` job) —
applied, with its two probes gated — and directs two accounting corrections,
made in README: the host-allocator assumption is stated for the block
allocation/clearing/release calls, and fixed word-size bounds are documented
as constants. The `PU_ASSUMED` copy is lowered in the same commit;
`run_v16_review.py` (12 jobs) passes under both sanitizers
(`tests/acceptance-results/v17/`). The two commits after it complete the
allocator (`src/arena.c`: one reservation, free lists, paged buffers,
chunked clearing; README "The allocator") and lower the proof-use audit to
engine units (`SYMS`/`EDGES`/`AUDIT`; README "The proof-use audit in
units"); `review_arena_budget` and `review_audit_budget` are gated.
The v19 review's corrections (R1 prerequisites before every verdict, R2 the
audit as a shared judgment with per-judgment marks, R3 paged retirement) are
applied as supplied and its probes gated; the kernel calls units make are now
kernel continuations (`src/kcont.c`: a thread whose stack is the retained
continuation, one fine transition per unit, yielding only lock-free, shared
jobs for pure calls), the engine's remaining fixed-size records and chunked
tables come from the arena with chunk clearing in units, and the kernel's
interner hashes/compares/copies outside its lock. The kernel's allocator
(`src/kalloc.c` over the arena, clearing/copying one word per step), its
interner (unlocked hashing/comparison/copy, incremental growth from fresh
zero arrays) and its sorts (one sift per step) are in transitions as well;
what remains is stated in README ("The v19 review and the kernel
continuations": the transition-free evaluator task and the constant added by
a yield deferred past a locked section).

The v20 review (`REVIEW-v20.md`, bundle in `tests/review-v20/`) is
implemented: the reviewer's `v20-local-fixes.patch` unchanged; per-job
kernel continuations with yielding checker and evaluator waits (R1);
attempt-local UNRESOLVED outcomes restarted on a later attempt and
propagated to dependent jobs (R2); the evaluator task inside the ordinary
accounting, cursor-based interner probing with unlocked comparison and a
publication check on `n`/`gen`/migration placements, heap-sorted maps (R3);
reusable zero blocks through dirty lists cleared in units (R4). The outer
critical sections were audited per acquisition site
(`tests/acceptance-results/v21/lock-audit.txt`) and the input-sized ones in
the checker, the evaluator, the term layer and the proof-use boundary were
moved out of their locks or stepped; README ("The v20 review") lists the
sites that remain, with their measured maxima. `run_v20_review.py` 19/19 and
`run_v19_review.py` 16/16 under ASan+LSan and TSan; `make test` and
`make tsan` clean with the v20 probes gated.

The foundation review (`tests/review-foundation/`, `PREFIX-CONTRACT.md`,
`FOUNDATION-ROUTE.md` at the repository root) is integrated at the
producer/receipt boundary: committed prefix facts published at every
forwarding cut, lifted to waiters by one-waiter notification jobs (SEQ and
CONTEXT), and selected as immutable pinned facts by the adapter search.
`review_live_prefix` and `run_live_prefix.py` pass (4/4 ASan+LSan, 4/4 TSan);
`tests/test_prefix.c` covers the contract's nested, premise, face, joined,
schedule and proof-use cases. README ("§84.2 committed prefixes") lists what
is not implemented.

The V21 review (`tests/review-v21/`) is implemented: the reviewer's zero-block
patch unchanged (R1); evaluator waits name the continuation advancing the
awaited producer, with stable job handles and predicate revalidation (R2);
exclusive event attribution through reuse scopes (R3); extensible claim,
root and queue tables and no continuation registry (R4); dependency-driven
teardown with closed-session discard (R5). `bounds.patch` is merged; the
arena grows by host extents; levels, costs and differences are exact
naturals with framed arithmetic in the engine; the kernel's recursion runs on
on-demand stack segments. README ("The V21 review and the bounds contract")
lists results and what is not done.

Integration status of §§83–84 / §88, stated precisely: the constructors and
the generic action are production templates in `src/runtime.c`, used by the
host export and validated against the compiler's emitted maps by conversion;
the compiler's `identity_pair/identity_action` remain the host-prepared
convenience, their bodies not re-routed through `rt_action` (the equality of
the two is checked by conversion in `test_runtime`, not assumed). The
proof-use boundary is production code in `src/proof.c`, invoked at
preparation for every evidence use; it is not invoked by `check`,
`certificate_verify`, `compile_*` or the evaluator, whose meanings are
unchanged. Verdict caching is per judgment with revision dependencies; the
author's whole-environment `environment` guard survives only as the `env`
snapshot field of `ProofUse`.

## 6. Representation choices a reviewer should know

Listed in `README.md` under "Representation decisions". The two most likely to raise an
eyebrow: a neutral result retains the original eliminator reference (as §12 says) rather
than a rebuilt head around the evaluated scrutinee (the review accepted this); and bound
atoms of scopes live in the variable/dimension id spaces (`BOUND_BIT = 1<<61`, below the
atom shift of the interval and face encodings) so that no existing structural operation
needed a new case for them.

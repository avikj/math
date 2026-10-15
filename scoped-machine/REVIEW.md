# Reviewer guide

This is a from-scratch C11 implementation of `HANDOFF.md` (*Scoped references and face
sensitive cubical evaluation with interaction optimality*, 14 October 2026). The guide
says how to check it without trusting the implementer's summary.

## 1. Run

    make test     # ASan/UBSan: 124 acceptance/law checks + 23 net checks; 24-schedule comparison;
                  # concurrent clients (storms, pools); then the first two suites again with 4-thread pools
    make tsan     # the same suites under ThreadSanitizer (several minutes)

Expected final lines: `124 passed, 0 failed`, `schedule check passed`, `concurrent check passed`.

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
| §31 comparison | `canon_finish` | `src/canon.c` |

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

## 5. Open items for the spec author

1. **Conversion of types in occurrence validity (§2, §22 item 4).** `occurrence_validate`
   compares a context's declared type with the variable's declaration type by reference
   identity. The spec gives no definitional-equality procedure and says it does not prove
   equations by pointer identity; a conversion check is a design decision the author must
   make (structural only, full bidirectional checker with conversion via `whnf`, or none).
2. **Control deliveries.** A false-face or invalid-occurrence request is a DELIVER with no
   REQUEST/PUB (§10 says the continuation receives `NO_OBSERVATION`; §26's four transitions
   do not list it). It is deterministic per configuration; the author may want to name it
   as an event class.

## 6. Representation choices a reviewer should know

Listed in `README.md` under "Representation decisions". The two most likely to raise an
eyebrow: a neutral result retains the original eliminator reference (as §12 says) rather
than a rebuilt head around the evaluated scrutinee; and the composition clauses are C
definitions building core terms with provenance-keyed fresh names rather than `GLOBAL`
bodies, because a family parameter with a free dimension cannot be passed through a term
variable in this representation.

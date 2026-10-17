Subject: V21 review — R1–R5 corrected; bounds patch merged; extensible arena; exact naturals with framed arithmetic; nesting on stack segments; run_v21 8/8, run_v20 19/19, run_v19 16/16, prefix 4/4 under ASan+LSan and TSan

This tree also contains the §84.2 prefix integration delivered as v22
(README "§84.2 committed prefixes"); your V21 bundle is in `tests/review-v21/`,
`review_v21.c` / `run_v21_review.py` in `tests/` unchanged and gated.

Per case (fresh builds through your runners, `tests/acceptance-results/v23/`)
- zero-head, zero-order: 0 nonzero words; zero-stress: 4 000 allocations all
  zero. Your `arena-clear-owner.patch` applied unchanged; its ownership
  invariant is kept by the extent allocator (below).
- ledger: actual 19, charged 19.
- capacity: 257 continuations complete (no registry).
- wait-owner: the consumer names B's active producer (actual_owner=1).
- cleanup-wait, cleanup-drain: both return.
All eight exit 0 under ASan+UBSan+LSan (`detect_leaks=1`) and TSan.

R2 — waits denote actual awaited work. A task records the continuation
executing it on its producer (`Entry.exec_kc/exec_job`); a waiting
continuation names, via `producer_owner`, the continuation advancing the
awaited entry or a RUNNING producer it consumes (one entry per step); the
dependency handle is the job id read at installation (`KCont.blocked_job`).
In the engine a kernel predicate wait (`Op.kwait`) is revalidated after each
unit of its dependency and never receives the dependency's result as a JOIN.
Evaluator waits name only continuations executing tasks, which are never
themselves waiting, so these edges cannot close a cycle; checker claim waits
keep the checker's wait-cycle and assumption rules. Added: `test_v21_extra
wait-shared` (two consumers of one producer both name it; an unrelated
continuation stays suspended while they complete), `wait-early` (the consumer
completes on the producer's publication while the owner's call is still
running).

R3 — exclusive attribution. A reuse scope owns a kernel call's work and the
evaluator tasks of every producer it launched (`Entry.scope`, entered per
task on whatever thread runs it); each event increments the global counter
and once its owner's scope; a closed scope folds exactly once. No global
before/after snapshot remains. `ledger-mixed`: shape, dependency-check and
receipt classes, serial and interleaved, 0 and 4 workers: charged = actual in
every case.

R4 — capacities. Claims, root occurrences and the evaluator queue are chunked
tables over full-width directories, chunks created before the lock, consumed
queue chunks retired; `growth`: 5 000 claims, roots and simultaneously queued
tasks across chunk boundaries.

R5 — teardown. `work_free` drains started continuations through their
dependencies (each pass grants every continuation not waiting on an
uncompleted one; passes repeat while one completes); what remains is discarded
under the closed-session precondition (`kc_abandon`: never granted again, its
parked thread detached, its host-allocated record kept). `cleanup-orders`:
both allocation orders, a second consumer, handles released before and after.
A restarted job's old stack is released one frame per unit (your
`job_restart_if_stale` note).

Bounds contract
- `bounds.patch` merged onto the current tree; `review_bounds` at arities 1,
  16, 17, 63, 64, 65, 129 (mixed 3, 63, 129; your probe requires n > 0 and
  multiples of 3 for mixed), required depth 4 096, sparse/full-width
  directories, complete signatures — both sanitizers.
- Arena: host extents on demand, exact extent index for kalloc, orders to the
  native width, FRESH / DIRTY_FREE / CLEARING / ZERO_READY. Dirty blocks are
  reused by ordinary allocations directly and by unlocked zero allocations
  after clearing outside the arena lock, one word per transition; a requester
  holding a lock takes FRESH storage (no clearing under a lock).
  `test_arena_extents`: 25 growth boundaries with old blocks intact, dirty
  reuse with 0 nonzero words, constant owned footprint over 200 rounds,
  production check VALID under four-page extents.
- Exact naturals (`nat.c`): immediates below 2^63, canonical interned limb
  records above, one transition per limb. Levels exact (interned optional
  pairs, decimal labels); costs exact (`COST_MAX` removed); differences exact
  signed (`int64_t` readers return `INT64_MIN` when not representable). Every
  engine cost operation goes through `cost_op`: immediates in the unit, boxed
  operands as a shared `KK_NAT` job resumed at a saved phase. `test_exact`:
  U_{2^32+1} : U_{2^32+2}; U_{2^64} : U_{2^64+1}; 2^192 by carry with decimal
  export; costs past 2^62 and 2^64; 3 − 2^64; a 256-limb addition at one
  transition per grant; an engine SUM 2^128 + 2^128 = 2^129. The large-value
  host-failure assertions in `test_work` are replaced by exact tests; your
  `review_end_to_end packed-level` now stores 2^32 exactly and rejects the
  mismatched annotation as INVALID; `universe` passes the reserved word
  UINT64_MAX, which aborts (a permitted outcome of that mode).
- Nesting: `infer_clause`, `check_clause`, `conv_type_clause`,
  `conv_term_clause`, `spine`, `shape_under`, `interp`, `val_ref`, `val_scope`
  continue on a fresh same-thread stack segment when fewer than 256 KiB remain
  (`kstack.c`, swapcontext with sanitizer fiber annotations). `test_deep`:
  f^20000(x) shaped, validated, evaluated and checked on a 256 KiB thread (690
  segments; 5 000 under TSan). This is not the explicit-frame
  defunctionalization of §6.

Lowered locked sections: net operation rules compute their kernel results
from node snapshots before locking (`op_compute`/`op_commit`); CONTINUE_REFERENCE
and EVAL rules issue their evaluator requests after unlocking; no arity or
retry cap in the redex step; compiler keys interned outside `CR.mu`; template
library registered outside its mutex. Lock audit (`lock-audit.txt`): above
124 fine steps only the engine's synchronous constructors/drivers under `LOCK`
remain (4 610 in `dgraph_add_producer`, 477, 258, 230, 207).

Remaining bounded-transition sites, exactly
- the kernel's recursion is C recursion on stack segments, not explicit frames;
- engine synchronous constructors/drivers hold `LOCK` for their whole run;
  `dgraph_add_*` and the compiler's record vectors grow by copying under lock;
- sections wrapping a fixed-size-key interner call under the term lock or an
  entry lock are bounded by the key's probe-chain length over 32.

Exact dependencies on your side (IMMEDIATE-SCOPE rows not implemented)
- Witnessed effect / authority boundary: FOUNDATION-ROUTE §4 states the
  exclusion law and its refinement proof, and that a local implementation can
  realize it by atomic head advancement, but not the machine rule: the record
  shape of an authority boundary, a proposal, an accepted occurrence and its
  receipt; the judgment that admits a proposal (its premises and how they
  enter checking); how an accepted occurrence appears in a term, a boundary and
  a substitution; what a pending transfer is in the machine's terms. With
  those, the local realization (head advanced under its owner's lock, receipts
  as immutable facts, replay rejected by the consumed-occurrence check) is
  direct.
- End-to-end acceptance (runtime identity, pending prefix, shared producer,
  distinct consumers, accepted effect, pending transfer, a balance-preserving
  cycle with retained change): depends on the rule above for the effect,
  transfer and balance parts; the identity, prefix and producer parts exist.
- Whole-machine overlap/refinement and the declaration/posing interface: the
  actual complete-state relation and its transition inventory are in README
  ("The V21 review…", "§84.2…", "The v20 review…" and the lock audit); the
  overlap classification and theorem are yours.

Results: `run_v21_review.py` 8/8, `run_v20_review.py` 19/19,
`run_v19_review.py` 16/16, `run_live_prefix.py` 4/4 under ASan+UBSan+LSan
and TSan; `make test` and `make tsan` clean (TEST.log, TSAN.log).

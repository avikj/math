# HANDOFF (v20 review round, work in progress) — state at the last push

Tree: avikj/math main, scoped-machine/. Suites green under ASan at the last
check (test_main, test_work 217, test_reuse 101, test_compiler 85, test_check
80, test_proof_use 21). Full gates (make test / make tsan) NOT rerun since the
v20 review began; the author's run_v20_review.py NOT run end to end.

## Done this round (REVIEW-v20.md, tests/review-v20/)
- v20-local-fixes.patch applied unchanged (R1a help-to-completion, R3(3)
  mapb_finish heap sort, R4a chunked_free ownership).
- R1(b): continuations are per job (no global active gate). A checker claim
  wait or evaluator wait inside a continuation yields naming the owning
  continuation (kc_wait; check.c claim_wait_locked; eval.c eval_wait_locked);
  the job then waits on that job (step_kernel sets waiting_on; deliver_to
  leaves a KERNEL frame to re-examine its own condition). W.kc_active /
  W.kc_owner are inspection only (most recently granted continuation).
  review_v20 independent / independent-release / independent-cone pass.
- R2: KOutcome (OK / INVALID / UNRESOLVED). An unresolved job is failed with
  o->unresolved = check_attempt(); a request in a later attempt restarts it
  (job_restart_if_stale in job_for / job_at); dependents inherit the tag in
  deliver_to. check_attempt() added. review_v20 retry / prepare-retry pass.
- R3(1): evaluator tasks resumable (execute marks k->in_eval instead of the
  lock-depth exemption); shape.c interns/memos without the outer shape_mu.
  evaluator-32 max 52 fine steps per unit; evaluator-256 max 52 (was 3087).
  evaluator-1024 NOT yet run.
- R3(2): kernel interner: cursor-based probing (<= 32 probes per locked
  section, candidates compared unlocked, kc_safepoint between sections),
  budgeted migration with retained placement cursor (moving/mprobe), O(1)
  insertion at the scanned chain end, generation counter. review_v20_intern
  300: max 32 transitions per grant.
- R4(b): zero-region blocks are reused: released ones go to a dirty list,
  cleared 32 words per arena_tend_zero step (driven by arena_tend each unit),
  then a zero-ready pool per order; arena_alloc_zero takes the pool first.
  review_v20 lifecycle / fresh-retire pass.
- Teardown: work_free completes abandoned continuations BEFORE freeing job
  stacks, then kc_shutdown.
- Lock-section audit tool: build with -DKC_LOCK_AUDIT (common.h wrappers
  record per-thread fine steps under the outermost lock per site; report at
  exit). Last audit (CUBICAL_WORKERS=0, all suites) — sites still holding
  input-sized work under a lock, to fix next:
    eval.c:425 find_adapter (E.entries_mu held over candidate scan) 587518
    check.c claim_index_locked under K.mu (1054/567/1096/1290/613/479):
      wordmap hashing/intern of keys under K.mu  up to 491542
    eval.c:566 roots_mu vec_push 65538 (vector growth copy)
    net.c:740 multi-node lock across a rule 32223
    template.c:1036 `once` init 21639
    eval.c:245 res_mu vec_push 4098; eval.c:516 a->mu 1040; check.c:281 547
  Everything else <= 350.

## Not done (next steps, in order)
1. Fix the audited sites above (move hashing/interning outside K.mu in
   claim_index_locked — wordmap is internally synchronized; find_adapter
   candidate collection outside entries_mu or cursored; vec growth under
   roots_mu/res_mu → Paged or unlocked growth; net.c:740 and template once).
2. words_append / variable memcpy transitions (common.h: per-word tick via
   kc_tick when kc_tl; count in a fine counter).
3. Gate review_v20 (all modes), review_v20_intern (64, 300) in Makefile test
   and tsan; run run_v20_review.py (19 jobs) asan + tsan; full gates.
4. README: replace "~33/~80 transitions" statements with the audit table
   (per-site max) and the remaining qualifications; REVIEW.md paragraph;
   MESSAGE for the author (reviewer asked: per-case result, bounds,
   ownership invariant; inspector mapping for W.kc_active).
5. Remove KC_TRACE getenv("KC_ABORT_AT") debug line in kcont.c (harmless,
   only under -DKC_TRACE).

# Review of v14 / 4d51993

## Acceptance decision

This delivery answers the **ba09e33 six-finding review**. It is not treated as
an answer to the later b8ba937 follow-up. The latter's higher-level node test
was run as additional evidence and now passes without further changes.

**R1–R5 are accepted as corrected in this pass. The original R6 table-drain
defect is also corrected.** All fourteen independent jobs pass under both
ASan/UBSan and TSan, including the production runtime's 85 checks.

The full bounded-step obligation remains open, as the worker explicitly
discloses. One specific remaining initialization loop is documented below,
with a tested patch. This is work within the existing R6/§94 requirement.
It does not reopen the accepted mathematical constructors or require a new
architecture.

## Source and evidence

Reviewed the user-supplied `scoped-machine-v14-delivery.zip`, whose message
identifies commit `4d51993`. Compared its source with the prior b8ba937 delivery.
Changes are in `work.c`, `runtime.c/.h`, `compiler.c`, `proof.c`, and `check.c`.
The object files shipped in the archive were **not used**. Every core C file
was freshly compiled for each sanitizer configuration.

The independent runner is the fourteen-job follow-up runner from the previous
review. It includes the twelve earlier jobs, the higher-level production-node
case and the production runtime suite. ASan runs use `detect_leaks=0` because
this review host cannot perform LSan's process inspection. The worker's LSan
and full `make test`/`make tsan` results remain worker-supplied evidence; no
independent full-gate rerun is claimed here.

| Finding or test | Independent result |
| --- | --- |
| R1: alternating public support handles | PASS under both sanitizers |
| R1: SUPPORT/MUST yielding the same canonical set | PASS under both |
| R1: table growth across suspended insertion | PASS under both |
| R2: singleton at a=2, r=0 | VALID under both |
| R3: dependent two-node residual export | VALID under both |
| R4: ap/J/reuse substitution identity, with typing/conversion controls | All three reference equalities hold under both |
| R5: cold concurrent runtime and proof use | PASS, including TSan |
| R6: one reduction unit must not drain the pending table relocation | PASS under both |
| Unchanged §96 witness at zero/four workers, plus mixed levels | PASS under both |
| Later follow-up: node_(2,0,0) | Signature and body VALID under both |
| Production runtime suite | 85 checks, zero failures under both |

The separate `check` diagnostic initialization is compatible with the reviewed
calls: a valid check now leaves a defined empty diagnostic. It is not counted
as a substitute for any of the six repairs.

## Why the repairs address the causes

R1 reserves an exclusive record extent, with no published id before all payload
words have been copied. Slot-array generations invalidate saved probes and
comparison continuations. The candidate is probed again before publication,
and an equal completed key receives the existing id. These changes address
both record corruption and loss of canonical identity while retaining
suspension.

R2 uses `max(a,r+1)` for the outer family Π codomain. R3 carries the tail's
already-specialized terminal type through the residual fold. Both match the
previously tested mathematical corrections.

R4 constructs ap, J and reuse over their complete typed formal telescopes,
caches one body per level tuple, and invokes it by simultaneous substitution.
R5 initializes the runtime/proof modules during the existing serial compiler
lifecycle and synchronizes the template-count reader. This closes the observed
cold-client races under that lifecycle; it does not introduce concurrent reset.

R6 gives reduction and mapped-proof record construction retained finishing
phases, using framed child interning. Fixed-key lookups consult the old table
during migration instead of forcing it to finish. The formerly failing drain
case now leaves relocation pending after its one-unit budget.

## Remaining local issue inside R6: reservation initializes an entire payload

`work.c::step_intern`, phase 5, currently contains:

```
for (size_t k = 0; k < f->buf.n; k++)
    words_push(&t->store, 0);
```

This is variable work inside one unit even when no allocation or capacity
growth occurs. The new regression preallocates enough capacity, fills the
unused extent with a sentinel, advances the production reservation phase once,
and counts actual payload words changed:

| Payload words | Budget | Charged handle units | Payload words written |
| --- | --- | --- | --- |
| 64 | 1 | 1 | 64 |
| 4,096 | 1 | 1 | 4,096 |

It also completes each operation and checks the exact record contents and
canonical id. The delivered code is functionally correct in these cases, but
this reservation body does not meet the bounded-unit claim. The existing
disclosure about amortized buffer growth does not explain these writes: the
probe confirms that the storage pointer/capacity is already available.

### Ready correction

`reservation.patch` makes reservation a logical extent reservation:

1. Check that the extent-end addition is representable.
2. Ensure capacity using the current helper.
3. Capture the offset and advance the store's logical end by header + payload.
4. Write only the two header words.
5. Leave the payload private and uninitialized until the existing one-word
   COPY phase fills it; publish only after that phase finishes.

No payload zeroing is necessary: an unpublished extent has no record id or
table slot, and every payload word is written before it becomes readable as
a record. Exclusive extents and the generation/reprobe logic remain intact.

With the patch, the same two probes write **zero** payload words in the
reservation unit, then complete to correct canonical records. The candidate
passes the interleave, same-key, growth and drain regressions plus this new
reservation regression under **both** sanitizer configurations. Candidate
evidence is saved separately and is not attributed to the unmodified delivery.

This patch removes the redundant initialization loop. It deliberately retains
the existing capacity helper: capacity growth itself is still part of the
already-disclosed allocation refinement. Applying this local patch must not
be reported as completion of that broader obligation.

## Exact next instruction

Keep the accepted corrections and apply the supplied reservation patch.
Add `review_reservation_budget.c` to the existing regression gates. Continue
the already-assigned §94 work: suspend fixed-key collision probes, buffer
growth/copying/initialization and kernel/audit traversal at the required bounded
steps. The existing PREPARE buffer-copy/sort paths must be included in that
lowering rather than hidden behind the fact that its final interning is framed.
Retain actual fine-work accounting and the semantic coarse projection.

No further implementation choice is left open for this local reservation
repair. The next pass should integrate it and finish the disclosed lowering,
preserving the corrected semantics and current constructor family. R1–R5
need not be represented as still unimplemented merely because §94 is not done.

## Reproduction

The bundle contains `run_v14_review.py`. It fresh-builds by default and runs
the previous fourteen jobs plus the reservation probe:

```
python3 run_v14_review.py TREE --sanitizer asan --output asan.json
python3 run_v14_review.py TREE --sanitizer tsan --output tsan.json
```

All fifteen jobs should pass after the local patch. The saved evidence for this
review consists of the fourteen-job runs against the delivered source and the
reservation/candidate tests executed separately, as their filenames indicate.
Use `--detect-leaks 0` only on hosts where LSan is unavailable. The reserve test
includes production `work.c` directly and therefore links without `work.o`,
as the runner arranges.

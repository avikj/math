# Independent review of ba09e33

Reviewed source: `avikj/math`, `scoped-machine/`, commit
`ba09e3307401ee35c21b4941f0b27a8cdbe8b163`. All 130 fetched files were checked
against the commit tree's Git blob hashes. The supplied snapshot was not modified.

**Decision: retain this construction; do not sign off this revision yet.**
The runtime construction is executing and checking. The prior alias regressions
are closed. Six specific implementation findings remain below. These findings
require corrections to the existing implementation, not a different calculus,
a new planner, or separation into new runtimes.

## Independently established progress

The unchanged §96 `review_runtime_nodes.c` passes with zero and four installed
evaluator workers under ASan/UBSan and TSan. It checks the closed node function,
the runtime-built nonempty diagram, the resulting collapse/expansion, both
inverse witnesses and their endpoints, with **zero registered transforms**.
Its mixed-level cases `(1,0,0)`, `(0,1,0)`, `(0,0,1)` also pass. The full runtime
mode took about 1.45–1.48 seconds under ASan/UBSan and 2.5–2.6 seconds under TSan
in the first focused run. This resolves the earlier memory failure for this
particular witness; it is not a performance claim about every composite term.

The existing alias scope/face tests pass at zero and four workers under
ASan/UBSan. The existing work-budget, proof-use (19 checks), fine-counter,
work (217 checks), and default runtime (76 checks) suites also pass in the
focused run. The source change restricting the shape memo's
environment to the subterm's free boundary matches the measured improvement.

I did not repeat the worker's entire forty-minute TSan gate. The separate
`build/runtime full` attempt exceeded the local 180-second review limit and is
not counted as passing; it is not a seventh correctness finding. See the saved
JSON for each actual run. LeakSanitizer cannot inspect `/proc/.../task` on this
review host, so these independent ASan runs use `detect_leaks=0`. The worker's
reported LSan results remain worker-supplied evidence.

## R1 — resumable interning corrupts records and loses canonical identity

**Priority:** correctness blocker. **Location:** `src/work.c`, `step_intern`,
especially phases 1/3 (lines 527–545), and saved slot cursors in INTERN/LOOKUP.
**Contract:** §§71, 75.2, 94.2; suspended independent handles may interleave.

**Public reproduction:** create two distinct named atoms, call `op_support` on
each atom formula, then alternate `op_step(handle,1)` until both complete.
Their returned sets must be the respective singleton sets. Instead:

```
a=6 b=7
returned records=(1790477323352341347,2),(2,2)
expected records=(K_SET,6),(K_SET,7)
```

This is a single-threaded logical interleaving, so a data-race sanitizer alone
cannot find it. The `same-key` mode interleaves SUPPORT and MUST on the same
atom, which must return the same canonical singleton. It also fails.

The mechanism is exact: phase 1 appends a header to the shared `Words store`
and remembers its starting offset. Phase 3 later appends payload words to the
current shared end. Another handle can append its header/payload between those
steps. The first record's declared contiguous payload then contains the other
record's bytes.

There is an additional publication problem in the same transaction. The
`growth` mode suspends after copying a complete key, grows the table through
ordinary `atom_named` calls, then resumes publication. The saved slot index
belongs to the old table. The framed singleton gets id 3010 while ordinary
canonical interning of that same singleton gets 3011.

**Required repair:** make each suspended insertion a valid transaction.

1. Give the candidate exclusive storage whose extent cannot be interleaved
   with another candidate's writes. A retained offset/extent or an owned
   payload block must identify the whole record; appending each word to the
   current global end is not valid reservation.
2. Keep incomplete payloads unavailable to ordinary record readers.
3. Before publishing, re-establish the probe in the current table and check
   for an already interned equal key. Only one canonical id may be returned.
   Table changes between units must invalidate saved slot cursors, including
   LOOKUP and comparison continuations that subsequently resume probing.
   Do not overwrite an occupied slot or publish at an old table's index.
4. Retain all copying, hashing, comparison, reprobe, growth and cleanup state
   in frames. Serializing each whole operation until completion would evade
   the interleaving failure by violating the required suspension contract.

These are representation invariants, not a choice of new mathematics.
Regression modes: `review_work_edges interleave`, `same-key`, `growth`.
The first two use only public operations; the growth mode uses a white-box
stop at the production publication phase and public constructors to grow it.

## R2 — the singleton family's outer Π has the wrong formation level

**Location:** `src/runtime.c:147`, `sing_formals`.
**Contract:** §§59.1, 83.2, 87: exact levels for the full constructor family.

For `A : U_a`, the formal family has type

```
D : Π(x:A). Π(e:Path_A(t,x)). U_r.
```

The inner Π forms at `max(a,r+1)`. Therefore the outer constructor must be

```
mk_pi_lv(a, max(a, level_succ(r)), x, A,
         mk_pi_lv(a, level_succ(r), e, E, mk_universe(r)))
```

The current outer codomain annotation is only `r+1`. Cases with `a <= r+1`
hide the error. At `a=2,r=0`, a valid context and valid family image produce
INVALID: `universe annotation differs from the formation levels`.

**Repair:** the one-line change in `runtime-level-and-residual.patch`.
The `levels` regression passes with that candidate patch and fails on ba09e33.
Keep exact levels; do not introduce cumulativity or weaken annotation checks.

## R3 — residual export forgets substitutions performed by its tail

**Location:** `src/runtime.c:500–517`, `export_fold`, particularly line 514.
**Contract:** §§44, 83–84, 87 case 3, dependent right-fold export.

A valid two-node residual telescope suffices:

```
Γ = A:U_0, a:A
x1:A, e1:Path_A(a,x1)
x2:A, e2:Path_A(x1,x2)
terminal Z = Path_A(x2,x2).
```

`diagram_validate` returns VALID. `rt_diagram_export` then returns a term
whose check at the advertised presentation type is INVALID: `unbound variable`.
The canonical terminal is `Path_A(a,a)`.

At an outer fold step, the tail has already specialized the terminal along
later nodes. The code instead computes `Zc = reindex(o,nu)` from the original
terminal `o`, retaining later variables that should have disappeared.

**Repair:** the fold returns its presentation and its current canonical
terminal type. Define `Z_n = o`, then at node k:

```
nu_k = [x_k ↦ t_k, e_k ↦ refl(t_k)]     // one simultaneous map
Z_k = reindex(Z_(k+1), nu_k)
centre = reindex(tail_presentation, nu_k).
```

Use `Z_k` in the maps-composition and presentation annotations. Pass `Z_k`
outward; do not restart from `o`. The supplied patch implements this local
change. Its two-node `residual` regression checks VALID with the candidate.
It needs no new eliminator or host compilation during evaluation.

## R4 — ap, J and reuse bypass the fixed-template contract

**Location:** `src/runtime.c`, `rt_ap` (89–93), `rt_J` (304–309),
`rt_reuse` (492–495). **Contract:** §§74–84/87 and `runtime.h`'s explicit
fixed-template, simultaneous-substitution contract.

These functions build raw origins directly over actual arguments. The other
constructor families instead memoize an origin over formal arguments and
return its instantiated view.

For valid `x,y:A`, `p:Path_A(x,x)`, `q:Path_A(y,y)` and the simultaneous map
`σ=[x↦y,p↦q]`, the regression reports:

```
all six helper terms typecheck
all three specialized/direct pairs convert equal
reference equality: ap=0 reuse=0 J=0
```

Thus the problem is the promised identity of references and reusable template
construction, not a claim that these three mathematical formulas are wrong.

**Repair:** use the existing memoized-formals/`inst` pattern for all three.
Keep the current core bodies and declare all their parameter dependencies:

| Helper | Formal telescope (levels as in its API) |
| --- | --- |
| ap | `A:U_l, B:U_m, f:Πz:A.B, x:A, y:A, p:Path_A(x,y)` |
| J | `A:U_l, a:A, P:Πb:A.Πp:Path_A(a,b).U_lp, d:P a refl, b:A, p:Path_A(a,b)` |
| reuse | `B:U_lb, O:Πz:B.U_lo, x:B, y:B, p:Path_B(x,y), a:O x` |

Build one body per level tuple, bind its internal dimensions there, and
instantiate its term formals in one simultaneous map. Preserve declared
types, guards and dependency closure. In particular `B` in ap must enter its
typed formal dependencies even though the existing raw body ignores `Bt`.
Use the corrected outer Π level from R2 when declaring J's family telescope.
The `commute` regression must retain its positive typing/conversion controls
and additionally pass all three reference equalities.

## R5 — the new modules race on concurrent first use

**Location:** `src/runtime.c:14`, `rt_init`; `src/proof.c:18`, `proof_init`.
**Contract:** the existing multi-client lifecycle/concurrency contract.

After ordinary serial `machine_init/eval_init/check_init/compiler_init`, eight
clients simultaneously calling `rt_maps_id` race in `wordmap_init`. Eight
clients calling `proof_use` race in `memset(&P,...)` / initialization. Both
reproduce with TSan, `halt_on_error=1`, exit 66. The proof test warms ordinary
checking first, so the observed race is in the new proof module's first use.

**Repair:** include both modules in the existing serial initialization phase
before public clients are admitted, with matching teardown at the already
required quiescent lifecycle boundary. Remove unsynchronized first-use
mutation from public calls. If idempotent public init remains callable, guard
it with a lifecycle lock; a bare `live` boolean is insufficient. Synchronize
`rt_template_count` reads with writes as well. Preserve machine restart support;
a once-per-process initializer cannot permanently bind a previous machine's
tables or identities. No concurrent reset is requested.

Regression modes: `runtime-cold`, `proof-cold`. They must remain cold after
normal public initialization; do not warm each module in the test to hide the
race. They can become safe because normal initialization now initializes them.

## R6 — a formula reduction unit still drains arbitrary table growth

**Location:** `src/work.c:117–121`, `proof_intern`, `reduction_record`,
`step_reduce` phase 1. **Contract:** §94.2(4), specifically no forced
`ktab_settle`, and the README's claimed formula/certificate unit bounds.

The regression suspends a reduction of `formula_one()` immediately before its
ordinary result frame, stages pending production table growth, and asks for
one unit:

```
charged handle units = 1
old table slots = 4096
relocation cursor after the unit = 4096
relocation pending = false
```

The call is `step_reduce → proof_intern → intern_sync → ktab_settle` (and
`reduction_record` also uses synchronous interning). This is not a term/checker
kernel call or an adversarial collision assumption. It contradicts the new
README rows saying proof/list/reduction records use framed INTERN and that a
unit never drains another operation's relocation.

**Repair:** replace these in-frame synchronous interning calls with retained
child-INTERN phases; carry the proof id into a later reduction-record phase.
Do the same for list/proof/result records on the other reduction branches.
Audit all `intern_sync`, `find_sync`, `ktab_settle`, variable copies and
variable traversal paths reachable from `service/step`, not only the former
NORMALIZE/delivery reproductions. Preserve the existing exact recurrence.
`drain` must return within 32 relocation visits/probes, retain the remainder,
and later complete to the same reduction/proof result.

The README separately discloses unrefined fixed-key probes, amortized buffer
growth and synchronous kernel/audit calls. Those are still unfinished §94
requirements, not solved by disclosure or by retrospective fine counters.
R6 additionally disproves the claimed completed formula fragment. Correct
the inaccurate table rows now; complete the promised frame refinement before
claiming the abstract-step/C-work bound. Neither this correction nor any other
finding introduces search, a frontier, branch-and-bound or program enumeration.

## Worker execution order and acceptance

1. Repair interning transaction safety (R1), including equal keys and growth
   across a suspension. Keep the one-unit interface.
2. Apply the local universe/residual patch (R2/R3); integrate fixed templates
   (R4) and normal lifecycle initialization (R5).
3. Complete R6's framed record paths and the remaining §94 helper audit.
4. Run the supplied runner with a fresh build under both sanitizers, then the
   existing full gates. Preserve the §96 witness unchanged and retain both
   zero/four-worker runs. Report any still-unrefined helper explicitly rather
   than calling R2/§94 complete.

```
python3 run_ba09e33_review.py /path/to/scoped-machine --sanitizer asan --output asan.json
python3 run_ba09e33_review.py /path/to/scoped-machine --sanitizer tsan --output tsan.json
```

Use `--detect-leaks 0` only where the host cannot run LSan; the worker host
previously supported it. The runner expects **all twelve jobs to exit zero**
on the corrected tree. On ba09e33 the TSan run has nine failing regression
jobs and three passing unchanged §96 witness jobs. The two candidate-patch
passes are recorded separately and are not attributed to unmodified ba09e33.

The complete implementation is not accepted yet. The verified runtime
construction and alias correction remain accepted progress. This review
closes its immediate deliverable: each reported defect has an executable
reproduction and a concrete repair contract, without asking the worker to
invent new mathematics.

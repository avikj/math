# PLAN — converting the one execution system to bounded steps (agreed 18 Oct 2026, 14:47)

This file is the working contract. Every step re-reads it. Nothing here is optional.

## 1. Base

24b2bfb implements HANDOFF §§1–59 with five review rounds; `make test` (ASan/UBSan, 75 s) and
`make tsan` (0 reports, 84 s) pass; the §§83/96 runtime-construction witnesses and the §88
proof-use module (11 cases) pass unchanged on it. It was correct for its specification, which
permitted host algorithms inside rules (§19), checking as a separate phase (§34) and blocking
claims (§59.4). Those permissions are what today's direction makes incorrect.

## 2. Why the later history grew

The step bound entered at §65 (15 Oct). 3a0d7c4 met it, and §§67–73, by adding `work.c` — a
second record store and a second operation/frame engine — beside `eval.c`. Every later layer kept
both and added bridges (reuse on the second engine; kcont/kstack; kframe in 95cd52a; my drop
rewrite). Rule: the bound is met by converting the ONE existing system. Never add a second engine,
store, continuation form or bridge.

## 3. The requirement

(a) Every counted step is bounded: `Instr ≤ c·N + d`, N = steps. Any code inside one step whose
work depends on the size of a term, map, face, set, field list, waiter list or table is incorrect.

(b) The fine steps are steps of the relation with the diamond: §§26–27 (one producer per key,
linear continuations, exhaustive request/publication overlaps). So every computation over
variable data is a producer keyed by (operation family, operands) in the one protocol of
`eval.c`, executed as bounded steps, each delivery its own step. A memo computed twice
(wordmap_get / compute / wordmap_put race) is incorrect.

Representation consequences:
- variable records = bounded-arity interned sequences (maps, interval/face clauses, dim/var
  sets, origin field lists, template environments, scope telescopes, contexts, system branches);
- hash collisions advance one probe per step; table growth migrates a bounded number of slots per step;
- fixed-size nodes from free lists, refilled by a counted step (malloc is not a bounded primitive);
- entry state by compare-and-swap (U→R installs the evaluator; waiter push on a lock-free stack;
  R→D swaps the stack); interning inserts by CAS; per-worker deques. No critical section holds
  unbounded work.

## 4. Incorrect in 24b2bfb (to be converted)

- term.c: open_ref (all n fields, each through reindex); mapb_finish (whole vector key); compose;
  make_view (boundary walk + support/fv/required under term_mu); reindex (recursive, racy memo);
  lifted_map; context_make O(n²).
- dnf.c/face.c/interval.c: meet (clause product), normalize, entails, forall, project,
  substitute, negate; set union/remove rebuild vectors.
- intern.c: hash over variable key, unbounded probe loop, full rehash under mutex.
- eval.c: evaluate→open_ref and face tests; eval_system_head loop; publish enqueues all waiters
  (340–343); publish_branchwise/resume_branch/resume_comp_family loops; comp_clause synchronous;
  mk_* through make_view.
- scope.c/template.c/lib.c: recursive capture/reindex/apply; recursive interp; make_view_env,
  environment restriction.
- net.c: rule_op host calls; materialize n ports (uint8_t, line 319); rule_dup_shell copies.
- check.c: recursive checking/conversion; claim_acquire blocks (pthread_cond_wait 188, 208, 318);
  observe calls whnf synchronously; admission blocks (1561).
- compiler.c: recursive synchronous validation/emission/certificate.
(canon.c/match.c: test harness outside execution — unaffected.)

## 5. What stays / what changes

Stays: all mathematics and laws (C[ρ][σ]=C[ρ;σ], single-lookup substitution, dependency-closed
restriction, opening without evaluation, (t, π_S χ) key and projection theorem, capture/apply/∀
laws, reindex(TVIEW(Q,E),σ)=TVIEW(Q,E[σ]), cubical clauses, template library programs, compiler
emission, certificate tags, checker and conversion rules); the REQ/EVAL/PUB/DELIVER protocol and
§27 overlaps; the test suite as semantic regressions.

Changes: execution form. Each function of §4 becomes a family: entry key = (family, operands),
a frame with cursor/locals, a step function doing one bounded increment then requesting a child
key, continuing, or publishing. A synchronous driver `run(family,args)` drives a key's jobs to
publication so unconverted callers keep working; conversion goes family by family with tests green.

One representation: raw origin = constant-field instance of the constructor-program
representation (reduction handoff §4.4), binders by (depth, slot) as in scopes. Gives alpha
identity, raw = template-view identity, and removes the VIEW/TVIEW branch in every head operation.

## 6. Scope after §59

Included: §60 (readings of protocol events: per-family step counters, per-entry counts, folds);
§65 (this plan); §75 (= families); §76 (by representation); §77 (actions keyed by content; checker/
conversion requests keyed by dependency-closed context restriction); §79 (global reads record
revisions; reuse under a later environment when all match); §§80, 83–84, 96 (fixed templates per
level tuple: Maps, presentation composition, dependent singleton with h,k, zero, node, generic
action F/G with middle inverse paths, groupoid laws via J and K(w); compiler exports diagrams as
these values); §88 proof use (judgment family; SCC iteratively, one edge per step; CORE, ASSUMED,
PENDING, INVALID, UNRESOLVED); witnessed-source readings (exact counts: low digit + carry blocks,
CONTINUATION-AND-COUNT-CLOSURE §C; per-producer event support; W(H) by support union; folds as
families); EFFECT-AUTHORITY §§2–9 + §10 witness (proposals, ordered reservations, one atomic commit,
lazy finalization, receipts, duplicate delivery = same receipt, conflict on second consume, cash
instance) as job families; CUBICAL-STOKES-ADDENDUM §10 interface (cube maps and face composition
from substitution, ∂, ∂²=0, cochains/pairing, relative cuts, resource map B, defects of supplied
comparison cells; production cells only from actual rules or checked supplied witnesses).

Excluded: §§61–64, 66–73 (plan comparison/selection — the detour); §86 posing and §§87/91
reflection (not meaningful as stated / no rule supplied; neither implemented nor claimed).

The one contradiction: mid-run adoption (PREFIX-CONTRACT, LIVE-CUT-ADOPTION, prefixes of running
computations) breaks the diamond (§85: lengths 2 and 3 from one state) when a key's recipe consults
whether some other result happens to exist yet. Resolution (superseding the earlier "index frozen per
workload", which was a phase barrier — see §9.5): no recipe ever consults existence of a result.
Reuse is a dependency named by the recipe itself: a specialization key (SPECIALIZE, d, σ) requests
d and transports; a restriction to a stronger face is the same key by the projection theorem
(t, π_S χ); a receipt is the published value of its producer's key. Each result is usable by every
key whose recipe depends on it the moment it is published, in the same run, and the step count of
every key is schedule-independent because its dependency set is fixed by its key. EFFECT-AUTHORITY §10
item 2 realized by keyed sharing (two deliveries of one producer).

## 7. Time (derived upper bound)

| Component | Lines |
|---|---:|
| Protocol: family-keyed entries, CAS states, per-delivery steps, frame storage, worker deques | 900 |
| Bounded records: interned sequence nodes, fixed-size allocator, sequences for all variable records | 600 |
| One construction representation, (depth,slot) binders, field opening on demand | 700 |
| Substitution families | 600 |
| Interval/face families | 700 |
| Scope families | 500 |
| Template interpretation families | 500 |
| Evaluator dispatch and composition clauses | 600 |
| Net | 350 |
| Checking/conversion/admission | 2,000 |
| Compiler | 700 |
| Proof use | 250 |
| Runtime constructions as templates + compiler export | 500 |
| Keys: content, projected contexts, revisions | 250 |
| Receipts + frozen index + specialization | 500 |
| Readings: exact counts, support, folds | 350 |
| Effects | 650 |
| Stokes interface | 550 |
| Tests (11 white-box files adapted + acceptance) | 900 |
| Total | 12,100 |

≤ 33.6 h writing; machine ≈ 15 min (≈30 s build+focused tests per component; one full ASan+TSan
gate at the end).

## 8. Order (one commit per step, focused tests green)

1. Protocol generalization + bounded records + synchronous driver.
2. Substitution, interval/face, set families; single construction representation; field opening on demand.
3. Scope and template families; evaluator dispatch and composition clauses; net (arity-252 and shell copy disappear).
4. Checking, conversion, admission families (no blocking claims, no nested whnf).
5. Compiler and proof-use families; runtime-construction templates; content/context keys; revisions.
6. Receipts as keyed specialization/restriction dependencies (no frozen index; §10).
7. Readings and exact counts.
8. Effects and the Stokes interface; EFFECT-AUTHORITY §10 witness from one execution.
9. Full gates.

Standing rules: design each family completely before writing it; no defect-driven development;
no subagents; work only from the shared specifications; no second engine/store/continuation form.

## 9. Corrections adopted from the 14:54 attachment (binding on all later steps)

1. No representation may insert a dependency absent from the object. Variable records are NOT
   converted to cons sequences: reaching field k must not require traversing fields 0..k-1.
   Records stay contiguous (O(1) access to any field); what becomes stepped is their
   construction and interning: hashing, trie descent and full-key comparison of a variable
   record are a family advancing a bounded number of words per step. (Sequence module removed.)
2. Judgments depend on their actual premises, not on admission of everything registered.
   Whole-environment admission (§57 R1 / §59.4 freeze-reopen lifecycle) is replaced by validity
   of the judgment's dependency closure: the symbols its context, type and term actually reach,
   with their declarations/bodies checked as premises (a cyclic dependency such as bad/dependent
   still rejects when used). No global freeze, no session qualification of cached judgments.
3. One route for identity actions. TRANSFORM_CALL, CompiledTransform, GraphPairTemplate,
   certificate re-emission and APPLY_TRANSFORM/CONTINUE_REFERENCE are identified with the
   ordinary generic action (§83.4 F/G on Diagram values). The host compiler becomes an input
   adapter that builds Diagram values (with diagnostics); it defines no second semantic route.
   This replaces "compiler as families" in step 5 and reduces it.
4. Readings are folds of the local records of the steps that ran. No central event journal
   into which subsystems report; no global serialization of histories.

## 10. Rule from the 15:23 attachment (binding)

5. No host distinction may change the dependency, admissibility or compositional behaviour of the
   represented construction. Concretely: no phase barrier (check-then-run, finish-workload-then-
   reuse, register-then-publish); no privileged preparatory language with its own state or
   authority; a derived value (identity p, transform, receipt, completed prefix) acts through the
   generic action wherever its type permits, as soon as it exists, with no "install" event between;
   one judgment is executed once — the checker and the evaluator request the same keys rather than
   re-deriving. Ability of an added mechanism to solve the problems it introduced is no defence of it.
   Consequence for §8: step 6 is "receipts as keyed specialization/restriction dependencies"
   (no frozen index); step 4 removes the global admission gate and shares judgment keys with
   evaluation.

## 11. Step-2 machinery (as built) and the remaining step-2 design

Built (2c): frame families `family_define(name, step, loc_size, pure)`; a step ends in exactly one
of frame_request / frame_call (subroutine frame with a parent, no entry) / frame_yield /
frame_finish; FR_* program-counter macros; per-family locals records from pools; pure keys omit
the environment version. The §5 synchronous driver is `family_call`: never blocks, valid inside
and outside jobs — READY returns the value; U is claimed (INLINE_CLAIM at the bottom of the waiter
stack) and the producer is driven on the calling thread, then published to everyone who arrived;
R elsewhere is computed on the calling thread without publication. It drives the same step
functions (no second engine); its use disappears as callers become frame programs. Order is
bottom-up through it: a converted family is awaited by converted callers and called through
family_call by unconverted ones.

Remaining step-2 sub-steps, each a commit with tests green:
- 2d stepped interning: a record under construction is appended one word per step into pooled
  pages with an incremental hash; trie descent, full-key comparison and record copy advance a
  bounded number of words per step; the id is reserved before the copy, the leaf is published
  by CAS, a lost race re-descends and compares (the reserved id stays unused). No mutex held
  across steps.
- 2e sets and DNF: dim/var sets (make, union, remove, contains), interval and face operations
  (join, meet, negate, normalize with absorption, entails, forall, project, endpoint, substitute)
  as pure producers keyed by interned operands; each step reads/compares/appends O(1) words;
  clause positions are cursors in frame locals (no traversal to reach a field).
- 2f maps: mapb_finish (sort = stepped merge, duplicate/identity removal), lookup (binary search,
  one probe per step), compose, override, restriction.
- 2g substitution: reindex, construction instance building (environment, support, free
  variables, required face), environment maps, construction closure — producers over the above.

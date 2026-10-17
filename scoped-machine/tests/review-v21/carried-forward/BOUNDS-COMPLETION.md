# Exact representation contract and remaining integration

This document implements the user's rule: no arbitrary bound on an input, mathematical value, telescope, nesting depth, or represented structure before actual resource exhaustion. It supplements the V20 review and the bounds review. It does not change the mathematical calculus, the identity compiler, or the notion of sharing.

The supplied patch is an independently tested implementation of scope-vector growth, construction-face stacks, complete template signatures, full-width sparse table/page directories, and injective bound-atom coordinates. The arena's fixed total reservation, exact-number migration, and removal of dependence on a finite native call stack are **not implemented by that patch**. Their required integration is specified below. The earlier V20 progress/retry/fine-accounting/reclamation findings remain in force; this addendum does not sign them off.

## 1. Machine words, values, and addresses

Three categories must remain distinct.

1. An address/index into physically resident storage may use `size_t`, with checked arithmetic. The radix directory in the patch covers every `size_t` key. A fixed directory fanout, number of bits in an address, or finite primitive-rule arity is not an input cutoff.
2. A mathematical natural such as a universe level or finite cost must support an arbitrary finite limb sequence. A number much larger than a machine word can require only a few limbs. Its numeric magnitude does not justify resource failure.
3. A handle identifies a resident immutable object. A word-sized handle is valid when the record footprint means exhausting its available identifiers would already exhaust the native address space. Numeric coordinates must not be packed into that handle and thereby lose bits.

The patch changes bound atoms from packed `(depth,slot)` values to interned pairs and uses address-sized coordinates. It also widens `BinderSlot`, `FieldIndex`, shape/traversal depths, and net node identifiers. It does not turn a huge *coordinate* into a valid telescope: structural validation still requires an existing enclosing telescope and a declared slot of the correct sort.

## 2. Exact naturals: representation and API

Use one canonical representation for finite naturals. Keep the existing small-value fast path; represent larger values by immutable, interned, little-endian 64-bit limb vectors with no high zero limbs. Zero has zero limbs. Length is an address-sized physical vector length, not the value's magnitude.

A concrete word ABI is:

```
Nat: bit 63 clear => immediate value in [0, 2^63)
     bit 63 set   => handle to a canonical non-small limb record
```

Reserve `UINT64_MAX` for the existing explicitly typed sentinel use; do not admit it as a Nat handle. At least a record header and limb are needed for each boxed value, so available resident memory is exhausted before the remaining handle namespace. Never interpret the handle's numeric order as the value's order. Canonicalization ensures two handles denote the same natural iff they are equal in the same machine lifetime.

Provide these interfaces, with persistent implementations as specified in §3:

```
nat_from_word(uint64_t) -> Nat
nat_from_limbs(length, immutable_limbs) -> Nat
nat_compare(Nat, Nat) -> LESS | EQUAL | GREATER
nat_add(Nat, Nat) -> Nat
nat_sub_ge(Nat a, Nat b) -> Nat           // premise a >= b
nat_successor(Nat) -> Nat
nat_max(Nat, Nat) -> Nat
nat_export(Nat) -> canonical length and limbs
```

`nat_from_word` boxes values whose top bit is set. Callers must use it for external numeric words: directly casting such a word to `Nat` would turn a value into a handle. Small literals remain usable through the documented immediate constructor.

Costs are `Finite(Nat) | Infinity`. In the current word ABI `COST_INF` can remain the distinct reserved sentinel; it must never mean overflow or allocation failure. Addition has the existing absorbing-infinity rule. Order places infinity above every finite cost. Remove `COST_MAX` as a semantic ceiling.

Levels are naturals; absence is an option tag. Replace packed level pairs by an interned tuple of two optional levels. The opaque pair handle is stored where the packed word lived; every reader uses accessors. `mk_universe(n)` stores the exact natural `n`, formation produces `U_(n+1)`, and level equality is exact equality. A concrete large level does not require enumerating the smaller universes.

Signed cost differences are `Zero | Positive(Nat nonzero) | Negative(Nat nonzero)`. Their premises require finite costs; infinity is never coerced to an integer or used to form an undefined infinity-minus-infinity difference. `costdiff_epsilon` and `costdiff_masked` need exact accessors. A compatibility conversion to `int64_t` may explicitly return “not representable in requested host type”; it must not be the machine's stored result or silently alter it.

## 3. Persistent arithmetic frames

Arithmetic on a variable number of limbs must run through the existing shared operation protocol. Add arithmetic job families to that protocol; do not place a complete multiprecision operation inside one engine frame.

Keys are `(family, immutable operands)`. Arithmetic itself has no environment/session dependency. Repeated requests join one running job or reuse its completed answer. The output limb builder is owned by the job. Budget exhaustion preserves it, its cursor and its carry/borrow. Publication occurs only after canonical interning completes through the existing framed interner.

| Family/state | One transition | Retained next state |
|---|---|---|
| FROM_LIMBS/TRIM | Inspect one high limb; discard it logically if zero | Decremented high index, or known canonical length |
| FROM_LIMBS/COPY | Copy one retained limb | Next limb index and output builder |
| ADD/INIT | Read operand lengths, set `i=0`, `carry=0`, `used=0` | ADD/LIMB |
| ADD/LIMB | Read `a_i,b_i` (zero beyond their lengths), produce one sum limb | `i+1`, carry, highest nonzero output position |
| ADD/CARRY | Append the final nonzero carry if present | Complete canonical length |
| COMPARE/LENGTH | Compare canonical limb counts | Result, or highest common limb index |
| COMPARE/LIMB | Compare one pair of limbs from high to low | Result, or previous index |
| SUB_GE/LIMB | Read one pair of limbs, subtract with borrow, write one output limb | Next index, borrow, highest nonzero output position |
| INTERN | Join/request the existing framed canonical interner | Waiter continuation; no synchronous payload scan |
| RETURN | Publish the canonical Nat or comparison result once | READY |

For a limb addition without compiler-specific wide integers:

```
u  = a_i + b_i                 // unsigned word arithmetic
c1 = (u < a_i)
v  = u + carry
c2 = (v < u)
output_i = v
carry = c1 || c2
```

For subtraction:

```
u = b_i + borrow
c = (u < b_i)
output_i = a_i - u
borrow = c || (a_i < u)
```

The final borrow is zero under the `a >= b` premise. Recording the highest nonzero output position while producing limbs avoids an uncharged trailing-zero sweep. `successor` is ADD with one. `max` returns one operand after COMPARE. Signed difference requests COMPARE, then the correctly oriented SUB_GE, and retains the sign. Both zero and infinity require no limb allocation.

Every work-engine site currently using a C arithmetic/comparison expression on `Cost` must request these operations and resume from a saved program counter. In particular this includes SUM, residual family minima, proof SPLIT/FACTOR/DISJOINT/OR/WEAKEN, certificate comparisons, reduction/mapped-proof clauses, and geodesic edge inequalities. Replacing only `cost_add` is insufficient. C comparisons of *canonical handles for equality* remain valid; ordering uses COMPARE.

The checker and evaluator use the same exact level operations. Their synchronous public drivers drive these same retained operations to completion. Existing kernel lowering must allow suspension at their dependencies; a second, synchronous arithmetic implementation is unnecessary.

Proof of arithmetic correctness is the loop invariant

`sum of emitted limbs + carry * 2^(64*i) = sum of the two consumed prefixes`

for ADD, with the analogous borrow equation for SUB_GE. Canonicalization and exact interning preserve the value and its identity. Each limb transition uses a bounded number of word instructions. Increasing precision increases the number of transitions, never the domain of a transition.

## 4. Serialization, keys, and annotations

Interning inside one machine may key records by canonical Nat handles. Cross-machine export/comparison must export their normalized limbs, with the finite/infinity/absent/sign tags. Never print or compare boxed handle numbers as though they were mathematical values.

Migrate every occurrence of levels: universe payloads, paired formation annotations, template level parameters, scope signatures, diagram/transform record annotations, exported graph labels, and compiler certificates. Read stored annotations through their accessors; no `>>32`, masks, or narrowing casts remain as a numeric interpretation.

Migrate every occurrence of costs: model weights/overrides, accumulated work costs, lower and upper certificates, geodesic potentials, signed differences and diagnostic output. Values crossing the former thresholds must preserve sharing and check against the same exact expectations as small values.

Native `size_t` arithmetic for allocating limb storage is checked before addition/multiplication. Overflow there describes an unaddressable physical allocation; overflow of an individual arithmetic limb is carried to another limb.

## 5. Extensible arena: allocation state machine

Keep the existing ownership and retirement rules. Replace the fixed total reservation and the fixed fresh half with a collection of allocator-owned extents. Any initial extent size is a growth policy, not a capacity limit. Maintain an exact index of owned extents for `kalloc` ownership tests: checking only `arena_base <= p < arena_base + ARENA_WORDS` is no longer valid.

Use page-sized allocation units. A block descriptor is `(extent, page_offset, order, state)`. Buddy offsets are relative to that extent, so the extent's starting virtual address need only satisfy page alignment. Use native-address-derived orders rather than the constant 23. A block's state is exactly one of OWNED, DIRTY_FREE, CLEARING, ZERO_READY, or MERGED. The descriptor itself remains owned until its block is installed in a free structure or released to the host.

| Allocation phase | Action | Rule |
|---|---|---|
| LOOKUP | Inspect the requested order's reusable blocks | Available nonzero blocks can satisfy ordinary allocation; zero requests require ZERO_READY |
| SPLIT | Split one larger reusable block into two buddies | Retain one, publish the other; repeat in later units |
| CLEAR | Clear at most `CHUNK_WORDS` of the selected dirty block | Cursor is retained; no other requester can use a partially cleared block |
| CLAIM | Install the completed block for this requester | Exactly one owner; publish after initialization |
| EXTEND | Request additional address space when reusable blocks cannot satisfy the demand | Actual host allocation outcome, never a fixed reservation ceiling |
| WAIT_RESOURCE | Retain the request and completed work if supply is unavailable | Does not imply invalid mathematics, inequality, infinity, or a permanent failed judgment |

The allocator must reclaim dead fresh blocks. DIRTY_FREE is reusable storage, not a permanent graveyard. Ordinary allocations may consume it directly; zero allocations clear it in bounded chunks. Retiring an already-owned block never cancels live work. Coalescing free buddies performs one merge per transition; it never merges across extent ownership boundaries.

Extent metadata and directory publication also belong to counted, retained work. On growth, live object addresses remain stable. A block requiring contiguous storage must obtain a sufficiently large addressable extent; segmented representations already used by the engine continue to allocate fixed pages.

An operating-system allocation is a host resource action, not an asserted constant-time theorem about the operating system. Keep that action explicit in the host/resource model and account for all variable work performed by the runtime itself. A fixed per-step C bound must never conceal a variable-size clear, copy, scan, allocation fallback, or lock-held completion loop.

`malloc/calloc/realloc`-style kernel callers that can need a pending allocation must prepare it before taking the publication lock, then lock, revalidate and publish. Losing a publication race releases the private candidate through the same ownership protocol. Do not wait for a shared allocator job while retaining an unrelated machine lock.

## 6. Native stack and construction state

The patch removes the explicitly imposed 16-deep construction-face stack. A pthread stack retained as a kernel continuation still has a host-configured capacity. It must not become a hidden maximum mathematical nesting depth.

The portable completion is the same defunctionalization already used by the engine: recursive kernel calls become explicit frames containing `(operation, immutable operands, local cursor/state, return continuation)`. A call pushes a child request and stores the parent's return program counter. Returning delivers the child result to that continuation. Iterate the dispatcher instead of recursively calling C.

Apply this to recursive components reached by arbitrary input structure, including scoped traversal/validation, shape construction, template interpretation, checking/conversion, and recursive diagram construction. Preserve the existing operation keys, required faces, running-state/cycle handling, and checked outcomes. Do not turn recursive definitions into unbounded *eager* unfolding while doing this lowering.

For scope validation, the telescope stack is a persistent linked stack of scope handles. A validation frame retains the exact stack handle and the local declaration-prefix cursor. Its memo key remains `(record, exact telescope stack)`. Changing the storage of the stack does not justify reusing a validity result under a different telescope or outside its binder.

This is a control-flow translation: every call/return in the existing algorithm corresponds to a frame request/delivery. It adds no inference rule or search strategy. Frame allocation can suspend through §5. Increase in nesting consumes more resident frames, ending only at an actual resource condition.

## 7. Integration order and completion gates

1. Apply the tested patch or port its changes onto the worker's current tree. It targets `c365d86`; do not overwrite newer corrections. The directory change subsumes the old `chunked_free` ownership fix from the earlier V20 patch.
2. Complete extent ownership/reuse and allocator request continuations with the already required V20 lock/progress corrections. Keep the sparse directory implementation or an equivalent full-address-domain structure.
3. Add exact Nat storage and shared arithmetic frames; migrate levels, costs, signed differences and export together. Remove obsolete tests that assert that a large *mathematical value* is a host failure, replacing them with exact-value tests.
4. Finish kernel frame lowering, including allocation dependencies and native-stack independence. Keep attempt-local UNRESOLVED handling and independence of unrelated demands from the earlier V20 review.
5. Run the following acceptance cases and the existing semantic/concurrency gates. Report actual results, not a claim based solely on source shape.

Required acceptance:

- All scope-agent forms agree with the host operation at arities 0, 1, 16, 17, 63, 64, 65 and 129, including mixed dependent locals, partial guards, and empty telescopes.
- A complete signature is checked even when it would exceed a former temporary buffer. A final invalid obligation is rejected, rather than omitted.
- Sparse indices past 2^26 and across several radix boundaries preserve old addresses and values. The full-width directory test reaches `SIZE_MAX` without allocating intervening payloads.
- Tiny test extents cross several allocator growth boundaries; old references stay valid, dirty blocks are reused after bounded clearing, and a repeated allocate/retire workload reaches a stable owned-storage footprint. No result depends on the chosen initial extent size.
- Level `2^32+1`, costs beyond `2^62` and `2^64`, a multi-limb carry chain, and a negative difference beyond `int64_t` remain exact through storage, operations and export. One-step budgets advance at most one declared arithmetic transition, including canonical interning rather than an uncharged completion scan.
- More than 16 required-face scopes preserve push/pop semantics. Deep structural terms run with a deliberately small native thread stack using the explicit-frame driver, so the test demonstrates independence from native stack depth.
- Same-key clients join a pending growth/arithmetic request. An unrelated finite request progresses while another request is suspended. Retrying after resource/budget suspension preserves completed shared work and does not cache a false mathematical verdict.

Completion means these interfaces are implemented and gated. The supplied source patch is a verified increment toward that condition, not a claim that the unchanged arena, packed numerics, or pthread-stack kernel already satisfy it.

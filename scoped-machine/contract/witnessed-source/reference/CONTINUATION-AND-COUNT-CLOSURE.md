# Concrete closure of continuation, allocator-index and count obligations

These are implementation instructions for V23 R3–R5 within the existing machine, not requests for a new subsystem or for authorization. The semantics, shared operation keys and typing rules stay the same.

## A. Continuation destruction without evaluating a program

The distinction is ownership, not elapsed steps. A continuation may be destroyed when the closed-session condition has removed all live clients/externally retained obligations, or when a private unreachable frame is retired. A still-owned live computation remains pending. Teardown is not a mathematical result and must not publish `INVALID`, `UNEQUAL` or a fabricated successful value.

Each suspended operation must expose its retained state rather than hide required cleanup solely in native stack locals. Use the already specified explicit frame record:

```
Frame = (operation, program_counter, immutable operands,
         owned temporaries, awaited child/ticket, return continuation,
         dependency snapshot, accounting owner, cleanup cursor)
```

For each frame kind, give its fixed table of owned fields and the cleanup recipe. Ownership of variable vectors/paged storage is represented by their existing retirement handles. A field is initialized before the frame's program counter makes its ownership visible; transferred fields are cleared when ownership moves. A failed or cancelled frame releases only fields it still owns.

`DROP_FRAME` performs one owned-field release or one page/registration cleanup step, advances its cleanup cursor, then pops the frame when complete. `DROP_JOB` iterates this over its retained stack without executing the semantic bodies. Shared child jobs are unreferenced, not destroyed while other owners remain. A cancelled wait registration is detached or marked unclaimable under its predicate lock; late deliveries consume their own ticket ownership and cannot resume a retired continuation. Snapshot refs and reuse scopes are released exactly once. No scope can be freed while an actual task still uses it.

Normal frames use the same dispatcher: CALL stores the return program counter and requests/pushes a child; RETURN installs its result and advances the parent. Wait cycles remain pending states of that graph. They do not prevent destroying the graph at a closed boundary. Actual task worker threads run the dispatcher and return to a bounded pool; the number of pending mathematical continuations does not require one native thread per continuation.

A stackful transitional implementation must supply an equivalent cleanup registry and an explicit lock-free cancellation return path through its owned stack segments. `pthread_detach`, `pthread_cancel` without cleanup coverage, `longjmp` past owned locals, and unmapping a stack still used by a thread are not equivalent. The current source has no such complete cleanup registry, so explicit frames are the direct completion of the existing requirement.

Allocation failure while constructing a future frame is a resource outcome at the allocator boundary. The current retained frame and already published facts survive. The destructor needs pre-existing ownership metadata; it must not allocate an input-sized scratch copy just to discover what it owns. Releasing fixed pages and visiting cleanup fields remain counted transitions. Actual OS thread/stack acquisition/release is an explicit host action.

Acceptance cases: finite call beyond the former `2^20` allowance; a genuinely waiting cycle; both producer/waiter allocation orders; obsolete tickets; a nested segmented call if that implementation remains; a failed preparation owning temporaries; repeated closed init/free cycles with zero retained native workers and stable reusable storage. The existing `cleanup-long` wrapper checks the native-worker part directly.

## B. Bounded ownership index for an extensible allocator

Keep the extent list if useful for diagnostics. Add an address-radix membership index whose lookup is bounded by the backend's actual pointer width, independent of extent count. This is an architectural bound on an address representation, not a bound on interval variables or a mathematical input.

One exact construction uses dyadic interval prefixes of native `uintptr_t` addresses. For each new extent `[b,e)`, decompose it into aligned power-of-two blocks; the standard decomposition has at most twice the address width many prefixes. Insert those prefixes into a binary address trie. A node either marks a wholly owned prefix or has children for its next address bit. Lookup follows at most one child per address bit and succeeds upon an owned-prefix marker. A foreign address fails at a missing child. A marker never denotes an address outside an allocated extent.

Use a private persistent path-copy or equivalent publication protocol. All new nodes and their initialization are prepared before the new root is published. A failed extension cannot leave owned markers for a mapping already released to the host. Existing immutable nodes/roots stay valid for readers; publish the root with release and read with acquire. The arena lifetime presently retains extents, so there is no concurrent extent removal case. If extent release is added, retire roots/nodes only after readers no longer retain them.

The number of pointer/bit operations in a lookup is bounded by the actual address width. Prefix decomposition and path preparation are either retained bounded steps or charged at the declared extent-acquisition boundary; they are not hidden in `arena_owns`. Index-node allocation must not recurse into the index that is currently being initialized. Supply fixed-size bootstrap metadata pages/records through the existing allocator's explicit resource path.

Tests should use tiny extents and query the first, middle and last extents, holes, one-past-end and foreign pointers. Assert membership and a lookup-node bound derived from the native address width, while increasing the number of extents. Preserve existing clearing/reuse/interleaving tests. Do not assert a runtime bound from a timing measurement.

## C. Exact work readings without recursive instrumentation

An authoritative count is an exact natural, not a word with silent modular arithmetic. This does not require running the general Nat kernel inside every `fine_bump`.

A simple exact lazy representation is a word-sized low digit plus a persistent sequence of carry blocks:

\[
\operatorname{value}(l,B)=l+2^w\,\operatorname{length}(B),\quad 0\le l<2^w.
\]

An increment that does not overflow changes l. An overflow installs one preowned fixed-size carry node and resets l. There is no carry propagation through the length of B: its length remains represented structurally until an exact reading is demanded. Adding a word-sized amount creates at most one new carry block. Larger bulk additions use their retained arithmetic job. Another bounded-update exact representation is permitted if it supplies the same value/update/extraction proof.

Publish the low digit and carry-prefix identity consistently. Single-writer shards with immutable published snapshots are appropriate for actual worker threads; a shared counter requires a bounded critical update and a linearized snapshot. Reserve any needed carry storage before entering a non-yielding section. With bounded critical sections, the maximum emergency carry records needed for that section is derived from its maximum increments, not an arbitrary mathematical-count ceiling. Failure to acquire further storage is the ordinary resource condition. Never reset a high part or silently stop counting.

An exact snapshot retains `(low, carry-prefix)` for each relevant shard and its owner/phase. Extraction folds the immutable carry prefixes and sums shard values through the existing shared exact-Nat jobs. A second request joins/reuses this extraction. A delta is exact subtraction between retained snapshots, not unsigned word subtraction. Closing an accounting scope transfers its retained contribution once; late events retain their precise owner and extend the owner's late contribution once. No global before/after attribution is reintroduced.

This representation makes the update identity elementary: ordinary increment adds one; wrap replaces `2^w−1` by zero and adds one carry block of value `2^w`, also adding one. Induction proves the reading for arbitrary finite event counts. Shared-history union remains the event-identity operation; a numeric sum must not duplicate an event merely because two views reference it.

Accounting maintenance is included in the bounded implementation of a charged transition, rather than recursively producing an infinite sequence of “account for accounting” events. Its fixed-size per-event update establishes the forward C-bound factor. When a requested observation normalizes/serializes a large exact count, that variable work has its own finite later trace and does not change the earlier captured snapshot. This avoids self-reference while retaining actual costs.

Migrate semantic consumers of `FineVector`, `WorkLedger`, reuse scopes, producer/continuation accumulated steps and event counts to exact readings. Native `size_t` is still correct for an addressable buffer length or a caller's one-grant budget. A diagnostic `*_low64` projection may remain if clearly typed/named as a residue; a checked `to_u64` conversion returns out-of-range rather than inventing a small exact answer. Do not store boxed Nat handles in old arithmetic fields and continue using C `+`, `<` or formatting on them.

Acceptance: seed a valid exact counter just below `2^64`, take one real counted event, and obtain exact `2^64`; word conversion reports out-of-range. Repeat across a closed scope with late contributions, mixed-owner interleaving and concurrent snapshot/updates. Check that each carry/update frame respects the bounded-work inventory. Existing small-counter equalities should still hold after checked conversion.

## D. Remaining lock-held work

Continue the already disclosed lowering: engine synchronous drivers must drive the same retained jobs without enclosing the entire run in `W.mu`; variable-size compiler/demand vectors grow through prepared paged storage or framed relocation; an outer lock cannot make an interner's variable probe chain non-yielding. Prepare, pin, unlock, perform framed work, relock, revalidate and publish. A race loser releases its private candidate through the same ownership rules. The tests should drive colliding keys and growth boundaries, not only average cases.

These requirements are the concrete connection between the desired elementary transition count and C work. Exact numerics, more stack space, or additional counter ticks alone do not discharge them.

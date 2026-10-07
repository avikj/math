# The hyperactive machine: write-once dataflow over an address tree

This is the ground-up derivation of the step relation, with its one-step
diamond (hence min-steps / geodesic by the essay's §5 `RandomDescent`).
Reviewable as mathematics; the Agda mechanization is gated on the pinned
checker and tracks this note theorem-for-theorem.

## State

One table, not two. Each address holds one of three statuses:

```
Status  =  empty  |  pending Cell  |  done Out
slot    :  Addr → Status
St      =  (env : Env) × (slot : Addr → Status)
```

`env` is immutable (reads are free and shared — the contractible-slot
law, made architectural). Addresses are the list-tree of ListAddr.agda:
a root judgment at `[i]`, the k-th child of α at `k ∷ α`. A `done` slot
keeps its verdict forever: the sub-tree of `done` slots **is** the
completed derivation, laid out as geometry — bytecode = the complex
itself, falling out rather than imposed.

A cell declares the addresses whose verdicts it reads:

```
deps : Cell → List Addr
rule : Env → Cell → (∀ γ ∈ deps c, Out) → Out × List Cell
```

`rule` sees `env`, the cell, and the (already-resolved) verdicts of its
dependencies; it returns this cell's verdict and the children to spawn.
(The non-aggregating machine of Diamond.agda is the special case
`deps c = []`.)

## Step

An **active** site is an occupied, unblocked slot:

```
Active s  =  Σ (α , c).  slot s α ≡ pending c
                       × (∀ γ ∈ deps c.  Σ v. slot s γ ≡ done v)
```

Firing at α with resolved deps `ds`:

```
fire s a  =  s with  slot α             := done (verdict)
                     slot (child k α)   := pending (childₖ)   for each k
```

where `(verdict, children) = rule env c ds`. The write touches exactly
`α` and its immediate children; it reads only `env` and the `done` slots
named by `deps c`.

## Invariant

**I (prefix-free occupancy):** if `slot α` is not `empty`, every proper
extension of `α` is `empty`.

Holds initially (roots `[i]` pairwise non-extending). Preserved by a
fire at α:

- α: `pending → done` — still non-empty, and its proper extensions were
  empty before and are untouched except the children.
- child `k ∷ α`: `empty → pending`. Before the fire it was empty: it is a
  proper extension of the occupied α, so empty by I. Its own proper
  extensions are proper extensions of α (transitivity of ext), hence
  empty by I and untouched. ∎

Consequence used below: a `pending` slot is never `done`, because a slot
has exactly one status. No separate write-once lemma is needed — `done`
is terminal (fire acts only on `pending` α and `empty` children), so a
verdict, once written, never changes.

## One-step diamond

Two active steps at `α ≠ β`.

**Write/write disjointness.** Fire-a writes `{α} ∪ {k∷α}`; fire-b writes
`{β} ∪ {l∷β}`. The four coincidences are all impossible:
`α=β` excluded; `α = l∷β` ⟹ α extends β, both occupied, contradicts I;
`k∷α = β` symmetric; `k∷α = l∷β` ⟹ (child-inj) `α=β`, excluded. So the
two write-sets are disjoint, and the pending/slot updates commute
(pointwise `update-comm` on disjoint addresses).

**Read/write non-interference — the part aggregation needed.** Fire-a
reads only `done` slots (its resolved deps), present at `s`. Does fire-b
*write* any slot fire-a reads? Fire-b writes `out`-status only at `β`
(and spawns `pending` at children, never `done`). Suppose `β ∈ deps cₐ`.
Then `slot s β = done _` (a's dep is resolved). But `β` is b's site, so
`slot s β = pending c_b`. A slot is not both — contradiction. So
`β ∉ deps cₐ`, fire-b changes no slot fire-a reads, and symmetrically.
Therefore each step leaves the other available, with the same cell, the
same resolved deps, and the same verdict; the two double-fires reach one
state. ∎

This is the Kahn-network / monotone-dataflow determinacy argument, and it
is exactly what the single `Status` table buys: a dependency is a read of
a *terminal* `done` slot, so an available step's reads can never be
racing an unfinished write — if the awaited slot were still pending, the
reader would not be available. Dependencies sequence the work; they do
**not** threaten the diamond, because the diamond only quantifies over
steps available *now*, and two now-available steps are independent.

## Consequences (inherited, not re-proved)

Instantiating the essay's `RandomDescent (St-with-I) Step diamond`:

- **equal length** — all complete reductions to a normal form have one
  length;
- **geodesic** — that length is the minimum; no schedule is shorter;
- so the **runtime may pick any schedule** (demand-driven, sequential,
  parallel) and is step-optimal by construction — it never has to be
  clever about order. This is the whole point: min-steps inference is a
  property of the step relation, discharged once, for every program.

Normal form = no active site = every slot `empty` or `done`: the
derivation tree is complete, every demanded judgment resolved.

## Cost (the two axes, essay §5.3)

- **length** = number of fires (the geodesic count above).
- **effect-cost** = per fire, `0` if `rule`'s verdict map is injective
  given the cell (reversible), `k` for a `2ᵏ`-fold merge — charged on the
  residue of `rule`, nothing else (essay Prop 5.8). The `done` tree
  retains every input distinction except what a merging `rule` explicitly
  drops, and that drop is where — and the only where — Landauer cost is
  paid.

## What this supersedes

`Diamond.agda`'s two-table (pending, out) machine is the `deps = []`
restriction and remains valid as that special case. The Status-table
machine is the general one and is what the cubical cell kinds instantiate
(each kind supplies `deps`, `rule`; the diamond is already proved for
all of them). `Spawn.agda`'s address axioms and `ListAddr.agda` carry
over unchanged.

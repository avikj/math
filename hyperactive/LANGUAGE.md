# The cell language and rule table (core fragment)

Every cell kind is one `(deps, rule)` entry for the Status-table machine
of `MACHINE.md`. The diamond — hence min-steps — is already proved for
*any* `(deps, rule)`, so adding a cell kind adds no proof obligation
beyond stating it; that is the payoff of the generic theorem.

Notation: a cell at address α with `slot α = pending c`. `rule` sees
`env`, `c`, and the verdicts at `deps c` (all `done` when the cell is
active). It returns `(verdict, children)`; children are spawned at
`0∷α, 1∷α, …`. `env` is the immutable shared pool of value terms;
operands are pool indices.

## 1. Values and neutrals

A **value** is a cell whose verdict is itself — no work, no children:

```
Con t [f₁ … fₐ]     data constructor, tag t, field addresses fᵢ
Neu  x              a neutral: an unknown (a fresh symbol), verdict = itself
Lam  ⟨body, frame⟩  a closure
Univ, Pi, Sig, …    type formers, also values (types are data)
```

`deps = []`, `rule env c _ = (c , [])`. A value is already `done` the
moment it is observed. Neutrals are first-class: an open term is an
ordinary state, so "checking" needs no second machine (the wall that
forced the external checker is gone — there is no linear read to pay and
no missing-agent gap, because `Neu` is a verdict like any other).

## 2. Application / elimination (the one-sided wall, dissolved)

```
App f a        deps = [f]        -- read the function's verdict
rule env (App f a) [vf] =
  case vf of
    Lam ⟨body, frame⟩ → (Redex, [ instantiate body frame a ])   -- β: spawn the body
    Neu _             → (Stuck (App f a) , [])                   -- neutral spine, a value
    _                 → (TypeError , [])
```

`App` reads only its function slot. No agent has a "mouth"; reading is a
declared dep, not a consumption, so there is no one-sided ordering: an
eliminator that needs several operands lists them all in `deps` and the
`rule` sees them together. The `Ubhayatah` trapped-cost of one-sided
inspection does not arise — `deps` is a set, not a sequence.

## 3. Equality judgments — native checking with aggregation

This is the cell nets could not host. `Eql i j` asks whether the pool
values at `i` and `j` are equal; it reads **both** (`deps = [i, j]`),
decomposes on their heads, spawns child judgments, and aggregates.

```
deps (Eql i j) = [i, j]
rule env (Eql i j) [vi, vj] =
  case (vi, vj) of
    (Con t  fs , Con t' gs) →
        if t ≠ t' or |fs| ≠ |gs|
          then (Done False , [])                      -- mismatch: immediate, from EITHER head
          else (Agg And len , [ Eql fₖ gₖ | k ])      -- spawn child Eql per field, verdict aggregates
    (Neu x , Neu y) → (Done (decide (x ≡ y)) , [])    -- two neutrals: equal iff same symbol
    (Lam _ , Lam _) → (Eta i j , [ Eql (appFresh i) (appFresh j) ])
                                                       -- under a binder: apply both to one FRESH
                                                       -- neutral, compare outputs (η / funext)
    _               → (Done False , [])
```

Two remarks make this the whole point of the design:

- **Mismatch answers from either side.** `t ≠ t'` is read off the pair of
  heads at once — no commitment to inspect `i` before `j`. This is the
  two-sidedness the net format structurally lacked.
- **Under a binder, neutrals do the work.** `Lam` vs `Lam` spawns one
  child comparing the bodies applied to a *fresh* `Neu` — open-term
  comparison is an ordinary state, no external checker, no second rule
  table. `λx.x+0 ≡ λx.x` runs here: apply both to `Neu x₀`, the left
  reduces `x₀+0 → x₀` (ordinary fires), the right is `x₀`, child `Eql`
  sees `Neu x₀` vs `Neu x₀`, `Done True`; parent aggregates `True`.

**Aggregation** (`Agg And n`, `Eta`) is a cell that reads its own n
children's verdicts and combines:

```
deps (Agg And n at α) = [ 0∷α, 1∷α, …, (n−1)∷α ]     -- its children's done slots
rule env (Agg And n) vs = (Done (all isTrue vs) , [])
```

Because children's addresses are deterministic (`k∷α`), the parent names
them exactly; it becomes active only when all are `done` (its deps), and
by the dataflow diamond this waiting never threatens min-steps — the
parent simply is not an active site until its children resolve.

## 4. A declaration is the program (no body)

A top-level `name : A = ?` with the body omitted is a **goal cell** whose
type is `A`. For a Σ-goal `Σ B. P A B` the mechanism is:

```
Goal (Σ B. P)   deps = []
rule env (Goal (Σ B. P)) _ =
  (Done ⟨witness⟩ , [ check-cell ])
```

where the witness is produced by the type's own resolution — for a
*contractible* specification (the sort spec at a fixed input is
contractible: its centre is `(isort A , refl , sortedPf)` via the
carrier equivalence) the witness is forced, inferred not guessed, and the
spawned `check-cell` is the `Eql`/`Path` judgment certifying it, resolved
by §3. Empty fibre ⟹ the check-cell is `Done False` (no inhabitant);
crowded fibre ⟹ the goal is a superposition cell (§5). There is no
separate checker pass: the goal's verdict and its certificate are cells
on the one machine, which is exactly "verify = decide".

`sort : Π A. Σ B. (multiset A ≡ multiset B) × Sorted B` with no body
resolves `B` at each `A` by this rule, at the step-count the object fixes
(§MACHINE geodesic), and `sortCost : Π n. Nat` resolves on the same
machine by reading the `length` of the resolution's trace (the `done`
sub-tree) — collapse as a value, §5.

## 5. Choice coordinates (superposition) — collapse as a value

A `Sup L a b` cell is a value lying along a choice coordinate `L`; its two
faces are `a` and `b`. Reading a face is `∂_L^ε` (MACHINE address face,
free on coordinates the cell doesn't mention — degeneracy = sharing). A
specification applied to a `Sup` of candidates spawns the judgment over
each face; survivors are the fibre; `Collapse` is a cell whose verdict is
the list of vertices (faces folded, multiplicity conserved — never
merged), on which computation continues. `&{}` is the empty fibre
(`Done False`). This is the one paid coordinate-crossing (the non-
contractible residue); everything else is routing, charged zero by the
dichotomy.

## 6. Cubical cells (extension, same pattern)

Each is a `(deps, rule)` entry; the diamond is inherited. Stated here,
mechanized after the core is green:

- `Path A x y`, `PathP`, interval `I0 I1 ∧ ∨ ~` (value cells / faces).
- `coe L r s x` — `deps = [L]`; `rule` dispatches on the type-former
  verdict of `L`: Π conjugates, Σ componentwise, Path via the hcomp
  square, `Ua` gives f forward / g backward (uaβ), Glue its program, a
  HIT pushes into its constructor.
- `hcomp A φ u base` — returns a true face's top; base when all faces
  false; else dispatches on the type, or is the stuck value `#HCm` when
  the interval is a neutral (a stuck composite is a value — higher
  structure, nothing erased).
- `Glue`, `glue`, `unglue`, `ua` (from Glue; uaβ definitional).
- HIT cells via the general schema: point and path constructors, `hrec`/
  `helim`, `coe` through parametric HITs.

Every one of these reads its declared deps and consumes only its own
site; none reintroduces a second evaluator, a one-sided operator, or an
erased read. The machine is one reduction; checking, running, and
specialization are the same fires with different amounts of `Neu` in the
pool.

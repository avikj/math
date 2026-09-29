# State / Event — Time / Information

Pratt's Chu program makes state and event mutually dual coordinates of one heterogeneous interaction. His quantum work reads the same duality as information/time complementarity rather than treating time as an external parameter added after state semantics.

The project's causal carrier makes this dual reading exact. Let `x ≡ₙ y` mean agreement through observational depth `n`. A single crossing satisfies `x ≡ₙ₊₁ y ⇒ σx ≡ₙ σy`; a word `w` satisfies `x ≡ₙ₊|w| y ⇒ w(x) ≡ₙ w(y)`. Read dynamically, `|w|` is elapsed interaction depth / causal radius. Read observationally, it is the amount of source information required to determine the requested output depth. The same modulus is time in one orientation and information demand in the dual orientation.

The carrier also has a globally readable conserved charge `Q : R → Z/4` while no bounded local observer can determine it: for every finite depth there are locally indistinguishable states with different global charge. This is a concrete state/event and local/global information separation rather than an analogy about complementarity.

Action residual phase gives a second exact observation theorem. For observation `q`, action `step`, predictor `P`, and additive residual `δ(x)=q(step x)-P(qx)`, a character `χ` sends residual to relative phase. Equality under the phase observation is exactly membership of the difference in the character kernel. The checked hostile example has injective classical residual `δ(x)=2x` while every sign character sends the entire residual to the identity phase. Thus a faithful distinction at one level can be completely invisible under another observation.

This is precisely why [the Fibre Law](02-fibre-law.md) matters for measurement: a visible result never licenses discarding the distinctions in its fibre unless the desired downstream result descends through that observation.

The four-phase algebra, quarter-turn, global charge, and exhausted cellwise centralizer connect this page to Pratt's `Chu₄` program, but the exact algebraic identification must be proved at the level of his evaluation algebra, not inferred from cardinality. The physical carrier is developed in [Interaction Geometry Becomes Physics](09-interaction-geometry-physics.md).

## Canonical checked construction

Residual/phase: [`ActionResidualPhase.agda`](../../formal/cubical/theorems/residue/ActionResidualPhase.agda). Causal/geodesic and Z/4 theorem ledger: [`PNP_GEODESIC_REDUCTION_20260916.md`](../../research/PNP_GEODESIC_REDUCTION_20260916.md). Chu-facing bridge: [`ChuDefect.agda`](../../formal/cubical/theorems/order/ChuDefect.agda).

## External coordinates

[Chu spaces](https://ncatlab.org/nlab/show/Chu+space), [character theory](https://en.wikipedia.org/wiki/Character_theory), [quantum logic](https://plato.stanford.edu/entries/qt-quantlog/).

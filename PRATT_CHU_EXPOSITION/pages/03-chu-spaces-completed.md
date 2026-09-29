# Chu Spaces Completed

A Chu space starts from heterogeneous interaction `(A,X,e)` with `e : A × X → K`; currying gives the mutually dual state/observation presentations `A → K^X` and `X → K^A`. Pratt used this small geometry to connect automata/schedules, state/event duality, concurrency, linear logic, universal mathematics, and quantum semantics.

Apply [the Fibre Law](02-fibre-law.md) directly to `e`. The complete conservative interaction is `A × X ≃ Σ k : K , fib e k`, and the type of conservative completions over `e` is contractible. Classical Chu retains the visible matrix entry; the lossless completion retains exactly the source distinctions identified by that entry. This is the first completion, and it is forced.

A Chu transform `(g,h)` satisfies the adjointness equation `e_A(a,h y)=e_B(g a,y)`. At the dependent level that equality transports the complete family above the equal visible values. When the structured interaction spaces themselves are equivalent, univalence turns that equivalence into identity in the universe, so every dependent construction transports. Chu's contravariant observation map and covariant state map become boundaries of executable dependent transport rather than merely an extensional commuting equation.

Pratt's Rational Mechanics begins from the same heterogeneous interaction and derives homogeneous state transition and event precedence by residuation. The fibre law supplies a complementary rigidity statement: once a visible interaction map is fixed, its conservative residual coordinate is forced.

The fixed value object `K` is itself a restriction. A universe-valued interaction `R : A × X → U` assigns a complete interaction type to every state/observation pair. Its total space is classified by the universal family `π : Σ T : U , T → U`; finite dependent towers flatten to one family. This is the direct bridge from Pratt's Stone-gamut/universal-mathematics program to the classifier in [Lossless Interdependent Interaction](01-lossless-interdependent-interaction.md).

Pratt's `Chu₂ → Chu₃ → Chu₄` program should be read together with [Concurrency Is Geometry](04-concurrency-is-geometry.md) and the four-phase carrier in [State/Event — Time/Information](06-state-event-time-information.md).

## Canonical checked construction

Chu-facing checked sources: [`ChuAdvance.agda`](../../formal/cubical/theorems/residue/ChuAdvance.agda), [`ChuDefect.agda`](../../formal/cubical/theorems/order/ChuDefect.agda), [`ObsBridge.agda`](../../formal/cubical/theorems/logic/ObsBridge.agda). Forced completion is supplied by [`Trace...agda`](../../fibre/src/Fibre/Trace_TheTraceFamilyIsForcedToBeTheFibreAndTheCarrierIsItsContractibleCase.agda) and [`Ekatva...agda`](../../formal/cubical/theorems/residue/Ekatva_LosslessnessIsAPropertyTheCompletionsOfAMapFormAContractibleTypeAndTheMachinesIsUnique.agda).

## External coordinates

[Vaughan Pratt, Chu spaces](https://ncatlab.org/nlab/show/Chu+space), [Chu spaces as a semantic bridge between linear logic and mathematics](https://doi.org/10.1016/S0304-3975(01)00169-4).

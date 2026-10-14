# net: CCHM on an optimal interaction net

- `net.c`: the fixed step. It contains:
  - the Asperti–Guerrini interaction system, transcribed rule by rule
    (sources in the file header): levelled λ, @, fans, brackets,
    croissants and erasers;
  - data: a constructor and a case agent, which are a datatype's Scott
    construction with its binders already met (one case interaction is n
    β-steps);
  - neutral application and neutral case;
  - read-back.
- `cubical.lam`: the cubical layer as definitions, following MACHINE_SPEC
  §§4–25:
  - the De Morgan interval and faces;
  - partial elements;
  - type codes;
  - comp, with the face first and then the head table: Π, Σ, PathP, Glue
    (all six stages), U, a system head, and a type's own Kan structure;
  - fill, hcomp, coe, coeRS, idEquiv, lineEquiv, extendEquiv, glue,
    unglue and ua;
  - path operations;
  - the identity agent's forward and backward bodies (NET_SPEC §1),
    wire elimination (§2), handles (§3), cut and difference (§5).
- `examples/`: one term each, with no numbers. `discrete.lam` declares a
  two-point type with its Kan structure.

Run: `net cubical.lam [examples/discrete.lam] examples/<name>.lam`. It
prints the normal form, then its length in interactions; read-back's own
interactions are counted apart.

How the cubical layer stands on the net, without new agents:

- **A dimension binder is a binder.** A line is `\i. A`, and substituting
  an interval is β.
- **comp reads the head of `A(i)` at a generic point `gen`.** No face holds
  there, and a face read there is ∀i of it. Each component is then the
  line `\i. component (A i)`.
- **Re-reading the components at each point is exact, under one
  condition.** It is the same as reading them generically and then
  substituting, provided no type code collapses at a face. So the Glue
  code, and comp in U, stay codes at a full face. Their elements still
  collapse, through `glue` and `unglue`.
- **This is the one difference from MACHINE_SPEC §16.** There,
  `Glue [1 ↦ (T,e)] A → T`. Here that type prints as its code, and
  everything built from it computes as T.

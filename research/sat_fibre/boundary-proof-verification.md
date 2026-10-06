# Boundary and representative proof receipt

Checked with Agda 2.8.0.1 and the installed Cubical v0.9 library during the
2026-09-16/17 session. Both final checks exited 0. Both modules use `--safe`
and contain no postulates or unsolved holes. The first check rebuilt library
interfaces and emitted existing library `UnsupportedIndexedMatch` warnings;
the final representative check contains only its checking line.

```sh
/opt/homebrew/bin/agda --safe --cubical --guardedness --no-import-sorts -WnoUnsupportedIndexedMatch --no-libraries -i research/sat_fibre -i formal/cubical/theorems/physics -i /Users/avikjain/.cache/cubical-v0.9 research/sat_fibre/SATBoundary.agda

/opt/homebrew/bin/agda --safe --cubical --guardedness --no-import-sorts -WnoUnsupportedIndexedMatch --no-libraries -i research/sat_fibre -i /Users/avikjain/.cache/cubical-v0.9 research/sat_fibre/RepresentativeContinuation.agda
```

SHA-256 of the checked sources:

```text
e3fe95de4c19c6c00d07ef3cc71c9e16280d922c5456eea01940619ea7171f14  SATBoundary.agda
56be086cc31bd3db0f9dae0912bfd1d4f5a5398801dc173d54eeec09e10dff19  RepresentativeContinuation.agda
```

The first check's successful exit is recorded in the tool transcript.
The final second check's output is retained in
[representative-agda-check.log](representative-agda-check.log).

These checks establish the declarations in these modules. They do not
establish a SAT complexity bound, construct a minimum representative basis,
or certify an Agda-to-HVM compiler. The representative selector/dominance
evidence and the cheap spanning expressions remain explicit hypotheses.
The retained-fibre result instantiates `photon.Fibre.lossless` directly.

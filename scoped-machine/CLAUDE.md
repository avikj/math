# Notes for agents working on scoped-machine

These record judgment errors already made here. Read them before touching code.

## What the machine is
- Source of the mathematics: `../docs/index.html` (Respecting Equality). Read §§0–5 and §9 before judging anything.
  Equality is equivalence and computes (ua, Glue). Every reversible step is a transport. Posing a declaration
  with its forced identities and normalizing is complete inference (5.27). Identities, transport, univalence
  and posing are the core of the system, never optional features.
- The machine is the combined keyed relation of HANDOFF §§19, 24–31: scoped references, one producer per key
  (U/R/D), frames that transcribe the dispatch table, explicit join boxes. §24 replaced the lambda net with it.
- The optimality theorem (paper 5.11–5.17, HANDOFF §§25–31) holds when ALL of these hold:
  1. a canonical key completely determines its computation;
  2. each frame has one owner and a deterministic next step;
  3. no waiter order, caller identity, view of the first requester, or timing changes a computation;
  4. every shared-state overlap is diagrammed with its counted events;
  5. completion includes all demanded work (no started-and-discarded demand).
  One producer per key is one invariant inside this, not the theorem.

## Rules learned the hard way
- Never delete, exclude or call optional anything before finding what in the paper/HANDOFF it realizes.
- Never repeat a reviewer's framing (e.g. "missing", "unspecified") without checking it against the paper.
- Parallelism = independent demands outstanding at once, joined by an explicit join (§26). No spawn,
  launch or threading primitives.
- A view belongs to resolution only. Nodes carry no view; a child carries only its own premises.
- No family branches on readiness of another entry.
- Adoption: name the relation (fixed demand network vs adaptive) and the reading before claiming balance;
  write the overlap diagrams with counted events first. Never drop actual work to make diagrams balance.
- Evidence words: a race detector run is not a protocol proof; a passing test is not the theorem.
- Don't write code while the design is being aligned with the user.

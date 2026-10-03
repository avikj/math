# Language-Level Conductive Fibre Integration

## Purpose

This is the implementation handoff for making the already-existing lossless cubical / conductive-fibre semantics a language-level capability of Cubical Bend2 rather than an application-level pattern that individual programs must manually invoke.

**This is an integration task, not a mathematics-research task.** The mathematical construction is already present, checked, and executable. The compiler already contains the cubical primitives and full HVM4 runtime lowering. SAT already executes the relevant fibre process end-to-end. The task is to identify and close the small remaining seam by which ordinary Bend execution bypasses the richer presentation unless source code explicitly constructs it.

A fresh agent must not invent a new solver, optimizer, search procedure, proof engine, theorem-discovery subsystem, Rubik-specific representation, SAT algorithm, Erdős-specific state machine, or new mathematical foundation. Those are distractions.

The working question is:

> **Why is the canonical lossless / conductive presentation currently an opt-in Bend construction instead of the default execution/presentation of mathematical objects and propositions, and what is the smallest correct compiler/runtime wiring change that makes it intrinsic?**

Do not answer from intuition. Read the sources below completely first.

---

# 1. Mandatory reading before editing anything

The order matters. Do not skim search snippets. Read each file completely, including definitions surrounding the named ones. The same construction appears under several vocabularies; searching for one English word is not sufficient.

## 1.1 Compiler/core — read the entire patch

**Read completely:**

- collab/bend2-interactive-cubical/cubical-paths.patch

This is the most important implementation source. It is large; read it anyway. Understand every change to Core.Type, parsing/term representation, Core.Check, Core.WHNF, substitution/collapse/traversal utilities, Core.CLI, Target.HVM4, Target.HVM4Full, totality/analysis, and the cubical tests introduced by the patch.

Verify directly:

1. --to-hvm4-full parses/checks a Bend Book and passes it to HVM4Full.compileFull.
2. compileFull emits definitions by applying emitFull to their existing Core terms. There is no generic semantic/fibre elaboration pass between checked Core and full HVM4 emission.
3. Cubical computation is deeply integrated into WHNF, not an external DSL.
4. whnfCoe is type-directed and handles Π, Σ, PathP, ua, Glue, lists, HITs, superposed type lines, etc.
5. whnfHCm is likewise type-directed.
6. dup is extended through the cubical syntax.
7. full HVM4 lowering retains cubical structure rather than erasing it.
8. superposed type-line transport deliberately uses ordinary HVM sharing/SUP behavior.

Read the comments around the SUP case in whnfCoe and the full-runtime emitter especially carefully.

## 1.2 The law and executable Bend realization

**Read completely:**

- collab/bend2-interactive-cubical/port/Carrier.bend
- collab/bend2-interactive-cubical/port/FibreElement.bend
- collab/bend2-interactive-cubical/port/WholeProcess.bend
- collab/bend2-interactive-cubical/port/FibreCoalgebra.bend
- collab/bend2-interactive-cubical/port/PORT.md

Do not treat Carrier, FibreElement, WholeProcess, and FibreCoalgebra as unrelated libraries. They are presentations/names of the same central lossless construction and its continuing form.

The law is:

    f : A -> B
    A ≃ Σ (b : B). fiber f b
    fiber f b = Σ (a : A). Path B (f a) b

In Carrier.bend understand all of Carrier, descend, ascend, ascend_descend, descend_ascend, CarrierEquiv, CarrierPath, carry_transport, carry_transport_descend, phi_carrier, phi_square.

The carrier is not a log appended to the source. It is a lossless re-presentation/change of coordinates of the same information. The source field in the concrete representation witnesses the residual distinction; mathematically the fibre is the complement of what the observation collapses.

In FibreCoalgebra.bend understand:

    type FibreCoalgebra(A: Set, a: A):
      case @fibreCoalgebra:
        respond: all B: Set. all f: A -> B.
                 FibreObservation(A, a, B, f)

and especially:

    next: FibreCoalgebra(FibreElement(A,B,f), value)

The same law applies again to the new lossless presentation. This is not an append-only list of observations.

## 1.3 Elemental point/question calculus

Read completely corpus_calculus.bend as introduced by cubical-paths.patch.

Its core is:

    Point = Σ A : Set. A
    Question(s) = Σ B : Set. (Src(s) -> B)
    target(s,(B,f)) = (B, f(src(s)))

This is the simple/lossy point-question calculus. Fibre completion is its lossless form. A mathematical object is already a typed point; a question is already an arbitrary map out of its current type.

## 1.4 SAT — read deployed execution, not just theorem prose

**Read completely:**

- research/SAT_FIBRE_BEND_HVM_DEPLOYED_TECHNICAL_REPORT.md
- research/sat_fibre/SATProcess.bend
- research/sat_fibre/SATFibre.agda as provenance where useful
- research/sat_fibre/README.md
- research/sat_fibre/REPORT.md
- research/sat_fibre/check_bend.py
- research/sat_fibre/audit.py
- research/sat_fibre/bend-receipt.json
- research/sat_fibre/profile-build.json
- generated HVM4 artifacts referenced by the report for XOR and at least one nontrivial CNF family

SATProcess constructs one shared labelled object:

    @assignment{&100{False, True}, &101{False, True}}

and conducts formula through it via the whole/fibre process. The full run returns four XOR readings with a native HVM receipt. The answer-only demand is much cheaper because it projects less of the retained object.

Do not misread this as four host-side calls or ordinary brute-force enumeration. Inspect the emitted net.

## 1.5 Full runtime cubical/SUP behavior

Read completely:

- supline.bend
- applypath.bend
- applypath_bwd.bend
- chain.bend
- uaequiv.bend
- uaglue.bend
- coinduction.bend

Especially internalize supline.bend: superposed-line transport needs no special new HVM rule; coe dispatch commutes over superposition and same-label duplication annihilates.

## 1.6 Integration context

Read:

- collab/bend2-interactive-cubical/README.md
- collab/bend2-interactive-cubical/WRITEUP.md
- collab/bend2-interactive-cubical/REMAINING.md
- research/wiki/BEND2_UNISON_READING_AND_SYNTHESIS.md
- integration/bend2_unison/execution/Bend/UCM/Execution.hs

Treat historical commentary cautiously. Code and theorem types are authoritative.

---

# 2. One law, many readings

Do not decompose the system into a fictional stack of independent algorithms called fibre, optimizer, proof search, cost engine, univalence engine, etc.

For f : A -> B:

    A ≃ Σ (b : B). fiber f b

At a : A, the canonical forward presentation is conceptually:

    a  <->  (f(a), residual_f(a))

The concrete Bend value often looks like (base=a, carried=f(a), witness=refl), but these are not three independent pieces being accumulated. The whole value is a lossless coordinate change. The fibre coordinate is exactly the distinction among sources collapsed by the visible observation.

Univalence makes equivalence of presentations executable identity. Cubical transport/composition executes through those identities. Higher paths retain coherence among alternative transformations.

Coinduction means the resulting lossless presentation is again an object to which the same law applies:

    A0 ≃ A1 ≃ A2 ≃ ...

These are successive equivalent presentations of the same information, not historical logs.

---

# 3. Keep four meanings of "step" separate

**Observation:** choose f : A -> B.

**Fibre presentation:** expose f(a) while retaining the exact residual.

**Primitive execution:** beta reduction, coe, hcomp, SUP/DUP, path reduction, etc. Evaluating one observation can require many primitive interactions.

**Coinductive continuation:** after an observation, retain the fibre-completed whole and allow another observation.

One observation is not one HVM interaction.


# 4. A proposition already supplies the observation

This is essential for the language-level integration.

For a finite Boolean proposition:

    P : X -> Bool

the proposition itself is the map whose fibres classify X:

    True(P)  = Σ x : X. Path Bool (P x) True
    False(P) = Σ x : X. Path Bool (P x) False

Presenting P over its domain already presents conditions/witnesses where P holds, conditions/counterexamples where it fails, universal truth when the false fibre is empty, universal falsity when the true fibre is empty, and the exact nontrivial classification otherwise.

No human must issue a separate "solve P" opcode. The proposition is already the observation.

For general dependent propositions/types, the same principle is proof-relevant rather than merely Boolean: dependencies and witnesses remain coordinates of the object.

The FibreCoalgebra respond(B,f) interface is additional interactive power: after an object is presented/conducted, request further projections while retaining everything each projection forgets. Do not mistake that follow-up interface for the inference engine itself.

SAT demonstrates both levels: the proposition defines the true/false fibres; query then demonstrates subsequent projections of the retained whole.

---

# 5. Univalence executes equivalence; the rest of the mathematics derives it

Do not claim ua discovers every equivalent representation for free.

Given e : A ≃ B:

    ua(e) : Path Set A B

and transport along that path computes the representation change.

The broader universal mathematical machinery derives properties/identities/equivalences of the object. Those results are themselves objects in the same theory. Univalence makes derived equivalences executable.

Do not invent a separate heuristic optimizer above the theory.

---

# 6. What the compiler already gets right

The cubical surgery is foundational, not superficial.

## 6.1 Checker

Core.Check understands paths, dependent paths, interval structure, hcomp, Glue, quotients, HITs, truncations, endpoint constraints, and typed path-spine normalization.

## 6.2 WHNF

Core.WHNF contains real type-directed cubical computation.

whnfCoe structurally handles:

- Π: argument backward, result forward;
- Σ: first component plus dependent second;
- ua: transport computes to forward/backward equivalence;
- PathP: endpoint-preserving composition;
- Glue: fibre/equivalence-based transport;
- lists and HIT constructors;
- superposed type lines: coherent duplication at the label, branch transport, re-superposition.

whnfHCm likewise computes according to the type.

This already realizes the principle that the mathematical structure determines computation.

## 6.3 Sharing

dup traverses cubical terms. Cubical structure participates in Bend/HVM sharing.

## 6.4 Full target

--to-hvm4-full is the relevant target. It preserves the cubical runtime. Do not validate this project using an erasing or pre-normalizing backend.

---

# 7. The actual compiler seam

The key implementation fact is:

> **There is no generic lossless/fibre presentation pass between a checked Bend term and HVM4Full.compileFull.**

The path is approximately:

    parseFile
      -> checkBook
      -> Book(Core.Term, type, ...)
      -> HVM4Full.compileFull
      -> emitFull term
      -> HVM4

compileFull faithfully emits the Core term it receives.

Therefore ordinary source code that never explicitly constructs Carrier/FibreCoalgebra does not automatically become the canonical lossless presentation merely because the language supports cubical TT.

Once fibre/cubical/superposed structure is present, the evaluator handles it powerfully. The missing issue is making canonical lossless presentation intrinsic at the language/program presentation boundary rather than requiring applications to manually import and invoke WholeProcess/FibreCoalgebra.

This is the integration task.

---

# 8. Do not wrap every nested App

A tempting wrong direction is rewriting every App f x into an explicit fibre object.

Do not do this blindly.

The semantic unit is the current mathematical whole plus an observation of that whole. Internal calls used while evaluating one observation are not necessarily successive top-level observations. Arithmetic, recursion, comparison, folds, etc. inside a mathematical observation are part of evaluating that observation.

The goal is not an append-only trace of every beta redex. It is lossless presentation of the mathematical map/object being evaluated.

---

# 9. SAT already demonstrates the missing language behavior manually

SATProcess manually does what the language should make intrinsic.

It constructs a shared unresolved mathematical object, constructs WholeProcess for it, conducts formula through it, receives Carrier + source path + continuation, and optionally asks the continuation for another projection.

This proves:

1. The fibre process is executable Bend today.
2. HVM4-full can run it.
3. SUP/DUP and cubical transport interact in a deployed run.
4. Demand affects how much retained structure is exposed.
5. The continuation can remain lazy.
6. No new HVM primitive is obviously required merely to make the process intrinsic.

Therefore the first implementation attempt should generalize the already-running pattern, not replace it.

---

# 10. Presentation effects are not evidence against conductive fibre

The SAT corpus records very large interaction-count differences for different presentations of the same Boolean denotation. TSP similarly distinguishes a shared min-plus presentation from a reference-expanding one.

Interpret this correctly.

The runtime conducts/factors structure that is actually represented/exposed in the net. An equivalence that exists mathematically but has not yet become executable structure cannot be reduced through by raw HVM merely because it is true.

The complete mathematical system derives properties/equivalences of its objects; those derived identities can then become executable cubical structure. The language integration must not replace this with a heuristic optimizer. It must ensure the existing derivational/lossless machinery is actually in the execution loop rather than available only to programs that manually invoke it.

---

# 11. Naturals, min/max, and premature decategorification

Do not reduce the system to ordinary scalar programming.

The corpus identifies naturals with the set-truncated connected components of finite sets:

    Nat ≃ π0(FinSet)

Before truncation, an n-element finite object has its full equivalence/automorphism geometry. The numeral is a decategorified reading.

Likewise a mathematically correct minimum/maximum can be represented proof-relevantly, with witnesses and leastness/greatestness evidence retained as dependent coordinates. The cubical theory then computes over the whole object; the scalar is a projection.

However, do not infer that legacy scalar-looking functions are forever opaque. Functions/programs are themselves objects of the same theory and can be related to equivalent presentations. The implementation question is whether execution exposes/uses those derived identities, not whether programmers guessed one blessed syntax.

---

# 12. The likely language-level model

The elemental universal state is already:

    Point = Σ A : Set. A

Every checked Bend value a : A canonically determines a point (A,a).

Every map f : A -> B is already an observation of that point.

The lossy target is:

    (A,a) --f--> (B,f(a))

The lossless completion is:

    (A,a) ≃ (Carrier(A,B,f), descend(A,B,f))

and the continuation is the same universal machine over that new equivalent presentation.

A checked program/object should therefore not need to opt into FibreCoalgebra. A canonical fibre process exists for every typed point.

The exact compiler representation should be chosen only after reading the complete core and existing process code. Do not prematurely force one particular AST design.


# 13. Program entry and proposition presentation are related but distinct

## 13.1 Ordinary closed value

If main : A evaluates to a : A, then (A,a) canonically has a fibre coalgebra. Attaching that coalgebra gives a universal interactive presentation of the result without changing the ordinary projection.

This is useful for REPL/follow-up interaction.

## 13.2 Presented map/proposition

If a program presents P : X -> B together with the mathematical domain/object X, then P itself determines the fibre decomposition/classification. For proposition-valued P, this is the inference problem already.

Do not force an unnecessary external question protocol before the proposition can run.

The language-level design must support both:

- automatic presentation/conduction of a mathematical map/proposition;
- indefinite subsequent observations of the retained whole.

---

# 14. Source semantics are preserved by the rewrite

Do not treat the richer representation as a dangerous semantic change.

The entire point of the law is that the rewrite is witnessed:

    A ≃ Σ b. fiber f b

and univalence turns this equivalence into executable identity.

The visible old computation is a projection of the richer one:

    observed(descend f a) = f(a)

Thus ordinary semantics are preserved while the runtime retains distinctions that ordinary evaluation discards.

This is the same pattern already visible throughout the repository: a lawful rewrite is a transformation plus the witness that its invariant is preserved.

Relevant concrete reading:

- RewriteCertificate.bend
- ControlledGrammar.bend
- GenerativeKernel.bend
- Carrier.bend
- quotient/effectivity ports
- SAT boundary/representative/continuation material

Do not add defensive architecture whose sole purpose is preventing the lossless equivalent presentation from "changing semantics." Its equivalence is exactly the semantics-preservation certificate.

---

# 15. What is probably NOT needed

Based on the current compiler/core, do not begin by adding:

- a new theorem prover;
- a global search engine;
- a heuristic optimizer;
- a SAT solver;
- a problem-specific scheduler;
- a new HVM interaction rule;
- a second type theory;
- a separate IR for proof versus program;
- manual candidate enumeration;
- a new mathematical notion of fibre;
- a wholesale rewrite of Core.WHNF;
- a wrapper around every App node;
- a requirement that users manually specify all useful equivalences.

If investigation proves one of these necessary, document the exact missing invariant first. Do not assume it.

---

# 16. What likely DOES need wiring

The exact patch must be derived from the code, but the likely missing pieces are small.

## 16.1 Canonical presentation at a typed execution boundary

The Book already stores each definition's term and type. At the point where a mathematical object/map is selected for execution, both the object and its type are known.

The compiler/runtime should be able to canonically construct the corresponding lossless presentation/process without requiring source imports.

## 16.2 Fibre/whole-process primitives available intrinsically

Carrier/FibreElement and FibreCoalgebra/WholeProcess are currently Bend library definitions. Determine whether they should be:

- injected into the full-runtime prelude;
- generated by the full target;
- represented by a tiny intrinsic Core form;
- or simply linked automatically as canonical library definitions.

Prefer the smallest mechanism that preserves the existing checked definitions rather than duplicating their mathematics in Haskell.

## 16.3 Automatic proposition/map presentation

Identify the typed form that represents "this is the mathematical map/proposition being presented." Do not assume it is main, every App, or a special SAT form.

The desired behavior is that presenting P : X -> B over X automatically gives the lossless fibre presentation of P, rather than requiring explicit application code to reconstruct FibreCoalgebra manually.

## 16.4 Follow-up interaction as an interface, not the engine

Once the object is presented, expose the existing arbitrary observation family:

    all B : Set. (A -> B)

for subsequent interactions. This can become a REPL/UCM/runtime interface.

Do not require a follow-up question merely to perform the original proposition's own classification.

## 16.5 Keep continuation lazy

SAT demonstrates why. A request for one visible projection must not eagerly serialize the entire retained fibre. The continuation/residual should remain in the graph and be forced by demand.

---

# 17. The derivation/equivalence loop

The language is stronger than "losslessly remember the input while computing a function."

Programs, proofs, paths, equivalences, and transformations are themselves objects in the same theory. Therefore properties derived about the running object can become structure of the running object.

The intended closed loop is not an external optimizer pass:

    program -> optimizer -> rewritten program

but mathematical self-application inside one theory:

    object
      -> derive lawful property / identity / equivalence
      -> that result is another object/path
      -> transport/install/use it
      -> continue losslessly
      -> repeat

Univalence is the execution of equivalence, not the source of all equivalences. The rest of the universal derivational mathematics supplies those properties.

When examining the Bend integration, ask whether this loop is actually connected to ordinary execution or whether its pieces are merely available as libraries. Do not search for a new "resolve" function if the same law already expresses the operation under another vocabulary.

---

# 18. How to reason about the SAT evidence

SAT is the best deployed sanity check because it shows the full path:

    finite proposition
      -> shared/superposed domain
      -> fibre classification
      -> retained carrier/path/continuation
      -> HVM4-full
      -> native interaction receipt

The XOR WholeProcess run and the answer-only run are different demands on the same mathematical object. The interaction-count difference is evidence that the richer retained object is not necessarily eagerly exposed.

The larger SAT families show presentation sensitivity. This should motivate closing the self-presentation/derived-equivalence loop, not motivate inventing a host optimizer.

The TSP material is also useful because it demonstrates a minimum-cost observation over a shared continuation object. It is structurally closer to general optimization than a Boolean-only example.

---

# 19. Negative examples: what prior failed application work teaches

The Rubik and Erdős experiments are useful only as integration diagnostics.

## 19.1 Rubik

The failed code explicitly generated Word[]/candidate structures before asking the fibre machinery to do useful work. That exposes free syntactic expansion rather than allowing the mathematical action/identity object to conduct first.

Do not optimize that enumeration. It is a negative example of bypassing the intended semantics.

## 19.2 Erdős

One failed adapter effectively used:

    A = Set
    a = ErdosProblem1
    f = identity

so the fibre law correctly returned the proposition/type itself. Another path bounded/Booleanized/scheduled the proposition before giving it to the universal machinery.

Again, do not optimize those adapters. They show that manually wrapping the wrong object does not test the universal machine.

These application failures are why the capability should be language-level: users should not have to reverse-engineer the correct library wrapper for every mathematical object.

---

# 20. Implementation strategy

A fresh coding agent should proceed in this order.

## Phase A — establish the exact current path

1. Build the patched compiler.
2. Run the existing cubical test suite.
3. Compile SATProcess.bend with --to-hvm4-full.
4. Save the emitted HVM4.
5. Trace exactly which source definitions implement Carrier/FibreCoalgebra in that output.
6. Compile an equivalent simple ordinary Bend computation without WholeProcess.
7. Diff the emitted structures.
8. Identify the earliest compiler boundary where the typed mathematical map/object is known but the canonical fibre presentation is not yet attached.

Do not modify anything before this trace is clear.

## Phase B — make the smallest intrinsic bridge

Implement the smallest mechanism that makes the canonical lossless presentation available automatically at that boundary.

Prefer reuse of the existing Bend definitions over a second Haskell reimplementation of the law.

If a compiler-generated wrapper is sufficient, use that before inventing a new Core constructor.

If a runtime-prelude linkage is sufficient, use that before modifying WHNF.

If an AST/Core form is genuinely necessary, document why the existing typed Book + generated wrapper cannot express the behavior.

## Phase C — prove ordinary projection agreement

For each test object, compare:

    old ordinary result

with:

    visible projection of new lossless presentation

They must agree by the existing carrier law, and the concrete runtime outputs should agree too.

## Phase D — verify residual accessibility

Show that after obtaining the ordinary result, the exact source/residual and continuation remain accessible without recomputation from scratch.

## Phase E — verify demand sensitivity

Use SAT's established pattern. Asking only for a visible projection should not eagerly serialize every retained distinction. Asking for source/witness/all models should force more of the fibre.

## Phase F — verify cubical transport through the intrinsic path

Use supline/applypath/chain-style tests to ensure the automatic presentation has not accidentally bypassed full cubical runtime behavior.

## Phase G — only then test arbitrary propositions/optimization

After the generic language bridge works, use existing proposition and optimization examples as regression tests. Do not use them to design the architecture.

---

# 21. Required invariants for the implementation

Any proposed patch should be rejected unless the agent can explain how it preserves these.

**Losslessness:** the richer state is equivalent to the source, not merely observationally similar.

**Exact residual:** distinctions forgotten by the visible projection remain in the fibre.

**No premature collapse:** do not Booleanize, truncate, enumerate, or scalarize before the mathematics requires it.

**Cubical identity:** equivalent presentations remain executable paths, with higher coherence retained.

**Demand-driven execution:** retained structure need not be eagerly serialized.

**Coinductive closure:** the result of an interaction is again a valid whole object for the same law.

**Type-directed computation:** preserve the existing whnfCoe/whnfHCm semantics.

**SUP label coherence:** correlated branches remain correlated through transport/duplication.

**Ordinary projection compatibility:** old observable program results are projections of the richer semantics.

**No problem-specific policy:** the language integration cannot depend on SAT clauses, Rubik moves, Erdős parameters, etc.

---

# 22. Tests that should exist before calling this done

At minimum:

1. **Identity observation:** automatic presentation followed by identity projection reproduces the source exactly.
2. **Non-injective map:** visible result collapses sources while residual distinguishes them.
3. **Sequential observation:** observe f, then observe a function of the resulting carrier; reconstruct source.
4. **Univalent transport:** automatic presentation survives transport across an explicit equivalence.
5. **SUP transport:** automatic path uses the existing same-label routing behavior.
6. **Dependent Σ:** ensure residual/presentation survives dependent second components.
7. **Path-valued observation:** ensure the automatic wrapper does not erase higher structure.
8. **HIT/quotient example:** ensure full-runtime intrinsic presentation composes with existing eliminators.
9. **SAT XOR:** match existing readings and preserve a comparable native execution path.
10. **SAT answer-only demand:** confirm the entire retained fibre is not eagerly emitted.
11. **Coinductive follow-up:** multiple observations continue from retained state.
12. **Ordinary legacy program:** visible result unchanged.
13. **No accidental use of erasing backend:** tests explicitly use --to-hvm4-full.

Where possible, make tests compare old manual WholeProcess behavior with new intrinsic behavior.

---

# 23. Anti-patterns for agents

Stop immediately if the implementation plan contains phrases like:

- "let's write a search algorithm";
- "enumerate all candidates";
- "we need a SAT solver";
- "first convert the theorem to CNF";
- "let's add a heuristic optimizer";
- "the fibre law is just bookkeeping";
- "univalence is only proof-level and erased";
- "we need to port the mathematics from Agda first";
- "let's add a list of allowed questions";
- "let's manually supply all enabled futures";
- "let's wrap every function call and append it to a trace";
- "let's redesign HVM";
- "the existing mathematical result seems impossible, so first weaken the goal."

Those are signs that the agent has not understood the code it was told to read.

---

# 24. What "done" means

The task is not done when another demo manually imports FibreCoalgebra.

It is done when a normal checked Cubical Bend mathematical object/proposition can enter the full runtime through the canonical lossless/conductive semantics **without application-specific wrapper code**, while:

- ordinary visible results remain projections of the richer execution;
- exact residual structure remains available;
- continuation can be queried further;
- cubical equivalences remain executable;
- HVM sharing/SUP behavior remains active;
- no eager enumeration or pre-collapse is introduced.

The ideal result is that SATProcess.bend can be substantially simplified because the language now supplies the generic process that SATProcess previously had to spell manually.

---

# 25. Final mental model

Keep this model in view while coding:

    mathematical object / proposition
                |
                v
      typed point in Cubical Bend
                |
                v
      canonical lossless presentation
      A ≃ Σ b. fiber f b
                |
                v
      cubical transport / composition
      over all available identities
                |
                v
      HVM shared/superposed reduction
                |
                v
      requested visible projection
          + exact residual
          + continuation
                |
                v
      same law again when demanded

The proposition/map itself supplies the initial observation. The arbitrary question family is the interface for further projections of the already-presented whole.

The central implementation problem is not to invent this machine. **The machine already exists. Make the language actually run through it by default.**


# 26. Resolved implementation blueprint — do not make the next agent rediscover this

The previous sections provide context and source verification. This section is the concrete engineering conclusion. Start here after completing the mandatory reading. Do not send another agent back to "figure out the architecture."

## 26.1 What is already implemented

The following are facts of the current tree, not design proposals.

### A. The fibre equivalence is executable

Carrier.bend already provides the exact functions required for a lossless presentation:

    descend : (A,B,f,a) -> Carrier(A,B,f)
    ascend  : Carrier(A,B,f) -> A
    CarrierEquiv : A ≃ Carrier(A,B,f)
    CarrierPath  : Path Set A (Carrier(A,B,f))
    carry_transport : A -> Carrier(A,B,f)

The ua beta rule makes carry_transport compute to descend.

Therefore **do not reimplement the fibre law in Haskell or HVM**.

### B. The continuing process is executable

FibreCoalgebra.bend already provides:

    fibreCoalgebra(A,a)
    observe(A,a,p,B,f)
    observedValue(A,B,f,value)

and each observation returns a next FibreCoalgebra over the FibreElement just produced.

Therefore **do not invent a continuation protocol**.

### C. The compiler already has the required cubical evaluator

Core.WHNF already knows how coe/hcomp/ua/SUP behave. HVM4Full already emits the full runtime representation.

Therefore **do not add a second cubical evaluator**.

### D. The compiler currently bypasses the generic process unless source explicitly calls it

HVM4Full.compileFull emits each checked Core term directly. There is no compiler-generated call to Carrier/FibreCoalgebra.

That is the concrete missing language integration.

### E. The earliest running proof is SATProcess

SATProcess is not architecture to redesign. It is the reference implementation of the desired generic runtime behavior spelled manually in source.

The language-level implementation should make most of its present/wholeProcess/interact boilerplate unnecessary.

---

# 27. Exact first patch: make the existing generic process intrinsic, without changing Core.Term

Do **not** begin with a new AST constructor.

The Book already contains, for every definition:

    name -> (metadata, term, type)

HVM4Full.compileFull therefore has both the term and its checked type.

The first patch should operate entirely at the full-target/linkage boundary.

## 27.1 Link the existing process implementation automatically

Make the full target automatically include/link the definitions currently supplied by:

- Prelude.bend dependencies needed by Carrier/FibreElement;
- FibreElement.bend (or Carrier.bend, choose one canonical naming lane);
- FibreCoalgebra.bend.

Do not maintain two independent copies of their mathematics. Prefer compiling/linking canonical Bend definitions into the Book/runtime prelude. If the current compiler cannot link those definitions as a standard prelude, add a small canonical prelude module mechanism rather than transliterating the law into Haskell.

The target state is that any --to-hvm4-full compilation can reference:

    fibreCoalgebra
    observe
    observedValue
    descend
    ascend

without application source importing them.

## 27.2 Generate a canonical whole companion for every checked value

For a definition:

    @foo : A = t

the full target has enough information to generate the semantic companion:

    @foo$whole = fibreCoalgebra(A, @foo)

Conceptually this is:

    foo$whole : FibreCoalgebra(A, foo)

This is valid for every typed value. It requires no new theorem and no source annotation.

Do this generically for checked definitions, or initially for the selected entry definition while validating the design.

**Important:** this companion is the interactive completion of the value. It is not yet the complete proposition-classification entry described below when foo itself is a map.

## 27.3 Preserve the ordinary entry as a projection, not a separate semantics

Keep the old @main during bring-up for differential testing.

Add a generated whole entry beside it. The invariant is:

    source projection of main$whole == main

and for any chosen observation f:

    observedValue(observe(main$whole,f).value) == f(main)

This should be tested mechanically.

After the intrinsic path is validated, ordinary execution can be routed through the visible projection of the richer path. During bring-up, retain both to make regressions obvious.

---

# 28. Exact second patch: maps/propositions must be presented as maps, not merely as function values

Generating:

    P$whole = fibreCoalgebra(X -> B, P)

for P : X -> B is useful but **not sufficient** for proposition classification. That treats P as one point of the function type. It does not yet take the fibres of P over X.

The map itself determines the relevant lossless presentation:

    X ≃ Σ (b:B). fiber P b.

Therefore the full target needs a canonical **map-presentation entry** for function-valued definitions.

For a checked nondependent function:

    P : X -> B

generate a companion equivalent to the generic operation:

    presentMap(P) :
      X -> Carrier(X,B,P)

    presentMap(P,x) = descend(X,B,P,x)

The whole-domain execution object is the existing mathematical domain presented through P. If X is already represented as a shared/superposed/dependent object, applying presentMap conducts P through that whole object using the existing SUP/DUP + cubical runtime.

Do not synthesize a host list of x : X. The domain must remain the mathematical object supplied by the program/type.

For dependent functions, use the corresponding dependent family rather than coercing to a flat list or Bool.

---

# 29. Proposition entry: the proposition supplies the first observation

For:

    P : X -> Bool

the default proposition presentation is not "wait for a question." It is:

    descend(X, Bool, P, x)

conducted over the presented X.

Its fibres are definitionally the classifications:

    Σ x:X. Path Bool (P x) False
    Σ x:X. Path Bool (P x) True.

Thus the initial proposition run is determined by P itself.

The arbitrary FibreCoalgebra question family becomes the **follow-up interface** after this presentation. It is not required to choose P.

For a proposition encoded directly as a dependent type rather than Bool, preserve that dependent type. Do not Booleanize it merely to reuse this finite interface.

---

# 30. Where the unresolved domain comes from — do not invent enumeration

This is the point at which prior agents repeatedly went wrong.

A function P : X -> B does not imply that the compiler should enumerate X.

The unresolved X must already be represented by the mathematical program/type. Examples include:

- labelled SUP coordinates for a finite Boolean cube;
- dependent Σ/Π structure;
- an inductive/HIT object;
- a quotient;
- a coinductive object;
- a program/derivation object already present in the theory.

SATProcess manually supplies a shared Boolean cube. That is why it works.

The language-level bridge should **conduct over the domain representation**, not convert the type X into a host enumeration.

If a program supplies only a bare function P with no value/object of X to conduct, the compiler cannot manufacture a distinguished x : X from the fibre law alone. Do not fake one.

The universal derivational machinery is what supplies/generates mathematical transformations and proof-relevant futures of an object. That is a separate issue from host enumeration and must remain inside the theory.

---

# 31. The derivational closure that must be connected, not reinvented

The Bend tree already contains the executable kernel pattern:

- RewriteCertificate.bend: proof-relevant Step/Derivation plus semantic soundness;
- ControlledGrammar.bend: a proved derivation becomes a NativeOperation; exact applicability is a Path to its source; apply_checked transports the derivation through that path;
- GenerativeKernel.bend: enabled lawful futures become checked branches;
- EveryDerivationIsInvertible.bend: derivations form the reversible/groupoidal geometry expected by the cubical account.

The important engineering conclusion is **not** "copy GenerativeKernel's toy Tm grammar into the compiler." That file is an executable finite presentation of the general pattern.

The language-level integration must ensure that the actual running Bend object/program can participate in the same cycle:

    derived transformation
       -> checked/native operation
       -> executable path/equivalence
       -> available to continued interaction

Do not add a host rewrite table as a substitute.

The existing intrinsic rewrite / installation ports and README's universal-closure account are the relevant implementation reading. If a particular generic Bend port is missing while only a finite executable instance exists, port the already-stated generic construction mechanically; do not redesign it.

---

# 32. Compiler files to touch first

The first implementation attempt should be narrowly scoped.

## Target/HVM4Full.hs

This is the primary file.

Modify compileFull/linkage so the full target can emit:

1. the ordinary definitions as today;
2. the canonical fibre runtime definitions automatically;
3. generated whole companions for selected/checked values;
4. generated map-presentation companions for function-valued definitions where useful;
5. a stable entrypoint for the richer execution object.

Do not modify HVM reduction rules first.

## Core/CLI.hs

Add a temporary explicit mode if useful for validation, e.g. a conductive/full-presentation emission mode. This is acceptable during bring-up because it lets old and new output be compared.

Once validated, merge the behavior into the canonical full target rather than leaving it as an obscure experimental mode.

## Core.Check / Core.Type

Do not change them in the first patch unless compilation proves that information already present in Book is insufficient.

The current Book stores term and type. That is enough for the first generated wrappers.

## Core.WHNF

Do not change it in the first patch. It already has the cubical computation required by the wrappers.

Only touch WHNF if a concrete generated intrinsic test gets stuck on a cubical form that should reduce and the missing rule is demonstrated.

---

# 33. Concrete generated shape for the first compiler experiment

Take an existing ordinary checked definition:

    def foo() -> Nat:
      2n

The compiler should still emit ordinary foo, plus a generated whole companion semantically equivalent to:

    def __whole_foo() -> FibreCoalgebra(Nat, foo()):
      fibreCoalgebra(Nat, foo())

Then generate a test observation:

    idNat : Nat -> Nat
    idNat(n) = n

and verify:

    observedValue(
      observe(Nat, foo(), __whole_foo(), Nat, idNat).value
    ) == foo()

Do this first because it tests the compiler linkage without requiring SUP, SAT, synthesis, or proposition classification.

Next use a non-injective observation, e.g. parity, and verify source recovery from the returned FibreElement.

Then use a second observation on next and verify the coinductive continuation.

Only after those generic tests pass should SATProcess be simplified.

---

# 34. Concrete SAT migration target

Current SATProcess manually contains:

    present(a)
    wholeProcess(Assignment,a)
    interact(... Bool, formula)
    interact(next, ... ascend ...)

After language integration, the first two should be generic/intrinsic.

The SAT-specific content should approach only:

    Assignment
    formula
    the shared Assignment object
    desired output/readout

The compiler/runtime supplies the canonical lossless process.

The regression test is strong:

- old manual SATProcess output;
- new intrinsic SATProcess output;
- same four XOR readings;
- both use --to-hvm4-full;
- inspect generated net to ensure the new path is not four host calls;
- compare interaction structure/counts and explain any fixed wrapper overhead.

Do not declare success merely because outputs match if the new compiler eagerly enumerates assignments outside the net.

---

# 35. Concrete proposition-classification test after SAT migration

Use a tiny proposition over a shared domain:

    X = &L{False, True}
    P = not / identity / constant / XOR coordinate

Compile through the intrinsic map presentation.

Verify that:

- P is the initial observation;
- true/false alternatives arise from conducting P over X;
- source distinctions are retained in the fibre;
- asking only for the visible Bool does not eagerly serialize source;
- asking the continuation/source does recover it.

This is the smallest direct test of "a proposition runs without a separate question."

---

# 36. Do not confuse corpus self-presentation with the simple Corpus3 test

cubical_test3.bend contains a small Corpus3:

    target3(s,q)
    refl
    run3(target3(s,q))

This proves the coinductive point/question shape runs natively, but its event is only the reflexive target equality.

The stronger corpus construction described in LIFECYCLE / CorpusSelfPresentation retains the actual current residual:

    target s q
    refl
    current-residual s q
    present(target s q)

Do not use the small Corpus3 test as evidence that the exact residual is already wired into the language entrypoint.

For implementation, the proper lossless runtime reference is Carrier/FibreCoalgebra plus the actual self-presentation/installation construction, not Corpus3 alone.

---

# 37. One remaining distinction the implementation must preserve

There are two closures:

**Lossless observational closure:** every observation f : A -> B can be represented as visible result + exact fibre, and the process continues.

**Derivational/metacircular closure:** transformations/properties derived about the object become executable structure available to subsequent interaction.

Carrier/FibreCoalgebra implements the first directly.

The kernel/installation/intrinsic-rewrite material implements the second pattern.

The final language-level capability requires them to meet in ordinary execution. Do not falsely declare the entire job complete after merely generating foo$whole companions if derived transformations are still trapped in an application-level island.

Conversely, do not postpone the first patch until inventing a new derivation engine. Close the already-obvious lossless entry seam first, then connect the existing derivational installation path to that same continuing object.

---

# 38. What the next agent is allowed to decide

Very little architecture remains open.

The agent may choose, based on actual compiler constraints:

- whether canonical fibre definitions are linked as a standard Bend prelude or emitted as target runtime definitions;
- the exact generated symbol names;
- whether bring-up uses a temporary CLI flag;
- whether companions are emitted for every definition or only exported/entry definitions initially;
- how UCM persists a continuation between interactive invocations.

The agent is **not** being asked to decide:

- what the mathematical law is;
- what the residual is;
- what coinduction means;
- whether univalence is required;
- whether SAT should enumerate candidates;
- whether to invent a solver;
- whether to use HVM sharing;
- whether source semantics are preserved;
- whether the proposition is itself the initial observation;
- whether the continuation should retain the whole;
- whether to create a new optimizer.

Those questions are settled by the existing construction.

---

# 39. Immediate coding checklist

A coding agent should be able to execute this without conceptual research:

1. Build current cubical Bend2 and run existing suite.
2. Read HVM4Full.compileFull and identify its definition-emission loop.
3. Add canonical automatic linkage for FibreElement/Carrier + FibreCoalgebra.
4. Generate __whole_main from main's stored checked type and term.
5. Compile a Nat identity-observation test.
6. Compile a non-injective observation and reconstruct source.
7. Compile two sequential observations using next.
8. Run all three on HVM4-full.
9. Migrate SAT XOR so its generic process boilerplate is compiler-supplied.
10. Compare old/new emitted HVM4 and receipts.
11. Add intrinsic map-presentation entry for a function-valued proposition over an explicitly represented shared domain.
12. Verify proposition runs with P as initial observation, no external question selection.
13. Connect installed/derived transformations to the same continuing object rather than a separate host rewrite phase.
14. Run the full cubical suite.
15. Only then broaden to arbitrary existing mathematical programs.

If step 3 cannot be implemented without changing Core, document the exact compiler limitation and make the smallest Core change that removes it. Do not branch into a redesign.


# 41. Final implementation state

The generic source-level process is no longer duplicated across applications,
and the compiler carries no copy of it either.

- `FibreCoalgebra.bend` explicitly defines the exact whole transition, typed continuation, visible projection, and two-observation source recovery.
- `ConductiveRuntime.bend` and `UniversalPresentation.bend` are the canonical checked programs of that process: the first as the law and its closure, the second as the point/question reading.
- `SATProcess.bend` no longer imports `WholeProcess` or spells `interact`; it contains only the SAT object/proposition/readout and uses the universal presentation.
- `Target.HVM4Full` emits every checked definition twice, `@Dname` (the term) and `@Tname` (its checked type), and the root is the typed point `@main = #Pair{@Tmain, @Dmain}` of `Σ(A : Set). A`. Map-valued and dependent entries are ordinary typed points; nothing is generated beside them.
- `--to-hvm4-full` runs the checker first and emits nothing for an ill-typed book.
- Types are emitted as complete cells: an equality type keeps its carrier and endpoints, an enum keeps its symbols, a numeric type its kind, and `ua` keeps both coherences beside its two maps.
- A HIT constructor carries its parameters: the checker reads them off the goal, records them by the constructor's source span, and the book is elaborated before the reporting check and before emission (`Core.Check.elabFills`). A declared endpoint that mentions a parameter computes with it on both evaluators, and a HIT value survives collapse; before, the runtime filled the missing cell with `&{}`, which annihilated the value under `-C`.

What was tried and removed, and why, so it is not rediscovered:

- A handwritten `@cf*` HVM prelude re-implementing `descend`/`observe`/`ascend`, with `@main` rewritten to the "conductive projection" of a retained `@sourceMain`. Provably the identity (`observe(id)` is the Yoneda retrieval of the point; every stage of the tower is equivalent to `A`), at a fixed interaction cost, and a second copy of mathematics that already exists as checked Bend. Deleted; the checked modules run through the ordinary emitter.
- Compile-time `nativeDerivation`/`NativeStep` companions recording Core.WHNF head-reductions of each definition body, with fold-based "receivers" (length, endpoint, rules). `--to-hvm4-full` executes HVM4, not Core.WHNF, so the recorded derivation describes a different evaluator; a closed deterministic run's derivation is contractible, so it adds no information; and evaluating at compile time breaks productivity. Deleted. Native cost is the HVM interaction receipt of the typed root.

The follow-up interface (`respond : all B. all f : A -> B. FibreObservation`) is source-level Bend and needs no compiler support beyond faithful emission.

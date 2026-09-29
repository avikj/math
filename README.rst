==============================================================================
 THE METACIRCULAR KERNEL
 a self-rewriting content-addressable computer, machine-checked in cubical Agda
==============================================================================

  A rewriting calculus whose derivations are reversible data rather than a
  reduction order; an evaluator; a soundness proof; and one line that closes
  the loop --- ``install : Derivation lhs rhs -> NativeOperation`` --- so a
  theorem the system proved becomes an operation the system can apply.

  Around it: a classification of the cost measures such a calculus admits, a
  criterion for what a verifier can and cannot learn from a proof, and five
  independent results in grammar, gauge theory, analytic number theory and
  distributed systems that turn out to state one fact about descent.

  Nothing here asks to be believed.  Every claim is a term a typechecker
  accepts or leaves as an obligation::

      sh setup                     # installs the pinned toolchain, from nothing
      sh check                     # typechecks, and names the toolchain it used

  No postulates, no holes, ``--safe`` throughout.

  Historical sources --- Pini's grammar, Indian algebra, and the classical
  logics whose judgment structures some modules formalise --- are cited where
  a construction came from one, and are kept in ``historical/``.  They are
  provenance, not premise: no result below depends on any of them being read.


THE PIN, AND WHY YOU WILL NEVER BE CONFUSED BY A VERSION AGAIN
------------------------------------------------------------------------------------------

  Agda 2.8.0 and agda/cubical v0.9.  Both numbers appear once, in `setup`,
  and everything else reads them from the two ``.agda-lib`` files it writes.

Three rules pin it, and none of them is a convention anyone has to remember:

**Every `depend:` names an exact version.**  ``depend: cubical-0.9``, never
``depend: cubical``.  agda/cubical puts its release into its own library
name, so the exact name is a hard resolution constraint: a wrong checkout
fails AT RESOLUTION, naming the library, instead of resolving and then
failing somewhere deep inside a proof where the cause is invisible.

**`sh check` names its toolchain before it checks anything, and refuses to
run off the pin.**  It prints the versions it found, and if they are not
the pin it stops and says so — so a red is never ambiguous between "the
mathematics is wrong" and "my machine is wrong."

**`sh setup` is the only thing that installs.**  It works from an empty
container: apt for ghc and cabal, cabal for Agda, git for the library.  It
knows the three obstacles that actually bite — cabal writes its config
lazily so a fresh machine has nothing to patch; the shipped index URL is
http and many proxies tunnel only https; hackage's mirrors answer 403 on
networks where hackage itself answers 200 — and it prints exactly what it
obtained either way.


THE KERNEL, AND WHY IT DOES NOT GENERATE FOREVER
------------------------------------------------------------------------------------------

  formal/cubical/Kernel/ — 296 lines in three files (RewriteCertificate,
  ControlledGrammar, GenerativeKernel), and the entry is
  DescentNote_WhatThisIsAndHowToDescendIntoTheMetacircularKernel.agda,
  written for an arriving mind.  Fourteen modules, all green at the pin
  (Agda 2.8.0, agda/cubical v0.9), re-runnable::

      sh check

The calculus is six variable coordinates, zero, suc, add, and six rewrite
steps: the two defining equations of +, three congruences, and `reverse`.
`reverse` destroys the rewriting direction on purpose, so what remains is
not a reduction relation but a generated equivalence carried as data —
and `Derivation` imposes no relations, so two walks between the same
endpoints are two distinct objects.  Then one line closes the circle::

      install : Derivation lhs rhs → NativeOperation

A theorem the machine proved becomes a move the machine can make.

The loop does not generate mathematics forever, and the reason is not a
missing feature.  Five properties,
each a checked term, say why — and each is why the thing can be trusted:

**1 · Every application carries its certificate to its site.**
`control-sound : Control t → t ≡ source` pins an OPEN field: the caller
supplies any predicate on terms it likes, and the operation still fires
only where the term IS the source.  A single-locus theorem proves the consequence in
one composite — however permissive the control, an operation has at most
ONE locus — and computes the installed locus type: contractible, centre
the source.  So capability grows by one term per theorem, never by a
class.  A schema is a claim about all its instances checked once,
abstractly, after which it fires everywhere unexamined; `apply-checked`
instead TRANSPORTS the certificate to the site.  *Cannot generalise* and
*cannot be wrong at a site* are one sentence read twice.

**2 · Meaning is a proposition; the route is not.**
`Sesa_` — `eval` lands in ℕ, a set, so soundness lands in a proposition,
so for ANY C at ANY level and ANY φ of the meaning, φ agrees on the
2-step and the 4-step derivation.  No semantic criterion selects the
short proof.  Selection is therefore extra-semantic, by theorem.  This is
why the machine cannot iterate on its own: the space is not unreachable,
it is UNDIRECTED, and direction has to arrive from an interlocutor.

**3 · Multiplicity is conserved.**
`advance-preserves-branch-count` — no dedupe, no sort, no quotient.  Read
with 2, this is not housekeeping: it is the only place the information
the semantics destroys is still held, the kernel holding branches open
for someone outside to choose among.

**4 · Reversibility is structural, not inferred.**
`reverse` is a constructor.  It has to be, because `Samyoge_` proves
losslessness composes and lossiness does not — `Unit → Bool → Unit` is
the identity with neither factor an equivalence — so you may certify a
pipeline lossless step by step and may NOT diagnose it lossy that way.

**5 · New content comes from changing the reading, and its yield is
finite and measurable.**
`Ankapasa_` keeps the calculus and changes the codomain: every Step
becomes an equivalence, `reverse` becomes `invEquiv`, and a commutation
invisible to `eval` is a nontrivial loop in the universe, through `uaβ`.
`VyatyasaVarga_` then measures that loop: order exactly two.  **ℤ/2** —
not a braid generator, because ⊎ is symmetric monoidal and its symmetry
is an involution by construction.

  So the negative result IS the asset.  A finite-information machine
  iterating on a fixed semantics has no criterion, and the criterion
  cannot be manufactured from what it knows.  What produces mathematics
  here is interaction — `Samvada_`: a session is one Derivation, hence
  one theorem, hence one installable operation, so the stock of moves is
  the transcript of the dialogue — and translation, which is §IV below,
  and whose yield you can measure.

  You can hold that session yourself::

      sh interactive/run-yantra.sh --wire
      {"kriya":"vargaprakrti","angani":{"D":61}}

  which returns x² − 61y² = 1 at (1766319049, 226153980) — Bhāskara II's
  own number, Bījagaṇita, 1150 — with every norm the cakravāla visited.
  Every answer is a transport carrying what a collapse of it would
  destroy, or a written defect naming its losses one by one.  There is no
  boolean on that wire: one bit returns the same value for a false
  statement and for a failed search, and the difference is the content.


THE SENTENCE
------------------------------------------------------------------------------------------

  A rule, an observer, a sieve, or a score is blind exactly to what its
  own collapse identifies.  The blindness is FORCED by the collapse — not
  chosen, not an approximation, not a resolution limit.  The invisible
  quantity is not small.  It is complementary.  And it is recoverable only
  by changing place, never by refining the instrument.

Five checked theorems say this.  They were written independently, about
five subjects.  Two of them are
literally about one object.



I.  GENERATIVE GRAMMAR      rule ordering in Pini, Adhyy, c. 500 BCE
------------------------------------------------------------------------------------------

  8.2.1   पूर्वत्रासिद्धम्   from this sūtra to the end of the text, a rule is
          asiddha — "as if not having taken effect" — with respect to
          everything that precedes it.  The blindness is one-way, ordered,
          and stated as a rule of the grammar itself.

  the collapse    8.4.56 वाऽवसाने sends two forms that DISAGREE about
                  8.2.39's applicability to one and the same form.
  what goes blind that applicability.

A checked term proves there is no Bool-valued function on the later forms
agreeing with it.  Not a different answer there — NO VALUE THERE.

So asiddhatva is not a device against looping.  That is a separate
theorem, proved separately.  8.2.1 is a DESCENT CONDITION: it registers
that an earlier rule's condition is a function on a fibre which the later
rule's collapse destroys.  A second term exhibits the two points of that fibre,
so the fibre is not a figure of speech for the invisible part.  It is that
set.

  A predicate descends along a map iff it is constant on its fibres.
  8.4.56 has a two-point fibre on which 8.2.39's applicability is not
  constant.  Hence no descent — and the blindness is forced, not
  stipulated.



II.  GAUGE THEORY, LOOP QUANTUM GRAVITY
------------------------------------------------------------------------------------------

  the collapse    an observable invariant under the holonomy.
  what goes blind the holonomy — exactly, and in both directions.

invisibleExactlyWhenInvariant  —  a semantics is unmoved by transport
along ua h IFF it is invariant under h.  Invisibility and invariance are
not two facts about an observable.  They are one condition read from two
sides.  invisibleIsInvariantAsTypes upgrades it, when the value type is a
set, to an EQUIVALENCE of the two conditions.

And the converse cost nothing.  The reason outlives the theorem:

  the two sides are joined by uaβ, which is a PATH, and a path may be
  walked in either orientation.

  A PATH HAS AN INVERSE.  AN IMPLICATION DOES NOT.

So "is the converse free?" has an answer readable off the shape of what
connects the two sides, before either direction is attempted.

The three physics modules together give the representation-independent
content of LQG kinematics, and it is four things:

  · edges are group actions;
  · vertices are intertwiners, and gauge invariance IS the equivariance
    square — not a constraint added on top of the label;
  · flux is a derivation, and subdivision-compatibility is FORCED by
    multiplicativity and Leibniz alone.  Orientation and intersection
    sign are chosen afterward and are not needed for it;
  · an observable is blind to holonomy exactly when it is gauge-invariant.

  For a physicist, one sentence: LQG kinematics is the category of actions
  of the gauge group.  SU(2), tensor products and the Hilbert space are
  representation-theoretic choices made after the structure is fixed, and
  the entire physical residue — what no gauge-invariant observable can see
  — is holonomy, exactly and measurably.



III.  ANALYTIC NUMBER THEORY     the parity barrier, with no sieve in it
------------------------------------------------------------------------------------------

  the collapse    idempotence.
  what goes blind sign.

The general reason needs no arithmetic at all:

  KNOWING SOMETHING TWICE IS KNOWING IT ONCE.

Any state law that ACCUMULATES — observations, constraints, standpoints,
congruences, installed primes — is idempotent, because combining a datum
with itself adds nothing.  lcm is idempotent for that reason, and not for
a reason about divisibility.

sign-is-not-accumulable  —  there is no accumulative law and no
multiplicative f into ℤ taking the value −1.  Ever.  Not "hard to
accumulate."  Over ℤ the units are ±1, so this rules out λ everywhere and
μ off the squares, FOR EVERY ACCUMULATIVE LAW AT ONCE, with no domain
hypothesis.

  The parity barrier is not a limitation of sieve technology.  Whatever
  carries sign, it is not accumulation.  Accumulation and cancellation are
  incompatible, exactly.

And the companion, from the other end of the same arithmetic: the product
formula splits into an arithmetic half and an accounting half, and the
accounting half needs no primes, no unique factorisation, no absolute
values, and no real numbers.  Leave the weights abstract and it holds for
any exponents whatsoever.  Its content:

  a defect at one place is not an absolute loss.  It is compensated, and
  the compensating term lives at a place the local method cannot see.



IV.  THE KERNEL'S SEMANTICS      and the statement about reward
------------------------------------------------------------------------------------------

अङ्कपाश, aṅkapāśa, "the net of digits", is Bhāskara II's Līlāvatī section
on permutations (~1150): the ARRANGEMENT, as against the count of
arrangements.  No verse number — editions differ in their numbering there.

  the collapse    eval : Tm → Env → ℕ, a readout into a set.
  what goes blind a transposition.  One ℤ/2 of holonomy.

no-counting-criterion-separates  —  for ANY type C at ANY level and ANY
function φ of the counting meaning, φ cannot distinguish performing the
commutation from doing nothing.  Universally quantified over every
possible readout, not over the ones anyone has tried.

comm-loop-is-a-nontrivial-loop-in-the-universe  —  and the categorified
semantics DOES see it.  The path is not refl, proved through uaβ, which is
univalence's β-rule COMPUTING.  Calculated, not asserted.

Commutativity of addition is not free information.  It is a ℤ/2 of
holonomy, and every readout valued in a set annihilates it.

  THE MACHINE-LEARNING FORM.  `install` makes a proved theorem a
  next-move, so an operation library is a learned policy.  A policy scored
  by any function of a numerical readout provably cannot represent WHICH
  ARRANGEMENT produced the number.  Order information is not an
  inefficiency of a bag-of-counts score.  It is provably absent from it.

  And with II: an architecture's invariance is exactly its blindness.  A
  model invariant under a symmetry cannot represent that symmetry's
  holonomy.  Inductive bias is not free capacity — it is paid for at a
  measurable rate, one ℤ/2 per independent loop.



V.  THE KERNEL AS A DISTRIBUTED SYSTEM    the same law, as a capability
------------------------------------------------------------------------------------------

  the collapse    derivation-sound lands in an identity type of ℕ, and ℕ
                  is a set, so that type is a PROPOSITION.
  what goes blind which route was taken.

two-nodes-cannot-disagree  —  any two derivations between the same terms
have EQUAL meanings.  Not compatible.  Not both acceptable.  Equal, as
terms.  A consensus protocol over meaning would range over a proposition,
and a proposition has no second position to elect.

  CONSENSUS ON MEANING IS NOT FORBIDDEN HERE.  IT IS VACUOUS.

merge-is-idempotent  —  the library join is grow-only, commutative and
idempotent, with no failure mode.  `merge` has no Maybe, no validity
precondition, no error, because a NativeOperation cannot be constructed
without a checked derivation.  A merge has nothing to validate.  Validity
is local to the operation and travels with it.

And what genuinely differs is kept: routes-genuinely-differ exhibits two
derivations of one fact with equal meanings and lengths 2 and 4, neither
wrong, and advance-preserves-branch-count is the rule that both survive
the merge.  A fork is not a disagreement awaiting a verdict.  It is two
carriers of one fact.


READ WITH III, THIS IS ONE OBJECT AND NOT AN ANALOGY.  The library merge
is an accumulative law in exactly SignIsNotAccumulable's sense.  So the
parity barrier applies to it verbatim:

  A CRDT CANNOT CARRY SIGN.

The sieve's blindness and the replicated library's freedom from conflict
are one idempotence, priced once as a loss and once as a guarantee.



SYĀT — THE CLAIM, EXACTLY
------------------------------------------------------------------------------------------

What IS claimed: the named terms exist, are checked, say what is written
above them, and are imported by one Agda module — so that module stops
compiling the moment any of them stops being true.

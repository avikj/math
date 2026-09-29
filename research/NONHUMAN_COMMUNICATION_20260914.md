# Non-human communication: the datasets, the literature, the mathematics, and what this corpus executes on them

*2026-09-14. Companion files: `communication/DATASETS_ANIMAL.md`,
`communication/DATASETS_PLANT_FUNGAL_MICROBIAL.md`,
`communication/MATHEMATICS_OF_NONHUMAN_COMMUNICATION.md`,
`communication/REGISTRY.json`; the executed work is in
`collab/bend2-cubical/biosemiotic/` (README there has every run).*

## 0. The claim, exactly

What was asked: find all animal / plant / fungal communication ("language")
datasets, the literature, and the mathematics; connect them to this corpus's
mathematical endgame (the elucidator, the fibre law, the superposition
computer); and execute.

What is delivered, and nothing more:

1. **A registry** of the public datasets across taxa and modalities (acoustic,
   gestural, chemical, electrical), with access URLs, sizes, annotation type,
   and whether sequence structure is annotated — and a registry of what is
   *not* public (`communication/`).
2. **The literature map by mathematical construct**: information theory
   (Zipf, Menzerath–Altmann, entropy rate, mutual-information decay), formal
   language theory (Chomsky-hierarchy tests, k-reversible automata,
   compositionality tests), sequence models and latent spaces, unsupervised
   alignment / "translation" mathematics (Procrustes, Gromov–Wasserstein,
   the isomorphism assumption and its documented failures), compression and
   algorithmic information, symbolic dynamics — and, per method, exactly which
   conclusions the mathematics licenses (`communication/MATHEMATICS_…md`).
3. **The mapping** from those constructs onto the corpus's checked objects (§2
   below). Every row names the corpus term it refers to; none of the rows
   asserts a theorem the corpus has not checked.
4. **Execution on real data** (§3): the elucidator factoring
   `coda ≃ (tempo, rhythm)` run on the 8,718-coda Dominica sperm-whale dataset
   (Sharma et al. 2024), exactly in integers, verified on every coda, and run
   on the HVM4 interaction-net runtime as one superposition: elucidation,
   spec-driven search with erasure of failing branches, transport along the
   tempo fibre, the rhythm *class* recovered as a quotient by a lens with the
   lens resolution measured, and the cost regimes of superposition measured
   (including the one where it loses). Two discrete systems (Japanese tit
   ordering rule, Campbell's monkey affixation) as superposed acceptors.

**Not claimed.** No new theorem is added to the cubical corpus in this pass
(the pinned Agda toolchain is not installed in this container; the executable
is the raw HVM4 net plus a Python reference, the same pair `SUPGEN_DEMO.md`
uses). No "translation" of any non-human signal into meaning is claimed: what
the mathematics below licenses, and what was executed, is the *factoring* of
signal spaces into transport-invariant shape × fibre, the *quotient* that a
class label is, and *transport* between representations along an equivalence
that must be **supplied** — the corpus's own abstract 52/53 discipline: the
extractor runs; the collision is given. Plant and fungal signal datasets are
registered but not executed (their hosts — figshare, Zenodo — are blocked from
this container; the animal data came from GitHub).

### 0.1 The registry in numbers (`communication/REGISTRY.json`)

208 dataset/resource entries (100 animal; 108 plant, fungal, microbial,
cross-kingdom and theory) and 183 mathematics references. Access: 107 open,
24 derived-only, 9 by request, 10 private, 6 catalogue-only, 45 with no
dataset at all (figures only), 7 unverified. Sequence structure annotated:
33 yes, 29 partial, 146 no. Signal paired with context / addressee /
referent: 70 of 208. **Open, sequence-annotated, and context-paired — the
intersection abstract 18's joint-reading construction needs — is 13
entries**: the Dominica coda dataset (executed on here), the two babbler
datasets, three chimpanzee / bonobo combination corpora, the honeybee
waggle-dance sets, BEBE, Khait's plant sounds, two small plant
electrophysiology sets, and two slime-mould behaviour sets. 23 of the 108
plant/fungal entries carry a published critique disputing the communication
claim. Of the mathematics references, 72 were verified by search this
session and 110 are recalled bibliographic details to be re-checked before
citation.

### 0.2 Corrections after reading the checked terms (added the same day)

The first draft of this document and of the biosemiotic README was written
from the abstracts and the Bend layer, not from the Agda. Reading the terms
changes three things, stated here so the rest is read correctly.

1. **Which "elucidator".** The coda factoring instantiates the fibre law —
   `Fibre.Carrier` (bind the output: `singl (f a)`, contractible),
   `SarvavibhagaH` (`A ≃ Σ[b] fiber f b` for every map; the image is the
   standpoint's quotient, the fibre is what it cannot see), and
   `Vishvayantra.lossless` — applied to the map `ICIs ↦ rhythm`. It mirrors
   `collab/bend2-cubical/elucidator.bend`, whose header says
   "compression-is-transport". It is **not** `Vivarana`, the corpus's
   elucidator proper: there, `AdiBija` proves the derivation type is
   *initial* (every receiver has exactly one fold) and `elucidate` returns a
   derivation's complete reading across a lens family (length, depth
   integral, meaning), each component certified unique by `fold-unique`.
   That is a statement about traces of the kernel, and nothing in the coda
   work touches it. Where the text below says "the elucidator" it means the
   fibre-law factoring.

2. **The lens table is `ApurvaIndriyam` measured.** `प्रवहति S q` (q descends
   along S, with the factoring map `h` as data) gives `तन्तौ-अन्धः`: a derived
   reading is blind inside its source's fibres, by two rewrites, with no
   hypothesis on any type. A coarser lens is post-processing of a finer one,
   so every row of the lens table is a dashboard of the row above and blind
   on its fibres; the "purity" column measures that blindness against the
   human annotation. And `अपूर्वम्` is the certificate for a new sense: a
   pair the present sensorium cannot split, which the proposal splits,
   refutes every possible derivation at once. The codas `1+1+3` and `5R1`
   are exactly such a pair for rhythm-as-sensorium and tempo-as-proposal
   (same rhythm at lens 10, tempos ≈1 s vs ≈0.33 s): tempo is not a reading
   of rhythm, and symmetrically rhythm is not a reading of tempo. Sharma et
   al.'s "two independent features" is an `अपूर्वम्` term on real data, and
   the annotated `CodaType` is a dashboard of the joint reading.

3. **The exchange result is a shadow argument, and its object is the
   h-level of the event datum.** `NerodeYantra` proves: when the next
   observation factors through the current one (`out ∘ δ ≡ g ∘ out`, the
   observation a coalgebra homomorphism), the whole Nerode relation is the
   kernel of one observation, as an equivalence of types. On the whale
   exchange the shape channel nearly satisfies this (preserved 51 % of
   steps against 37 % null) and the tempo channel does not (median drift
   17 ms is small but not zero, and not a function of the previous coda):
   the exchange's state exceeds its readout, so no finite window of codas
   is Nerode-complete for it. The measurement itself uses the method of
   `HLEVEL_OF_INTERACTION` §4: a set-valued invariant (shape kept, signed
   drift) separates steps without computing the h-level of the interaction's
   event datum. What the corpus makes precise, and the field has no word
   for, is that question: modelled as `Fibre.Samvada`'s `ISC`, an exchange
   is contractible (a service, `एक-नेत्रम्`) iff its event datum is a
   proposition, and branches iff the datum is proof-relevant
   (`वर्धन-बहुत्वम्`). "Is the other whale a generator or a service to this
   one" is an h-level, and the drift table is its decategorified shadow.

Everything below stands with those readings substituted.

## 1. What the corpus has that the field is reaching for

The field's stated program (Andreas et al. 2022 iScience, the CETI roadmap;
Earth Species Project) is: collect signal corpora → discover units → find
sequential/combinatorial structure → ground units in behavioural context →
"translate". Its mathematics, as actually used, is: clustering (units),
information theory (structure), latent embeddings (representation), and
cross-space alignment (translation). Each of these is a **projection** in the
README's sense (`weight = π(trace)`): a scalar or a point summarising a
process, with the process discarded.

The corpus holds, as checked terms, the objects those projections discard:

| corpus object | where | what it is |
|---|---|---|
| the fibre law `A ≃ Σ B (fiber f)` | `fibre/src/Fibre/Carrier.agda`; `collab/bend2-cubical/fibrelaw.bend` (35 ✓, runs on the net) | every map factors losslessly as (its visible projection, the fibre it forgot); the completion is unique (contractible) |
| the elucidator `m ≃ (start, shape)` | `collab/bend2-cubical/elucidator.bend`, `supfugue.bend`; abstract 50 | a sequence is its transport-invariant shape plus the fibre saying which transport; every fugue voice is one subject transported |
| observational equivalence is the truncation | abstracts 06, 12, 16, 22 | any evaluator into a discrete outcome domain factors through `‖derivation‖`; no function of the outcome separates two routes to it; the class is the *quotient*, the route is the fibre |
| the Nerode congruence computed | abstract 15; `port/MyhillNerodeMinimalMachine.bend` | the minimal observable state of a sensor family is an equality of types, not a bound; two readings each blind can be jointly faithful (abstract 18) |
| the unbounded fibre under pruning | abstracts 16, 28 | dedup / clustering selects one representative of an unbounded family by a criterion that is provably not a function of behaviour; counts, lengths and meaning are three different orders |
| superposed evaluation with erasure | `supgen_synthesize.hvm4`, `SUPGEN_DEMO.md`, `PUSC.md` | a candidate family is one term; a spec runs over it once with shared work; failing branches annihilate; survivors arrive certified by the erasure |
| transport across `ua` | `chain.bend`, `uaequiv.bend`, `RUNTIME_ALGEBRA.md` | a proved equivalence is a runtime path; moving data along it is a reduction; composite / inverse / Π / Σ lines run on the net |
| the lens as the observer boundary | abstract 45 | a quotient is lossless for the declared exact observers and lethal to the undeclared ones; quotienting before declaring the observer class is the error |
| generalisation vs shareability | abstract 03 | a skill carrying its training-state identification fires at exactly one state; the generalising form fires everywhere and costs nothing |

## 2. The mapping, construct by construct

Each row: the field's construct → what it computes → the corpus reading → what
that reading *adds or forbids*. Citations to papers are in
`communication/MATHEMATICS_OF_NONHUMAN_COMMUNICATION.md`.

### 2.1 Zipf / Zipf–Mandelbrot / Menzerath–Altmann fits

*Computes:* a rank–frequency (or length–constituent) slope over a unit
inventory; used as a "language-likeness" score (McCowan–Hanser–Doyle 1999 on
dolphin whistles; Semple 2010 gelada; Heesen 2019 chimp gesture; Youngblood
2024/Arnon 2025 humpback song; Ferrer-i-Cancho's critiques).

*Corpus reading:* a generating function of the unit-count fibre. Abstract 21:
"a generating function does not determine a bijection, and the difference is
a group action". A Zipf slope is a decategorified count; two inventories with
the same slope may differ by any relabelling and any grammar. Abstract 28:
cardinality is the wrong measure — "how many units", "how long is this
utterance", and "what does the family mean" are three orders on one object.

*What it forbids:* inferring structure (let alone meaning) from the slope.
The field's own critiques (Ferrer-i-Cancho; the random-typing argument) say
the same in statistical terms; the corpus says it as a type: the slope is a
function out of a truncation.

### 2.2 Entropy rate, Markov order, mutual-information decay

*Computes:* conditional entropies `H(x_n | x_{n-k}…x_{n-1})` and their limit;
MI(k) between symbols at distance k (Sainburg et al. 2019: power-law decay in
birdsong and speech; Kershenbaum 2014: vocal sequences are not the Markov
chains they were thought to be — renewal / hierarchical processes fit better).

*Corpus reading:* an entropy is `π(trace)` for the observer "next-symbol
predictor at window k". The Nerode congruence (abstract 15) is the exact
version: the minimal state is the kernel of the joint observation, and
whether the next observation factors through the current one *is* the
Markov question, decided as an equivalence of types rather than estimated.
Kershenbaum's finding that a renewal process fits better than a Markov chain
is, in this vocabulary, the statement that the observable *does not* factor
through the last k symbols — the Nerode class is larger than any k-window.

*What it adds:* the minimal automaton is computed, not fitted; two
observation families with the same lcm (same kernel) are indistinguishable by
theorem (abstract 15's "same multiple, same observations").

### 2.3 Formal-language tests and "syntax"

*Computes:* whether animals discriminate strings of an (AB)ⁿ vs AⁿBⁿ grammar
(Fitch & Hauser 2004; Gentner 2006; the Beckers–Berwick–Bolhuis critique that
finite-state strategies suffice for every published result); k-reversible
automata for birdsong (Berwick et al. 2011); ordering rules with behavioural
readout (Suzuki 2016 Japanese tit ABC-D; Engesser 2016).

*Corpus reading:* every one of these is an acceptor and its Nerode classes.
`collab/bend2-cubical/biosemiotic/tit_syntax.hvm4` runs the tit ordering rule
as a two-state acceptor over a superposition of candidate utterances: the
ungrammatical ones erase. The critique (finite-state suffices) is abstract
16 seen from the other side: the behavioural specification (accept / reject
on the tested strings) does not determine the grammar — the fibre of
grammars over the spec is unbounded, and "context-free" is a selection
inside that fibre by a criterion that is not a function of the behaviour.

*What it forbids:* attributing a grammar class from a finite accept/reject
table. What it adds: the ordering rule itself is an executable object that
composes (a spec over a superposition), not a p-value.

### 2.4 Compositionality tests (Berthet 2025 bonobo; Leroux 2023 chimp; Girard-Buttoz 2022)

*Computes:* whether the "meaning" (a behavioural-context vector) of a
combination is a function of the meanings of its parts — trivial (additive)
vs non-trivial (one part modifies the other) — via distances in a
context-feature embedding.

*Corpus reading:* compositionality is exactly "the readout factors through
the parts": `read(AB) = φ(read A, read B)`. The fibre law says every map
factors, and the question is only whether the factoring's fibre is
contractible (trivial composition) or not (the residue is where the
non-trivial part lives, `śeṣa`). Abstract 18 gives the shape: two readings
each blind that are jointly faithful — the pair carries what neither
component does.

*What it adds:* the test is a fibre-contractibility question, decidable on a
finite context table, rather than a distance threshold in an embedding.
The published critique of the bonobo result (Wartel et al. 2026, *PeerJ*
14:e21651: re-running the multiple-correspondence-analysis pipeline on
randomised data gives 35–84 % false positives; a permutation test that
recomputes the embedding gives p = 0.26) is the lens warning of abstract 45
in statistical form — the quotient (the embedding) was taken before the
observer class (the null that preserves the dependence structure) was
declared.

### 2.5 Latent spaces, UMAP / VAE repertoires, foundation models

*Computes:* a point per vocalisation (Sainburg 2020; Goffinet 2021; AVES,
BioLingual, NatureLM-audio, animal2vec); clusters = units; distances =
similarity.

*Corpus reading:* the embedding is a map `f : Signal → ℝⁿ`; the fibre law says
the lossless object is `Σ (y : ℝⁿ). fiber f y`, and the embedding alone is
lossless iff every fibre is a point. It never is (the encoder is a
projection by construction). Clustering on the embedding is the merge that
abstract 07/16's scheduler is forbidden to perform: it selects a
representative of the fibre. The corpus does not say "do not cluster"; it
says (abstract 45) declare the observer class first — the quotient is lossless
for exactly the observers that factor through it and lethal to the rest.

*What it adds:* a per-lens accounting. §3.3 below performs it on the whale
data: the number of shape nodes as a function of lens resolution, the purity
of each node against the human annotation, and the discovery that the
annotation mixes shape with fibre.

### 2.6 Alignment / "translation" (Conneau–Lample 2018; Alvarez-Melis–Jaakkola 2018; Søgaard–Ruder–Vulić 2018; Earth Species Project; CETI)

*Computes:* an orthogonal map (Procrustes) or an optimal-transport coupling
(Gromov–Wasserstein) between two embedding spaces, assuming they are
approximately isomorphic; adversarial refinement without parallel data.

*Corpus reading:* this is transport along `ua(e)` for an equivalence
`e : A ≃ B` — the README's "certified equivalence induces a path; a value
crosses the representation boundary by transport". The unsupervised
literature's "isomorphism assumption" is the assumption that `e` *exists*;
its documented failures (non-isomorphic spaces across typologically distant
languages, Søgaard 2018; Vulić 2020) are the statement that the fibre of the
best alignment is not contractible. Gromov–Wasserstein is a scalar
(`π(trace)`) of the relational structure; the corpus keeps the coupling as
the object. Abstract 24 (cost and inverse cannot coexist) and abstract 30
(the transpose is a dagger, never an inverse) bound what a learned map can be:
a Procrustes solution is a dagger; the inverse exists only on the
contractible-fibre locus.

*What it forbids:* calling a Procrustes/GW alignment a translation. What it
adds: when an equivalence *is* supplied (a proved one, or one certified by a
round trip on the data), transport along it runs on the net, composes, and
inverts (`chain.bend`; §3.4 executes the tempo-fibre transport on real
codas). The discipline is abstract 52/53's: the extractor is a function; the
collision — here the equivalence between two species' signal spaces — is
**given**, and finding it is the frontier the field names honestly (Yovel &
Rechavi 2023; Rendall–Owren–Ryan 2009's "influence, not information").

### 2.7 Compression, MDL, algorithmic information

*Computes:* Lempel–Ziv / NCD / grammar-induction (ADIOS) complexity of a
sequence corpus as a structure measure; MDL for repertoire size.

*Corpus reading:* "compression is transport" — `elucidator.bend`'s header. A
compressor that keeps the decoder is a lossless factoring; its "subject" is
the shape and its dictionary is the fibre; abstract 20: the deduplication
store is the expensive object. Kolmogorov complexity of a single string is
the length lens of abstract 50 (the elucidator's three lenses: length, depth,
meaning — the length lens separates routes the meaning lens identifies).

### 2.8 Plant electrophysiology and fungal spike trains (Adamatzky 2022; Volkov; Khait 2023)

*Computes:* spike detection, inter-spike-interval clustering into "words",
word-length distributions compared to human languages.

*Corpus reading:* identical to the coda case — inter-spike intervals are
inter-click intervals; the "word" is a lens quotient on the interval vector;
the Zipf comparison is §2.1. The executed coda pipeline applies verbatim to
Adamatzky's Zenodo recordings (records 5790768, 3997031, 1451496) and to
Khait et al.'s plant ultrasonic clicks (Dryad 10.5061/dryad.jwstqjqf7) once
fetched (blocked here; see the registry's access column). The sceptic
literature — Blatt, Pullum, Draguhn, Bowman, Robinson & Taiz 2024 (*Fungal
Ecology* 68:101326: the "words" are analyst-chosen thresholds on a signal
that may be electrode artefact, with no receiver test); Buffi et al. 2025
(*FEMS Microbiol. Rev.*: shielding, drift, no identified channel); Karst,
Jones & Hoeksema 2023 on mycorrhizal-network overclaims — is the lens
warning of abstract 45 in biological dress: the word boundary is a lens,
the lens was not declared, and the Zipf-like length distribution that
survives it is §2.1's decategorified count. The one independent,
Faraday-caged confirmation that *some* fungal electrical activity is
biological (biocide-sensitive) is Buffi et al. 2025 *iScience* 28:113484.

### 2.9 The receiver's invariances, not the analyst's

The elucidator's "shape" is whatever the declared transport leaves fixed.
For codas the transport is tempo scaling and the invariant is Sharma et
al.'s rhythm, which their playback-free analysis treats as the whales'
category; the biology has not yet tested it by playback. For birdsong the
obvious transport (pitch transposition) is the wrong one: starlings
generalise on spectral shape, not pitch (Bregman, Patel & Gentner 2016,
*PNAS* 113:1666), and songbirds weight absolute pitch far more than humans
(Hulse & Cynx 1985; Weisman et al. 2004). A factoring is a claim about
which fibre the receiver discards; the corpus can compute any declared one
and certify its losslessness, but which one is *the animal's* is an
empirical datum the registry's "pairs signal with context" column tracks.

## 3. What was executed (summary; details and every number in `collab/bend2-cubical/biosemiotic/README.md`)

### 3.1 The factoring is an identity on real data

Dominica codas (8,718 rows; 8,696 with all intervals present), intervals in
ms, exact shape = vector / gcd, fibre = gcd: `coda == gcd * shape` for
8,696 / 8,696. On the HVM4 net, `coda_exact_roundtrip.hvm4` reconstructs an
18-coda superposition from its `#Coda{fibre, shape}` pairs and returns 1 on
every branch (1,624 interactions).

### 3.2 The elucidation over a superposition

`@elucidate = λ&c. #Coda{@tempo(c), @shape(c)}` over 18 real codas as one
`&L{…}`: 18 `#Coda{tempo, rhythm}` terms in one pass (3,843 interactions).

### 3.3 The class is the lens (the substantive result)

At the data's own resolution, 8,696 codas are 8,440 distinct exact shapes.
The 34 annotated rhythm types are a quotient by a coarser observation. The
lens table (EC1 clan, 7,268 non-noise codas):

| lens R (bins / unit) | shape nodes | largest node | purity vs annotation |
|---|---|---|---|
| 1000 | 6,950 | 3 | 0.999 |
| 100 | 3,086 | 86 | 0.935 |
| 20 | 632 | 1,428 | 0.869 |
| 10 | 216 | 3,230 | 0.727 |
| 3 | 97 | 2,702 | 0.701 |
| 2 | 45 | 4,741 | 0.422 |

At R = 10 the largest node `(3,3,2,2)` holds 2,068 codas annotated `1+1+3`
and 1,136 annotated `5R1`: same rhythm, different tempo (≈1 s vs ≈0.33 s).
**The human annotation scheme mixes shape with fibre**; the factoring
separates them, recovering Sharma et al.'s own rhythm × tempo independence
from the raw intervals with no clustering. On the net (`coda_lens10.hvm4`)
the collapse prints equal terms for codas of one class.

### 3.4 Search inside evaluation, and transport along the fibre

`coda_spec.hvm4`: keep the codas whose R = 10 shape is `[3,3,2,2]`; the rest
erase. Survivors: one 1+1+3 coda and two 5R1 codas (2,745 interactions), the
answer certified by the erasure. `coda_transport.hvm4`: a 5R3 coda's rhythm
at a 5R1 coda's tempo → `[83,81,81,84]` beside the real 5R1 `[81,77,74,80]`:
"5R1 is 5R3 transported along the tempo fibre", computed.

### 3.5 Cost regimes, measured honestly

18 independent codas down 18 independent lines: superposed 2,803 vs separate
1,326 interactions (ratio 2.11 — superposition **loses**, as
`SYNTHESIS.md` §4 predicts for branches that share no work). Plain vs
ornamented coda (shared prefix, superposed tail): 1,230 vs 1,164 (1.06,
break-even: the prefix sum is shared, the normalisation is not). The
saving the corpus measured (one line over many values, 0.37 at N = 8) is not
available for factoring independent signals; it is available for moving a
batch of signals along one proved equivalence, which is the translation
step, not the factoring step.

### 3.6 The exchange: rubato is the fibre moving while the shape holds

On the dataset's temporally ordered file (3,840 codas with whale identity
and onset time), consecutive codas by one whale within 6 s preserve the
lens-10 shape in 51.0 % of steps (null, random same-whale pairs: 36.9 %),
and when the shape is preserved the tempo moves by a median of 17 ms (null:
116 ms). That signed, small motion of the fibre along the interaction
history is Sharma et al.'s rubato, read off the factoring with no feature
engineering: the exchange is a braid (README §13) whose steps transport the
shape and move the fibre. `coda_exchange.hvm4` runs 16 real consecutive
pairs as one superposition through `@step`, returning each step's transport
witness `#Step{shapeKept, drift}` as data (9,178 interactions; every branch
agrees with the Python table).

### 3.7 The whole instrument (details and tables in the biosemiotic README §8)

- **The rhythm types are Piṅgala metres.** Reading each coda's intervals in
  units of its shortest interval gives a laghu/guru word; `1+1+3` is GGLL
  (95 %), the 5R types are LLLL, 4D is GLL, 7D1 is GGGLLL. The repertoire
  occupies 14 of the 16 four-syllable metres and, by mātrā weight, 8/8,
  9/13, 16/21, 19/34 of Virahāṅka's counts at weights 5–8, thinning above.
  On the net the prastāra of 16 metres is sorted into its Meru cells in one
  pass and a spec keeps the three metres the whales use most.
- **The readout does not factor along time.** H(next | current) is 2.48
  bits against a 3.46-bit null with 257 classes; the next class is the
  likeliest one in 54 % of steps where `NerodeYantra`'s factoring would give
  100 %. A k = 1 acceptor learned from half the dialogues and run on the net
  accepts 4 of 10 held-out sequences.
- **What crosses between whales is the metre, at the receiver's tempo.**
  Cross-whale steps keep the fine shape at the null rate (19–23 % vs 19 %)
  but keep the metre in 51 % of steps (null 36 %), re-expressed 8 % apart
  in tempo (2 % within a whale, 21 % at random); overlap makes no
  difference. The encounter transports a coarser invariant than the one a
  single whale conserves.
- **Sign birth.** A two-part description length of the corpus is minimal
  near lens 8 with about 140 signs (25.5 bits per coda); adding signs pays
  until then and costs after.
- **The Zipf slope is the lens's.** It runs from −2.0 at lens 2 to −0.1 at
  lens 1000 on the same codas.
- **Rubato's modulus.** Relative |Δtempo| per same-whale step with the
  shape kept: median 2.1 %, p99 13 %.
- **Two blind readings, jointly faithful (abstract 18).** Against the
  24 annotated types, metre alone is blind on 464 of 10,000 pairs and tempo
  alone on 1,054; the joint reading is blind on 2, with purity 0.992. The
  annotation is the joint of two readings neither of which descends along
  the other.
- **The tempo is state (`ObservabilityQuotient`).** Bisimulation refinement
  of the empirical machine (285 metre × tempo-bin states, readout = metre)
  keeps 280 classes: every frequent metre's tempo variants are separated
  by their futures (GGLL's four bins into four blocks). The fibre carries
  state along the run; metre alone is not a safe quotient.
- **The arrow of time (`theorems/primes/pair_field/ReversalInvariant`).** Every scalar reading is
  reversal-blind; the metre is blind only on its 1,794 palindromes
  (24.7 %), the exact shape on 7 codas. GGLL occurs 3,661 times, LLGG 0:
  the whales' metres front-load the long intervals.
- **The run is partly its answer stream (`Prasna`).** H(B_next) 3.81 bits
  falls to 2.28 given A's last coda, to 1.24 given B's own last, to 0.77
  given both. The answer adds 0.48 bits beyond own state; own state adds
  1.51 beyond the answer.
- **Order inside the Meru cell (`KramaNairapeksya`).** Every scalar
  reading is a total and blind to all permutations; the cell (n, k) is
  the orbit. H(metre) = H(cell) 3.06 + H(arrangement | cell) 0.38 bits,
  against 1.81 available: the whales use one arrangement per cell (GGLL
  3,726 of 3,754 in (4,2)) and spend the order channel only in (4,1),
  (4,3), (6,3).
- **Born signs, per sign (hieroglyphics II).** 77 of 204 metres earn a
  sign-table entry; every human-named metre is among them, and 65 born
  signs have no human name (GLLL 350, LGLL 211 the largest).
- **The two clans differ in the fibre at the metre lens, and not below
  it.** I(clan; metre × tempo) is 0.42 of 0.50 bits; inside the shared
  metre LLLL, tempo alone carries 0.84 of 0.94 bits (EC1 at 329 ms, EC2
  at 1,133 ms). But at lens 10 EC1's `5R1` is [3,3,2,2] (accelerating,
  last/first 0.73) and EC2's `5R3` is even ([2,2,3,3], 1.04), overlap
  0.16. Transport with a 6 ms spec inside the evaluation erases every
  branch: 0 of 623 `5R3` codas translate to a `5R1`. The translation
  exists at one lens and not at another.
- **The round trip (`Ekatva`).** Through another whale's tempo and back,
  the exact shape returns the coda on 68 % of codas and misses by 0.8 ms
  on the rest: the millisecond grid is a lens too.
- **Distance from one execution (`Niyati`).** H(next | current) 1.77
  bits over 82 runs (null 3.41); three of 57 runs are a point; the
  support allows 3.7 bits of branching per step, the whales realise 1.8.
- **Hiding and hardness.** Hiding the tempo from the metre reading costs
  0.19 bits per step of next-metre prediction; hiding the metre from the
  tempo reading costs 0.21 bits of next-tempo prediction.
- **Ornamentation as a shared line: not confirmed.** On 409 neighbouring
  pairs differing by one click, the ornamented coda's prefix carries the
  neighbour's shape at 48 % (null 59 %) at lens 4 and 28 % (null 19 %) at
  lens 10; the dialogue file lacks the annotation Sharma's ornament is
  defined against.

### 3.8 Discrete systems

Japanese tit ABC-D ordering rule as a Nerode acceptor over six candidate
utterances: `[D,ABC]` and `[D]` erase, four survive (514 interactions).
Campbell's monkey `-oo` affixation: six calls factored to `#Call{root,
affix}` in one pass (114 interactions).

## 4. The frontier, stated exactly (what would make "translation" a term)

Translation between signal spaces `A` (species / individual / context 1) and
`B` (2) is, in this calculus, `transport(ua e)` for `e : A ≃ B` — or, when no
equivalence exists, the fibre law's completion `A ≃ Σ b:B. fib_f(b)` for a
map `f`, with the residue `fib_f` carried rather than dropped. Three things
are therefore required, and the corpus supplies the first two:

1. **The factoring of each space** into shape × fibre by its own
   transport-invariants (executed above for temporal codas; the same program
   applies to any interval sequence, and to symbol sequences via the
   acceptor).
2. **The transport machinery** once `e` is given (`chain.bend`,
   `uaequiv.bend`, `fibrelaw.bend`: composite, inverse, Π/Σ lines, all on
   the net).
3. **The equivalence `e` itself**, or the map `f` and its grounding. This is
   the field's open problem and it is not a computation over the signal
   corpus alone: abstracts 06/12/22 prove that no function of the outcome
   (behaviour, context vector, embedding) selects the route; Piantadosi–Hill
   2022 and Mollo–Millière 2023 say the same about distributional meaning.
   What the corpus adds is the *shape* of the missing datum: it is a fibre
   over the behavioural readout, and abstract 18 says two blind readings
   (e.g. acoustic structure and behavioural context) can be jointly faithful
   where each alone is not. That is a concrete instruction for dataset
   design — record the paired readings, not the marginals — and every
   dataset in the registry is tagged by whether it does.

Absences the survey established, each a construction the corpus could
supply because it already holds the object: no peer-reviewed application of
ε-machines / computational mechanics, of persistent homology, of normalised
compression distance, or of ADIOS-style grammar induction to any animal
vocal repertoire; no CETI or Earth Species Project paper that performs an
actual cross-species embedding alignment (the "translation" framing lives
in programme statements). The Nerode machine (abstract 15) *is* the
ε-machine's causal-state construction done as an equality of types, and
`port/MyhillNerodeMinimalMachine.bend` runs it.

Next constructions, in order: (i) the coda pipeline as a Bend2 file under
`--total` with the per-mille lens as a `Path` (the Python + raw-HVM4 pair
here is the same trust level as `SUPGEN_DEMO.md`; the cubical certificate is
the next rung); (ii) the same run on Adamatzky's fungal inter-spike intervals
and Khait's plant ultrasonic emissions when the hosts are reachable; (iii)
the Nerode machine of `port/MyhillNerodeMinimalMachine.bend` instantiated on
Bengalese-finch syllable sequences (Koumura 2016; Nicholson 2017) — the
k-reversible claim of Berwick 2011 as a computed minimal automaton rather
than a fitted one; (iv) the joint-reading construction of abstract 18 on a
dataset that pairs signal with context (the registry marks which do).

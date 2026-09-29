# biosemiotic — the fibre-law factoring run on real non-human communication data, on the net

*Naming, corrected after reading the Agda: what runs here is the fibre law
(`fibre/src/Fibre/Carrier.agda`, `SarvavibhagaH`, `Vishvayantra.lossless`)
applied to the map ICIs ↦ rhythm, in the form `../elucidator.bend` gives it.
It is not `formal/cubical/kernel/Vivarana`, the corpus's elucidator proper,
which is the unique fold of the initial derivation type (`AdiBija`) across a
lens family. The lens table in §3 is `ApurvaIndriyam` measured (a coarser
lens descends along a finer one and is blind on its fibres; `1+1+3` vs `5R1`
is an `अपूर्वम्` pair certifying tempo as a sense distinct from rhythm), and
§7 is a `NerodeYantra` failure measured through a set-valued shadow. See
`research/NONHUMAN_COMMUNICATION_20260914.md` §0.2.*

The corpus's factoring `m ≃ (start, shape)` (`../elucidator.bend`, the fibre law
`A ≃ Σ B (fiber f)` of `../fibrelaw.bend`) applied to published animal
communication data, executed on the real HVM4 interaction-net runtime
(HigherOrderCO/HVM4, `gcc -O2 -o src/hvm src/hvm.c`), with the same program
shape as `../supfugue.bend` and `../supgen_synthesize.hvm4`: the whole sample
is handed in as ONE superposition, the factoring commutes over it, failing
branches erase, and the survivors are enumerated by `-C`.

Every number below was produced by running the files in this directory; the
runs are reproduced by

    HVM=/path/to/hvm4/src/hvm python3 coda_elucidator.py DominicaCodas.csv   # writes out/*.hvm4 and runs the analysis
    HVM=/path/to/hvm4/src/hvm python3 coda_regimes.py                       # writes out/RESULTS_regimes.txt
    hvm tit_syntax.hvm4 -s -C20 ; hvm campbell_affix.hvm4 -s -C20

`DominicaCodas.csv` is the public dataset of Sharma, Gero, Payne, Gruber, Rus,
Torralba & Andreas, *Contextual and combinatorial structure in sperm whale
vocalisations*, Nature Communications 15:3617 (2024), from
https://github.com/pratyushasharma/sw-combinatoriality (Dominica Sperm Whale
Project, 2005–2018; 8,718 codas; nine inter-click-interval columns; annotated
`CodaType`; clan; social unit). The paper's own factoring of a coda into
**rhythm** (the inter-click-interval vector normalised by total duration,
tempo-invariant) and **tempo** (the duration) IS the elucidator's
(shape, fibre) reading: shape = rhythm, fibre = tempo.

## 1. The factoring is an identity on every real coda (Python, then the net)

Inter-click intervals in milliseconds; exact shape = the vector divided by its
gcd; fibre = the gcd. `coda == gcd * shape` holds for **8,696 / 8,696** codas
(22 rows with a zero/absent interval are excluded). On the net,
`out/coda_exact_roundtrip.hvm4` reconstructs each coda of an 18-coda
superposition from its `#Coda{fibre, shape}` pair and compares it structurally
(`===`) with the original: **1 on every branch, 1,624 interactions** total.

## 2. The elucidation runs over the superposition (`out/coda_superposition.hvm4`)

18 real codas (types 5R3, 1+1+3, 4R2, 5R1, 3R, 4D; three each) as one
`&L{…}` superposition; `@elucidate = λ&c. #Coda{@tempo(c), @shape(c)}` applied
once. Output (collapse): 18 `#Coda{tempo_ms, rhythm_permille}` terms,
3,843 interactions. `out/coda_shape_only.hvm4` reads only the shape: 2,803.

## 3. What the data actually says about "the rhythm class" — the lens result

At millisecond resolution almost every coda is its own shape node:
8,696 codas → **8,440 distinct exact shapes** (8,360 per-mille rhythms); only
252 exact shapes carry more than one coda, and those are mostly literal
repeats at the same tempo. The annotated rhythm *classes* (34 `CodaType`
labels; 24 non-noise in clan EC1) are therefore **not** an identity of shapes
at the data's own resolution. They are a quotient by a coarser observation —
exactly the corpus's statement that the class lives in the lens, and the exact
fibre is unbounded (abstract 16, "pruning by observational equivalence
collapses an unbounded fibre"). Reading the 7,268 EC1 non-noise codas through
lenses of decreasing resolution R (bins per unit of normalised duration):

| lens R | shape nodes | largest node | purity (nodes of one annotated type) |
|---|---|---|---|
| 1000 | 6,950 | 3 | 0.999 |
| 200 | 5,066 | 17 | 0.979 |
| 100 | 3,086 | 86 | 0.935 |
| 50 | 1,632 | 333 | 0.886 |
| 20 | 632 | 1,428 | 0.869 |
| 10 | 216 | 3,230 | 0.727 |
| 5 | 160 | 3,002 | 0.800 |
| 3 | 97 | 2,702 | 0.701 |
| 2 | 45 | 4,741 | 0.422 |

At R = 10 the largest node, shape `(3,3,2,2)`, holds 2,068 codas annotated
`1+1+3` and 1,136 annotated `5R1`: the two annotated types have the SAME
rhythm and differ in TEMPO (1+1+3 ≈ 0.8–1.2 s; 5R1 ≈ 0.33 s). The annotation
scheme mixes the shape with the fibre; the factoring separates them. This is
Sharma et al.'s own finding (rhythm × tempo are independent axes) recovered
from the raw intervals by the elucidator with no clustering step.

`out/coda_lens10.hvm4` runs the R = 10 lens over the 18-coda superposition on
the net (2,813 interactions): the collapse prints equal terms for codas of one
class — `[3,3,2,2]` three times, `[5,3,2]` three times, `[4,3,3]` and
`[3,2,2,3]` twice.

## 4. Search inside evaluation (`out/coda_spec.hvm4`) and transport (`out/coda_transport.hvm4`)

Spec: keep the codas whose R = 10 shape is `[3,3,2,2]`; every other branch
erases (`&{}`). Survivors: the 1+1+3 coda `[242,231,171,145]` and the two 5R1
codas `[89,92,77,71]`, `[102,95,75,66]` — 2,745 interactions for the whole
search, the answer certified by the erasure of the alternatives (SupGen's
mechanism, `../SUPGEN_DEMO.md`).

Transport along the fibre: the rhythm of a 5R3 coda (`[357,350,347,363]`,
tempo 1,417 ms) re-expressed at a 5R1 coda's tempo (329 ms) gives
`[83,81,81,84]` (148 interactions) — next to the real 5R1 coda
`[81,77,74,80]`. "5R1 is 5R3 transported along the tempo fibre" is the
dataset's own naming (5 regular clicks, tempo 1 vs 3) computed rather than
annotated.

## 5. Cost regimes, measured (the honest part; cf. `../SYNTHESIS.md` §4)

| regime | superposed | separate | ratio |
|---|---|---|---|
| 18 different codas down 18 different lines (R = 1000 lens) | 2,803 | 1,326 | **2.11** |
| plain coda vs its ornamented twin (shared prefix, superposed tail), 6 pairs | 1,230 | 1,164 | **1.06** |

Superposition does **not** pay for factoring independent codas: the branches
share nothing, and the corpus's measured penalty for that regime (~1.4×)
reappears here larger (2.1×) because the per-branch work is tiny. The
ornamentation case (Sharma et al.'s ornament = an extra terminal click; the
plain and ornamented coda share every interval but the last) shares the prefix
sum but not the normalisation, whose divisor differs — break-even. The sharing
that pays is one LINE over many values (a proved equivalence moving a batch),
not many values down many lines. The claim this directory supports is
therefore exactly: the factoring, the class-as-lens, the spec-search and the
transport all *run* on the net over real data; the parallel-superposition
saving is available only where downstream work is invariant across branches.

## 6. Discrete syntax: two more published systems, hand-encoded

`tit_syntax.hvm4` — Japanese tit call combinations (Suzuki, Wheatcroft &
Griesser 2016, Nature Communications 7:10986): ABC-D is understood, D-ABC is
not. The ordering rule as a two-state acceptor (the Nerode classes) run over a
superposition of six candidate utterances: survivors `[ABC,D]`, `[ABC]`,
`[ABC,D,ABC,D]`, `[ABC,ABC,D]`; `[D,ABC]` and `[D]` erase. 514 interactions.

`campbell_affix.hvm4` — Campbell's monkey `-oo` suffixation (Ouattara,
Lemasson & Zuberbühler 2009, PNAS 106:22026): six calls as one superposition
factored to `#Call{root, affix}` in one pass, 114 interactions.

Both are the elucidator on symbols instead of intervals; neither adds a claim
beyond the published finding it encodes.

## 7. The exchange: rubato is the fibre moving while the shape holds (`coda_exchange.py`, `out/coda_exchange.hvm4`)

The dataset's second file, `sperm-whale-dialogues.csv` (3,840 codas, 2014–2018,
with whale identity, recording and onset time), is the temporally ordered
subset. Sharma et al. define **rubato** as the smooth drift of tempo across
consecutive codas of one rhythm by one whale inside an exchange. In the
corpus's terms an exchange is an interaction history (README §6, §13);
consecutive codas are its states; the interaction's transport witness at
each step is *what stayed* (the shape) and *what moved* (the fibre).

Measured on the 2,637 consecutive same-whale coda pairs within 6 s (Sharma
et al.'s window), against a null of random same-whale pairs:

| | consecutive pairs | random same-whale pairs |
|---|---|---|
| lens-10 shape preserved across the step | **51.0 %** (1,344 / 2,637) | 36.9 % |
| median \|tempo drift\| when the shape is preserved | **17 ms** | 116 ms |
| median \|tempo drift\| when the shape changes | 34 ms | — |

The shape crosses the step more often than chance and, when it does, the
fibre moves by a few percent of the tempo: that small, signed motion of the
fibre along the braid *is* rubato, read off the factoring with no feature
engineering. On the net, `out/coda_exchange.hvm4` hands 16 real consecutive
pairs (8 shape-kept, 8 shape-changed) to one function `@step` returning
`#Step{shapeKept, drift}` per interaction step — the transport witness of
each step as data — 9,178 interactions; every branch agrees with the Python
table in `out/exchange_pairs.tsv`. (Structural `===` on two lazily built
lists stays stuck under a superposition in collapse mode; list equality is
therefore written as a strict recursion, `@eqL`.)

## 8. The whole instrument, run (`full_instrument.py`, `nerode_net.py`; log in `out/instrument_run.log`)

Each reading below is named by the checked term that licenses it. All
numbers are from one run on the two public files.

### 8.1 The rhythm types are Piṅgala metres (`theorems/metre`: `MatraVarnaGuru`, `PrastaraPankti`, `Matramerus`, `Meru`)

Read each coda's intervals in units of its shortest interval: an interval of
one unit is laghu, of two or more is guru. A coda is then a laghu/guru
word, a mātrā-vṛtta, and its mātrā is `matraOf` (laghu 1, guru 2). The
annotated rhythm types come out as single metres with no clustering:

| annotated type | dominant metre | share | distinct metres |
|---|---|---|---|
| 1+1+3 | GGLL | 0.95 | 5 |
| 5R1 / 5R2 / 5R3 | LLLL | 0.56 / 0.99 / 0.99 | 10 / 3 / 3 |
| 4R2 | LLL | 0.98 | 4 |
| 4D | GLL | 0.65 | 3 |
| 7D1 | GGGLLL | 0.44 | 10 |

The repertoire against Piṅgala's counts: for 4-interval codas (6,383 of
them) the whales use 14 of the 16 metres of saṅkhyā 2⁴; the Meru row is
occupied 1/1, 4/4, 5/6, 4/4, 0/1 for k = 0…4 guru (the all-guru row is
unreachable by construction, since the shortest interval is always laghu).
By mātrā weight, against Virahāṅka's count `length (सर्व n)`: weight 5 uses
8 / 8, weight 6 uses 9 / 13 (and carries 3,921 codas, the GGLL type),
weight 7 uses 16 / 21, weight 8 uses 19 / 34, and above weight 10 the
repertoire thins to a few percent of the prastāra. The Nārāyaṇa samāsa over
{1,2,3,…} (the full mora vector) has 405 distinct vectors; the top four are
(2,2,1,1), (1,1,1,1), (1,1,1), (2,1,1,1).

On the net, `out/prastara_meru.hvm4` hands all 16 four-syllable metres to
`@meru` as one superposition and sorts each into its Meru cell
`#Cell{varṇa, guru, mātrā}` in one pass (3,056 interactions; the cells
enumerate C(4,k) with mātrā = varṇa + guru on every branch, the theorem
`मात्रा-वर्ण-गुरु` observed branch by branch). `out/prastara_spec.hvm4` keeps
only the metres that real 4-interval codas use most: survivors `[2,2,1,1]`,
`[2,1,1,1]`, `[1,1,1,1]`; the other 13 erase (3,387 interactions).

### 8.2 The readout does not factor along time (`NerodeYantra`)

`nerode-saṅkoca` says: if `out ∘ δ ≡ g ∘ out`, the Nerode relation is the
kernel of one observation. On each whale's ordered codas (lens-10 class,
257 classes):

| k | H(next \| last k) bits | shuffled null |
|---|---|---|
| 0 | 4.324 | 4.324 |
| 1 | 2.479 | 3.463 |
| 2 | 1.615 | 2.188 |
| 3 | 1.003 | 1.107 |

The next class is the most likely one given the current in 54 % of steps;
a factoring would give 100 %. The state of a whale in an exchange exceeds
its readout at every window measured. `nerode_net.py` learns the k = 1
transition support from half the dialogues (156 classes, 522 transitions)
and runs it on the net as an acceptor over a superposition of held-out
sequences: 4 of 10 survive, the rest erase (16,314 interactions), agreeing
with the Python check.

### 8.3 What crosses between whales is the metre, at the receiver's own tempo (`TheEncounterOfTwoPeers`, README §6)

A coda by whale B within 6 s of a coda by whale A, against same-whale steps
and random pairs:

| step | n | lens-10 shape kept | metre kept | same click count | median rel. \|Δtempo\| when metre kept |
|---|---|---|---|---|---|
| same whale | 1,211 | 51.0 % | 71.9 % | 81.8 % | 0.021 |
| cross whale, overlapping (chorus) | 906 | 19.3 % | 51.0 % | 63.9 % | 0.077 |
| cross whale, non-overlapping | 1,210 | 23.0 % | 50.4 % | 65.0 % | 0.082 |
| random pairs | 6,000 | 18.8 % | 35.7 % | 60.9 % | 0.214 |

At the fine lens nothing crosses between whales (19–23 % against a 19 %
null). At the metre lens half of all cross-whale steps carry the metre
over (51 % against 36 %), and the receiver re-expresses it at its own tempo
(8 % apart, against 2 % within a whale and 21 % at random). Whether the
codas overlap or not makes no difference. So the encounter's transport is
the metre and its fibre is the tempo, and which lens shows the transport is
itself a finding: the transported invariant is coarser than the invariant a
single whale keeps. Revelation (README §6, "B now has A's shape") is
measurable here; generation (a new shape appearing at B) is the other half
of every cross-whale step.

### 8.4 Sign birth: the lens where compression stops paying (hieroglyphics II, `Laghava`)

`चिह्नजन्म ⟺ संरचनासंपीडनलाभ > 0`: a sign is born only when it compresses more
than it costs. A two-part code of the 7,268 EC1 codas (10 bits per class
centroid coordinate; per coda `log₂ K` for the sign plus a residual per
interval in per-mille): total bits by lens R — 194.3k at R = 1 (12 signs),
192.6k at R = 3 (97), **185.3k at R = 8 (144 signs, 25.5 bits per coda)**,
199.6k at R = 10 (216), 205.9k at R = 20 (632), 267.0k at R = 100 (3,086).
The code is a reading; the shape of its minimum is the point: adding signs
pays until roughly 140 of them and costs thereafter. Sharma et al.'s 18
rhythms × 5 tempos is 90 composite signs, in the same range.

### 8.5 The Zipf slope is a function of the lens (abstracts 21, 28)

Rank–frequency slope of class frequencies: −2.04 at R = 2, −1.96 at R = 3,
−1.60 at R = 10, −1.23 at R = 20, −0.96 at R = 50, −0.71 at R = 100, −0.10
at R = 1000. The one number the field reports as a property of a species is
a decategorified count whose value is set by the analyst's lens.

### 8.6 The tempo trajectory's modulus (`SthairyaSutra`)

Same-whale steps with the shape kept: relative |Δtempo| median 0.021, p90
0.065, p99 0.130 (absolute: median 17 ms, p90 50 ms, p99 123 ms, max 546 ms).
Rubato is a small, bounded motion of the fibre per crossing.

### 8.7 Two blind readings, jointly faithful (abstract 18, `ApurvaIndriyam`)

Against the annotation (24 EC1 types, 7,266 codas), on 10,000 sampled pairs:

| reading | classes | purity | blind pairs (same class, different type) | pairs it separates that the annotation joins |
|---|---|---|---|---|
| metre alone | 174 | 0.868 | 464 | 516 |
| tempo alone (Sharma's 5 bins) | 5 | 0.738 | 1,054 | 1,519 |
| click count alone | 8 | 0.641 | 2,902 | 0 |
| **joint metre × tempo** | 281 | **0.992** | **2** | 1,862 |
| joint click count × tempo | 36 | 0.957 | 57 | 1,519 |

Each reading alone is blind on named pairs (metre LLLL carries `1+1+3`, `5R1`,
`5R2`, `5R3`; LLL carries `1+31`, `4D`, `4R1`, `4R2`; every tempo bin carries
9–13 types). The joint reading is faithful to two pairs in ten thousand.
That is abstract 18's shape on data: the human annotation is, to 99 %, the
joint of a metre reading and a tempo reading, neither of which descends
along the other (`अपूर्वम्` both ways), and the joint's 281 classes over-split
the 24 labels (1,862 separated pairs the annotation joins) — the residue the
annotator quotiented away, which a receiver may or may not.

### 8.8 The tempo is state, not noise: the observability quotient (`ObservabilityQuotient`, `MyhillNerodeMinimalMachine`)

The safe quotient of a machine's states is not the kernel of one
observation but ForeverEq = ⋂ₙ ker(P Tⁿ): two states are identified only
if every future observation agrees. On the empirical whale machine (states
= metre × Sharma's tempo bin, transitions = observed successors within a
whale's run, readout = the metre), bisimulation refinement gives:

| | count |
|---|---|
| states (metre × tempo-bin) | 285 |
| readout classes (metres alone) | 201 |
| bisimulation classes (ForeverEq) | 280 |

148 metres have all their tempo variants identified by their futures, but
those are the rare metres with one or two occurrences. Every frequent
metre is split by tempo: GGLL's four tempo bins fall into four distinct
quotient blocks (counts 60 / 501 / 318 / 1,315), LLLL's five bins into five,
LLL's five into five. The futures of a GGLL at tempo bin 0 and a GGLL at
tempo bin 4 differ, so the quotient refuses to identify them. Where §8.3
found the tempo is what a receiver re-expresses, this says the tempo is
what the sender's own next coda depends on: the fibre carries state along
the run, and `ker P` (metre only) is not a safe reading of the machine.

### 8.9 The arrow of time in the repertoire (`theorems/primes/pair_field/ReversalInvariant`)

List reversal is the ℤ/2 involution on codas. A reading is blind to it or
sighted; its fixed locus is the palindromic metres.

| reading | reversal-blind codas (of 7,266) |
|---|---|
| click count, tempo, mātrā, guru count | 100 % (all four are scalar; scalars are achromatic) |
| metre | 24.7 % (the 1,794 palindromes) |
| exact shape | 0.1 % (7 codas) |

The repertoire is not reversal-symmetric: GGLL occurs 3,661 times, its
reversal LLGG 0 times; GLLL 301 against LLLG 16; LGLL 196 against LLGL 1;
GGGLLL 79 against LLLGGG 13. The whales' metres begin with the long
intervals and accelerate. Every scalar reading in the literature (click
count, duration, "tempo") is blind to this by construction; the chromatic
readings (metre, shape) see it in three codas of four.

### 8.10 The run is the answer stream, partially (`Prasna`, `SamvadaPrasna`)

`Prasna` reads an interaction's run as its stream of answers: the next
state is a reaction to the environment's answer. On 1,810 triples
(A's last coda, B's last coda, B's next coda) within dialogues:

| conditioning | H(B_next) bits | shuffled null |
|---|---|---|
| nothing | 3.806 | |
| A's last (the answer) | 2.275 | 3.151 |
| B's own last (own state) | 1.243 | 3.157 |
| both | 0.768 | 2.414 |

B's next metre equals B's own last metre in 75.2 % of steps and A's last
metre in 50.9 %. The answer carries 0.475 bits beyond B's own state; B's
own state carries 1.506 bits beyond the answer. So B's run is not its
answer stream alone (`Prasna`'s determinism-is-silence limit would give
0 bits of own-state), nor a generator ignoring the answer; it is a
service with memory whose reaction to the answer is conditioned by where
it already is. The exchange of §7 (metre kept, tempo drifting) is the
visible face of these numbers.

### 8.11 Order inside the Meru cell: what every total is blind to (`KramaNairapeksya`)

A total spends only associativity and commutativity, so it is indifferent
to the enumeration: every scalar reading of a coda (click count, tempo,
mātrā, guru count) is blind to every permutation of the intervals, not
only to reversal. The Meru cell (n syllables, k gurus) is the permutation
orbit, of size C(n,k); the order is what lives inside it.

| cell (n,k) | C(n,k) | codas | arrangements used | H(arrangement) | log₂ C(n,k) | top |
|---|---|---|---|---|---|---|
| (4,2) | 6 | 3,754 | 5 | 0.073 | 2.585 | GGLL 3,726, LLGG 20, GLGL 3 |
| (4,1) | 4 | 612 | 4 | 1.323 | 2.000 | GLLL 350, LGLL 211, LLLG 47 |
| (3,1) | 3 | 315 | 3 | 0.609 | 1.585 | GLL 275, LLG 36 |
| (4,3) | 4 | 152 | 4 | 1.189 | 2.000 | LGGG 97, GGGL 47 |
| (6,3) | 20 | 123 | 8 | 1.614 | 4.322 | GGGLLL 79, GGLLLG 22, LLLGGG 14 |
| (5,2) | 10 | 119 | 6 | 1.294 | 3.322 | GGLLL 86, LLLGG 21 |

H(metre) = H(cell) + H(arrangement | cell) = 3.064 + 0.375 bits, against
1.809 bits the arrangements could carry if the whales used their cells
uniformly. So the totals (n, k) recover the metre to within 0.375 bits per
coda on average: the repertoire is concentrated in one arrangement per
cell, most extremely at (4,2). The order carries information a total
cannot see, and the whales spend that channel sparingly; where they spend
it, (4,1), (4,3), (6,3), it is a full bit or more. §8.9's arrow of time is
the direction of that concentration.

### 8.12 The born-sign inventory (hieroglyphics II, per sign)

§8.4 varied the lens. Here the lens is fixed at the metre and each metre is
tested on its own: it earns an entry in the sign table iff the entry
shortens a two-part description of the corpus (table of spellings +
per-coda escape flag + index-or-spelling), `चिह्नजन्म ⟺ लाभ > 0`, greedily.

| | |
|---|---|
| metres in the corpus | 204 |
| description with no signs | 78,232 bits |
| born signs | 77 (31,781 bits; 3.65 per coda) |
| last born / first refused | GGLGGG (3 codas, +1.1 bits) / LGG (6 codas, −3.1) |
| human types with a majority metre | 17 types on 12 metres, all 12 born |
| born signs with no human name | 65 |

The first six born, with their human names where they have one: GGLL
(3,726; `1+1+3`), LLLL (1,865; `5R1 5R2 5R3`), GLLL (350; unnamed), LLL
(405; `4R1 4R2`), LGLL (211; unnamed), GLL (275; `1+31 4D 1+32`). The two
unnamed signs in the top six are the (4,1) cell's two dominant
arrangements, which the human scheme folds into other types or noise.
Every human-named metre is born; the born inventory is three times
larger than the named one. Full inventory in `out/instrument_round_three.tsv`.

### 8.13 The two clans differ in the fibre (`ApurvaIndriyam` at the clan level; `PariksaDvaya`)

The Dominica file carries two vocal clans, EC1 (7,770 codas) and EC2 (949).
Which reading separates them?

| reading | I(clan; reading), of H(clan) = 0.497 bits |
|---|---|
| click count | 0.005 |
| tempo bin | 0.080 |
| metre | 0.186 |
| human type | 0.373 |
| metre × tempo | 0.420 |

Inside the one metre both clans use most, LLLL (the 5R family: EC1 1,206
codas, EC2 659), the tempo alone separates them almost entirely,
I(clan; tempo | LLLL) = 0.840 of 0.937 bits: EC1's LLLL sits in tempo bins
0–1 (median 334 ms, the types `5R1`/`5R2`), EC2's in bins 3–4 (median
1,144 ms, the type `5R3`), a ratio of 3.4. No metre with ten or more codas
is heard only in EC2; twenty are heard only in EC1.

So at the metre lens the dialect difference on the shared family is a
difference in the fibre only: the same metre, at a tempo three times
slower. At a finer lens it is not. The per-mille shapes:

| type | codas | median tempo | median per-mille shape | lens-10 shape (mode) | last/first interval |
|---|---|---|---|---|---|
| `5R1` (EC1) | 1,510 | 329 ms | [285, 280, 226, 208] | [3,3,2,2] (75 %) | 0.73 |
| `5R2` (EC1) | 287 | 508 ms | [240, 258, 240, 258] | [2,3,2,3] | 1.08 |
| `5R3` (EC2) | 642 | 1,133 ms | [247, 246, 251, 256] | [2,2,3,3] | 1.04 |

EC1's "regular" five-click coda accelerates by a quarter over its length;
EC2's is even. Their lens-10 shape distributions overlap by 0.157. So the
dialect translation exists at the metre lens and does not exist at lens
10 or below, and the net says so: `clan_transport.py` superposes 24 real
EC2 `5R3` codas, transports each along the fibre to EC1's median `5R1`
tempo, and keeps only those within 6 ms per interval of EC1's median
`5R1` (search inside evaluation, `out/coda_clan_transport.hvm4`). Every
branch erases: 0 survivors in 8,178 interactions, and 0 of all 623 `5R3`
codas in Python (EC1's own `5R1` codas pass the same test at 14.9 %). The
earlier nearest-neighbour reading (an EC2 `5R3` transported to EC1's
tempo lands nearest a real `5R1`) is true only because `5R1` dominates
EC1's LLLL codas; it is not a translation. Which lens the receiver reads
at decides whether the two clans say the same thing slowly and quickly,
or two different things.

### 8.14 The round trip and its residue (`Ekatva`, `CompressionIsTransport`)

The lossless recoding a ↦ (f a, fibre point) round-trips exactly; a lens
that drops the fibre does not, and the residue is what it dropped. Every
coda was sent c → lens → another whale's tempo → lens → its own tempo:

| lens | round trip exact | mean residue per coda |
|---|---|---|
| R = 10 | 9 / 8,696 (0.1 %) | 94.3 ms |
| R = 100 | 216 (2.5 %) | 7.6 ms |
| R = 1000 | 4,976 (57.2 %) | 1.08 ms |
| exact (gcd) shape | 5,901 (67.9 %) | 0.83 ms |

Even the exact shape does not round-trip through another tempo on 32 % of
codas, by under a millisecond: the receiver's millisecond grid is itself
a lens, and the residue is its rounding. On the net
(`out/coda_roundtrip.hvm4`) 18 real codas were sent to the next coda's
tempo and back in one superposed pass at R = 1000 and collapsed with
their residues (0–2 ms) beside them, 6,945 interactions.

### 8.15 How far the whale machine is from one execution (`Niyati`)

For the universal machine the space of productive runs from a
configuration is contractible: one machine, one history. The empirical
whale machine (states = metre × tempo-bin, 82 runs, 3,740 steps) has
H(next | current) = 1.766 bits against a 3.414-bit null. Per run (57 runs
of eight or more codas): minimum 0.000, median 0.700, maximum 1.846 bits.
Three runs are a point, every step forced; the rest are a genuine space.
Its size under the observed transition support, in bits of history:

| horizon k | log₂ |histories| (visit-weighted) | per step |
|---|---|---|---|
| 1 | 4.60 | 4.60 |
| 2 | 7.86 | 3.93 |
| 3 | 11.49 | 3.83 |
| 5 | 18.55 | 3.71 |

The support allows about 3.7 bits of branching per step; the whales
realise 1.77. The gap, 1.9 bits per step, is what the run's own past
forbids beyond what the support does: the stream is far from a point but
much nearer to one than its support.

### 8.16 What a reading hides is what makes its next step hard (`HidingAndHardness`)

| prediction | conditioning | bits | the hidden part shown | hardness the hiding costs |
|---|---|---|---|---|
| next metre | current metre (tempo hidden) | 1.482 | 1.292 | 0.190 |
| next tempo | current tempo (metre hidden) | 1.061 | 0.854 | 0.207 |

Both readings pay about a fifth of a bit per step for what they hide,
and the two costs are nearly equal: the fibre and the base each carry
roughly the same amount of the other's future. Read with §8.8 (the tempo
is state) and §8.9 (scalars are achromatic), the whale machine is
a joint of two readings each of which is, to a fifth of a bit, a
sufficient statistic for its own next value.

### 8.17 Ornamentation tested as a shared line, and not confirmed

Sharma et al.'s fourth feature is an extra click. If the ornamented coda
were the neighbouring coda's line plus one click, the shared-prefix
regime of §5 would be its natural program. Within a whale's run, on the
409 consecutive pairs whose click counts differ by one:

| lens | ornamented coda's prefix equals the neighbour's shape | null (random coda of that length) |
|---|---|---|
| R = 4 | 47.7 % | 59.2 % |
| R = 10 | 27.9 % | 19.4 % |

The ornament interval is 0.80 of the neighbour's mean interval (p10 0.44,
p90 1.85). The signal is not there at this resolution: at the coarse
lens the neighbour's shape is found in the prefix *less* often than a
random coda's, at the finer lens slightly more. Sharma et al. define the
ornament against the annotated rhythm type of the surrounding codas,
which the dialogue file does not carry, so this is a failure to confirm
with the readings available here, not a refutation. A per-length test
(is the first n−1 intervals' metre a born metre?) is uninformative because
the born inventory covers nearly every short metre (94–99 %), and is
reported in the log only.

## Files

    coda_elucidator.py   reads the CSV; exact & per-mille factoring; lens table; emits out/coda_*.hvm4
    coda_regimes.py      lens-10, spec, transport programs; cost regimes; writes out/RESULTS_regimes.txt
    coda_exchange.py     rubato as fibre motion along real exchanges; emits out/coda_exchange.hvm4
    full_instrument.py   metre/prastāra, Nerode deficit, encounter, sign-birth MDL, Zipf-vs-lens, Lipschitz; emits out/prastara_*.hvm4
    nerode_net.py        a Nerode acceptor learned from half the dialogues, run on the net over held-out sequences
    round_two.py         observability quotient (bisimulation), reversal blindness / arrow of time, Prasna entropies; log in out/instrument_round_two.log
    clan_transport.py    EC2 5R3 → EC1 5R1 by transport with a spec inside the evaluation; emits out/coda_clan_transport.hvm4
    round_four.py        distance from one execution (Niyati), hiding-and-hardness, ornamentation as a shared line; log in out/instrument_round_four.log
    round_three.py       order inside the Meru cell, born-sign inventory, the two clans as readings, round-trip residue (emits out/coda_roundtrip.hvm4); log in out/instrument_round_three.log
    tit_syntax.hvm4      Japanese tit ordering rule over a superposition
    campbell_affix.hvm4  Campbell's monkey root × affix factoring
    out/                 generated programs, sample_codas.tsv, lens_resolution.tsv, python_run.log
    RESULTS.txt          the runs, verbatim

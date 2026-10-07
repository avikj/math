# Status — what was asked, what is delivered, where (all verified by running the patched binary)

Build: `cubical-paths.patch` **and** `cubical-paths-hvm4-tail.patch` on
DKormann/Bend2 @ f026483; GHC 9.12.2, cabal 3.18, `LC_ALL=C.utf8` (without it
the binary aborts on any UTF-8 source and prints nothing). `bend f.bend` checks
and runs; `bend check` is not a subcommand.

`cubical-paths.patch` is TRUNCATED at its last hunk: `src/Target/HVM4.hs` ends
mid-definition, with `label` missing its `Sym` and catch-all clauses and `op2`
absent entirely, so `Op2 o a b -> ... op2 o ...` at line 121 is a scope error
and the tree does not compile. `cubical-paths-hvm4-tail.patch` supplies the
missing tail, taken verbatim from the identical definitions in
`src/Target/HVM4Full.hs`. Apply both, in that order.

| Ask | Delivered | Evidence |
|---|---|---|
| Native execution of cubical transport on the runtime (path as runtime data) | universe path = Church pair `(fwd,bwd)`; `coe` = direction projection; `--to-hvm4-raw` emits without pre-normalisation; HVM3 never pre-normalises | `applypath.bend` on HVM4: `@applyPath(*)(*)(@negPath)(1) ⇒ 0`; `t_fwd_neg/t_bwd_neg/t_fwd_id/t_bwd_id` raw 0/0/1/1, HVM3 same (VERIFICATION.md) |
| Pth transport through non-constant families | `whnfCoe` Pth case builds the `HCm` square | `pth2.bend` 2✓ |
| Sound totality classifier | descending-column analysis; `loop` is `[unchecked]`; **`--total` gate** refuses such files (exit 1) | `loop.bend`, `bend loop.bend --total` |
| Narrow "univalence complete" | raw-Iso level: only the path-side round trip; Iso-side fails as it must | `uaroundtrip.bend` 4✓ 1✗ (deliberate); README/WRITEUP/CORRECTIONS corrected |
| General hcomp (cofibration systems) | one constructor `HCm A [(φ,u)] base`, faces arbitrary interval formulas (DNF), per-cell boundary + adjacency checks; false faces dropped | `hcompfaces.bend` 5✓, `isprop.bend` 3✓ (GENERAL_HCOMP.md) |
| hfill | parser sugar `hfill(A,[(φ,u)…],base) : Path(base, hcompN(…))` | `hfill.bend` 4✓, must-fail `wrong` ✗ |
| Coherent reverse univalence round trip | `Equiv = Σ f. ∀y. isContr(fiber f y)`; `uaE`; `pathToEquiv`; `uaEquivRoundTrip : pathToEquiv(uaE e) = e` | `uaequiv.bend` 17✓; `uaequiv_mustfail.bend` wrong1/wrong2 ✗; `roundtrip.bend` 21✓ (parallel agent) |
| The object itself: `A ≃ Σ B (fiber f)` | `isoToIsEquiv` (library `lemIso`, transcribed), `totalEquiv` for every `f`, `losslessPath = uaE(totalEquiv)`, `present/retrieve` by `coe`, laws by refl | `fibrelaw.bend` 35✓ (FIBRE_LAW.md) |
| …running on the net | `presentNeg`/`retrieveNeg` and the contraction `contrNeg0/1` on the raw HVM4 net and HVM3 | 0/1/1/0 and 0/0, itrs in FIBRE_LAW.md |
| **Transport across chains of equivalences performed by the net** (composite / inverse / Π / Σ lines as runtime paths; raw mode strict) | closed runtime path algebra `pathRep/lineRep/coeRep`; `whnfCoe` gains the same inverse/composite rules | `chain.bend` 19✓; 12 transports × 3 evaluators agree; itrs 12/19/31 for 1/2/3 equivalences (RUNTIME_ALGEBRA.md) |
| **Everything cubical at runtime** (README: the trace IS the path; partial knowledge) | `--to-hvm4-full`: intervals, paths, types, `coe`, `hcomp` are runtime objects; stuck `#HCm` on symbolic faces; DUP-SUP routing native | RUNTIME_FULL.md: chain/fibre/t_*/supline/isprop_run all correct on the full runtime |
| **Kan rules for the universe** (the last open frontier) | transport through Glue; `hcomp` in `Set` = Glue with `transpEquiv`; `ua` derived from Glue, uaβ definitional | `uaglue.bend` 26✓, `hcompset.bend` 10✓, `glue.bend` 8✓, `glue_mustfail` 3✗ (GLUE.md) |
| **The highest construction executed** (forcing theorem, both instances) | `forcing_run.bend` 82✓; 8 observations identical on normaliser and HVM4 full runtime | FORCING.md (RUN section) |
| **The coinductive calculus and the braid fabric** (`Prasna`/`Prashna`/`Niyati`, `AnantaVeni`) | depth-indexed `IExec`/`Answers`, `run-is-answers` as a coherent Equiv, silence-is-determinism, the braid relations pointwise; machines run on HVM with superposed answers measured | `interaction.bend` 36✓, `braid.bend` 16✓ (INTERACTION.md) |
| **Genuine coinduction** (the corpus's `--guardedness` records, copattern bisimulations) | `Answers`/`IExec` as corecursive records, `replay`/`forgetStates` corecursive, both `run-is-answers` round trips as corecursive paths, all `[productive]`; unguarded and destructor-recursive "proofs" refused under `--total`; false bisimulation fails finitely | `coinduction.bend` 13✓, `streams.bend` 10✓, `coinduction_mustfail.bend` (wrong ✗) (COINDUCTION.md); `--total` passes on coinduction/interaction/braid |
| **Cost of keeping the calculus at runtime** (does "everything runtime" cost a rerun per use?) | no: transport paid once under sharing (marginal 14 itrs vs 150). Superposed transport has two regimes: a SHARED line over N values wins and improves with N (marginal 38 vs 139), DIFFERENT lines lose by a constant ~1.4x — superposition pays exactly when branches share work | `bench_*.bend`, `./suite.sh` (SYNTHESIS.md §3-4) |
| **General silence-is-determinism** (Prasna §3, contractible `Q`, varying `δ`) | corecursive dependent path `answersUnique : PathP(λi. Answers(p @ i))` over a path of states; `isContr(IExec x)` for any such interaction; Niyati's one-execution as the `Q = Unit` instance; run on HVM | `silence.bend` 25✓ `--total` passes, main = 4 on both runtimes; `silence_mustfail.bend` (wrongTail, wrongCentre ✗) |
| **General HIT schema** (the last language gap: every HIT the corpus uses as ONE declaration form) | `type … path @c(fields): Path(…)` of any dimension; `@c{args}`; `hrec`/`helim`; endpoints, elimination, hcomp-commutation, coe-through-parametric-HITs in checker and full runtime | circle, Susp/Sⁿ, pushout, torus, Klein, set quotient + effectivity (23✓), prop/set truncation, hub-and-spoke: `hit_*.bend` 16 files, `hit_circle_mustfail` ✗ (HITS.md) |
| **Retire Agda: the corpus's constitutive modules IN BEND** (`port/`, PORT.md) | `import Name` modules; `Prelude.bend` (h-levels, path algebra, equivalences, `isSetNat` by encode–decode); the kernel — RewriteCertificate (with induction certificates), ControlledGrammar, GenerativeKernel, PvsNP-gap, EveryDerivationIsInvertible, WindingCost — and the fibre law Carrier, each an Agda module = one Bend file, zero rejections, mains on HVM4 | `port/*.bend`: 38/57/73/90/98/63/64/52 ✓ |
| **The feature audit** (every Agda feature/library the corpus uses vs Bend, each row a checked file) | AUDIT.md: nothing the corpus does needs a feature Bend lacks; the differences are stated exactly (no implicit args, untyped one-step conversion, `Set : Set`) | AUDIT.md |
| Tighten writeup (Analysis counts syntax) | stated as syntax counts; overclaims removed | WRITEUP.md, CORRECTIONS.md |
| Push/pull main every few minutes; merge parallel agents' work | merged `HCmN`→unified constructor, REF_ENDPOINTS (same hunk), `roundtrip.bend` | git log |

Checker mechanisms that had to exist for the above (all in the patch):
typed endpoint law for var- **and Ref-**headed path spines (`spineTy`),
`epNormCtx` traversing `SigM` and unfolding saturated non-path Ref
applications (`unfoldable`), `(<i> t) @ r` beta in `infer`, false faces
dropped in `whnfHCm`, emitters resolving literal endpoints before erasure.

Erased targets (`--to-hvm4`, `--to-hvm4-raw`, `--to-hvm`) are kept as cost
comparison points; the full runtime is `--to-hvm4-full`. In the checker/normaliser nothing cubical is stuck any more (Glue Kan rules
in). The full runtime (`--to-hvm4-full`) has the same Kan rules (`@coeGlue`,
`hcomp` at `#Set` → `#Glue`); RUNTIME_FULL.md lists the two runtime caveats.

Suite: `./suite.sh` — 108 `.bend` files, bad=0. Every file must check clean
except the registered soundness probes (the registry is in the script):
`coinduction_mustfail erasure glue_mustfail hfill quotient_mustfail
silence_mustfail uaequiv_mustfail uaroundtrip`. Register any new file that
contains a deliberate rejection; an unregistered one reads as a regression.

Cubical completeness, audited and itemised in **REMAINING.md** — sections A,
B, C and E are now CLOSED:
- `hcomp` has its full type-directed rule set (Pi, Sigma, PathP, Nat, List,
  discrete types, Set, Glue) in BOTH the checker and the full runtime.
- `comp`, `hfill`, `transp` with a cofibration, `Partial`/systems/`pout` and
  `Sub`/`inS`/`outS` all exist, parse, check and run.
- Two HITs: the SetQuotient and the circle `S1`; both reach the runtime.
- Every traversal is exhaustive; the JS backend fails loudly instead of
  silently erasing a path.
Remaining: a GENERAL HIT schema (§D), and the one Glue composition law that
cannot be stated without face-restricted contexts (§B).

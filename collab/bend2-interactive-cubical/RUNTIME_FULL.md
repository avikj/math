# `--to-hvm4-full` — the cubical calculus as a runtime, nothing erased

The README's machine is the fabric of paths: a trace *is* a path, traces
compose, invert and carry higher coherences, and knowledge is partial. So the
compiled program must keep every cubical object alive at runtime. This target
does. `Target/HVM4Full.hs` (in `cubical-paths.patch`) emits Bend2 terms with
**no erasure and no compile-time normalisation**; the prelude is
`Core.WHNF`'s cubical reduction rewritten as an HVM4 program.

| object | runtime representation |
|---|---|
| interval | data: `#I0`, `#I1`, symbolic `#INot{i}`, `#IAnd{i,j}`, `#IOr{i,j}` (`@inot/@iand/@ior` evaluate when they can) |
| value path `<i> t` | data `#PLm{λi. t}`; `p @ r` is `@pathAt(p, r)` |
| universe path | data `#UaU{A,B,f,g,gf,fg}` (both coherences kept beside the two maps), `#CompU{P,Q}` (`hcomp` in `Set`), endpoints by `@pL/@pR`, symbolic application `#At{p,i}` |
| type | data: `#Bool`, `#Nat`, `#Set`, `#Pi{A,B}`, `#Sig{A,B}`, `#Path{A,u,v}`, `#Eql{A,x,y}`, `#Enum{syms}`, `#Num{kind}`, … — a type is a cell like any other, never abbreviated |
| `coe(L, r, s, x)` | `@coe`: if `r`,`s` agree → `x`; else evaluate `L(#IMark)` and **dispatch on the type former at runtime**: rigid → `x`; `#Pi` → conjugate domain/codomain lines; `#Sig` → componentwise along the filled first component; `#Path` → the hcomp-conjugation square; `#At{p,i}` → `@coeU` on the universe path (`ua` → `f`/`g`; composite → sequential) |
| `hcompN(A, faces, base)` | `@hcomp`: evaluates each face; a true face returns its tube's top; all-false returns the base; **otherwise it is stuck data `#HCm{A, faces, base}`** — partial knowledge, decided when a later application fixes the interval |
| superposed line `&L{A i, B i}` | **no rule**: the `@coe` dispatch is a match, HVM4 commutes a match over a superposition, and the same-label dup of the transported value annihilates — the fibre routing (DUP-SUP) is the net's own interaction |

## Verified on the full runtime (HVM4, `-C10`)

All values agree with the checker's normaliser (`bend f.bend`) and with the
erased targets; interactions are now the cost of the *runtime* dispatch.

| program | result | itrs |
|---|---|---|
| `t_fwd_neg / t_bwd_neg / t_fwd_id / t_bwd_id` | 0 / 0 / 1 / 1 | 123 / 126 / 44 / 45 |
| `chain.bend` `viaNegNeg True/False` (composite) | 1 / 0 | 537 / 539 |
| `viaNeg3`, `viaNeg3Bwd` (three equivalences) | 0/1, 0/1 | 1096–1121 |
| `viaInv` (inverse line) | 0 / 1 | 140 / 134 |
| `viaPi` (Π line) / `viaSig` (Σ line) | 0/1 / 0/1 | 282/273 / 275/265 |
| `fibrelaw.bend` `presentNeg True/False` | 0 / 1 | 207 / 196 |
| `retrieveNeg True/False` (`coe` back along `uaE(totalEquiv)`) | 1 / 0 | 409 / 409 |
| `contrNeg0 / contrNeg1` — the fibre-contraction path (`lemIso`'s 4-face `hcompN`s run on the net) | 0 / 0 | 223 / 191 |
| `supline.bend` — `coe` along `&0{negPath@i, Bool}` of `&0{True,True}` | `&0{0,1}` = `&0{False,True}` | 195 |
| `isprop_run.bend` — `isPropIsContr`'s 4-face composite at `(i1,i0)` and every other corner | `()` | 168 |

Partial knowledge, observed: `pcompH(...) @ #IVar{0}` on the net is
`#HCm{#Nat, #Cons{#Face{#IVar{0}, …}, #Cons{#Face{#INot{#IVar{0}}, …}}}, #Zer}` —
a stuck composition carrying its faces; the same term at `#I0` is `#Zer`, at
`#I1` the tube's top. The face is decided by whoever later supplies the interval.

## Comparison points kept

`--to-hvm4` (normalise-then-erase), `--to-hvm4-raw` (erase, strict, universe
paths as Church pairs) and `--to-hvm` (HVM3) remain, so the cost of erasure vs
runtime can be read side by side (e.g. `viaNeg3`: 31 itrs erased, 1106 full).

## Kan rules on the runtime

`@coe` on a `#Glue{A, faces}` line (`@coeGlue`) and `@hcomp` at `#Set`
(`#Glue` over the base with `@transpEquiv` of each tube — pathToEquiv computed
by the runtime `@coe` through Σ/Π/Path type data) mirror the checker's rules.
Faces are read off the line at the marker and instantiated at `r`/`s` by
interval substitution (`@substI`), since re-evaluating the line at a literal
endpoint lets a true face collapse the Glue to its partial type. Verified:

| program | result | itrs |
|---|---|---|
| `uaglue.bend` `viaGlue True/False` (ua derived from Glue) | 0 / 1 | 797 / 789 |
| `viaGlueBwd True/False` | 0 / 1 | 811 / 802 |
| `hcompset.bend` `viaSq(i0)` (2-dim universe composition; equivalence computed on the net) | 0 | 1935 |
| `viaSq(i1)` | 0 | 147 |
| `viaTwist True/False` (non-constant base line) | 1 / 0 | 587 / 589 |
| whole earlier matrix (chain, fibre law, contraction, superposed line) | unchanged | — |

A glue value with no live faces is its base; a Glue type keeps its faces
(types are consumed only by `@coe`). Binders now get globally unique names.

## Set-quotient recursor on the full runtime

`Quo`/`QCl`/`QEq`/`QSq`/`QRec` emit to `--to-hvm4-full`: `@qrec` computes
`qrec([a]) → f a` and `qrec(eq/ a b w @ i) → resp a b w @ i` (with `@pathAt`
giving `eq/ @ i0 = [a]`, `@ i1 = [b]`), commuting over `Sup` natively. Verified:
`qrec(qcl 3n, dbl) ⇒ 6`, `qrec(qeq(2n,2n,refl)@i0, dbl) ⇒ 4`; `minmachine`,
`quotient`, `nerode_effective_closed` all emit and run.

## Typed points: what the emitted program is

The emitted object is the whole checked complex, not a value with its types
stripped. `--to-hvm4-full` runs the checker first (the report goes to
stderr, stdout is exactly the program) and emits nothing for an ill-typed
book. Every definition `name : A = a` is emitted twice, in disjoint
namespaces:

    @Dname = <a>        the term
    @Tname = <A>        its checked type, emitted by the same emitter

and the root is the entry as a point of `Σ(A : Set). A`:

    @main = #Pair{@Tmain, @Dmain}

so `hvm p.hvm4 -s` prints `#Pair{<type>, <value>}` (e.g.
`#Pair{#Nat{},#Suc{#Suc{#Zer{}}}}`). A map-valued entry is the point
`(#Pi{…}, λ…)`; nothing is generated beside it. There is no runtime copy of
the fibre law or its coinductive closure: `port/FibreCoalgebra.bend` and
`port/ConductiveRuntime.bend` are ordinary checked programs going through
this emitter (`verify_conductive_entry.sh`). Unary operations, unsolved
metavariables, and floats are refused rather than miscompiled; `**` is
`@pow`; a char is its code point.

A HIT constructor is written bare (`@seg{a}`): it carries no parameters, and
the checker reads them off the goal. They are cells of the checked term, so
checking is two passes: a silent one records every bare constructor's
parameters by its source span, the book is elaborated (`Core.Check.elabFills`,
instantiating binders exactly as `check` does), and the reporting pass runs on
the elaborated book. A declared endpoint that mentions a parameter
(`@bot{f(a)}` in the cylinder of `f`) then computes with the actual `f`, in the
normaliser and on the runtime (`hit_param_endpoint.bend`: 6 at both ends of
the segment at 3, for `f = dbl`), where before it was an opaque placeholder in
the one and an empty superposition in the other, which annihilated the whole
value under collapse. A constructor that reaches emission without its
parameters is refused, like any other cell the emitter cannot make complete.

A superposed point of a dependent family is typed by the DUP of its goal at
the value's label, which is the net's own DUP-SUP rule run on the type:
`(&0{True, False}, &0{3n, ()}) : Σ b:Bool. F(b)` checks as `3n : F(True)`
and `() : F(False)`, its typed point is
`#Pair{#Sig{#Bool, λb. F b}, #Pair{&L0{1,0}, &L0{3,()}}}`, and `-C10` reads
off exactly the two diagonal points, never `(3n, False)`
(`sup_dependent.bend`; the different-label sibling is a must-fail). The
same-label case is the contractible fibre and routes; a different label is
an independent coordinate and must inhabit both fibres
(`SETTLED_BY_THE_CORPUS.md` §1).

One consequence to know: a typed point whose cells include a recursive
function (a HIT parameterised by `dbl`, or a `main` that is `dbl`) has no
finite normal form, and `hvm -s`, which normalises fully and expands every
reference, does not terminate on it; the in-process normaliser prints such a
reference by name. That is the printer, not the object: observe such a point
through a map out of it, as the fibre law says, rather than printing the whole.

## Caveats

- `coe` to a *symbolic* endpoint stays stuck (`@dir` = 2); the runtime
  `pathToEquiv` therefore carries stuck proof components, but the function
  and the fibre centre (inverse) compute, which is what transport needs.
- Dependent Π/Σ lines go through the generic `@coe`. Over a varying base the
  family receives a transport **to a symbolic endpoint** (`coe r→i`), which
  this prelude leaves stuck (`#StuckCoe`); a family that does not inspect it
  still computes (probe: `Σ b:(negPath@i). Nat` transports `(True, 3n)` to
  `3n` on the net). Note the checker rejects that probe's
  well-typedness anyway (`b : negPath@i` is not `Bool`), correctly.
- Traces are inspectable data: the typed point of `negNeg` prints
  `#Pair{#Path{…}, #CompU{λi. …#At{#UaU{#Bool,#Bool,neg,neg,…}, i}…, λi. …}}` — the
  composite path itself, faces and all, beside its type. Paths between
  universe paths are `#PLm` over these.

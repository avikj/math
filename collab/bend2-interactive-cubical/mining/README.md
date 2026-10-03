# Native Bitcoin mining run — executor handoff

## Run this

From a checkout containing this directory, with the **patched cubical Bend2**
and **HVM4 C runtime** already built:

```sh
export BEND=/absolute/path/to/bend
export HVM=/absolute/path/to/HVM4/src/hvm
bash collab/bend2-interactive-cubical/mining/run.sh \
  collab/bend2-interactive-cubical/mining/genesis-mainnet.json \
  /tmp/bitcoin-native-run-001
```

The output directory must be new/empty. The included input is the actual
mainnet genesis header template with **all 32 nonce bits free** (4,294,967,296
candidates), not a supplied winning nonce and not a reduced-round hash.
It is historical input, not a current mining job. A known genesis nonce is
used **only in the native conformance gate**, never passed into the search.

For a fresh build on Linux, after installing GHC 9.12.2, Cabal >=3.14,
Node.js >=18, Git, Clang, and the usual Haskell/C development prerequisites:

```sh
bash collab/bend2-interactive-cubical/mining/bootstrap.sh /tmp/bitcoin-native-toolchain
source /tmp/bitcoin-native-toolchain/env.sh
# Then run the command above.
```

Bootstrap uses the repository's `cubical-paths.patch`, Bend2 `f026483`,
HVM3 `fba2e9c82faf6e2f019c9ecea94c32f19a8b7820` (compiler dependency), and
HVM4 `6defdfc7dae2a3cca5dd6e74ed0612385b5646a8` (execution).
It uses a dedicated directory, records hashes, and never edits an existing
executor build. Network and Haskell package mirrors are required for bootstrap;
no network is required by the runner once the binaries and checkout exist.
An already working build can be supplied directly instead.

Optional explicit wall-clock cap:

```sh
RUN_SECONDS=600 BEND="$BEND" HVM="$HVM" bash \
  collab/bend2-interactive-cubical/mining/run.sh JOB.json /tmp/bitcoin-native-run-002
```

An interrupted, rejected, or out-of-memory run is **not** an empty fibre.

## Actual invocation, not a replacement search engine

The existing `SUPGEN_DEMO.md` execution pattern is retained:

```hvm
@btcCandidates = @DbtcAppend(@btcPrefixes, @btcNonces)
@main = @btcKeep(@DbtcRun(@btcTarget, @btcCandidates))
```

`btcPrefixes` is the supplied family of immutable 76-byte header prefixes.
Each free nonce bit appears as one named native `&Nk{0,1}` choice (HVM4
encodes a label name in 24 bits, four characters at most).
The same candidate is passed through the hash/specification and retained in
its receipt. No host loop expands candidate headers, selects nonce values,
executes mining SHA calls, or invokes an external SAT/SMT solver.
Independent bits have independent labels; the header and its predicate use
one shared candidate, not unrelated superpositions. With several templates,
template choice and nonce choice are independent; fields within a template
remain coupled. The first inner digest is the actual input to the outer hash.

`MiningSha256.bend` is a new **source port of the full bit-level predicate**
from `formal/cubical/Sha256.agda`, not a new search algorithm. It preserves
LSB-first words, MSB-first messages, the 64-word schedule, all 64 rounds per
compression, modular ripple addition, feed-forward, and the strictness binders.
The two inner blocks and one outer block execute all 192 SHA rounds. Only the
fixed 80-byte/32-byte padding is specialized to literal data. The Bitcoin
comparison reverses digest BYTES, not individual bits, and uses `<=`.

`MiningClaim.bend` imports the existing `port/Carrier.bend` and calls
`carry_transport` on that predicate. The return value contains the acceptance
bit, exact header, and `Path(Bool, btcAccept(target, header), acceptance)`.
The existing SupGen keep pattern inspects acceptance; failed branches become
`&{}`; a surviving native result is `#Hit{headerBits, pathReceipt}`.
The cubical receipt remains in the output. The program is compiled with
**`--to-hvm4-full` only**, so the actual `@coe`/path runtime accompanies it.
No `--to-hvm4`, `--to-hvm4-raw`, JS erasure, or CPU mining fallback is allowed.

This is a concrete invocation of the existing implemented SUP/specification
mechanism with the complete Bitcoin instance.

## Supply an actual job

The JSON contract is intentionally small:

```json
{
  "format": "bitcoin-native-job-v1",
  "job_id": "your-job-id",
  "network": "mainnet",
  "headers": ["160 hexadecimal characters: the serialized 80-byte header"],
  "nonce": {"base": "00000000", "mask": "ffffffff"},
  "max_solutions": 1,
  "provenance": "Your node/pool template identifier and context"
}
```

This documentation placeholder is not a runnable header; the adjacent
`genesis-mainnet.json` is. In your job, replace `headers` with exact serialized
headers from your trusted template builder. Do not hash display-order hashes.
Header fields other than nonce are immutable inside each supplied template.
To expose authorized version/time/coinbase choices, supply additional complete
header templates. They must have the same parent and nBits. The template
builder must enforce current chain rules, transaction validity, merkle/coinbase
commitments, time rules, and any negotiated version mask.
Duplicate 76-byte templates are rejected, not silently merged.

`nonce.base` and `nonce.mask` are ordinary numeric 32-bit hex, not serialized
little-endian bytes. Mask bits are free; unmasked bits are fixed by base. Base
must be zero on masked bits. Thus `{base:"12340000",mask:"0000ffff"}` names
65,536 nonces, and `{base:"00000000",mask:"ffffffff"}` names all 2^32.
The input size is linear in supplied templates and free bits, NOT the number
of candidates. The header's original nonce is ignored when defining the family.

The block target is decoded directly from nBits with negative/zero/overflow
and network-limit rejection. The supported presets are mainnet and regtest;
unknown networks are rejected instead of assigned guessed consensus parameters.
For a pool share, optionally supply a plain 64-digit `share_target`, at least
as large as the block target. Each output is checked against BOTH thresholds;
a share is never labeled a qualifying network block unless it meets that target.
No raw digest words, intermediate states, target overrides, or round counts
are accepted as free job inputs.

## What the runner does and retains

1. Validate the job and emit one native candidate value; record source hashes.
2. Run `MiningClaim.bend --total`. Nonzero status, rejection/unchecked markers,
   or absent check markers stop the run. Emission is not treated as checking.
3. Emit `--to-hvm4-full` and verify the full-runtime marker and required symbols.
   Rename only the library's main and attach the job plus existing keep pattern.
4. Run full native SHA empty/abc vectors, exact genesis SHA256d and PoW,
   width rejection, and native Carrier source reconstruction. All six Boolean
   outputs must be one. These are integrity gates, not a reduced mining task.
5. Execute `hvm mining.hvm4 -s -C<max_solutions>` once.
6. Independently rehash ONLY the emitted headers with Node's standard crypto,
   verify membership in the supplied header family and nonce mask, and compare
   the complete 256-bit hash against the search and block targets.

Files in the output directory:

- `job.original.json`, `job.lock.json`, `manifest.json`, `source/`: exact input,
  generated sources and hashes, source revision, and generated candidate value.
- `binaries.jsonl`, `platform.txt`, `events.jsonl`: binary hashes, platform,
  phase starts/completions/failures. Existing binary compatibility is gated;
  build provenance is not inferred merely from a successful gate.
- `typecheck.log`, `library.hvm4`, `input.hvm4`, `mining.hvm4`: compiler output
  and exact net. `gate.hvm4`/`gate.log` plus stderr retain native conformance.
- `results.hvm.txt`, `runtime.stderr`: untouched native output and statistics.
- `verified-hits.json`: byte-exact headers, full independent hashes, nonce,
  template index, both target decisions, and the printed runtime path receipt.

A zero-exit process with no survivors is reported as no emitted hit. A limit
stop after a hit does NOT establish anything about unvisited branches. Timeout,
OOM, parse error, stuck output, lost receipt, and failed native gate have
separate failure events. Never describe any of them as a proof of absence.
The raw receipt is retained even though the independent crypto verifier checks
PoW rather than serving as a cubical proof checker. No block is submitted by
this program. Submission and stale-job handling belong to the node/pool owner.

## Checks available without the native toolchain

```sh
node --test collab/bend2-interactive-cubical/mining/transport-checks.mjs
bash -n collab/bend2-interactive-cubical/mining/run.sh
bash -n collab/bend2-interactive-cubical/mining/bootstrap.sh
```

These check serialization, compact targets, masks, header membership, source
framing, and independent verification.
The native runner gates remain mandatory. The full-family native input contains
neither the known genesis nonce nor its expected hash as a supplied solution.

The Agda proof sources are:

- `formal/cubical/BitcoinMiningOnTheWire.agda`: existing `Prog` composition of
  SHA twice and target comparison, retained-source laws and conditional `Hit`.
- `formal/cubical/BitcoinMiningCut.agda`: round-equation-based suffix observer
  and exactness proof sources. Not wired into the default predicate.

Check them separately with the repository's Agda 2.8.0 / cubical v0.9 pin:

```sh
bash collab/bend2-interactive-cubical/mining/check-agda.sh
```

If a native gate fails, preserve the exact logs and fix the source/compiler
mismatch. Do not bypass the gate, reduce the round count, change the target,
substitute an external miner, or claim that host checks establish native success.

## Primary-source anchors

- Native substrate: `../SUPGEN_DEMO.md`, `../port/Carrier.bend`,
  `../port/Prelude.bend`, `../cubical-paths.patch`, `../HANDOFF.md`.
- SHA definition: `../../../formal/cubical/Sha256.agda`.
- Bitcoin serialization: https://developer.bitcoin.org/reference/block_chain.html
- Bitcoin target checks: https://github.com/bitcoin/bitcoin/blob/master/src/pow.cpp
- Compact arithmetic: https://github.com/bitcoin/bitcoin/blob/master/src/arith_uint256.cpp
- Genesis bytes/hash: https://github.com/bitcoin/bitcoin/blob/master/src/kernel/chainparams.cpp
- Runtime syntax: https://github.com/HigherOrderCO/HVM4/blob/6defdfc7dae2a3cca5dd6e74ed0612385b5646a8/docs/hvm/core.md

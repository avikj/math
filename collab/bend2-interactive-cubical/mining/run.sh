#!/usr/bin/env bash
# One native SUP evaluation. No CPU/Python/Node mining fallback.
set -Eeuo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
if [[ $# != 2 ]]; then
  printf 'Usage: BEND=/absolute/bend HVM=/absolute/hvm bash %s JOB.json NEW_OUTPUT_DIRECTORY\n' "$0" >&2
  exit 2
fi
NODE=${NODE:-node}
command -v "$NODE" >/dev/null || { echo 'Node.js 18+ is required for transport and independent verification only.' >&2; exit 127; }
JOB=$(realpath -- "$1")
OUT=$(realpath -m -- "$2")
"$NODE" "$HERE/mining.mjs" prepare "$JOB" "$OUT"
phase=preflight
trap 'rc=$?; "$NODE" "$HERE/mining.mjs" mark "$OUT" "$phase" failed "exit=$rc; raw logs retained"; exit "$rc"' ERR
record() { "$NODE" "$HERE/mining.mjs" mark "$OUT" "$phase" "$1" "${2:-}"; }
BEND=$(command -v "${BEND:-bend}") || { echo 'Set BEND to the patched cubical Bend2 executable; bootstrap.sh can build it.' >&2; false; }
HVM=$(command -v "${HVM:-hvm}") || { echo 'Set HVM to the HVM4 C executable, not HVM3.' >&2; false; }
BEND=$(realpath -- "$BEND")
HVM=$(realpath -- "$HVM")
"$NODE" "$HERE/mining.mjs" identity bend "$BEND" > "$OUT/binaries.jsonl"
"$NODE" "$HERE/mining.mjs" identity hvm4 "$HVM" >> "$OUT/binaries.jsonl"
printf 'os=%s\narch=%s\n' "$(uname -s)" "$(uname -m)" > "$OUT/platform.txt"
record passed 'exact binary hashes recorded; this is compatibility gating, not an inferred build attestation'

# --to-hvm4-full is an emitter and is not substituted for checking.
phase=typecheck
(cd "$OUT/source" && "$BEND" MiningClaim.bend --total) > "$OUT/typecheck.log" 2>&1
if grep -Eq '✗|\[unchecked\]|NOT AT THE PIN|error:|Error:|Exception|undefined|Unbound' "$OUT/typecheck.log"; then
  echo 'Native checker rejected a definition; see typecheck.log' >&2; false
fi
grep -Eq '✓|\[total\]|\[productive\]' "$OUT/typecheck.log" || { echo 'No native check/classification markers were emitted.' >&2; false; }
record passed

phase=emit
(cd "$OUT/source" && "$BEND" MiningClaim.bend --to-hvm4-full) > "$OUT/library.hvm4" 2> "$OUT/emit.stderr"
"$NODE" "$HERE/mining.mjs" link "$OUT/library.hvm4" "$OUT/input.hvm4" "$OUT/mining.hvm4"
record passed 'full cubical runtime retained; main is the existing SupGen keep/spec pattern over the supplied candidate value'

# Full 64-round SHA + double-SHA Bitcoin vectors and actual native transport.
# No known nonce is supplied to the search; it appears only in this gate.
phase=conformance
(cd "$OUT/source" && "$BEND" Gate.bend --to-hvm4-full) > "$OUT/gate.typed.hvm4" 2> "$OUT/gate-emit.stderr"
# Full-runtime roots are typed points (#Pair{type,value}).  The conformance
# verifier intentionally checks the value projection only, so retarget this
# executable gate to the already-emitted checked value @Dmain.  The typed root
# remains preserved in the retained gate.typed.hvm4 artifact.
python3 - "$OUT/gate.typed.hvm4" "$OUT/gate.hvm4" <<'PY'
import pathlib, re, sys
src = pathlib.Path(sys.argv[1]).read_text()
src, n = re.subn(r'(?m)^@main = ', '@typedGateMain = ', src, count=1)
if n != 1:
    raise SystemExit('expected exactly one typed @main gate root')
src += '\n@main = @Dmain\n'
pathlib.Path(sys.argv[2]).write_text(src)
PY
"$HVM" "$OUT/gate.hvm4" -s -C1 > "$OUT/gate.log" 2> "$OUT/gate.stderr"
"$NODE" "$HERE/mining.mjs" gate "$OUT/gate.log"
record passed

phase=native-search
LIMIT=$("$NODE" --input-type=module -e 'import fs from "node:fs"; console.log(JSON.parse(fs.readFileSync(process.argv[1],"utf8")).max_solutions)' "$OUT/job.lock.json")
record started "collapse limit=$LIMIT; candidate family is not enumerated by the host"
# A timeout is an interruption, NEVER a proof of an empty candidate family.
# Leave RUN_SECONDS unset for an unbounded executor run. Set it explicitly
# when the execution environment has a resource budget.
if [[ -n ${RUN_SECONDS:-} ]]; then
  [[ "$RUN_SECONDS" =~ ^[1-9][0-9]*$ ]] || { echo 'RUN_SECONDS must be a positive integer.' >&2; false; }
  command -v timeout >/dev/null
  timeout --signal=TERM --kill-after=10 "$RUN_SECONDS" "$HVM" "$OUT/mining.hvm4" -s "-C$LIMIT" > "$OUT/results.hvm.txt" 2> "$OUT/runtime.stderr"
else
  "$HVM" "$OUT/mining.hvm4" -s "-C$LIMIT" > "$OUT/results.hvm.txt" 2> "$OUT/runtime.stderr"
fi
record completed 'native process exited zero; no statement about unseen branches after a result-limit stop'
phase=independent-verification
"$NODE" "$HERE/mining.mjs" verify "$OUT" "$OUT/results.hvm.txt"
record passed 'raw native cubical receipts and independent SHA256d verification retained'
printf '\nRun artifacts: %s\nVerified output: %s/verified-hits.json\n' "$OUT" "$OUT"

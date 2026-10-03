#!/usr/bin/env bash
# End-to-end check of the full-runtime seam: one checker, one emitter, one net.
#   - only a checked book is emitted, and ill-typed input yields no program;
#   - the root is the checked entry as a typed point (A, a) of Σ(A : Set). A;
#   - types are emitted cells like any other (Eql, Enum, ua with coherences);
#   - the fibre law and its coinductive continuation are ordinary Bend
#     (port/FibreCoalgebra.bend) running through the same emitter;
#   - a HIT constructor's parameters are cells: read off the goal by the
#     checker, carried in the term, computed with, and kept under collapse.
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
BEND="${1:-bend}"
HVM="${2:-hvm}"
HERE="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# run FILE EXPECTED: compile (from FILE's directory, so imports resolve), then
# require the exact normal form of the root.
run() {
  local src="$1" want="$2" out
  (cd "$(dirname "$src")" && "$BEND" "$(basename "$src")" --to-hvm4-full) > "$TMP/p.hvm4" 2> "$TMP/check.log"
  grep -Fqx '@main = #Pair{@Tmain, @Dmain}' "$TMP/p.hvm4"
  out="$("$HVM" "$TMP/p.hvm4" -s 2>&1)"
  printf '%s\n' "$out"
  [ "$(printf '%s\n' "$out" | head -1)" = "$want" ] || {
    echo "$src: expected root $want" >&2
    exit 1
  }
}

run "$HERE/conductive_entry_smoke.bend" '#Pair{#Nat{},#Suc{#Suc{#Zer{}}}}'
grep -Eqx '@Tid = #Pi\{#Nat, λ&b[0-9]+u[0-9]+\. #Nat\}' "$TMP/p.hvm4"
echo "TYPED-POINT OK"

run "$HERE/port/FibreCoalgebra.bend" '#Pair{#Nat{},#Suc{#Suc{#Zer{}}}}'
run "$HERE/port/ConductiveRuntime.bend" '#Pair{#Nat{},#Suc{#Suc{#Zer{}}}}'
echo "FIBRE-LAW-AND-CONTINUATION OK"

run "$HERE/complex_cells_smoke.bend" '#Pair{#Bool{},0}'
grep -Fqx '@DnegPath = #UaU{#Bool, #Bool, @Dneg, @Dneg, @DnegLnv, @DnegLnv}' "$TMP/p.hvm4"
grep -Fqx '@DColour = #Enum{#Con{#red, #Con{#green, #Nil}}}' "$TMP/p.hvm4"
grep -Eq '^@Trefl = .*#Eql\{(b[0-9]+u[0-9]+), (b[0-9]+u[0-9]+), \2\}' "$TMP/p.hvm4"
echo "CELLS OK"

# A HIT constructor's parameters are cells the checker reads off the goal and
# carries into the term: a declared endpoint that mentions one computes with
# it (the cylinder of dbl collapses its segment at 3 to 6 at both ends), and a
# HIT value survives collapse (`-C`), where an erased parameter would have
# annihilated it.
run "$HERE/hit_param_endpoint.bend" '#Pair{#Nat{},#Suc{#Suc{#Suc{#Suc{#Suc{#Suc{#Zer{}}}}}}}}'
(cd "$HERE" && "$BEND" hit_trunc.bend --to-hvm4-full) > "$TMP/trunc.hvm4" 2>/dev/null
[ "$("$HVM" "$TMP/trunc.hvm4" -s -C10 2>&1 | head -1 | sed 's/ .*//')" = '#Pair{#HT_PTrunc{#Nat{}},#C_PTrunc_tin{#Nat{},#Suc{#Suc{#Suc{#Zer{}}}}}}' ]
echo "HIT-PARAMETERS OK"

# A superposed point of a dependent family is typed by the DUP of its goal at
# the value's label (the checker runs the net's own DUP-SUP rule on the type):
# `(&0{True,False}, &0{3n,()}) : Σ b:Bool. F(b)` checks fibrewise, and its
# typed point collapses to exactly the two diagonal readings, never a cross
# term. The different-label sibling is a registered must-fail in suite.sh.
(cd "$HERE" && "$BEND" sup_dependent.bend --to-hvm4-full) > "$TMP/supdep.hvm4" 2>/dev/null
"$HVM" "$TMP/supdep.hvm4" -s -C10 2>&1 | grep -v '^- ' | sed 's/\x1b\[[0-9;]*m//g; s/ #[0-9]*$//' > "$TMP/supdep.out"
[ "$(wc -l < "$TMP/supdep.out")" -eq 2 ]
grep -Fqx '#Pair{#Sig{#Bool{},λa.λ{0:#Unit{};λb.#Nat{}}(a)},#Pair{1,#Suc{#Suc{#Suc{#Zer{}}}}}}' "$TMP/supdep.out"
grep -Fqx '#Pair{#Sig{#Bool{},λa.λ{0:#Unit{};λb.#Nat{}}(a)},#Pair{0,#One{}}}' "$TMP/supdep.out"
echo "SUP-DEPENDENT OK"

if "$BEND" "$HERE/gate_mustfail.bend" --to-hvm4-full > "$TMP/gate.hvm4" 2>/dev/null; then
  echo "ill-typed input was emitted" >&2
  exit 1
fi
[ ! -s "$TMP/gate.hvm4" ] || { echo "ill-typed input produced output" >&2; exit 1; }
echo "CHECK-GATE OK"

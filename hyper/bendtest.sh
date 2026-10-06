#!/usr/bin/env bash
# The Bend dialect as the test suite: every corpus program with a `main` is checked
# and emitted by Bend2 (`--to-hyper`), run by hyper, and its printed value compared with Bend2's
# own normaliser. Usage: ./bendtest.sh [FILE.bend…]   (default: the whole corpus)
set -u
export LC_ALL=C.UTF-8 LANG=C.UTF-8
HERE=$(cd "$(dirname "$0")" && pwd); HYPER=${HYPER:-$HERE/hyper}
BEND=${BEND:-/home/user/bend-build/Bend2/dist-newstyle/build/x86_64-linux/ghc-9.12.2/bend-0.1.0.0/x/bend/opt/build/bend/bend}
CORPUS=$HERE/../collab/bend2-interactive-cubical
TMP=${TMPDIR:-/tmp}/hyper-bend.$$; mkdir -p "$TMP"
if [ $# -gt 0 ]; then files=("$@"); else
  files=(); for f in "$CORPUS"/*.bend "$CORPUS"/port/*.bend; do grep -q '^def main' "$f" && files+=("$f"); done; fi
pass=0; fail=0; skip=0
for f in "${files[@]}"; do
  d=$(dirname "$f"); b=$(basename "$f" .bend)
  ( cd "$d" && timeout 120 "$BEND" "$b.bend" > "$TMP/$b.oracle" 2>&1 ); orc=$?
  if [ $orc -ne 0 ] || grep -q '✗' "$TMP/$b.oracle"; then skip=$((skip+1)); echo "SKIP $b (oracle does not check)"; continue; fi
  want=$(awk 'f{print} /^$/{f=1}' "$TMP/$b.oracle")
  [ -z "$want" ] && { skip=$((skip+1)); echo "SKIP $b (no main run by the oracle)"; continue; }
  ( cd "$d" && timeout 120 "$BEND" "$b.bend" --to-hyper > "$TMP/$b.hyper" 2>/dev/null ) || { fail=$((fail+1)); echo "FAIL $b (emit)"; continue; }
  got=$(timeout 60 "$HYPER" bend "$TMP/$b.hyper" 2>"$TMP/$b.err"); rc=$?
  if [ $rc -eq 0 ] && [ "$got" == "$want" ]; then pass=$((pass+1)); echo "ok   $b  $(tail -2 "$TMP/$b.err" | tr '\n' ' ')"
  else fail=$((fail+1)); echo "FAIL $b"; echo "  want: $(echo "$want" | head -3 | cut -c1-160)"; echo "  got:  $(echo "$got" | head -3 | cut -c1-160) $(head -c 200 "$TMP/$b.err" | tr '\n' ' ')"; continue; fi
  # §10.7 schedules: the other schedule (right demand first) reaches the same value in the same count
  got2=$(HYPER_SCHEDULE=right timeout 60 "$HYPER" bend "$TMP/$b.hyper" 2>"$TMP/$b.err2")
  if [ "$got2" == "$want" ] && [ "$(tail -2 "$TMP/$b.err2")" == "$(tail -2 "$TMP/$b.err")" ]; then pass=$((pass+1))
  else fail=$((fail+1)); echo "FAIL schedule $b: left $(tail -2 "$TMP/$b.err" | tr '\n' ' ') right $(tail -2 "$TMP/$b.err2" | tr '\n' ' ')$([ "$got2" == "$want" ] || echo ' (value differs)')"; fi
done
# §10.5 sharing regimes: one line over N values (sup) costs no more than N separate runs (sep)
for sup in "$TMP"/bench_*_sup.err; do [ -f "$sup" ] || continue; sep=${sup%_sup.err}_sep.err; [ -f "$sep" ] || continue
  a=$(grep -o 'Itrs: [0-9]*' "$sup" | grep -o '[0-9]*'); b=$(grep -o 'Itrs: [0-9]*' "$sep" | grep -o '[0-9]*')
  n=$(basename "${sup%_sup.err}")
  if [ -n "$a" ] && [ -n "$b" ] && [ "$a" -le "$b" ]; then pass=$((pass+1)); echo "ok   sharing $n: sup $a ≤ sep $b"; else fail=$((fail+1)); echo "FAIL sharing $n: sup $a > sep $b"; fi
done
echo "pass=$pass fail=$fail skip=$skip"

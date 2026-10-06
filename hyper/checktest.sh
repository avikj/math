#!/usr/bin/env bash
# The checker differential (MAP.md §10.6): every corpus program, including the must-fail probes, is
# elaborated by Bend2 without a verdict (`--to-hyper-unchecked`) and checked by `hyper check`; the
# verdict per definition (✓/✗) is compared with Bend2's own checker.
set -u
export LC_ALL=C.UTF-8 LANG=C.UTF-8
HERE=$(cd "$(dirname "$0")" && pwd); HYPER=${HYPER:-$HERE/hyper}
BEND=${BEND:-/home/user/bend-build/Bend2/dist-newstyle/build/x86_64-linux/ghc-9.12.2/bend-0.1.0.0/x/bend/opt/build/bend/bend}
CORPUS=$HERE/../collab/bend2-interactive-cubical
TMP=${TMPDIR:-/tmp}/hyper-check.$$; mkdir -p "$TMP"
if [ $# -gt 0 ]; then files=("$@"); else files=("$CORPUS"/*.bend "$CORPUS"/port/*.bend); fi
agree=0; disagree=0; skipped=0; files_ok=0; files_bad=0
for f in "${files[@]}"; do
  d=$(dirname "$f"); b=$(basename "$f" .bend)
  ( cd "$d" && timeout 120 "$BEND" "$b.bend" > "$TMP/$b.oracle" 2>&1 )
  sed 's/\x1b\[[0-9;]*m//g' "$TMP/$b.oracle" | grep -E '^[✓✗] ' | grep -v '\[HIT:' | awk '{print $2, $1}' | sort > "$TMP/$b.want"
  if [ ! -s "$TMP/$b.want" ]; then skipped=$((skipped+1)); echo "SKIP $b (oracle: no verdicts)"; continue; fi
  if ! ( cd "$d" && timeout 120 "$BEND" "$b.bend" --to-hyper-unchecked > "$TMP/$b.hyper" 2>/dev/null ); then skipped=$((skipped+1)); echo "SKIP $b (no elaboration)"; continue; fi
  timeout 120 "$HYPER" check "$TMP/$b.hyper" > "$TMP/$b.out" 2>"$TMP/$b.err"
  sed 's/\x1b\[[0-9;]*m//g' "$TMP/$b.out" | grep -E '^[✓✗] ' | awk '{print $2, $1}' | sort > "$TMP/$b.got"
  a=$(join "$TMP/$b.want" "$TMP/$b.got" | awk '$2==$3' | wc -l); dis=$(join "$TMP/$b.want" "$TMP/$b.got" | awk '$2!=$3')
  n=$(wc -l < "$TMP/$b.want"); ngot=$(wc -l < "$TMP/$b.got")
  agree=$((agree+a)); nd=$(echo -n "$dis" | grep -c .); disagree=$((disagree+nd))
  if [ "$nd" -eq 0 ] && [ "$ngot" -eq "$n" ]; then files_ok=$((files_ok+1)); echo "ok   $b  ($n defs)"
  else files_bad=$((files_bad+1)); echo "DIFF $b  ($a/$n agree; hyper reported $ngot)"; echo "$dis" | sed 's/^/  /' | head -6; [ -s "$TMP/$b.err" ] && head -c 200 "$TMP/$b.err" | sed 's/^/  ! /'; fi
done
echo "files ok=$files_ok bad=$files_bad skipped=$skipped; definitions agree=$agree disagree=$disagree"

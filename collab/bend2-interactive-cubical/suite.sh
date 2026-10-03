#!/usr/bin/env bash
# The suite. Every .bend must check clean, EXCEPT the files registered below,
# which must each contain at least one rejected definition (the soundness
# probes: a proof that must not go through). Run: ./suite.sh [path-to-bend]
#
# If you add a file containing a deliberate failure, REGISTER IT HERE — an
# unregistered one reads as a regression, and a registered file that suddenly
# passes reads as the checker having gone unsound.
set -u
export LC_ALL=C.utf8 LANG=C.utf8   # without this bend aborts silently (0/0)
BEND="${1:-$(cat /tmp/BENDBIN 2>/dev/null || echo bend)}"
# Every file is also checked with --total, which refuses a file containing
# any [unchecked] definition. Guardedness is an analysis in Bend2 -- its logic
# is non-total by design -- but the cubical lane does not need that freedom,
# and 114 of the 118 files here are [total] or [productive] throughout. The
# four that are not are listed, each one deliberate: a loop is the point of
# the file.
#   loop            loop.bend       the unguarded loop itself
#   recon           recon_bach.bend a reconstruction driven to a fixed point
#   bad             streams.bend    the registered counterexample to guardedness
#   coinduction_mustfail            a must-fail probe
NONTOTAL="loop recon_bach streams coinduction_mustfail"

MUSTFAIL="coinduction_mustfail erasure glue_mustfail hfill kan_mustfail quotient_mustfail sub_mustfail transp_mustfail partial_mustfail circle_mustfail truncation_mustfail hit_circle_mustfail hit_mustfail
          silence_mustfail uaequiv_mustfail uaroundtrip gate_mustfail sup_dependent_mustfail"
cd "$(dirname "$0")" || exit 1
bad=0; n=0
for f in *.bend; do
  nm=$(basename "$f" .bend); n=$((n+1))
  out=$(timeout 300 "$BEND" "$f" 2>&1)
  if ! printf '%s' "$NONTOTAL" | tr -s ' \n' '\n\n' | grep -qx "$nm"; then
    tot=$(timeout 300 "$BEND" "$f" --total 2>&1 | grep -c 'unchecked')
    [ "$tot" -eq 0 ] || { echo "NONTOTAL $nm (has an [unchecked] definition and is not registered)"; bad=$((bad+1)); }
  fi
  ok=$(printf '%s' "$out" | grep -c "✓"); ko=$(printf '%s' "$out" | grep -c "✗")
  if printf '%s' "$MUSTFAIL" | tr -s ' \n' '\n\n' | grep -qx "$nm"; then
    [ "$ko" -ge 1 ] || { echo "MUSTFAIL-PASSED $nm (expected a rejection, got none)"; bad=$((bad+1)); }
  else
    { [ "$ko" -eq 0 ] && [ "$ok" -ge 1 ]; } || { echo "FAIL $nm ok=$ok ko=$ko"; bad=$((bad+1)); }
  fi
done

# The full target emits a checked entry as its typed point (A, a).
cond_tmp=$(mktemp)
if timeout 300 "$BEND" conductive_entry_smoke.bend --to-hvm4-full >"$cond_tmp" 2>/dev/null \
   && grep -Fqx '@main = #Pair{@Tmain, @Dmain}' "$cond_tmp"; then
  echo "TYPED-POINT ENTRY OK"
else
  echo "FAIL typed-point entry"
  bad=$((bad+1))
fi
rm -f "$cond_tmp"

echo "files=$n bad=$bad"; [ "$bad" -eq 0 ]

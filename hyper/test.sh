#!/usr/bin/env bash
# hyper/test.sh: build the net, reproduce the SAT fibre results exactly, resolve the sort declaration, and check every citation in MAP.md and NOTES.md.
set -u; cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -w -o hyper net.c || exit 1
pass=0; fail=0
if python3 satcheck.py "$PWD/hyper" > /tmp/satcheck.$$ 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL satcheck: $(tail -3 /tmp/satcheck.$$ | tr '\n' ' ')"; fi; rm -f /tmp/satcheck.$$
if python3 sortcheck.py "$PWD/hyper" > /tmp/sortcheck.$$ 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL sortcheck: $(grep FAIL /tmp/sortcheck.$$ | head -3 | tr '\n' ' ')"; fi; rm -f /tmp/sortcheck.$$
if ./cite.sh >/dev/null; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL cite: $(./cite.sh | tail -3 | tr '\n' ' ')"; fi
echo "pass=$pass fail=$fail"; [ $fail -eq 0 ]

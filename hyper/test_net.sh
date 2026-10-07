#!/bin/sh
# the net: hyper/net.c (HVM4 verbatim + hyper's agents).  Every program under n/ is run and its value and
# interaction count are pinned; satcheck must still reproduce the SAT fibre receipts exactly.
cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -w -c net.c -o net.o || exit 1
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -pthread -o hyper cell.c read.c verify.c main.c net.o -lm || exit 1
pass=0; fail=0
pin() { f=$1; want=$2; witrs=$3
  got=$(./hyper net n/$f.hvm4 2>&1 | grep -v SAT_PROFILE | grep -v '^$' | head -1); itrs=$(./hyper net n/$f.hvm4 -s 2>&1 | grep -oE '"interactions":[0-9]+' | sed 's/.*://')
  if [ "$got" = "$want" ] && [ "$itrs" = "$witrs" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f: got '$got' ($itrs) want '$want' ($witrs)"; fi; }
# Block A: the collapse as a value (COL, written %x): the fibre as a list, multiplicity conserved, dead sides dropped
pin xor   '#Cons{#Pair{#F{},#T{}},#Cons{#Pair{#T{},#F{}},#Nil{}}}' 97
pin same  '#Cons{#Pair{#F{},#F{}},#Cons{#Pair{#T{},#T{}},#Nil{}}}' 11
pin empty '#Nil{}' 35
pin diff  '#Cons{#Pair{#F{},#F{}},#Cons{#Pair{#F{},#T{}},#Cons{#Pair{#T{},#F{}},#Cons{#Pair{#T{},#T{}},#Nil{}}}}}' 38
# Block B: a declaration with no body is a coordinate, with fresh labels per unfolding (&(n){..}, a run-time label)
pin sat3  '#Cons{#Cons{#F{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Nil{}}}' 302
# ? is a fresh number, the name of a coordinate (FRS): under recursion a static label reads every unfolding as one
# coordinate (two leaves of the eight lists), a fresh label names each (eight leaves)
pin fresh '#Pair{#Cons{#Cons{#F{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Nil{}}},#Cons{#Cons{#F{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#F{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#T{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Nil{}}}}}}}}}}' 165
# MAP §0 on the net: every arrangement of [3,1,2] as a line (one fresh coordinate per place), `sorted` run on it,
# the one survivor read by %: nine comparisons, five dead sides
pin sort3 '#Cons{#Cons{1,#Cons{2,#Cons{3,#Nil{}}}},#Nil{}}' 458
# the SAT fibre receipts, exactly as recorded (research/sat_fibre): the readback path is untouched
if [ -z "$SKIP_SATCHECK" ]; then r=$(cd .. && python3 hyper/satcheck.py ./hyper/hyper net 2>&1 | tail -1); case "$r" in "satcheck pass=282 fail=0") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL satcheck: $r";; esac; fi
echo "pass=$pass fail=$fail"; [ "$fail" = 0 ]

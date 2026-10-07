#!/bin/sh
# the net: hyper/net.c (HVM4 verbatim + hyper's agents).  Every program under n/ is run and its value and
# interaction count are pinned; satcheck must still reproduce the SAT fibre receipts exactly.
cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -w -c net.c -o net.o || exit 1
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -pthread -o hyper cell.c read.c verify.c main.c net.o -lm || exit 1
pass=0; fail=0
pin() { f=$1; want=$2; witrs=$3
  got=$(./hyper net n/$f.hvm4 2>&1 | grep -v SAT_PROFILE | grep -v '^$' | head -1 | sed 's/↑//g'); itrs=$(./hyper net n/$f.hvm4 -s 2>&1 | grep -oE '"interactions":[0-9]+' | sed 's/.*://')
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
# Block C: the cubical layer as net programs (n/cubical.hvm4, the lane's full-runtime prelude): coe dispatching at run
# time on the universe path, hcomp deciding a face, transport along one shared superposed line read by %
pin ua      '#Pair{#T{},#T{}}' 268
pin hcnat   '#Suc{#Zer{}}' 25
pin supline '#Cons{#T{},#Cons{#F{},#Nil{}}}' 269
# Block D: verify is decide — a typed point's judgment is one equation T === @infer(D) on the net (n/judge.hvm4):
# Π, Σ, Bool, Nat, Eql/refl over quoted syntax; two must-fail cases reduce to 0; a superposed point against a
# goal is a superposition of equations (EQL-SUP, no rule added), read by %
pin judge '#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{#Cons{1,#Cons{0,#Nil{}}},#Nil{}}}}}}}}' 1290
# the cubical formers (n/judgecub.hvm4), twenty cases: plm against Path (and a wrong end), path application, coe along a
# constant line (and a wrong target), ua of the identity, hcomp with a tube whose i0 end is the base (and one whose is
# not), Glue with no face, glue/unglue, a Glue face with a wrong contraction (0) and with the identity equivalence's
# contraction (1: the endpoint rule for a typed neutral path, Σ η and path η), λp. <i> p @ i by path η, Bool/Nat/List
# eliminators, fst/snd (and snd against the wrong type), and a superposed cubical point read by %.
# The identity equivalence checks only with fresh labels per binder instantiation (the default; -L is HVM4's).
pin judgecub '#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{#Cons{1,#Cons{0,#Nil{}}},#Nil{}}}}}}}}}}}}}}}}}}}}}' 36337
# the circle, Partial and systems (branches on their cells, agreement, coverage), transp with a cofibration (the line
# constant on φ), Sub/inS/outS, the set quotient with its point and path constructors and its recursor (n/judgehit.hvm4)
pin judgehit '#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Nil{}}}}}}}}}}}}}}}}}}}}}' 6933
# MAP §0 on the net, with types (n/declare.hvm4): sort A = Σ B. (perm A B ≡ True) × (sorted B ≡ True) at A = [2,0,1];
# D is the line of every arrangement with (refl, refl); the judgment runs once on the line (EQL commutes over it,
# 49 EQL-SUP-L), five sides erase, and % is the fibre: the one point ([0,1,2], (refl, refl))
pin declare '#Cons{#SPair{#SCons{#SZer{},#SCons{#SSuc{#SZer{}},#SCons{#SSuc{#SSuc{#SZer{}}},#SNil{}}}},#SPair{#SRefl{},#SRefl{}}},#Nil{}}' 10625
# an enumeration as a type (n/judgeenum.hvm4): the type, a symbol against it (and one not in it), a match with every
# symbol covered (and one without), and the match evaluated
pin judgeenum '#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{#Suc{#Zer{}},#Nil{}}}}}}}' 1609
# the SAT fibre receipts, exactly as recorded (research/sat_fibre) under -L, the labels HVM4 gave them; the readback path is untouched
if [ -z "$SKIP_SATCHECK" ]; then r=$(cd .. && python3 hyper/satcheck.py ./hyper/hyper net -L 2>&1 | tail -1); case "$r" in "satcheck pass=282 fail=0") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL satcheck: $r";; esac; fi
echo "pass=$pass fail=$fail"; [ "$fail" = 0 ]

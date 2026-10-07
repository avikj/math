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
# Block C: the cubical layer as net programs (n/cubical.hvm4): ua is CCHM's Glue line and transport along it is the Glue
# transport rule (no shortcut), a Glue at a true face is its partial type, hcomp deciding a face, transport along one
# shared superposed line read by %
pin ua '#Pair{#F{},#T{}}' 2858
pin hcnat '#Suc{#Zer{}}' 25
pin supline '#Cons{#F{},#Cons{#F{},#Nil{}}}' 1712
# Block D: verify is decide — a typed point's judgment is one equation T === @infer(D) on the net (n/judge.hvm4):
# Π, Σ, Bool, Nat, Eql/refl over quoted syntax; two must-fail cases reduce to 0; a superposed point against a
# goal is a superposition of equations (EQL-SUP, no rule added), read by %
pin judge '#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{#Cons{1,#Cons{0,#Nil{}}},#Nil{}}}}}}}}' 1299
# the cubical formers (n/judgecub.hvm4), twenty cases: plm against Path (and a wrong end), path application, coe along a
# constant line (and a wrong target), ua of the identity, hcomp with a tube whose i0 end is the base (and one whose is
# not), Glue with no face, glue/unglue, a Glue face with a wrong contraction (0) and with the identity equivalence's
# contraction (1: the endpoint rule for a typed neutral path, Σ η and path η), λp. <i> p @ i by path η, Bool/Nat/List
# eliminators, fst/snd (and snd against the wrong type), and a superposed cubical point read by %.
# The identity equivalence checks only with fresh labels per binder instantiation (the default; -L is HVM4's).
pin judgecub '#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{#Cons{1,#Cons{0,#Nil{}}},#Nil{}}}}}}}}}}}}}}}}}}}}}' 56989
# faces with a bound interval variable are decided per cell: the face-bearing parts of a type (Partial's carrier,
# Sub's element, Glue's faces) are syntax suspended over the environment, so restriction to a cell is evaluation under
# the environment restricted; inconsistent cells are dropped
# the circle, Partial and systems (branches on their cells, agreement, coverage), transp with a cofibration — the line
# constant on φ by the marker test: L at two markers equal on every cell (a moving line on φ=i1 fails, on φ=i0 passes,
# a constant line under a binder passes) — Sub/inS/outS, the set quotient with its constructors and recursor (n/judgehit.hvm4)
pin judgehit '#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}' 182879
# index §9.15 on the net, with types (n/declare.hvm4): sort A = Σ B : Rearr A. Sorted B ≡ True at A = [2,0,1] indexed
# as a tree; D = @any(Tspec): the coordinate over Rearr A is the relabellings, factored over the index (§9.2, §9.8: six
# points, one fresh coordinate per interleaving choice), refl over the equation; the judgment cuts five sides and % is
# the fibre: ([0,1,2], refl)
pin declare '#Cons{#SPair{#SCons{#SVal{#Zer{}},#SCons{#SVal{#Suc{#Zer{}}},#SCons{#SVal{#Suc{#Suc{#Zer{}}}},#SNil{}}}},#SRefl{}},#Nil{}}' 4578
# index §9 followed entry by entry on numbers (n/sort9.hvm4): the whole relabelling line cut once by Sorted at n=4, and the
# declaration followed through 9.3/9.6/9.15 on the balanced numeral (n=8: 17 comparisons, 475 interactions) and on the
# tally (20 comparisons, 543): OP2-NUM-NUM is the count of comparisons, 69 = 32 + 17 + 20
pin sort9 '#Pair{#Cons{#Cons{0,#Cons{1,#Cons{2,#Cons{3,#Nil{}}}}},#Nil{}},#Pair{#Cons{0,#Cons{1,#Cons{2,#Cons{3,#Cons{4,#Cons{5,#Cons{6,#Cons{7,#Nil{}}}}}}}}},#Cons{0,#Cons{1,#Cons{2,#Cons{3,#Cons{4,#Cons{5,#Cons{6,#Cons{7,#Nil{}}}}}}}}}}}' 2731
c=$(./hyper net n/sort9.hvm4 -s 2>&1 | grep -oE '"OP2-NUM-NUM":[0-9]+' | sed 's/.*://'); if [ "$c" = 69 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL sort9 comparisons: $c want 69"; fi
# the comparison as one cell per pair (n/sort9cell.hvm4): the whole line cut once touches every pair (6, 28); posed per
# node it touches 5 at n=4 (merge's count), 22 balanced and 20 tally at n=8; 53 = 6 + 5 + 22 + 20 distinct pairs
pin sort9cell '#Pair{#Cons{#Cons{#S{#Z{}},#Cons{#S{#S{#S{#Z{}}}},#Cons{#Z{},#Cons{#S{#S{#Z{}}},#Nil{}}}}},#Nil{}},#Pair{#Cons{#S{#Z{}},#Cons{#S{#S{#S{#Z{}}}},#Cons{#Z{},#Cons{#S{#S{#Z{}}},#Nil{}}}}},#Pair{#Cons{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Cons{#S{#Z{}},#Cons{#S{#S{#S{#S{#Z{}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}},#Cons{#Z{},#Cons{#S{#S{#S{#S{#S{#Z{}}}}}},#Cons{#S{#S{#Z{}}},#Nil{}}}}}}}}},#Cons{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Cons{#S{#Z{}},#Cons{#S{#S{#S{#S{#Z{}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}},#Cons{#Z{},#Cons{#S{#S{#S{#S{#S{#Z{}}}}}},#Cons{#S{#S{#Z{}}},#Nil{}}}}}}}}}}}}' 52144
c=$(./hyper net n/sort9cell.hvm4 -s 2>&1 | grep -oE '"OP2-NUM-NUM":[0-9]+' | sed 's/.*://'); if [ "$c" = 53 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL sort9cell comparisons: $c want 53"; fi
# an enumeration as a type (n/judgeenum.hvm4): the type, a symbol against it (and one not in it), a match with every
# symbol covered (and one without), and the match evaluated
pin judgeenum '#Cons{1,#Cons{1,#Cons{0,#Cons{1,#Cons{0,#Cons{#Suc{#Zer{}},#Nil{}}}}}}}' 1627
# the SAT fibre receipts, exactly as recorded (research/sat_fibre) under -L, the labels HVM4 gave them; the readback path is untouched
if [ -z "$SKIP_SATCHECK" ]; then r=$(cd .. && python3 hyper/satcheck.py ./hyper/hyper net -L 2>&1 | tail -1); case "$r" in "satcheck pass=282 fail=0") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL satcheck: $r";; esac; fi
echo "pass=$pass fail=$fail"; [ "$fail" = 0 ]

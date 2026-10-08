#!/bin/sh
# the net: hyper/net.c (HVM4 verbatim + hyper's agents).  Every program under n/ is run and its value and
# interaction count are pinned; satcheck must still reproduce the SAT fibre receipts exactly.
cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -w -c net.c -o net.o || exit 1
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -pthread -o hyper cell.c read.c verify.c main.c net.o -lm || exit 1
pass=0; fail=0
export SAT_MAX_ITRS=4000000000 SAT_MAX_HEAP=1300000000
# no program in the suite touches a primitive: the parser refuses an operator outside -L, and the ledger must show none
pin() { f=$1; want=$2; witrs=$3
  if ./hyper net n/$f.hvm4 -s 2>&1 | grep -qE '"OP2-[A-Z-]+":[1-9]'; then echo "FAIL $f: primitive arithmetic in the ledger"; fail=$((fail+1)); return; fi
  got=$(./hyper net n/$f.hvm4 2>&1 | grep -v SAT_PROFILE | grep -v '^$' | head -1 | sed 's/↑//g'); itrs=$(./hyper net n/$f.hvm4 -s 2>&1 | grep -oE '"interactions":[0-9]+' | sed 's/.*://')
  if [ "$got" = "$want" ] && [ "$itrs" = "$witrs" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f: got '$got' ($itrs) want '$want' ($witrs)"; fi; }
# Block A: the collapse as a value (COL, written %x): the fibre as a list, multiplicity conserved, dead sides dropped
pin xor   '#Cons{#Pair{#F{},#T{}},#Cons{#Pair{#T{},#F{}},#Nil{}}}' 97
pin same  '#Cons{#Pair{#F{},#F{}},#Cons{#Pair{#T{},#T{}},#Nil{}}}' 11
pin empty '#Nil{}' 35
pin diff  '#Cons{#Pair{#F{},#F{}},#Cons{#Pair{#F{},#T{}},#Cons{#Pair{#T{},#F{}},#Cons{#Pair{#T{},#T{}},#Nil{}}}}}' 38
# Block B: a declaration with no body is a coordinate, with fresh labels per unfolding (&(n){..}, a run-time label)
pin sat3  '#Cons{#Cons{#F{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Nil{}}}' 305
# ? is a fresh number, the name of a coordinate (FRS): under recursion a static label reads every unfolding as one
# coordinate (two leaves of the eight lists), a fresh label names each (eight leaves)
pin fresh '#Pair{#Cons{#Cons{#F{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Nil{}}},#Cons{#Cons{#F{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#F{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#T{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#F{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#F{},#Cons{#T{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#F{},#Nil{}}}},#Cons{#Cons{#T{},#Cons{#T{},#Cons{#T{},#Nil{}}}},#Nil{}}}}}}}}}}' 165
# index 0.3 / 0.4 / 0.7 / 0.8 / 0.11 on the net (n/interval.hvm4): a path is &I{a,b}, a face is |0I / |1I, the interval's
# operations are reparametrisations of a cube; all sixteen laws of 0.3 hold as vertex equality; the contraction of the
# one fact reads (x, refl) at i=0 and (y, p) at i=1
pin interval '#Pair{[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],#Pair{#Pair{#A{},#A{}},#Pair{#B{},&J{#A{},#B{}}}}}' 2778
# index 6.1–6.3 / 9.11 on the net (n/numeral.hvm4): Bool is one coordinate, a numeral is its bits, the type of k-bit
# numerals is the k-cube; addition place by place with carries, comparison from the top as a cut; 3+5, the 2-cube + 3
# as a fibre, 3 <= 5, and <= on the 2-cube read by %
pin numeral '#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}},#Pair{#Cons{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#S{#Z{}}}}}},#Cons{#S{#S{#S{#S{#Z{}}}}},#Cons{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Nil{}}}}},#Pair{#T{},#Cons{#T{},#Cons{#T{},#Cons{#T{},#Nil{}}}}}}}' 870
# index §9 on the net (n/sort.hvm4): the declaration Σ B. (B is a rearrangement of A) × Sorted B, the input indexed by the
# cube; the rearrangements as a cube with one named coordinate per interleaving choice (9.2, 9.8, 9.11), Sorted as the
# restriction taking at each coordinate the face the head comparison names (9.3, 9.6), the faces kept as the permutation
# (0.2, 3.6) and replayed as verification (8.6).  Elements are numerals (bits), nothing primitive.  Faces taken = comparisons
# made: 5 at n=4, 17 at n=8 balanced, 20 on the tally (9.9); the balanced numeral is cheaper than the tally (9.7, 9.11);
# the unrestricted coordinate at n=4 has 24 = 4! vertices (9.2, 9.8)
pin sort '#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}},#Pair{#Pair{#Cons{#Z{},#Cons{#S{#Z{}},#Cons{#S{#S{#Z{}}},#Cons{#S{#S{#S{#Z{}}}},#Nil{}}}}},#Pair{#S{#S{#S{#S{#S{#Z{}}}}}},1}},#Pair{#Pair{#Cons{#Z{},#Cons{#S{#Z{}},#Cons{#S{#S{#Z{}}},#Cons{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#Z{}}}}},#Cons{#S{#S{#S{#S{#S{#Z{}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}},#Nil{}}}}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}},1}},#Pair{#Cons{#Z{},#Cons{#S{#Z{}},#Cons{#S{#S{#Z{}}},#Cons{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#Z{}}}}},#Cons{#S{#S{#S{#S{#S{#Z{}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}},#Nil{}}}}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}},1}}}}}' 13815
# the type of the matrix product (n/product.hvm4): the defining equations taken on the cube of all inputs at once,
# the function as one shape; its normal form kept as the shape (no collapse to vertices), 2x2 with 1-bit entries
pin product '#Blk{#Leaf{&d__P{&d__S{#Cons{#F{},#Nil{}},&d__1{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d__${&d__S{#Cons{#F{},#Nil{}},&d__1{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d__S{#Cons{#T{},#Nil{}},&d__1{#Cons{#T{},#Nil{}},#Cons{#F{},#Cons{#T{},#Nil{}}}}}}}},#Leaf{&d__P{&d__S{#Cons{#F{},#Nil{}},&d_aw{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d_aF{&d__S{#Cons{#F{},#Nil{}},&d_aw{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d__S{#Cons{#T{},#Nil{}},&d_aw{#Cons{#T{},#Nil{}},#Cons{#F{},#Cons{#T{},#Nil{}}}}}}}},#Leaf{&d_aT{&d_aW{#Cons{#F{},#Nil{}},&d__1{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d__${&d_aW{#Cons{#F{},#Nil{}},&d__1{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d_aW{#Cons{#T{},#Nil{}},&d__1{#Cons{#T{},#Nil{}},#Cons{#F{},#Cons{#T{},#Nil{}}}}}}}},#Leaf{&d_aT{&d_aW{#Cons{#F{},#Nil{}},&d_aw{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d_aF{&d_aW{#Cons{#F{},#Nil{}},&d_aw{#Cons{#F{},#Nil{}},#Cons{#T{},#Nil{}}}},&d_aW{#Cons{#T{},#Nil{}},&d_aw{#Cons{#T{},#Nil{}},#Cons{#F{},#Cons{#T{},#Nil{}}}}}}}}}' 3515
# index 5.11 / 5.13 / 5.24 on net.c (n/diamond.hvm4): one term, eight normaliser schedules (-R), one ledger; the
# seeded order is confirmed to differ (schedule_flips > 0) and the interaction count does not move
d0=$(./hyper net n/diamond.hvm4 -s 2>&1 | grep -oE '"interactions":[0-9]+' | sed 's/.*://'); dok=1
for R in 1 2 3 5 8 13 21; do o=$(./hyper net n/diamond.hvm4 -s -R $R 2>&1); di=$(echo "$o" | grep -oE '"interactions":[0-9]+' | sed 's/.*://'); fl=$(echo "$o" | grep -oE '"schedule_flips":[0-9]+' | sed 's/.*://'); [ "$di" = "$d0" ] && [ "$fl" != 0 ] || { dok=0; echo "FAIL diamond R=$R: $di flips=$fl want $d0"; }; done
[ "$d0" = 1242 ] || { dok=0; echo "FAIL diamond: $d0 want 1242"; }; if [ $dok = 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
echo "pass=$pass fail=$fail"; [ "$fail" = 0 ]

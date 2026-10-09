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
# index 6.1-6.3 on the net (n/number.hvm4): a number is a multitude of position-less units, its relabellings
# discarded; counting reads the vertices; addition is disjoint union, multiplication is product; the ring
# identities hold by construction and are read off as counts: 2+3, 2*3, 3+2, 2(3+5), 2*3+2*5, (2+3)(5+2), (2*3)*5
pin number '#Pair{#S{#S{#S{#S{#S{#Z{}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Pair{#S{#S{#S{#S{#S{#Z{}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}' 2624
# the type of the matrix product generic in its entries (n/product.hvm4): entries are named units, C_ik = sum_j a_ij x b_jk
# on the complex; the normal form of each entry is its monomials, eight cells in all
pin product '#Pair{#Blk{#Cons{#Pr{#A11{},#B11{}},#Cons{#Pr{#A12{},#B21{}},#Nil{}}},#Cons{#Pr{#A11{},#B12{}},#Cons{#Pr{#A12{},#B22{}},#Nil{}}},#Cons{#Pr{#A21{},#B11{}},#Cons{#Pr{#A22{},#B21{}},#Nil{}}},#Cons{#Pr{#A21{},#B12{}},#Cons{#Pr{#A22{},#B22{}},#Nil{}}}},#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}' 277
# the integers as the repo constructs them (n/integer.hvm4): a loop, directed units, composition is union, the winding
# is read (charge-adds 3+2, mirror-cancels, 3 forward 2 back, (-2)(-3), 2(-3))
pin integer '#Pair{#W{#S{#S{#S{#S{#S{#Z{}}}}}},#Z{}},#Pair{#W{#Z{},#Z{}},#Pair{#W{#S{#Z{}},#Z{}},#Pair{#W{#S{#S{#S{#S{#S{#S{#Z{}}}}}}},#Z{}},#W{#Z{},#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}' 665
# the signed product type (n/product_signed.hvm4): the direct shape and, as a different starting term, the
# seven-product writing; their readings by winding per monomial agree; cells formed: 8 against 32
pin product_signed '#Pair{#Pair{#Blk{#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}}},#Blk{#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#S{#Z{}},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Cons{#W{#Z{},#Z{}},#Nil{}}}}}}}}}}}}}}}}}}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}},#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}' 53987
# the N x N product type on the index cube (n/blocks.hvm4): product of blocks the type again, product of leaves one
# cell, sum of leaves one shared cell, negation one cell; the defining shape and the seven-product writing side by
# side at depth 2 (4x4). Products formed (APP-LAM) by depth 1..5: direct 60/452/3428/26596/209380 (x8), seven
# 139/1460/12267/94156/692339 (x7.4); the rest of the seven term's interactions is the unsharing of its output on
# reading (DUP-NOD), which 5.21 does not charge and net.c does (open defect)
pin blocks '{#P1{#P1{#B{}}},#P1{#P2{#B{}}}},#Sum{#P4{#P1{#B{}}},#P4{#P2{#B{}}}}}},#Neg{#Pr{#Sum{#Sum{#P3{#P3{#A{}}},#Neg{#P3{#P1{#A{}}}}},#Sum{#P4{#P3{#A{}}},#Neg{#P4{#P1{#A{}}}}}},#Sum{#P1{#P1{#B{}}},#P1{#P2{#B{}}}}}}},#Sum{#Pr{#Sum{#P1{#P3{#A{}}},#Neg{#P1{#P1{#A{}}}}},#Sum{#Sum{#P2{#P1{#B{}}},#P2{#P2{#B{}}}},#Neg{#Sum{#P4{#P1{#B{}}},#P4{#P2{#B{}}}}}}},#Pr{#Sum{#Sum{#P3{#P3{#A{}}},#Neg{#P3{#P1{#A{}}}}},#Neg{#Sum{#P1{#P3{#A{}}},#Neg{#P1{#P1{#A{}}}}}}},#Sum{#Sum{#P1{#P1{#B{}}},#P1{#P2{#B{}}}},#Sum{#P2{#P1{#B{}}},#P2{#P2{#B{}}}}}}}}}}}}}}' 6872
# the writing type at a node for the polynomial product (n/writing.hvm4), posed as sort is posed: cells are
# coordinates, the equations C = A.B are faces, the cell fixed by the swap is one representative (its choices are
# exchanged by the substitutions x -> 1-x, 1/x, -x, which the faces verify on the point as identities of the object),
# the orbit cell's u and v as their classes. One point, Karatsuba; 25 sides erased; the three images hold (T, T, T)
pin writing '#Pair{#Cons{#W{#U{#P{},#P{}},#V{#P{},#P{}},#Wc{#O{},#P{},#O{}}},#Cons{#W{#U{#P{},#O{}},#V{#P{},#O{}},#Wc{#P{},#N{},#O{}}},#Cons{#W{#U{#O{},#P{}},#V{#O{},#P{}},#Wc{#O{},#N{},#P{}}},#Nil{}}}},#Pair{#Pair{#T{},#Cons{#W{#U{#P{},#O{}},#V{#P{},#O{}},#Wc{#P{},#N{},#O{}}},#Cons{#W{#U{#P{},#P{}},#V{#P{},#P{}},#Wc{#O{},#P{},#O{}}},#Cons{#W{#U{#O{},#N{}},#V{#O{},#N{}},#Wc{#O{},#N{},#P{}}},#Nil{}}}}},#Pair{#Pair{#T{},#Cons{#W{#U{#P{},#P{}},#V{#P{},#P{}},#Wc{#O{},#P{},#O{}}},#Cons{#W{#U{#O{},#P{}},#V{#O{},#P{}},#Wc{#O{},#N{},#P{}}},#Cons{#W{#U{#P{},#O{}},#V{#P{},#O{}},#Wc{#P{},#N{},#O{}}},#Nil{}}}}},#Pair{#T{},#Cons{#W{#U{#P{},#N{}},#V{#P{},#N{}},#Wc{#O{},#N{},#O{}}},#Cons{#W{#U{#P{},#O{}},#V{#P{},#O{}},#Wc{#P{},#P{},#O{}}},#Cons{#W{#U{#O{},#N{}},#V{#O{},#N{}},#Wc{#O{},#P{},#P{}}},#Nil{}}}}}}}}' 18597
# the symmetry of the 2x2 product derived from its generators (n/sym22.hvm4): 24 relabellings (six of order 6); the
# shear, conjugation by [[1,1],[0,1]], as an identity on cells; Strassen's writing holds the faces, and so do its
# images under the shear and under the order-6 element (8.6); alphabet-orbits: the trace cell 1, S x S x S 10, an
# orbit cell 36
pin sym22 '#Pair{#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}},#T{}},#Pair{#Pair{#T{},#T{}},#Pair{#S{#Z{}},#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}},#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}' 5333458
# the 2x2 writing type at a node posed as sort is posed (n/writing22.hvm4): the fixed cell's two classes, the orbit
# generator over its three conjugacy classes, u over its sixteen classes under the generator's centraliser, v and w
# coordinates the faces cut, nothing else posed: 8 points, all Strassen's shape (its sign and class variants),
# 23,860 sides erased, the other two generator classes empty
pin writing22 '#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}},#Cons{#W{#Q{#P{},#O{},#O{},#P{}},#Q{#P{},#O{},#O{},#P{}},#Q{#P{},#O{},#O{},#P{}}},#Cons{#W{#Q{#O{},#P{},#O{},#P{}},#Q{#O{},#O{},#N{},#P{}},#Q{#N{},#O{},#O{},#O{}}},#Cons{#W{#Q{#O{},#O{},#O{},#N{}},#Q{#P{},#O{},#P{},#O{}},#Q{#P{},#N{},#O{},#O{}}},#Cons{#W{#Q{#O{},#O{},#N{},#P{}},#Q{#N{},#O{},#O{},#O{}},#Q{#O{},#P{},#O{},#P{}}},#Cons{#W{#Q{#P{},#O{},#P{},#O{}},#Q{#P{},#N{},#O{},#O{}},#Q{#O{},#O{},#O{},#N{}}},#Cons{#W{#Q{#N{},#O{},#O{},#O{}},#Q{#O{},#P{},#O{},#P{}},#Q{#O{},#O{},#N{},#P{}}},#Cons{#W{#Q{#P{},#N{},#O{},#O{}},#Q{#O{},#O{},#O{},#N{}},#Q{#P{},#O{},#P{},#O{}}},#Nil{}}}}}}}}}' 17120271
# the lower bound in the index posing (5.27): the symmetric form's shorter lengths read by %% are empty: the fixed cell
# alone (length 1): 5 sides erased, no leaf; the orbit alone (length 6): 729 sides erased, no leaf
# the 2x2 writing type with the index as the cube (n/writing22q.hvm4): nothing derived outside the net; the reading %%
# projects the choice coordinates lazily and discards relabellings (6.1); the ledger and the reading's counts are pinned
r=$(./hyper net n/writing22q.hvm4 -s 2>&1); wi=$(echo "$r" | grep -oE '"interactions":[0-9]+' | sed 's/.*://'); wv=$(echo "$r" | grep -oE '"COLQ-VAL":[0-9]+' | sed 's/.*://'); ws=$(echo "$r" | grep -oE '"COLQ-SAME":[0-9]+' | sed 's/.*://'); we=$(echo "$r" | grep -oE '"COLQ-ERA":[0-9]+' | sed 's/.*://')
if [ "$wi" = 10009786 ] && [ "$wv" = 24 ] && [ "$ws" = 24 ] && [ "$we" = 87213 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL writing22q: itrs=$wi val=$wv same=$ws era=$we want 10009786/24/24/87213"; fi
# the reading's classes under the identities the net verified (n/classes22.hvm4): the 24 leaves of % carried into their
# orbits under the relabellings, the scaling and the shear within the alphabet: 3 classes, orbits of 8, 48 and 24
pin classes22 '#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}},#Pair{#S{#S{#S{#Z{}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},#Cons{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}},#Nil{}}}}}}' 36382729
# with the per-pair basis change (A -> PA, C -> C P^-1, found by the faces among row and column shears) no word of
# length <= 5 in all the identities, staying in the alphabet, joins the three classes (n/reach22.hvm4)
pin reach22 '#Pair{#F{},#Pair{#F{},#F{}}}' 149685846
# the type's symmetry group read off the cube (n/sym22g.hvm4): 3072 slot-preserving relabellings as choices, the
# faces keep 48, their orders read on the entries: 1 of order 1, 19 of 2, 8 of 3, 12 of 4, 8 of 6
pin sym22g '' 13826800
# the N x N product executed with the writing the net read from the type (n/blocks22.hvm4): at depth k the net forms
# 7^k products (1, 7, 49, 343 at depths 0..3; pinned at depth 2: 49 products, 16 entries of C)
pin blocks22 '#Pair{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#S{#Z{}}}}}}}}}}}}}}}}}}' 10043177
# index 5.11 / 5.13 / 5.24 on net.c (n/diamond.hvm4): one term, eight normaliser schedules (-R), one ledger; the
# seeded order is confirmed to differ (schedule_flips > 0) and the interaction count does not move
d0=$(./hyper net n/diamond.hvm4 -s 2>&1 | grep -oE '"interactions":[0-9]+' | sed 's/.*://'); dok=1
for R in 1 2 3 5 8 13 21; do o=$(./hyper net n/diamond.hvm4 -s -R $R 2>&1); di=$(echo "$o" | grep -oE '"interactions":[0-9]+' | sed 's/.*://'); fl=$(echo "$o" | grep -oE '"schedule_flips":[0-9]+' | sed 's/.*://'); [ "$di" = "$d0" ] && [ "$fl" != 0 ] || { dok=0; echo "FAIL diamond R=$R: $di flips=$fl want $d0"; }; done
[ "$d0" = 1242 ] || { dok=0; echo "FAIL diamond: $d0 want 1242"; }; if [ $dok = 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
echo "pass=$pass fail=$fail"; [ "$fail" = 0 ]

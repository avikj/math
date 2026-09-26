#!/usr/bin/env bash
# hyper/test.sh — the substrate's checks: values, and the ledger's count where a check is about cost.
set -u; cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -o hyper cell.c read.c main.c -lm || exit 1
pass=0; fail=0
nat() { local s='#Zer{}'; local k; for ((k=0;k<$1;k++)); do s="#Suc{$s}"; done; echo "$s"; }   # a numeral is a point of Nat
check() { got=$(./hyper run "$1" "$2" 2>&1 | head -1); if [ "$got" = "$3" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1 $2: got '$got' want '$3'"; fi; }
check t/basic.hyper main      '#Suc{#Suc{#Suc{#Suc{#Zer{}}}}}'
# §10.4 capture probes: cap4 = 4, two∘two = 4, the triple = 16
check t/basic.hyper cap4    "$(nat 4)"
check t/basic.hyper two-two "$(nat 4)"
check t/basic.hyper triple  "$(nat 16)"
check t/lazy.hyper  main      '#False{}'
check t/sup.hyper   pick0     "$(nat 1)"
check t/sup.hyper   pick1     "$(nat 2)"
got=$(./hyper run t/sup.hyper dist | head -1); case "$got" in "&"*"{$(nat 6),$(nat 7)}") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL dist: $got";; esac
got=$(./hyper run t/sup.hyper matchsup | head -1); case "$got" in '&'*'{#False{},#True{}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL matchsup: $got";; esac
check t/sup.hyper   main      "#Pair{$(nat 1),$(nat 2)}"
check t/kan.hyper   reg       "$(nat 5)"
check t/kan.hyper   suptrp    '#True{}'
check t/kan.hyper   hc-true   "$(nat 7)"
check t/kan.hyper   hc-none   "$(nat 0)"
check t/kan.hyper   hc-nat    '#Suc{#Zer{}}'
check t/kan.hyper   pitrp     "$(nat 9)"
# a Glue type with a true face IS that partial type (glueT)
got=$(./hyper run t/ua.hyper glue-at-0 | head -1); case "$got" in '#Bool{}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL glue-at-0: $got";; esac
check t/ua.hyper    fwd-true  '#False{}'
check t/ua.hyper    fwd-false '#True{}'
check t/ua.hyper    bwd-true  '#False{}'
# §10.5 sharing: a transport consumed k times costs one transport plus k small increments (linear in k, each ≪ the transport)
u1=$(./hyper run t/ua.hyper use1 | sed -n 's/^- Itrs: //p'); u2=$(./hyper run t/ua.hyper use2 | sed -n 's/^- Itrs: //p'); u4=$(./hyper run t/ua.hyper use4 | sed -n 's/^- Itrs: //p')
if [ $((u4-u1)) -eq $((3*(u2-u1))) ] && [ $((u2-u1)) -lt 10 ] && [ "$u1" -gt 50 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL sharing k uses: $u1 $u2 $u4"; fi
# composites in the universe: hcomp in Set is a Glue type (transpEquiv); the inverse and Pi lines of ua
check t/setcomp.hyper via-inv      '#False{}'
check t/setcomp.hyper via-pi       '#False{}'
check t/setcomp.hyper via-negneg-t '#True{}'
check t/setcomp.hyper via-negneg-f '#False{}'
# higher inductive types: endpoint from the type, eliminator at a symbolic interval, face into a stuck spine,
# eliminator over a composite (comp along the motive), transport pushing into a constructor's field
check t/hit.hyper loop0     '#base{}'
check t/hit.hyper at-sym    "$(nat 2)"
check t/hit.hyper at-0      "$(nat 1)"
check t/hit.hyper faced     "$(nat 1)"
check t/hit.hyper helim-sq  '#Zer{}'
got=$(./hyper run t/hit.hyper sup-pt | head -1); case "$got" in "&"*"{$(nat 1),$(nat 1)}") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL sup-pt: $got";; esac
check t/hit.hyper merid-t   '#merid{#Bool{},#False{}}'
check t/hit.hyper merid-t0  '#north{#Bool{}}'
# the interval is De Morgan, not Boolean: absorption holds, complement does not
got=$(./hyper run t/kan.hyper absorb | head -1);   case "$got" in i[0-9]*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL absorb: $got";; esac
got=$(./hyper run t/kan.hyper nocompl | head -1);  case "$got" in '~i'*'∨i'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL nocompl: $got";; esac
got=$(./hyper run t/kan.hyper demorgan | head -1); case "$got" in '~i'*'∨~i'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL demorgan: $got";; esac
# no capture: the face at M passes inside; the inner sup keeps its own fresh name (a heap address, not a fixed label)
got=$(./hyper run t/sup.hyper nocapture | head -1); case "$got" in "&"*"{$(nat 5),$(nat 6)}") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL nocapture: $got";; esac
# the machine that asks (§5): questions from the world, an ASK answered by the world
got=$(printf '(lam p (proj 0 p))\n(lam t (proj 0 (proj 1 t)))\n' | ./hyper interact t/interact.hyper main | grep -v Itrs | tr '\n' ' ')
if [ "$got" == "#Pair{$(nat 1),#Pair{$(nat 2),$(nat 3)}} $(nat 1) #Pair{$(nat 1),#Pair{$(nat 2),$(nat 3)}} " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL interact: $got"; fi
got=$(printf '(ctr True)\n(lam p (proj 1 p))\n' | ./hyper interact t/interact.hyper asks | grep -v Itrs | tr '\n' ' ')
if [ "$got" == "? #Who{} #Pair{#True{},$(nat 7)} $(nat 7) " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL ask: $got"; fi
# §3.3 erase at the projection: a forgotten port costs one row where it is forgotten; the fibre's size never enters
checkn() { got=$(./hyper run "$1" "$2" 2>&1 | grep -v Words | tr '\n' ' '); if [ "$got" = "$3 - Itrs: $4 " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1 $2: got '$got' want '$3 - Itrs: $4'"; fi; }
# §3 a demanded port fires once: a redex held by both sides of a distribution is one row (3*4 once, not per side)
checkn t/erase.hyper fst-big "$(nat 1)" 2
checkn t/erase.hyper and-f   '#False{}' 4
checkn t/erase.hyper and-t   '#True{}' 3
checkn t/erase.hyper const   "$(nat 7)" 2
checkn t/erase.hyper dflt    "$(nat 3)" 3
checkn t/erase.hyper carry   "$(nat 1)" 2
# the census of a question (Fibre.WholePartialDesa), as programs: Σ a. f a ≡ b declared with no witness, its points asked.
# f : Unit → Bool is one point at True and none at False; g : Bool → Unit is two points at Tt (a bit lost); g∘f is one point
# (the sequential diagnostic would add the losses and be wrong); `leaves` is the census as a list.
check t/census.hyper at-true '#Tt{}'
check t/census.hyper at-false '*'
got=$(./hyper run t/census.hyper forget-at-tt | head -1); case "$got" in '&'*'{#True{},#False{}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL census forget: $got";; esac
check t/census.hyper census-forget '#Cons{#True{},#Cons{#False{},#Nil{}}}'   # the declaration's order: True is declared before False in the constructor table
check t/census.hyper compose-at-tt '#Tt{}'
check t/census.hyper not-at-true '#False{}'
# the encounter of two peers (kernel-flat/TheEncounterOfTwoPeers…), as a program over `trace`: two terms that reach one
# normal form; τ = mine ⊕ rev theirs has their lengths' sum; the round trip τ ⊕ rev τ is twice it; a third term has no meeting
check t/meet.hyper meeting '#True{}'
check t/meet.hyper no-meeting '#False{}'
check t/meet.hyper mine "$(nat 4)"
check t/meet.hyper theirs "$(nat 1)"
check t/meet.hyper tau-length "$(nat 5)"
check t/meet.hyper round-length "$(nat 10)"
# the crossing: two redexes that do not touch, one value
check t/meet.hyper cross "$(nat 26)"
# the joint state (theorems/logic/Jiva_…), as programs: the fibre of the comparison ⟨p,q⟩ over a pair of readings is
# declared and resolved: one point for the product, none for the diagonal at (True,False), two for the hidden bit; a
# living step has a witness pair that agrees at p and disagrees after the step, a dead step has none
check t/jiva.hyper product-at-tf '#Pair{#True{},#False{}}'
check t/jiva.hyper diagonal-at-tf '*'
check t/jiva.hyper diagonal-at-tt '#True{}'
got=$(./hyper run t/jiva.hyper hidden-at-tt | head -1); case "$got" in '&'*'{#True{},#False{}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL joint hidden: $got";; esac
got=$(./hyper run t/jiva.hyper cnot-left | head -1); case "$got" in '&'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL living step: $got";; esac
check t/jiva.hyper cnot-right '*'
check t/jiva.hyper dead-left '*'
check t/jiva.hyper dead-right '*'
# §0.3 step 1: a declaration with a type and no body is a coordinate; a match asks it and it becomes the superposition of
# the match's constructors, correlated across every holder (one label on both sides of pair), split only as far as asked
got=$(./hyper run t/coord.hyper pick | head -1); case "$got" in "&"*"{$(nat 1),$(nat 2)}") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL coord pick: $got";; esac
got=$(./hyper run t/coord.hyper pair | head -1); l1=$(echo "$got" | sed -n "s/^#Pair{&\([0-9]*\){$(nat 1),$(nat 2)},&\([0-9]*\){#False{},#True{}}}\$/\1 \2/p")
if [ -n "$l1" ] && [ "${l1% *}" = "${l1#* }" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL coord pair: $got"; fi
got=$(./hyper run t/coord.hyper depth | head -1); case "$got" in "&"*"{$(nat 0),&"*"{$(nat 1),$(nat 2)}}") pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL coord depth: $got";; esac
# §0.3 step 2: the declaration is the program.  sort's specification, its only text, resolves B for A = [3,1,2];
# the fibre of isort over [1,2] has two points and prints as their superposition; an empty fibre prints as *.
check t/sort.hyper main '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Suc{#Suc{#Zer{}}}},#Nil{}}}}'
got=$(./hyper run t/sort.hyper perms | head -1); case "$got" in '&'*'{#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Nil{}}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Zer{}},#Nil{}}}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL sort perms: $got";; esac
check t/sort.hyper none '*'
check t/sort.hyper head '#Suc{#Zer{}}'
# §0.3 step 4: sort is a declaration with a Π type and no body; applied to A it is the coordinate of the Σ at A.
check t/sort.hyper sort-A '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Suc{#Suc{#Zer{}}}},#Nil{}}}}'
# the run along free coordinates: isort of three unknowns has six arrangements, each a leaf with its own events;
# one comparison asked twice is one question and one split
check t/sort.hyper n-isort3 "$(nat 6)"
check t/sort.hyper n-isort2 "$(nat 2)"
check t/sort.hyper n-two-asks "$(nat 2)"
check t/sort.hyper n-two-asks-b "$(nat 4)"
# the decision tree of isort along three free coordinates: comparisons per leaf, and at most three
check t/sort.hyper sp3 "#Cons{$(nat 2),#Cons{$(nat 3),#Cons{$(nat 2),#Cons{$(nat 2),#Cons{$(nat 3),#Cons{$(nat 3),#Nil{}}}}}}}"
check t/sort.hyper c-isort3 "$(nat 3)"
# the declaration sort along free inputs: the two arrangements for two, the six for three, no contradictory leaf
check t/sort.hyper n-run2 "$(nat 2)"
check t/sort.hyper count3 "$(nat 6)"
check t/sort.hyper sort-nil '#Nil{}'
check t/sort.hyper sort-dup '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Nil{}}}}'
# the declarations never exercised before: sort at a free list, sortCost through a declared free function, the chart move
check t/sort.hyper sortCost-3 "$(./hyper run t/sort.hyper cost3 2>/dev/null | head -1)"
check t/sort.hyper chart-move '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Suc{#Suc{#Zer{}}}},#Nil{}}}}'
# every identifier MAP.md names is on the line it cites
if ./cite.sh >/dev/null; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL cite: $(./cite.sh | tail -3 | tr '\n' ' ')"; fi
echo "pass=$pass fail=$fail"; [ $fail -eq 0 ]

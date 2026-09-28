#!/usr/bin/env bash
# hyper/test.sh — the substrate's checks: values, and the ledger's count where a check is about cost.
set -u; cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -o hyper cell.c read.c verify.c main.c -lm || exit 1
pass=0; fail=0
check() { got=$(timeout 20 ./hyper run "$1" "$2" 2>&1 | head -1); if [ "$got" = "$3" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1 $2: got '$got' want '$3'"; fi; }
check t/basic.hyper main      '#Suc{#Suc{#Suc{#Suc{#Zer{}}}}}'
# §10.4 capture probes: cap4 = 4, two∘two = 4, the triple = 16
check t/basic.hyper cap4    '4'
check t/basic.hyper two-two '4'
check t/basic.hyper triple  '16'
check t/lazy.hyper  main      '#False{}'
check t/sup.hyper   pick0     '1'
check t/sup.hyper   pick1     '2'
check t/sup.hyper   dist      '&1{6,10}'
check t/sup.hyper   matchsup  '&1{#False{},#True{}}'
check t/sup.hyper   main      '#Pair{1,2}'
check t/kan.hyper   reg       '5'
check t/kan.hyper   suptrp    '#True{}'
check t/kan.hyper   hc-true   '7'
check t/kan.hyper   hc-none   '0'
check t/kan.hyper   hc-nat    '#Suc{#Zer{}}'
check t/kan.hyper   pitrp     '9'
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
check t/hit.hyper at-sym    '2'
check t/hit.hyper at-0      '1'
check t/hit.hyper faced     '1'
check t/hit.hyper helim-sq  '#Zer{}'
check t/hit.hyper sup-pt    '&1{1,1}'
check t/hit.hyper merid-t   '#merid{#Bool{},#False{}}'
check t/hit.hyper merid-t0  '#north{#Bool{}}'
# the interval is De Morgan, not Boolean: absorption holds, complement does not
got=$(./hyper run t/kan.hyper absorb | head -1);   case "$got" in i[0-9]*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL absorb: $got";; esac
got=$(./hyper run t/kan.hyper nocompl | head -1);  case "$got" in '~i'*'∨i'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL nocompl: $got";; esac
got=$(./hyper run t/kan.hyper demorgan | head -1); case "$got" in '~i'*'∨~i'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL demorgan: $got";; esac
# no capture: the face at M passes inside; the inner sup keeps its own fresh name (a heap address, not a fixed label)
got=$(./hyper run t/sup.hyper nocapture | head -1); case "$got" in '&'*'{5,6}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL nocapture: $got";; esac
# the machine that asks (§5): questions from the world, an ASK answered by the world
got=$(printf '(lam p (proj 0 p))\n(lam t (proj 0 (proj 1 t)))\n' | ./hyper interact t/interact.hyper main | grep -v Itrs | tr '\n' ' ')
if [ "$got" == "#Pair{1,#Pair{2,3}} 1 #Pair{1,#Pair{2,3}} " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL interact: $got"; fi
got=$(printf '(ctr True)\n(lam p (proj 1 p))\n' | ./hyper interact t/interact.hyper asks | grep -v Itrs | tr '\n' ' ')
if [ "$got" == "? #Cons{'w',#Cons{'h',#Cons{'o',#Nil{}}}} #Pair{#True{},7} 7 " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL ask: $got"; fi
# the checker (verify.c) on its probes: every definition checks
n=$(./hyper check t/check.hyper 2>/dev/null | grep -c '✓'); m=$(grep -c '^(def' t/check.hyper)
if [ "$n" -eq "$m" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL check: $n of $m definitions check"; fi
# §3.3 erase at the projection: a forgotten port costs one row where it is forgotten; the fibre's size never enters
checkn() { got=$(./hyper run "$1" "$2" 2>&1 | grep -v Words | tr '\n' ' '); if [ "$got" = "$3 - Itrs: $4 " ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1 $2: got '$got' want '$3 - Itrs: $4'"; fi; }
# §3 a demanded port fires once: a redex held by both sides of a distribution is one row (3*4 once, not per side)
checkn t/sup.hyper shared-redex '&3{13,14}' 6
checkn t/erase.hyper fst-big '1' 2
checkn t/erase.hyper and-f   '#False{}' 4
checkn t/erase.hyper and-t   '#True{}' 3
checkn t/erase.hyper const   '7' 2
checkn t/erase.hyper dflt    '3' 3
checkn t/erase.hyper carry   '1' 2
# §9 schedules: the redex bag is the only scheduler; serving the right demand first, or a coin per choice, gives
# the same value in the same count on every probe above (a fresh dimension's printed name is gauge, not value)
for pair in t/basic.hyper:main t/sup.hyper:dist t/sup.hyper:matchsup t/kan.hyper:reg t/kan.hyper:hc-nat t/kan.hyper:pitrp t/ua.hyper:fwd-true t/setcomp.hyper:via-pi t/hit.hyper:helim-sq t/hit.hyper:merid-t t/erase.hyper:and-f t/sort.hyper:sort-A t/sort.hyper:sort-dup t/sort.hyper:n-run2 t/sort.hyper:c-isort3; do
  f=${pair%%:*}; d=${pair##*:}; a=$(./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' '); b=$(HYPER_SCHEDULE=right ./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' '); c=$(HYPER_SCHEDULE=7 ./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' ')
  if [ "$a" = "$b" ] && [ "$a" = "$c" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL schedule $f $d: [$a] [$b] [$c]"; fi; done
# the census of a question (Fibre.WholePartialDesa), as programs: Σ a. f a ≡ b declared with no witness, its points asked.
# f : Unit → Bool is one point at True and none at False; g : Bool → Unit is two points at Tt (a bit lost); g∘f is one point
# (the sequential diagnostic would add the losses and be wrong); `leaves` is the census as a list.
check t/census.hyper at-true '#Tt{}'
check t/census.hyper at-false '*'
got=$(./hyper run t/census.hyper forget-at-tt | head -1); case "$got" in '&'*'{#False{},#True{}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL census forget: $got";; esac
check t/census.hyper census-forget '#Cons{#False{},#Cons{#True{},#Nil{}}}'
check t/census.hyper compose-at-tt '#Tt{}'
check t/census.hyper not-at-true '#False{}'
# the encounter of two peers (kernel-flat/TheEncounterOfTwoPeers…), as a program over `trace`: two terms that reach one
# normal form; τ = mine ⊕ rev theirs has their lengths' sum; the round trip τ ⊕ rev τ is twice it; a third term has no meeting
check t/meet.hyper meeting '#True{}'
check t/meet.hyper no-meeting '#False{}'
check t/meet.hyper mine '4'
check t/meet.hyper theirs '1'
check t/meet.hyper tau-length '5'
check t/meet.hyper round-length '10'
# §7 the crossing: two redexes that do not touch, contracted in the two orders: same value, same len, different traces (§8: no section)
l=$(HYPER_TRACE=1 ./hyper run t/meet.hyper cross | sed -n '1p;4p' | tr '\n' '|'); r=$(HYPER_TRACE=1 HYPER_SCHEDULE=right ./hyper run t/meet.hyper cross | sed -n '1p;4p' | tr '\n' '|')
lv=${l%%|*}; rv=${r%%|*}; lt=${l#*|}; rt=${r#*|}; ln=$(echo "$lt" | wc -w); rn=$(echo "$rt" | wc -w)
if [ "$lv" = "26" ] && [ "$lv" = "$rv" ] && [ "$ln" -eq "$rn" ] && [ "$lt" != "$rt" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL crossing: [$l] [$r]"; fi
# the trace as a term: the two schedules of the crossing give the same value and the same events
l=$(./hyper run t/meet.hyper crossing | head -1); r=$(HYPER_SCHEDULE=right ./hyper run t/meet.hyper crossing | head -1)
if [ "$l" = '#Pair{26,#Cons{#op2{2},#Cons{#op2{2},#Cons{#op2{1},#Nil{}}}}}' ] && [ "$l" = "$r" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL crossing trace: $l $r"; fi
# the joint state (theorems/logic/Jiva_…), as programs: the fibre of the comparison ⟨p,q⟩ over a pair of readings is
# declared and resolved: one point for the product, none for the diagonal at (True,False), two for the hidden bit; a
# living step has a witness pair that agrees at p and disagrees after the step, a dead step has none
check t/jiva.hyper product-at-tf '#Pair{#True{},#False{}}'
check t/jiva.hyper diagonal-at-tf '*'
check t/jiva.hyper diagonal-at-tt '#True{}'
got=$(./hyper run t/jiva.hyper hidden-at-tt | head -1); case "$got" in '&'*'{#False{},#True{}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL joint hidden: $got";; esac
got=$(./hyper run t/jiva.hyper cnot-left | head -1); case "$got" in '&'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL living step: $got";; esac
check t/jiva.hyper cnot-right '*'
check t/jiva.hyper dead-left '*'
check t/jiva.hyper dead-right '*'
# §0.3 step 1: a declaration with a type and no body is a coordinate; a match asks it and it becomes the superposition of
# the match's constructors, correlated across every holder (one label on both sides of pair), split only as far as asked
got=$(./hyper run t/coord.hyper pick | head -1); case "$got" in '&'*'{2,1}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL coord pick: $got";; esac
got=$(./hyper run t/coord.hyper pair | head -1); l1=$(echo "$got" | sed -n 's/^#Pair{&\([0-9]*\){2,1},&\([0-9]*\){#False{},#True{}}}$/\1 \2/p')
if [ -n "$l1" ] && [ "${l1% *}" = "${l1#* }" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL coord pair: $got"; fi
got=$(./hyper run t/coord.hyper depth | head -1); case "$got" in '&'*'{0,&'*'{1,2}}') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL coord depth: $got";; esac
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
check t/sort.hyper n-isort3 '6'
check t/sort.hyper n-isort2 '2'
check t/sort.hyper n-two-asks '2'
check t/sort.hyper n-two-asks-b '4'
# the decision tree of isort along three free coordinates: comparisons per leaf, and at most three
check t/sort.hyper sp3 '#Cons{2,#Cons{3,#Cons{2,#Cons{2,#Cons{3,#Cons{3,#Nil{}}}}}}}'
check t/sort.hyper c-isort3 '3'
# the declaration sort along free inputs: the two arrangements for two, the six for three, no contradictory leaf
check t/sort.hyper n-run2 '2'
check t/sort.hyper count3 '6'
check t/sort.hyper sort-nil '#Nil{}'
check t/sort.hyper sort-dup '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Nil{}}}}'
# every identifier MAP.md names is on the line it cites
if ./cite.sh >/dev/null; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL cite: $(./cite.sh | tail -3 | tr '\n' ' ')"; fi
echo "pass=$pass fail=$fail"; [ $fail -eq 0 ]

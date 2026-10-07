#!/usr/bin/env bash
# hyper/test.sh — the substrate's checks: values, and the ledger's count where a check is about cost.
set -u; cd "$(dirname "$0")"
gcc -std=gnu11 -O2 -w -c net.c -o net.o || exit 1
gcc -std=gnu11 -O2 -Wall -Wno-misleading-indentation -Wno-unused-parameter -Wno-unused-function -pthread -o hyper cell.c read.c verify.c main.c net.o -lm || exit 1
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
for pair in t/basic.hyper:main t/sup.hyper:dist t/sup.hyper:matchsup t/kan.hyper:reg t/kan.hyper:hc-nat t/kan.hyper:pitrp t/ua.hyper:fwd-true t/setcomp.hyper:via-pi t/hit.hyper:helim-sq t/hit.hyper:merid-t t/erase.hyper:and-f t/sort.hyper:chart-move; do
  f=${pair%%:*}; d=${pair##*:}; a=$(./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' '); b=$(HYPER_SCHEDULE=right ./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' '); c=$(HYPER_SCHEDULE=7 ./hyper run $f $d 2>&1 | grep -v Words | tr '\n' ' ')
  if [ "$a" = "$b" ] && [ "$a" = "$c" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL schedule $f $d: [$a] [$b] [$c]"; fi; done
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
# MAP §0.3 step 6: the chart move.  Carrier isort with isoToEquiv of descend/ascend; transport along its ua is descend
# (uaβ), so the carried image is sort's point, with no coordinate, far below resolving the type
check t/sort.hyper chart-move '#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Suc{#Suc{#Zer{}}}},#Nil{}}}}'
got=$(./hyper run t/sort.hyper chart-move | sed -n 2p); case "$got" in '- Itrs: 173') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL chart-move count: $got";; esac
# step 4 closed: the specification b/sort_at_A checks under the typed path (prelude's iso tower, ua, the carrier, chart-move);
# HYPER_CHECK_ALL verifies every typed definition the file and the prelude carry, not only the book's
got=$(./hyper check t/sort.hyper 2>&1 | tr -d '\033' | sed 's/\[[0-9;]*m//g'); case "$got" in *'✗'*) fail=$((fail+1)); echo "FAIL check t/sort.hyper: $got";; *'✓ sort_at_A'*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL check sort_at_A: $got";; esac
if HYPER_CHECK_ALL=1 ./hyper check t/sort.hyper 2>&1 | grep -q '✗'; then fail=$((fail+1)); echo "FAIL HYPER_CHECK_ALL t/sort.hyper"; else pass=$((pass+1)); fi
# step 5: a declaration with no body is the census of the book at its type — one entry resolves, two refuse, none refuse
check t/declare.hyper main '#True{}'
got=$(./hyper run t/declare.hyper some-bool 2>&1); case "$got" in *विकलादेश*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL crowded declaration: $got";; esac
got=$(./hyper run t/declare.hyper no-such 2>&1); case "$got" in *नास्ति*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL empty declaration: $got";; esac
check t/sort.hyper b/sort_spec '#Pair{#Cons{#Suc{#Zer{}},#Cons{#Suc{#Suc{#Zer{}}},#Cons{#Suc{#Suc{#Suc{#Zer{}}}},#Nil{}}}},#Pair{#Refl{},#Refl{}}}'
got=$(./hyper run t/sort.hyper b/sort_spec | sed -n 2p); case "$got" in '- Itrs: 174') pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL sort_spec count: $got";; esac
# §9 parallel demand over the one arena: under HYPER_PARALLEL=4 the value, the count and the words are the sequential run's
for pair in t/basic.hyper:main t/basic.hyper:triple t/sup.hyper:dist t/sup.hyper:matchsup t/kan.hyper:reg t/kan.hyper:hc-nat t/kan.hyper:pitrp t/ua.hyper:fwd-true t/setcomp.hyper:via-pi t/hit.hyper:helim-sq t/hit.hyper:merid-t t/erase.hyper:and-f t/sort.hyper:chart-move t/sort.hyper:b/sort_spec t/declare.hyper:main; do
  f=${pair%%:*}; d=${pair#*:}; base=$(timeout 60 ./hyper run "$f" "$d" 2>&1 | head -3); par=$(HYPER_PARALLEL=4 timeout 60 ./hyper run "$f" "$d" 2>&1 | head -3)
  if [ "$base" = "$par" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL parallel $pair:"; echo "  seq: $(echo "$base" | tr '\n' ' ')"; echo "  par: $(echo "$par" | tr '\n' ' ')"; fi
done
# the checker's conversion rules refuse what they must (t/mustfail.hyper): the verdicts, exactly
got=$(./hyper check t/mustfail.hyper 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -E '^[✓✗]' | tr '\n' ' ')
want='✓ ok_id ✗ face_not_vacuous ✗ two_closures ✗ proj_not_sig ✗ path_wrong_family ✓ ok_declared : a coordinate of its type '
if [ "$got" = "$want" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL mustfail verdicts: $got"; fi
# witnessing a proposition (research/SAT_FIBRE_BEND_HVM_DEPLOYED_TECHNICAL_REPORT.md): the domain is one labelled
# superposition shared by every occurrence, the proposition reduces once over it, a failing branch is erased, and the
# collapse is the fibre.  XOR's fibre over True and over False; a contradiction's empty fibre
check t/sat.hyper xor-true  '#Cons{#Pair{#False{},#True{}},#Cons{#Pair{#True{},#False{}},#Nil{}}}'
check t/sat.hyper xor-false '#Cons{#Pair{#False{},#False{}},#Cons{#Pair{#True{},#True{}},#Nil{}}}'
check t/sat.hyper contradiction '#Nil{}'
# one proposition, two presentations (sat_fibre/REPORT.md §5): both empty; the order that meets the contradiction
# first costs less, the other reproduces the cube before erasing it
check t/sat.hyper short '#Nil{}'
check t/sat.hyper reversed '#Nil{}'
cs=$(./hyper run t/sat.hyper short | sed -n 2p); cr=$(./hyper run t/sat.hyper reversed | sed -n 2p)
if [ "$cs" = "- Itrs: 314" ] && [ "$cr" = "- Itrs: 24" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL presentation counts: $cs / $cr"; fi
# constructing a specified map (SUPGEN_DEMO.md): the candidates are one superposition, the specification erases
# every other one, and the survivor is not, certified by the erasure of the alternatives
check t/sat.hyper synth-at '#Cons{#Pair{#True{},#False{}},#Nil{}}'
for d in xor-true xor-false contradiction short reversed synth-at; do
  a=$(./hyper run t/sat.hyper $d | head -2); b=$(HYPER_SCHEDULE=right ./hyper run t/sat.hyper $d | head -2); c=$(HYPER_SCHEDULE=7 ./hyper run t/sat.hyper $d | head -2)
  if [ "$a" = "$b" ] && [ "$a" = "$c" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL schedule t/sat.hyper $d"; fi; done
# the SAT fibre results (research/sat_fibre), reproduced exactly on the net: outputs, interactions, heap words and
# every rule, for the elementary suite, the NP families, the colour frames and the frozen cost model at n = 1..18
if python3 satcheck.py "$PWD/hyper" net > /tmp/satcheck.$$ 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL satcheck: $(tail -3 /tmp/satcheck.$$ | tr '\n' ' ')"; fi; rm -f /tmp/satcheck.$$
# every identifier MAP.md names is on the line it cites
if ./cite.sh >/dev/null; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL cite: $(./cite.sh | tail -3 | tr '\n' ' ')"; fi
echo "pass=$pass fail=$fail"; [ $fail -eq 0 ]

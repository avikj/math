#!/bin/sh
# Handoff sections 38 and 47: build, then the self-test (section 23 cases and every
# scope agent), the checking suite, the examples under every scheduling
# policy and worker count compared exactly against one baseline, the
# comparator's own accept/reject cases, a thread-race build with several
# workers, and an address/undefined/leak build.
set -e
cd "$(dirname "$0")/.."
B=${TMPDIR:-/tmp}/cell-checks; mkdir -p "$B"
cc -std=gnu11 -O1 -Wall -Wextra -pthread -o "$B/cell" cell.c
cc -std=gnu11 -O1 -Wall -Wextra -o "$B/cellcmp" cellcmp.c
cc -std=gnu11 -g -O1 -fsanitize=thread -pthread -o "$B/cell-tsan" cell.c
cc -std=gnu11 -g -O0 -fsanitize=address,undefined -fno-sanitize-recover=undefined -pthread -o "$B/cell-asan" cell.c
echo "== self-test"; "$B/cell" --selftest | tail -1
echo "== checking"; "$B/cell" core.cell checks/checking.cell | grep -c PASS
echo "== identity compiler (sections 39-47)"; "$B/cell" core.cell checks/transform.cell | grep -E "^(identity|equivalence|residual|cutpath|contractible|reject|assert)" | sed 's/ (tokens [0-9-]*)//' 
echo "== schedules"
"$B/cell" -w 1 -p lifo -d "$B/base" core.cell examples.cell > /dev/null
for s in "-w 1 -p fifo" "-w 1 -p random -s 1" "-w 1 -p random -s 2" "-w 1 -p mixed -s 3" "-w 4 -p lifo" "-w 4 -p random -s 5" "-w 8 -p mixed -s 6"; do
  "$B/cell" $s -d "$B/other" core.cell examples.cell > /dev/null
  printf "%-22s " "$s"; "$B/cellcmp" "$B/base" "$B/other"
done
echo "== schedules, identity compiler"
"$B/cell" -w 1 -p lifo -d "$B/tbase" core.cell checks/transform.cell > /dev/null
for s in "-w 1 -p fifo" "-w 1 -p random -s 11" "-w 4 -p mixed -s 12" "-w 8 -p random -s 13"; do
  "$B/cell" $s -d "$B/tother" core.cell checks/transform.cell > /dev/null
  printf "%-22s " "$s"; "$B/cellcmp" "$B/tbase" "$B/tother"
done
echo "== comparator"
G=checks/graphs
"$B/cellcmp" $G/base.graph $G/renamed.graph
"$B/cellcmp" $G/triangles.graph $G/triangles2.graph
for g in payload endpoint events aliasing; do if "$B/cellcmp" $G/base.graph $G/$g.graph > /dev/null; then echo "accepted $g"; exit 1; else echo "rejected $g"; fi; done
if "$B/cellcmp" $G/triangles.graph $G/hexagon.graph > /dev/null; then echo "accepted hexagon"; exit 1; else echo "rejected hexagon (refinement-ambiguous)"; fi
echo "== thread races (8 workers)"
"$B/cell-tsan" -w 8 -p random -s 9 --selftest > /dev/null
"$B/cell-tsan" -w 8 -p random -s 9 core.cell examples.cell > /dev/null
"$B/cell-tsan" -w 8 -p mixed -s 10 core.cell checks/checking.cell > /dev/null
"$B/cell-tsan" -w 8 -p random -s 14 core.cell checks/transform.cell > /dev/null
echo "== address, undefined behaviour, leaks"
"$B/cell-asan" -w 4 -p mixed -s 4 --selftest > /dev/null
"$B/cell-asan" -w 4 -p mixed -s 4 core.cell examples.cell > /dev/null
"$B/cell-asan" -w 4 -p random -s 8 core.cell checks/checking.cell > /dev/null
"$B/cell-asan" -w 4 -p mixed -s 15 core.cell checks/transform.cell > /dev/null
echo "all checks passed"

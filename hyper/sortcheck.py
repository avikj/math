#!/usr/bin/env python3
"""sortcheck: the sort declaration (sort.hvm) resolved on RUNTIME for many A.

For each A, @A is replaced and the whole collapse is run (-C: every surviving leaf, not the first).  It must
terminate, and its leaves must be exactly one list, sorted(A): the fibre of the specification over A is a single
point.  The interaction and heap counts are printed; nothing about them is asserted here.

usage: sortcheck.py RUNTIME...
"""
import itertools, re, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNTIME = sys.argv[1:] or sys.exit(__doc__)
SOURCE = (HERE/'sort.hvm').read_text()
TMP = Path(tempfile.mkdtemp(prefix='sortcheck.'))
cases = [[], [0], [5], [1, 0], [0, 0], [3, 1, 2], [2, 1, 2], [0, 3, 0, 1], [4, 4, 4, 4], [5, 3, 1, 4, 2]]
cases += [list(p) for p in sorted(set(itertools.permutations([2, 0, 1, 1])))]
passed = failed = 0
for a in cases:
    src = re.sub(r'^@A = .*$', '@A = [' + ', '.join(f'{x}n' for x in a) + ']', SOURCE, flags=re.M)
    path = TMP/'sort.hvm'
    path.write_text(src)
    p = subprocess.run(RUNTIME + [str(path), '-s', '-C'], capture_output=True, text=True, timeout=600,
                       env={'SAT_MAX_ITRS': '200000000', 'SAT_MAX_HEAP': '2000000000'})
    out = re.sub(r'\x1b\[[0-9;]*m', '', p.stdout)
    leaves = [l.split(' #')[0] for l in out.splitlines() if l.startswith('[')]
    want = '[' + ','.join(f'{x}n' for x in sorted(a)) + ']'
    itrs = re.search(r'Itrs: (\d+)', out)
    heap = re.search(r'Heap: (\d+)', out)
    ok = p.returncode == 0 and leaves == [want]
    passed += ok
    failed += not ok
    print(f'{"ok  " if ok else "FAIL"} A={a} leaves={leaves} itrs={itrs and itrs[1]} heap={heap and heap[1]}', flush=True)
print(f'sortcheck pass={passed} fail={failed}')
sys.exit(1 if failed else 0)

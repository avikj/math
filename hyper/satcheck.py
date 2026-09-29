#!/usr/bin/env python3
"""satcheck: the SAT fibre results of research/sat_fibre, reproduced exactly.

Every recorded run is re-emitted by the research generators and run on RUNTIME, a command prefix that takes an
interaction-net program the way HVM4 does (`RUNTIME FILE -s -C` or `-C1`), prints the collapsed normal form and
`Itrs:` / `Heap:` on stdout, and a `SAT_PROFILE {...}` rule profile on stderr, stopping with exit 124 at the
interaction budget SAT_MAX_ITRS.  The run must reproduce what was recorded, not approximately:

  results.json        the elementary suite: 27 instances x 4 demands; outputs, interactions, heap
  np_results.json     pigeonhole, permutation, colouring, planted 3-CNF, 4 presentations, first/all demands;
                      outputs, interactions, heap, every rule count, and the budget exits
  color_results.json  raw coordinates against canonical colours with six retained frames
  cost_results.json   F_n = (x1|~x1)&...&xn&~xn at n = 13..18 in both presentations
  and the frozen model for every n from 1 to 18:  T_short(n) = 9*2^n + 16n - 4,  T_reverse(n) = n + 30,
  with every rule count of the short presentation (cost_predictions.predicted_rules).

usage: satcheck.py RUNTIME...        e.g.  satcheck.py ./hyper     or  satcheck.py path/to/hvm-profile
"""
import itertools, json, os, re, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAT = HERE.parent/'research'/'sat_fibre'
sys.path.insert(0, str(SAT))
from experiment import emit, evaluate, family_cases          # noqa: E402
from np_experiment import program, cases as np_cases         # noqa: E402
from color_experiment import net                             # noqa: E402
from cost_predictions import predicted_rules                 # noqa: E402

RUNTIME = sys.argv[1:]
if not RUNTIME:
    sys.exit(__doc__)
TMP = Path(tempfile.mkdtemp(prefix='satcheck.'))
passed = failed = 0


def run(source, demand, budget=None):
    path = TMP/'p.hvm4'
    path.write_text(source)
    env = dict(os.environ)
    if budget:
        env['SAT_MAX_ITRS'] = str(budget)
    p = subprocess.run(RUNTIME+[str(path), '-s', '-C1' if demand == 'first' else '-C'],
                       capture_output=True, text=True, env=env, timeout=600)
    out = re.sub(r'\x1b\[[0-9;]*m', '', p.stdout)
    m = re.search(r'SAT_PROFILE (\{.*\})', p.stderr)
    return p.returncode, out, json.loads(m[1]) if m else None


def nonzero(rules):
    return {k: v for k, v in rules.items() if v}


def check(label, ok, detail=''):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f'FAIL {label}: {detail}', flush=True)


def load(name):
    return json.loads((SAT/name).read_text())


# ---- the elementary suite -------------------------------------------------------------------------------------
recorded = {(r['name'], r['mode']): r for r in load('results.json')['results']}
for name, n, cnf in family_cases():
    rows = sorted((sum(b << i for i, b in enumerate(bits)), evaluate(cnf, bits))
                  for bits in itertools.product((0, 1), repeat=n))
    models = [a for a, b in rows if b]
    for mode in ('answers', 'carrier', 'models', 'first'):
        want = recorded[(name, mode)]
        code, out, prof = run(emit(n, cnf, mode), mode)
        if mode == 'carrier':
            got = sorted((int(a), int(b)) for a, b in re.findall(r'#Row\{(\d+),\s*(\d+)\}', out)); ok = got == rows
        elif mode == 'models':
            got = [int(x) for x in re.findall(r'#SAT\{(\d+)\}', out)]; ok = sorted(got) == models
        elif mode == 'first':
            got = [int(x) for x in re.findall(r'#SAT\{(\d+)\}', out)]; ok = len(got) == min(1, len(models)) and all(g in models for g in got)
        else:
            got = [int(x) for x in re.findall(r'#Answer\{(\d+)\}', out)]; ok = set(got) == {b for _, b in rows}
        itrs = int(re.search(r'Itrs: (\d+)', out)[1]) if re.search(r'Itrs: (\d+)', out) else None
        heap = int(re.search(r'Heap: (\d+)', out)[1]) if re.search(r'Heap: (\d+)', out) else None
        check(f'{name} {mode}', code == 0 and ok and len(got) == want['outputs']
              and itrs == want['interactions'] and heap == want['heap_nodes'],
              f'code {code} outputs {len(got)}/{want["outputs"]} itrs {itrs}/{want["interactions"]} heap {heap}/{want["heap_nodes"]}')

# ---- the NP-complete families ---------------------------------------------------------------------------------
npr = load('np_results.json')
budget = npr['interaction_budget']
recorded = {(r['name'], r['presentation'], r['demand']): r for r in npr['results']}
for name, n, cnf, sat, models in np_cases():
    for presentation in ('short', 'reverse', 'strict', 'gated'):
        for mode in ('first', 'all') if models is not None else ('first',):
            want = recorded[(name, presentation, mode)]
            code, out, prof = run(program(n, cnf, presentation), mode, budget)
            witnesses = [int(x) for x in re.findall(r'#SAT\{(\d+)\}', out)]
            if want['status'] == 'budget_inconclusive':
                check(f'{name} {presentation} {mode}', code == 124 and prof and prof['interactions'] == want['interactions']
                      and nonzero(prof['rules']) == nonzero(want['rules']),
                      f'code {code} itrs {prof and prof["interactions"]}/{want["interactions"]}')
                continue
            sound = all(evaluate(cnf, [(w >> i) & 1 for i in range(n)]) for w in witnesses)
            check(f'{name} {presentation} {mode}', code == 0 and prof and sound and len(witnesses) == want['outputs']
                  and prof['interactions'] == want['interactions'] and prof['heap_nodes'] == want['heap_nodes']
                  and nonzero(prof['rules']) == nonzero(want['rules']),
                  f'code {code} outputs {len(witnesses)}/{want["outputs"]} itrs {prof and prof["interactions"]}/{want["interactions"]}')

# ---- colour frames --------------------------------------------------------------------------------------------
recorded = {(r['name'], r['framed']): r for r in load('color_results.json')}
color_cases = [('triangle', 3, list(itertools.combinations(range(3), 2))),
               ('K4', 4, list(itertools.combinations(range(4), 2))),
               ('K4_isolated8', 8, list(itertools.combinations(range(4), 2))),
               ('triangle_isolated8', 8, list(itertools.combinations(range(3), 2))),
               ('path6', 6, [(i, i+1) for i in range(5)]),
               ('path8', 8, [(i, i+1) for i in range(7)])]
for name, v, edges in color_cases:
    readings = []
    for framed in (False, True):
        want = recorded[(name, framed)]
        code, out, prof = run(net(v, edges, framed), 'all')
        values = [int(x) for x in re.findall(r'#Coloring\{(\d+)\}', out)]
        sound = all(all((c//3**a) % 3 != (c//3**b) % 3 for a, b in edges) for c in values)
        readings.append(set(values))
        check(f'colour {name} {"framed" if framed else "raw"}', code == 0 and prof and sound and len(values) == want['outputs']
              and prof['interactions'] == want['interactions'] and prof['heap_nodes'] == want['heap_nodes']
              and nonzero(prof['rules']) == nonzero(want['rules']),
              f'code {code} outputs {len(values)}/{want["outputs"]} itrs {prof and prof["interactions"]}/{want["interactions"]}')
    check(f'colour {name} frames agree', readings[0] == readings[1])

# ---- the frozen cost model and its held-out runs --------------------------------------------------------------
recorded = {(r['n'], r['presentation']): r for r in load('cost_results.json')}
for n in range(1, 19):
    cnf = [[i, -i] for i in range(1, n)]+[[n], [-n]]
    for presentation, total in (('short', 9*2**n+16*n-4), ('reverse', n+30)):
        code, out, prof = run(program(n, cnf, presentation), 'all')
        ok = code == 0 and prof and '#SAT{' not in out and prof['interactions'] == total
        if presentation == 'short':
            ok = ok and nonzero(prof['rules']) == predicted_rules(n)
        if (n, presentation) in recorded:
            ok = ok and prof['heap_nodes'] == recorded[(n, presentation)]['heap_nodes']
        check(f'F_{n} {presentation}', ok, f'code {code} itrs {prof and prof["interactions"]}/{total}')

print(f'satcheck pass={passed} fail={failed}')
sys.exit(1 if failed else 0)

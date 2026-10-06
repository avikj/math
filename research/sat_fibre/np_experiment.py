#!/usr/bin/env python3
"""CNF constraints reproduced as labelled alternatives and reduced on HVM4.

No host SAT procedure supplies an answer. Mathematical constructions supply
expected outcomes; every emitted satisfying assignment is checked separately.
Bounded runs report inconclusive, never UNSAT, if reduction did not complete.
"""
import argparse
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import random
import re
import statistics
import subprocess
import time
from experiment import emit, evaluate, fold

ROOT = Path(__file__).resolve().parent


def pigeonhole(p, h):
    cell = lambda i, j: i*h+j+1
    clauses = [[cell(i, j) for j in range(h)] for i in range(p)]
    clauses += [[-cell(i, a), -cell(i, b)] for i in range(p)
                for a, b in itertools.combinations(range(h), 2)]
    clauses += [[-cell(a, j), -cell(b, j)] for j in range(h)
                for a, b in itertools.combinations(range(p), 2)]
    return clauses


def coloring(v, edges):
    color = lambda i, j: i*3+j+1
    clauses = [[color(i, j) for j in range(3)] for i in range(v)]
    clauses += [[-color(i, a), -color(i, b)] for i in range(v)
                for a, b in itertools.combinations(range(3), 2)]
    clauses += [[-color(a, j), -color(b, j)] for a, b in edges for j in range(3)]
    return clauses


def cases():
    for h in (2, 3, 4, 5):
        yield f'php{h+1}_{h}', (h+1)*h, pigeonhole(h+1, h), False, 0
        if h <= 4:
            yield f'permutation{h}', h*h, pigeonhole(h, h), True, math.factorial(h)
    for v in (3, 4):
        yield f'color_K{v}', v*3, coloring(v, itertools.combinations(range(v), 2)), v == 3, 6 if v == 3 else 0
    yield 'color_K4_plus_isolated', 24, coloring(8, itertools.combinations(range(4), 2)), False, 0
    for n in (10, 14, 18, 22, 26):
        for seed in (17, 41):
            rng = random.Random(seed+n*100)
            planted = [rng.randrange(2) for _ in range(n)]
            cnf = []
            for _ in range(round(4.26*n)):
                variables = rng.sample(range(n), 3)
                clause = [(v+1)*rng.choice((-1, 1)) for v in variables]
                if not evaluate([clause], planted):
                    clause[0] *= -1
                cnf.append(clause)
            yield f'planted3_{n}_{seed}', n, cnf, True, None


def program(n, cnf, presentation):
    if presentation == 'reverse':
        cnf = list(reversed(cnf))
    source = emit(n, cnf, 'models')
    if presentation == 'strict':
        source = source.replace('.&.', '&&').replace('.|.', '||')
    elif presentation == 'gated':
        mask = fold('+', [f'(x{i} * {1 << i})' for i in range(n)], '0')
        body = f'#SAT{{{mask}}}'
        for clause in reversed(cnf):
            literals = [f'x{abs(v)-1}' if v > 0 else f'(1 - x{-v-1})' for v in clause]
            body = f'@gate({fold(".|.", literals, "0")})({body})'
        source = '@gate = λ{0: λa.&{}; _: λp.λa.a}\n'
        source += '@solve = '+''.join(f'λ&x{i}.' for i in range(n))+body+'\n'
        source += '@main = @solve'+''.join(f'(&V{i}{{0,1}})' for i in range(n))+'\n'
    return source


def invoke(binary, path, mode, timeout=30):
    before = time.monotonic()
    p = subprocess.run([binary, str(path), '-s', '-C1' if mode == 'first' else '-C'],
                       capture_output=True, text=True, timeout=timeout)
    out = re.sub(r'\x1b\[[0-9;]*m', '', p.stdout)
    profile = re.search(r'SAT_PROFILE (\{.*\})', p.stderr)
    return p.returncode, out, p.stderr, json.loads(profile[1]) if profile else None, time.monotonic()-before


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--profile', required=True)
    parser.add_argument('--hvm', required=True)
    parser.add_argument('--budget', type=int, default=2000000)
    args = parser.parse_args()
    os.environ['SAT_MAX_ITRS'] = str(args.budget)
    folder = ROOT/'np_generated'
    folder.mkdir(exist_ok=True)
    inputs = list(cases())
    (ROOT/'np_predictions.json').write_text(json.dumps([
        dict(name=name, n=n, cnf=cnf, satisfiable=sat, models=models)
        for name, n, cnf, sat, models in inputs], indent=2)+'\n')
    results = []
    for name, n, cnf, expected_sat, models in inputs:
        for presentation in ('short', 'reverse', 'strict', 'gated'):
            path = folder/f'{name}_{presentation}.hvm4'
            path.write_text(program(n, cnf, presentation))
            for mode in ('first', 'all') if models is not None else ('first',):
                record = dict(name=name, variables=n, clauses=len(cnf),
                              literal_occurrences=sum(map(len, cnf)),
                              presentation=presentation, demand=mode)
                try:
                    code, out, err, profile, elapsed = invoke(args.profile, path, mode)
                except subprocess.TimeoutExpired:
                    record['status'] = 'timeout_inconclusive'
                    results.append(record)
                    continue
                (folder/f'{name}_{presentation}_{mode}.log').write_text(out+err)
                assert code in (0, 124), (path, code, out, err)
                assert profile is not None, err
                assert sum(profile['rules'].values()) == profile['interactions']
                witnesses = list(map(int, re.findall(r'#SAT\{(\d+)\}', out)))
                assert len(set(witnesses)) == len(witnesses), (name, 'duplicate witnesses')
                for mask in witnesses:
                    assert 0 <= mask < 2**n
                    assert evaluate(cnf, [(mask >> i) & 1 for i in range(n)]), (name, mask)
                record.update(profile, profile_seconds=elapsed, outputs=len(witnesses))
                record['status'] = 'complete' if code == 0 else 'budget_inconclusive'
                if code == 0:
                    assert bool(witnesses) == expected_sat, (name, presentation, mode, out)
                    if mode == 'all':
                        assert len(witnesses) == models
                    # Original runtime must reproduce both answers and counts.
                    baseline = []
                    for _ in range(3):
                        bc, bo, be, _, bt = invoke(args.hvm, path, mode)
                        assert bc == 0, be
                        bw = list(map(int, re.findall(r'#SAT\{(\d+)\}', bo)))
                        assert bw == witnesses
                        assert int(re.search(r'Itrs: (\d+)', bo)[1]) == profile['interactions']
                        baseline.append(bt)
                    record['original_wall_seconds_median'] = statistics.median(baseline)
                    record['original_wall_seconds_samples'] = baseline
                results.append(record)
                print(name, presentation, mode, record['status'], profile['interactions'], flush=True)
                # Persist after each run so bounded or interrupted work survives.
                (ROOT/'np_results.json').write_text(json.dumps(dict(
                    profile_sha256=hashlib.sha256(Path(args.profile).read_bytes()).hexdigest(),
                    hvm_sha256=hashlib.sha256(Path(args.hvm).read_bytes()).hexdigest(),
                    interaction_budget=args.budget, results=results), indent=2)+'\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Small, exhaustive correctness/complexity experiment; no third-party packages.

Predictions are written before any runtime invocation. HVM does the Boolean
evaluation and branch filtering; Python emits syntax and checks every answer.
The truth-table quotient is a diagnostic oracle, not a scalable SAT algorithm.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def evaluate(cnf, bits):
    return int(all(any(bits[abs(lit)-1] == (lit > 0) for lit in clause)
                   for clause in cnf))


def family_cases():
    yield 'empty', 0, []
    yield 'empty_clause', 0, [[]]
    yield 'xor', 2, [[1, 2], [-1, -2]]
    yield 'contradiction', 1, [[1], [-1]]
    yield 'simplified_unsat10', 10, [[]]
    yield 'simplified_true10', 10, []
    # Two-colouring constraints for an even and an odd cycle.
    for n in (4, 5):
        edges = [(i, i % n + 1) for i in range(1, n+1)]
        yield f'cycle{n}', n, [c for a, b in edges for c in ([a, b], [-a, -b])]
    for n in (2, 4, 6, 8, 10):
        yield f'tautology{n}', n, [[i, -i] for i in range(1, n+1)]
        yield f'unique{n}', n, [[i] for i in range(1, n+1)]
        yield f'late_unsat{n}', n, [[i, -i] for i in range(1, n)] + [[n], [-n]]
    # Equality of two bit words: the same CNF, two variable orders.
    for k in (2, 3, 4, 5):
        cnf = [c for i in range(1, k+1) for c in ([-i, i+k], [i, -i-k])]
        yield f'equality{k}', 2*k, cnf


def residual_widths(n, cnf, order):
    widths = []
    for depth in range(n+1):
        residuals = set()
        for prefix in itertools.product((0, 1), repeat=depth):
            table = []
            for suffix in itertools.product((0, 1), repeat=n-depth):
                assignment = [0]*n
                for v, b in zip(order, prefix+suffix):
                    assignment[v] = b
                table.append(evaluate(cnf, assignment))
            residuals.add(tuple(table))
        widths.append(len(residuals))
    return widths


def fold(op, xs, identity):
    result = identity
    for x in reversed(xs):
        result = f'({x} {op} {result})'
    return result


def emit(n, cnf, mode):
    literals = lambda c: [f'x{abs(v)-1}' if v > 0 else f'(1 - x{-v-1})' for v in c]
    expr = fold('.&.', [fold('.|.', literals(c), '0') for c in cnf], '1')
    mask = fold('+', [f'(x{i} * {1 << i})' for i in range(n)], '0')
    if mode == 'answers':
        body = f'#Answer{{{expr}}}'
    elif mode == 'carrier':
        body = f'#Row{{{mask},{expr}}}'
    else:
        body = f'@keep({expr})({mask})'
    binders = ''.join(f'λ&x{i}.' for i in range(n))
    arguments = ''.join(f'(&V{i}{{0,1}})' for i in range(n))
    return ('@keep = λ{0: λa.&{}; _: λp.λa.#SAT{a}}\n'
            f'@solve = {binders}{body}\n@main = @solve{arguments}\n')


def run(hvm, path, limit=None):
    start = time.monotonic()
    p = subprocess.run([hvm, str(path), '-s', '-C' if limit is None else f'-C{limit}'],
                       text=True, capture_output=True, timeout=30, check=True)
    out = re.sub(r'\x1b\[[0-9;]*m', '', p.stdout)
    count = re.search(r'Itrs: (\d+)', out)
    heap = re.search(r'Heap: (\d+)', out)
    if not count or not heap:
        raise RuntimeError(out + p.stderr)
    return out, dict(interactions=int(count[1]), heap_nodes=int(heap[1]),
                     elapsed_seconds=time.monotonic()-start)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--hvm', required=True)
    args = parser.parse_args()
    generated = ROOT / 'generated'
    generated.mkdir(exist_ok=True)
    cases = list(family_cases())
    predictions = []
    expected = {}
    for name, n, cnf in cases:
        rows = sorted((sum(b << i for i, b in enumerate(bits)), evaluate(cnf, bits))
                      for bits in itertools.product((0, 1), repeat=n))
        expected[name] = rows
        widths = residual_widths(n, cnf, list(range(n)))
        prediction = dict(name=name, variables=n, clauses=cnf,
                          assignments=2**n, models=sum(b for _, b in rows),
                          residual_widths=widths)
        if name.startswith('equality'):
            k = n//2
            prediction['interleaved_widths'] = residual_widths(
                n, cnf, [v for i in range(k) for v in (i, i+k)])
            assert widths[k] == 2**k
            assert max(prediction['interleaved_widths']) <= 3
        predictions.append(prediction)
    (ROOT / 'predictions.json').write_text(json.dumps(predictions, indent=2)+'\n')
    results = []
    for name, n, cnf in cases:
        for mode in ('answers', 'carrier', 'models', 'first'):
            path = generated / f'{name}_{mode}.hvm4'
            path.write_text(emit(n, cnf, mode))
            out, stats = run(args.hvm, path, 1 if mode == 'first' else None)
            path.with_suffix('.log').write_text(out)
            rows = expected[name]
            if mode == 'carrier':
                actual = sorted((int(a), int(b)) for a, b in re.findall(r'#Row\{(\d+),\s*(\d+)\}', out))
                assert actual == rows, (name, mode, actual)
            elif mode in ('models', 'first'):
                actual = [int(x) for x in re.findall(r'#SAT\{(\d+)\}', out)]
                models = [a for a, b in rows if b]
                if mode == 'first':
                    assert len(actual) == min(1, len(models)) and all(a in models for a in actual)
                else:
                    assert sorted(actual) == models, (name, mode, actual)
            else:
                actual = [int(x) for x in re.findall(r'#Answer\{(\d+)\}', out)]
                # Projecting away assignments may erase unused choices. The
                # set of answers is preserved; multiplicity need not survive.
                assert set(actual) == {b for _, b in rows}, (name, mode, actual)
            results.append(dict(name=name, mode=mode, outputs=len(actual), **stats))
        print(name, 'verified', flush=True)
    report = dict(hvm=str(Path(args.hvm).resolve()),
                  hvm_sha256=hashlib.sha256(Path(args.hvm).read_bytes()).hexdigest(),
                  predictions_sha256=hashlib.sha256((ROOT/'predictions.json').read_bytes()).hexdigest(),
                  results=results)
    (ROOT/'results.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()

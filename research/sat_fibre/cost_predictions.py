#!/usr/bin/env python3
"""Freeze and test a rule-count model on previously unmeasured sizes.

This is a falsifiable cost model, NOT a proof of the HVM transition relation.
It was inferred from n=1,2,3,4,10 and the source rules. Sizes 13..18 are
held-out checks. The model is deliberately retained separately from results.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
from np_experiment import program

ROOT = Path(__file__).resolve().parent


def predicted_rules(n):
    p = 2**n
    return {'AND-ONE': 2*n-1, 'AND-SUP': n+1, 'AND-ZER': 2,
            'APP-LAM': p+n, 'APP-MAT-NUM-MAT': p,
            'APP-MAT-SUP': p-1, 'APP-SUP': p-1, 'DUP-LAM': p-1,
            'DUP-NOD': 3*p+3*n-2, 'DUP-SUP-DIFF': p+n-1,
            'DUP-SUP-SAME': n, 'OP2-NUM-NUM': n, 'OP2-NUM-SUP': n,
            'OR-ONE': 2*n-1, 'OR-SUP': 2*n, 'OR-ZER': n+1}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--profile', required=True)
    args = parser.parse_args()
    predictions = [dict(n=n, short=9*2**n+16*n-4, reverse=n+30,
                        short_rules=predicted_rules(n)) for n in range(13, 19)]
    (ROOT/'cost_predictions.json').write_text(json.dumps(predictions, indent=2)+'\n')
    results = []
    for p in predictions:
        n = p['n']
        cnf = [[i, -i] for i in range(1, n)]+[[n], [-n]]
        for presentation in ('short', 'reverse'):
            path = ROOT/'generated'/f'predicted_unsat{n}_{presentation}.hvm4'
            path.write_text(program(n, cnf, presentation))
            run = subprocess.run([args.profile, str(path), '-s', '-C'],
                                 capture_output=True, text=True, timeout=30, check=True)
            profile = json.loads(re.search(r'SAT_PROFILE (\{.*\})', run.stderr)[1])
            assert profile['interactions'] == p[presentation]
            assert '#SAT{' not in run.stdout
            if presentation == 'short':
                assert {k: v for k, v in profile['rules'].items() if v} == p['short_rules']
            results.append(dict(n=n, presentation=presentation, **profile))
            print(n, presentation, profile['interactions'], 'predicted exactly', flush=True)
    (ROOT/'cost_results.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()

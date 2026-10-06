#!/usr/bin/env python3
"""Compare raw colour coordinates with canonical colours + a six-frame fibre."""
import argparse
import itertools
import json
from pathlib import Path
import re
import subprocess
from experiment import fold

ROOT = Path(__file__).resolve().parent
PERMS = list(itertools.permutations(range(3)))


def choice(values, label, depth=0):
    if len(values) == 1:
        return str(values[0])
    return f'&{label}{depth}{{{values[0]},{choice(values[1:], label, depth+1)}}}'


def net(v, edges, framed):
    coordinates = ['0', '1']+[f'c{i}' for i in range(2, v)] if framed else [f'c{i}' for i in range(v)]
    predicate = fold('.&.', [f'({coordinates[a]} != {coordinates[b]})' for a, b in edges], '1')
    bodycoords = [f'@perm(f)({c})' for c in coordinates] if framed else coordinates
    code = fold('+', [f'({c} * {3**i})' for i, c in enumerate(bodycoords)], '0')
    if framed:
        code = f'(λ&f.{code})({choice(list(range(6)), "F")})'
    source = '@keep = λ{0: λa.&{}; _: λp.λa.#Coloring{a}}\n'
    for index, perm in enumerate(PERMS):
        source += f'@p{index} = λ{{0: {perm[0]}; 1: {perm[1]}; _: λp.{perm[2]}}}\n'
    source += '@perm = λ{'+ '; '.join(f'{i}: @p{i}' for i in range(5))+'; _: λp.@p5}\n'
    variables = range(2 if framed else 0, v)
    source += '@solve = '+''.join(f'λ&c{i}.' for i in variables)+f'@keep({predicate})({code})\n'
    source += '@main = @solve'+''.join(f'({choice([0,1,2],f"V{i}")})' for i in variables)+'\n'
    return source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--profile', required=True)
    parser.add_argument('--hvm', required=True)
    args = parser.parse_args()
    folder = ROOT/'color_generated'
    folder.mkdir(exist_ok=True)
    cases = [('triangle', 3, list(itertools.combinations(range(3), 2)), 6),
             ('K4', 4, list(itertools.combinations(range(4), 2)), 0),
             ('K4_isolated8', 8, list(itertools.combinations(range(4), 2)), 0),
             ('triangle_isolated8', 8, list(itertools.combinations(range(3), 2)), 6*3**5),
             ('path6', 6, [(i,i+1) for i in range(5)], 3*2**5),
             ('path8', 8, [(i,i+1) for i in range(7)], 3*2**7)]
    predictions = [dict(name=name, vertices=v, edges=edges, models=models,
                        raw_coordinate_count=3**v, canonical_coordinate_count=3**(v-2),
                        retained_frames=6) for name,v,edges,models in cases]
    (ROOT/'color_predictions.json').write_text(json.dumps(predictions,indent=2)+'\n')
    results = []
    for name,v,edges,models in cases:
        readings = []
        for framed in (False,True):
            path=folder/f'{name}_{"framed" if framed else "raw"}.hvm4'
            path.write_text(net(v,edges,framed))
            p=subprocess.run([args.profile,str(path),'-s','-C'],capture_output=True,text=True,timeout=30,check=True)
            profile=json.loads(re.search(r'SAT_PROFILE (\{.*\})',p.stderr)[1])
            values=list(map(int,re.findall(r'#Coloring\{(\d+)\}',p.stdout)))
            assert len(values)==len(set(values))==models
            for value in values:
                colors=[(value//3**i)%3 for i in range(v)]
                assert all(colors[a]!=colors[b] for a,b in edges)
            baseline=subprocess.run([args.hvm,str(path),'-s','-C'],capture_output=True,text=True,timeout=30,check=True)
            assert list(map(int,re.findall(r'#Coloring\{(\d+)\}',baseline.stdout)))==values
            assert int(re.search(r'Itrs: (\d+)',baseline.stdout)[1])==profile['interactions']
            (path.with_suffix('.log')).write_text(p.stdout+p.stderr)
            readings.append(set(values))
            results.append(dict(name=name,framed=framed,outputs=len(values),**profile))
            print(name,framed,len(values),profile['interactions'],flush=True)
        assert readings[0]==readings[1], name
    (ROOT/'color_results.json').write_text(json.dumps(results,indent=2)+'\n')


if __name__=='__main__': main()

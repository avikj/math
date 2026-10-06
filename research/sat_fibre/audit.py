#!/usr/bin/env python3
"""Audit stored experimental evidence; this does not rerun HVM or Agda."""
import hashlib
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
from cost_predictions import predicted_rules

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
TSP = ROOT.parent / 'tsp_fibre'


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    counts = {}
    datasets = {}
    for label, path in [('basic', ROOT/'results.json'), ('np', ROOT/'np_results.json'),
                        ('cost', ROOT/'cost_results.json'), ('color', ROOT/'color_results.json'),
                        ('tsp', TSP/'results.json')]:
        payload = read(path)
        rows = payload['results'] if isinstance(payload, dict) else payload
        datasets[label] = rows
        complete = sum(r.get('status', 'complete') == 'complete' for r in rows)
        counts[label] = dict(cases=len(rows), complete=complete, inconclusive=len(rows)-complete)
        for row in rows:
            if 'rules' in row:
                assert sum(row['rules'].values()) == row['interactions'], (label, row)
    assert [counts[k]['cases'] for k in ('basic','np','cost','color','tsp')] == [108,120,12,12,32]
    predictions = {p['n']: p for p in read(ROOT/'cost_predictions.json')}
    for row in datasets['cost']:
        n = row['n']
        predicted = 9*2**n+16*n-4 if row['presentation']=='short' else n+30
        assert row['interactions'] == predicted == predictions[n][row['presentation']]
        if row['presentation']=='short':
            assert {k:v for k,v in row['rules'].items() if v} == predicted_rules(n)
    spec = importlib.util.spec_from_file_location('tsp_generator', TSP/'experiment.py')
    tsp = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tsp)
    predictions = {(p['family'],p['n']):p for p in read(TSP/'predictions.json')}
    for row in datasets['tsp']:
        family = 'circle' if row['name'].startswith('circle') else 'potential'
        p = predictions[family,row['n']]
        weights, optimum, certificate = tsp.matrix(family,row['n'])
        assert (weights,optimum,certificate) == (p['weights'],p['optimum'],p['certificate'])
        source, expected = tsp.net(weights,row['sharing'])
        assert source == (TSP/'generated'/f'{row["name"]}.hvm4').read_text()
        assert len(source.encode()) == row['source_bytes']
        assert all(p[k] == v for k,v in expected.items())
        n = row['n']
        cert_route = certificate['route']
        assert sorted(cert_route[:-1]) == list(range(n)) and cert_route[0] == cert_route[-1] == 0
        assert sum(weights[a][b] for a,b in zip(cert_route,cert_route[1:])) == optimum
        if family == 'circle':
            assert all(weights[i][j]>=1 for i in range(n) for j in range(n) if i!=j)
        else:
            u = certificate['potentials']
            assert all(weights[i][j]>=3+u[i]+u[j] for i in range(n) for j in range(n) if i!=j)
            assert optimum == 3*n+2*sum(u)
        if row['status']=='complete':
            route = row['route']
            assert route[0] == route[-1] == 0 and sorted(route[:-1]) == list(range(n))
            assert sum(weights[a][b] for a,b in zip(route,route[1:])) == row['cost'] == optimum
            if row['sharing']:
                assert row['rules']['OP2-NUM-NUM'] == p['transitions']+p['closing_extensions']+p['min_comparisons']
                assert row['rules']['DUP-SUP-SAME'] == row['rules']['DUP-SUP-DIFF'] == 0
    bend = read(ROOT/'bend-receipt.json')
    assert digest(ROOT/'SATProcess.bend') == bend['source_sha256']
    assert bend['readings'] == [[0,0,0],[0,1,1],[1,0,1],[1,1,0]] and bend['interactions']==1624
    profile = read(ROOT/'profile-build.json')
    provenance = {}
    for label, path, expected in [('hvm',Path(bend['hvm']),bend['hvm_sha256']),
                                  ('bend',Path(bend['bend']),bend['bend_sha256']),
                                  ('profile',Path(profile['binary']),profile['binary_sha256'])]:
        assert digest(path) == expected, label
        provenance[label] = dict(path=str(path),sha256=expected)
    for path in (ROOT/'np_results.json', TSP/'results.json'):
        recorded = read(path)
        assert recorded['profile_sha256'] == provenance['profile']['sha256']
        assert recorded['hvm_sha256'] == provenance['hvm']['sha256']
    proof_checks = read(ROOT/'proof-verification.json')
    assert len(proof_checks) == 4
    for check in proof_checks:
        assert check['exit_code'] == 0
        assert digest(REPO/check['module']) == check['source_sha256']
    counts['bend'] = dict(cases=1,complete=1,inconclusive=0)
    sources = {str(p.relative_to(REPO)):digest(p) for folder in (ROOT,TSP)
               for p in sorted(folder.iterdir()) if p.suffix in ('.agda','.py','.bend','.md')}
    receipt = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
                   kind='stored-evidence audit; no runtime or proof checker rerun',
                   proof_modules_checked=len(proof_checks), counts=counts, total_cases=sum(v['cases'] for v in counts.values()),
                   total_complete=sum(v['complete'] for v in counts.values()),
                   provenance=provenance,sources_sha256=sources)
    (ROOT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('counts','total_cases','total_complete')},indent=2))


if __name__ == '__main__':
    main()

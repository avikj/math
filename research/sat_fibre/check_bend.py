#!/usr/bin/env python3
"""Stage existing imports, check the coinductive client, execute full lowering."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--bend', required=True)
parser.add_argument('--hvm', required=True)
args = parser.parse_args()
with tempfile.TemporaryDirectory(prefix='sat-fibre-') as directory:
    stage = Path(directory)
    deps = ROOT.parents[1] / 'collab/bend2-cubical/port'
    # Isolated copies: do not edit the existing port or the installed compiler.
    for source in deps.glob('*.bend'):
        shutil.copy2(source, stage/source.name)
    shutil.copy2(ROOT/'SATProcess.bend', stage/'SATProcess.bend')
    checked = subprocess.run([args.bend, str(stage/'SATProcess.bend'), '--total'],
                             capture_output=True, text=True, timeout=60, check=True)
    (ROOT/'bend-check.log').write_text(checked.stdout+checked.stderr)
    emitted = subprocess.run([args.bend, str(stage/'SATProcess.bend'), '--to-hvm4-full'],
                             capture_output=True, text=True, timeout=60, check=True)
    (ROOT/'SATProcess.hvm4').write_text(emitted.stdout)
    executed = subprocess.run([args.hvm, str(ROOT/'SATProcess.hvm4'), '-s', '-C'],
                              capture_output=True, text=True, timeout=30, check=True)
    output = re.sub(r'\x1b\[[0-9;]*m', '', executed.stdout)
    (ROOT/'bend-runtime.log').write_text(output+executed.stderr)
    triples = [tuple(map(int, row)) for row in re.findall(
        r'#reading\{\},#Pair\{([01]),#Pair\{([01]),#Pair\{([01]),', output)]
    assert sorted(triples) == [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)], output
    receipt = dict(bend=str(Path(args.bend).resolve()),
                   bend_sha256=hashlib.sha256(Path(args.bend).read_bytes()).hexdigest(),
                   hvm=str(Path(args.hvm).resolve()),
                   hvm_sha256=hashlib.sha256(Path(args.hvm).read_bytes()).hexdigest(),
                   source_sha256=hashlib.sha256((ROOT/'SATProcess.bend').read_bytes()).hexdigest(),
                   imports={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in deps.glob('*.bend')},
                   readings=triples,
                   interactions=int(re.search(r'Itrs: (\d+)', output)[1]))
    (ROOT/'bend-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(output)

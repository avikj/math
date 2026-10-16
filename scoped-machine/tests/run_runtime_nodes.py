#!/usr/bin/env python3
"""Fresh-build the §96 nonempty runtime-diagram witness against a supplied tree.

No source is patched implicitly. --eval-source is solely for reproducing the
author's explicit b612a07-plus-R1 candidate; use the worker's corrected tree
without that option for acceptance. Pools are installed by the C witness.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('tree', type=Path)
p.add_argument('--sanitizer', choices=('asan', 'tsan', 'none'), default='asan')
p.add_argument('--detect-leaks', choices=('0', '1'), default='1')
p.add_argument('--eval-source', type=Path)
p.add_argument('--existing-objects', action='store_true', help='author convenience only')
p.add_argument('--output', type=Path, default=Path('runtime-node-results.json'))
p.add_argument('--timeout', type=int, default=600)
p.add_argument('--modes', nargs='+', choices=('generic', 'runtime', 'levels'), default=('runtime', 'levels'))
p.add_argument('--cc', default='cc')
a = p.parse_args()
tree = a.tree.resolve()
if (tree/'scoped-machine').is_dir():
    tree /= 'scoped-machine'
if not (tree/'src/eval.c').is_file():
    p.error('expected scoped-machine source tree')
here = Path(__file__).resolve().parent
flags = ['-std=c11', '-O1', '-g', '-Wall', '-Wextra', '-fno-omit-frame-pointer',
         '-pthread', '-I', str(tree/'src')]
if a.sanitizer != 'none':
    flags += ['-fsanitize=' + ('address,undefined' if a.sanitizer == 'asan' else 'thread')]
env = {**os.environ, 'ASAN_OPTIONS': 'detect_leaks='+a.detect_leaks+':halt_on_error=1',
       'UBSAN_OPTIONS': 'halt_on_error=1:print_stacktrace=1', 'TSAN_OPTIONS': 'halt_on_error=1'}
report = {'tree': str(tree), 'sanitizer': a.sanitizer,
          'detect_leaks': a.detect_leaks, 'source_sha256': {}, 'results': []}
status = 0
try:
    with tempfile.TemporaryDirectory(prefix='runtime-node-witness-') as temp:
        build = Path(temp)
        objects = []
        for source in sorted((tree/'src').glob('*.c')):
            chosen = a.eval_source.resolve() if a.eval_source and source.stem == 'eval' else source
            report['source_sha256'][source.name] = hashlib.sha256(chosen.read_bytes()).hexdigest()
            if a.existing_objects and chosen == source:
                obj = tree/'build/tsan'/(source.stem+'.o') if a.sanitizer == 'tsan' else source.with_suffix('.o')
                assert obj.is_file(), obj
            else:
                obj = build/(source.stem+'.o')
                subprocess.run([a.cc, *flags, '-c', str(chosen), '-o', str(obj)], check=True)
            objects.append(str(obj))
        if a.eval_source:
            report['eval_source_override'] = str(a.eval_source.resolve())
        witness = here/'review_runtime_nodes.c'
        report['witness_sha256'] = hashlib.sha256(witness.read_bytes()).hexdigest()
        exe = build/'review_runtime_nodes'
        subprocess.run([a.cc, *flags, str(witness), *objects, '-o', str(exe)], check=True)
        jobs = [(w,m) for m in a.modes for w in ((0,) if m == 'levels' else (0,4))]
        for workers, mode in jobs:
            start = time.monotonic()
            try:
                r = subprocess.run([str(exe), str(workers), mode], env=env,
                                   capture_output=True, text=True, timeout=a.timeout)
                item = {'workers': workers, 'mode': mode, 'exit_code': r.returncode,
                        'stdout': r.stdout, 'stderr': r.stderr}
            except subprocess.TimeoutExpired:
                item = {'workers': workers, 'mode': mode, 'exit_code': None, 'error': 'timeout'}
            item['seconds'] = round(time.monotonic()-start, 3)
            report['results'].append(item)
            print(json.dumps(item), flush=True)
        status = int(any(r['exit_code'] != 0 for r in report['results']))
except subprocess.CalledProcessError as error:
    report['build_failure'] = {'command': error.cmd, 'exit_code': error.returncode}
    status = 1
finally:
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2)+'\n')
raise SystemExit(status)

#!/usr/bin/env python3
"""V22 prefix review: 17 jobs per configuration, all must exit zero.

Default: build production objects freshly. --objects reuses an explicitly
chosen matching object directory. ASan leak checking defaults to enabled;
the review host's evidence explicitly used --detect-leaks 0.
"""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('tree', type=Path)
p.add_argument('--sanitizer', choices=['asan', 'tsan', 'none'], default='asan')
p.add_argument('--detect-leaks', choices=['0', '1'], default='1')
p.add_argument('--objects', type=Path)
p.add_argument('--output', type=Path, default=Path('v22-results.json'))
p.add_argument('--timeout', type=int, default=150)
a = p.parse_args()
tree = a.tree.resolve()
if (tree / 'scoped-machine').is_dir():
    tree /= 'scoped-machine'
here = Path(__file__).resolve().parent
flags = ['-std=c11', '-O1', '-g', '-fno-omit-frame-pointer', '-pthread', '-I' + str(tree / 'src')]
if a.sanitizer != 'none':
    flags += ['-fsanitize=' + ('address,undefined' if a.sanitizer == 'asan' else 'thread')]
env = dict(os.environ, ASAN_OPTIONS='detect_leaks=' + a.detect_leaks + ':halt_on_error=1',
           UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1', TSAN_OPTIONS='halt_on_error=1')
cases = []
for mode in ['ready-prefix', 'late-context', 'adapter-premise', 'branch-prefix', 'comp-guard', 'subscriber-race']:
    for workers in [0, 4]:
        cases.append((mode + '-' + str(workers), 'review', [mode, str(workers)]))
for mode in ['specialize', 'restrict']:
    for workers in [0, 4]:
        cases.append(('live-' + mode + '-' + str(workers), 'live', [mode, str(workers)]))
cases.append(('production-prefix', 'production', ['all']))
report = dict(tree=str(tree), sanitizer=a.sanitizer, detect_leaks=a.detect_leaks,
              reused_objects=bool(a.objects), results=[])
try:
    with tempfile.TemporaryDirectory(prefix='review-v22-') as td:
        build = Path(td)
        def compile_one(src):
            obj = a.objects.resolve() / (src.stem + '.o') if a.objects else build / (src.stem + '.o')
            if a.objects:
                assert obj.is_file(), obj
            else:
                subprocess.run(['cc', *flags, '-c', str(src), '-o', str(obj)], check=True)
            return str(obj)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            objects = list(pool.map(compile_one, sorted((tree / 'src').glob('*.c'))))
        sources = dict(review=here / 'review_v22.c', live=tree / 'tests/review_live_prefix.c',
                       production=tree / 'tests/test_prefix.c')
        binaries = {}
        for name, kind, args in cases:
            if kind not in binaries:
                binary = build / kind
                subprocess.run(['cc', *flags, str(sources[kind]), *objects, '-o', str(binary)], check=True)
                binaries[kind] = binary
            start = time.monotonic()
            try:
                r = subprocess.run([str(binaries[kind]), *args], env=env, capture_output=True,
                                   text=True, timeout=a.timeout)
                row = dict(name=name, args=args, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr)
            except subprocess.TimeoutExpired as e:
                row = dict(name=name, args=args, exit_code=None, error='timeout',
                           stdout=(e.stdout or b'').decode(), stderr=(e.stderr or b'').decode())
            row['seconds'] = time.monotonic() - start
            report['results'].append(row)
            print(name, 'exit', row['exit_code'], flush=True)
except (AssertionError, subprocess.CalledProcessError) as e:
    report['build_error'] = str(e)
finally:
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2) + '\n')
raise SystemExit(int('build_error' in report or len(report['results']) != len(cases)
                    or any(r['exit_code'] != 0 for r in report['results'])))

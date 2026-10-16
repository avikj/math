#!/usr/bin/env python3
"""Focused v19 correction runner. Every listed job must pass."""
import argparse, concurrent.futures, json, os, subprocess, tempfile, time
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=['asan','tsan','none'],default='asan')
p.add_argument('--detect-leaks',choices=['0','1'],default='1')
p.add_argument('--objects',type=Path,help='Matching independently built core objects; omitted = fresh build.')
p.add_argument('--output',type=Path,default=Path('v19-results.json'))
p.add_argument('--timeout',type=int,default=120)
a=p.parse_args();tree=a.tree.resolve();here=Path(__file__).resolve().parent
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I',str(tree/'src'),'-I',str(tree/'tests')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'reused_objects':bool(a.objects),'results':[]}
try:
 with tempfile.TemporaryDirectory(prefix='review-v19-') as td:
    build=Path(td);objects={}
    def compile_one(s):
        o=a.objects.resolve()/(s.stem+'.o') if a.objects else build/(s.stem+'.o')
        if a.objects:assert o.is_file(),o
        else:subprocess.run(['cc',*flags,'-c',str(s),'-o',str(o)],check=True)
        return s.stem,str(o)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        objects.update(pool.map(compile_one,sorted((tree/'src').glob('*.c'))))
    cases=[('review_v19',here/'review_v19.c',False,[[x] for x in ['arena-directory','arena-empty','audit-admission','audit-marks']]),
      ('review_v19_work',here/'review_v19_work.c',True,[['sync-reap'],['audit-sharing']]),
      ('review_assumption_copy',here/'review_assumption_copy.c',True,[['both'],['transform'],['reference']]),
      ('review_arena_budget',tree/'tests/review_arena_budget.c',True,[[]]),
      ('review_audit_budget',tree/'tests/review_audit_budget.c',True,[['256']]),
      ('review_store_interleave',tree/'tests/review_store_interleave.c',True,[[]]),
      ('review_prepare_boundary',tree/'tests/review_prepare_boundary.c',True,[['64'],['4096']]),
      ('production_work',tree/'tests/test_work.c',False,[[]]),
      ('production_proof_use',tree/'tests/test_proof_use.c',False,[[]])]
    for name,source,white,modes in cases:
        binary=build/name
        objs=[v for k,v in objects.items() if not(white and k=='work')]
        subprocess.run(['cc',*flags,str(source),*objs,'-o',str(binary)],check=True)
        for args in modes:
            t=time.monotonic()
            try:
                r=subprocess.run([str(binary),*args],env=env,capture_output=True,text=True,timeout=a.timeout)
                row={'name':name,'args':args,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
            except subprocess.TimeoutExpired as e:
                row={'name':name,'args':args,'exit_code':None,'error':'timeout'}
            row['seconds']=time.monotonic()-t;report['results'].append(row)
            print(name,args,'exit',row['exit_code'],flush=True)
except (subprocess.CalledProcessError,AssertionError) as e:
    report['build_error']=str(e)
finally:
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(int('build_error' in report or any(r['exit_code']!=0 for r in report['results'])))

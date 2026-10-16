#!/usr/bin/env python3
"""Focused v16 regression runner. All jobs must pass after the boundary patch."""
import argparse, concurrent.futures, json, os, subprocess, tempfile, time
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=['asan','tsan','none'],default='asan')
p.add_argument('--detect-leaks',choices=['0','1'],default='1')
p.add_argument('--objects',type=Path,help='Matching independently built core objects; omitted = fresh build.')
p.add_argument('--output',type=Path,default=Path('v16-results.json'))
p.add_argument('--timeout',type=int,default=120)
a=p.parse_args();tree=a.tree.resolve();here=Path(__file__).resolve().parent
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I',str(tree/'src'),'-I',str(tree/'tests')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'reused_objects':bool(a.objects),'results':[]}
try:
 with tempfile.TemporaryDirectory(prefix='review-v16-') as td:
    build=Path(td);objects={}
    def compile_one(s):
        o=a.objects.resolve()/(s.stem+'.o') if a.objects else build/(s.stem+'.o')
        if a.objects:assert o.is_file(),o
        else:subprocess.run(['cc',*flags,'-c',str(s),'-o',str(o)],check=True)
        return s.stem,str(o)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        objects.update(pool.map(compile_one,sorted((tree/'src').glob('*.c'))))
    cases=[('review_work_edges',tree/'tests/review_work_edges.c',True,[['interleave'],['same-key'],['growth'],['drain']]),
      ('review_reservation_budget',tree/'tests/review_reservation_budget.c',True,[[]]),
      ('review_store_growth',tree/'tests/review_store_growth.c',True,[[]]),
      ('review_store_interleave',here/'review_store_interleave.c',True,[[]]),
      ('review_work_budget',tree/'tests/review_work_budget.c',True,[[]]),
      ('production_work',tree/'tests/test_work.c',False,[[]]),
      ('production_reuse',tree/'tests/test_reuse.c',False,[[]]),
      ('review_prepare_boundary',here/'review_prepare_boundary.c',True,[['64'],['4096']])]
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

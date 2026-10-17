#!/usr/bin/env python3
"""Independent V23 probes. Every selected case must exit zero after correction.
exact-export.patch fixes five export cases; scope-depth.patch fixes the two
scope cases. Neither patch fixes cleanup-long or counter-wrap.
"""
import argparse, concurrent.futures, json, os, subprocess, tempfile, time
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=['asan','tsan','none'],default='asan')
p.add_argument('--detect-leaks',choices=['0','1'],default='1')
p.add_argument('--objects',type=Path,help='Matching freshly built objects, optional')
p.add_argument('--output',type=Path,default=Path('v23-results.json'))
p.add_argument('--timeout',type=int,default=90)
p.add_argument('--only',help='Comma-separated modes')
a=p.parse_args();tree=a.tree.resolve();here=Path(__file__).resolve().parent
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I'+str(tree/'src')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
modes=['canon-tail','export-universe','export-template','export-runtime','long-name','cleanup-long','counter-wrap','small-stack-validation','deep-capture']
if a.only:modes=[m for m in modes if m in a.only.split(',')]
report=dict(tree=str(tree),sanitizer=a.sanitizer,detect_leaks=a.detect_leaks,reused_objects=bool(a.objects),results=[])
try:
 with tempfile.TemporaryDirectory(prefix='review-v23-') as td:
  build=Path(td)
  def compile_one(src):
   obj=a.objects.resolve()/(src.stem+'.o') if a.objects else build/(src.stem+'.o')
   if a.objects:assert obj.is_file(),obj
   else:subprocess.run(['cc',*flags,'-c',str(src),'-o',str(obj)],check=True)
   return str(obj)
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
   objects=list(pool.map(compile_one,sorted(s for s in (tree/'src').glob('*.c') if s.stem!='work')))
  binary=build/'review_v23'
  subprocess.run(['cc',*flags,str(here/'review_v23.c'),*objects,'-Wl,--wrap=pthread_create','-o',str(binary)],check=True)
  for mode in modes:
   start=time.monotonic()
   try:
    r=subprocess.run([str(binary),mode],env=env,capture_output=True,text=True,timeout=a.timeout)
    row=dict(mode=mode,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr)
   except subprocess.TimeoutExpired as e:
    row=dict(mode=mode,exit_code=None,error='timeout',stdout=(e.stdout or b'').decode(),stderr=(e.stderr or b'').decode())
   row['seconds']=time.monotonic()-start;report['results'].append(row)
   print(mode,'exit',row['exit_code'],row.get('error',''),flush=True)
except (AssertionError,subprocess.CalledProcessError) as e:report['build_error']=str(e)
finally:
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(int('build_error' in report or any(r['exit_code']!=0 for r in report['results'])))

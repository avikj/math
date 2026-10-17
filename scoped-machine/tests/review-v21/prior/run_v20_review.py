#!/usr/bin/env python3
"""V20 regression runner. All cases must exit zero on a fully corrected tree.
Fresh-build default; --objects accepts matching independently built objects.
"""
import argparse,concurrent.futures,json,os,subprocess,tempfile,time
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path);p.add_argument('--sanitizer',choices=['asan','tsan','none'],default='asan')
p.add_argument('--detect-leaks',choices=['0','1'],default='1');p.add_argument('--objects',type=Path)
p.add_argument('--output',type=Path,default=Path('v20-results.json'));p.add_argument('--timeout',type=int,default=120)
p.add_argument('--only',help='Comma-separated case names (default: all).')
a=p.parse_args();tree=a.tree.resolve();here=Path(__file__).resolve().parent
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I'+str(tree/'src'),'-I'+str(tree/'tests')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
cases=[]
for mode in ['independent','independent-release','independent-cone','retry','prepare-retry','lifecycle','fresh-retire']:
 cases.append((mode,'work',[mode]))
for n in [32,256,1024]:cases.append(('evaluator-'+str(n),'work',['evaluator',str(n)]))
for n in [64,512]:cases.append(('map-sort-'+str(n),'work',['map-sort',str(n)]))
for n in [64,300]:cases.append(('collision-'+str(n),'intern',[str(n)]))
cases += [('delivered-kernel-probe','kernel',['64']),('production-check','check',[]),('production-reuse','reuse',[]),('production-compiler','compiler',[]),('production-runtime','runtime',[])]
if a.only:cases=[c for c in cases if c[0] in a.only.split(',')]
report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'reused_objects':bool(a.objects),'results':[]}
try:
 with tempfile.TemporaryDirectory(prefix='review-v20-') as td:
  build=Path(td);objects={}
  def compile_one(src):
   obj=a.objects.resolve()/(src.stem+'.o') if a.objects else build/(src.stem+'.o')
   if a.objects:assert obj.is_file(),obj
   else:subprocess.run(['cc',*flags,'-c',str(src),'-o',str(obj)],check=True)
   return src.stem,str(obj)
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:objects.update(pool.map(compile_one,sorted((tree/'src').glob('*.c'))))
  binaries={}
  sources={'work':here/'review_v20.c','intern':here/'review_v20_intern.c','kernel':tree/'tests/review_kernel_budget.c','check':tree/'tests/test_check.c','reuse':tree/'tests/test_reuse.c','compiler':tree/'tests/test_compiler.c','runtime':tree/'tests/test_runtime.c'}
  for name,kind,args in cases:
   if kind not in binaries:
    binary=build/kind
    objs=[v for k,v in objects.items() if not(kind in ['work','kernel'] and k=='work')]
    subprocess.run(['cc',*flags,str(sources[kind]),*objs,*(['-Wl,--wrap=qsort'] if kind=='work' else []),'-o',str(binary)],check=True)
    binaries[kind]=binary
   start=time.monotonic()
   try:
    r=subprocess.run([str(binaries[kind]),*args],env=env,capture_output=True,text=True,timeout=a.timeout)
    row={'name':name,'args':args,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
   except subprocess.TimeoutExpired as e:row={'name':name,'args':args,'exit_code':None,'error':'timeout'}
   row['seconds']=time.monotonic()-start;report['results'].append(row);print(name,'exit',row['exit_code'],flush=True)
except (AssertionError,subprocess.CalledProcessError) as e:report['build_error']=str(e)
finally:
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(int('build_error' in report or any(x['exit_code']!=0 for x in report['results'])))

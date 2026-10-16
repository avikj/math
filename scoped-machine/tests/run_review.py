#!/usr/bin/env python3
"""Fresh-build and check b612a07 corrections and the next-increment witnesses.
Alias and bounded-step tests return nonzero on the reviewed uncorrected tree.
The proof-boundary module is an author integration witness, not production.
"""
import argparse,json,os,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=('asan','tsan','none'),default='asan')
p.add_argument('--detect-leaks',choices=('0','1'),default='1')
p.add_argument('--output',type=Path,default=Path('review-results.json'))
p.add_argument('--cc',default='cc')
p.add_argument('--existing-objects',action='store_true',help='author convenience: use this tree\'s matching make objects')
a=p.parse_args();tree=a.tree.resolve();here=Path(__file__).resolve().parent
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
assert (tree/'src/eval.c').is_file()
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I',str(tree/'src'),'-I',str(tree/'tests')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'results':[]}
status=0
try:
 with tempfile.TemporaryDirectory(prefix='review-b612a07-') as td:
  b=Path(td);objs={}
  for source in sorted((tree/'src').glob('*.c')):
   obj=(tree/'build/tsan'/(source.stem+'.o') if a.sanitizer=='tsan' else source.with_suffix('.o')) if a.existing_objects else b/(source.stem+'.o')
   if a.existing_objects: assert obj.is_file(),obj
   else:subprocess.run([a.cc,*flags,'-c',str(source),'-o',str(obj)],check=True)
   objs[source.stem]=str(obj)
  jobs=[]
  for name in ('review_alias_scope','review_alias_faces','review_work_budget'):
   core=[v for k,v in objs.items() if not (name=='review_work_budget' and k=='work')]
   subprocess.run([a.cc,*flags,str(here/(name+'.c')),*core,'-o',str(b/name)],check=True)
   for w in ((0,) if name=='review_work_budget' else (0,4)):
    jobs.append((name,w,[str(b/name)]+([] if name=='review_work_budget' else [str(w)]),'v9-correction'))
  ni=here/'next-increment'
  pb=b/'proof_boundary.o'
  subprocess.run([a.cc,*flags,'-c',str(ni/'proof_boundary.c'),'-o',str(pb)],check=True)
  for name in ('review_runtime_presentations','review_singleton_witnesses','review_generic_identity_action','review_certificate_boundary','test_proof_boundary','review_frame_cost'):
   extra=[str(pb)] if name in ('review_certificate_boundary','test_proof_boundary') else []
   subprocess.run([a.cc,*flags,str(ni/(name+'.c')),str(here/'review_workers.c'),'-Wl,--wrap=eval_init',*extra,*objs.values(),'-o',str(b/name)],check=True)
   for w in (0,4):jobs.append((name,w,[str(b/name)],'next-increment-witness'))
  for name,w,cmd,kind in jobs:
   try:
    r=subprocess.run(cmd,env={**env,'REVIEW_WORKERS':str(w)},capture_output=True,text=True,timeout=180)
    item={'name':name,'actual_workers':w,'kind':kind,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
   except subprocess.TimeoutExpired:
    item={'name':name,'actual_workers':w,'kind':kind,'exit_code':None,'error':'timeout'}
   report['results'].append(item);print(json.dumps(item),flush=True)
  status=int(any(x['exit_code']!=0 for x in report['results']))
except subprocess.CalledProcessError as e:
 report['build_failure']={'command':e.cmd,'exit_code':e.returncode};status=1
finally:
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(status)

#!/usr/bin/env python3
"""Fresh-build the current core and run the proof/cost boundary witnesses."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=('asan','tsan','none'),default='asan')
p.add_argument('--detect-leaks',choices=('0','1'),default='1')
p.add_argument('--output',type=Path,default=Path('boundary-results.json'))
p.add_argument('--cc',default='cc')
a=p.parse_args(); tree=a.tree.resolve()
if (tree/'scoped-machine').is_dir(): tree/='scoped-machine'
if not (tree/'src/machine.c').is_file(): p.error('expected scoped-machine source')
here=Path(__file__).resolve().parent
flags=['-std=c11','-Wall','-Wextra','-O1','-g','-fno-omit-frame-pointer','-pthread','-I',str(tree/'tests')]
if a.sanitizer!='none': flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env=dict(os.environ)
if a.sanitizer=='asan':
    env['ASAN_OPTIONS']='detect_leaks='+a.detect_leaks+':halt_on_error=1'
    env['UBSAN_OPTIONS']='halt_on_error=1:print_stacktrace=1'
if a.sanitizer=='tsan': env['TSAN_OPTIONS']='halt_on_error=1'
names=['review_certificate_boundary','test_proof_boundary','review_frame_cost']
results=[]; report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'results':results}
status=0
try:
    with tempfile.TemporaryDirectory(prefix='proof-cost-boundaries-') as td:
        build=Path(td); objs=[]
        for source in sorted((tree/'src').glob('*.c')):
            obj=build/(source.stem+'.o')
            subprocess.run([a.cc,*flags,'-c',str(source),'-o',str(obj)],check=True)
            objs.append(str(obj))
        module=build/'proof_boundary.o'
        subprocess.run([a.cc,*flags,'-c',str(here/'proof_boundary.c'),'-o',str(module)],check=True)
        for name in names:
            subprocess.run([a.cc,*flags,str(here/(name+'.c')),str(module),*objs,'-o',str(build/name)],check=True)
        for workers in (1,4):
            for name in names:
                try:
                    r=subprocess.run([str(build/name)],env={**env,'CUBICAL_WORKERS':str(workers)},text=True,capture_output=True,timeout=90)
                    item={'name':name,'workers':workers,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
                except subprocess.TimeoutExpired:
                    item={'name':name,'workers':workers,'exit_code':None,'error':'timeout'}
                results.append(item); print(json.dumps(item),flush=True)
        if any(r['exit_code']!=0 for r in results): status=1
except subprocess.CalledProcessError as e:
    report['build_failure']={'command':e.cmd,'exit_code':e.returncode}; status=1
finally:
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(status)

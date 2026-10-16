#!/usr/bin/env python3
"""Build the supplied tree and run independent b8ba937 review regressions.
Every mode must exit zero on a corrected implementation.
"""
import argparse, concurrent.futures, json, os, subprocess, tempfile, time
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('tree',type=Path)
p.add_argument('--sanitizer',choices=['asan','tsan','none'],default='asan')
p.add_argument('--detect-leaks',choices=['0','1'],default='1')
p.add_argument('--objects',type=Path,help='Reuse matching core objects; omit for a fresh build.')
p.add_argument('--output',type=Path,default=Path('b8ba937-results.json'))
p.add_argument('--timeout',type=int,default=120)
a=p.parse_args();tree=a.tree.resolve()
if (tree/'scoped-machine').is_dir():tree/='scoped-machine'
assert (tree/'src/work.c').is_file()
here=Path(__file__).resolve().parent
flags=['-std=c11','-O1','-g','-fno-omit-frame-pointer','-pthread','-I',str(tree/'src')]
if a.sanitizer!='none':flags+=['-fsanitize='+('address,undefined' if a.sanitizer=='asan' else 'thread')]
env={**os.environ,'ASAN_OPTIONS':'detect_leaks='+a.detect_leaks+':halt_on_error=1','UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1','TSAN_OPTIONS':'halt_on_error=1'}
report={'tree':str(tree),'sanitizer':a.sanitizer,'detect_leaks':a.detect_leaks,'reused_objects':bool(a.objects),'results':[]}
try:
    with tempfile.TemporaryDirectory(prefix='review-b8ba937-') as td:
        build=Path(td);objects={}
        def compile_one(s):
            o=a.objects.resolve()/(s.stem+'.o') if a.objects else build/(s.stem+'.o')
            if a.objects:assert o.is_file(),o
            else:subprocess.run(['cc',*flags,'-c',str(s),'-o',str(o)],check=True)
            return s.stem,str(o)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            objects.update(pool.map(compile_one,sorted((tree/'src').glob('*.c'))))
        jobs=[]
        for source,modes in [('review_work_edges.c',['interleave','same-key','growth','drain']),('review_runtime_edges.c',['levels','residual','commute','runtime-cold','proof-cold'])]:
            binary=build/Path(source).stem
            objs=[v for k,v in objects.items() if not (source=='review_work_edges.c' and k=='work')]
            subprocess.run(['cc',*flags,str(here/source),*objs,'-o',str(binary)],check=True)
            jobs.extend((binary,[mode]) for mode in modes)
        witness=build/'review_runtime_nodes'
        subprocess.run(['cc',*flags,str(here/'review_runtime_nodes.c'),*objects.values(),'-o',str(witness)],check=True)
        jobs.extend((witness,args) for args in [['0','runtime'],['4','runtime'],['0','levels']])
        for source,label in [(here/'review_node_level.c','review_node_level'),(tree/'tests/test_runtime.c','production_runtime')]:
            binary=build/label
            subprocess.run(['cc',*flags,'-I',str(tree/'tests'),str(source),*objects.values(),'-o',str(binary)],check=True)
            jobs.append((binary,[]))
        for binary,args in jobs:
            start=time.monotonic()
            try:
                r=subprocess.run([str(binary),*args],env=env,capture_output=True,text=True,timeout=a.timeout)
                row=dict(name=binary.name,args=args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr)
            except subprocess.TimeoutExpired as e:
                row=dict(name=binary.name,args=args,exit_code=None,error='timeout',stdout=(e.stdout or b'').decode(errors='replace') if isinstance(e.stdout,bytes) else e.stdout,stderr=(e.stderr or b'').decode(errors='replace') if isinstance(e.stderr,bytes) else e.stderr)
            row['seconds']=time.monotonic()-start;report['results'].append(row)
            print(binary.name,args,'exit',row['exit_code'],flush=True)
except (subprocess.CalledProcessError,AssertionError) as e:
    report['build_error']=str(e)
finally:
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(int('build_error' in report or any(r['exit_code']!=0 for r in report['results'])))

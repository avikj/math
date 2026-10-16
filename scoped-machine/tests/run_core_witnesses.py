#!/usr/bin/env python3
"""Compile and run the three ordinary-core construction witnesses."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("tree",type=Path)
p.add_argument("--sanitizer",choices=("asan","tsan","none"),default="asan")
p.add_argument("--detect-leaks",choices=("0","1"),default="1")
p.add_argument("--output",type=Path,default=Path("core-witness-results.json"))
p.add_argument("--cc",default="cc")
p.add_argument("--diagnose-current-admission",action="store_true",help="also reproduce the current VALID/W_STUCK recursive-proof boundary")
a=p.parse_args()
tree=a.tree.resolve()
if (tree/"scoped-machine").is_dir(): tree/= "scoped-machine"
if not (tree/"src/machine.c").is_file(): p.error("expected scoped-machine tree")
here=Path(__file__).resolve().parent
flags=["-std=c11","-O1","-g","-fno-omit-frame-pointer","-pthread","-I",str(tree/"tests")]
if a.sanitizer!="none": flags += ["-fsanitize="+("address,undefined" if a.sanitizer=="asan" else "thread")]
env=dict(os.environ)
if a.sanitizer=="asan":
    env["ASAN_OPTIONS"]="detect_leaks="+a.detect_leaks+":halt_on_error=1"
    env["UBSAN_OPTIONS"]="halt_on_error=1:print_stacktrace=1"
if a.sanitizer=="tsan": env["TSAN_OPTIONS"]="halt_on_error=1"
names=["review_runtime_presentations","review_singleton_witnesses","review_generic_identity_action"]
if a.diagnose_current_admission: names.append("review_recursive_proof_boundary")
results=[]
report={"tree":str(tree),"sanitizer":a.sanitizer,"detect_leaks":a.detect_leaks,"results":results}
status=0
try:
    with tempfile.TemporaryDirectory(prefix="runtime-core-witnesses-") as td:
        build=Path(td); objs=[]
        for source in sorted((tree/"src").glob("*.c")):
            obj=build/(source.stem+".o")
            subprocess.run([a.cc,*flags,"-c",str(source),"-o",str(obj)],check=True)
            objs.append(str(obj))
        for name in names:
            subprocess.run([a.cc,*flags,str(here/(name+".c")),*objs,"-o",str(build/name)],check=True)
        for workers in (1,4):
            for name in names:
                e={**env,"CUBICAL_WORKERS":str(workers)}
                try:
                    r=subprocess.run([str(build/name)],env=e,text=True,capture_output=True,timeout=180)
                    item={"name":name,"workers":workers,"exit_code":r.returncode,"stdout":r.stdout,"stderr":r.stderr}
                except subprocess.TimeoutExpired:
                    item={"name":name,"workers":workers,"exit_code":None,"error":"timeout"}
                results.append(item); print(json.dumps(item),flush=True)
        if any(r["exit_code"]!=0 for r in results): status=1
except subprocess.CalledProcessError as error:
    report["build_failure"]={"command":error.cmd,"exit_code":error.returncode}; status=1
finally:
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(report,indent=2)+"\n")
raise SystemExit(status)

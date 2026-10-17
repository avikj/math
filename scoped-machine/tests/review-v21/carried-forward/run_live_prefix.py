#!/usr/bin/env python3
"""Build and run the §84.2 live-prefix regression on a supplied tree.

Zero exit is the required corrected behavior. The reviewed c365d86 base
returns one for every case: answers are right but one beta is repeated.
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
p.add_argument("tree", type=Path)
p.add_argument("--sanitizer", choices=("asan", "tsan", "none"), default="asan")
p.add_argument("--detect-leaks", choices=("0", "1"), default="1")
p.add_argument("--objects", type=Path, help="Optional matching independently built objects")
p.add_argument("--output", type=Path, default=Path("prefix-results.json"))
a = p.parse_args()
tree = a.tree.resolve()
if (tree / "scoped-machine").is_dir():
    tree /= "scoped-machine"
here = Path(__file__).resolve().parent
flags = ["-std=c11", "-O1", "-g", "-fno-omit-frame-pointer", "-pthread", "-I" + str(tree / "src")]
if a.sanitizer != "none":
    flags += ["-fsanitize=" + ("address,undefined" if a.sanitizer == "asan" else "thread")]
env = dict(os.environ, ASAN_OPTIONS="detect_leaks=" + a.detect_leaks + ":halt_on_error=1",
           UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1", TSAN_OPTIONS="halt_on_error=1")
report = dict(tree=str(tree), sanitizer=a.sanitizer, detect_leaks=a.detect_leaks,
              reused_objects=bool(a.objects), results=[])
try:
    with tempfile.TemporaryDirectory(prefix="review-prefix-") as td:
        build = Path(td)
        def compile_one(src):
            obj = a.objects.resolve() / (src.stem + ".o") if a.objects else build / (src.stem + ".o")
            if a.objects:
                assert obj.is_file(), obj
            else:
                subprocess.run(["cc", *flags, "-c", str(src), "-o", str(obj)], check=True)
            return str(obj)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            objects = list(pool.map(compile_one, sorted((tree / "src").glob("*.c"))))
        binary = build / "prefix"
        subprocess.run(["cc", *flags, str(here / "review_live_prefix.c"), *objects, "-o", str(binary)], check=True)
        for mode in ("specialize", "restrict"):
            for workers in (0, 4):
                start = time.monotonic()
                try:
                    r = subprocess.run([str(binary), mode, str(workers)], env=env,
                                       capture_output=True, text=True, timeout=120)
                    row = dict(mode=mode, workers=workers, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr)
                except subprocess.TimeoutExpired:
                    row = dict(mode=mode, workers=workers, exit_code=None, error="timeout")
                row["seconds"] = time.monotonic() - start
                report["results"].append(row)
                print(mode, workers, "exit", row["exit_code"], flush=True)
except (AssertionError, subprocess.CalledProcessError) as e:
    report["build_error"] = str(e)
finally:
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2) + "\n")
raise SystemExit(int("build_error" in report or any(r["exit_code"] != 0 for r in report["results"])))

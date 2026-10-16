#!/usr/bin/env python3
"""Build the v9 acceptance tests against a worker tree without changing it.

Production must implement the supplied reuse_stats.h ABI. A missing implementation
is an implementation requirement, not a reason to link a test stub.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("tree", type=Path, help="repository root or scoped-machine directory")
p.add_argument("--output", type=Path, default=Path("reuse-acceptance-results.json"))
p.add_argument("--cc", default="cc")
p.add_argument("--sanitizer", choices=("asan", "tsan", "none"), default="asan")
p.add_argument("--workers", type=int, default=1)
p.add_argument("--detect-leaks", choices=("0", "1"), default="1")
p.add_argument("--timeout", type=int, default=180)
a = p.parse_args()
tree = a.tree.resolve()
if (tree / "scoped-machine").is_dir():
    tree /= "scoped-machine"
if not (tree / "src" / "machine.c").is_file():
    p.error("tree does not contain scoped-machine/src/machine.c")
if a.workers < 1 or a.timeout < 1:
    p.error("workers and timeout must be positive")
here = Path(__file__).resolve().parent
flags = ["-std=c11", "-O1", "-g", "-fno-omit-frame-pointer", "-pthread",
         "-I", str(here), "-I", str(tree / "tests"), "-I", str(tree / "src")]
if a.sanitizer != "none":
    flags += ["-fsanitize=" + ("address,undefined" if a.sanitizer == "asan" else "thread")]
env = dict(os.environ)
env["CUBICAL_WORKERS"] = str(a.workers)
if a.sanitizer == "asan":
    env["ASAN_OPTIONS"] = "detect_leaks=" + a.detect_leaks + ":halt_on_error=1"
    env["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
if a.sanitizer == "tsan":
    env["TSAN_OPTIONS"] = "halt_on_error=1"
results = []
report = {"specification": "uniform reuse v9, sections 74-82",
          "tree": str(tree), "sanitizer": a.sanitizer, "workers": a.workers,
          "detect_leaks": a.detect_leaks if a.sanitizer == "asan" else None,
          "results": results}
exit_code = 0
try:
    with tempfile.TemporaryDirectory(prefix="reuse-acceptance-") as td:
        b = Path(td)
        objects = []
        # Include any new production modules added by the worker.
        for source in sorted((tree / "src").glob("*.c")):
            obj = b / (source.stem + ".o")
            subprocess.run([a.cc, *flags, "-c", str(source), "-o", str(obj)], check=True)
            objects.append(str(obj))
        programs = {
            "boundaries": "accept_sharing_boundaries.c",
            "checker": "accept_check_weakening.c",
            "handles": "accept_shared_work_handle.c",
        }
        for name, source in programs.items():
            subprocess.run([a.cc, *flags, str(here / source), *objects, "-o", str(b / name)], check=True)
        jobs = [("boundaries", mode) for mode in
                ("origin", "alpha", "face", "specialize", "environment", "identity-name", "work")]
        jobs += [("checker", None), ("handles", None)]
        for program, mode in jobs:
            cmd = [str(b / program)] + ([mode] if mode else [])
            try:
                r = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=a.timeout)
                item = {"program": program, "mode": mode, "exit_code": r.returncode,
                        "stdout": r.stdout, "stderr": r.stderr}
            except subprocess.TimeoutExpired as error:
                item = {"program": program, "mode": mode, "exit_code": None,
                        "error": "timeout", "timeout_seconds": a.timeout,
                        "stdout": (error.stdout or b"").decode(errors="replace") if isinstance(error.stdout, bytes) else (error.stdout or ""),
                        "stderr": (error.stderr or b"").decode(errors="replace") if isinstance(error.stderr, bytes) else (error.stderr or "")}
            results.append(item)
            print(json.dumps(item), flush=True)
        if any(item["exit_code"] != 0 for item in results):
            exit_code = 1
except subprocess.CalledProcessError as error:
    report["build_failure"] = {"command": error.cmd, "exit_code": error.returncode}
    exit_code = 1
finally:
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2) + "\n")
raise SystemExit(exit_code)

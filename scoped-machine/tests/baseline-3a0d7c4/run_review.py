#!/usr/bin/env python3
"""Reproduce sharing diagnostics without changing the target checkout."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

p = argparse.ArgumentParser()
p.add_argument("tree", type=Path, help="repository root or scoped-machine directory")
p.add_argument("--output", type=Path, default=Path("sharing-review-results.json"))
p.add_argument("--cc", default="cc")
p.add_argument("--detect-leaks", choices=("0", "1"), default="0")
a = p.parse_args()
tree = a.tree.resolve()
if (tree / "scoped-machine").is_dir():
    tree /= "scoped-machine"
here = Path(__file__).resolve().parent
names = "intern dnf machine interval face term scope template eval lib net match canon check compiler work".split()
flags = ["-std=c11", "-O1", "-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer", "-pthread", "-I", str(tree / "tests")]
env = {**os.environ, "ASAN_OPTIONS": "detect_leaks=" + a.detect_leaks}
results = []
with tempfile.TemporaryDirectory(prefix="sharing-review-") as td:
    b = Path(td)
    objects = {}
    for name in names:
        obj = b / (name + ".o")
        subprocess.run([a.cc, *flags, "-c", str(tree / "src" / (name + ".c")), "-o", str(obj)], check=True)
        objects[name] = obj
    programs = [
        ("boundaries", here / "review_sharing_boundaries.c", list(objects.values())),
        ("checker", here / "review_check_sharing.c", [v for k, v in objects.items() if k != "check"]),
        ("work-suite", tree / "tests" / "test_work.c", list(objects.values())),
    ]
    for name, source, objs in programs:
        subprocess.run([a.cc, *flags, str(source), *map(str, objs), "-o", str(b / name)], check=True)
    jobs = [("boundaries", mode) for mode in ["origin", "alpha", "face", "specialize", "environment", "identity-name", "work"]]
    jobs += [("checker", None), ("work-suite", None)]
    for program, mode in jobs:
        cmd = [str(b / program)] + ([mode] if mode else [])
        r = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=120)
        result = {"program": program, "mode": mode, "exit_code": r.returncode, "stdout": r.stdout, "stderr": r.stderr}
        results.append(result)
        print(r.stdout, end="")
        if r.stderr:
            print(r.stderr, end="")
a.output.write_text(json.dumps({"assessed_commit": "3a0d7c40816ad93e90e42c8f08a94379fbf151dc", "tree": str(tree), "sanitizers": "ASan/UBSan", "detect_leaks": a.detect_leaks, "results": results}, indent=2) + "\n")
raise SystemExit(0 if all(r["exit_code"] == 0 for r in results) else 1)

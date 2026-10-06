#!/usr/bin/env python3
"""Instrument a COPY of HVM4: rule counts and bounded experimental runs.

Reduction rules are unchanged. Timings from this binary include profiling
overhead; use the original binary for performance measurements.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--source', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
source = args.source.read_text()
names = sorted(set(re.findall(r'ITRS_INC\("([^"]+)"\)', source)))
# Partition the existing DUP-SUP counter without changing its reduction.
source = source.replace('ITRS_INC("DUP-SUP");',
    'ITRS_INC(lab == term_ext(sup) ? "DUP-SUP-SAME" : "DUP-SUP-DIFF");')
names = sorted((set(names) - {'DUP-SUP'}) | {'DUP-SUP-SAME', 'DUP-SUP-DIFF'})
instrument = r'''
static const char *SAT_NAMES[] = { @NAMES@ };
static u64 SAT_COUNTS[@COUNT@] = {0};
static u64 SAT_BUDGET = 5000000;
static u64 SAT_HEAP_BUDGET = 32000000;
static void sat_report(void) {
  fprintf(stderr, "SAT_PROFILE {\"interactions\":%llu,\"heap_nodes\":%llu,\"rules\":{",
    (unsigned long long)ITRS, (unsigned long long)(HEAP_NEXT - 1));
  for (int i = 0; i < @COUNT@; ++i) {
    fprintf(stderr, "%s\"%s\":%llu", i ? "," : "", SAT_NAMES[i], (unsigned long long)SAT_COUNTS[i]);
  }
  fprintf(stderr, "}}\n");
}
static void sat_init(void) {
  char *limit = getenv("SAT_MAX_ITRS");
  char *heap = getenv("SAT_MAX_HEAP");
  if (limit) SAT_BUDGET = strtoull(limit, NULL, 10);
  if (heap) SAT_HEAP_BUDGET = strtoull(heap, NULL, 10);
  atexit(sat_report);
}
static void sat_tick(const char *name) {
  if (ITRS >= SAT_BUDGET) {
    fprintf(stderr, "SAT_LIMIT interactions\n");
    exit(124);
  }
  for (int i = 0; i < @COUNT@; ++i) {
    if (strcmp(name, SAT_NAMES[i]) == 0) { ++SAT_COUNTS[i]; return; }
  }
  fprintf(stderr, "unknown rule: %s\n", name);
  exit(125);
}
'''.replace('@NAMES@', ','.join(json.dumps(n) for n in names)).replace('@COUNT@', str(len(names)))
assert source.count('static u64 ITRS = 0;') == 1
source = source.replace('static u64 ITRS = 0;', 'static u64 ITRS = 0;\n'+instrument)
assert source.count('      ITRS++; \\') == 1
source = source.replace('      ITRS++; \\', '      sat_tick(name); \\\n      ITRS++; \\')
source = source.replace('int main(int argc, char **argv) {',
                        'int main(int argc, char **argv) {\n  sat_init();')
source = source.replace('  u64 next = at + size;', '''  u64 next = at + size;
  if (next > SAT_HEAP_BUDGET) {
    fprintf(stderr, "SAT_LIMIT heap\\n");
    exit(124);
  }''')
args.output.parent.mkdir(parents=True, exist_ok=True)
cfile = args.output.with_suffix('.c')
cfile.write_text(source)
subprocess.run(['clang', '-O2', '-o', str(args.output), str(cfile)], check=True)
(ROOT/'profile-build.json').write_text(json.dumps(dict(
    original_source=str(args.source.resolve()),
    original_sha256=hashlib.sha256(args.source.read_bytes()).hexdigest(),
    instrumented_source=str(cfile.resolve()),
    instrumented_sha256=hashlib.sha256(cfile.read_bytes()).hexdigest(),
    binary=str(args.output.resolve()),
    binary_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest(),
    rules=names), indent=2)+'\n')
print(args.output)

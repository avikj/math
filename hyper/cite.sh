#!/usr/bin/env bash
# cite.sh — every identifier MAP.md, NOTES.md and RUNTIME.md name must be on the line it cites.
# A citation is `path:LINE` `ident`, or `:LINE` `ident` continuing the last path. Exit 1 on any miss.
set -u; cd "$(dirname "$0")/.."
python3 - <<'PY'
import re, sys, os
pat = re.compile(r"`([^`\n]*\.agda)(?::(\d+))?`(?:\s*`([^`\n]+)`)?|`:(\d+)`\s*`([^`\n]+)`")
bad = 0; n = 0
for doc in ('hyper/MAP.md', 'hyper/NOTES.md', 'hyper/RUNTIME.md'):
  s = open(doc, encoding='utf-8').read(); path = None
  for m in pat.finditer(s):
    if m.group(1):
      path = m.group(1); n += 1
      if not os.path.exists(path): print(f"{doc}: MISSING FILE {path}"); bad += 1; continue
      if m.group(2) is None: continue
      line, ident = int(m.group(2)), m.group(3)
      if ident is None: print(f"{doc}: NO IDENT at {path}:{line}"); bad += 1; continue
    else:
      line, ident = int(m.group(4)), m.group(5); n += 1
      if path is None or not os.path.exists(path): print(f"{doc}: NO FILE for :{line} {ident}"); bad += 1; continue
    lines = open(path, encoding='utf-8').read().split('\n')
    if line > len(lines) or ident not in lines[line-1]: print(f"{doc}: NOT AT {path}:{line}: {ident}"); bad += 1
print(f"citations={n} bad={bad}")
sys.exit(1 if bad else 0)
PY

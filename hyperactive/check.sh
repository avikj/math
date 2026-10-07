#!/bin/sh
# Typecheck the hyperactive modules. Run from THIS directory (the agda-lib
# root); the include path is relative to it.
cd "$(dirname "$0")" || exit 1
AGDA=agda; command -v agda >/dev/null 2>&1 || AGDA="$HOME/.local/bin/agda"
rc=0
for f in Diamond DecTable ListAddr Spawn StatusMachine; do
  if LC_ALL=C.UTF-8 AGDA_DIR="$HOME/.agda-pin" "$AGDA" --safe "$f.agda" >/tmp/hyper.$f.log 2>&1; then
    echo "$f: OK"
  else
    echo "$f: FAIL"; tail -8 /tmp/hyper.$f.log; rc=1
  fi
done
exit $rc

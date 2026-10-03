#!/bin/bash
# Builds the cubical Bend/HVM fork from scratch and runs its suite.
#
# Clones DKormann/Bend2 at the pinned commit, applies cubical-paths.patch
# and glue-emit.patch,
# clones HVM3 as a local package with the one include fix it needs, builds
# with GHC 9.12.2, and runs suite.sh (112 .bend files; the registered
# must-fail probes must each be rejected).
#
# Needs: git, and GHC 9.12.2 + cabal on PATH. The language edition HVM3
# uses (GHC2024) requires GHC 9.10 or newer; 9.4 cannot build this.
#   ghcup install ghc 9.12.2 && ghcup set ghc 9.12.2
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:-/tmp/bend-interactive-cubical}
UPSTREAM=f026483
HVM3_DIR="$WORK/HVM3"

export LC_ALL=C.utf8 LANG=C.utf8   # HVM3 embeds .c files via Template Haskell;
                                   # a non-UTF-8 locale makes the build fail and
                                   # makes the built binary abort silently

# HVM3 asks for the GHC2024 language edition, which GHC 9.8 and older do not
# know. Cabal reports that as "rejecting: HVM-0.1.0.0 (conflict: requires
# unknown language GHC2024)", which reads like a dependency problem and is
# not one. If the GHC on PATH is too old, look for a new enough one under
# ghcup before giving up.
ghc_ok() { [ -x "$1" ] && case "$("$1" --numeric-version 2>/dev/null)" in
  9.1[0-9]*|9.[2-9][0-9]*|[1-9][0-9]*) return 0 ;; *) return 1 ;; esac ; }
if ! ghc_ok "$(command -v ghc || true)"; then
  for cand in "$HOME"/.ghcup/bin/ghc-9.1[0-9]* "$HOME"/.ghcup/bin/ghc; do
    if ghc_ok "$cand"; then
      PATH="$(dirname "$cand"):$PATH"; export PATH
      echo "using GHC $("$cand" --numeric-version) from $(dirname "$cand")"
      break
    fi
  done
fi
if ! ghc_ok "$(command -v ghc || true)"; then
  echo "need GHC 9.10 or newer (HVM3 uses the GHC2024 language edition);" >&2
  echo "found $(ghc --numeric-version 2>/dev/null || echo none)." >&2
  echo "  ghcup install ghc 9.12.2 && ghcup set ghc 9.12.2" >&2
  exit 1
fi

mkdir -p "$WORK"

# HVM3 must be a LOCAL package: its Runtime.c omits two includes that the
# linker needs, and editing cabal's cached source-repository-package copy
# does not rebuild the store artifact.
if [ ! -d "$HVM3_DIR/.git" ]; then
  git clone https://github.com/HigherOrderCO/HVM3 "$HVM3_DIR"
fi
if ! grep -q 'reduce/ref.c' "$HVM3_DIR/src/HVM/Runtime.c"; then
  sed -i '/#include "runtime\/reduce\/dup_una.c"/a #include "runtime/reduce/ref.c"\n#include "runtime/reduce/ref_sup.c"' \
    "$HVM3_DIR/src/HVM/Runtime.c"
  echo "patched HVM3 Runtime.c (adds reduce/ref.c and reduce/ref_sup.c)"
fi

if [ ! -d "$WORK/Bend2/.git" ]; then
  git clone https://github.com/DKormann/Bend2 "$WORK/Bend2"
fi
cd "$WORK/Bend2"
git checkout -q $UPSTREAM
git checkout -q -- .
git apply "$HERE/cubical-paths.patch"
# glue-emit.patch is kept separate on purpose: it is the change that lets a
# univalence path written the CCHM way (a Glue line) reach the runtime, and
# a reviewer should be able to read it without reading 7,000 lines first.
git apply "$HERE/glue-emit.patch"
# keep upstream's hs-highlight source-repository (HVM3 needs >=1.0.5, which
# is not on Hackage); replace only the HVM3 entry with the patched local copy
cat > cabal.project <<EOF
packages: . $HVM3_DIR

package *
  optimization: 2

source-repository-package
  type: git
  location: https://github.com/HigherOrderCO/hs-highlight
EOF

echo "building (first build compiles HVM3 too; this takes a while)"
cabal build 2>&1 | tail -5
BEND=$(cabal list-bin bend)
echo "bend: $BEND"

echo
echo "suite (every .bend checks clean, except the registered must-fail probes,"
echo "which must each contain a rejected definition)."
echo "Expected: bad=0 (the two probes written in the bend2-cubical fork's"
echo "vocabulary, hit_test and setquotient_test, live in that lane only)."
"$HERE/suite.sh" "$BEND"

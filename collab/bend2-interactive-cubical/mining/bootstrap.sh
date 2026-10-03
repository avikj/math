#!/usr/bin/env bash
# Build in a NEW dedicated directory; never modify the executor's existing build.
# Needs network, GHC 9.12.2, cabal >=3.14, C toolchain, development headers.
set -Eeuo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
[[ $# == 1 ]] || { echo "Usage: bash $0 NEW_BUILD_DIRECTORY" >&2; exit 2; }
WORK=$(realpath -m -- "$1")
[[ ! -e "$WORK" ]] || { echo 'Build directory already exists; use a new path or use your existing binaries directly.' >&2; exit 2; }
for tool in git ghc cabal node; do command -v "$tool" >/dev/null; done
[[ $(ghc --numeric-version) == 9.12.2 ]] || { echo 'This compiler is pinned to GHC 9.12.2. Install that toolchain before bootstrap.' >&2; exit 2; }
CC=${CC:-clang}; command -v "$CC" >/dev/null
mkdir -p "$WORK"
trap 'rc=$?; echo "BUILD FAILED (exit $rc); checkout/logs remain at $WORK" >&2; exit "$rc"' ERR
clone_pin() {
  git clone --no-checkout "$1" "$2"
  git -C "$2" checkout --detach "$3"
}
clone_pin https://github.com/DKormann/Bend2.git "$WORK/Bend2" f026483
clone_pin https://github.com/HigherOrderCO/HVM3.git "$WORK/HVM3" fba2e9c82faf6e2f019c9ecea94c32f19a8b7820
clone_pin https://github.com/HigherOrderCO/HVM4.git "$WORK/HVM4" 6defdfc7dae2a3cca5dd6e74ed0612385b5646a8
git -C "$WORK/Bend2" apply --check "$HERE/../cubical-paths.patch"
git -C "$WORK/Bend2" apply "$HERE/../cubical-paths.patch"
# The pinned HVM3 package omits two FFI definitions from its C aggregator.
node --input-type=module - "$WORK/HVM3" <<'JS'
import fs from 'node:fs'; import path from 'node:path';
const root=process.argv[2], file=path.join(root,'src/HVM/Runtime.c');
let s=fs.readFileSync(file,'utf8');
for(const name of ['ref.c','ref_sup.c']) {
  const inc=`#include "runtime/reduce/${name}"`;
  if(!fs.existsSync(path.join(root,'src/HVM/runtime/reduce',name))) throw Error('missing pinned '+name);
  if(!s.includes(inc)) s+='\n'+inc+'\n';
}
fs.writeFileSync(file,s);
JS
if [[ -f "$HERE/../hvm3-gcc15.patch" ]]; then
  git -C "$WORK/HVM3" apply --check "$HERE/../hvm3-gcc15.patch"
  git -C "$WORK/HVM3" apply "$HERE/../hvm3-gcc15.patch"
fi
cat > "$WORK/Bend2/cabal.project" <<'PROJECT'
packages: . ../HVM3

package *
  optimization: 2

-- HVM3 requires hs-highlight >=1.0.5; that release is supplied by HOC's
-- source repository and is not published on Hackage.
source-repository-package
  type: git
  location: https://github.com/HigherOrderCO/hs-highlight

package zlib
  flags: +bundled-c-zlib
PROJECT
(cd "$WORK/Bend2" && cabal update && cabal build exe:bend 2>&1 | tee "$WORK/bend-build.log")
BEND=$(cd "$WORK/Bend2" && cabal list-bin exe:bend)
(cd "$WORK/HVM4" && "$CC" -O2 -o src/hvm src/hvm.c 2>&1 | tee "$WORK/hvm-build.log")
HVM="$WORK/HVM4/src/hvm"
printf 'export BEND=%q\nexport HVM=%q\n' "$BEND" "$HVM" > "$WORK/env.sh"
{
  ghc --version; cabal --version; "$CC" --version
  for name in Bend2 HVM3 HVM4; do printf '%s=' "$name"; git -C "$WORK/$name" rev-parse HEAD; done
  sha256sum "$HERE/../cubical-paths.patch" "$BEND" "$HVM"
} > "$WORK/build-identity.txt"
printf 'Built. Load executables with: source %q\nThen invoke mining/run.sh; native gates remain mandatory.\n' "$WORK/env.sh"

#!/usr/bin/env bash
# Direct proof checking avoids Lake startup contention during parallel development.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -x .toolchain/lean-4.24.0-linux/bin/lean ]]; then
 export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
fi
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for d in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do
 export LEAN_PATH="$LEAN_PATH:$d"
done
exec lean "$@"

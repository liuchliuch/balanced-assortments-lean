#!/usr/bin/env bash
# --final also checks an existing frozen inventory. Never silently create one.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:---preliminary}"
[[ "$mode" == --preliminary || "$mode" == --final ]] || { echo 'usage: build.sh [--preliminary|--final]' >&2; exit 2; }
mkdir -p logs
if [[ -x .toolchain/lean-4.24.0-linux/bin/lake ]]; then
 export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
fi
python3 scripts/check_project.py --release | tee logs/source-preflight.json
sha256sum -c paper/SHA256SUMS | tee logs/original-validation.log
python3 scripts/snapshot.py --pins-only | tee logs/dependency-pin-validation.json
lake build BalancedAssortments 2>&1 | tee logs/all-module-build.log
lake env lean scripts/AxiomAudit.lean 2>&1 | tee logs/transitive-axiom-audit.log
lake env lean --trust=0 scripts/AxiomAudit.lean 2>&1 | tee logs/trust-zero-all-imports.log
python3 scripts/regressions.py --out logs/regressions
if [[ "$mode" == --final ]]; then
 python3 scripts/snapshot.py --verify | tee logs/frozen-inventory-validation.json
fi
printf 'PASS: %s mechanical checks; source-semantic acceptance remains separate.\n' "$mode"

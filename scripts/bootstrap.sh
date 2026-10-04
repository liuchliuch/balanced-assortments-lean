#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
elan toolchain install leanprover/lean4:v4.24.0
lake exe cache get
lake build

#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
stamp="${1:-$(date -u +%Y%m%dT%H%M%SZ)}"
[[ "$stamp" =~ ^[A-Za-z0-9_-]+$ ]] || { echo 'Invalid checkpoint stamp' >&2; exit 2; }
flag="${2:-}"
[[ -z "$flag" || "$flag" == --final ]] || { echo 'usage: checkpoint.sh [stamp] [--final]' >&2; exit 2; }
out="$(dirname "$root")/balanced-assortments-source-${stamp}.tar.gz"
args=(--out "$out")
[[ -z "$flag" ]] || args+=(--final)
python3 "$root/scripts/pack_source.py" "${args[@]}"

#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "Removing Codex-local workflow notes from artifact tree..."
rm -f skills/README.md

echo "Removing Rocq build products and local solver caches..."
find . \
  -path './.git' -prune -o \
  \( -name '*.vo' \
     -o -name '*.vos' \
     -o -name '*.vok' \
     -o -name '*.glob' \
     -o -name '.*.aux' \
     -o -name '.Makefile.d' \
     -o -name '*.v.timing' \
     -o -name '*.timing.diff' \
     -o -name '*.v.before-timing' \
     -o -name '*.v.after-timing' \
     -o -name 'time-of-build*.log' \
     -o -name '.lia.cache' \
     -o -name '.nia.cache' \
     -o -name '.nlia.cache' \
     -o -name '.nra.cache' \
     -o -name '.csdp.cache' \
     -o -name 'lia.cache' \
     -o -name 'nia.cache' \
     -o -name 'nlia.cache' \
     -o -name 'nra.cache' \
     -o -name 'csdp.cache' \
  \) -type f -delete

echo "Artifact cleanup complete."

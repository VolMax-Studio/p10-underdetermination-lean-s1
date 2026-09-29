#!/usr/bin/env bash
# Regenerate SHA256SUMS over every tracked artifact (all files except SHA256SUMS itself and build/VCS dirs).
set -euo pipefail
cd "$(dirname "$0")/.."
find . -type f \
  -not -path './.git/*' -not -path './.lake/*' -not -path './.venv/*' -not -path './.toolchain/*' \
  -not -path '*/__pycache__/*' -not -name SHA256SUMS -not -path './.fakebin/*' \
  | sed 's|^\./||' | LC_ALL=C sort | xargs sha256sum > SHA256SUMS
wc -l SHA256SUMS

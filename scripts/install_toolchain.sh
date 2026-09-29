#!/usr/bin/env bash
# Install the PINNED Lean toolchain artifact into ./.toolchain (no elan, no GitHub, no `lake update`).
#
# Artifact: conda-forge package lean4-4.33.0-h6c1889d_0.conda (Lean 4.33.0, commit 5da8a13c...).
# The package SHA-256 below is pinned; the extracted `lean` executable digest is pinned again in
# manifest/VerifierManifestS1.json and re-checked by scripts/p10tool.py at verification time.
# Needs: curl, unzip, python3 with `zstandard` (see requirements.lock).
set -euo pipefail
cd "$(dirname "$0")/.."

PKG_URL="https://conda.anaconda.org/conda-forge/linux-64/lean4-4.33.0-h6c1889d_0.conda"
PKG_SHA256="cb623d648243b9668c8753fb2efd61a00163cf92eb133ccdfd51bc48c2023f29"
DEST="$PWD/.toolchain/lean4-4.33.0"

if [[ -x "$DEST/bin/lean" ]]; then
  echo "toolchain already installed: $DEST"
else
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  curl -fsSL --retry 3 -o "$tmp/pkg.conda" "$PKG_URL"
  actual="$(sha256sum "$tmp/pkg.conda" | cut -d' ' -f1)"
  if [[ "$actual" != "$PKG_SHA256" ]]; then
    echo "error: toolchain package digest mismatch: $actual" >&2
    exit 1
  fi
  (cd "$tmp" && unzip -q pkg.conda)
  python3 - "$tmp" "$DEST" <<'PY'
import glob, sys, tarfile, zstandard
tmp, dest = sys.argv[1], sys.argv[2]
files = glob.glob(f"{tmp}/pkg-lean4-*.tar.zst")
assert len(files) == 1, files
with open(files[0], "rb") as fh:
    r = zstandard.ZstdDecompressor().stream_reader(fh)
    with tarfile.open(fileobj=r, mode="r|") as t:
        t.extractall(dest, filter="data")
PY
fi
echo "export PATH=\"$DEST/bin:\$PATH\""

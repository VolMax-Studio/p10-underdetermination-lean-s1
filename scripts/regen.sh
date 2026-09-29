#!/usr/bin/env bash
# Regenerate every derived artifact in the correct order (maintainer step; NOT part of verification):
#   vectors -> clean build -> verifier manifest -> statement + COSE (TEST key) -> pin -> SHA256SUMS
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/gen_vectors.py >/dev/null
python3 scripts/gen_binding.py
rm -rf .lake/build
lake build
python3 scripts/p10tool.py manifest
python3 scripts/p10tool.py statement vectors/p1.instance.json \
  --module P10.Certs.P1 --theorem P10.Certs.P1.cert --cert-file P10/Certs/P1.lean --out vectors/out/p1
sha256sum manifest/VerifierManifestS1.json | cut -d' ' -f1 > profile/VERIFIER_MANIFEST_PIN.txt
python3 scripts/gen_testvectors_md.py
scripts/update_sums.sh

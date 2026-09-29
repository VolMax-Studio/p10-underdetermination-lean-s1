#!/usr/bin/env bash
# Canonical fail-closed verification of the whole S1 reference chain.
#
#   ./scripts/verify.sh                 full run (includes the mutation suite)
#   P10_SKIP_MUTATIONS=1 ./scripts/verify.sh   everything except the mutation suite (faster; NOT canonical)
#
# Requirements on PATH: the pinned `lean`/`lake` (see scripts/install_toolchain.sh), python3 with the
# modules pinned in requirements.lock, sha256sum, grep. Never runs `lake update`, never touches the network.
# Any failing step aborts with a non-zero exit code; there is no "warn and continue".
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"

step() { printf '\n==> %s\n' "$*"; }
die()  { printf 'VERIFY FAIL: %s\n' "$*" >&2; exit 1; }

require() { command -v "$1" >/dev/null 2>&1 || die "required tool missing: $1"; }
for t in lean lake leanchecker python3 sha256sum grep sort find; do require "$t"; done

step "external verifier-manifest pin (root of trust)"
# The pin is the only anchor for the verifier tree: a tree cannot vouch for itself. It MUST come from outside
# the tree (e.g. the profile InstanceCommitment / an out-of-band publication of the manifest digest).
#   canonical:            P10_EXPECT_MANIFEST_SHA256=<sha256 obtained out of band> ./scripts/verify.sh
#   self-consistency run: P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh   (reads profile/VERIFIER_MANIFEST_PIN.txt)
if [[ -n "${P10_EXPECT_MANIFEST_SHA256:-}" ]]; then
  pin="$P10_EXPECT_MANIFEST_SHA256"
  echo "  using the externally supplied pin"
elif [[ "${P10_ALLOW_INTREE_PIN:-0}" == "1" ]]; then
  pin="$(tr -d '\n' < profile/VERIFIER_MANIFEST_PIN.txt)"
  echo "  WARNING: in-tree pin — this run proves self-consistency only; it is NOT an external trust anchor"
else
  die "external pin required: set P10_EXPECT_MANIFEST_SHA256=<sha256 of manifest/VerifierManifestS1.json obtained out of band> (or P10_ALLOW_INTREE_PIN=1 for a self-consistency run)"
fi
[[ "$pin" =~ ^[0-9a-f]{64}$ ]] || die "malformed manifest pin"

step "python environment: every package pinned in requirements.lock must match exactly"
python3 scripts/check_env.py requirements.lock || die "python environment differs from requirements.lock"

check_sums() {
  # verifies every listed file AND that no unlisted file exists (source tree contamination)
  sha256sum --strict --check --quiet SHA256SUMS || die "SHA256SUMS mismatch ($1)"
  local listed actual
  listed="$(cut -c67- SHA256SUMS | LC_ALL=C sort)"
  actual="$(find . -type f -not -path './.git/*' -not -path './.lake/*' -not -path './.venv/*' \
            -not -path './.toolchain/*' -not -path '*/__pycache__/*' -not -name SHA256SUMS \
            | sed 's|^\./||' | LC_ALL=C sort)"
  [[ "$listed" == "$actual" ]] || die "source tree contamination ($1): file set differs from SHA256SUMS:
$(diff <(printf '%s\n' "$listed") <(printf '%s\n' "$actual") || true)"
  if [[ -d .git ]] && command -v git >/dev/null 2>&1; then
    local dirty
    dirty="$(git status --porcelain --untracked-files=all 2>/dev/null || true)"
    if [[ -n "$dirty" ]]; then
      echo "  note ($1): git working tree differs from HEAD (tracked-file content is still pinned by SHA256SUMS):"
      printf '%s\n' "$dirty" | head -20
    fi
  fi
}

step "SHA256SUMS (pre-build) + tree contamination check"
check_sums pre-build

step "normative profile snapshot digest"
want_profile="b92c0d689b9f16f2184ba2addb8653ed881595cc3a0117c62cadadf5c6dc6558"
got_profile="$(sha256sum profile/normative/P10_Underdetermination_Profile_v0.1.1.md | cut -d' ' -f1)"
[[ "$got_profile" == "$want_profile" ]] || die "profile snapshot digest $got_profile != $want_profile"
echo "  $got_profile"

step "toolchain identity"
lean --version
[[ "$(cat lean-toolchain)" == "leanprover/lean4:v4.33.0" ]] || die "lean-toolchain differs from the pinned identifier"
lean --version | grep -q "version 4.33.0" || die "lean is not 4.33.0"
[[ ! -e lake-manifest.json ]] || python3 -c "import json;m=json.load(open('lake-manifest.json'));assert m['packages']==[],'lake-manifest has packages'" \
  || die "lake-manifest.json must list no dependencies (frozen, no Mathlib)"

step "Lean source policy (escape hatches, metaprogramming allowlist, strict certificate modules)"
python3 scripts/lint_lean.py P10 P10.lean tests || die "Lean source policy violation"


step "clean build (no lake update; warnings are errors)"
rm -rf .lake/build
lake build --wfail
lake build --wfail >/dev/null   # idempotence

step "kernel replay: leanchecker over every module of the P10 library (not just #print axioms)"
lake env leanchecker P10 || die "leanchecker replay failed"

step "axiom audit (#print axioms for every exported theorem)"
audit_out="$(lake env lean P10/AxiomAudit.lean)"
printf '%s\n' "$audit_out" | tail -5
n_expected="$(grep -c '^#print axioms ' P10/AxiomAudit.lean)"
n_ok="$(printf '%s\n' "$audit_out" | grep -c 'does not depend on any axioms$' || true)"
n_lines="$(printf '%s\n' "$audit_out" | grep -c . || true)"
[[ "$n_ok" == "$n_expected" && "$n_lines" == "$n_expected" ]] \
  || die "axiom audit: expected $n_expected axiom-free lines, got $n_ok of $n_lines"
echo "  axiom audit: $n_ok/$n_expected declarations axiom-free"

step "Lean test suite (positive, must-fail, sha256 differential)"
python3 scripts/run_tests.py

step "third-party verification of the S1 test vector (checker-owned proposition, TEST signature)"
python3 scripts/p10tool.py verify vectors/out/p1.cose --manifest-digest "$pin" | tail -4
python3 scripts/cose_crosscheck.py vectors/out/p1.cose

if [[ "${P10_SKIP_MUTATIONS:-0}" != "1" ]]; then
  step "negative mutation suite"
  python3 scripts/mutation_suite.py
else
  echo; echo "WARNING: mutation suite skipped (P10_SKIP_MUTATIONS=1); this is not the canonical run"
fi

step "SHA256SUMS (post-build) + tree contamination check"
check_sums post-build

step "artifact digests"
sha256sum SHA256SUMS manifest/VerifierManifestS1.json vectors/out/p1.statement.json vectors/out/p1.cose \
  vectors/p1.instance.json profile/normative/P10_Underdetermination_Profile_v0.1.1.md

echo
echo "VERIFY PASS"

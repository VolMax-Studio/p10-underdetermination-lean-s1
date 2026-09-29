# p10-underdetermination-lean-s1

**Status: DRAFT. Self-reviewed. Not independently validated. Not ratified. No release, no tag.**

Executable reference chain for the ratified **P10 Underdetermination Profile** (v0.1.1, normative source:
`VolMax-Studio/p10-underdetermination-profile` @ `3c20df23…`, file SHA-256
`b92c0d689b9f16f2184ba2addb8653ed881595cc3a0117c62cadadf5c6dc6558`, see `profile/SOURCE.md`).
This repository does **not** modify the profile; it is a checkable implementation of its formal core.

```
ratified profile semantics (§2.1, §2.2)
  → Lean formalization                       P10/Core.lean, P10/Certificate.lean
  → witness-carrying certificate             P10.UnderdeterminationCertificate
  → exact input/proposition binding          P10/Wire.lean (decoder), P10/Sha256.lean, P10/Bound.lean
  → machine-readable statement               in-toto Statement v1, experimental predicate
  → SCITT-shaped Signed Statement            COSE_Sign1, TEST key (registration NOT demonstrated)
  → third-party reproducible verifier        scripts/p10tool.py verify
  → negative mutation suite                  scripts/mutation_suite.py (mutation cases + Python↔Lean decoder differential + Python-pin, lint and pin-policy regressions)
  → CI / verify.sh / audits / hashes         scripts/verify.sh, .github/workflows/verify.yml
```

## Scope

S1 answers one question: *can the ratified formal definitions be implemented faithfully in Lean, and a concrete
witness certificate be kernel-checked* — and then goes further: the proposition proved by the kernel is
**computed from the committed bytes** and is the profile's exact `CertificateTargetV0` for the evidence, claim and
witnesses NAMED in those bytes (`P10.Bound (filebytes% "<file>") (hex% "<sha256>")`), and the verifier compiles that
target itself, in a separate process, before the certificate is loaded.

## Exact claim

For the committed S1 instance `vectors/p1.instance.json` (SHA-256 `62353069…e824`), the Lean kernel accepts
`P10.Certs.P1.cert : P10.Bound bytes digest`, i.e. (a) the bytes have that SHA-256 (kernel-computed value of an
implementation that is vector- and `hashlib`-tested, not proved correct), (b) they decode canonically (strict decoder,
`encode (decode b) = b`) to an instance, and (c) for THAT instance's evidence `e`, claim `c` and NAMED witnesses `w₀`, `w₁`
the profile's `CertificateTargetV0(π,e,c,w₀,w₁)` holds in the frozen S1 toy profile: `e ∈ Eπ`, `w₀,w₁ ∈ Wπ`, both
`Compatibleπ` with `e`, and `Evalπ(c,w₀) ≠ Evalπ(c,w₁)`. (Draft PR #1 asserted only the weaker `Underdeterminedπ(e,c)`,
"some pair exists"; gate finding F1 — fixed in PR #2.) All audited declarations depend on **no axioms**.

## Non-claims

* Not shown: that `Wπ` covers the real world; that `Compatibleπ` models reality; that any evidence source is truthful;
  that any runtime used the profile in its decision path; that failure to find witnesses means determinacy (the
  implementation proves the opposite schema: `no_certificate_does_not_imply_determinate`).
* The S1 profile is a five-world **toy fixture**; no profile-adequacy review has been done (profile §7.2).
* **Not a conforming P10 receipt.** No `InstanceCommitment`, `EvidenceClosure`, `CoverageProof`, `FullPrefixReplay`,
  registration-order verification or SCITT Receipt exists here (profile §§2.3–2.6 unimplemented).
* **SCITT registration is NOT DEMONSTRATED.** A SCITT receipt would prove registration only, never the epistemic
  content; P10/Lean checks underdetermination, a Transparency Service would merely register the Signed Statement.
* The COSE signature uses a public deterministic **test key** with no authority — never a human/issuer key.
* Wire codec is a strict *subset* of JCS; §2.7 conformance for general worlds is not demonstrated.
* "Third-party reproducible verification" is the claim; **"independently validated semantics" is not** — no outside
  party has reviewed the profile→Lean mapping (`profile/IMPLEMENTATION_BINDING.md`) or the checker.
* Novelty of the same-evidence countermodel criterion is not claimed (`RELATED_WORK.md`).

## Normative vs implementation boundary

The profile is the only normative source. `profile/IMPLEMENTATION_BINDING.md` maps every implemented definition to
its profile section, Lean symbol, source file and digest, and lists representation choices, deviations and what is
not implemented. A disagreement between Lean and the profile is a bug in this repo.

## TCB / threat boundary (details: `THREAT_MODEL.md`)

Kernel-checked: definitions, theorems, decoder, canonical round trip, SHA-256 evaluation, certificate. Trusted: Lean
kernel and the exact toolchain (`lean`, `lake`, `leanchecker`, `libleanshared.so`, all digest-pinned); the
elaboration-time byte elaborators in `P10/Bytes.lean` (the only metaprogram allowed; enforced by lint); `scripts/p10tool.py`
(file hashing of the profile/sources, JCS of the statement, COSE verification, orchestration); the SHA-256 in
`P10/Sha256.lean` is checked against FIPS vectors in the kernel and against `hashlib`, not proved correct.

## Positioning (Sergeev §3/§9, Wadkins)

P10 operationalizes the same-evidence support test as an explicit witness-carrying, machine-checkable artifact under
committed executable profile semantics, with exact profile/evidence/witness/proof/verifier bindings suitable for
transparent registration. P10 does not claim priority over the logical criterion. Sergeev's *Claim Boundaries* -01
(§3 same-evidence test, §9 verification route) was **not accessible** in the build environment; it is described in
`RELATED_WORK.md` only as characterized by the requester. Wadkins' decision-time governance is a different property
from verifier-time recomputation (profile §5, §6); nothing here establishes decision-time binding.

## Reproduce

```sh
# Ubuntu 24.04-like host: apt-get install -y curl unzip python3-venv libgmp10 libuv1t64
python3 -m venv .venv && .venv/bin/pip install -r requirements.lock
export PATH="$PWD/.venv/bin:$PATH"
eval "$(scripts/install_toolchain.sh)"       # pinned conda-forge Lean 4.33.0, package SHA-256 checked
P10_EXPECT_MANIFEST_SHA256=<manifest digest obtained OUT OF BAND> ./scripts/verify.sh   # canonical, fail-closed
```

**The verifier-manifest pin is the only root of trust and must come from outside the tree.** Without
`P10_EXPECT_MANIFEST_SHA256` (or `--manifest-digest` for `p10tool.py verify`) verification HALTs with no verdict. A tree cannot
vouch for itself: an adversary who controls the whole tree can rewrite the manifest, the in-tree pin file, the statement
and re-sign with the public TEST key, and the result is self-consistent. `P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh` reads
`profile/VERIFIER_MANIFEST_PIN.txt` and prints a warning: it proves self-consistency only. Anchoring the pin externally
(profile `InstanceCommitment`, registration) is S2/S3 work and is NOT demonstrated here.
`P10_SKIP_MUTATIONS=1` skips the mutation suite (faster, not canonical).
`verify.sh` checks that EVERY package pinned in `requirements.lock` is installed at exactly the pinned version
(`scripts/check_env.py`, no exemptions; regression-tested in the mutation suite). It never runs `lake update` and never uses the network. It also: checks `SHA256SUMS` and the exact file set before
and after the build, checks the profile digest, forbids `sorry`/`admit`/`native_decide`/`axiom`/`unsafe`/… in Lean
sources (comment-aware lint), clean-builds with warnings as errors, audits `#print axioms` for every exported theorem,
replays every module through the kernel with `leanchecker`, runs positive/must-fail/differential tests, verifies the
signed test vector with the third-party verifier (checker-owned target precompiled in a separate process, kernel replay,
exact-type check of the checked theorem), runs the mutation suite, and prints artifact digests.

### Expected PASS output (abridged)

```
axiom audit: 54/54 declarations axiom-free
run_tests: 23 passed, 0 failed
VERDICT: PASS
mutation suite: all cases as expected (see script output for the count)
VERIFY PASS
```

## Layout

| Path | Role |
|---|---|
| `P10/Core.lean`, `Certificate.lean` | profile definitions; certificate; theorems A–E |
| `P10/Fixtures.lean` | S1 toy profile; P1 and N1–N4, M3 fixtures |
| `P10/Wire.lean`, `Bytes.lean`, `Sha256.lean`, `Bound.lean` | decoder/encoder, byte elaborators, SHA-256, digest-bound statement |
| `P10/Certs/P1.lean`, `P10/AxiomAudit.lean` | the certificate; the axiom audit |
| `tests/`, `tests/must_fail/` | kernel-checked reject theorems; files that MUST NOT compile |
| `vectors/` | committed instance bytes, negative vectors, signed statement (`vectors/out/`) |
| `manifest/VerifierManifestS1.json` | toolchain/source/olean/policy digests (canonical JSON) |
| `profile/` | normative snapshot, `IMPLEMENTATION_BINDING.md`, axiom policy, pins |
| `scripts/` | verifier, mutation suite, tests, lint, `CheckModule.lean` (olean type check), toolchain installer, regeneration |
| `THREAT_MODEL.md`, `TEST_VECTORS.md`, `RELATED_WORK.md`, `RELEASE_CHECKLIST.md` | documentation |

## Measured feasibility (this environment: 4 vCPU, 15 GB)

See `TEST_VECTORS.md` §Benchmarks. In short: kernel `decide` handles the strict decoder and a 4-block SHA-256 in
seconds; no `native_decide` was needed.

## Known limitations

Toy profile; wire codec subset; per-vector (not universal) canonical-form *uniqueness on the accept side* (universal
`decode ∘ encode = id` is proved); SHA-256 not proved correct in Lean; profile-digest and source-digest bindings are
external (hashing script in TCB); Lean 4.33.0 rather than the profile kernel's 4.34.0; no independent review. CI actions are pinned to the commit SHAs that the `v4` tags resolved to in CI run #2
(`actions/checkout` 11d5960a…, `actions/upload-artifact` ea165f8d…; read from that run's log, not re-checked against the
action repositories).

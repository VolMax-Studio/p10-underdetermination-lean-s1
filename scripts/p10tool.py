#!/usr/bin/env python3
"""p10tool — S1 statement builder and third-party-reproducible verifier.

Trust boundary (see THREAT_MODEL.md): this script is part of the TCB for everything
that Lean does not formalize: SHA-256 hashing of files, JCS canonicalization of the
statement, COSE_Sign1 signature verification, and orchestration of the Lean check.
It has NO epistemic authority: the only thing that establishes underdetermination is
the Lean kernel accepting the checker-owned proposition `P10.Bound <bytes> <sha256>`.

Verdicts (exit codes):  PASS = 0   REJECT = 1   HALT = 2 (required artifact unavailable).
Everything fails closed: any unexpected condition is REJECT or HALT, never PASS.

Subcommands
  manifest                  write manifest/VerifierManifestS1.json (canonical JSON)
  statement <vector>        build statement + COSE_Sign1 (TEST KEY) into vectors/out/
  verify <cose> [--manifest-digest H] [--repo DIR]
  lean-check <vector> <sha256> <module> <theorem> [--repo DIR]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

# ----------------------------------------------------------------------------- constants

PROFILE_SNAPSHOT = "profile/normative/P10_Underdetermination_Profile_v0.1.1.md"
PROFILE_SOURCE_REPO = "VolMax-Studio/p10-underdetermination-profile"
PROFILE_SOURCE_COMMIT = "3c20df23781831867834e9bbaaf321acd6a71272"
EXPECTED_PROFILE_SHA256 = "b92c0d689b9f16f2184ba2addb8653ed881595cc3a0117c62cadadf5c6dc6558"

STATEMENT_TYPE = "https://in-toto.io/Statement/v1"
PREDICATE_TYPE = "urn:volmax:p10:underdetermination:s1-experimental:v0"
COSE_CONTENT_TYPE = "application/vnd.in-toto+json"

TEST_KEY_SEED_LABEL = b"P10-S1-TEST-KEY-v0 -- NOT A REAL KEY, NO AUTHORITY, DO NOT TRUST"
TEST_ISS = "urn:volmax:p10:s1:TEST-ISSUER-NO-AUTHORITY"
TEST_KID = b"p10-s1-test-key-v0"

# Files whose digests are bound by the verifier manifest (paths relative to repo root).
SEMANTICS_FILES = ["P10/Core.lean", "P10/Certificate.lean", "P10/Fixtures.lean"]
DECODER_FILES = ["P10/Bytes.lean", "P10/Wire.lean", "P10/Sha256.lean", "P10/Bound.lean"]
CERT_DIR = "P10/Certs"
TOOLCHAIN_FILES = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
POLICY_FILES = ["profile/AXIOM_POLICY.md", "profile/ACCEPTANCE_COMMAND.txt"]
VERIFIER_FILES = ["scripts/p10tool.py", "scripts/verify.sh", "scripts/mutation_suite.py",
                  "scripts/run_tests.py", "scripts/lint_lean.py", "scripts/install_toolchain.sh",
                  "scripts/cose_crosscheck.py", "scripts/check_env.py", "scripts/gen_binding.py", "scripts/gen_testvectors_md.py",
                  "scripts/gen_vectors.py", "scripts/regen.sh", "scripts/update_sums.sh"]
AUDIT_FILE = "P10/AxiomAudit.lean"
MANIFEST_PATH = "manifest/VerifierManifestS1.json"
OLEAN_DIR = ".lake/build/lib/lean"

# Wire vocabulary (mirrors P10/Wire.lean; differential-tested by the mutation suite).
CLAIMS = {"secondBit", "firstBit"}
EVIDENCES = {"f0s_", "f0s0", "f0s1", "f1s_", "f1s0", "f1s1", "inconsistent", "outside"}
WORLDS = {"w00", "w01", "w10", "w11", "wOut"}
WIRE_KIND = "p10-s1-instance-v0"
WIRE_PROFILE = "p10-s1-toy-v0"

PASS, REJECT, HALT = "PASS", "REJECT", "HALT"


class Verdict(Exception):
    def __init__(self, verdict: str, reason: str):
        super().__init__(reason)
        self.verdict = verdict
        self.reason = reason


def reject(reason: str):
    raise Verdict(REJECT, reason)


def halt(reason: str):
    raise Verdict(HALT, reason)


# ----------------------------------------------------------------------------- helpers

def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def read_bytes(root: str, rel: str) -> bytes:
    p = os.path.join(root, rel)
    if not os.path.isfile(p):
        halt(f"required artifact unavailable: {rel}")
    with open(p, "rb") as f:
        return f.read()


def sha256_file(root: str, rel: str) -> str:
    return sha256_bytes(read_bytes(root, rel))


def jcs(obj) -> bytes:
    """RFC 8785 canonical JSON for the subset used here: objects, arrays, strings, booleans,
    null and integers. Keys sorted (ASCII keys => identical to UTF-16 code-unit order),
    no insignificant whitespace, non-ASCII emitted as UTF-8. Floats are refused."""
    def check(o):
        if isinstance(o, float):
            raise ValueError("floats are not permitted in P10 S1 canonical JSON")
        if isinstance(o, dict):
            for k, v in o.items():
                if not isinstance(k, str):
                    raise ValueError("non-string key")
                check(v)
        elif isinstance(o, list):
            for v in o:
                check(v)
    check(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def set_digest(root: str, files: list[str]) -> tuple[str, list[dict]]:
    """Digest of a file set: SHA-256 over `<sha256>  <path>\\n` lines sorted by path."""
    entries = [{"path": f, "sha256": sha256_file(root, f)} for f in sorted(files)]
    listing = "".join(f"{e['sha256']}  {e['path']}\n" for e in entries).encode()
    return sha256_bytes(listing), entries


def list_certs(root: str) -> list[str]:
    d = os.path.join(root, CERT_DIR)
    if not os.path.isdir(d):
        halt(f"required artifact unavailable: {CERT_DIR}")
    return sorted(f"{CERT_DIR}/{n}" for n in os.listdir(d) if n.endswith(".lean"))


def run(cmd: list[str], cwd: str, timeout: int = 900) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout)
    except FileNotFoundError:
        halt(f"required tool unavailable: {cmd[0]}")
    except subprocess.TimeoutExpired:
        halt(f"timeout running {' '.join(cmd)}")
    return p.returncode, (p.stdout + p.stderr).decode("utf-8", "replace")


# ----------------------------------------------------------------------------- wire decoder (Python mirror)

def decode_instance(b: bytes) -> dict:
    """Strict decoder mirroring P10.Wire.decode: accepts exactly the canonical form
    {"claim":C,"evidence":E,"kind":K,"profile":P,"spec":S,"w0":A,"w1":B}."""
    tok = rb"([A-Za-z0-9_.:-]*)"
    pat = (rb'\{"claim":"' + tok + rb'","evidence":"' + tok + rb'","kind":"' + tok +
           rb'","profile":"' + tok + rb'","spec":"' + tok + rb'","w0":"' + tok +
           rb'","w1":"' + tok + rb'"\}')
    m = re.fullmatch(pat, b)
    if not m:
        reject("instance bytes are not in the canonical S1 wire form")
    claim, evidence, kind, profile, spec, w0, w1 = (g.decode() for g in m.groups())
    if kind != WIRE_KIND or profile != WIRE_PROFILE:
        reject("instance kind/profile identifier mismatch")
    if claim not in CLAIMS or evidence not in EVIDENCES or w0 not in WORLDS or w1 not in WORLDS:
        reject("unknown token in instance")
    return {"claim": claim, "evidence": evidence, "kind": kind, "profile": profile,
            "spec": spec, "w0": w0, "w1": w1}


# ----------------------------------------------------------------------------- limitations (verbatim from profile)

def extract_verbatim_limitations(profile_bytes: bytes) -> list[dict]:
    text = profile_bytes.decode("utf-8")
    out = []
    for lid, marker in (("AP1", "**AP1 limitation (verbatim, mandatory in the receipt):**"),
                        ("COVERAGE_INSTANCE", "**Coverage/instance limitation (verbatim, mandatory in the receipt):**")):
        i = text.find(marker)
        if i < 0:
            reject(f"profile snapshot lacks the verbatim marker for {lid}")
        rest = text[i + len(marker):].lstrip("\n")
        line = rest.split("\n", 1)[0]
        if not line.startswith("> "):
            reject(f"profile snapshot: unexpected layout after {lid} marker")
        out.append({"id": lid, "source": "P10 profile v0.1.1 §3 (verbatim)", "text": line[2:]})
    return out


S1_LIMITATIONS = [
    {"id": "S1_MODEL_ADEQUACY", "source": "S1",
     "text": "Underdetermination is established RELATIVE TO the committed profile semantics only. "
             "This does not show that W covers the real world, that Compatible models reality, "
             "that any evidence source is truthful, or that any runtime used this profile in its "
             "decision path."},
    {"id": "S1_NO_SEARCH_INFERENCE", "source": "S1",
     "text": "Failure to find a witness pair is not evidence of determinacy; no such inference is drawn."},
    {"id": "S1_TOY_PROFILE", "source": "S1",
     "text": "The S1 profile is a five-world toy fixture. It is not a concrete P10 profile for any real claim "
             "and has had no profile-adequacy review (profile §7.2)."},
    {"id": "S1_NOT_A_CONFORMING_RECEIPT", "source": "S1",
     "text": "This statement is an experimental S1 artifact. It has no InstanceCommitment, EvidenceClosure, "
             "CoverageProof, FullPrefixReplay, SCITT Receipt or registration-order verification; none of "
             "profile sections 2.3-2.6 is implemented. It is not a conforming P10 receipt."},
    {"id": "S1_CODEC_SUBSET", "source": "S1",
     "text": "The wire format is a strict subset of RFC 8785 JCS (flat object, ASCII-safe string values) "
             "chosen for kernel decodability; profile section 2.7 codec conformance for general worlds "
             "is not demonstrated."},
    {"id": "S1_TEST_SIGNATURE", "source": "S1",
     "text": "The COSE_Sign1 signature uses a public, deterministic TEST key with no authority. "
             "It is not an issuer or human ratification signature."},
    {"id": "S1_STATUS", "source": "S1",
     "text": "Implementation status: self-reviewed, not independently validated, not ratified."},
]


def build_limitations(profile_bytes: bytes) -> list[dict]:
    return extract_verbatim_limitations(profile_bytes) + S1_LIMITATIONS


# ----------------------------------------------------------------------------- lean interaction

def lean_env_info(root: str) -> dict:
    rc, out = run(["lean", "--version"], root)
    if rc != 0:
        halt("lean unavailable")
    lean_path = os.path.realpath(subprocess.run(["which", "lean"], capture_output=True).stdout.decode().strip())
    with open(lean_path, "rb") as f:
        lean_sha = sha256_bytes(f.read())
    shared = os.path.join(os.path.dirname(os.path.dirname(lean_path)), "lib", "lean", "libleanshared.so")
    shared_sha = "absent"
    if os.path.isfile(shared):
        with open(shared, "rb") as f:
            shared_sha = sha256_bytes(f.read())
    return {"version_string": out.strip(), "executable_sha256": lean_sha, "shared_lib_sha256": shared_sha}


def lean_build(root: str, clean: bool = True):
    """Build from scratch by default: `filebytes%` reads files that Lake does not track as
    dependencies, so an incremental build could hide a changed vector."""
    if clean:
        shutil.rmtree(os.path.join(root, ".lake", "build"), ignore_errors=True)
    rc, out = run(["lake", "build"], root)
    if rc != 0:
        reject("lake build failed:\n" + out[-2000:])
    return out


def checker_owned_check(root: str, vector: str, digest: str, module: str, theorem: str) -> str:
    """Generate the CHECKER-OWNED statement from the committed bytes and ask Lean to
    check the certificate against it. The certificate never supplies its own proposition."""
    if not re.fullmatch(r"[A-Za-z0-9_./-]+", vector) or ".." in vector:
        reject("unsafe vector path")
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        reject("malformed digest")
    if not re.fullmatch(r"P10\.Certs\.[A-Za-z0-9_]+", module) or \
            not re.fullmatch(r"P10\.Certs\.[A-Za-z0-9_]+\.[A-Za-z0-9_]+", theorem):
        reject("unsafe module/theorem name")
    src = (
        f"import {module}\n"
        f"set_option maxRecDepth 100000\n"
        f"example : P10.Bound (filebytes% \"{vector}\") (hex% \"{digest}\") := {theorem}\n"
        f"#print axioms {theorem}\n"
    )
    with tempfile.TemporaryDirectory(dir=root) as td:
        f = os.path.join(td, "CheckerOwned.lean")
        with open(f, "w") as fh:
            fh.write(src)
        rc, out = run(["lake", "env", "lean", os.path.relpath(f, root)], root)
    if rc != 0:
        reject("Lean rejected the certificate against the checker-owned proposition:\n" + out[-1500:])
    want = f"'{theorem}' does not depend on any axioms"
    lines = [l for l in out.splitlines() if l.strip()]
    if lines != [want]:
        reject("unexpected Lean output (axioms/warnings) for checker-owned check:\n" + out[-1500:])
    return out


def axiom_audit(root: str) -> str:
    rc, out = run(["lake", "env", "lean", AUDIT_FILE], root)
    if rc != 0:
        reject("axiom audit file failed to elaborate:\n" + out[-1500:])
    with open(os.path.join(root, AUDIT_FILE), encoding="utf-8") as f:
        n_expected = sum(1 for l in f if l.startswith("#print axioms "))
    lines = [l for l in out.splitlines() if l.strip()]
    ok = [l for l in lines if l.endswith("does not depend on any axioms")]
    if len(ok) != n_expected or len(lines) != n_expected:
        reject(f"axiom audit: expected {n_expected} axiom-free declarations, "
               f"got {len(ok)} of {len(lines)} lines:\n" + out[-1500:])
    return out


# ----------------------------------------------------------------------------- manifest

def compute_manifest(root: str, with_oleans: bool = True) -> dict:
    sem_d, sem_e = set_digest(root, SEMANTICS_FILES)
    dec_d, dec_e = set_digest(root, DECODER_FILES)
    cert_d, cert_e = set_digest(root, list_certs(root))
    tc_d, tc_e = set_digest(root, TOOLCHAIN_FILES)
    pol_d, pol_e = set_digest(root, POLICY_FILES)
    ver_d, ver_e = set_digest(root, VERIFIER_FILES)
    oleans = {}
    od = os.path.join(root, OLEAN_DIR)
    if with_oleans and os.path.isdir(od):
        for dp, _, fns in os.walk(od):
            for fn in fns:
                if fn.endswith(".olean"):
                    rel = os.path.relpath(os.path.join(dp, fn), root)
                    oleans[rel] = sha256_file(root, rel)
    lean = lean_env_info(root)
    with open(os.path.join(root, "lean-toolchain")) as f:
        tc_id = f.read().strip()
    return {
        "manifest_version": "P10-S1-VerifierManifest-v0",
        "profile_specification_sha256": sha256_file(root, PROFILE_SNAPSHOT),
        "lean_toolchain_identifier": tc_id,
        "lean_version_string": lean["version_string"],
        "lean_toolchain_artifact_identifier": "lean-linux-x86_64-executable (conda-forge lean4 4.33.0 build h6c1889d_0)",
        "lean_toolchain_artifact_sha256": lean["executable_sha256"],
        "lean_shared_library_sha256": lean["shared_lib_sha256"],
        "mathlib": "not used (no dependencies; lake-manifest.json has an empty package list)",
        "semantics_source_digest": sem_d, "semantics_source_files": sem_e,
        "decoder_source_digest": dec_d, "decoder_source_files": dec_e,
        "certificate_source_digest": cert_d, "certificate_source_files": cert_e,
        "toolchain_config_digest": tc_d, "toolchain_config_files": tc_e,
        "axiom_policy_digest": pol_d, "axiom_policy_files": pol_e,
        "verifier_scripts_digest": ver_d, "verifier_script_files": ver_e,
        "olean_digest_set": dict(sorted(oleans.items())),
        "axiom_audit_file_sha256": sha256_file(root, AUDIT_FILE),
    }


def write_manifest(root: str) -> str:
    m = compute_manifest(root)
    data = jcs(m)
    os.makedirs(os.path.join(root, "manifest"), exist_ok=True)
    with open(os.path.join(root, MANIFEST_PATH), "wb") as f:
        f.write(data)
    return sha256_bytes(data)


# ----------------------------------------------------------------------------- signing (TEST key)

def test_private_key():
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    seed = hashlib.sha256(TEST_KEY_SEED_LABEL).digest()
    return Ed25519PrivateKey.from_private_bytes(seed)


def test_public_bytes() -> bytes:
    from cryptography.hazmat.primitives import serialization
    return test_private_key().public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw)


def cose_okp(with_private: bool):
    from pycose.keys import OKPKey
    from pycose.keys.curves import Ed25519
    from pycose.keys.keyparam import KpKid
    d = hashlib.sha256(TEST_KEY_SEED_LABEL).digest()
    x = test_public_bytes()
    if with_private:
        return OKPKey(crv=Ed25519, d=d, x=x, optional_params={KpKid: TEST_KID})
    return OKPKey(crv=Ed25519, x=x, optional_params={KpKid: TEST_KID})


def sign_statement(payload: bytes, subject: str) -> bytes:
    """SCITT-shaped Signed Statement: COSE_Sign1 with protected alg, kid, content type and
    CWT claims (label 15: iss=1, sub=2). No receipt (label 394) is attached: registration
    in a Transparency Service is NOT demonstrated."""
    from pycose.messages import Sign1Message
    from pycose.headers import Algorithm, KID, ContentType
    from pycose.algorithms import EdDSA
    msg = Sign1Message(
        phdr={Algorithm: EdDSA, KID: TEST_KID, ContentType: COSE_CONTENT_TYPE,
              15: {1: TEST_ISS, 2: subject}},
        uhdr={}, payload=payload)
    msg.key = cose_okp(True)
    return msg.encode(tag=True)


def verify_cose(blob: bytes) -> tuple[dict, bytes]:
    import cbor2
    from pycose.messages import Sign1Message
    from pycose.headers import Algorithm, KID, ContentType
    try:
        msg = Sign1Message.decode(blob)
    except Exception as e:  # malformed COSE
        reject(f"COSE_Sign1 decode failed: {e}")
    p = msg.phdr
    if p.get(Algorithm) is None or p[Algorithm].fullname != "EDDSA":
        reject("protected alg must be EdDSA")
    if p.get(ContentType) != COSE_CONTENT_TYPE:
        reject("protected content type must be application/vnd.in-toto+json")
    if p.get(KID) != TEST_KID:
        reject("unknown kid: only the S1 TEST key is accepted by this verifier")
    cwt = p.get(15)
    if not isinstance(cwt, dict) or not isinstance(cwt.get(1), str) or not isinstance(cwt.get(2), str):
        reject("protected CWT claims (iss, sub) missing or not tstr")
    if cwt[1] != TEST_ISS:
        reject("unexpected iss")
    if 394 in msg.uhdr:
        # A receipt would need real SCITT verification, which S1 does not implement.
        halt("SCITT receipt present but receipt verification is not implemented in S1")
    msg.key = cose_okp(False)
    try:
        ok = msg.verify_signature()
    except Exception as e:
        reject(f"signature verification error: {e}")
    if not ok:
        reject("COSE_Sign1 signature invalid")
    return cwt, msg.payload


# ----------------------------------------------------------------------------- statement

def proposition_identity(instance_sha: str, dec_d: str, sem_d: str, spec: str, vector: str) -> str:
    return sha256_bytes(jcs({
        "decoder_source_digest": dec_d,
        "instance_sha256": instance_sha,
        "lean_predicate": "P10.Bound",
        "lean_statement_template": 'P10.Bound (filebytes% "<instance>") (hex% "<instance sha256>")',
        "semantics_source_digest": sem_d,
        "spec_sha256": spec,
        "vector_path": vector,
    }))


def build_statement(root: str, vector: str, module: str, theorem: str, cert_file: str,
                    *, skip_lean: bool = False) -> tuple[bytes, bytes]:
    manifest_digest = write_manifest(root)
    manifest = json.loads(read_bytes(root, MANIFEST_PATH))
    inst_bytes = read_bytes(root, vector)
    inst = decode_instance(inst_bytes)
    profile_bytes = read_bytes(root, PROFILE_SNAPSHOT)
    profile_sha = sha256_bytes(profile_bytes)
    if profile_sha != EXPECTED_PROFILE_SHA256:
        reject("profile snapshot digest differs from the recorded ratified digest")
    if inst["spec"] != "sha256:" + profile_sha:
        reject("instance spec field does not equal the profile snapshot digest")
    inst_sha = sha256_bytes(inst_bytes)
    if skip_lean:
        # ATTACKER MODE (used by scripts/mutation_suite.py to model a malicious runtime): fill in
        # whatever Lean outputs can be obtained, tolerate failures. The verifier must not care.
        audit_out = cert_out = ""
        try:
            audit_out = axiom_audit(root)
        except Verdict:
            pass
        try:
            cert_out = checker_owned_check(root, vector, inst_sha, module, theorem)
        except Verdict:
            pass
    else:
        lean_build(root)
        audit_out = axiom_audit(root)
        cert_out = checker_owned_check(root, vector, inst_sha, module, theorem)
    cert_sha = sha256_file(root, cert_file)
    lean = lean_env_info(root)
    limitations = build_limitations(profile_bytes)
    pred = {
        "status": "EXPERIMENTAL DRAFT S1; self-reviewed; not independently validated; not ratified",
        "outcome": {"result": "NotDemonstrated", "reason": "underdetermined"},
        "profile": {
            "spec_path": "P10_Underdetermination_Profile_v0.1.1.md",
            "spec_sha256": profile_sha,
            "media_type": "text/markdown",
            "source_repo": PROFILE_SOURCE_REPO,
            "source_commit": PROFILE_SOURCE_COMMIT,
        },
        "instance": {
            "path": vector, "sha256": inst_sha, "wire_kind": inst["kind"],
            "wire_profile_id": inst["profile"],
            "encoding": "RFC 8785 JCS subset: flat object, sorted ASCII keys, ASCII-safe string values",
        },
        "claim": {"token": inst["claim"], "digest": sha256_bytes(jcs({"claim": inst["claim"]}))},
        "evidence": {"token": inst["evidence"], "digest": sha256_bytes(jcs({"evidence": inst["evidence"]}))},
        "witnesses": [
            {"token": inst["w0"], "digest": sha256_bytes(jcs({"world": inst["w0"]}))},
            {"token": inst["w1"], "digest": sha256_bytes(jcs({"world": inst["w1"]}))},
        ],
        "proposition": {
            "lean_predicate": "P10.Bound",
            "lean_statement": f'P10.Bound (filebytes% "{vector}") (hex% "{inst_sha}")',
            "identity_digest": proposition_identity(
                inst_sha, manifest["decoder_source_digest"], manifest["semantics_source_digest"],
                profile_sha, vector),
        },
        "certificate": {
            "lean_module": module, "lean_module_path": cert_file, "lean_module_sha256": cert_sha,
            "theorem": theorem,
            "axiom_audit_output_sha256": sha256_bytes(audit_out.encode()),
            "checker_owned_output_sha256": sha256_bytes(cert_out.encode()),
            "proof_mode": "Lean kernel type-check of P10.Bound (kernel-evaluated SHA-256 + decoder + checker via `decide`); "
                          "native_decide: not used; custom axioms: none; sorry: none",
        },
        "verifier": {
            "manifest_path": MANIFEST_PATH, "manifest_sha256": manifest_digest,
            "lean_toolchain": manifest["lean_toolchain_identifier"],
            "lean_version_string": lean["version_string"],
            "lean_executable_sha256": lean["executable_sha256"],
            "lean_shared_library_sha256": lean["shared_lib_sha256"],
            "lake_manifest_sha256": sha256_file(root, "lake-manifest.json"),
            "mathlib": manifest["mathlib"],
            "decoder_source_digest": manifest["decoder_source_digest"],
            "semantics_source_digest": manifest["semantics_source_digest"],
            "verifier_scripts_digest": manifest["verifier_scripts_digest"],
            "python_verifier_note": "p10tool.py is TCB for hashing, JCS, COSE and orchestration",
        },
        "limitations": limitations,
        "limitations_digest": sha256_bytes(jcs(limitations)),
        "must_understand": ["limitations"],
        "not_demonstrated": [
            "SCITT registration / Receipt (no Transparency Service was used)",
            "InstanceCommitment, EvidenceClosure, CoverageProof, FullPrefixReplay",
            "independent validation of the semantic mapping",
            "faithfulness of the S1 toy profile to any real world",
            "that any runtime consumed this verdict at decision time",
        ],
    }
    statement = {
        "_type": STATEMENT_TYPE,
        "subject": [{"name": vector, "digest": {"sha256": inst_sha}}],
        "predicateType": PREDICATE_TYPE,
        "predicate": pred,
    }
    payload = jcs(statement)
    subject = "urn:volmax:p10:s1:TEST-SUBJECT:" + inst_sha[:16]
    return payload, sign_statement(payload, subject)


# ----------------------------------------------------------------------------- verify

SPEC_TOK_RE = re.compile(r'bytes% "sha256:([0-9a-f]{64})"')


def verify(root: str, cose_path: str, manifest_pin: str | None) -> dict:
    report = {"checks": []}

    def ok(name, detail=""):
        report["checks"].append({"check": name, "result": "ok", "detail": detail})

    if not os.path.isfile(cose_path):
        halt(f"COSE artifact unavailable: {cose_path}")
    with open(cose_path, "rb") as f:
        blob = f.read()
    cwt, payload = verify_cose(blob)
    ok("cose_signature_and_headers", "TEST key only; no SCITT receipt")

    try:
        st = json.loads(payload)
    except Exception:
        reject("payload is not JSON")
    if jcs(st) != payload:
        reject("payload is not JCS-canonical")
    ok("payload_jcs_canonical")
    if st.get("_type") != STATEMENT_TYPE or st.get("predicateType") != PREDICATE_TYPE:
        reject("statement/predicate type mismatch")
    pred = st.get("predicate")
    if not isinstance(pred, dict):
        reject("missing predicate")
    if pred.get("must_understand") != ["limitations"] or not pred.get("limitations"):
        reject("limitations is a must-understand field and must be present")
    if pred.get("outcome") != {"result": "NotDemonstrated", "reason": "underdetermined"}:
        reject("outcome must be NotDemonstrated(reason=underdetermined)")
    for forbidden in ("S_R", "receipt_ref", "coverage_verification_result"):
        if forbidden in pred:
            reject(f"post-registration field {forbidden} must not be in the issuer-signed payload (M30)")
    ok("statement_shape")

    # --- profile
    profile_bytes = read_bytes(root, PROFILE_SNAPSHOT)
    profile_sha = sha256_bytes(profile_bytes)
    if profile_sha != EXPECTED_PROFILE_SHA256:
        reject("profile snapshot digest differs from the recorded ratified profile digest (M1/N8)")
    if pred["profile"]["spec_sha256"] != profile_sha:
        reject("statement profile digest differs from the profile snapshot (stale certificate / N8)")
    wire = read_bytes(root, "P10/Wire.lean").decode("utf-8")
    m = SPEC_TOK_RE.search(wire)
    if not m or m.group(1) != profile_sha:
        reject("Lean decoder's specTok differs from the profile snapshot digest (M32)")
    ok("profile_digest_chain", profile_sha)

    # --- limitations verbatim
    lims = build_limitations(profile_bytes)
    if pred["limitations"] != lims:
        reject("limitations differ from the verbatim profile text / S1 limitations (M31)")
    if pred["limitations_digest"] != sha256_bytes(jcs(lims)):
        reject("limitations_digest mismatch (M31)")
    ok("limitations_verbatim")

    # --- manifest
    committed = read_bytes(root, MANIFEST_PATH)
    manifest_sha = sha256_bytes(committed)
    if manifest_pin is not None and manifest_pin != manifest_sha:
        reject("manifest digest differs from the pinned (profile-committed) digest (M33)")
    if pred["verifier"]["manifest_sha256"] != manifest_sha:
        reject("statement verifier digest differs from the committed manifest (M35)")
    man = json.loads(committed)
    src_now = compute_manifest(root, with_oleans=False)
    for k, v in src_now.items():
        if k == "olean_digest_set":
            continue  # compared after the build
        if man.get(k) != v:
            reject(f"committed VerifierManifest differs from the artifacts on disk at '{k}' (M33)")
    ok("verifier_manifest", manifest_sha)
    for k in ("decoder_source_digest", "semantics_source_digest", "verifier_scripts_digest"):
        if pred["verifier"][k] != man[k]:
            reject(f"statement {k} differs from manifest")
    lean = lean_env_info(root)
    if lean["executable_sha256"] != man["lean_toolchain_artifact_sha256"] or \
            lean["shared_lib_sha256"] != man["lean_shared_library_sha256"] or \
            lean["version_string"] != man["lean_version_string"]:
        reject("Lean toolchain artifact differs from the manifest (M33)")
    with open(os.path.join(root, "lean-toolchain")) as f:
        if f.read().strip() != man["lean_toolchain_identifier"]:
            reject("lean-toolchain differs from the manifest")
    ok("toolchain_identity", lean["version_string"])

    # --- instance
    vec = pred["instance"]["path"]
    inst_bytes = read_bytes(root, vec)
    inst_sha = sha256_bytes(inst_bytes)
    if inst_sha != pred["instance"]["sha256"] or inst_sha != st["subject"][0]["digest"]["sha256"]:
        reject("instance digest mismatch (claim/evidence/witness mutation)")
    inst = decode_instance(inst_bytes)
    if inst["spec"] != "sha256:" + profile_sha:
        reject("instance spec field differs from the profile digest")
    checks = [
        (pred["claim"], "claim", inst["claim"], {"claim": inst["claim"]}),
        (pred["evidence"], "evidence", inst["evidence"], {"evidence": inst["evidence"]}),
        (pred["witnesses"][0], "w0", inst["w0"], {"world": inst["w0"]}),
        (pred["witnesses"][1], "w1", inst["w1"], {"world": inst["w1"]}),
    ]
    for entry, name, tok, obj in checks:
        if entry["token"] != tok or entry["digest"] != sha256_bytes(jcs(obj)):
            reject(f"{name} identity in statement differs from instance bytes")
    ok("instance_binding", inst_sha)

    # --- proposition identity
    pid = proposition_identity(inst_sha, man["decoder_source_digest"], man["semantics_source_digest"],
                               profile_sha, vec)
    if pred["proposition"]["identity_digest"] != pid or \
            pred["proposition"]["lean_statement"] != f'P10.Bound (filebytes% "{vec}") (hex% "{inst_sha}")':
        reject("proposition identity differs (the proved proposition is not the stated one)")
    ok("proposition_identity", pid)

    # --- certificate
    cert = pred["certificate"]
    cf = cert["lean_module_path"]
    if cf not in [e["path"] for e in man["certificate_source_files"]]:
        reject("certificate module is not bound by the manifest")
    if cf != cert["lean_module"].replace(".", "/") + ".lean":
        reject("certificate module name does not match its path")
    if sha256_file(root, cf) != cert["lean_module_sha256"]:
        reject("certificate module digest mismatch")
    lean_build(root)
    # oleans exist only after build; recompute manifest oleans against committed manifest
    if jcs(compute_manifest(root)) != committed:
        reject("build outputs (.olean digests) differ from the committed manifest (M33)")
    out_audit = axiom_audit(root)
    if sha256_bytes(out_audit.encode()) != cert["axiom_audit_output_sha256"]:
        reject("axiom audit output digest differs from the statement")
    out_chk = checker_owned_check(root, vec, inst_sha, cert["lean_module"], cert["theorem"])
    if sha256_bytes(out_chk.encode()) != cert["checker_owned_output_sha256"]:
        reject("checker-owned check output digest differs from the statement")
    ok("lean_kernel_check", f"{cert['theorem']} : Bound <{vec}> <sha256 {inst_sha[:16]}…>; axioms: none")

    report["verdict"] = PASS
    report["claim"] = ("NotDemonstrated(reason=underdetermined) is established relative to the committed "
                       "S1 profile semantics for the committed instance bytes")
    report["signed_by"] = cwt[1] + " (TEST key)"
    report["scitt_registration"] = "NOT DEMONSTRATED"
    return report


# ----------------------------------------------------------------------------- CLI

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("manifest", "statement", "verify", "lean-check"):
        sp = sub.add_parser(name)
        sp.add_argument("--repo", default=os.getcwd())
        if name == "statement":
            sp.add_argument("vector")
            sp.add_argument("--module", required=True)
            sp.add_argument("--theorem", required=True)
            sp.add_argument("--cert-file", required=True)
            sp.add_argument("--out", required=True, help="output stem, writes <stem>.statement.json and <stem>.cose")
            sp.add_argument("--skip-lean", action="store_true", help=argparse.SUPPRESS)
        if name == "verify":
            sp.add_argument("cose")
            sp.add_argument("--manifest-digest")
        if name == "lean-check":
            sp.add_argument("vector")
            sp.add_argument("digest")
            sp.add_argument("module")
            sp.add_argument("theorem")
    a = ap.parse_args(argv)
    root = os.path.abspath(a.repo)
    try:
        if a.cmd == "manifest":
            print(write_manifest(root))
            return 0
        if a.cmd == "statement":
            payload, cose = build_statement(root, a.vector, a.module, a.theorem, a.cert_file,
                                            skip_lean=a.skip_lean)
            os.makedirs(os.path.dirname(os.path.join(root, a.out)) or ".", exist_ok=True)
            with open(os.path.join(root, a.out + ".statement.json"), "wb") as f:
                f.write(payload)
            with open(os.path.join(root, a.out + ".cose"), "wb") as f:
                f.write(cose)
            print(sha256_bytes(payload), sha256_bytes(cose))
            return 0
        if a.cmd == "lean-check":
            print(checker_owned_check(root, a.vector, a.digest, a.module, a.theorem), end="")
            return 0
        if a.cmd == "verify":
            cose = a.cose if os.path.isabs(a.cose) else os.path.join(root, a.cose)
            rep = verify(root, cose, a.manifest_digest)
            print(json.dumps(rep, indent=2, sort_keys=True))
            print("VERDICT: PASS")
            return 0
    except Verdict as v:
        print(f"VERDICT: {v.verdict}: {v.reason}", file=sys.stderr)
        return 1 if v.verdict == REJECT else 2
    except Exception as e:  # fail closed on ANY unexpected error
        print(f"VERDICT: REJECT: unexpected error (fail-closed): {type(e).__name__}: {e}", file=sys.stderr)
        return 1
    return 2


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Negative mutation suite for the S1 reference chain.

Every case copies the pristine tree to a scratch directory, applies ONE mutation
(or simulates ONE malicious runtime), runs the third-party verifier
(`scripts/p10tool.py verify`) and asserts that the verdict is the expected fail-closed
one *for the expected reason* (substring match), so a mutation cannot "pass" by failing
for an unrelated cause.

Expected verdicts: REJECT (exit 1) or HALT (exit 2). One case is deliberately expected to
PASS and is labelled INFO: it documents that a fully self-consistent *alternative*
verifier tree is accepted unless the verifier-manifest digest is pinned (which is why
the profile commits `verifier_manifest_digest`). Invoke from the repository root:

    python3 scripts/mutation_suite.py [--keep] [--only SUBSTR]
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

spec = importlib.util.spec_from_file_location("p10tool", os.path.join(HERE, "p10tool.py"))
p10tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p10tool)

COSE = "vectors/out/p1.cose"
VECTOR = "vectors/p1.instance.json"
MODULE, THEOREM, CERTFILE = "P10.Certs.P1", "P10.Certs.P1.cert", "P10/Certs/P1.lean"
EXPECT_CODE = {"REJECT": 1, "HALT": 2, "PASS": 0}


def sha256_file(path: str) -> str:
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def read(root, rel):
    with open(os.path.join(root, rel), "rb") as f:
        return f.read()


def write(root, rel, data):
    os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
    with open(os.path.join(root, rel), "wb") as f:
        f.write(data)


def edit(root, rel, old: str, new: str, count=1):
    s = read(root, rel).decode()
    assert old in s, f"mutation anchor not found in {rel}: {old!r}"
    write(root, rel, s.replace(old, new, count).encode())


def tool(root, *args, env=None, timeout=1800):
    e = dict(os.environ)
    if env:
        e.update(env)
    p = subprocess.run([sys.executable, os.path.join(root, "scripts/p10tool.py"), *args],
                       cwd=root, capture_output=True, env=e, timeout=timeout)
    return p.returncode, (p.stdout + p.stderr).decode("utf-8", "replace")


def regen(root, vector=VECTOR, module=MODULE, theorem=THEOREM, certfile=CERTFILE, out="vectors/out/p1"):
    """Attacker step: rebuild manifest + statement + signature over the mutated tree,
    skipping the Lean checks (a malicious runtime signs whatever it likes; the test key is public)."""
    subprocess.run(["lake", "build"], cwd=root, capture_output=True)  # may fail; attacker ignores
    rc, out_ = tool(root, "statement", vector, "--module", module, "--theorem", theorem,
                    "--cert-file", certfile, "--out", out, "--skip-lean")
    assert rc == 0, f"attacker regen failed: {out_}"


def resign(root, mutate, out="vectors/out/p1.cose"):
    """Attacker step: edit the signed statement's JSON and re-sign with the (public) test key."""
    old = read(root, COSE)
    from pycose.messages import Sign1Message
    msg = Sign1Message.decode(old)
    st = json.loads(msg.payload)
    mutate(st)
    payload = p10tool.jcs(st)
    write(root, out, p10tool.sign_statement(payload, "urn:volmax:p10:s1:TEST-SUBJECT:mutated"))


# ----------------------------------------------------------------------------- cases

def case_profile_bytes(r):
    write(r, p10tool.PROFILE_SNAPSHOT, read(r, p10tool.PROFILE_SNAPSHOT) + b"\n")


def case_semantics(r):
    edit(r, "P10/Fixtures.lean", "| .w01 | .w11 | .wOut => true", "| .w11 | .wOut => true | .w01 => false")


def case_semantics_regen(r):
    case_semantics(r)
    regen(r)


def inst_edit(field, value):
    def go(r):
        s = read(r, VECTOR).decode()
        import re
        s2 = re.sub(rf'("{field}":")[^"]*(")', rf'\g<1>{value}\g<2>', s, count=1)
        assert s2 != s
        write(r, VECTOR, s2.encode())
    return go


def inst_edit_regen(field, value):
    def go(r):
        inst_edit(field, value)(r)
        regen(r)
    return go


def case_decoder_swap(r):
    edit(r, "P10/Wire.lean", "(worldOfTok a.1).bind fun w0 =>\n    (worldOfTok z.1).bind fun w1",
         "(worldOfTok z.1).bind fun w0 =>\n    (worldOfTok a.1).bind fun w1")


def case_decoder_swap_regen(r):
    case_decoder_swap(r)
    regen(r)


def case_toolchain_file(r):
    write(r, "lean-toolchain", b"leanprover/lean4:v4.34.0\n")


def case_lake_manifest(r):
    s = read(r, "lake-manifest.json").decode()
    write(r, "lake-manifest.json", s.replace('"packages": []', '"packages": [], "x": 1').encode())


def case_lakefile(r):
    edit(r, "lakefile.toml", "autoImplicit = false", "autoImplicit = true")


def case_fake_lean(r):
    # a different executable that reports the same --version: digest differs
    d = os.path.join(r, ".fakebin")
    os.makedirs(d)
    real = subprocess.run(["which", "lean"], capture_output=True).stdout.decode().strip()
    f = os.path.join(d, "lean")
    with open(f, "w") as fh:
        fh.write(f'#!/bin/sh\nexec "{real}" "$@"\n')
    os.chmod(f, os.stat(f).st_mode | stat.S_IEXEC)


def st_prop_identity(st):
    st["predicate"]["proposition"]["identity_digest"] = "0" * 64


def st_prop_statement(st):
    st["predicate"]["proposition"]["lean_statement"] = 'P10.Bound (filebytes% "vectors/negative/n3_same_value.json") (hex% "00")'


def st_drop_limitations(st):
    del st["predicate"]["limitations"]


def st_edit_limitation(st):
    st["predicate"]["limitations"][0]["text"] += " (edited)"


def st_manifest_digest(st):
    st["predicate"]["verifier"]["manifest_sha256"] = "1" * 64


def st_inject_sr(st):
    st["predicate"]["S_R"] = "checkpoint"


def st_outcome(st):
    st["predicate"]["outcome"] = {"result": "Determinate", "reason": "determinate"}


def st_theorem_weaker(st):
    st["predicate"]["certificate"]["theorem"] = "P10.Certs.P1.underdetermined"


def st_profile_digest(st):
    st["predicate"]["profile"]["spec_sha256"] = "2" * 64


def st_witness(st):
    st["predicate"]["witnesses"][1]["token"] = "w10"


def case_st(mut):
    return lambda r: resign(r, mut)


def case_stale_new_profile(r):
    """New profile bytes with everything in the tree made self-consistent for it, but the OLD
    signed statement reused."""
    import re
    prof = read(r, p10tool.PROFILE_SNAPSHOT) + b"\n<!-- v0.1.2 -->\n"
    write(r, p10tool.PROFILE_SNAPSHOT, prof)
    new = hashlib.sha256(prof).hexdigest()
    old = p10tool.EXPECTED_PROFILE_SHA256
    for rel in ("scripts/p10tool.py", "P10/Wire.lean", VECTOR):
        s = read(r, rel).decode()
        write(r, rel, s.replace(old, new).encode())
    # attacker also refreshes the manifest (so only the stale statement is wrong)
    subprocess.run(["lake", "build"], cwd=r, capture_output=True)
    tool(r, "manifest")


def certificate_replace(new_body):
    def go(r):
        edit(r, CERTFILE, "theorem cert : P10.Bound bytes digest :=\n  P10.bound_of_check (by decide) (by decide)",
             new_body)
        regen(r)
    return go


def case_forged_runtime_n3(r):
    """A 'runtime' issues NotDemonstrated for the same-value vector n3, attaching the P1 certificate,
    with honest digests for n3 and a valid (test-key) signature."""
    rc, out = tool(r, "statement", "vectors/negative/n3_same_value.json", "--module", MODULE,
                   "--theorem", THEOREM, "--cert-file", CERTFILE, "--out", "vectors/out/p1", "--skip-lean")
    assert rc == 0, out


def case_forged_runtime_no_cert(r):
    def m(st):
        st["predicate"]["certificate"]["lean_module"] = "P10.Certs.Nonexistent"
        st["predicate"]["certificate"]["lean_module_path"] = "P10/Certs/Nonexistent.lean"
    resign(r, m)


def case_runtime_other_semantics_old_cert(r):
    """Runtime uses different internal semantics (compatibility made vacuous) but attaches the old
    statement and certificate."""
    edit(r, "P10/Fixtures.lean", "| .obs f s, w => obsCompat f s w", "| .obs _ _, _ => true")


def case_benign_edit_regen(r):
    """Benign, semantics-preserving edit of a bound source file (a comment) with the manifest and the
    statement honestly regenerated (Lean checks run for real)."""
    edit(r, "P10/Fixtures.lean", "namespace P10.S1\n", "namespace P10.S1\n-- benign edit\n")
    subprocess.run(["lake", "build"], cwd=r, capture_output=True)
    rc, out = tool(r, "statement", VECTOR, "--module", MODULE, "--theorem", THEOREM,
                   "--cert-file", CERTFILE, "--out", "vectors/out/p1")
    assert rc == 0, out


def _write_cert(r, name, body):
    write(r, f"P10/Certs/{name}.lean", body.encode())


def _sha(r, rel):
    return hashlib.sha256(read(r, rel)).hexdigest()


def _n_bytes(vec):
    return f'def bytes : List Nat := filebytes% "{vec}"'


def case_f1_honest_cert(vec, inst, ud_ev, name):
    """F1: an HONEST, hatch-free certificate for a vector whose NAMED witnesses are invalid, obtained by
    proving `Underdetermined` through a different pair. Must not type-check against the exact target."""
    def go(r):
        d = _sha(r, vec)
        _write_cert(r, name, (
            "import P10.Bound\nset_option maxRecDepth 100000\n"
            f"namespace P10.Certs.{name}\nopen P10 P10.S1 P10.Wire\n"
            f"{_n_bytes(vec)}\ndef digest : List Nat := hex% \"{d}\"\n"
            f"theorem dec : decode bytes = some {inst} := by decide\n"
            f"theorem ud : Underdetermined profile {ud_ev} c0 :=\n"
            "  ⟨.w00, .w01, rfl, rfl, rfl, rfl, by change evalB c0 .w00 ≠ evalB c0 .w01; decide⟩\n"
            "theorem cert : P10.Bound bytes digest :=\n"
            "  ⟨(by decide), (holds_iff dec).2 ⟨listEq_sound (by decide), ud⟩⟩\n"
            f"end P10.Certs.{name}\n"))
        rc, out = tool(r, "statement", vec, "--module", f"P10.Certs.{name}", "--theorem",
                       f"P10.Certs.{name}.cert", "--cert-file", f"P10/Certs/{name}.lean",
                       "--out", "vectors/out/p1", "--skip-lean")
        assert rc == 0, out
    return go


def _hijack_module(r):
    n3 = _sha(r, "vectors/negative/n3_same_value.json")
    p1 = _sha(r, "vectors/p1.instance.json")
    _write_cert(r, "Hijack", (
        "import P10.Certs.P1\n"
        "macro_rules\n"
        "  | `(filebytes% \"vectors/negative/n3_same_value.json\") => `(filebytes% \"vectors/p1.instance.json\")\n"
        "macro_rules\n"
        f"  | `(hex% \"{n3}\") => `(hex% \"{p1}\")\n"
        "namespace P10.Certs.Hijack\n"
        f"theorem cert : P10.Bound (filebytes% \"vectors/p1.instance.json\") (hex% \"{p1}\") := P10.Certs.P1.cert\n"
        "end P10.Certs.Hijack\n"))


def _inject_module(r):
    n1 = _sha(r, "vectors/negative/n1_determined.json")
    _write_cert(r, "Inject", (
        "import P10.Bound\nimport Lean\nopen Lean Elab Command Term Meta\n\n"
        "run_cmd liftTermElabM do\n"
        f"  let stx ← `(P10.Bound (filebytes% \"vectors/negative/n1_determined.json\") (hex% \"{n1}\"))\n"
        "  let ty ← Term.elabType stx\n  let ty ← instantiateMVars ty\n"
        "  withOptions (·.setBool `debug.skipKernelTC true) <|\n"
        "    addDecl (.thmDecl { name := `P10.Certs.Inject.cert, levelParams := [], type := ty, "
        "value := mkConst ``True.intro })\n"))


def case_meta_full(builder, vec, name):
    """Full-pipeline variant: the attacker also builds/signs a statement for `vec` citing the module."""
    def go(r):
        builder(r)
        subprocess.run(["lake", "build", f"P10.Certs.{name}"], cwd=r, capture_output=True)
        rc, out = tool(r, "statement", vec, "--module", f"P10.Certs.{name}", "--theorem",
                       f"P10.Certs.{name}.cert", "--cert-file", f"P10/Certs/{name}.lean",
                       "--out", "vectors/out/p1", "--skip-lean")
        assert rc == 0, out
    return go


def case_meta_direct(builder, name):
    """Direct variant: the module is built and the checker-owned check is invoked directly, BYPASSING the
    source-policy lint, to prove that the architecture (precompiled target + kernel replay) is a
    boundary in its own right."""
    def go(r):
        builder(r)
        rc = subprocess.run(["lake", "build", f"P10.Certs.{name}"], cwd=r, capture_output=True).returncode
        assert rc == 0, f"attack module {name} must build for the direct test"
    return go


def case_unsafe_direct(body):
    def go(r):
        edit(r, CERTFILE, "theorem cert : P10.Bound bytes digest :=\n  P10.bound_of_check (by decide) (by decide)", body)
        subprocess.run(["lake", "build", MODULE], cwd=r, capture_output=True)
    return go


CASES = [
    # (id, description, setup, pin?, expected verdict, [acceptable reason substrings])
    ("M1-profile-bytes", "profile snapshot bytes mutated", case_profile_bytes, True, "REJECT",
     ["profile snapshot digest differs"]),
    ("M1-semantics-stale", "Lean semantics source mutated; old statement + certificate", case_semantics, True, "REJECT",
     ["committed VerifierManifest differs"]),
    ("M1-semantics-regen", "Lean semantics mutated; attacker regenerates manifest+statement (pinned manifest)",
     case_semantics_regen, True, "REJECT", ["supplied pin"]),
    ("M1-semantics-regen-selfpin", "same, attacker supplies THEIR OWN manifest digest as the pin: Lean must still refuse",
     case_semantics_regen, "self", "REJECT", ["lake build failed", "Lean rejected"]),
    ("N5-claim-stale", "claim in instance bytes mutated (old statement)", inst_edit("claim", "firstBit"), True,
     "REJECT", ["instance digest mismatch"]),
    ("N5-claim-regen", "claim mutated, statement regenerated: certificate no longer checks",
     inst_edit_regen("claim", "firstBit"), True, "REJECT", ["lake build failed", "Lean rejected"]),
    ("N6-evidence-stale", "evidence mutated (old statement)", inst_edit("evidence", "f0s0"), True,
     "REJECT", ["instance digest mismatch"]),
    ("N6-evidence-regen", "evidence mutated, statement regenerated", inst_edit_regen("evidence", "f0s0"), True,
     "REJECT", ["lake build failed", "Lean rejected"]),
    ("N7-w0-stale", "w0 mutated (old statement)", inst_edit("w0", "w10"), True, "REJECT",
     ["instance digest mismatch"]),
    ("N7-w0-regen", "w0 mutated, statement regenerated", inst_edit_regen("w0", "w10"), True, "REJECT",
     ["lake build failed", "Lean rejected"]),
    ("N7-w1-stale", "w1 mutated (old statement)", inst_edit("w1", "wOut"), True, "REJECT",
     ["instance digest mismatch"]),
    ("N7-w1-regen", "w1 mutated (outside W), statement regenerated", inst_edit_regen("w1", "wOut"), True,
     "REJECT", ["lake build failed", "Lean rejected"]),
    ("N7-witness-in-statement", "statement names a different w1 than the bytes", case_st(st_witness), True,
     "REJECT", ["identity in statement differs"]),
    ("M34-prop-identity", "proposition identity digest altered", case_st(st_prop_identity), True, "REJECT",
     ["proposition identity differs"]),
    ("M34-prop-statement", "statement claims the proposition of another vector", case_st(st_prop_statement), True,
     "REJECT", ["proposition identity differs"]),
    ("M34-weaker-theorem", "statement points at a theorem proving a different proposition",
     case_st(st_theorem_weaker), True, "REJECT", ["Lean rejected the certificate"]),
    ("M-decoder-stale", "Lean decoder mutated (w0/w1 swapped); old statement", case_decoder_swap, True, "REJECT",
     ["committed VerifierManifest differs"]),
    ("M-decoder-regen", "decoder mutated, statement regenerated: certificate no longer checks",
     case_decoder_swap_regen, True, "REJECT", ["supplied pin"]),
    ("M-decoder-regen-selfpin", "decoder mutated, regenerated, attacker-supplied pin: Lean refuses", case_decoder_swap_regen, "self",
     "REJECT", ["lake build failed", "Lean rejected"]),
    ("M33-toolchain-file", "lean-toolchain changed", case_toolchain_file, True, "REJECT",
     ["committed VerifierManifest differs"]),
    ("M33-lake-manifest", "lake-manifest.json changed", case_lake_manifest, True, "REJECT",
     ["committed VerifierManifest differs"]),
    ("M33-lakefile", "lakefile.toml changed", case_lakefile, True, "REJECT",
     ["committed VerifierManifest differs"]),
    ("M33-lean-executable", "different lean executable with identical version string", case_fake_lean, True,
     "REJECT", ["lean_toolchain_artifact_sha256", "toolchain artifact differs", "resolves a different lean"]),
    ("M35-verifier-digest", "statement verifier.manifest_sha256 != manifest", case_st(st_manifest_digest), True,
     "REJECT", ["statement verifier digest differs"]),
    ("M17-no-limitations", "predicate without limitations", case_st(st_drop_limitations), True, "REJECT",
     ["limitations is a must-understand"]),
    ("M31-limitation-edited", "verbatim limitation text altered", case_st(st_edit_limitation), True, "REJECT",
     ["limitations differ"]),
    ("M30-S_R-in-payload", "post-registration field S_R inside the signed payload", case_st(st_inject_sr), True,
     "REJECT", ["post-registration field"]),
    ("M-outcome", "outcome rewritten to Determinate", case_st(st_outcome), True, "REJECT",
     ["outcome must be"]),
    ("N8-stale-cert-new-profile", "profile changed and tree made consistent, OLD signed statement reused",
     case_stale_new_profile, True, "REJECT", ["stale certificate"]),
    ("F1-honest-cert-outside-evidence", "F1: honest hatch-free certificate for evidence outside Eπ via a different pair",
     case_f1_honest_cert("vectors/negative/m_outside_evidence.json", "⟨.secondBit, .outside, .w00, .w01⟩",
                         ".outside", "ME"), "self", "REJECT", ["lake build failed"]),
    ("F1-honest-cert-incompatible-witness", "F1: honest certificate although the NAMED witness w10 is incompatible",
     case_f1_honest_cert("vectors/negative/n2_incompatible.json", "⟨.secondBit, .obs false none, .w01, .w10⟩",
                         "eU", "N2c"), "self", "REJECT", ["lake build failed"]),
    ("F2-macro-hijack-full", "F2: certificate module hijacks filebytes%/hex% (full pipeline, signed statement for n3)",
     case_meta_full(_hijack_module, "vectors/negative/n3_same_value.json", "Hijack"), "self", "REJECT",
     ["policy violation"]),
    ("F2-macro-hijack-direct", "F2: same module, checker-owned check invoked DIRECTLY (lint bypassed): the precompiled "
     "target must refuse", case_meta_direct(_hijack_module, "Hijack"), "direct", "REJECT",
     ["Lean rejected the certificate", "mismatch"],
     ("vectors/negative/n3_same_value.json", "P10.Certs.Hijack", "P10.Certs.Hijack.cert")),
    ("F3-kernel-bypass-full", "F3: run_cmd + debug.skipKernelTC + addDecl of True.intro typed as Bound n1 (full pipeline)",
     case_meta_full(_inject_module, "vectors/negative/n1_determined.json", "Inject"), "self", "REJECT",
     ["policy violation"]),
    ("F3-kernel-bypass-direct", "F3: same module, checker-owned check invoked DIRECTLY (lint bypassed): kernel replay must refuse",
     case_meta_direct(_inject_module, "Inject"), "direct", "REJECT", ["leanchecker"],
     ("vectors/negative/n1_determined.json", "P10.Certs.Inject", "P10.Certs.Inject.cert")),
    ("cert-sorry-direct", "sorry certificate, checker invoked directly (lint bypassed)",
     case_unsafe_direct("theorem cert : P10.Bound bytes digest := sorry"), "direct", "REJECT",
     ["unexpected Lean output", "Lean rejected"], (VECTOR, MODULE, THEOREM)),
    ("cert-native-decide-direct", "native_decide certificate, checker invoked directly (lint bypassed)",
     case_unsafe_direct("theorem cert : P10.Bound bytes digest :=\n  P10.bound_of_check (by native_decide) (by decide)"),
     "direct", "REJECT", ["unexpected Lean output", "Lean rejected", "leanchecker"], (VECTOR, MODULE, THEOREM)),
    ("CONTROL-honest-direct", "positive control: the honest P1 certificate passes the direct checker-owned check",
     lambda r: None, "direct", "PASS", [], (VECTOR, MODULE, THEOREM)),
    ("N8-statement-profile-digest", "statement profile digest altered", case_st(st_profile_digest), True,
     "REJECT", ["statement profile digest differs"]),
    ("cert-sorry-regen", "certificate replaced by `sorry`, statement regenerated",
     certificate_replace("theorem cert : P10.Bound bytes digest := sorry"), "self", "REJECT",
     ["forbidden construct", "unexpected Lean output", "Lean rejected", "audit"]),
    ("cert-native-decide-regen", "certificate uses native_decide, statement regenerated",
     certificate_replace("theorem cert : P10.Bound bytes digest :=\n  P10.bound_of_check (by native_decide) (by decide)"), "self", "REJECT",
     ["forbidden construct", "unexpected Lean output", "Lean rejected", "audit"]),
    ("cert-axiom-regen", "certificate replaced by an added axiom, statement regenerated",
     certificate_replace("axiom evil : P10.Bound bytes digest\ntheorem cert : P10.Bound bytes digest := evil"), "self", "REJECT",
     ["forbidden construct", "unexpected Lean output", "Lean rejected", "audit"]),
    ("forged-runtime-n3", "runtime signs NotDemonstrated for the same-value vector, attaching the P1 certificate",
     case_forged_runtime_n3, True, "REJECT", ["Lean rejected the certificate"]),
    ("forged-runtime-no-cert", "runtime signs NotDemonstrated citing a certificate that does not exist",
     case_forged_runtime_no_cert, True, "REJECT", ["not bound by the manifest"]),
    ("runtime-other-semantics-old-cert", "runtime with different internal semantics attaches the old certificate",
     case_runtime_other_semantics_old_cert, True, "REJECT", ["committed VerifierManifest differs"]),
    ("INFO-benign-regen-pinned", "benign edit of a bound file, everything regenerated; verifier pinned to the "
     "committed manifest", case_benign_edit_regen, True, "REJECT", ["supplied pin"]),
    ("INFO-benign-regen-selfpin", "same, but the attacker supplies THEIR OWN manifest digest as the pin: accepted as a "
     "DIFFERENT (equivalent) verifier tree — a pin taken from the tree itself is NOT a trust anchor; the pin must "
     "come from outside", case_benign_edit_regen, "self", "PASS", []),
    ("F4-no-pin-HALT", "verify without any manifest pin: HALT, no verdict (a tree cannot vouch for itself)",
     lambda r: None, None, "HALT", ["EXTERNAL verifier-manifest pin"]),
]


def differential_decoder(root) -> list[str]:
    """Python decoder vs Lean partition (tests/Decoder.lean asserts the Lean side)."""
    fails = []
    lean_none = ["m8_whitespace", "m8_key_order", "m8_trailing_newline", "m8_unknown_token", "m8_escape",
                 "m32_wrong_spec", "m_wrong_kind", "m_wrong_profile"]
    lean_some = ["n1_determined", "n2_incompatible", "n3_same_value", "n4_empty_compatible",
                 "m3_outside_world", "m_outside_evidence"]
    for n in lean_none:
        b = read(root, f"vectors/negative/{n}.json")
        try:
            i = p10tool.decode_instance(b)
            # wrong spec decodes syntactically in Python; the spec equality is a separate check
            if n == "m32_wrong_spec" and i["spec"] != "sha256:" + p10tool.EXPECTED_PROFILE_SHA256:
                continue
            fails.append(f"python decoder accepted {n}")
        except p10tool.Verdict:
            pass
    for n in lean_some:
        try:
            p10tool.decode_instance(read(root, f"vectors/negative/{n}.json"))
        except p10tool.Verdict:
            fails.append(f"python decoder rejected {n}")
    return fails


def env_pin_regression() -> list[str]:
    """A mismatched Python TCB dependency must never pass the environment check: mutate the lock file
    (one package at a time, for EVERY pinned package including cryptography), add a missing package and
    an unpinned line; every one must make scripts/check_env.py fail and name the culprit. Also assert
    that verify.sh delegates to check_env.py and carries no per-package exemption."""
    fails = []
    script = os.path.join(HERE, "check_env.py")
    lock = os.path.join(ROOT, "requirements.lock")
    pins = [l.strip() for l in open(lock) if "==" in l]

    def run_lock(text):
        with tempfile.NamedTemporaryFile("w", suffix=".lock", delete=False) as f:
            f.write(text)
        try:
            p = subprocess.run([sys.executable, script, f.name], capture_output=True)
        finally:
            os.unlink(f.name)
        return p.returncode, (p.stdout + p.stderr).decode()

    rc, out = run_lock("\n".join(pins) + "\n")
    if rc != 0:
        fails.append("pristine lock does not pass check_env: " + out[-300:])
    for pin in pins:
        name = pin.split("==")[0]
        mutated = [pin.split("==")[0] + "==0.0.0+mutated" if q == pin else q for q in pins]
        rc, out = run_lock("\n".join(mutated) + "\n")
        if rc == 0 or name not in out:
            fails.append(f"mutated pin for {name} was not rejected (exit {rc})")
    rc, out = run_lock("\n".join(pins + ["p10-nonexistent-package==1.0"]) + "\n")
    if rc == 0:
        fails.append("missing package was not rejected")
    rc, out = run_lock("\n".join(pins + ["six>=1.0"]) + "\n")
    if rc == 0:
        fails.append("unpinned lock line was not rejected")
    rc, out = run_lock("")
    if rc == 0:
        fails.append("empty lock was not rejected")
    v = open(os.path.join(HERE, "verify.sh")).read()
    if "scripts/check_env.py requirements.lock" not in v or '!= "cryptography"' in v or "pkg !=" in v:
        fails.append("verify.sh does not delegate to check_env.py or contains a per-package exemption")
    return fails


def lint_regression() -> list[str]:
    """Source-policy lint must catch the known evasions, including line-split option names."""
    fails = []
    lint = os.path.join(HERE, "lint_lean.py")
    good_cert = read(ROOT, CERTFILE).decode()
    cases = [
        ("valid certificate module passes", "P10/Certs/G.lean", good_cert, 0),
        ("line-split debug option", "P10/X.lean", "set_option\n  debug.skipKernelTC true\n", 1),
        ("setBool on options", "P10/X.lean", "def x := opts.setBool `debug.skipKernelTC true\n", 1),
        ("run_cmd outside allowlist", "P10/X.lean", "run_cmd pure ()\n", 1),
        ("macro_rules in certificate", "P10/Certs/H.lean", "import P10.Bound\nmacro_rules\n  | `(x) => `(y)\n", 1),
        ("import Lean in certificate", "P10/Certs/H.lean", "import Lean\n", 1),
        ("attribute outside allowlist", "P10/X.lean", "attribute [simp] Nat.add_zero\n", 1),
        ("attribute on certificate theorem", "P10/Certs/H.lean", "import P10.Bound\n@[simp] theorem t : True := trivial\n", 1),
        ("non-maxRecDepth option", "P10/X.lean", "set_option maxHeartbeats 0\n", 1),
        ("elab outside allowlist", "P10/X.lean", "elab \"foo%\" : term => pure default\n", 1),
        ("instance in certificate", "P10/Certs/H.lean", "import P10.Bound\ninstance : Inhabited Nat := ⟨0⟩\n", 1),
    ]
    for name, rel, text, want in cases:
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                f.write(text)
            rc = subprocess.run([sys.executable, lint, path], capture_output=True).returncode
        if rc != want:
            fails.append(f"lint case '{name}': expected exit {want}, got {rc}")
    return fails


def pin_policy_regression() -> list[str]:
    """verify.sh must refuse to run without an external pin (and reject a malformed one)."""
    fails = []
    base = {k: v for k, v in os.environ.items() if not k.startswith("P10_")}
    for label, extra, needle in (("no pin", {}, "external pin required"),
                                 ("malformed pin", {"P10_EXPECT_MANIFEST_SHA256": "zz"}, "malformed manifest pin")):
        env = dict(base)
        env.update(extra)
        p = subprocess.run(["bash", os.path.join(HERE, "verify.sh")], cwd=ROOT, env=env,
                           capture_output=True, timeout=120)
        out = (p.stdout + p.stderr).decode()
        if p.returncode == 0 or needle not in out:
            fails.append(f"verify.sh with {label}: expected failure containing {needle!r}, got exit {p.returncode}")
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--only")
    a = ap.parse_args()

    # pristine baseline must PASS and provides the pinned manifest digest
    pin = sha256_file(os.path.join(ROOT, p10tool.MANIFEST_PATH))
    rc, out = tool(ROOT, "verify", COSE, "--manifest-digest", pin)
    if rc != 0:
        print("BASELINE DID NOT PASS:\n" + out)
        return 1
    print(f"baseline PASS; pinned manifest digest {pin}")

    total = ok = 0
    failures = []
    t0 = time.time()
    for case in CASES:
        cid, desc, setup, use_pin, expected, reasons = case[:6]
        direct = case[6] if len(case) > 6 else None
        if a.only and a.only not in cid:
            continue
        total += 1
        scratch = tempfile.mkdtemp(prefix="p10mut-")
        dst = os.path.join(scratch, "tree")
        shutil.copytree(ROOT, dst, ignore=shutil.ignore_patterns(".git", ".venv", "__pycache__", ".toolchain"))
        try:
            env = None
            setup(dst)
            if direct is not None:
                vec, mod, thm = direct
                rc, out = tool(dst, "lean-check", vec, _sha(dst, vec), mod, thm)
            else:
                args = ["verify", COSE]
                if use_pin is True:
                    args += ["--manifest-digest", pin]          # the pristine, externally obtained pin
                elif use_pin == "self":
                    # attacker-supplied pin: the digest of the attacker's own manifest
                    args += ["--manifest-digest", _sha(dst, p10tool.MANIFEST_PATH)]
                if cid == "M33-lean-executable":
                    env = {"PATH": os.path.join(dst, ".fakebin") + os.pathsep + os.environ["PATH"]}
                rc, out = tool(dst, *args, env=env)
            want = EXPECT_CODE[expected]
            reason_ok = (not reasons) or any(r in out for r in reasons)
            good = rc == want and reason_ok
            tag = "PASS" if good else "FAIL"
            if good:
                ok += 1
            else:
                failures.append((cid, rc, out[-900:]))
            first = [l for l in out.splitlines() if l.startswith("VERDICT")] or out.strip().splitlines()[:1]
            print(f"[{tag}] {cid}: expected {expected}, got exit {rc}; {first[0][:150] if first else ''}")
        finally:
            if not a.keep:
                shutil.rmtree(scratch, ignore_errors=True)

    d_fails = differential_decoder(ROOT)
    total += 1
    if d_fails:
        failures.append(("differential-decoder", 0, "; ".join(d_fails)))
        print("[FAIL] differential-decoder:", d_fails)
    else:
        ok += 1
        print("[PASS] differential-decoder: Python and Lean decoders induce the same partition on 14 vectors")

    for label, fn in (("lint-regression", lint_regression), ("pin-policy-regression", pin_policy_regression)):
        f_ = fn()
        total += 1
        if f_:
            failures.append((label, 0, "; ".join(f_)))
            print(f"[FAIL] {label}:", f_)
        else:
            ok += 1
            print(f"[PASS] {label}")
    e_fails = env_pin_regression()
    total += 1
    if e_fails:
        failures.append(("env-pin-regression", 0, "; ".join(e_fails)))
        print("[FAIL] env-pin-regression:", e_fails)
    else:
        ok += 1
        print("[PASS] env-pin-regression: every pinned Python dependency (incl. cryptography) is enforced; "
              "mutated/missing/unpinned locks are rejected; verify.sh has no exemption")

    print(f"\nmutation suite: {ok}/{total} as expected in {time.time() - t0:.0f}s")
    for cid, rc, out in failures:
        print(f"--- UNEXPECTED: {cid} (exit {rc})\n{out}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())

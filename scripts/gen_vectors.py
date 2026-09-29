#!/usr/bin/env python3
"""Generate the S1 wire vectors. Output is JCS-canonical (RFC 8785) for this subset:
flat object, sorted ASCII keys, ASCII-safe string values, no whitespace, no trailing newline.
Run from the repository root. Deterministic; committed outputs are hashed in SHA256SUMS."""
import json, os, sys

SPEC = "sha256:b92c0d689b9f16f2184ba2addb8653ed881595cc3a0117c62cadadf5c6dc6558"
KIND = "p10-s1-instance-v0"
PROFILE = "p10-s1-toy-v0"

def inst(claim, evidence, w0, w1, *, spec=SPEC, kind=KIND, profile=PROFILE):
    obj = {"claim": claim, "evidence": evidence, "kind": kind, "profile": profile,
           "spec": spec, "w0": w0, "w1": w1}
    # json.dumps(sort_keys, compact separators) == JCS for this ASCII-only subset
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()

V = {
  # positive fixture P1: same evidence, both worlds compatible, claim values differ
  "vectors/p1.instance.json": inst("secondBit", "f0s_", "w00", "w01"),
  # N1: evidence determines the claim -> no witness pair is accepted
  "vectors/negative/n1_determined.json": inst("secondBit", "f0s0", "w00", "w01"),
  # N2: w10 is not compatible with f0s_ (values differ: w01=1, w10=0)
  "vectors/negative/n2_incompatible.json": inst("secondBit", "f0s_", "w01", "w10"),
  # N3: both compatible and distinct, but the claim (firstBit) has the same value
  "vectors/negative/n3_same_value.json": inst("firstBit", "f0s_", "w00", "w01"),
  # N4: empty-compatible evidence: nothing to witness
  "vectors/negative/n4_empty_compatible.json": inst("secondBit", "inconsistent", "w00", "w01"),
  # M3: wOut is compatible and divergent, but outside W
  "vectors/negative/m3_outside_world.json": inst("secondBit", "f0s_", "w00", "wOut"),
  # evidence outside E
  "vectors/negative/m_outside_evidence.json": inst("secondBit", "outside", "w00", "w01"),
  # M8: non-canonical encodings of the P1 instance (must all be rejected by the decoder)
  "vectors/negative/m8_whitespace.json":
      b'{"claim": "secondBit","evidence":"f0s_","kind":"p10-s1-instance-v0","profile":"p10-s1-toy-v0","spec":"' + SPEC.encode() + b'","w0":"w00","w1":"w01"}',
  "vectors/negative/m8_key_order.json":
      b'{"evidence":"f0s_","claim":"secondBit","kind":"p10-s1-instance-v0","profile":"p10-s1-toy-v0","spec":"' + SPEC.encode() + b'","w0":"w00","w1":"w01"}',
  "vectors/negative/m8_trailing_newline.json": inst("secondBit", "f0s_", "w00", "w01") + b"\n",
  "vectors/negative/m8_unknown_token.json": inst("secondBit", "f0s_", "w00", "w02"),
  "vectors/negative/m8_escape.json":
      b'{"claim":"second\\u0042it","evidence":"f0s_","kind":"p10-s1-instance-v0","profile":"p10-s1-toy-v0","spec":"' + SPEC.encode() + b'","w0":"w00","w1":"w01"}',
  # profile identity mutations inside the wire
  "vectors/negative/m32_wrong_spec.json":
      inst("secondBit", "f0s_", "w00", "w01", spec="sha256:" + "0" * 64),
  "vectors/negative/m_wrong_kind.json": inst("secondBit", "f0s_", "w00", "w01", kind="p10-s1-instance-v1"),
  "vectors/negative/m_wrong_profile.json": inst("secondBit", "f0s_", "w00", "w01", profile="p10-s1-toy-v1"),
}

if __name__ == "__main__":
    os.makedirs("vectors/negative", exist_ok=True)
    for path, data in V.items():
        with open(path, "wb") as f:
            f.write(data)
        print(path, len(data))

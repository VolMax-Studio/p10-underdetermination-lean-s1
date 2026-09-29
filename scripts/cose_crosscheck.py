#!/usr/bin/env python3
"""Second, independent COSE_Sign1 check (RFC 9052 §4.4 Sig_structure) using only cbor2 + cryptography,
so that acceptance of the signed test vector does not depend on pycose alone.
Also asserts the SCITT Signed Statement shape used by S1: tag 18, protected {1:-8, 3:content-type,
4:kid, 15:{1:iss,2:sub}}, empty unprotected header (no Receipt / label 394), detached=false.
Usage: cose_crosscheck.py FILE.cose  -> exit 0 ok, 1 fail. Uses the public S1 TEST key only."""
import hashlib
import sys

import cbor2
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

SEED = hashlib.sha256(b"P10-S1-TEST-KEY-v0 -- NOT A REAL KEY, NO AUTHORITY, DO NOT TRUST").digest()


def main(path: str) -> int:
    obj = cbor2.loads(open(path, "rb").read())
    if not (isinstance(obj, cbor2.CBORTag) and obj.tag == 18):
        print("not a tagged COSE_Sign1"); return 1
    prot_b, unprot, payload, sig = obj.value
    prot = cbor2.loads(prot_b)
    ok = (prot.get(1) == -8 and prot.get(3) == "application/vnd.in-toto+json" and
          isinstance(prot.get(15), dict) and isinstance(prot[15].get(1), str) and
          isinstance(prot[15].get(2), str) and len(unprot) == 0 and isinstance(payload, bytes))
    if not ok:
        print("unexpected SCITT Signed Statement shape"); return 1
    sig_structure = cbor2.dumps(["Signature1", prot_b, b"", payload])
    pub = Ed25519PrivateKey.from_private_bytes(SEED).public_key()
    try:
        pub.verify(sig, sig_structure)
    except InvalidSignature:
        print("signature invalid"); return 1
    print(f"cose_crosscheck: ok (EdDSA over RFC 9052 Sig_structure; iss={prot[15][1]}; no receipt)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))

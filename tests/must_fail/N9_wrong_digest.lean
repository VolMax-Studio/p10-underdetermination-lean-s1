import P10

/-! MUST FAIL: the P1 certificate is presented for the P1 bytes but with a WRONG digest
(the digest in a statement would then not be the digest of the proved bytes). The kernel-computed
SHA-256 refuses. -/
set_option maxRecDepth 100000
example : P10.Bound (filebytes% "vectors/p1.instance.json")
    (hex% "0000000000000000000000000000000000000000000000000000000000000000") :=
  P10.Certs.P1.cert

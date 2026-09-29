import P10

/-!
FIPS 180-4 / NIST example vectors for the in-Lean SHA-256, checked by the kernel
(`decide`, no `native_decide`). `scripts/verify.sh` additionally runs `Sha256Diff.lean`
and compares many message lengths (including all padding boundaries) against `hashlib`.
-/

open P10.Sha256

set_option maxRecDepth 100000

/-- "abc" (one block). -/
theorem fips_abc :
    sha256 (bytes% "abc") =
      hex% "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by decide

/-- The empty message. -/
theorem fips_empty :
    sha256 [] = hex% "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by decide

/-- 448-bit message (padding spills into a second block). -/
theorem fips_two_block :
    sha256 (bytes% "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      hex% "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by decide

/-- 896-bit message (two full data blocks + padding block). -/
theorem fips_896 :
    sha256 (bytes% "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") =
      hex% "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" := by decide

#print axioms fips_abc
#print axioms fips_empty
#print axioms fips_two_block
#print axioms fips_896

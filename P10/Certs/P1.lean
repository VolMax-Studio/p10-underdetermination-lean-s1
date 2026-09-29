import P10.Bound

/-!
# Certificate for the positive vector P1

The certificate is a kernel-checked term of type `Bound bytes digest`, where `bytes` is the
literal content of `vectors/p1.instance.json` (via `filebytes%`). The proposition is fixed by `P10.Bound`
(canonical form + the exact `CertificateTargetV0` for the witnesses named in the bytes); the
certificate cannot choose it. The verifier checks this theorem against `CheckerTarget.Target`, a
definition it writes and PRECOMPILES in its own Lean process (literal bytes and digest) before this
module is loaded, then replays the whole library with `leanchecker`
(see `scripts/p10tool.py: checker_owned_check`).
-/

set_option maxRecDepth 100000

namespace P10.Certs.P1

open P10 P10.S1 P10.Wire

def bytes : List Nat := filebytes% "vectors/p1.instance.json"

/-- The bytes decode to exactly this instance (evidence `eU`, claim `secondBit`,
witnesses `w00`, `w01`). -/
theorem decoded : decode bytes = some ⟨.secondBit, .obs false none, .w00, .w01⟩ := by
  decide

/-- The encoding of the decoded instance is the committed byte string itself
(canonical form, profile §2.7). -/
theorem canonical : encode ⟨.secondBit, .obs false none, .w00, .w01⟩ = bytes :=
  listEq_sound (by decide)

/-- SHA-256 of `vectors/p1.instance.json` (also checked externally by `sha256sum`). -/
def digest : List Nat := hex% "62353069823aace3a91b37ffabcdf7b2d608134457276b2a5e597ebb49e0e824"

/-- The certificate: the bytes have digest `digest` (kernel-computed SHA-256) and decode to a
canonical instance that is `Underdeterminedπ`. -/
theorem cert : P10.Bound bytes digest :=
  P10.bound_of_check (by decide) (by decide)

/-- Undigested form. -/
theorem holds : Holds bytes := cert.holds

/-- Unpacked: the exact `CertificateTargetV0` for the witnesses NAMED in the bytes. -/
theorem target : CertificateTargetV0 profile eU c0 .w00 .w01 :=
  ((holds_iff decoded).1 holds).2

/-- Unpacked: `Underdeterminedπ(eU, secondBit)` in the S1 profile. -/
theorem underdetermined : Underdetermined profile eU c0 :=
  holds_underdetermined decoded holds

end P10.Certs.P1

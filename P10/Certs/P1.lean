import P10.Bound

/-!
# Certificate for the positive vector P1

The certificate is a kernel-checked term of type `Bound bytes digest`, where `bytes` is the
literal content of `vectors/p1.instance.json` (via `filebytes%`). The proposition is
fixed by `P10.Bound` (which contains `P10.Wire.Holds`); the certificate cannot choose it. The checker-owned
statement `Bound (filebytes% "vectors/p1.instance.json") (hex% <digest>)` is re-elaborated by
`scripts/verify.sh` in a separate file that imports only this module's theorem name.
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

/-- Unpacked: `Underdeterminedπ(eU, secondBit)` in the S1 profile. -/
theorem underdetermined : Underdetermined profile eU c0 :=
  ((holds_iff decoded).1 holds).2

end P10.Certs.P1

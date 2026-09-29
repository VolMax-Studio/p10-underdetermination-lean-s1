import P10

/-!
N1 — evidence determines the claim: an underdetermination certificate cannot be constructed.
Kernel-checked facts (the file must compile; `scripts/verify.sh` runs it):
 * for EVERY witness pair the checker-owned `CertificateTargetV0` is refuted;
 * hence no `UnderdeterminationCertificate` exists;
 * the wire vector for this case is rejected by the reflective checker.
-/

open P10 P10.S1 P10.Wire

def bytes : List Nat := filebytes% "vectors/negative/n1_determined.json"

theorem n1_no_pair (w0 w1 : World) : ¬ CertificateTargetV0 profile eD c0 w0 w1 :=
  n1_determined_no_target w0 w1

theorem n1_no_certificate : ¬ Nonempty (UnderdeterminationCertificate profile eD c0) :=
  n1_determined_no_certificate

theorem n1_wire_decodes : decode bytes = some ⟨.secondBit, .obs false (some false), .w00, .w01⟩ := by
  decide

theorem n1_wire_rejected : check bytes = false := by decide

/-- Proposition-level: the kernel proves `¬ Holds` for these bytes (not merely `check = false`). -/
theorem n1_not_holds : ¬ Holds bytes :=
  not_holds_of_not_target n1_wire_decodes (n1_determined_no_target _ _)

#print axioms n1_no_pair
#print axioms n1_no_certificate
#print axioms n1_wire_rejected
#print axioms n1_not_holds
